#include "co_wrapper.h"
#include "crc32.h"
#include "percent_tracker.h"
#include "sdo.h"
#include "slcan.h"
#include "timedate.h"
#include <ctype.h>
#include <math.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PORT_ID "VID_F055&PID_1337"

#define CANOPEN_FLASHER_VER "1.0.0"

#define REBOOT_TO 400
#define RETRY_CNT 5

#define QUANT_FLASH 256

#define BLOCK_SZ (534)

extern int parse_file_cfg(const char *file_name);
extern int parse_file_fw(const char *file_name);

typedef enum
{
	FW_PREBOOT = 0,
	FW_BOOT,
	FW_APP,
} FW_TYPE_t;

static const char *fw_type_str[] = {"PREBOOT", "BOOT", "APP", "CFG"};

enum
{
	ERR_ARGC = 1,
	ERR_FILE,
	ERR_FILE_READ,
	ERR_INIT,
	ERR_DEV_INIT,
	ERR_REBOOT,
	ERR_WR,
	ERR_RD,
	ERR_CHK,
};

static FILE *f = NULL;
static uint8_t *content = NULL;
static progress_tracker_t tr;
static ssize_t cnt;

static CO_t *co;
static sp_t sp = {0};

enum
{
	CO_SDO_FLASHER_W_STOP = 0x00,			  /* The target is instructed to stop the running programme (HALT) */
	CO_SDO_FLASHER_W_START = 0x01,			  /* The target is instructed to start the selected programme (FAST BOOT) */
	CO_SDO_FLASHER_W_RESET_STAT = 0x02,		  /* The target is instructed to reset the status (index 0x1F57) */
	CO_SDO_FLASHER_W_CLEAR = 0x03,			  /* The target is instructed to clear that area of the flash that has been selected with the appropriate sub-index (FLASH ERASE) */
	CO_SDO_FLASHER_W_START_BOOTLOADER = 0x80, /* You can jump back from the application into the bootloader using this command. This entry must therefore also be supported by the application to start the bootloader (refer also to 3.2). "Reboot" */
	CO_SDO_FLASHER_W_SET_SIGNATURE = 0x83,	  /* The target is instructed to flag the selected and programmed program as „valid“. In addition to a valid CRC and node number, this is the requirement to start the program automatically after a power-on-reset */
	CO_SDO_FLASHER_W_CLR_SIGNATURE = 0x84,	  /* The target is instructed to flag the selected and programmed program as „invalid“. After a power-on RESET, the application would then not be started; the bootloader remains active. */
	CO_SDO_FLASHER_CHECK_SIGNATURE = 0x10,
};

enum
{
	CO_SDO_FLASHER_R_OK = 0x00000000,		  /* The last command transmitted has been run without error */
	CO_SDO_FLASHER_R_BUSY = 0x00000001,		  /* A command is still being run */
	CO_SDO_FLASHER_R_NOVALPROG = 0x00000002,  /* An attempt has been made to start an invalid application programme */
	CO_SDO_FLASHER_R_FORMAT = 0x00000004,	  /* The format of binary data that have been transferred to index 0x1F50 is incorrect */
	CO_SDO_FLASHER_R_CRC = 0x00000006,		  /* The CRC of the binary data is incorrect */
	CO_SDO_FLASHER_R_NOTCLEARED = 0x00000008, /* An attempt has been made to programme although there is a valid application programme */
	CO_SDO_FLASHER_R_WRITE = 0x0000000A,	  /* An error occurred during the writing of the flash */
	CO_SDO_FLASHER_R_ADDRESS = 0x0000000C,	  /* An attempt has been made to write an invalid address into the flash */
	CO_SDO_FLASHER_R_SECURED = 0x0000000E,	  /* An attempt has been made to write to a protected flash area */
	CO_SDO_FLASHER_R_NVDATA = 0x00000010,	  /* An error has occurred when accessing the non-volatile memory (e.g. programming the signature) */
};

enum
{
	SDO_FL_ERR_STS_FL = 10,
	SDO_FL_ERR_WR_CMD,
	SDO_FL_ERR_RD_IDENT,
	SDO_FL_ERR_RD_IDENT2,
	SDO_FL_ERR_ID_SAME_SECOND_TIME,
	SDO_FL_ERR_SIZE_BIGGER_THAN_BUFFER,
	SDO_FL_ERR_WR_PAYLOAD,
	SDO_FL_ERR_NOT_FOUND,
	SDO_FL_ERR_LOCKED
};

static const char *SDO_FL_ERR2STR(uint32_t err)
{
	switch(err)
	{
	default: return "Unknown";
	case SDO_FL_ERR_STS_FL: return "STS_FL";
	case SDO_FL_ERR_WR_CMD: return "WR_CMD";
	case SDO_FL_ERR_RD_IDENT: return "RD_IDENT";
	case SDO_FL_ERR_RD_IDENT2: return "RD_IDENT2";
	case SDO_FL_ERR_ID_SAME_SECOND_TIME: return "ID_SAME_SECOND_TIME";
	case SDO_FL_ERR_SIZE_BIGGER_THAN_BUFFER: return "SIZE_BIGGER_THAN_BUFFER";
	case SDO_FL_ERR_WR_PAYLOAD: return "WR_PAYLOAD";
	case SDO_FL_ERR_NOT_FOUND: return "NOT_FOUND";
	case SDO_FL_ERR_LOCKED: return "LOCKED";
	}
}

struct __attribute__((packed))
{
	uint32_t block_number;
	uint32_t address;
	uint32_t size;
	uint8_t data[BLOCK_SZ];
	uint8_t data_crc[4];
} block;

static void on_exit_cb(void)
{
	sp_close(&sp);
	co_wrapper_deinit(&co);
	if(f) fclose(f);
	if(content) free(content);
	f = NULL;
	content = NULL;
}

static size_t file_len(void)
{
	fseek(f, 0, SEEK_END);
	size_t s = (size_t)ftell(f);
	rewind(f);
	return s;
}

static struct
{
	bool write;
	FW_TYPE_t sel;
	char *file_name;
	char *dev_name;
	int id;
} cfg = {0};

static int parse_arg(char *argv[], int argc)
{
	if(argc != 5 && argc != 6)
	{
		fprintf(stderr, "Error! CANOPEN FLASHER [ver. %s]: Wrong argument count!\nUsage:\n"
						"  w/r     - write/read operation\n"
						"  p/b/a/c - fw select: preboot/boot/app/config\n"
						"  file    - firmware binary\n"
						"  id      - device CAN ID\n"
						"  name    - device name (write)\n",
				CANOPEN_FLASHER_VER);
		return ERR_ARGC;
	}

	int w = strcmp(argv[1], "w") == 0 ? 1 : (strcmp(argv[1], "r") == 0 ? 0 : -1);
	if(w < 0)
	{
		fprintf(stderr, "Error! 1st argument is [r/w], not [%s]!\n", argv[1]);
		return ERR_ARGC;
	}
	cfg.write = w;

	int s = strcmp(argv[2], "p") == 0 ? FW_PREBOOT : (strcmp(argv[2], "b") == 0 ? FW_BOOT : (strcmp(argv[2], "a") == 0 ? FW_APP : (strcmp(argv[2], "c") == 0 ? FW_APP + 1 : -1)));
	if(s < 0)
	{
		fprintf(stderr, "Error! 2st argument is [p/b/a/c], not [%s]!\n", argv[2]);
		return ERR_ARGC;
	}
	if(s == FW_PREBOOT && cfg.write)
	{
		fprintf(stderr, "Error! PREBOOT write is not yet supported!\n");
		return ERR_ARGC;
	}
	if(s == FW_APP + 1 && cfg.write)
	{
		fprintf(stderr, "Error! CFG write is not yet supported!\n");
		return ERR_ARGC;
	}
	cfg.sel = s;

	cfg.file_name = argv[3];
	cfg.id = atoi(argv[4]);
	cfg.dev_name = argc == 6 ? argv[5] : NULL;
	if(cfg.write && !cfg.dev_name)
	{
		fprintf(stderr, "Error! Name not specified for write mode!\n");
		return ERR_ARGC;
	}
	return 0;
}

#define CHK(x) \
	if((sts = x) != 0) printf("ERR %s: %s\n", #x, sp_err2_str(sts))

static void sp_rx(sp_t *p, const uint8_t *data, size_t len) { slcan_parse(((CO_t *)p->priv)->CANmodule, data, len); }

static int read_sts_flash(CO_t *c, uint8_t id, const char *op)
{
	uint32_t err_code, flash_sts = 0;
	size_t rd = sizeof(flash_sts);
	for(int i = 0; i < 20; i++)
	{
		if((err_code = read_SDO(c->SDOclient, id, 0x1F57, 1, (uint8_t *)&flash_sts, sizeof(flash_sts), &rd, 100)) == 0)
		{
			if(flash_sts == CO_SDO_FLASHER_R_OK) return 0;
			if(flash_sts != CO_SDO_FLASHER_R_BUSY) break;
		}
		delay_ms(100);
	}
	printf("error:    read_sts_flash %s failed, status: x%x | SDO: x%X", op, flash_sts, err_code);
	return SDO_FL_ERR_STS_FL;
}

static void dev_reset(CO_t *c, uint8_t id)
{
	uint32_t cmd;
	cmd = CO_SDO_FLASHER_W_START_BOOTLOADER;
	int sts = write_SDO(c->SDOclient, id, 0x1F51, 1, (uint8_t *)&cmd, sizeof(cmd), 100);
}

static void str_to_upper(char *temp)
{
	char *name = strtok(temp, ":");
	char *s = name;
	while(*s)
	{
		*s = toupper((unsigned char)*s);
		s++;
	}
}

static int dev_prepare(CO_t *c, uint8_t id, const char *tgt_name, const char *oth_name)
{
	uint32_t cmd;
	CO_SDO_abortCode_t sts;

	uint8_t str[64] = {0};
	size_t rd = sizeof(str);
	if((sts = read_SDO(co->SDOclient, id, 0x1008, 0, str, sizeof(str), &rd, 800)) != 0) return SDO_FL_ERR_RD_IDENT;

	str_to_upper((char *)str);
	if(strcmp((char *)str, tgt_name) != 0 && strcmp((char *)str, oth_name) != 0)
	{
		printf("error:    device (%s or %s) not found: %s\n", tgt_name, oth_name, str);
		return SDO_FL_ERR_NOT_FOUND;
	}
	if(strcmp((char *)str, oth_name) == 0) // need reset
	{
		dev_reset(c, id);
		SLEEP_MS(150);
		rd = sizeof(str);
		memset(str, 0, sizeof(str));
		if((sts = read_SDO(c->SDOclient, id, 0x1008, 0, str, sizeof(str), &rd, 800)) != 0) return SDO_FL_ERR_RD_IDENT2;
		str_to_upper((char *)str);
		if(strcmp((char *)str, tgt_name) == 0) return 0;
		if(strcmp((char *)str, oth_name) == 0) return SDO_FL_ERR_LOCKED;
	}

	cmd = CO_SDO_FLASHER_W_STOP;
	if((sts = write_SDO(c->SDOclient, id, 0x1F51, 1, (uint8_t *)&cmd, sizeof(cmd), 3000)) != 0) return SDO_FL_ERR_WR_CMD;
	if((sts = read_sts_flash(c, id, "CO_SDO_FLASHER_W_STOP")) != 0) return sts;

	cmd = CO_SDO_FLASHER_W_CLEAR;
	if((sts = write_SDO(c->SDOclient, id, 0x1F51, 1, (uint8_t *)&cmd, sizeof(cmd), 3000)) != 0) return SDO_FL_ERR_WR_CMD;
	if((sts = read_sts_flash(c, id, "CO_SDO_FLASHER_W_CLEAR")) != 0) return sts;

	return 0;
}

static int dev_write(CO_t *c, uint8_t id, uint32_t addr, const uint8_t *data, uint32_t size)
{
	uint32_t cmd;
	CO_SDO_abortCode_t sts;

	uint8_t str[64] = {0};
	size_t rd = sizeof(str);

	if(size > BLOCK_SZ) return SDO_FL_ERR_SIZE_BIGGER_THAN_BUFFER;

	block.block_number = addr;
	block.address = addr;
	block.size = size;

	memcpy(block.data, data, block.size);
	uint32_t block_crc = crc32((uint8_t *)&block, 12U + block.size);
	memcpy(&block.data[block.size], (uint8_t *)&block_crc, sizeof(block_crc));

	if((sts = write_SDO(c->SDOclient, id, 0x1F50, 1, (uint8_t *)&block, 16 + block.size, 3000)) != 0) return SDO_FL_ERR_WR_PAYLOAD;
	if((sts = read_sts_flash(c, id, "WRITE BLOCK")) != 0) return sts;
	return 0;
}

static int dev_read(CO_t *c, uint8_t id, uint8_t fw_sel, uint32_t addr, uint8_t *data, uint32_t *size)
{
	block.block_number = fw_sel;
	block.address = addr;
	block.size = 0;

	uint32_t block_crc = crc32((uint8_t *)&block, 12U + block.size);
	memcpy(&block.data[block.size], (uint8_t *)&block_crc, sizeof(block_crc));

	int sts = write_SDO(c->SDOclient, id, 0x1F50, 1, (uint8_t *)&block, 16 + block.size, 3000);
	if(sts) return -1;

	uint8_t pkt[1024];
	size_t rd = sizeof(pkt);
	sts = read_SDO(c->SDOclient, id, 0x1F50, 1, pkt, sizeof(pkt), &rd, 100);
	if(!sts)
	{
		if(rd < 5) return -2;
		uint8_t sel = pkt[0];
		uint32_t off;
		memcpy(&off, &pkt[1], 4);
		if(sel != fw_sel || off != addr) return -3;
		memcpy(data, &pkt[5], rd - 5);
		return rd - 5;
	}
	return -4;
}

static int dev_check(CO_t *c, uint8_t id)
{
	uint32_t cmd;
	CO_SDO_abortCode_t sts;
	cmd = CO_SDO_FLASHER_CHECK_SIGNATURE;
	if((sts = write_SDO(c->SDOclient, id, 0x1F51, 1, (uint8_t *)&cmd, sizeof(cmd), 3000)) != 0) return SDO_FL_ERR_WR_CMD;
	if((sts = read_sts_flash(c, id, "CO_SDO_FLASHER_CHECK_SIGNATURE")) != 0) return sts;
	return 0;
}

int main(int argc, char *argv[])
{
	int sts = parse_arg(argv, argc);
	if(sts) return sts;

	atexit(on_exit_cb);

	sp_list_t list = {0};

	// while(sp_enumerate(&list))
	// 	if(strstr(list.info.port, "ttyS") == NULL) printf("    %s#%s#%s\n", list.info.port, list.info.description, list.info.hardware_id);

	while(sp_enumerate(&list))
		if(strstr(list.info.hardware_id, PORT_ID) != NULL)
		{
			strcat(sp.port_name, list.info.port);
			printf("Using %s %s %s\n", list.info.port, list.info.description, list.info.hardware_id);
			sp_enumerate_finish(&list);
			break;
		}

	CHK(co_wrapper_init(&co, &sp));
	if(sts) return ERR_INIT;

	CHK(sp_open(&sp, 0, sp_rx, co));
	if(sts) return ERR_INIT;

	// uint32_t cmd3 = 0x73617665; // cfg save
	// int stsd = write_SDO(co->SDOclient, cfg.id, 0x1010, 1, (uint8_t *)&cmd3, sizeof(cmd3), 3000);

	if(cfg.write)
	{
		f = fopen(cfg.file_name, "rb");
		if(!f)
		{
			fprintf(stderr, "error:    open file %s\n", cfg.file_name);
			return ERR_FILE;
		}

		size_t content_length = file_len();
		content = malloc(content_length);

		size_t read = fread(content, 1, content_length, f);
		if(read != content_length)
		{
			fprintf(stderr, "error:    read file (%zu %zu)\n", read, content_length);
			return ERR_FILE_READ;
		}

		fprintf(stderr, "info:    flashing %s %s to \"%s\" (%zu bytes)...\n",
				cfg.file_name, fw_type_str[cfg.sel], cfg.dev_name, content_length);

		int errc = 1;

		char oth_name[256];
		if(cfg.sel == FW_BOOT)
		{
			snprintf(oth_name, sizeof(oth_name), "%s_LDR", cfg.dev_name);
			strcat(cfg.dev_name, "_APP");
		}
		if(cfg.sel == FW_APP)
		{
			snprintf(oth_name, sizeof(oth_name), "%s_APP", cfg.dev_name);
			strcat(cfg.dev_name, "_LDR");
		}

		sts = dev_prepare(co, cfg.id, cfg.dev_name, oth_name);
		if(sts)
		{
			fprintf(stderr, "error:    failed to prepare: %s\n", SDO_FL_ERR2STR(sts));
			return ERR_DEV_INIT;
		}

		for(uint32_t retry = 0; retry < RETRY_CNT; retry++)
		{
			PERCENT_TRACKER_INIT(tr);
			for(uint32_t off = 0;; off += QUANT_FLASH)
			{
				if(off >= content_length)
				{
					errc = 0;
					break;
				}

				uint32_t size_to_write = (uint32_t)content_length - off > QUANT_FLASH ? QUANT_FLASH : (uint32_t)content_length - off;
				int sts_dfu_write;
				for(uint32_t retr_write = 0; retr_write < RETRY_CNT; retr_write++)
				{
					if((sts_dfu_write = dev_write(co, cfg.id, off, &content[off], size_to_write)) >= 0) break;
				}
				if(sts_dfu_write < 0)
				{
					errc = ERR_WR;
					break;
				}

				PERCENT_TRACKER_TRACK(tr, (double)off / (double)(content_length),
									  { fprintf(stderr, "\rinfo:    %.1f%% | pass: %lld sec | est: %lld sec        ",
												100.0 * tr.progress, tr.time_ms_pass / 1000, tr.time_ms_est / 1000); });
				fflush(stdout);
			}
			if(errc == 0)
			{
				fprintf(stderr, "\rinfo:    100.0%% | pass: %.3f sec | speed: %.2f kB/s        ",
						(double)tr.time_ms_pass * 0.001, (double)(content_length / (double)tr.time_ms_pass));
				break;
			}
			if(retry != RETRY_CNT - 1) fprintf(stderr, "error:    trying again...\n");
		}
		fprintf(stderr, "\n");

		if(!errc && cfg.sel <= FW_APP)
		{
			sts = dev_check(co, cfg.id);
			if(sts)
			{
				fprintf(stderr, "error:    failed to check HW\n");
				errc = ERR_CHK;
			}
		}
		fprintf(stderr, errc ? "error:    update failed\n" : "info:    OK, exiting...\n");

		if(errc == 0) dev_reset(co, cfg.id);
	}
	else // read
	{
		f = fopen(cfg.file_name, "wb");
		if(!f)
		{
			fprintf(stderr, "error:    open file %s\n", cfg.file_name);
			return ERR_FILE;
		}
		fprintf(stderr, "info:    reading \"%s\" %s to %s...\n", cfg.dev_name, fw_type_str[cfg.sel], cfg.file_name);

		uint32_t cmd = CO_SDO_FLASHER_W_STOP;
		write_SDO(co->SDOclient, cfg.id, 0x1F51, 1, (uint8_t *)&cmd, sizeof(cmd), 3000);
		if(!sts) sts = read_sts_flash(co, cfg.id, "CO_SDO_FLASHER_W_STOP");
		if(sts)
		{
			fprintf(stderr, "error:    failed to setup device \"%s\"\n", cfg.dev_name);
			return ERR_REBOOT;
		};

		int errc = 1;
		uint8_t pkt[QUANT_FLASH];
		PERCENT_TRACKER_INIT(tr);
		for(uint32_t offset = 0, readed_length = 0;; offset += (uint32_t)sts)
		{
			errc = 1;
			for(uint32_t try = 0; try < 5; try++)
			{
				uint32_t readed = sizeof(pkt);
				sts = dev_read(co, cfg.id, cfg.sel, offset, pkt, &readed);
				if(sts < 0)
				{
					fprintf(stderr, "\rerror:    failed to read (%d) @%d\n", sts, offset);
				}
				else
				{
					errc = 0;
					break;
				}
			}
			if(errc) break;

			readed_length += (uint32_t)sts;
			fprintf(stderr, "\rreading... %d bytes", readed_length);
			if(sts == 0) // done
			{
				struct timeval t1;
				gettimeofday(&t1, NULL);
				tr.time_ms_pass = (uint64_t)((t1.tv_sec - tr.t0.tv_sec) * 1000 + (t1.tv_usec - tr.t0.tv_usec) / 1000);
				tr.time_ms_est = (uint64_t)((float)tr.time_ms_pass / tr.progress);
				fprintf(stderr, " | pass: %.3f sec | speed: %.2f kB/s\n", (double)tr.time_ms_pass * 0.001, (double)(readed_length / (double)tr.time_ms_pass));
				if(readed_length == 0) fprintf(stderr, "FW region is invalid (size is 0)\n");
				errc == 0;
				fclose(f);
				f = NULL;
				if(cfg.sel == FW_APP + 1 && readed_length) parse_file_cfg(cfg.file_name);
				if(cfg.sel <= FW_APP && readed_length) parse_file_fw(cfg.file_name);
				break;
			}

			size_t wr_cnt = fwrite(pkt, 1, (size_t)sts, f);
			if(wr_cnt != (size_t)sts)
			{
				fprintf(stderr, "error:    failed to write to file %s\n", cfg.file_name);
				errc = 1;
				break;
			}
		}
		fprintf(stderr, errc ? "Error!\n" : "info:    OK, exiting...\n");
		return errc;
	}
}
