#include "crc32.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CONFIG_MAX_KEY_SIZE 32
#define DATA_OFFSET 4
#define BUFFER_SIZE 32

typedef struct
{
	const char *key;
	uint16_t size;
	uint32_t data_abs_address;
	void *data;
} config_entry_t;

typedef enum
{
	CONFIG_STS_OK = 0,
	CONFIG_STS_STORAGE_READ_ERROR,
	CONFIG_STS_STORAGE_WRITE_ERROR,
	CONFIG_STS_STORAGE_WRONG_FORMAT,
	CONFIG_STS_STORAGE_OUT_OF_BOUNDS,
	CONFIG_STS_WRONG_SIZE_CONFIG,
	CONFIG_STS_CRC_INVALID,
	CONFIG_STS_KEY_LONG,
	CONFIG_STS_KEY_SHORT,
	CONFIG_STS_LENGTH_DATA_ZERO,
	CONFIG_STS_PARSER_NOT_FINISHED,
	CONFIG_STS_NO_DATA,
} config_sts_t;

typedef enum
{
	PROCESS_FINISH = 0,
	PROCESS_KEY,
	PROCESS_LENGTH,
	PROCESS_VALUE,
} sts_t;

typedef struct
{
	uint8_t name_buffer[CONFIG_MAX_KEY_SIZE];
	uint16_t name_buffer_size;
	uint16_t length_data;
	uint16_t length_size;
	uint32_t offset_entry_data; // global offset from the flash start
	sts_t sts;
} parse_struct_t;

static parse_struct_t parser;

static const char *err2str(int err)
{
	switch(err)
	{
	default: return "---";
	case CONFIG_STS_OK: return "OK";
	case CONFIG_STS_STORAGE_READ_ERROR: return "STORAGE_READ_ERROR";
	case CONFIG_STS_STORAGE_WRITE_ERROR: return "STORAGE_WRITE_ERROR";
	case CONFIG_STS_STORAGE_WRONG_FORMAT: return "STORAGE_WRONG_FORMAT";
	case CONFIG_STS_STORAGE_OUT_OF_BOUNDS: return "STORAGE_OUT_OF_BOUNDS";
	case CONFIG_STS_WRONG_SIZE_CONFIG: return "WRONG_SIZE_CONFIG";
	case CONFIG_STS_CRC_INVALID: return "CRC_INVALID";
	case CONFIG_STS_KEY_LONG: return "KEY_LONG";
	case CONFIG_STS_KEY_SHORT: return "KEY_SHORT";
	case CONFIG_STS_LENGTH_DATA_ZERO: return "LENGTH_DATA_ZERO";
	case CONFIG_STS_PARSER_NOT_FINISHED: return "PARSER_NOT_FINISHED";
	case CONFIG_STS_NO_DATA: return "NO_DATA";
	}
}

static config_sts_t parse_data(const uint8_t *content, const uint32_t offset_data, const uint8_t *data, uint16_t length)
{
	for(uint16_t i = 0; i < length; i++)
	{
		switch(parser.sts)
		{
		case PROCESS_FINISH:
			if(data[i] == '\0') continue; // padding is made of '\0'
										  // fall through
		case PROCESS_KEY:
			parser.sts = PROCESS_KEY;
			parser.name_buffer[parser.name_buffer_size++] = data[i];
			if(parser.name_buffer_size >= CONFIG_MAX_KEY_SIZE && data[i] != '\0') return CONFIG_STS_KEY_LONG; // no end zero
			if(data[i] == '\0' && parser.name_buffer_size <= 1) return CONFIG_STS_KEY_SHORT;
			if(data[i] == '\0') parser.sts = PROCESS_LENGTH;
			break;

		case PROCESS_LENGTH:
			parser.length_data |= data[i] << (8 * parser.length_size);
			if(++parser.length_size >= 2)
			{
				if(parser.length_data == 0) return CONFIG_STS_LENGTH_DATA_ZERO;
				parser.sts = PROCESS_VALUE;
				parser.offset_entry_data = offset_data + (i + 1U) /* next byte*/;
			}
			break;

		case PROCESS_VALUE:
			if(parser.offset_entry_data + parser.length_data == offset_data + i + 1) // entry is ready!
			{
				parser.sts = PROCESS_FINISH;
				{
					char str[2048];
					int len = 0;
					for(uint32_t j = 0; j < parser.length_data; j++)
						len += snprintf(&str[len], sizeof(str) - (size_t)len, " x%02x", content[parser.offset_entry_data + j]);

					fprintf(stderr, "| %3db | %-20s | %-40s|\n", parser.length_data, parser.name_buffer, str);
				}
				memset(&parser, 0, sizeof(parser));
			}
			break;

		default: break;
		}
	}
	return CONFIG_STS_OK;
}

static int parse(uint8_t *content, size_t content_length)
{
	uint8_t buffer_array[BUFFER_SIZE];
	uint32_t crc_val;

	uint32_t size_config;
	memcpy((uint8_t *)&size_config, content, sizeof(size_config));
	crc32_start((uint8_t *)&size_config, sizeof(uint32_t), &crc_val);

	const uint32_t end_data = DATA_OFFSET + size_config;

	if(size_config < (8) /* minimal data */ ||
	   size_config > DATA_OFFSET + content_length + 4 ||
	   (size_config & 0x03U) /* not the multiple of 4 */) return CONFIG_STS_WRONG_SIZE_CONFIG;

	uint32_t crc_calc = 0;
	for(uint32_t i = 0, word; i < size_config; i += 4)
	{
		memcpy((uint8_t *)&word, &content[DATA_OFFSET + i], sizeof(uint32_t));
		crc_calc = crc32_end((uint8_t *)&word, sizeof(uint32_t), &crc_val);
	}

	uint32_t crc_end;
	memcpy((uint8_t *)&crc_end, &content[end_data], sizeof(uint32_t));
	if(crc_end != crc_calc) return CONFIG_STS_CRC_INVALID;

	memset(&parser, 0, sizeof(parser));

	uint32_t offset_read = DATA_OFFSET;
	for(;;)
	{
		uint32_t size = BUFFER_SIZE;
		if(size > end_data - offset_read) size = end_data - offset_read;

		memcpy(buffer_array, &content[offset_read], size);

		config_sts_t sts = parse_data(content, offset_read, buffer_array, (uint16_t)size);
		if(sts) return sts;

		offset_read += size;

		// last
		if(offset_read == end_data)
		{
			if(parser.sts != PROCESS_FINISH) return CONFIG_STS_PARSER_NOT_FINISHED;
			return CONFIG_STS_OK;
		}
	}
}

int parse_file_cfg(const char *file_name);
int parse_file_cfg(const char *file_name)
{
	FILE *f = fopen(file_name, "rb");
	if(!f)
	{
		fprintf(stderr, "CFG: error:\topen file %s\n", file_name);
		return 1;
	}

	fseek(f, 0, SEEK_END);
	size_t file_size = (size_t)ftell(f);
	rewind(f);
	uint8_t *file_data = malloc(file_size);

	size_t read = fread(file_data, 1, file_size, f);
	if(read != file_size)
	{
		fprintf(stderr, "CFG: error:\tread file (%zu %zu)\n", read, file_size);
		if(f) fclose(f);
		if(file_data) free(file_data);
		return 2;
	}

	fprintf(stderr, "\n===== CFG Parser =====\n");
	fprintf(stderr, "-------------------------------------------------------------------------\n");
	int sts = parse(file_data, file_size);
	fprintf(stderr, "-------------------------------------------------------------------------\n");
	if(sts) fprintf(stderr, "Error: %s\n", err2str(sts));

	if(f) fclose(f);
	if(file_data) free(file_data);
	return 0;
}