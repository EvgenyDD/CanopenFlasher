#include "crc32.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum
{
	LOCK_NONE = 0,
	LOCK_BY_CRC,
	LOCK_BY_ADDR,
	LOCK_BY_SIZE_SMALL,
	LOCK_BY_ZERO_FIELDS_COUNT,
	LOCK_NO_PROD_FIELD,
	LOCK_NO_PROD_NAME_FIELD,
	LOCK_PROD_MISMATCH,
	LOCK_PROD_NAME_FAULT,
} FW_HDR_LOCK_t;

typedef struct
{
	uint32_t fw_size;
	uint32_t fw_crc32; // with fields, without fw_header_v1_t
	uint32_t fields_addr_offset;
	uint32_t reserved2;
} fw_header_v1_t;

typedef struct
{
	int locked;							// locked (::FW_HDR_LOCK_t)
	uintptr_t addr;						// pointer to fw
	uint32_t size;						// firmware size
	int fields_count;					// count of fields
	const char *field_product_ptr;		// pointer to value of the "product" field
	int field_product_len;				// "product" field length
	const char *field_product_name_ptr; // pointer to value of the "product_name" field
	int field_product_name_len;			// "product_name" field length
	uint32_t ver_major;					// parsed major version
	uint32_t ver_minor;					// parsed minor version
	uint32_t ver_patch;					// parsed patch version
} fw_info_t;

static const char *err2str(int err)
{
	switch(err)
	{
	default: return "---";
	case LOCK_NONE: return "LOCK_NONE";
	case LOCK_BY_CRC: return "LOCK_BY_CRC";
	case LOCK_BY_ADDR: return "LOCK_BY_ADDR";
	case LOCK_BY_SIZE_SMALL: return "LOCK_BY_SIZE_SMALL";
	case LOCK_BY_ZERO_FIELDS_COUNT: return "LOCK_BY_ZERO_FIELDS_COUNT";
	case LOCK_NO_PROD_FIELD: return "LOCK_NO_PROD_FIELD";
	case LOCK_NO_PROD_NAME_FIELD: return "LOCK_NO_PROD_NAME_FIELD";
	case LOCK_PROD_MISMATCH: return "LOCK_PROD_MISMATCH";
	case LOCK_PROD_NAME_FAULT: return "LOCK_PROD_NAME_FAULT";
	}
}

static int parse(fw_info_t *fw, fw_header_v1_t *hdr, uint8_t *content, size_t content_length, uint32_t header_offset)
{
	fw->locked = LOCK_NONE; // init
	memcpy(hdr, &content[header_offset], sizeof(fw_header_v1_t));

	fw->size = hdr->fw_size;
	if(fw->size > content_length) fw->locked = LOCK_BY_ADDR; // check flash range
	if(hdr->fw_size <= (header_offset + sizeof(fw_header_v1_t))) fw->locked = LOCK_BY_SIZE_SMALL;
	if(fw->locked) return fw->locked;

	uint32_t crc_val;
	crc32_start(content, header_offset, &crc_val);
	if(crc32_end(&content[header_offset + sizeof(fw_header_v1_t)], hdr->fw_size - (header_offset + (uint32_t)sizeof(fw_header_v1_t)), &crc_val) != hdr->fw_crc32) fw->locked = LOCK_BY_CRC;
	if(fw->locked) return fw->locked;
	return 0;
}

static void print_fields(uint8_t *content, uint32_t addr_fields_start, uint32_t region_size)
{
	unsigned int null_term_count = 0, element_count = 0 /* field keys or values */;
	bool null_captured = true; /* assuming that -1 element is '\0' */
	for(uint32_t i = 0; i < region_size; i++)
	{
		if(content[addr_fields_start + i] == '\0')
		{
			if(i == 0) return; // first element can't be zero
			null_term_count++;
			if(null_term_count == 1) element_count++;
			null_captured = true;
		}
		else
		{
			null_term_count = 0;
			if(null_captured) // start condition of the new string
			{
				null_captured = false;
				if((element_count & 1U) == 0) // check only keys, not values
				{
					fprintf(stderr, "| %-24s | %-24s|\n", &content[addr_fields_start + i],
							&content[addr_fields_start + i + strlen((const char *)&content[addr_fields_start + i]) + 1]);
				}
			}
		}
		if(null_term_count >= 2) return; // end of search
	}
}

int parse_file_fw(const char *file_name);
int parse_file_fw(const char *file_name)
{
	FILE *f = fopen(file_name, "rb");
	if(!f)
	{
		fprintf(stderr, "FW: error:\topen file %s\n", file_name);
		return 1;
	}

	fseek(f, 0, SEEK_END);
	size_t file_size = (size_t)ftell(f);
	rewind(f);
	uint8_t *file_data = malloc(file_size);

	size_t read = fread(file_data, 1, file_size, f);
	if(read != file_size)
	{
		fprintf(stderr, "FW: error:\tread file (%zu %zu)\n", read, file_size);
		if(f) fclose(f);
		if(file_data) free(file_data);
		return 2;
	}

	fprintf(stderr, "\n===== FW Parser =====\n");

	fw_info_t fw;
	fw_header_v1_t hdr;
	int sts = 1;
	uint32_t offset = 4;
	for(; offset < 0x800 || offset < file_size; offset++)
	{
		sts = parse(&fw, &hdr, file_data, file_size, offset);
		if(sts == LOCK_BY_ADDR ||
		   sts == LOCK_BY_CRC ||
		   sts == LOCK_BY_SIZE_SMALL) continue;
		if(sts) fprintf(stderr, "Error: %s\n", err2str(sts));
		fprintf(stderr, "@offset x%x\n", offset);
		break;
	}
	if(sts == 0)
	{
		fprintf(stderr, "------------------------------------------------------\n");
		print_fields(file_data, hdr.fields_addr_offset, file_size < hdr.fields_addr_offset ? 0 : (uint32_t)file_size - hdr.fields_addr_offset);
		fprintf(stderr, "------------------------------------------------------\n");
	}

	if(f) fclose(f);
	if(file_data) free(file_data);
	return 0;
}