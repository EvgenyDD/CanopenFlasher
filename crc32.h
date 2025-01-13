#ifndef CRC32_H__
#define CRC32_H__

#include <stdint.h>

uint32_t crc32(const uint8_t *pBuffer, uint32_t NumOfByte);
void crc32_start(const uint8_t *pBuffer, uint32_t NumOfByte, uint32_t *temp);
uint32_t crc32_end(const uint8_t *pBuffer, uint32_t NumOfByte, uint32_t *temp);

#endif // CRC32_H__