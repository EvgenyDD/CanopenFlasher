#ifndef SDO_H__
#define SDO_H__

#include "CANopen.h"
#include <stdint.h>

CO_SDO_abortCode_t read_SDO(CO_SDOclient_t *SDO_C, uint8_t nodeId,
							uint16_t index, uint8_t subIndex,
							uint8_t *buf, size_t bufSize, size_t *readSize,
							uint32_t timeout_ms);

CO_SDO_abortCode_t write_SDO(CO_SDOclient_t *SDO_C, uint8_t nodeId,
							 uint16_t index, uint8_t subIndex,
							 uint8_t *data, size_t dataSize,
							 uint32_t timeout_ms);

#endif // SDO_H__