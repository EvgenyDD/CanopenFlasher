#ifndef SLCAN_H__
#define SLCAN_H__

#include "sp.h"
#include <stdbool.h>
#include <stdint.h>

typedef struct __attribute__((packed))
{
	union
	{
		uint32_t std;
		uint32_t ext;
	} id;
	uint8_t IDE : 1;
	uint8_t RTR : 1;
	uint8_t DLC : 6;
	uint8_t data[8];
	uint16_t ts;
} can_msg_t;

int slcan_parse(void *priv, const uint8_t *msg, int len);
int slcan_tx(sp_t *sp, const can_msg_t *msg);

void cb_co_frame_rx(void *priv, can_msg_t *msg);
void cb_co_frame_tx(void *priv, can_msg_t *msg);

#endif // SLCAN_H__