#include "slcan.h"
#include "CO_driver_target.h"
#include <stdio.h>
#include <stdlib.h>

extern int CO_rx(void *priv, can_msg_t *msg);

#define SLCAN_MAX_FRAME_SIZE (40 + 1)

static uint8_t nibble2hex(uint8_t x) { return (x & 0x0F) > 9 ? (x & 0x0F) - 10 + 'A' : (x & 0x0F) + '0'; }
static uint8_t hex2nibble(char c, bool *e)
{
	if(c >= '0' && c <= '9')
		return c - '0';
	else if(c >= 'a' && c <= 'f')
		return c - 'a' + 10;
	else if(c >= 'A' && c <= 'F')
		return c - 'A' + 10;
	*e = true;
	return 0;
}

static int cb_frm_data_ext(const uint8_t *cmd, void *priv)
{
	can_msg_t msg = {.IDE = 1, .RTR = 0};
	bool e = false;
	msg.id.ext = (hex2nibble(cmd[1], &e) << 28) | (hex2nibble(cmd[2], &e) << 24) | (hex2nibble(cmd[3], &e) << 20) | (hex2nibble(cmd[4], &e) << 16) |
				 (hex2nibble(cmd[5], &e) << 12) | (hex2nibble(cmd[6], &e) << 8) | (hex2nibble(cmd[7], &e) << 4) | (hex2nibble(cmd[8], &e) << 0);
	msg.DLC = hex2nibble(cmd[9], &e);
	if(e || msg.DLC > 8) return -1;

	const uint8_t *p = &cmd[10];
	for(unsigned i = 0; i < msg.DLC; i++)
	{
		msg.data[i] = (hex2nibble(*p, &e) << 4) | hex2nibble(*(p + 1), &e);
		p += 2;
	}
	if(e) return -3;
	return CO_rx(priv, &msg);
}

static int cb_frm_data_std(const uint8_t *cmd, void *priv)
{
	can_msg_t msg = {.IDE = 0, .RTR = 0};
	bool e = false;
	msg.id.std = (hex2nibble(cmd[1], &e) << 8) | (hex2nibble(cmd[2], &e) << 4) | (hex2nibble(cmd[3], &e) << 0);
	if(cmd[4] < '0' || cmd[4] > '0' + 8) return -1;
	msg.DLC = cmd[4] - '0';
	if(msg.DLC > 8) return -2;
	const uint8_t *p = &cmd[5];
	for(unsigned i = 0; i < msg.DLC; i++)
	{
		msg.data[i] = (hex2nibble(*p, &e) << 4) | hex2nibble(*(p + 1), &e);
		p += 2;
	}
	if(e) return -3;
	return CO_rx(priv, &msg);
}

static int cb_frm_rtr_ext(const uint8_t *cmd, void *priv)
{
	can_msg_t msg = {.IDE = 1, .RTR = 1};
	bool e = false;
	msg.id.ext = (hex2nibble(cmd[1], &e) << 28) | (hex2nibble(cmd[2], &e) << 24) | (hex2nibble(cmd[3], &e) << 20) | (hex2nibble(cmd[4], &e) << 16) |
				 (hex2nibble(cmd[5], &e) << 12) | (hex2nibble(cmd[6], &e) << 8) | (hex2nibble(cmd[7], &e) << 4) | (hex2nibble(cmd[8], &e) << 0);
	if(cmd[9] < '0' || cmd[9] > '0' + 8) return -1;
	msg.DLC = cmd[9] - '0';
	if(msg.DLC > 8) return -2;
	if(e) return -3;
	return CO_rx(priv, &msg);
}

static int cb_frm_rtr_std(const uint8_t *cmd, void *priv)
{
	can_msg_t msg = {.IDE = 0, .RTR = 1};
	bool e = false;
	msg.id.std = (hex2nibble(cmd[1], &e) << 8) | (hex2nibble(cmd[2], &e) << 4) | (hex2nibble(cmd[3], &e) << 0);
	if(cmd[4] < '0' || cmd[4] > '0' + 8) return -1;
	msg.DLC = cmd[4] - '0';
	if(msg.DLC > 8) return -2;
	if(e) return -3;
	return CO_rx(priv, &msg);
}

static int process(void *priv, const uint8_t *msg, uint32_t len)
{
	switch(msg[0])
	{
	case 'T': return cb_frm_data_ext(msg, priv);
	case 't': return cb_frm_data_std(msg, priv);
	case 'R': return cb_frm_rtr_ext(msg, priv);
	case 'r':
		if(msg[1] <= '9') return cb_frm_rtr_std(msg, priv);
		return -1;

	case 's': // Set CAN bitrate
	case 'S': // Set CAN bitrate
	case 'O': // Open CAN in normal mode
	case 'L': // Open CAN in silent mode
	case 'l': // Open CAN with loopback enabled
	case 'C': // Close CAN
	case 'M': // Set CAN acceptance filter ID
	case 'm': // Set CAN acceptance filter mask
	case 'Z': // Enable/disable RX and loopback timestamping
	case 'D': // Tx CAN FD
	case 'F': // Get status flags
	default:
		return -1;

	case '\a':
	case '\r':
		if(len > 1) return slcan_parse(priv, msg + 1, len - 1);
		return -1;
	}
}

int slcan_parse(void *priv, const uint8_t *msg, int len)
{
	int resp = 0;
	CO_CANmodule_t *m = (CO_CANmodule_t *)priv;

	for(int i = 0; i < len; i++)
	{
		if(msg[i] >= 32 && msg[i] <= 126)
		{
			if(m->slcan.pos < SLCAN_BUFFER_SIZE)
			{
				m->slcan.buf[m->slcan.pos] = msg[i];
				m->slcan.pos++;
			}
			else
			{
				m->slcan.pos = 0; // Buffer overrun; silently drop the data
			}
		}
		else if(msg[i] == '\r') // End of command (SLCAN)
		{
			m->slcan.buf[m->slcan.pos] = '\0';
			resp = process(priv, m->slcan.buf, m->slcan.pos);
			m->slcan.pos = 0;
		}
		else if(msg[i] == 8 || msg[i] == 127) // DEL or BS
		{
			if(m->slcan.pos > 0) m->slcan.pos -= 1;
		}
		else
		{
			m->slcan.pos = 0; // Invalid byte - drop the current command, this also includes Ctrl+C, Ctrl+D
		}
	}

	return resp;
}

int slcan_tx(sp_t *sp, const can_msg_t *msg)
{
	uint8_t data[SLCAN_MAX_FRAME_SIZE];
	uint8_t *p = data;
	if(msg->RTR)
	{
		*p++ = msg->IDE ? 'R' : 'r';
	}
	else
	{
		*p++ = msg->IDE ? 'T' : 't';
	}

	if(msg->IDE)
	{
		*p++ = nibble2hex(msg->id.ext >> 28);
		*p++ = nibble2hex(msg->id.ext >> 24);
		*p++ = nibble2hex(msg->id.ext >> 20);
		*p++ = nibble2hex(msg->id.ext >> 16);
		*p++ = nibble2hex(msg->id.ext >> 12);
		*p++ = nibble2hex(msg->id.ext >> 8);
		*p++ = nibble2hex(msg->id.ext >> 4);
		*p++ = nibble2hex(msg->id.ext >> 0);
	}
	else
	{
		*p++ = nibble2hex(msg->id.std >> 8);
		*p++ = nibble2hex(msg->id.std >> 4);
		*p++ = nibble2hex(msg->id.std >> 0);
	}
	*p++ = nibble2hex(msg->DLC);
	for(uint32_t i = 0; i < msg->DLC; i++)
	{
		const uint8_t byte = msg->data[i];
		*p++ = nibble2hex(byte >> 4);
		*p++ = nibble2hex(byte);
	}

	*p++ = nibble2hex(msg->ts >> 12);
	*p++ = nibble2hex(msg->ts >> 8);
	*p++ = nibble2hex(msg->ts >> 4);
	*p++ = nibble2hex(msg->ts >> 0);
	*p++ = '\r';

	return sp_write(sp, data, p - data);
}