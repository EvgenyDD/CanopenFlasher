#ifndef SP_H__
#define SP_H__

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#define SP_WRITE_TIMEOUT_MS 500
#define SP_RX_SIZE 1024

#define SP_INFO_LEN 256

enum
{
	SP_ERR_WR_ZERO = 1,
	SP_ERR_WR_LESS,
	SP_ERR_WR_LOCK,
	SP_ERR_WR_UNLOCK,
	SP_ERR_GET_MDM_STS,
	SP_ERR_SET_MDM_STS,
	SP_ERR_READ,
	SP_ERR_GET_OVERLAP,
	SP_ERR_WAIT_COMM_EVENT,
	SP_ERR_PORT_NOT_EXIST,
	SP_ERR_PORT_OPEN_BUSY,
	SP_ERR_PORT_OPEN_INVALID,
	SP_ERR_PORT_OPEN,
	SP_ERR_SET_TO,
	SP_ERR_GET_COMM_STATE,
	SP_ERR_SET_COMM_STATE,
	SP_ERR_SET_COMM_MASK,
	SP_ERR_CREATE_OVERLAP_OBJ,
	SP_ERR_CREATE_THREAD,
	SP_ERR_PARAM,
};

typedef enum
{
	SP_BYTESIZE_5 = 5,
	SP_BYTESIZE_6,
	SP_BYTESIZE_7,
	SP_BYTESIZE_8
} sp_bytesize_t;

typedef enum
{
	SP_PARITY_NONE = 0,
	SP_PARITY_ODD,
	SP_PARITY_EVEN,
	SP_PARITY_MARK,
	SP_PARITY_SPACE
} sp_parity_t;

typedef enum
{
	SP_STOP_BITS_1 = 1,
	SP_STOP_BITS_2,
	SP_STOP_BITS_1_5
} sp_stopbits_t;

typedef enum
{
	SP_FLOW_NONE = 0,
	SP_FLOW_SOFT,
	SP_FLOW_HARD
} sp_flowcontrol_t;

#if defined(_WIN32)

#include <initguid.h>
//
#include <windows.h>
//
#include <setupapi.h>

typedef struct
{
	HDEVINFO device_info_set;
	int idx;
	struct
	{
		char port[SP_INFO_LEN];
		char description[SP_INFO_LEN];
		char hardware_id[SP_INFO_LEN];
	} info;
} sp_list_t;
#else
#include <glob.h>
#include <pthread.h>
#include <stdbool.h>

typedef struct
{
	glob_t globbuf;
	bool inited;
	size_t idx;
	struct
	{
		char port[SP_INFO_LEN];
		char description[SP_INFO_LEN];
		char hardware_id[SP_INFO_LEN];
	} info;
} sp_list_t;
#endif

typedef struct sp_t sp_t;

struct sp_t
{
	char port_name[SP_INFO_LEN];
	volatile bool thr_run;
	int thr_error;
	void (*cb_rx)(sp_t *sp, const uint8_t *data, size_t len);
	uint8_t data_rx[SP_RX_SIZE];
	void *priv;

#if defined(_WIN32)
	HANDLE fd, thr_rcv;
	wchar_t port_name_prefixed[SP_INFO_LEN];
	OVERLAPPED fd_overlap_read, fd_overlap_write, fd_overlap_evt;
	BOOL evt_waiting;
	DWORD evt_mask, evt_mask_len;
	HANDLE write_mutex;
#else
	int fd;
	pthread_t thr_rcv;
	volatile bool thr_exited;
	bool xonxoff, rtscts;
	pthread_mutex_t write_mutex;
#endif
};

const char *sp_err2_str(int code);

int sp_enumerate(sp_list_t *list);
void sp_enumerate_finish(sp_list_t *list);

int sp_open(sp_t *sp, const char *port_name, void (*cb_rx)(sp_t *sp, const uint8_t *data, size_t len), void *priv);
int sp_open_ext(sp_t *sp, const char *port_name, void (*cb_rx)(sp_t *sp, const uint8_t *data, size_t len), void *priv,
				uint32_t baudrate, sp_bytesize_t bytesize, sp_parity_t parity, sp_stopbits_t stopbits, sp_flowcontrol_t flowcontrol);
// 115200, SP_BYTESIZE_8, SP_PARITY_NONE, SP_STOP_BITS_1, SP_FLOW_NONE
void sp_close(sp_t *sp);

int sp_write(sp_t *sp, const void *data, size_t size);

int sp_flush(sp_t *sp);
int sp_flush_rx(sp_t *sp);
int sp_flush_tx(sp_t *sp);

void sp_send_break(sp_t *sp, int duration);

int sp_get_cts(sp_t *sp, bool *sts);
int sp_get_dsr(sp_t *sp, bool *sts);
int sp_get_ri(sp_t *sp, bool *sts);
int sp_get_cd(sp_t *sp, bool *sts);

int sp_set_brk(sp_t *sp, bool level);
int sp_set_rts(sp_t *sp, bool level);
int sp_set_dtr(sp_t *sp, bool level);

#define V2HEX(v) ((v) + ((v) < 0xA ? '0' : ('A' - 10)))

static inline void put_ascii(uint8_t c)
{
	if(c >= ' ' && c <= 0x7E)
		putchar((char)c);
	else if(c == 0)
	{
		putchar('\\');
		putchar('0');
	}
	else if(c == 7)
	{
		putchar('\\');
		putchar('a');
	}
	else if(c == 8)
	{
		putchar('\\');
		putchar('b');
	}
	else if(c == 9)
	{
		putchar('\\');
		putchar('t');
	}
	else if(c == 10)
	{
		putchar('\\');
		putchar('n');
	}
	else if(c == 11)
	{
		putchar('\\');
		putchar('v');
	}
	else if(c == 12)
	{
		putchar('\\');
		putchar('f');
	}
	else if(c == 13)
	{
		putchar('\\');
		putchar('r');
	}
	else if(c == 27)
	{
		putchar('\\');
		putchar('e');
	}
	else
	{
		putchar('#');
		putchar(V2HEX(c >> 4));
		putchar(V2HEX(c & 0xF));
	}
}

#endif // SP_H__