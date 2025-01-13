// version: 1
#include "sp.h"
#include <stdio.h>

#if defined(_WIN32)
#include <fcntl.h>
#include <process.h>

#define SERIAL_OVERLAP_MODE

#define MIN(a, b) ((a) < (b) ? (a) : (b))

static unsigned int __stdcall thr_rcv(void *data)
{
	sp_t *sp = (sp_t *)data;
	DWORD bytes_to_read = 0, err, readed;
	COMSTAT stat;
	while(sp->thr_run)
	{
		if(!sp->evt_waiting)
		{
			sp->evt_mask = EV_RXCHAR;
			if(!WaitCommEvent(sp->fd, &sp->evt_mask, &sp->fd_overlap_evt))
			{
				if(GetLastError() != ERROR_IO_PENDING)
				{
					sp->thr_error = SP_ERR_WAIT_COMM_EVENT;
					return 0;
				}
				sp->evt_waiting = true;
			}
			else
			{
				ClearCommError(sp->fd, &err, &stat);
				bytes_to_read = stat.cbInQue;
				sp->evt_waiting = false;
			}
		}
		if(sp->evt_waiting)
		{
			switch(WaitForSingleObject(sp->fd_overlap_evt.hEvent, INFINITE))
			{
			case WAIT_OBJECT_0:
				GetOverlappedResult(sp->fd, &sp->fd_overlap_evt, &sp->evt_mask_len, false);
				ResetEvent(sp->fd_overlap_evt.hEvent);
				ClearCommError(sp->fd, &err, &stat);
				bytes_to_read = stat.cbInQue;
				sp->evt_waiting = false;
				break;
			case WAIT_TIMEOUT:
				bytes_to_read = 0;
				break;
			default:
				sp->evt_waiting = false;
				sp->thr_error = SP_ERR_GET_OVERLAP;
				return 0;
			}
		}
		if(bytes_to_read)
		{
			for(DWORD p = 0; p < bytes_to_read;)
			{
				DWORD sz = bytes_to_read - p;
				if(sz > SP_RX_SIZE) sz = SP_RX_SIZE;
				p += sz;
				if(!ReadFile(sp->fd, sp->data_rx, sz, &readed, &sp->fd_overlap_read))
				{
					sp->thr_error = SP_ERR_READ;
					return 0;
				}
				if(readed > 0) sp->cb_rx(sp, sp->data_rx, readed);
			}
		}
	}
	return 0;
}

int sp_open(sp_t *sp, const char *port_name, void (*cb_rx)(sp_t *sp, const uint8_t *data, size_t len), void *priv)
{
	sp->write_mutex = CreateMutex(NULL, false, NULL);
	sp->cb_rx = cb_rx;
	sp->priv = priv;
	if(port_name) memcpy(sp->port_name, port_name, MIN(strlen(port_name), sizeof(sp->port_name)));
	snwprintf(sp->port_name_prefixed, sizeof(sp->port_name_prefixed), L"\\\\.\\%s", sp->port_name);

#ifdef SERIAL_OVERLAP_MODE
	sp->fd = CreateFileW(sp->port_name_prefixed, GENERIC_READ | GENERIC_WRITE, 0, NULL, OPEN_EXISTING, FILE_FLAG_OVERLAPPED, NULL);
#else
	sp->fd = CreateFileW(sp->port_name_prefixed, GENERIC_READ | GENERIC_WRITE, 0, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
#endif
	if(sp->fd == INVALID_HANDLE_VALUE)
	{
		switch(GetLastError())
		{
		case ERROR_FILE_NOT_FOUND: return SP_ERR_PORT_NOT_EXIST;
		case ERROR_ACCESS_DENIED: return SP_ERR_PORT_OPEN_BUSY;
		case ERROR_PATH_NOT_FOUND: return SP_ERR_PORT_OPEN_INVALID;
		default: return SP_ERR_PORT_OPEN;
		}
	}

	COMMTIMEOUTS timeouts = {0};
#ifndef SERIAL_OVERLAP_MODE
	timeouts.ReadIntervalTimeout = 5 /*inter_byte_timeout*/;			   // nummber of milliseconds between bytes received to timeout on
	timeouts.ReadTotalTimeoutConstant = 5 /*read_timeout_constant*/;	   // constant number of milliseconds to wait after calling read
	timeouts.ReadTotalTimeoutMultiplier = 1 /*read_timeout_multiplier*/;   // multiplier against the number of requested bytes to wait after calling read
	timeouts.WriteTotalTimeoutConstant = 5 /*write_timeout_constant*/;	   // constant number of milliseconds to wait after calling write
	timeouts.WriteTotalTimeoutMultiplier = 1 /*write_timeout_multiplier*/; // multiplier against the number of requested bytes to wait after calling write
#endif
	if(!SetCommTimeouts(sp->fd, &timeouts)) return SP_ERR_SET_TO;

#ifdef SERIAL_OVERLAP_MODE
	if(!SetCommMask(sp->fd, EV_RXCHAR)) return SP_ERR_SET_COMM_MASK;
	sp->fd_overlap_read.hEvent = CreateEvent(NULL, true, false, NULL);
	sp->fd_overlap_write.hEvent = CreateEvent(NULL, true, false, NULL);
	sp->fd_overlap_evt.hEvent = CreateEvent(NULL, true, false, NULL);
	if(!sp->fd_overlap_read.hEvent || !sp->fd_overlap_write.hEvent || !sp->fd_overlap_evt.hEvent) return SP_ERR_CREATE_OVERLAP_OBJ;
	PurgeComm(sp->fd, PURGE_RXCLEAR | PURGE_TXCLEAR | PURGE_TXABORT | PURGE_RXABORT);
#endif

	sp_flush(sp);
	sp->thr_run = true;
	sp->thr_rcv = (HANDLE)_beginthreadex(0, 0, &thr_rcv, sp, 0, 0);
	if(!sp->thr_rcv || sp->thr_rcv == INVALID_HANDLE_VALUE) return SP_ERR_CREATE_THREAD;

	return 0;
}

int sp_open_ext(sp_t *sp, const char *port_name, void (*cb_rx)(sp_t *sp, const uint8_t *data, size_t len), void *priv,
				uint32_t baudrate, sp_bytesize_t bytesize, sp_parity_t parity, sp_stopbits_t stopbits, sp_flowcontrol_t flowcontrol)
{
	int sts = sp_open(sp, port_name, cb_rx, priv);
	if(sts) return sts;

	DCB dcbSerialParams = {0};
	dcbSerialParams.DCBlength = sizeof(dcbSerialParams);
	if(!GetCommState(sp->fd, &dcbSerialParams)) return SP_ERR_GET_COMM_STATE;

	switch(baudrate)
	{
	case 110: dcbSerialParams.BaudRate = CBR_110; break;
	case 300: dcbSerialParams.BaudRate = CBR_300; break;
	case 600: dcbSerialParams.BaudRate = CBR_600; break;
	case 1200: dcbSerialParams.BaudRate = CBR_1200; break;
	case 2400: dcbSerialParams.BaudRate = CBR_2400; break;
	case 4800: dcbSerialParams.BaudRate = CBR_4800; break;
	case 9600: dcbSerialParams.BaudRate = CBR_9600; break;
	case 14400: dcbSerialParams.BaudRate = CBR_14400; break;
	case 19200: dcbSerialParams.BaudRate = CBR_19200; break;
	case 57600: dcbSerialParams.BaudRate = CBR_57600; break;
	case 38400: dcbSerialParams.BaudRate = CBR_38400; break;
	case 115200: dcbSerialParams.BaudRate = CBR_115200; break;
	case 128000: dcbSerialParams.BaudRate = CBR_128000; break;
	case 256000: dcbSerialParams.BaudRate = CBR_256000; break;
	default: dcbSerialParams.BaudRate = baudrate; break;
	}

	switch(bytesize)
	{
	default:
	case SP_BYTESIZE_8: dcbSerialParams.ByteSize = 8; break;
	case SP_BYTESIZE_7: dcbSerialParams.ByteSize = 7; break;
	case SP_BYTESIZE_6: dcbSerialParams.ByteSize = 6; break;
	case SP_BYTESIZE_5: dcbSerialParams.ByteSize = 5; break;
	}

	switch(stopbits)
	{
	default:
	case SP_STOP_BITS_1: dcbSerialParams.StopBits = ONESTOPBIT; break;
	case SP_STOP_BITS_1_5: dcbSerialParams.StopBits = ONE5STOPBITS; break;
	case SP_STOP_BITS_2: break;
	}

	switch(parity)
	{
	case SP_PARITY_EVEN: dcbSerialParams.Parity = EVENPARITY; break;
	case SP_PARITY_ODD: dcbSerialParams.Parity = ODDPARITY; break;
	case SP_PARITY_MARK: dcbSerialParams.Parity = MARKPARITY; break;
	case SP_PARITY_SPACE: dcbSerialParams.Parity = SPACEPARITY; break;
	default:
	case SP_PARITY_NONE: dcbSerialParams.Parity = NOPARITY; break;
	}

	switch(flowcontrol)
	{
	case SP_FLOW_SOFT:
		dcbSerialParams.fOutxCtsFlow = false;
		dcbSerialParams.fRtsControl = RTS_CONTROL_DISABLE;
		dcbSerialParams.fOutX = true;
		dcbSerialParams.fInX = true;
		break;
	case SP_FLOW_HARD:
		dcbSerialParams.fOutxCtsFlow = true;
		dcbSerialParams.fRtsControl = RTS_CONTROL_HANDSHAKE;
		dcbSerialParams.fOutX = false;
		dcbSerialParams.fInX = false;
		break;
	default:
	case SP_FLOW_NONE:
		dcbSerialParams.fOutxCtsFlow = false;
		dcbSerialParams.fRtsControl = RTS_CONTROL_DISABLE;
		dcbSerialParams.fOutX = false;
		dcbSerialParams.fInX = false;
		break;
	}

	if(!SetCommState(sp->fd, &dcbSerialParams)) return SP_ERR_SET_COMM_STATE;
	return 0;
}

void sp_close(sp_t *sp)
{
	if(WaitForSingleObject(sp->thr_rcv, 0) == WAIT_OBJECT_0) printf("[SP] thread exited!\n");
	sp->thr_run = false;
	SetCommMask(sp->fd, EV_TXEMPTY);
	if(sp->thr_rcv) WaitForSingleObject(sp->thr_rcv, INFINITE);
	if(sp->thr_error) printf("[SP] thread error: %s\n", sp_err2_str(sp->thr_error));

	if(sp->thr_rcv) CloseHandle(sp->thr_rcv);
	if(sp->fd != INVALID_HANDLE_VALUE && sp->fd) CloseHandle(sp->fd);
	if(sp->write_mutex) CloseHandle(sp->write_mutex);
	if(sp->fd_overlap_read.hEvent) CloseHandle(sp->fd_overlap_read.hEvent);
	if(sp->fd_overlap_write.hEvent) CloseHandle(sp->fd_overlap_write.hEvent);
	if(sp->fd_overlap_evt.hEvent) CloseHandle(sp->fd_overlap_evt.hEvent);

	sp->thr_rcv = NULL;
	sp->fd = INVALID_HANDLE_VALUE;
	sp->write_mutex = NULL;
	sp->fd_overlap_read.hEvent = sp->fd_overlap_write.hEvent = sp->fd_overlap_evt.hEvent = NULL;
}

int sp_write(sp_t *sp, const void *data, size_t size)
{
	if(WaitForSingleObject(sp->write_mutex, INFINITE) != WAIT_OBJECT_0) return SP_ERR_WR_LOCK;
	DWORD bytes_written = 0;
#ifdef SERIAL_OVERLAP_MODE
	if(!WriteFile(sp->fd, data, (DWORD)size, &bytes_written, &sp->fd_overlap_write))
	{
		switch(WaitForSingleObject(sp->fd_overlap_write.hEvent, /*INFINITE*/ SP_WRITE_TIMEOUT_MS))
		{
		case WAIT_OBJECT_0:
			GetOverlappedResult(sp->fd, &sp->fd_overlap_write, &bytes_written, false);
			ResetEvent(&sp->fd_overlap_write.hEvent);
			break;
		case WAIT_TIMEOUT:
		default: bytes_written = 0; break;
		}
	}
#else
	WriteFile(sp->fd, data, (DWORD)size, &bytes_written, NULL);
#endif
	if(!ReleaseMutex(sp->write_mutex)) return SP_ERR_WR_UNLOCK;
	return size == bytes_written ? 0 : (bytes_written == 0 ? SP_ERR_WR_ZERO : SP_ERR_WR_LESS);
}

int sp_flush(sp_t *sp)
{
	if(WaitForSingleObject(sp->write_mutex, INFINITE) != WAIT_OBJECT_0) return SP_ERR_WR_LOCK;
	FlushFileBuffers(sp->fd);
	if(!ReleaseMutex(sp->write_mutex)) return SP_ERR_WR_UNLOCK;
	return 0;
}

int sp_flush_rx(sp_t *sp)
{
	PurgeComm(sp->fd, PURGE_RXCLEAR);
	return 0;
}

int sp_flush_tx(sp_t *sp)
{
	if(WaitForSingleObject(sp->write_mutex, INFINITE) != WAIT_OBJECT_0) return SP_ERR_WR_LOCK;
	PurgeComm(sp->fd, PURGE_TXCLEAR);
	if(!ReleaseMutex(sp->write_mutex)) return SP_ERR_WR_UNLOCK;
	return 0;
}

int sp_get_cts(sp_t *sp, bool *sts)
{
	DWORD dwModemStatus;
	if(!GetCommModemStatus(sp->fd, &dwModemStatus)) return SP_ERR_GET_MDM_STS;
	*sts = (MS_CTS_ON & dwModemStatus) != 0;
	return 0;
}

int sp_get_dsr(sp_t *sp, bool *sts)
{
	DWORD dwModemStatus;
	if(!GetCommModemStatus(sp->fd, &dwModemStatus)) return SP_ERR_GET_MDM_STS;
	*sts = (MS_DSR_ON & dwModemStatus) != 0;
	return 0;
}

int sp_get_ri(sp_t *sp, bool *sts)
{
	DWORD dwModemStatus;
	if(!GetCommModemStatus(sp->fd, &dwModemStatus)) return SP_ERR_GET_MDM_STS;
	*sts = (MS_RING_ON & dwModemStatus) != 0;
	return 0;
}

int sp_get_cd(sp_t *sp, bool *sts)
{
	DWORD dwModemStatus;
	if(!GetCommModemStatus(sp->fd, &dwModemStatus)) return SP_ERR_GET_MDM_STS;
	*sts = (MS_RLSD_ON & dwModemStatus) != 0;
	return 0;
}

int sp_set_brk(sp_t *sp, bool level) { return (!EscapeCommFunction(sp->fd, level ? SETBREAK : CLRBREAK)) ? SP_ERR_SET_MDM_STS : 0; }
int sp_set_rts(sp_t *sp, bool level) { return (!EscapeCommFunction(sp->fd, level ? SETRTS : CLRRTS)) ? SP_ERR_SET_MDM_STS : 0; }
int sp_set_dtr(sp_t *sp, bool level) { return (!EscapeCommFunction(sp->fd, level ? SETDTR : CLRDTR)) ? SP_ERR_SET_MDM_STS : 0; }
#endif
