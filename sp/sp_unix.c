// version: 1
#include "sp.h"

#if !defined(_WIN32)
#include <errno.h>
#include <fcntl.h>
#include <paths.h>
#include <poll.h>
#include <pthread.h>
#include <stdio.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/param.h>
#include <sys/select.h>
#include <sys/signal.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sysexits.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

#if defined(__linux__)
#include <linux/serial.h>
#endif

#ifndef TIOCINQ
#ifdef FIONREAD
#define TIOCINQ FIONREAD
#else
#define TIOCINQ 0x541B
#endif
#endif

static void *thr_rcv(void *arg)
{
	sp_t *sp = (sp_t *)arg;
	fd_set rfds;
	while(sp->thr_run)
	{
		FD_ZERO(&rfds);
		FD_SET(sp->fd, &rfds);
		struct timeval tv = {.tv_sec = 0, .tv_usec = 10 /*ms*/ * 1000};
		int n = select(sp->fd + 1, &rfds, 0, 0, &tv);
		if(n > 0)
		{
			if(FD_ISSET(sp->fd, &rfds))
			{
				// int bytes_available = 0;
				// if(-1 != ioctl(sp->fd, TIOCINQ, &bytes_available)) {}
				uint32_t readed = read(sp->fd, sp->data_rx, SP_RX_SIZE);
				if(readed <= 0)
				{
					sp->thr_error = SP_ERR_READ;
					sp->thr_exited = true;
					return 0;
				}
				sp->cb_rx(sp, sp->data_rx, readed);
			}
		}
		else if(n < 0)
		{
			sp->thr_error = SP_ERR_READ;
			sp->thr_exited = true;
			return 0;
		}
	}
	sp->thr_exited = true;
	return 0;
}

int sp_open(sp_t *sp, const char *port_name, void (*cb_rx)(sp_t *sp, const uint8_t *data, size_t len), void *priv)
{
	pthread_mutex_init(&sp->write_mutex, NULL);
	sp->cb_rx = cb_rx;
	sp->priv = priv;
	if(port_name) memcpy(sp->port_name, port_name, MIN(strlen(port_name), sizeof(sp->port_name)));

OPEN_AGAIN:
	sp->fd = open(sp->port_name, O_RDWR | O_NOCTTY | O_NONBLOCK);
	if(sp->fd == -1)
	{
		switch(errno)
		{
		case EINTR: printf("SP: recurse\n"); goto OPEN_AGAIN; // Recurse because this is a recoverable error
		case EACCES: return SP_ERR_PORT_OPEN_BUSY;
		case ENXIO: return SP_ERR_PORT_NOT_EXIST;
		case ENOENT: return SP_ERR_PORT_OPEN_INVALID;
		default: return SP_ERR_PORT_OPEN;
		}
	}

	struct termios options;
	tcgetattr(sp->fd, &options);
	options.c_iflag &= ~(INLCR | IGNCR | ICRNL | IXON | IXOFF);
	options.c_oflag &= ~(ONLCR | OCRNL);
	options.c_lflag &= ~(ECHO | ECHONL | ICANON | ISIG | IEXTEN);
	tcsetattr(sp->fd, TCSANOW, &options);

	sp_flush(sp);
	sp->thr_run = true;
	if(pthread_create(&sp->thr_rcv, NULL, thr_rcv, sp)) return SP_ERR_CREATE_THREAD;

	return 0;
}

int sp_open_ext(sp_t *sp, const char *port_name, void (*cb_rx)(sp_t *sp, const uint8_t *data, size_t len), void *priv,
				uint32_t baudrate, sp_bytesize_t bytesize, sp_parity_t parity, sp_stopbits_t stopbits, sp_flowcontrol_t flowcontrol)
{
	int sts = sp_open(sp, port_name, cb_rx, priv);
	if(sts) return sts;

	struct termios options;
	if(tcgetattr(sp->fd, &options) == -1) return SP_ERR_GET_COMM_STATE;

	options.c_cflag |= CLOCAL | CREAD;
	options.c_lflag &= ~(ICANON | ECHO | ECHOE | ECHOK | ECHONL | ISIG | IEXTEN); //|ECHOPRT
	options.c_oflag &= ~(OPOST);
	options.c_iflag &= ~(INLCR | IGNCR | ICRNL | IGNBRK);
#ifdef IUCLC
	options.c_iflag &= ~IUCLC;
#endif
#ifdef PARMRK
	options.c_iflag &= ~PARMRK;
#endif

	bool custom_baud = false;
	speed_t baud;
	switch(baudrate)
	{
	case 0: baud = B0; break;
	case 50: baud = B50; break;
	case 75: baud = B75; break;
	case 110: baud = B110; break;
	case 134: baud = B134; break;
	case 150: baud = B150; break;
	case 200: baud = B200; break;
	case 300: baud = B300; break;
	case 600: baud = B600; break;
	case 1200: baud = B1200; break;
	case 1800: baud = B1800; break;
	case 2400: baud = B2400; break;
	case 4800: baud = B4800; break;
	case 9600: baud = B9600; break;
	case 19200: baud = B19200; break;
	case 57600: baud = B57600; break;
	case 38400: baud = B38400; break;
	case 115200: baud = B115200; break;
	// case 128000: baud = B128000; break;
	case 230400: baud = B230400; break;
	// case 256000: baud = B256000; break;
	case 460800: baud = B460800; break;
	case 500000: baud = B500000; break;
	case 576000: baud = B576000; break;
	case 921600: baud = B921600; break;
	case 1000000: baud = B1000000; break;
	case 1152000: baud = B1152000; break;
	case 1500000: baud = B1500000; break;
	case 2000000: baud = B2000000; break;
	case 2500000: baud = B2500000; break;
	case 3000000: baud = B3000000; break;
	default:
		custom_baud = true;
#if defined(__linux__) && defined(TIOCSSERIAL)
		struct serial_struct ser;
		if(-1 == ioctl(sp->fd, TIOCGSERIAL, &ser)) return -25;
		ser.custom_divisor = ser.baud_base / (int)baudrate;
		ser.flags &= ~ASYNC_SPD_MASK;
		ser.flags |= ASYNC_SPD_CUST;
		if(-1 == ioctl(sp->fd, TIOCSSERIAL, &ser)) return -26;
#endif
	}
	if(custom_baud == false)
	{
#ifdef _BSD_SOURCE
		cfsetspeed(&options, baud);
#else
		cfsetispeed(&options, baud);
		cfsetospeed(&options, baud);
#endif
	}

	options.c_cflag &= (tcflag_t)~CSIZE;
	switch(bytesize)
	{
	case SP_BYTESIZE_5: options.c_cflag |= CS5; break;
	case SP_BYTESIZE_6: options.c_cflag |= CS6; break;
	case SP_BYTESIZE_7: options.c_cflag |= CS7; break;
	default:
	case SP_BYTESIZE_8: options.c_cflag |= CS8; break;
	}

	if(stopbits == SP_STOP_BITS_1)
		options.c_cflag &= (tcflag_t) ~(CSTOPB);
	else if(stopbits == SP_STOP_BITS_1_5)
		options.c_cflag |= (CSTOPB); // 1.5 same as 2, there is no POSIX support for 1.5
	else if(stopbits == SP_STOP_BITS_2)
		options.c_cflag |= (CSTOPB);

	options.c_iflag &= (tcflag_t) ~(INPCK | ISTRIP);
	if(parity == SP_PARITY_NONE)
		options.c_cflag &= (tcflag_t) ~(PARENB | PARODD);
	else if(parity == SP_PARITY_ODD)
		options.c_cflag |= (PARENB | PARODD);
	else if(parity == SP_PARITY_EVEN)
	{
		options.c_cflag &= (tcflag_t) ~(PARODD);
		options.c_cflag |= (PARENB);
	}
#ifdef CMSPAR
	else if(parity == SP_PARITY_MARK)
		options.c_cflag |= (PARENB | CMSPAR | PARODD);
	else if(parity == SP_PARITY_SPACE)
	{
		options.c_cflag |= (PARENB | CMSPAR);
		options.c_cflag &= (tcflag_t) ~(PARODD);
	}
#else
	else if(parity == SP_PARITY_MARK || parity == SP_PARITY_SPACE)
		return SP_ERR_PARAM; // OS does not support mark or space parity
#endif

	if(flowcontrol == SP_FLOW_NONE)
	{
		sp->xonxoff = false;
		sp->rtscts = false;
	}
	else if(flowcontrol == SP_FLOW_SOFT)
	{
		sp->xonxoff = true;
		sp->rtscts = false;
	}
	else if(flowcontrol == SP_FLOW_HARD)
	{
		sp->xonxoff = false;
		sp->rtscts = true;
	}
#ifdef IXANY
	if(sp->xonxoff)
		options.c_iflag |= (IXON | IXOFF); //|IXANY)
	else
		options.c_iflag &= ~(IXON | IXOFF | IXANY);
#else
	if(xonxoff)
		options.c_iflag |= (IXON | IXOFF);
	else
		options.c_iflag &= (tcflag_t) ~(IXON | IXOFF);
#endif
#ifdef CRTSCTS
	if(sp->rtscts)
		options.c_cflag |= (CRTSCTS);
	else
		options.c_cflag &= ~(CRTSCTS);
#elif defined CNEW_RTSCTS
	if(rtscts)
		options.c_cflag |= (CNEW_RTSCTS);
	else
		options.c_cflag &= (unsigned long)~(CNEW_RTSCTS);
#else
#error "OS Support seems wrong"
#endif

	// http://www.unixwiz.net/techtips/termios-vmin-vtime.html this basically sets the read call up to be a polling read, but we are using select to ensure there is data available to read before each call, so we should never needlessly poll
	options.c_cc[VMIN] = 0;
	options.c_cc[VTIME] = 0;

	if(tcsetattr(sp->fd, TCSANOW, &options) == -1) return SP_ERR_SET_COMM_STATE;
	return 0;
}

void sp_close(sp_t *sp)
{
	if(sp->thr_exited) printf("[SP] thread exited!\n");
	sp->thr_run = false;
	pthread_join(sp->thr_rcv, NULL);
	if(sp->thr_error) printf("[SP] thread error: %s\n", sp_err2_str(sp->thr_error));

	if(sp->fd != -1 && sp->fd) close(sp->fd);
	pthread_mutex_destroy(&sp->write_mutex);

	sp->fd = -1;
}

int sp_write(sp_t *sp, const void *data, size_t size)
{
	if(pthread_mutex_lock(&sp->write_mutex)) return SP_ERR_WR_LOCK;
	int bytes_written = 0;
	struct pollfd fds = {.fd = sp->fd, .events = POLLOUT};
	poll(&fds, 1, SP_WRITE_TIMEOUT_MS);
	if(fds.revents & POLLOUT)
	{
		bytes_written = write(sp->fd, data, size);
		tcdrain(sp->fd);
	}
	if(pthread_mutex_unlock(&sp->write_mutex)) return SP_ERR_WR_UNLOCK;
	return (int)size == bytes_written ? 0 : (bytes_written <= 0 ? SP_ERR_WR_ZERO : SP_ERR_WR_LESS);
}

int sp_flush(sp_t *sp)
{
	if(pthread_mutex_lock(&sp->write_mutex)) return SP_ERR_WR_LOCK;
	tcdrain(sp->fd);
	if(pthread_mutex_unlock(&sp->write_mutex)) return SP_ERR_WR_UNLOCK;
	return 0;
}

int sp_flush_rx(sp_t *sp)
{
	tcflush(sp->fd, TCIFLUSH);
	return 0;
}

int sp_flush_tx(sp_t *sp)
{
	if(pthread_mutex_lock(&sp->write_mutex)) return SP_ERR_WR_LOCK;
	tcflush(sp->fd, TCOFLUSH);
	if(pthread_mutex_unlock(&sp->write_mutex)) return SP_ERR_WR_UNLOCK;
	return 0;
}

void sp_send_break(sp_t *sp, int duration)
{
	tcsendbreak(sp->fd, (int)(duration / 4));
}

int sp_get_cts(sp_t *sp, bool *sts)
{
	int status;
	if(-1 == ioctl(sp->fd, TIOCMGET, &status)) return SP_ERR_GET_MDM_STS;
	*sts = 0 != (status & TIOCM_CTS);
	return 0;
}

int sp_get_dsr(sp_t *sp, bool *sts)
{
	int status;
	if(-1 == ioctl(sp->fd, TIOCMGET, &status)) return SP_ERR_GET_MDM_STS;
	*sts = 0 != (status & TIOCM_DSR);
	return 0;
}

int sp_get_ri(sp_t *sp, bool *sts)
{
	int status;
	if(-1 == ioctl(sp->fd, TIOCMGET, &status)) return SP_ERR_GET_MDM_STS;
	*sts = 0 != (status & TIOCM_RI);
	return 0;
}

int sp_get_cd(sp_t *sp, bool *sts)
{
	int status;
	if(-1 == ioctl(sp->fd, TIOCMGET, &status)) return SP_ERR_GET_MDM_STS;
	*sts = 0 != (status & TIOCM_CD);
	return 0;
}

int sp_set_brk(sp_t *sp, bool level) { return -1 == ioctl(sp->fd, level ? TIOCSBRK : TIOCCBRK) ? SP_ERR_SET_MDM_STS : 0; }

int sp_set_rts(sp_t *sp, bool level)
{
	int command = TIOCM_RTS;
	return -1 == ioctl(sp->fd, level ? TIOCMBIS : TIOCMBIC, &command) ? SP_ERR_SET_MDM_STS : 0;
}

int sp_set_dtr(sp_t *sp, bool level)
{
	int command = TIOCM_DTR;
	return -1 == ioctl(sp->fd, level ? TIOCMBIS : TIOCMBIC, &command) ? SP_ERR_SET_MDM_STS : 0;
}
#endif