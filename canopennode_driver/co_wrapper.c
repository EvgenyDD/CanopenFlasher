#include "co_wrapper.h"
#include "301/CO_HBconsumer.h"
#include "CANopen.h"
#include "CO_driver_target.h"
#include "OD.h"
#include "sp.h"
#include <sys/time.h>

#define TUNE_DELAY 10

#define TIME_DELTA_US(x, y) ((x.tv_sec - y.tv_sec) * 1000000LL + (x.tv_usec - y.tv_usec))

#ifdef _WIN32
#include <windows.h>
#define SLEEP_MS(msecs) Sleep(msecs)
#else
#include <errno.h>
#include <time.h>
#define SLEEP_MS(msecs)                                                            \
	struct timespec ts = {.tv_sec = msecs / 1000, .tv_nsec = msecs % 1000 * 1000}; \
	int res;                                                                       \
	do                                                                             \
	{                                                                              \
		errno = 0;                                                                 \
		res = nanosleep(&ts, NULL);                                                \
	} while(res != 0 && errno == EINTR)
#endif

uint8_t active_can_node_id = 2;			/* Copied from CO_pending_can_node_id in the communication reset section */
static uint8_t pending_can_node_id = 2; /* read from nonvolatile memory, configurable by LSS slave */
static uint16_t pending_can_baud = 500; /* read from nonvolatile memory, configurable by LSS slave */

#define NMT_CONTROL                  \
	(CO_NMT_STARTUP_TO_OPERATIONAL | \
	 CO_NMT_ERR_ON_ERR_REG |         \
	 CO_NMT_ERR_ON_BUSOFF_HB |       \
	 CO_ERR_REG_GENERIC_ERR |        \
	 CO_ERR_REG_COMMUNICATION)

#if defined(_WIN32)
#include <process.h>
static unsigned int __stdcall thr_poll(void *data)
#else
static void *thr_rcv(void *data)
#endif
{
	CO_t *co = (CO_t *)data;
	struct timeval tprev, tnow;
	gettimeofday(&tnow, NULL);
	while(co->CANmodule->thr_run)
	{
		tprev = tnow;
		gettimeofday(&tnow, NULL);
		CO_process(co, false, TIME_DELTA_US(tnow, tprev), NULL);
		SLEEP_MS(TUNE_DELAY);
	}
#if !defined(_WIN32)
	co->CANmodule->thr_exited = true;
#endif
	return 0;
}

int co_wrapper_init(CO_t **co, sp_t *sp)
{
	*co = CO_new(NULL, NULL);
	if(!(*co)) return 2;

	(*co)->CANmodule->CANptr = sp;
	(*co)->CANmodule->CANnormal = false;

	CO_CANsetConfigurationMode((*co)->CANmodule->CANptr);
	CO_CANmodule_disable((*co)->CANmodule);
	if(CO_CANinit(*co, (*co)->CANmodule->CANptr, pending_can_baud) != CO_ERROR_NO) return 3;

	OD_PERSIST_COMM.x1017_producerHeartbeatTime = 0;
	for(uint32_t i = 0; i < 127; i++)
	{
		OD_PERSIST_COMM.x1016_consumerHeartbeatTime[i] = ((i + 1) << 16) | 2500;
	}

	active_can_node_id = pending_can_node_id;
	uint32_t errInfo = 0;
	CO_ReturnError_t err = CO_CANopenInit(*co,		   /* CANopen object */
										  NULL,		   /* alternate NMT */
										  NULL,		   /* alternate em */
										  OD,		   /* Object dictionary */
										  NULL,		   /* Optional OD_statusBits */
										  NMT_CONTROL, /* CO_NMT_control_t */
										  0,		   /* firstHBTime_ms */
										  1000,		   /* SDOserverTimeoutTime_ms */
										  500,		   /* SDOclientTimeoutTime_ms */
										  false,	   /* SDOclientBlockTransfer */
										  active_can_node_id,
										  &errInfo);

	if(err != CO_ERROR_NO && err != CO_ERROR_NODE_ID_UNCONFIGURED_LSS) return err;

	err = CO_CANopenInitPDO(*co, (*co)->em, OD, active_can_node_id, &errInfo);
	if(err != CO_ERROR_NO && err != CO_ERROR_NODE_ID_UNCONFIGURED_LSS) return 5;

	CO_CANsetNormalMode((*co)->CANmodule);

	(*co)->CANmodule->slcan.pos = 0;

	(*co)->CANmodule->thr_run = true;
#if defined(_WIN32)
	(*co)->CANmodule->thr_rcv = (HANDLE)_beginthreadex(0, 0, &thr_poll, *co, 0, 0);
	if(!(*co)->CANmodule->thr_rcv || (*co)->CANmodule->thr_rcv == INVALID_HANDLE_VALUE) return 6;
#else
	if(pthread_create(&((*co)->CANmodule->thr_rcv), NULL, thr_rcv, *co)) return 6;
#endif

	return 0;
}

void co_wrapper_deinit(CO_t **co)
{
	if(*co)
	{
#if defined(_WIN32)
		if(WaitForSingleObject((*co)->CANmodule->thr_rcv, 0) == WAIT_OBJECT_0) printf("[CO] thread exited!\n");
		(*co)->CANmodule->thr_run = false;
		if((*co)->CANmodule->thr_rcv) WaitForSingleObject((*co)->CANmodule->thr_rcv, INFINITE);

#else
		if((*co)->CANmodule->thr_exited) printf("[CO] thread exited!\n");
		(*co)->CANmodule->thr_run = false;
		pthread_join((*co)->CANmodule->thr_rcv, NULL);
#endif
		CO_delete(*co);
		*co = NULL;
	}
}
