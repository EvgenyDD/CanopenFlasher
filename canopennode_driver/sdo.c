#include "sdo.h"
#include "co_wrapper.h"
#include <errno.h>
#include <sys/time.h>

#define TIME_DELTA_US(x, y) ((x.tv_sec - y.tv_sec) * 1000000LL + (x.tv_usec - y.tv_usec))

CO_SDO_abortCode_t read_SDO(CO_SDOclient_t *SDO_C, uint8_t nodeId, uint16_t index, uint8_t subIndex, uint8_t *buf, size_t bufSize, size_t *readSize, uint32_t timeout_ms)
{
	*readSize = 0;
	CO_SDO_return_t SDO_ret = CO_SDOclient_setup(SDO_C, CO_CAN_ID_SDO_CLI + nodeId, CO_CAN_ID_SDO_SRV + nodeId, nodeId);
	if(SDO_ret != CO_SDO_RT_ok_communicationEnd) return CO_SDO_AB_GENERAL;

	SDO_ret = CO_SDOclientUploadInitiate(SDO_C, index, subIndex, timeout_ms, false);
	if(SDO_ret != CO_SDO_RT_ok_communicationEnd) return CO_SDO_AB_GENERAL;

	struct timeval tprev, tnow;
	gettimeofday(&tnow, NULL);
	do
	{
		tprev = tnow;
		gettimeofday(&tnow, NULL);
		CO_SDO_abortCode_t abortCode = CO_SDO_AB_NONE;
		SDO_ret = CO_SDOclientUpload(SDO_C, TIME_DELTA_US(tnow, tprev), false, &abortCode, NULL, NULL, NULL);
		if(SDO_ret < 0) return abortCode;
#ifndef CO_SDO_HI_SPEED_MODE
		SLEEP_MS(1);
#endif
	} while(SDO_ret > 0);

	*readSize = CO_SDOclientUploadBufRead(SDO_C, buf, bufSize);

	return CO_SDO_AB_NONE;
}

CO_SDO_abortCode_t write_SDO(CO_SDOclient_t *SDO_C, uint8_t nodeId, uint16_t index, uint8_t subIndex, uint8_t *data, size_t dataSize, uint32_t timeout_ms)
{
	bool_t bufferPartial = false;

	CO_SDO_return_t SDO_ret = CO_SDOclient_setup(SDO_C, CO_CAN_ID_SDO_CLI + nodeId, CO_CAN_ID_SDO_SRV + nodeId, nodeId);
	if(SDO_ret != CO_SDO_RT_ok_communicationEnd) return CO_SDO_AB_GENERAL;

	SDO_ret = CO_SDOclientDownloadInitiate(SDO_C, index, subIndex, dataSize, timeout_ms, false);
	if(SDO_ret != CO_SDO_RT_ok_communicationEnd) return CO_SDO_AB_GENERAL;

	size_t nWritten = CO_SDOclientDownloadBufWrite(SDO_C, data, dataSize);
	if(nWritten < dataSize) bufferPartial = true;

	struct timeval tprev, tnow;
	gettimeofday(&tnow, NULL);
	do
	{
		tprev = tnow;
		gettimeofday(&tnow, NULL);
		CO_SDO_abortCode_t abortCode = CO_SDO_AB_NONE;
		SDO_ret = CO_SDOclientDownload(SDO_C, TIME_DELTA_US(tnow, tprev), false, bufferPartial, &abortCode, NULL, NULL);
		if(SDO_ret < 0) return abortCode;
#ifndef CO_SDO_HI_SPEED_MODE
		SLEEP_MS(1);
#endif
	} while(SDO_ret > 0);

	return CO_SDO_AB_NONE;
}