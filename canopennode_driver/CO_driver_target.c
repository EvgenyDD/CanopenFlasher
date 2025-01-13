#include "CO_driver_target.h"
#include "301/CO_driver.h"
#include "slcan.h"
#include "sp.h"

void CO_CANsetConfigurationMode(void *CANptr) {}

void CO_CANsetNormalMode(CO_CANmodule_t *CANmodule) { CANmodule->CANnormal = true; }

int CO_rx(void *priv, can_msg_t *msg);
int CO_rx(void *priv, can_msg_t *msg)
{
#ifdef CO_FRAME_RX_CB
	cb_co_frame_rx(priv, msg);
#endif
	if(msg->IDE || msg->RTR) return -1;

	// printf(">x%x %d\n", msg->id.std, msg->DLC);

	CO_CANmodule_t *can_module = (CO_CANmodule_t *)priv;
	CO_CANrx_t *buffer = NULL; /* receive message buffer from CO_CANmodule_t object. */
	bool_t msgMatched = false;

	CO_CANrx_t rcv_msg = {.ident = msg->id.std, .DLC = msg->DLC};
	memcpy(rcv_msg.data, msg->data, msg->DLC);

	// CAN module filters are not used, message with any standard 11-bit identifier
	// has been received. Search rxArray form CANmodule for the same CAN-ID
	buffer = &can_module->rxArray[0];
	uint16_t index;
	for(index = can_module->rxSize; index > 0U; index--)
	{
		if(((rcv_msg.ident ^ buffer->ident) & buffer->mask) == 0U)
		{
			msgMatched = true;
			break;
		}
		buffer++;
	}

	if(msgMatched && (buffer != NULL) && (buffer->CANrx_callback != NULL)) buffer->CANrx_callback(buffer->object, (void *)&rcv_msg);
	return 0;
}

CO_ReturnError_t CO_CANmodule_init(CO_CANmodule_t *CANmodule, void *CANptr, CO_CANrx_t rxArray[], uint16_t rxSize,
								   CO_CANtx_t txArray[], uint16_t txSize, uint16_t can_bitrate)
{
	if(CANmodule == NULL || rxArray == NULL || txArray == NULL) return CO_ERROR_ILLEGAL_ARGUMENT;

	CANmodule->CANptr = CANptr; // sp_t
	CANmodule->rxArray = rxArray;
	CANmodule->rxSize = rxSize;
	CANmodule->txArray = txArray;
	CANmodule->txSize = txSize;
	CANmodule->CANerrorStatus = 0;
	CANmodule->CANnormal = false;
	CANmodule->useCANrxFilters = false;
	CANmodule->bufferInhibitFlag = false;
	CANmodule->firstCANtxMessage = true;
	CANmodule->CANtxCount = 0U;
	CANmodule->errOld = 0U;

	for(uint16_t i = 0U; i < rxSize; i++)
	{
		rxArray[i].ident = 0U;
		rxArray[i].mask = 0xFFFFU;
		rxArray[i].object = NULL;
		rxArray[i].CANrx_callback = NULL;
	}
	for(uint16_t i = 0U; i < txSize; i++)
	{
		txArray[i].bufferFull = false;
	}
	return CO_ERROR_NO;
}

void CO_CANmodule_disable(CO_CANmodule_t *CANmodule) {}

CO_ReturnError_t CO_CANrxBufferInit(CO_CANmodule_t *CANmodule, uint16_t index, uint16_t ident, uint16_t mask, bool_t rtr,
									void *object, void (*CANrx_callback)(void *object, void *message))
{
	if(CANmodule && object && CANrx_callback && (index < CANmodule->rxSize))
	{
		CO_CANrx_t *buffer = &CANmodule->rxArray[index];
		buffer->object = object;
		buffer->CANrx_callback = CANrx_callback;
		buffer->ident = ident & 0x07FFU;
		if(rtr) buffer->ident |= 0x0800U;
		buffer->mask = (mask & 0x07FFU) /* | 0x0800U*/;
		return CO_ERROR_NO;
	}
	return CO_ERROR_ILLEGAL_ARGUMENT;
}

CO_CANtx_t *CO_CANtxBufferInit(CO_CANmodule_t *CANmodule, uint16_t index, uint16_t ident, bool_t rtr, uint8_t noOfBytes, bool_t syncFlag)
{
	if(CANmodule && (index < CANmodule->txSize))
	{
		CANmodule->txArray[index].ident = (uint32_t)ident & 0x07FFU;
		CANmodule->txArray[index].DLC = noOfBytes & 0xFU;
		CANmodule->txArray[index].bufferFull = false;
		CANmodule->txArray[index].syncFlag = syncFlag;
		return &CANmodule->txArray[index];
	}
	return NULL;
}

CO_ReturnError_t CO_CANsend(CO_CANmodule_t *CANmodule, CO_CANtx_t *buffer)
{
	CO_ReturnError_t err = CO_ERROR_NO;

	if(buffer->bufferFull)
	{
		if(!CANmodule->firstCANtxMessage) CANmodule->CANerrorStatus |= CO_CAN_ERRTX_OVERFLOW; /* don't set error, if bootup message is still on buffers */
		err = CO_ERROR_TX_OVERFLOW;
	}

	CO_LOCK_CAN_SEND(CANmodule);
	sp_t *sp = (sp_t *)CANmodule->CANptr;

	can_msg_t tx_msg = {.id.std = buffer->ident, .DLC = buffer->DLC};
	memcpy(tx_msg.data, buffer->data, buffer->DLC);

	slcan_tx(sp, &tx_msg);
#ifdef CO_FRAME_TX_CB
	cb_co_frame_tx(sp, &tx_msg);
#endif
	CANmodule->firstCANtxMessage = false; // first CAN message (bootup) was sent successfully
	CANmodule->bufferInhibitFlag = false; // clear flag from previous message

	/* if CAN TX buffer is free, copy message to it */
	// if(can_drv_tx(dev, buffer->ident, buffer->DLC, buffer->data) > 0 && CANmodule->CANtxCount == 0)
	// {
	// 	CANmodule->bufferInhibitFlag = buffer->syncFlag;
	// }
	// /* if no buffer is free, message will be sent by interrupt */
	// else
	// {
	// 	buffer->bufferFull = true;
	// 	CANmodule->CANtxCount++;
	// }
	CO_UNLOCK_CAN_SEND(CANmodule);

	return err;
}

void CO_CANclearPendingSyncPDOs(CO_CANmodule_t *CANmodule)
{
	uint32_t tpdoDeleted = 0U;

	CO_LOCK_CAN_SEND(CANmodule);
	/* Abort message from CAN module, if there is synchronous TPDO. Take special care with this functionality. */
	// if(can_drv_is_transmitting(dev) && CANmodule->bufferInhibitFlag)
	// {
	// 	/* clear TXREQ */
	// 	can_drv_tx_abort(dev);
	// 	CANmodule->bufferInhibitFlag = false; /* clear TXREQ */
	// 	tpdoDeleted = 1U;
	// }

	// if(CANmodule->CANtxCount != 0U) // delete also pending synchronous TPDOs in TX buffers
	// {
	// 	CO_CANtx_t *buffer = &CANmodule->txArray[0];
	// 	for(uint16_t i = CANmodule->txSize; i > 0U; i--)
	// 	{
	// 		if(buffer->bufferFull)
	// 		{
	// 			if(buffer->syncFlag)
	// 			{
	// 				buffer->bufferFull = false;
	// 				CANmodule->CANtxCount--;
	// 				tpdoDeleted = 2U;
	// 			}
	// 		}
	// 		buffer++;
	// 	}
	// }
	CO_UNLOCK_CAN_SEND(CANmodule);

	if(tpdoDeleted != 0U) CANmodule->CANerrorStatus |= CO_CAN_ERRTX_PDO_LATE;
}

/* Get error counters from the module. If necessary, function may use different way to determine errors. */
void CO_CANmodule_process(CO_CANmodule_t *CANmodule)
{
	// uint16_t overflow = can_drv_check_bus_off(dev) ? 1 : 0;
	// uint16_t rxErrors = can_drv_get_rx_error_counter(dev);
	// uint16_t txErrors = can_drv_get_tx_error_counter(dev);

	// uint32_t err = ((uint32_t)txErrors << 16) | ((uint32_t)rxErrors << 8) | overflow;

	// if(CANmodule->errOld != err)
	// {
	// 	uint16_t status = CANmodule->CANerrorStatus;
	// 	CANmodule->errOld = err;

	// 	if(txErrors >= 256U)
	// 	{
	// 		status |= CO_CAN_ERRTX_BUS_OFF;
	// 	}
	// 	else
	// 	{
	// 		/* recalculate CANerrorStatus, first clear some flags */
	// 		status &= 0xFFFF ^ (CO_CAN_ERRTX_BUS_OFF |
	// 							CO_CAN_ERRRX_WARNING | CO_CAN_ERRRX_PASSIVE |
	// 							CO_CAN_ERRTX_WARNING | CO_CAN_ERRTX_PASSIVE);
	// 		if(rxErrors >= 128)
	// 		{
	// 			status |= CO_CAN_ERRRX_WARNING | CO_CAN_ERRRX_PASSIVE;
	// 		}
	// 		else if(rxErrors >= 96)
	// 		{
	// 			status |= CO_CAN_ERRRX_WARNING;
	// 		}

	// 		if(txErrors >= 128)
	// 		{
	// 			status |= CO_CAN_ERRTX_WARNING | CO_CAN_ERRTX_PASSIVE;
	// 		}
	// 		else if(rxErrors >= 96)
	// 		{
	// 			status |= CO_CAN_ERRTX_WARNING;
	// 		}

	// 		/* if not tx passive clear also overflow */
	// 		if((status & CO_CAN_ERRTX_PASSIVE) == 0)
	// 		{
	// 			status &= 0xFFFF ^ CO_CAN_ERRTX_OVERFLOW;
	// 		}
	// 	}

	// 	if(overflow != 0)
	// 	{
	// 		status |= CO_CAN_ERRRX_OVERFLOW;
	// 	}

	// 	CANmodule->CANerrorStatus = status;
	// }
}
