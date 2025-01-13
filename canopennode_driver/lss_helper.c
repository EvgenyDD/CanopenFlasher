#include "lss_helper.h"
#include "CANopen.h"

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

#define LSS_POLLING_FUNC(f) \
	do                      \
	{                       \
		f;                  \
		interval = 1000;    \
		SLEEP_MS(1);        \
	} while(ret == CO_LSSmaster_WAIT_SLAVE)

int lss_helper_inquire(CO_t *co, uint32_t field, uint32_t *value)
{
	int interval = 0;
	CO_LSSmaster_return_t ret;
	LSS_POLLING_FUNC({ ret = CO_LSSmaster_Inquire(co->LSSmaster, interval, field, value); });
	return ret;
}

int lss_helper_inquire_lss_addr(CO_t *co, CO_LSS_address_t *addr)
{
	int interval = 0;
	CO_LSSmaster_return_t ret;
	LSS_POLLING_FUNC({ ret = CO_LSSmaster_InquireLssAddress(co->LSSmaster, interval, addr); });
	return ret;
}

int lss_helper_cfg_node_id(CO_t *co, uint8_t node_id)
{
	int interval = 0;
	CO_LSSmaster_return_t ret;
	LSS_POLLING_FUNC({ ret = CO_LSSmaster_configureNodeId(co->LSSmaster, interval, node_id); });
	return ret;
}

int lss_helper_cfg_bit_timing(CO_t *co, uint16_t kbit_s)
{
	int interval = 0;
	CO_LSSmaster_return_t ret;
	LSS_POLLING_FUNC({ ret = CO_LSSmaster_configureBitTiming(co->LSSmaster, interval, kbit_s); });
	return ret;
}

int lss_helper_activate_bit_timing(CO_t *co, uint16_t switch_delay_ms)
{
	return CO_LSSmaster_ActivateBit(co->LSSmaster, switch_delay_ms);
}

int lss_helper_cfg_store(CO_t *co)
{
	int interval = 0;
	CO_LSSmaster_return_t ret;
	LSS_POLLING_FUNC({ ret = CO_LSSmaster_configureStore(co->LSSmaster, interval); });
	return ret;
}

int lss_helper_select(CO_t *co, CO_LSS_address_t *addr)
{
	int interval = 0;
	CO_LSSmaster_return_t ret;
	LSS_POLLING_FUNC({ ret = CO_LSSmaster_switchStateSelect(co->LSSmaster, interval, addr); });
	return ret;
}

void lss_helper_deselect(CO_t *co)
{
	CO_LSSmaster_switchStateDeselect(co->LSSmaster);
}

int lss_helper_fastscan_select(CO_t *co, uint16_t timeout, uint32_t *vendor_id, uint32_t *product, uint32_t *rev, uint32_t *serial)
{
	CO_LSSmaster_fastscan_t fastscan;
	fastscan.scan[CO_LSS_FASTSCAN_VENDOR_ID] = vendor_id ? CO_LSSmaster_FS_MATCH : CO_LSSmaster_FS_SCAN;
	fastscan.scan[CO_LSS_FASTSCAN_PRODUCT] = product ? CO_LSSmaster_FS_MATCH : CO_LSSmaster_FS_SCAN;
	fastscan.scan[CO_LSS_FASTSCAN_REV] = rev ? CO_LSSmaster_FS_MATCH : CO_LSSmaster_FS_SCAN;
	fastscan.scan[CO_LSS_FASTSCAN_SERIAL] = serial ? CO_LSSmaster_FS_MATCH : CO_LSSmaster_FS_SCAN;

	if(vendor_id) fastscan.match.identity.vendorID = *vendor_id;
	if(product) fastscan.match.identity.productCode = *product;
	if(rev) fastscan.match.identity.revisionNumber = *rev;
	if(serial) fastscan.match.identity.serialNumber = *serial;

	CO_LSSmaster_changeTimeout(co->LSSmaster, timeout); /** TODO: check on lower baud rates */

	int interval = 0;
	CO_LSSmaster_return_t ret;
	LSS_POLLING_FUNC({ ret = CO_LSSmaster_IdentifyFastscan(co->LSSmaster, interval, &fastscan); });

	CO_LSSmaster_changeTimeout(co->LSSmaster, CO_LSSmaster_DEFAULT_TIMEOUT);
	return ret;
}
