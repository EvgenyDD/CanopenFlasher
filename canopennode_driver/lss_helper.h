#ifndef LSS_HELPER_H_
#define LSS_HELPER_H_

#include "305/CO_LSS.h"
#include "305/CO_LSSmaster.h"
#include "CANopen.h"
#include <stdint.h>

/**
 * @brief Gets field from the slave in the configuration LSS state
 *
 * @param field ::CO_LSS_cs_t CO_LSS_INQUIRE_* =>
 * 		CO_LSS_INQUIRE_VENDOR
 * 		CO_LSS_INQUIRE_PRODUCT
 * 		CO_LSS_INQUIRE_REV
 * 		CO_LSS_INQUIRE_SERIAL
 * 		CO_LSS_INQUIRE_NODE_ID
 * @param value pointer to get value
 * @return int ::CO_LSSmaster_return_t
 */
int lss_helper_inquire(CO_t *co, uint32_t field, uint32_t *value);

/**
 * @brief Gets 0x1018 fields from the slave in the configuration LSS state
 *
 * @param field
 * @param addr
 * @return int
 */
int lss_helper_inquire_lss_addr(CO_t *co, CO_LSS_address_t *addr);

/**
 * @brief Sets new CAN ID for the slave in the configuration LSS state
 *
 * @param node_id New ID, can be CO_LSS_NODE_ID_ASSIGNMENT to invalidate node ID
 * @return int ::CO_LSSmaster_return_t
 */
int lss_helper_cfg_node_id(CO_t *co, uint8_t node_id);

/**
 * @brief Sets new CAN Baud Rate for the slave in the configuration LSS state
 *
 * @param kbit_s New CAN baud
 * @return int ::CO_LSSmaster_return_t
 */
int lss_helper_cfg_bit_timing(CO_t *co, uint16_t kbit_s);

/**
 * @brief Applies current pending baud rates to the devices
 *
 * @param switch_delay_ms
 */
int lss_helper_activate_bit_timing(CO_t *co, uint16_t switch_delay_ms);

/**
 * @brief Store configuration to the device to non-volatile memory (if available)
 *
 * @return int ::CO_LSSmaster_return_t
 */
int lss_helper_cfg_store(CO_t *co);

/**
 * @brief Request LSS switch state select
 *
 * @param addr LSS target address. If NULL, all nodes are selected
 * @return int ::CO_LSSmaster_return_t
 */
int lss_helper_select(CO_t *co, CO_LSS_address_t *addr);

/**
 * @brief Request LSS switch state deselect
 *
 */
void lss_helper_deselect(CO_t *co);

/**
 * @brief Selects unconfigured slave for the configuration
 *
 * @param timeout Timeout for cyclic scan in ms
 * @param vendor_id !NULL for exact match, NULL for SCAN
 * @param product !NULL for exact match, NULL for SCAN
 * @param rev !NULL for exact match, NULL for SCAN
 * @param serial !NULL for exact match, NULL for SCAN
 * @return int ::CO_LSSmaster_return_t
 */
int lss_helper_fastscan_select(CO_t *co, uint16_t timeout, uint32_t *vendor_id, uint32_t *product, uint32_t *rev, uint32_t *serial);

#endif // LSS_HELPER_H_