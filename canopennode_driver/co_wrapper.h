#ifndef CO_WRAPPER_H_
#define CO_WRAPPER_H_

#include <CANopen.h>
#include <OD.h>
#include <sp.h>

int co_wrapper_init(CO_t **co, sp_t *sp);
void co_wrapper_deinit(CO_t **co);

#endif // CO_WRAPPER_H_