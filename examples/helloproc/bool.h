#ifndef VF_BOOL_H
#define VF_BOOL_H

/*
 * Verifast supports "bool" but C90 does not.  Linux defines its own
 * bool typedef in types.h, but we can't include it directly since
 * Verifast does not accept types.h
 *
 * This file, bool.h, includes the types.h, and is ignored by
 * Verifast.
 */


/*
 * It would be nice to include only the bool part of types.h here.
 */
#include "linux/types.h"


#endif /* VF_BOOL_H */

