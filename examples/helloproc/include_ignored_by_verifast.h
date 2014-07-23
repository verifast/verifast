#ifndef INCLUDE_IGNORED_BY_VERIFAST_H
#define INCLUDE_IGNORED_BY_VERIFAST_H

/*
 * Verifast supports "bool" without include, but C90 does not.
 * Linux defines its own bool typedef in types.h, but we can't include
 * it directly since Verifast does not accept types.h
 * In kernel space, one does not #include <stdbool.h>.
 *
 * This file, include_ignored_by_verifast.h, includes the file types.h,
 * and is ignored by Verifast. This is a workaround. The proper fix
 * would be to support the _Bool (with underscore) type in VeriFast.
 */


/*
 * It would be nice to include only the bool part of types.h here.
 */
#include "linux/types.h"


#endif /* INCLUDE_IGNORED_BY_VERIFAST_H */

