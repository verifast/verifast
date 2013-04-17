#ifndef CIRCULAR_INCLUDE3_H
#define CIRCULAR_INCLUDE3_H

//this fails because recursive type checking does
//not allow (guarded) circular includes at all
/*~*/#include "circular_include.h"

#endif
