#ifndef VF_MUTEX_IMPL_H
#define VF_MUTEX_IMPL_H

#include "vf_mutex.h"
#include "linux/mutex.h"

struct vf_mutex {
	struct mutex mutex;
};


#endif /* VF_MUTEX_IMPL_H */
