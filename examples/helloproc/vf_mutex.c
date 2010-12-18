#include "vf_mutex_impl.h"
#include "vf_mem.h"


/*
 * Linux supports two ways to initialize mutexes: static and dynamic.
 * Both uses macros.  We currently only support dynamic initialized
 * mutexes.
 */


struct vf_mutex *vf_mutex_create()
{
	struct vf_mutex *mutex = vf_kmalloc(sizeof(struct vf_mutex));
	if (mutex == 0){
		return 0;
	}else{
		mutex_init(&(mutex->mutex));
		return mutex;
	}
}


void vf_mutex_dispose(struct vf_mutex *mutex)
{

	/*
	 * The documentation in mutex.h, mutex.c, and
	 * Documentation/mutex-design.txt neglect mutex destruction.
	 * mutex.h defines an empty macro mutex_destroy which is not
	 * officially documented.
	 */
	
	vf_kfree(mutex);
}


void vf_mutex_lock(struct vf_mutex *mutex)
{
	mutex_lock(&(mutex->mutex));
}


void vf_mutex_unlock(struct vf_mutex *mutex)
{
	mutex_unlock(&(mutex->mutex));
}

