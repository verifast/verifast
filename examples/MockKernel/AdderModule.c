#include "threading.h"
#include "malloc.h"
#include "MockKernel.h"
#include "stdlib.h"

//@ #include "arrays.gh"

//@ unloadable_module;

static char adderName[11] = "/dev/adder";

static int acc;
static struct lock *adderLock;

//@ predicate adderLockInv() = integer(&acc, _);
//@ predicate adderDeviceState(;) = [1/2]module_code(AdderModule) &*& adderLock |-> ?adderLock_ &*& lock(adderLock_, _, adderLockInv);
//@ predicate adderFile(real frac, void *file) = [frac/2]module_code(AdderModule) &*& [frac]adderLock |-> ?adderLock_ &*& [frac]lock(adderLock_, _, adderLockInv);

void *adder_open()
    //@ requires [?f]adderDeviceState() &*& lockset(currentThread, nil);
    //@ ensures adderFile(f, result) &*& lockset(currentThread, nil);
{
    //@ open adderDeviceState();
    return 0;
    //@ close adderFile(f, 0);
}

int adder_read(void *file)
    //@ requires adderFile(?f, file) &*& lockset(currentThread, nil);
    //@ ensures adderFile(f, file) &*& lockset(currentThread, nil);
{
    //@ open adderFile(f, file);
    int currentAcc = 0;
    lock_acquire(adderLock);
    //@ open adderLockInv();
    currentAcc = acc;
    //@ close adderLockInv();
    lock_release(adderLock);
    return currentAcc;
    //@ close adderFile(f, file);
}

void adder_write(void *file, int value)
    //@ requires adderFile(?f, file) &*& lockset(currentThread, nil);
    //@ ensures adderFile(f, file) &*& lockset(currentThread, nil);
{
    //@ open adderFile(f, file);
    lock_acquire(adderLock);
    //@ open adderLockInv();
    {
        int acc0 = acc;
        //@ produce_limits(acc0);
        if (value < 0) {
            if (acc0 < INT_MIN - value) abort();
        } else {
            if (INT_MAX - value < acc0) abort();
        }
        acc += value;
    }
    //@ close adderLockInv();
    lock_release(adderLock);
    return;
    //@ close adderFile(f, file);
}

void adder_close(void *file)
    //@ requires adderFile(?f, file) &*& lockset(currentThread, nil);
    //@ ensures [f]adderDeviceState() &*& lockset(currentThread, nil);
{
    //@ open adderFile(f, file);
    return;
    //@ close [f]adderDeviceState();
}

static struct file_ops adderOps = {adder_open, adder_read, adder_write, adder_close};
static struct device *adderDevice;

/*@

predicate adderState(struct module *self, int deviceCount) =
    [1/2]module_code(AdderModule) &*&
    deviceCount == 1 &*&
    adderDevice |-> ?adderDevice_ &*&
    kernel_device(adderDevice_, self, adderName, ?adderNameChars, &adderOps, adderDeviceState) &*&
    struct_file_ops_padding(&adderOps) &*&
    length(adderNameChars) == 10;

@*/

void module_dispose(struct module *self)
    //@ requires adderState(self, ?deviceCount) &*& kernel_module_disposing(self, deviceCount);
    //@ ensures kernel_module_disposing(self, 0) &*& module(AdderModule, false);
{
    //@ open adderState(self, deviceCount);
    unregister_device(adderDevice);
    //@ open file_ops(&adderOps, _, _);
    //@ open adderDeviceState();
    lock_dispose(adderLock);
    //@ open adderLockInv();
    return;
    //@ close_module();
}

module_dispose_ *module_init(struct module *self) //@ : module_init_(AdderModule)
    //@ requires module(AdderModule, true) &*& kernel_module_initializing(self, 0);
    /*@
    ensures
        kernel_module_state(?state) &*& state(self, ?deviceCount) &*& [_]is_module_dispose_(result, state, AdderModule) &*&
        kernel_module_initializing(self, deviceCount);
    @*/
{
    //@ open_module();
    
    //@ close adderLockInv();
    //@ close create_lock_ghost_args(adderLockInv, nil, nil);
    adderLock = create_lock();
    //@ close adderDeviceState();
    
    //@ produce_function_pointer_chunk device_open(adder_open)(adderDeviceState, adderFile)() { call(); }
    //@ produce_function_pointer_chunk device_read(adder_read)(adderFile)(file) { call(); }
    //@ produce_function_pointer_chunk device_write(adder_write)(adderFile)(file, value) { call(); }
    //@ produce_function_pointer_chunk device_close(adder_close)(adderDeviceState, adderFile)(file) { call(); }
    //@ close file_ops(&adderOps, adderDeviceState, adderFile);
    adderDevice = register_device(self, adderName, &adderOps);
    
    //@ close kernel_module_state(adderState);
    //@ produce_function_pointer_chunk module_dispose_(module_dispose)(adderState, AdderModule)(self_) { call(); }
    
    return module_dispose;
    //@ close adderState(self, 1);
}
