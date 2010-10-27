#include "threading.h"
#include "malloc.h"
#include "MockKernel.h"
#include "stdlib.h"

//@ unloadable_module;

static char *adderName;

static int acc;
static struct lock *adderLock;

//@ predicate adderLockInv() = integer(&acc, _);
//@ predicate adderDeviceState(;) = [1/2]module_code(AdderModule) &*& pointer(&adderLock, ?adderLock_) &*& lock(adderLock_, _, adderLockInv);
//@ predicate adderFile(real frac, void *file) = [frac/2]module_code(AdderModule) &*& [frac]pointer(&adderLock, ?adderLock_) &*& [frac]lock(adderLock_, _, adderLockInv);

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

static struct file_ops *adderOps;
static struct device *adderDevice;

/*@

predicate adderState(struct module *self, int deviceCount) =
    [1/2]module_code(AdderModule) &*&
    deviceCount == 1 &*&
    pointer(&adderName, ?adderName_) &*& malloc_block(adderName_, 11) &*&
    pointer(&adderOps, ?adderOps_) &*& malloc_block_file_ops(adderOps_) &*&
    pointer(&adderDevice, ?adderDevice_) &*&
    kernel_device(adderDevice_, self, adderName_, ?adderNameChars, adderOps_, adderDeviceState) &*&
    length(adderNameChars) == 11;

@*/

void module_dispose(struct module *self)
    //@ requires adderState(self, ?deviceCount) &*& kernel_module_disposing(self, deviceCount);
    //@ ensures kernel_module_disposing(self, 0) &*& module(AdderModule, false);
{
    //@ open adderState(self, deviceCount);
    unregister_device(adderDevice);
    //@ assert pointer(&adderOps, ?adderOps_);
    //@ open file_ops(adderOps_, _, _);
    free(adderOps);
    free(adderName);
    //@ open adderDeviceState();
    lock_dispose(adderLock);
    //@ open adderLockInv();
    return;
    //@ close_module();
}

/*@

predicate chars2(char *c0, int length; list<char> cs) =
    length == 0 ?
        cs == nil
    :
        character(c0, ?c) &*& chars2(c0 + 1, length - 1, ?cs0) &*& cs == cons(c, cs0);

lemma void chars_to_chars2(char *c0)
    requires chars(c0, ?cs);
    ensures chars2(c0, length(cs), cs);
{
    open chars(c0, cs);
    switch (cs) {
        case nil:
        case cons(c, cs0):
            length_nonnegative(cs0);
            chars_to_chars2(c0 + 1);
    }
    close chars2(c0, length(cs), cs);
}

lemma void chars2_to_chars(char *c0)
    requires chars2(c0, ?n, ?cs);
    ensures chars(c0, cs);
{
    open chars2(c0, n, cs);
    switch (cs) {
        case nil:
        case cons(c, cs0):
            chars2_to_chars(c0 + 1);
    }
    close chars(c0, cs);
}

@*/

module_dispose_ *module_init(struct module *self) //@ : module_init_(AdderModule)
    //@ requires module(AdderModule, true) &*& kernel_module_initializing(self, 0);
    /*@
    ensures
        kernel_module_state(?state) &*& state(self, ?deviceCount) &*& [_]is_module_dispose_(result, state, AdderModule) &*&
        kernel_module_initializing(self, deviceCount);
    @*/
{
    //@ open_module();
    adderName = malloc(11);
    if (adderName == 0) abort();
    //@ malloc_block_limits(adderName);
    //@ chars_to_chars2(adderName);
    *(adderName + 0) = '/';
    *(adderName + 1) = 'd';
    *(adderName + 2) = 'e';
    *(adderName + 3) = 'v';
    *(adderName + 4) = '/';
    *(adderName + 5) = 'a';
    *(adderName + 6) = 'd';
    *(adderName + 7) = 'd';
    *(adderName + 8) = 'e';
    *(adderName + 9) = 'r';
    *(adderName + 10) = 0;
    //@ close chars2(adderName + 10, 1, _);
    //@ close chars2(adderName + 9, 2, _);
    //@ close chars2(adderName + 8, 3, _);
    //@ close chars2(adderName + 7, 4, _);
    //@ close chars2(adderName + 6, 5, _);
    //@ close chars2(adderName + 5, 6, _);
    //@ close chars2(adderName + 4, 7, _);
    //@ close chars2(adderName + 3, 8, _);
    //@ close chars2(adderName + 2, 9, _);
    //@ close chars2(adderName + 1, 10, _);
    //@ close chars2(adderName, 11, _);
    //@ chars2_to_chars(adderName);
    
    //@ close adderLockInv();
    //@ close create_lock_ghost_args(adderLockInv, nil, nil);
    adderLock = create_lock();
    //@ close adderDeviceState();
    
    adderOps = malloc(sizeof(struct file_ops));
    if (adderOps == 0) abort();
    adderOps->open_ = adder_open;
    adderOps->read = adder_read;
    adderOps->write = adder_write;
    adderOps->close_ = adder_close;
    //@ produce_function_pointer_chunk device_open(adder_open)(adderDeviceState, adderFile)() { call(); }
    //@ produce_function_pointer_chunk device_read(adder_read)(adderFile)(file) { call(); }
    //@ produce_function_pointer_chunk device_write(adder_write)(adderFile)(file, value) { call(); }
    //@ produce_function_pointer_chunk device_close(adder_close)(adderDeviceState, adderFile)(file) { call(); }
    //@ close file_ops(adderOps, adderDeviceState, adderFile);
    adderDevice = register_device(self, adderName, adderOps);
    
    //@ close kernel_module_state(adderState);
    //@ produce_function_pointer_chunk module_dispose_(module_dispose)(adderState, AdderModule)(self_) { call(); }
    
    return module_dispose;
    //@ close adderState(self, 1);
}
