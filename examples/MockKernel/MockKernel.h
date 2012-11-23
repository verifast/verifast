#ifndef MOCKKERNEL_H
#define MOCKKERNEL_H

#include "threading.h"

struct module;

//@ predicate kernel_module_initializing(struct module *module, int deviceCount);
//@ predicate kernel_module_disposing(struct module *module, int deviceCount);

typedef void *device_open/*@(predicate() device, predicate(real, void *) file_)@*/();
    //@ requires [?f]device() &*& lockset(currentThread, nil);
    //@ ensures file_(f, result) &*& lockset(currentThread, nil);
typedef int device_read/*@(predicate(real, void *) file_)@*/(void *file);
    //@ requires file_(?f, file) &*& lockset(currentThread, nil);
    //@ ensures file_(f, file) &*& lockset(currentThread, nil);
typedef void device_write/*@(predicate(real, void *) file_)@*/(void *file, int value);
    //@ requires file_(?f, file) &*& lockset(currentThread, nil);
    //@ ensures file_(f, file) &*& lockset(currentThread, nil);
typedef void device_close/*@(predicate() device, predicate(real, void *) file_)@*/(void *file);
    //@ requires file_(?f, file) &*& lockset(currentThread, nil);
    //@ ensures [f]device() &*& lockset(currentThread, nil);

struct file_ops {
    device_open *open_;
    device_read *read;
    device_write *write;
    device_close *close_;
};

/*@

predicate file_ops(struct file_ops *fileOps, predicate(;) device, predicate(real, void *) file;) =
    fileOps->open_ |-> ?open_ &*& [_]is_device_open(open_, device, file) &*&
    fileOps->read |-> ?read &*& [_]is_device_read(read, file) &*&
    fileOps->write |-> ?write &*& [_]is_device_write(write, file) &*&
    fileOps->close_ |-> ?close_ &*& [_]is_device_close(close_, device, file);

@*/

struct device;

/*@

predicate kernel_device(struct device *device, struct module *owner, char *name, list<char> nameChars, struct file_ops *fileOps, predicate(;) device);

@*/

struct device *register_device(struct module *owner, char *name, struct file_ops *ops);
    /*@
    requires
        kernel_module_initializing(owner, ?deviceCount) &*&
        string(name, ?nameChars) &*&
        file_ops(ops, ?device, _) &*& device();
    @*/
    //@ ensures kernel_module_initializing(owner, deviceCount + 1) &*& kernel_device(result, owner, name, nameChars, ops, device);

void unregister_device(struct device *device);
    //@ requires kernel_device(device, ?owner, ?name, ?nameChars, ?ops, ?device_) &*& kernel_module_disposing(owner, ?deviceCount);
    //@ ensures string(name, nameChars) &*& file_ops(ops, _, _) &*& device_() &*& kernel_module_disposing(owner, deviceCount - 1);

typedef void module_dispose_/*@(predicate(struct module *, int) state, int moduleMainModule)@*/(struct module *self);
    //@ requires state(self, ?deviceCount) &*& kernel_module_disposing(self, deviceCount);
    //@ ensures kernel_module_disposing(self, 0) &*& module(moduleMainModule, false);

//@ predicate kernel_module_state(predicate(struct module *, int) state) = true;

typedef module_dispose_ *module_init_/*@(int moduleMainModule)@*/(struct module *self);
    //@ requires module(moduleMainModule, true) &*& kernel_module_initializing(self, 0);
    /*@
    ensures
        kernel_module_state(?state) &*& state(self, ?deviceCount) &*&
        [_]is_module_dispose_(result, state, moduleMainModule) &*& kernel_module_initializing(self, deviceCount);
    @*/

#endif