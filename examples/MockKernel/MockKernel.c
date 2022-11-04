#include "threading.h"
#include "sockets.h"
#include "malloc.h"
#include "stdlib.h"
#include "libraries.h"
#include "string.h"
#include "MockKernel.h"
#include "MockKernelModule_proxy.h"
#include "lists.h"
//@ #include "counting.gh"
//@ #include "ghost_sets.gh"
//@ #include "contrib.gh"

struct module {
    struct module *next;
    char *name;
    void *library;
    module_dispose_ *dispose;
    int ref_count;  // 1 + (the number of threads using a driver provided by this module)
    //@ int contrib_sum_id; // ID of a ghost object that keeps track of each driver's contribution to the ref_count
    //@ int modulesId;  // ID of the ghost set that tracks the set of modules. Allows access to this set from the kernel_module_XXX predicates.
    //@ int devicesId; // ID of the ghost set that tracks the set of devices. Allows access to this set from the kernel_module_XXX predicates.
    //@ int devicesId2;  // Same value as devicesID. Allows access to this set from the kernel_device predicate.
};

static struct module *modules;

struct device {
    struct device *next;
    char *name;
    //@ list<char> nameChars;
    struct module *owner;
    struct file_ops *ops;
    //@ int useCount;  // Number of threads using this device.
    //@ struct file_ops *ops2;  // Same value as ops.
    //@ predicate(;) state;  // Module-provided predicate describing the resources used by the device.
    //@ predicate(real, void *) fileState;  // Module-provided predicate describing the resources used by a file.
};

static struct device *directory;

/*@

predicate ghost_set_member_handle_wrapper(pair<int, void *> input; unit output) =
    ghost_set_member_handle(fst(input), snd(input)) &*& output == unit;

predicate_ctor kernel_module(int modulesId, int devicesId)(struct module *module) =
    module->name |-> ?name &*& string(name, ?nameChars) &*& malloc_block(name, length(nameChars) + 1) &*&
    module->library |-> ?library &*& library(library, ?mainModule) &*&
    module->dispose |-> ?dispose &*& [_]is_module_dispose_(dispose, ?state, mainModule) &*& state(module, ?deviceCount) &*&
    module->ref_count |-> ?refCount &*&
    module->modulesId |-> modulesId &*&
    module->devicesId |-> devicesId &*&
    counting(module_devicesId2, module, deviceCount, devicesId) &*&
    counting(module_contrib_sum_id, module, deviceCount, ?contribSumId) &*&
    contrib_sum(contribSumId, deviceCount, refCount - 1) &*&
    counting(ghost_set_member_handle_wrapper, pair(modulesId, module), deviceCount, unit) &*&
    malloc_block_module(module);

predicate file_ops_wrapper1(struct device *device, predicate(;) state; struct file_ops *ops) =
    device->ops |-> ops &*& device->fileState |-> ?fileState &*& file_ops(ops, state, fileState) &*& state();
predicate file_ops_wrapper2(pair<struct device *, predicate(;)> device_state; struct file_ops *ops) =
    file_ops_wrapper1(fst(device_state), snd(device_state), ops);

predicate_ctor device(int modulesId, int devicesId)(struct device *device) =
    [1/2]device->name |-> ?name &*&
    [1/2]device->nameChars |-> ?nameChars &*& string(name, nameChars) &*&
    [1/2]device->owner |-> ?owner &*&
    ticket(ghost_set_member_handle_wrapper, pair(modulesId, owner), ?f1) &*& [f1]ghost_set_member_handle(modulesId, owner) &*&
    device->useCount |-> ?useCount &*& 0 <= useCount &*&
    counting(device_state, device, 2 + useCount, ?state) &*& ticket(device_state, device, ?stateFrac) &*& [stateFrac]device->state |-> state &*&
    counting(device_ops2, device, 2 + useCount, ?fileOps) &*& ticket(device_ops2, device, ?ops2Frac) &*& [ops2Frac]device->ops2 |-> fileOps &*&
    counting(file_ops_wrapper2, pair(device, state), useCount, fileOps) &*&
    ticket(module_contrib_sum_id, owner, ?f2) &*&
    [f2]owner->contrib_sum_id |-> ?contribSumId &*& contrib(contribSumId, useCount) &*&
    counting(ghost_set_member_handle_wrapper, pair(devicesId, device), useCount + 1, unit) &*&
    malloc_block_device(device);

predicate_ctor kernel_inv(int modulesId, int devicesId)() =
    pointer(&modules, ?modules_) &*& lseg(modules_, 0, ?modules, kernel_module(modulesId, devicesId)) &*&
    pointer(&directory, ?devices_) &*& lseg(devices_, 0, ?devices, device(modulesId, devicesId)) &*&
    ghost_set(modulesId, modules) &*& ghost_set(devicesId, devices);

predicate kernel_module_initializing(struct module *owner, int deviceCount) =
    [1/2]owner->modulesId |-> ?modulesId &*&
    [1/2]owner->devicesId |-> ?devicesId &*&
    counting(module_contrib_sum_id, owner, deviceCount, ?contribSumId) &*&
    contrib_sum(contribSumId, deviceCount, 0) &*&
    counting(ghost_set_member_handle_wrapper, pair(modulesId, owner), deviceCount, unit) &*&
    counting(module_devicesId2, owner, deviceCount, devicesId) &*&
    pointer(&directory, ?devices_) &*& lseg(devices_, 0, ?devices, device(modulesId, devicesId)) &*& ghost_set(devicesId, devices);

predicate kernel_device
    (
        struct device *device, struct module *owner, char *name, list<char> nameChars,
        struct file_ops *ops, predicate(;) state
    ) =
    ticket(module_devicesId2, owner, ?f) &*& [f]owner->devicesId2 |-> ?devicesId &*&
    ticket(ghost_set_member_handle_wrapper, pair(devicesId, device), ?f2) &*& [f2]ghost_set_member_handle(devicesId, device) &*&
    [1/2]device->owner |-> owner &*&
    [1/2]device->name |-> name &*&
    [1/2]device->nameChars |-> nameChars &*&
    ticket(device_state, device, ?deviceFrac) &*& [deviceFrac]device->state |-> state &*&
    ticket(device_ops2, device, ?ops2Frac) &*& [ops2Frac]device->ops2 |-> ops;

predicate kernel_module_disposing(struct module *owner, int deviceCount) =
    [1/2]owner->modulesId |-> ?modulesId &*&
    [1/2]owner->devicesId |-> ?devicesId &*&
    counting(module_contrib_sum_id, owner, deviceCount, ?contribSumId) &*& contrib_sum(contribSumId, deviceCount, 0) &*&
    counting(ghost_set_member_handle_wrapper, pair(modulesId, owner), deviceCount, unit) &*&
    counting(module_devicesId2, owner, deviceCount, devicesId) &*&
    pointer(&directory, ?devices_) &*& lseg(devices_, 0, ?devices, device(modulesId, devicesId)) &*& ghost_set(devicesId, devices);

@*/

static struct lock *kernelLock;

struct device *register_device(struct module *owner, char *name, struct file_ops *ops)
    /*@
    requires
        kernel_module_initializing(owner, ?deviceCount) &*&
        string(name, ?nameChars) &*&
        file_ops(ops, ?devicePred, ?fileState) &*& devicePred();
    @*/
    //@ ensures kernel_module_initializing(owner, deviceCount + 1) &*& kernel_device(result, owner, name, nameChars, ops, devicePred);
{
    //@ open kernel_module_initializing(owner, deviceCount);
    //@ create_ticket(ghost_set_member_handle_wrapper, pair(owner->modulesId, owner));
    //@ open ghost_set_member_handle_wrapper(_, _);
    //@ create_ticket(module_contrib_sum_id, owner);
    //@ create_contrib(owner->contrib_sum_id, 0);
    //@ create_ticket(module_devicesId2, owner);
    struct device *d = malloc(sizeof(struct device));
    if (d == 0) abort();
    d->name = name;
    //@ d->nameChars = nameChars;
    d->ops = ops;
    //@ d->useCount = 0;
    //@ d->state = devicePred;
    //@ start_counting(device_state, d);
    //@ create_ticket(device_state, d);
    //@ create_ticket(device_state, d);
    //@ d->ops2 = ops;
    //@ start_counting(device_ops2, d);
    //@ create_ticket(device_ops2, d);
    //@ create_ticket(device_ops2, d);
    d->owner = owner;
    d->next = directory;
    //@ assert pointer(&directory, ?devices_) &*& lseg(devices_, 0, ?ds, _);
    /*@
    if (mem(d, ds)) {
        lseg_separate(devices_, d);
        open device(owner->modulesId, owner->devicesId)(d);
    }
    @*/
    directory = d;
    //@ d->fileState = fileState;
    //@ close file_ops_wrapper1(d, devicePred, ops);
    //@ close file_ops_wrapper2(pair(d, devicePred), ops);
    //@ start_counting(file_ops_wrapper2, pair(d, devicePred));
    //@ ghost_set_add(owner->devicesId, d);
    //@ close ghost_set_member_handle_wrapper(pair(owner->devicesId, d), unit);
    //@ start_counting(ghost_set_member_handle_wrapper, pair(owner->devicesId, d));
    //@ create_ticket(ghost_set_member_handle_wrapper, pair(owner->devicesId, d));
    //@ open ghost_set_member_handle_wrapper(_, _);
    //@ close device(owner->modulesId, owner->devicesId)(d);
    //@ close lseg(d, 0, _, device(owner->modulesId, owner->devicesId));
    //@ close kernel_module_initializing(owner, deviceCount + 1);
    //@ close kernel_device(d, owner, name, nameChars, ops, devicePred);
    return d;
}

void unregister_device(struct device *device)
    //@ requires kernel_device(device, ?owner, ?name, ?nameChars, ?ops, ?device_) &*& kernel_module_disposing(owner, ?deviceCount);
    //@ ensures string(name, nameChars) &*& file_ops(ops, _, _) &*& device_() &*& kernel_module_disposing(owner, deviceCount - 1);
{
    //@ open kernel_device(device, owner, name, nameChars, ops, device_);
    //@ open kernel_module_disposing(owner, deviceCount);
    //@ if (deviceCount == 0) { stop_counting(module_devicesId2, owner); merge_fractions owner->devicesId2 |-> _; }
    //@ destroy_ticket(module_devicesId2, owner);
    //@ int devicesId = owner->devicesId;
    //@ ghost_set_match_member_handle(devicesId, device);
    linked_list_remove(&directory, device);
    //@ open device(owner->modulesId, owner->devicesId)(device);
    //@ assert [?f]ghost_set_member_handle(devicesId, device);
    //@ close [f]ghost_set_member_handle_wrapper(pair(owner->devicesId, device), unit);
    //@ destroy_ticket(ghost_set_member_handle_wrapper, pair(owner->devicesId, device));
    //@ int contribSumId = owner->contrib_sum_id;
    //@ destroy_ticket(module_contrib_sum_id, owner);
    //@ dispose_contrib(contribSumId);
    //@ stop_counting(ghost_set_member_handle_wrapper, pair(owner->devicesId, device));
    //@ open ghost_set_member_handle_wrapper(_, _);
    //@ ghost_set_remove(owner->devicesId, device);
    //@ int modulesId = owner->modulesId;
    //@ assert [?f1]ghost_set_member_handle(modulesId, owner);
    //@ close [f1]ghost_set_member_handle_wrapper(pair(owner->modulesId, owner), unit);
    //@ destroy_ticket(ghost_set_member_handle_wrapper, pair(owner->modulesId, owner));
    //@ close kernel_module_disposing(owner, deviceCount - 1);
    //@ stop_counting(file_ops_wrapper2, pair(device, device_));
    //@ open file_ops_wrapper2(_, _);
    //@ open file_ops_wrapper1(_, _, _);
    //@ destroy_ticket(device_ops2, device);
    //@ destroy_ticket(device_ops2, device);
    //@ stop_counting(device_ops2, device);
    //@ destroy_ticket(device_state, device);
    //@ destroy_ticket(device_state, device);
    //@ stop_counting(device_state, device);
    free(device);
}

void use_device(struct reader *reader, struct writer *writer, struct device *d)
    /*@
    requires
        reader(reader) &*& writer(writer) &*& lockset(currentThread, nil) &*&
        [?f1]d->ops |-> ?ops &*& [f1]file_ops(ops, ?device, ?file_) &*&
        [?f2]device();
    @*/
    /*@
    ensures
        reader(reader) &*& writer(writer) &*& lockset(currentThread, nil) &*&
        [f1]d->ops |-> ops &*& [f1]file_ops(ops, device, file_) &*&
        [f2]device();
    @*/
{
    //@ open file_ops(ops, _, _);
    device_open *open_ = d->ops->open_;
    device_close *close_ = d->ops->close_;
    void *file = open_();
    bool exitMenu = false;
    while (!exitMenu)
        /*@
        invariant
            reader(reader) &*& writer(writer) &*& file_(f2, file) &*& lockset(currentThread, nil) &*&
            [f1]d->ops |-> ops &*&
            [f1]ops->read |-> ?read &*& [f1]ops->write |-> ?write &*&
            [_]is_device_read(read, file_) &*&
            [_]is_device_write(write, file_);
        @*/
    {
        int choice = 0;
        writer_write_string(writer,
            "Device Menu:\r\n"
            "1. Read Value\r\n"
            "2. Write Value\r\n"
            "0. Exit\r\n");
        choice = reader_read_nonnegative_integer(reader);
        if (choice == 1) {
            device_read *read_ = d->ops->read;
            int value = read_(file);
            writer_write_string(writer, "Value read: ");
            writer_write_integer_as_decimal(writer, value);
            writer_write_string(writer, "\r\n");
        } else if (choice == 2) {
            int value = 0;
            device_write *write_ = d->ops->write;
            writer_write_string(writer, "Enter value:\r\n");
            value = reader_read_nonnegative_integer(reader);
            write_(file, value);
            writer_write_string(writer, "The value has been written\r\n");
        } else {
            exitMenu = true;
        }
    }
    close_(file);
    //@ close [f1]file_ops(ops, device, file_);
}

/*@

predicate kernel_inv_info(int modulesId, int devicesId) = true;

predicate_family_instance thread_run_data(handle_connection)(struct socket *socket) =
    [_]pointer(&kernelLock, ?kernelLock_) &*& kernel_inv_info(?modulesId, ?devicesId) &*& [_]lock(kernelLock_, _, kernel_inv(modulesId, devicesId)) &*&
    socket(socket, ?reader, ?writer) &*& reader(reader) &*& writer(writer);

@*/

void handle_connection(struct socket *socket) //@ : thread_run
    //@ requires thread_run_data(handle_connection)(socket) &*& lockset(currentThread, nil);
    //@ ensures lockset(currentThread, nil);
{
    //@ open thread_run_data(handle_connection)(socket);
    //@ open kernel_inv_info(?modulesId, ?devicesId);
    bool exitMenu = false;
    struct reader *reader = socket_get_reader(socket);
    struct writer *writer = socket_get_writer(socket);
    
    writer_write_string(writer, "Mock Kernel 1.0\r\n");
    
    while (!exitMenu)
        /*@
        invariant
            [_]pointer(&kernelLock, ?kernelLock_) &*& [_]lock(kernelLock_, _, kernel_inv(modulesId, devicesId)) &*& lockset(currentThread, nil) &*&
            reader(reader) &*& writer(writer);
        @*/
    {
        int choice = 0;
        writer_write_string(writer, "Loaded Modules:\r\n");
        
        lock_acquire(kernelLock);
        //@ open kernel_inv(modulesId, devicesId)();
        {
            struct module *m = modules;
            //@ assert pointer(&modules, ?modules_) &*& lseg(modules_, 0, ?ms, _);
            //@ close lseg(modules_, m, nil, kernel_module(modulesId, devicesId));
            while (m != 0)
                /*@
                invariant
                    lseg(modules_, m, ?ms1, kernel_module(modulesId, devicesId)) &*& lseg(m, 0, ?ms2, kernel_module(modulesId, devicesId)) &*&
                    append(ms1, ms2) == ms &*& writer(writer);
                @*/
            {
                //@ struct module *m0 = m;
                //@ open lseg(m, 0, _, _);
                //@ open kernel_module(modulesId, devicesId)(m);
                writer_write_string(writer, m->name);
                writer_write_string(writer, " (");
                writer_write_integer_as_decimal(writer, m->ref_count);
                writer_write_string(writer, " references) (handle: ");
                writer_write_pointer_as_hex(writer, m->library);
                writer_write_string(writer, ")\r\n");
                m = m->next;
                //@ close kernel_module(modulesId, devicesId)(m0);
                //@ lseg_add(modules_);
            }
            //@ open lseg(0, 0, _, _);
            //@ append_nil(ms1);
        }
        
        writer_write_string(writer, "Devices:\r\n");
        
        {
            struct device *d = directory;
            //@ assert pointer(&directory, ?devices_) &*& lseg(devices_, 0, ?ds, device(modulesId, devicesId));
            //@ close lseg(d, d, nil, device(modulesId, devicesId));
            while (d != 0)
                /*@
                invariant
                    writer(writer) &*&
                    lseg(devices_, d, ?ds1, device(modulesId, devicesId)) &*& lseg(d, 0, ?ds2, device(modulesId, devicesId)) &*& ds == append(ds1, ds2);
                @*/
            {
                //@ struct device *d0 = d;
                //@ open lseg(d, 0, _, _);
                //@ open device(modulesId, devicesId)(d);
                writer_write_string(writer, d->name);
                writer_write_string(writer, "\r\n");
                d = d->next;
                //@ close device(modulesId, devicesId)(d0);
                //@ lseg_add(devices_);
            }
            //@ open lseg(0, 0, _, _);
            //@ append_nil(ds1);
        }
        //@ close kernel_inv(modulesId, devicesId)();
        lock_release(kernelLock);
        
        writer_write_string(writer,
            "Menu:\r\n"
            "1. Load module\r\n"
            "2. Unload module\r\n"
            "3. Open device\r\n"
            "0. Exit\r\n");
        choice = reader_read_nonnegative_integer(reader);
        
        if (choice == 1) {
            
            char *name = 0;
            void *library = 0;
            struct module *m = 0;
            module_dispose_ *dispose = 0;
            module_init_ *init = 0;
            
            writer_write_string(writer, "Module name:\r\n");
            name = reader_read_line_as_string(reader);
            if (name == 0) abort();
            library = load_library(name);
            if (library == 0) {
                writer_write_string(writer, "Could not load the module.\r\n");
                free(name);
                goto skipLoad;
            }
            init = library_lookup_symbol_module_init(library);
            m = malloc(sizeof(struct module));
            if (m == 0) abort();
            m->library = library;
            m->name = name;
            m->ref_count = 1;
            lock_acquire(kernelLock);
            //@ open kernel_inv(modulesId, devicesId)();
            //@ int contribSumId = create_contrib_sum();
            //@ m->contrib_sum_id = contribSumId;
            //@ start_counting(module_contrib_sum_id, m);
            //@ assert pointer(&modules, ?modules_) &*& lseg(modules_, 0, ?ms, _);
            /*@
            if (mem(m, ms)) {
                lseg_separate(modules_, m);
                open kernel_module(modulesId, devicesId)(m);
            }
            @*/
            //@ ghost_set_add(modulesId, m);
            //@ close ghost_set_member_handle_wrapper(pair(modulesId, m), unit);
            //@ start_counting(ghost_set_member_handle_wrapper, pair(modulesId, m));
            //@ m->modulesId = modulesId;
            //@ m->devicesId = devicesId;
            //@ m->devicesId2 = devicesId;
            //@ start_counting(module_devicesId2, m);
            //@ close kernel_module_initializing(m, 0);
            dispose = init(m);
            //@ open kernel_module_state(?state);
            //@ open kernel_module_initializing(m, ?deviceCount);
            m->dispose = dispose;
            m->next = modules;
            modules = m;
            //@ close kernel_module(modulesId, devicesId)(m);
            //@ close lseg(m, 0, _, kernel_module(modulesId, devicesId));
            //@ close kernel_inv(modulesId, devicesId)();
            lock_release(kernelLock);
        skipLoad:
            ;
            
        } else if (choice == 2) {
            
            char *name = 0;
            struct module **pm = 0;
            bool done = false;
            writer_write_string(writer, "Module name:\r\n");
            name = reader_read_line_as_string(reader);
            if (name == 0) abort();
            lock_acquire(kernelLock);
            //@ open kernel_inv(modulesId, devicesId)();
            pm = &modules;
            done = false;
            //@ predicate(struct module *) kernel_module_ = kernel_module(modulesId, devicesId);
            //@ assert string(name, ?nameChars);
            while (!done)
                /*@
                invariant
                    writer(writer) &*& string(name, nameChars) &*&
                    pointer(&directory, ?devices_) &*& lseg(devices_, 0, ?ds, device(modulesId, devicesId)) &*& ghost_set(devicesId, ds) &*&
                    pointer(&modules, ?modules_) &*&
                    ghost_set<struct module *>(modulesId, ?ms) &*&
                    done ?
                        lseg(modules_, 0, ms, kernel_module(modulesId, devicesId))
                    :
                        pm == &modules ?
                            lseg(modules_, 0, ms, kernel_module(modulesId, devicesId))
                        :
                            lseg(modules_, ?m, ?ms1, kernel_module(modulesId, devicesId)) &*& pm == &((struct module *)m)->next &*& pointer(pm, ?next) &*&
                            kernel_module_(m) &*&
                            lseg(next, 0, ?ms2, kernel_module(modulesId, devicesId)) &*& ms == append(ms1, cons(m, ms2));
                @*/
            {
                struct module *m = *pm;
                if (m == 0) {
                    writer_write_string(writer, "No such module\r\n");
                    done = true;
                    /*@
                    if (pm == &modules) {
                    } else {
                        lseg_add(modules_);
                        lseg_append_final(modules_);
                    }
                    @*/
                } else {
                    //@ open lseg(m, 0, _, _);
                    //@ open kernel_module(modulesId, devicesId)(m);
                    int cmp = strcmp(name, m->name);
                    if (cmp == 0) {
                        if (m->ref_count == 1) {
                            module_dispose_ *dispose = m->dispose;
                            //@ close module_next(m, _);
                            /*@
                            if (pm != &modules) {
                                assert lseg(modules_, ?m0, ?ms1, _) &*& pointer(m0, m) &*& m->next |-> ?next &*& lseg(next, 0, ?ms2, _);
                                append_assoc(ms1, cons(m0, nil), cons(m, ms2));
                                ghost_set_remove_lemma(modulesId, append(ms1, cons(m0, nil)), m, ms2);
                            }
                            @*/
                            *pm = m->next;
                            //@ close kernel_module_disposing(m, _);
                            dispose(m);
                            //@ open kernel_module_disposing(m, 0);
                            free(m->name);
                            library_free(m->library);
                            //@ stop_counting(ghost_set_member_handle_wrapper, pair(modulesId, m));
                            //@ open ghost_set_member_handle_wrapper(_, _);
                            //@ ghost_set_remove(modulesId, m);
                            //@ stop_counting(module_contrib_sum_id, m);
                            //@ stop_counting(module_devicesId2, m);
                            //@ leak contrib_sum(_, _, _);
                            free(m);
                            writer_write_string(writer, "Module has been unloaded\r\n");
                            /*@
                            if (pm == &modules) {
                            } else {
                                lseg_add(modules_);
                                lseg_append_final(modules_);
                            }
                            @*/
                        } else {
                            //@ close kernel_module(modulesId, devicesId)(m);
                            //@ close lseg(m, 0, _, kernel_module(modulesId, devicesId));
                            /*@
                            if (pm == &modules) {
                            } else {
                                lseg_add(modules_);
                                lseg_append_final(modules_);
                            }
                            @*/
                            writer_write_string(writer, "Module is in use\r\n");
                        }
                        done = true;
                    } else {
                        //@ pointer_distinct(&modules, &m->next);
                        //@ close kernel_module(modulesId, devicesId)(m);
                        /*@
                        if (pm == &modules) {
                            close lseg(modules_, m, _, kernel_module(modulesId, devicesId));
                        } else {
                            close lseg(m, 0, _, kernel_module(modulesId, devicesId));
                            lseg_add(modules_);
                            open lseg(m, 0, _, _);
                        }
                        @*/
                        //@ produce_limits(m);
                        pm = &m->next;
                    }
                }
            }
            //@ close kernel_inv(modulesId, devicesId)();
            lock_release(kernelLock);
            free(name);
            
        } else if (choice == 3) {
        
            char *name = 0;
            struct device *d = 0;
            bool done = false;
            writer_write_string(writer, "Device name:\r\n");
            name = reader_read_line_as_string(reader);
            if (name == 0) abort();
            //@ assert string(name, ?nameChars);
            //@ assert [?lockFrac]lock(kernelLock_, _, _);
            lock_acquire(kernelLock);
            //@ open kernel_inv(modulesId, devicesId)();
            d = directory;
            done = false;
            //@ close lseg(d, d, nil, device(modulesId, devicesId));
            while (!done)
                /*@
                invariant
                    writer(writer) &*& reader(reader) &*& string(name, nameChars) &*&
                    [_]pointer(&kernelLock, kernelLock_) &*& locked(kernelLock_, ?kernelLockId, kernel_inv(modulesId, devicesId), currentThread, lockFrac) &*&
                    lockset(currentThread, cons(kernelLockId, nil)) &*&
                    pointer(&modules, ?modules_) &*& lseg(modules_, 0, ?ms, kernel_module(modulesId, devicesId)) &*& ghost_set(modulesId, ms) &*&
                    pointer(&directory, ?devices_) &*&
                    lseg(devices_, d, ?ds1, device(modulesId, devicesId)) &*& lseg(d, 0, ?ds2, device(modulesId, devicesId)) &*& ghost_set(devicesId, append(ds1, ds2));
                @*/
            {
                if (d == 0) {
                    writer_write_string(writer, "No such device\r\n");
                    done = true;
                } else {
                    //@ open lseg(d, 0, _, _);
                    //@ open device(modulesId, devicesId)(d);
                    //@ struct device *d0 = d;
                    int cmp = strcmp(d->name, name);
                    if (cmp == 0) {
                        
                        // Extract a fraction of the device state from the kernel lock
                        
                        //@ struct module *owner = d->owner;
                        //@ ghost_set_match_member_handle(modulesId, d->owner);
                        //@ lseg_separate(modules, d->owner);
                        //@ open kernel_module(modulesId, devicesId)(owner);
                        {
                            int refCount = d->owner->ref_count;
                            if (refCount == INT_MAX) abort();
                            d->owner->ref_count = refCount + 1;
                        }
                        //@ d->useCount++;
                        //@ int contribSumId = owner->contrib_sum_id;
                        //@ counting_match_fraction(module_contrib_sum_id, owner);
                        //@ assert contrib(contribSumId, ?useCount);
                        //@ dispose_contrib(contribSumId);
                        //@ create_contrib(contribSumId, useCount + 1);
                        //@ close kernel_module(modulesId, devicesId)(owner);
                        //@ lseg_add(modules);
                        //@ lseg_append_final(modules);
                        //@ predicate(;) device = d->state;
                        //@ struct file_ops *ops = d->ops2;
                        //@ create_ticket(file_ops_wrapper2, pair(d, device));
                        //@ create_ticket(ghost_set_member_handle_wrapper, pair(devicesId, d));
                        //@ open [?memberHandleFrac]ghost_set_member_handle_wrapper(_, _);
                        //@ create_ticket(device_state, d);
                        //@ create_ticket(device_ops2, d);
                        //@ close device(modulesId, devicesId)(d);
                        //@ close lseg(d, 0, _, device(modulesId, devicesId));
                        //@ lseg_append_final(devices_);
                        //@ close kernel_inv(modulesId, devicesId)();
                        lock_release(kernelLock);
                        
                        //@ open [?fileOpsFrac]file_ops_wrapper2(_, _);
                        //@ open file_ops_wrapper1(_, _, _);
                        use_device(reader, writer, d);
                        //@ close [fileOpsFrac]file_ops_wrapper1(d, device, ops);
                        //@ close [fileOpsFrac]file_ops_wrapper2(pair(d, device), ops);
                        
                        // Put the device state fraction back into the kernel lock
                        
                        lock_acquire(kernelLock);
                        //@ open kernel_inv(modulesId, devicesId)();
                        //@ ghost_set_match_member_handle(devicesId, d);
                        //@ assert pointer(&directory, ?devices1);
                        //@ lseg_separate(devices1, d);
                        //@ open device(modulesId, devicesId)(d);
                        //@ assert pointer(&modules, ?modules1);
                        //@ assert [_]d->owner |-> ?owner1;
                        //@ ghost_set_match_member_handle(modulesId, owner1);
                        //@ lseg_separate(modules1, owner1);
                        //@ open kernel_module(modulesId, devicesId)(owner1);
                        {
                            int refCount = d->owner->ref_count;
                            //@ produce_limits(refCount);
                            //@ assert contrib_sum(?contribSumId_, _, _);
                            //@ contrib_sum_nonnegative(contribSumId_);
                            d->owner->ref_count = refCount - 1;
                        }
                        //@ d->useCount--;
                        //@ int contribSumId1 = owner1->contrib_sum_id;
                        //@ assert contrib(contribSumId1, ?useCount1);
                        //@ counting_match_fraction(module_contrib_sum_id, owner1);
                        //@ dispose_contrib(contribSumId1);
                        //@ close [memberHandleFrac]ghost_set_member_handle_wrapper(pair(devicesId, d), unit);
                        //@ destroy_ticket(ghost_set_member_handle_wrapper, pair(devicesId, d));
                        /*@
                        if (useCount1 == 0) {
                            stop_counting(file_ops_wrapper2, pair(d, device));
                            open [1]file_ops_wrapper2(_, _);
                            open [1]file_ops_wrapper1(_, _, _);
                            open file_ops_wrapper2(_, _);
                            open file_ops_wrapper1(_, _, _);
                        }
                        @*/
                        //@ create_contrib(contribSumId1, useCount1 - 1);
                        //@ destroy_ticket(file_ops_wrapper2, pair(d, device));
                        //@ close kernel_module(modulesId, devicesId)(owner1);
                        //@ lseg_add(modules1);
                        //@ lseg_append_final(modules1);
                        //@ destroy_ticket(device_state, d);
                        //@ destroy_ticket(device_ops2, d);
                        //@ close device(modulesId, devicesId)(d);
                        //@ close lseg(d, 0, _, device(modulesId, devicesId));
                        done = true;
                    } else {
                        d = d->next;
                        //@ close device(modulesId, devicesId)(d0);
                        //@ lseg_add(devices_);
                    }
                }
            }
            //@ lseg_append_final(directory);
            //@ close kernel_inv(modulesId, devicesId)();
            lock_release(kernelLock);
            free(name);
            
        } else {
            exitMenu = true;
        }
    }
    socket_close(socket);
}

int main() //@ : main_full(MockKernel)
    //@ requires module(MockKernel, true);
    //@ ensures true;
{
    struct server_socket *serverSocket = 0;
    
    //@ open_module();
    //@ int modulesId = create_ghost_set<struct module *>();
    //@ int devicesId = create_ghost_set<struct device *>();
    //@ close lseg(0, 0, nil, kernel_module(modulesId, devicesId));
    //@ close lseg(0, 0, nil, device(modulesId, devicesId));
    //@ close kernel_inv(modulesId, devicesId)();
    //@ close create_lock_ghost_args(kernel_inv(modulesId, devicesId), nil, nil);
    kernelLock = create_lock();
    
    //@ assert pointer(&kernelLock, ?kernelLock_);
    //@ leak pointer(&kernelLock, kernelLock_);
    
    //@ leak lock(kernelLock_, _, kernel_inv(modulesId, devicesId));
    
    serverSocket = create_server_socket(12345);
    while (true)
        //@ invariant [_]pointer(&kernelLock, kernelLock_) &*& [_]lock(kernelLock_, _, kernel_inv(modulesId, devicesId)) &*& server_socket(serverSocket);
    {
        struct socket *socket = server_socket_accept(serverSocket);
        //@ close kernel_inv_info(modulesId, devicesId);
        //@ close thread_run_data(handle_connection)(socket);
        thread_start(handle_connection, socket);
    }
}
