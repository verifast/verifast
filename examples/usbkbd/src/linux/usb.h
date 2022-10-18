#ifndef _LINUX_USB_H
#define _LINUX_USB_H

#include <linux/mod_devicetable.h>
#include <linux/errno.h>
#include <linux/usb/ch9.h>
#include <linux/slab.h>
#include <linux/types.h>
#include <linux/device.h>

	
#define USB_DEVICE_ID_MATCH_DEVICE  0x0003 // original: (USB_DEVICE_ID_MATCH_VENDOR | USB_DEVICE_ID_MATCH_PRODUCT)
#define USB_DEVICE_ID_MATCH_DEV_RANGE 0x000C // original: (USB_DEVICE_ID_MATCH_DEV_LO | USB_DEVICE_ID_MATCH_DEV_HI)
#define USB_DEVICE_ID_MATCH_DEVICE_AND_VERSION 0x000F // original: (USB_DEVICE_ID_MATCH_DEVICE | USB_DEVICE_ID_MATCH_DEV_RANGE)
#define USB_DEVICE_ID_MATCH_DEV_INFO 0x0070  /* original: \
	(USB_DEVICE_ID_MATCH_DEV_CLASS | \
	USB_DEVICE_ID_MATCH_DEV_SUBCLASS | \
	USB_DEVICE_ID_MATCH_DEV_PROTOCOL)*/
#define USB_DEVICE_ID_MATCH_INT_INFO 0x0380 /* original: \
	(USB_DEVICE_ID_MATCH_INT_CLASS | \
	USB_DEVICE_ID_MATCH_INT_SUBCLASS | \
	USB_DEVICE_ID_MATCH_INT_PROTOCOL) */


#define URB_SHORT_NOT_OK        0x0001  /* report short reads as errors */
#define URB_ISO_ASAP            0x0002  /* iso-only, urb->start_frame ignored */
#define URB_NO_TRANSFER_DMA_MAP 0x0004  /* urb->transfer_dma valid on submit */
#define URB_NO_FSBR             0x0020  /* UHCI-specific */
#define URB_ZERO_PACKET         0x0040  /* Finish bulk OUT with short packet */
#define URB_NO_INTERRUPT        0x0080  /* HINT: no non-error interrupt needed */
#define URB_FREE_BUFFER         0x0100  /* Free transfer buffer with the URB */

/*---------------------------------------------------------*
 * Probe-Disconnect                                        *
 *---------------------------------------------------------*/

/* id is the ID of the usb_device_id table of the module that matched with the usb device (source: O'Really's Linux Device Drivers book)
 * This function is called from usb_probe_device, which claims its caller locks the Linux device (which is associated with an usb_interface)
 *
 * "The probe() and disconnect() methods are called in a context where they can sleep, but they should avoid abusing the privilege" -- usb.h
 *
 * usb.h does not state whether the interface data (see get_intfdata) is guaranteed to be zero when probe is entered.
 * If two probes are called after each other (so two drivers, first driver's probe returns an error, so the second
 * driver's probe is called), can the second driver assume the intfdata is zero?
 * So either this is not guaranteed at all, or it is done by Linux's USB or device driver model implementation
 * before probe is called, or modules are responsible themself for setting it zero if probe fails.
 * Empirical testing (Linux 2.6.35) confirms it is _not_ done by Linux's USB or device model implementation.
 * The specifications about probe in usb.h do not state probe does have to set intfdata back to zero on error (Linux 2.6.39),
 * but Linux sometimes contains unwritten rules.
 * Different drivers have been studied (namely drivers/input/misc/ati_remote2.c, drivers/input/tablet/kbtab.c,
 * drivers/net/usb/ipheth.c, drivers/net/usb/rtl8150.c, drivers/net/wimax/i2400m/usb.c,
 * drivers/net/wireless/ath/ath9k/hif_usb.c, drivers/staging/keucr/usb.c, drivers/staging/lirc/lirc_ttusbir.c,
 * drivers/usb/class/cdc-wdm.c, drivers/usb/class/usblp.c, drivers/usb/misc/cypress_cy7c63.c,
 * drivers/usb/misc/cytherm.c, drivers/usb/misc/trancevibrator.c, drivers/usb/misc/usbled.c,
 * drivers/usb/misc/usbsevseg.c, drivers/usb/wusbcore/cbaf.c, sound/usb/card.c)
 * Only one driver (drivers/net/usb/ipheth.c) did not set intfdata back to zero
 * after probe fails, but this might be a driver bug (if breaking an unwritten rule is considered a bug).
 * So it's hard to draw hard conclusions, so we do what is safest: we do not assume probe can assume
 * intfdata is initially zero, and we disallow probe to set intfdata to nonzero values if probe fails.
 * This way we are correct and safe in both cases.
 * 
 * Disconnect does not need to set intfdata to zero, since usb core already does this (in usb_unbind_interface, Linux 2.6.39).
 */
typedef int vf_usb_operation_probe_t(struct usb_interface *iface, /*const*/ struct usb_device_id *id);      
	//
	// We currently disallow submitting urbs even for a different error than -ENODEV (which might be a little too strict)
	// See also vf_usb-operation_disconnect_t.
	//
	/*@ requires
		usb_interface(this, ?disconnect_cb, iface, _, ?originalData, false, ?fracsize)
		&*& permission_to_submit_urb(?urbs_submitted, false)
		&*& not_in_interrupt_context(currentThread)
		&*& [fracsize]probe_disconnect_userdata(this, disconnect_cb)()
		&*& [?callback_link_f]usb_probe_callback_link(this)(disconnect_cb);
	@*/
	/*@ ensures
		not_in_interrupt_context(currentThread)
		&*& [callback_link_f]usb_probe_callback_link(this)(disconnect_cb)
		&*& result == 0 ? // success
			// probe_disconnect_userdata is not returned, so the user "has to put it somewhere",
			// and give it back with _disconnect.
			// you can put it in usb_interface: it includes userdata which
			// can eat whatever probe_disconnect_userdata contains.
			usb_interface(this, disconnect_cb, iface, _, ?data, true, fracsize)
			//&*& permission_to_submit_urb(_, false)
		: // failure
			usb_interface(this, disconnect_cb, iface, _, ?data, false, fracsize)
			
			// XXX meh, the permission count thing is annoying and I don't think it actually
			// solves much at all, so made it "_" for now.
			&*& permission_to_submit_urb(_, false)
			&*& data == originalData || data == 0
			&*& [fracsize]probe_disconnect_userdata(this, _)()
		;
	@*/

// Called from usb_unbind_device, which claims its caller locks the linuxdevice.
// Probe is called from usb_probe_interface which claims it is "called from driver core with dev locked" (quoted),
// so there is no concurrency between probe and disconnect.
//
// We know disconnect cannot be called _before_ probe (e.g. if a device is connected and disconnected very quickly
// and some scheduling took place), because it is documented in Documentation/usb/callbacks.txt.
//
// Disconnect can be called while the completion handler is still running(empirically tested, linux 2.6.32).
// It is unclear, however, whether the completion handler can still be called while the disconnect handler
// is being executed.
// usbkbd relies on assuming this is true.
// Otherwise, the follow scenario would be possible:
// _irq enters
// _disconnect enters
// _disconnect calls kill_urb
// _irq leaves
// _close is called
// _open is called
// _open submit new URB
// _irq enters
// _disconnect calls input_unregister
// _irq calls input_report
// Note that it is not allowed to call input_report while input_unregister has been called,
//   while this actually happens in the above scenario.

typedef void vf_usb_operation_disconnect_t (struct usb_interface *intf);
	/*@ requires usb_interface(?probe_cb, this, intf, ?dev, ?data, true, ?fracsize) &*& not_in_interrupt_context(currentThread)
		&*& [?callback_link_f]usb_disconnect_callback_link(this)(probe_cb);
	@*/
	/*@ ensures usb_interface(probe_cb, this, intf, dev, _, false, fracsize)
		&*& not_in_interrupt_context(currentThread)
		&*& [fracsize]probe_disconnect_userdata(_, this)()
		&*& [callback_link_f]usb_disconnect_callback_link(this)(probe_cb)
		
		// You're not allowed to submit URB's after disconnect (see usb.[ch] specs),
		// so give it back.
		&*& permission_to_submit_urb(_, false)
	;
	@*/


	
/*---------------------------------------------------------*
 * Driver                                                  *
 *---------------------------------------------------------*/


/*@
predicate usb_driver(struct usb_driver *driver, struct usb_device_id *id_table, int table_size, vf_usb_operation_probe_t *probe, vf_usb_operation_disconnect_t *disconnect) =
	driver->name |-> ?name
	&*& driver->probe |-> probe
	&*& driver->disconnect |-> disconnect
	&*& driver->id_table |-> id_table
	
	&*& [_]chars(name, _, ?cs) &*& mem('\0',cs) == true
	&*& is_vf_usb_operation_probe_t(probe) == true
	&*& is_vf_usb_operation_disconnect_t(disconnect) == true
	
	&*& usb_device_id_table(table_size, id_table);
@*/

// Not closeable to enforce usage of usb_driver_register.
//@ predicate usb_driver_registered(struct usb_driver *driver, struct usb_device_id *id_table, int table_size, vf_usb_operation_probe_t *probe, vf_usb_operation_disconnect_t *disconnect);

// To be filled in by the user (the developper of the usb driver).
// This would be a predicate family, but we need two "parameterizationing functions",
// while _disconnect does not get _probe as an argument (currently).
// so we just do it with a regular predicate for now, but should be fixed XXX.
// ---> update: it seems to work with multiple parameterization functions, migrated to that.
// tip: The user probably want to put "if probe == ... then disconnect = ..." in its definition.
//@ predicate_family probe_disconnect_userdata(vf_usb_operation_probe_t *probe, vf_usb_operation_disconnect_t *disconnect)();

/**
 * Typically the driver developer puts in what probe and disconnect are so that in callbacks he can use that
 * info.
 */
//@ predicate_family usb_probe_callback_link(vf_usb_operation_probe_t probe)(vf_usb_operation_disconnect_t *disconnect);
//@ predicate_family usb_disconnect_callback_link(vf_usb_operation_disconnect_t disconnect)(vf_usb_operation_probe_t *probe);

int usb_register(struct usb_driver *driver);
	/*@ requires
		usb_driver(driver, ?id_table, ?table_size, ?probe, ?disconnect)
		&*& usb_probe_callback_link(probe)(disconnect)
		&*& usb_disconnect_callback_link(disconnect)(probe)
		&*& not_in_interrupt_context(currentThread)
		&*& probe_disconnect_userdata(probe, disconnect)();
	@*/
	/*@ ensures
		not_in_interrupt_context(currentThread)
		&*& result == 0 ? // success
			usb_driver_registered(driver, id_table, table_size, probe, disconnect)
		: // faulure
			usb_driver(driver, id_table, table_size, probe, disconnect)
			&*& probe_disconnect_userdata(probe, disconnect)()
			&*& usb_probe_callback_link(probe)(disconnect)
			&*& usb_disconnect_callback_link(disconnect)(probe);
	@*/

// UNSAFE: deregistration is not enforced to happen on driver unload.
//         (this is not done because unload safety was not a target property)
void usb_deregister(struct usb_driver *driver);
//@ requires usb_driver_registered(driver, ?id_table, ?table_size, ?probe, ?disconnect) &*& not_in_interrupt_context(currentThread);
/*@ ensures usb_driver(driver, id_table, table_size, probe, disconnect)
	&*& usb_probe_callback_link(probe)(disconnect)
	&*& usb_disconnect_callback_link(disconnect)(probe)
	&*& not_in_interrupt_context(currentThread)
	&*& probe_disconnect_userdata(probe, disconnect)();
@*/

struct usb_host_endpoint {
	struct usb_endpoint_descriptor          desc;
	//struct usb_ss_ep_comp_descriptor        ss_ep_comp;
	//struct list_head                urb_list;
	//void                            *hcpriv;
	//struct ep_device                *ep_dev;        /* For sysfs info */
	//
	//unsigned char *extra;   /* Extra descriptors */
	//int extralen;
	//int enabled;
};


struct usb_device {
	struct usb_host_endpoint ep0;
	
	struct usb_device_descriptor descriptor;
	
	struct device dev;
	
	char *product;
	char *manufacturer;
	char *serial;
};
/*@ predicate usb_device(struct usb_device *usb_device, struct usb_endpoint_descriptor *ep0;) =
	usb_device_private(usb_device)
	
	// struct usb_device contains the implicit endpoint 0 (field "ep0").
	// If you have a device, the endpoint descriptor of ep0 thus exists.
	// So provide it here such that the API user can talk about the implicit endpoint 0.
	//
	//
	&*& usb_endpoint_descriptor(ep0, USB_DIR_OUT, USB_ENDPOINT_XFER_CONTROL, ?pipe)
	// According to USB 2.0 specs section 9.6.6, the bEndpointAddress is encoded
	// as quoted: "
	// 	Bit 3...0: The endpoint number
	//	Bit 6...4: Reserved, reset to zero
	//	Bit 7:
	//	Direction, ignored for
	//	control endpoints
	//	0 = OUT endpoint
	//	1 = IN endpoint
	//     " (end quote).
	// So, for the implicit control endpoint 0, 0 is indeed a valid bEndpointAddress.
	// It is not clear however whether a nonzero endpoint address is a valid address
	// (the direction can supposedly be set to garbage).
	// We set endpoint address to zero here to make stuff works, but in fact
	// we should do something smarter that keeps into account that multiple addresses
	// might be valid (well, we don't need that if USB core doesn't accept that, which
	// I don't know yet and I should look at it...)
	// XXX.
	&*& usb_endpoint_descriptor_data(ep0, 0 /* = endpoint address */)
	&*& usb_device->product |-> ?product &*& string(product, _)
	&*& usb_device->manufacturer |-> ?manufacturer &*& string(manufacturer, _)
	&*& usb_device->serial |-> ?serial &*& string(serial, _)	
;
@*/


//@ predicate usb_device_private(struct usb_device *usb_device;);



/*---------------------------------------------------------*
 * URB                                                     *
 *---------------------------------------------------------*/



/*
Semantics
=========
	Predicates:
		current_thread_in_cb(threadId thread, bool deferred_data_xfer)
		urb_struct
		cb_data_in() <-- userdef
		cb_data_out() <-- userdef
		kill_handle()
	
		predicate times (predicate() p, int times) =
			times > 0
			&*& times == 1 ?
				p()
			:
				p()
				&*& times(p, times-1)
		;


	----init
	pre
		emp
	post
		urb_struct


	----submit(ghost bool deferred_data_xfer)
	pre
		urb_struct
		* deferred_data_xfer ?
			current_thread_in_cb(currentThread, false)
		:
			cb_data_in
	post
		deferred_data_xfer ?
			current_thread_in_cb(currentThread, true)
		:
			kill_handle
	

	-----kill(ghost int count)
	pre
		times(kill_handle, count)
		
	post
		// We know you get cb_data_out (and not cb_data_in), because
		// a completion handler is also called if the urb cancels because
		// of a kill (so it's always called).
		times(cb_data_out, count)
	
	
	----cb
	pre
		cb_data_in * urb_struct * current_thread_in_cb(currentThread, false)
	post
		current_thread_in_cb(currentThread, ?deferred_data_xfer)
		* deferred_data_xfer ?
			cb_data_in
		:
			// in case of a resubmit in the cb without deferred_data_xfer,
			// it's ok that we also give back cb_data_out.
			// Indeed, there is a match/couple of cb-data-out(owned by usb)
			// and kill_handle(owned outside usb) in
			// that case, which is the invariant we have to maintain.
			// (assuming you can't kill inside a cb)
			cb_data_out
*/




// supposed to be non-closeable.
//@ predicate current_thread_in_cb(int thread, bool deferred_data_xfer);


// original syntax "typedef void (*usb_complete_t)(struct urb *);"
// but we can't put the "*" if we want verifast to parse it. So we do it with 2 typedefs.
// 
// The verification API does not allow getting an usb_interface in a completion
// handler. This is important if the completion handler is called concurrently
// with the disconnect callback.
//
// Caller is usb_hcd_giveback_urb on my system
// (empirically found, thanks to http://stackoverflow.com/questions/4141324/function-caller-in-linux-kernel)
//

typedef void usb_complete_t_no_pointer (struct urb *urb);
	/*@ requires
		urb_struct(true,
			urb, ?usb_dev, ?buffer, ?buffer_dma, ?buffer_alloc_size, ?user_alloc_dma, ?complete, ?context, ?setup
		)
		&*& buffer != 0
		&*& permission_to_submit_urb(?urbs_submitted, true)
		&*& complete_t_pred_fam(this)(?fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
		&*& current_thread_in_cb(currentThread, false);
	@*/
	/*@ ensures 
		permission_to_submit_urb(_, true)
		&*& current_thread_in_cb(currentThread, ?deferred_data_xfer)
		&*& deferred_data_xfer ?
			complete_t_pred_fam(this)(fracsize,
				urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
			)
		:
			complete_t_pred_fam_out(this)(fracsize,
				urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
			)
		;
	@*/


typedef usb_complete_t_no_pointer* usb_complete_t;



/*@
// Not all "standard urb arguments" here, otherwise user can't open urb_struct and
// edit some fields.
predicate urb_private(struct urb *urb, bool initialized, struct usb_device *dev, dma_addr_t data_dma, int actual_allocated_data_size, int flags, void *setup_packet;);
@*/

/* actual_allocated_data_size is not the urb->transfer_buffer_length field but the actually allocated amount of bytes.
 * user_allocated_dma indicates whether the buffer memory (data) is dma-aware allocated _by the user_.
 * data is the data the USB device sends (actually a buffer where this is stored). Do not confues with "context", a
 * pointer passed to the callback.
 */
/*@ predicate urb_struct(
	bool initialized,

	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup;
	) =
	
	// You can't write the status yourself (so we need a fraction here).
	// We explicitly specify some fraction size to avoid opening the
	// struct, stealing half of the fraction, and closing the struct again.
	[1/2]urb->status |-> ?status
	
	// The URB initialization function enforces dev is a proper device (when that function is called)
	// 
	// We allow writing to the struct field, but you can't write garbage in it
	// because it is enforced to be the same dev as in urb_private.
	&*& urb->dev |-> usb_dev
	
	&*& urb->transfer_flags |-> ?data_transfer_flags
	
	&*& urb->transfer_dma |-> buffer_dma
	
	// you can't overwrite it with non-working garbage, since
	// before submitting the URB, you have to have the complete_t_pred_fam.
	&*& urb->context |-> context
	
	&*& urb != 0
	
	// We disallow modifying data_transfer_flags and others by having them
	// as the arguments in urb_private. If you want to set
	// data, you will have to convert urb_private(old_flags)
	// to urb_private(new_flags) with urb_transfer_flags_add_no_transfer_dma_map.
	// urb_struct states some properties about the flags.
	// This way we:
	// * allow setting flags with struct field access (instead of a API incompatible wrapper function)
	// * disallow setting flags not supported by the verification approach
	// * disallow setting flags and submitting DMA-mapped memory after submitting urbs (because then you don't own urb_struct anymore)
	// * disallow setting URB_NO_TRANSFER_DMA_MAP whithout having DMA-mapped memory.
	// * disallow secretly putting garbage in urb->transfer_dma.
	// * disallow secretly closing urb_struct with another actual_allocated_data_size argument.
	//   This is important because the data owned by this predicate must be at least as large as
	//   the buffer size reported to the USB API (the urb->transfer_buffer_length field, set with usb_fill_int_urb).
	// - We disallow changing setup_packet by hand (instead of calling fill_control_urb), but this might be too strict (not checked)
	&*& urb_private(urb, initialized, usb_dev, buffer_dma, buffer_alloc_size, data_transfer_flags, setup)
	
	&*& (buffer != 0 ?
		uchars(buffer, buffer_alloc_size, ?cs)
	:true)
	
	&*& (initialized ?
		complete_t_ghost_param(complete, complete)
	:true)
	
	&*& (user_alloc_dma ?
		buffer != 0

		&*& true == ((data_transfer_flags | URB_NO_TRANSFER_DMA_MAP) == data_transfer_flags)
		
		// Must be allocated as DMA-consistent memory,
		// and you aren't allowed to secretly free it
		// (so after a function consumes urb_struct you don't own urb-alloc_coherent_block anymore)
		// See also the comment above at "urb_private".
		&*& usb_alloc_coherent_block(buffer, usb_dev, buffer_alloc_size, buffer_dma)
	:
		true)
	
	&*& setup != 0 ? // see comments in fill_control_urb
		//chars(setup, ?setup_packet_cs) // YYY
		uchars(setup, 8, ?setup_packet_cs)
	:
		true
		
;

predicate urb_struct_maybe(bool initialized, 
struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup;) =
	urb == 0 ?
		true // which means you can choose garbage for the other parameters.
	:
		urb_struct(initialized, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup)
	;

// See urb_struct.
lemma void urb_transfer_flags_add_no_transfer_dma_map(struct urb *urb, void *data, dma_addr_t data_dma, int data_size, int flags);
	// There is no need to have usb_alloc_coherent_block in the pre- an postcondition to enforce
	// correct arguments, since usb_alloc_coherent_block is already in the usb_struct predicate.
	requires
		urb_private(urb, ?initialized, ?dev, ?original_dma, data_size, ?original_flags, ?setup_packet)
		&*& true == ((original_flags | URB_NO_TRANSFER_DMA_MAP) == flags);
	ensures
		urb_private(urb, initialized, dev, data_dma, data_size, flags, setup_packet)
	
		// VeriFast cannot prove that (y == (x | flags)) implies (y == (y | flags)).
		// So we provide this knowledge here:
		&*& true == ((flags | URB_NO_TRANSFER_DMA_MAP) == flags)
		;

/* The URB has been submitted, this represents the rights you have for
 * operations on submitted URBs.
 * 
 * Note: we need to keep the DMA memory address (as parameter) since it doesn't change if it's set
 * by the user and we need this address if we want to free the DMA memory later.
 */
predicate urb_submitted(
	real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
);

/* Useful for postconditions where the urb might or might not be (re)submitted. */
predicate urb_maybe_submitted(
bool submitted,
real fracsize,
struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup) =
	submitted ?
		urb_submitted(
			fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
	:
		urb_struct(true, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup)
		&*& complete_t_pred_fam(complete)(fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
		
		
		
		// This is not leaked if the URB is killed.
		// But it is if the URB is not killed... do we enforce killing? XXX
	;

/* You can't submit urbs in all possible callbacks. This predicate makes sure you only
 * can submit urbs if you have the permission (represented by this predicate).
 * The integer counter represents the amount of urbs submitted. The actual value
 * is not intresting, but it is useful to specify whether the value has increased
 * e.g. a postcondition may state the value may not increase if the function of
 * the postcondition returns an error code.
 *
 * inside_completion_handler is true for submitting URBs inside completion handlers,
 * this is important because the URB submitted in a completion handlder is actually
 * submitted after the completion handler returns (at least we ASSUME so), and thus
 * the completion handler can still access its cb_data which is then consumed when
 * the cb returns.
 */
predicate permission_to_submit_urb(int nb_urbs_submitted, bool inside_completion_handler);
@*/

struct urb *usb_alloc_urb(int iso_packets, gfp_t mem_flags);
/*@ requires
	// iso_packets must be null for non-isochronous URBs, and we don't support isochronous URBs yet.
	iso_packets == 0
	
	&*& mem_flags != GFP_ATOMIC ?
		not_in_interrupt_context(currentThread)
	:
		true
	;
@*/
/*@ ensures
	(mem_flags != GFP_ATOMIC ?
		not_in_interrupt_context(currentThread)
	:
		true
	)
	&*& result == 0 ?
		true
	:
		urb_struct(false, result, ?dev, 0, ?data_dma, ?data_size, false,
			0, // set to 0 in usb_init_urb (assuming memsetting 0 results in zeroed function pointers)
			0, // analogues (assuming memsetting 0 results in int with value 0)
			0
		)
	;
@*/

/* Freeing the zero-address is allowed (this is not documented but it is implemented and used like that).
 *
 * Only calls (indirectly) functions like kfree, container_of, atomic_dec_and_test, so it is probably safe
 * in interrupt context.
 */
void usb_free_urb(struct urb *urb);
	// We need "urb_struct_maybe" here, otherwise we would have an "urb!=0?urb_struct(...)&*&...:true;" block in
	// both the pre and postcondition with the postcondition refering to matched variables
	// from the precondition, which does not work because they were matched inside the if.
	// An alternative is maybe to keep as much as needed outside of the urb_struct predicate (not tried),
	// but that would be the "if everything is global, it'll work" approach.
	//@ requires urb_struct_maybe(?initialized, urb, ?dev, ?data, ?data_dma, ?data_size, ?has_dma, ?complete_fn, ?context, ?setup_packet);
	/*@ ensures
		urb == 0 ?
			true // freeing zero.
		:
			(data != 0 ?
				uchars(data, data_size, ?cs)
		
				&*& has_dma?
					usb_alloc_coherent_block(data, dev, data_size, data_dma)
				:
					true
			:true)
			
			&*& (setup_packet != 0 ?
				uchars(setup_packet, 8, ?setup_packet_cs)
			:true)
	;
	@*/

//@ predicate usb_alloc_coherent_block(void *ptr; struct usb_device *dev, int size, int dma);

void *usb_alloc_coherent(struct usb_device *dev, size_t size, gfp_t mem_flags, dma_addr_t* dma);
	/*@ requires
		not_in_interrupt_context(currentThread) // might be unnecessarry, replace with mem_flags==ATOMIC-check if confirmation found / sources checked.
		&*& size >= 0 &*& integer(dma, ?ptr);
	@*/
	/*@ ensures 
		not_in_interrupt_context(currentThread)
		&*& result == 0 ?
			integer(dma, ptr)
		:
			usb_alloc_coherent_block(result, dev, size, ?ptr2) &*& integer(dma, ptr2)
			&*& uchars(result, size, ?cs)
		;
	@*/

/* Freeing the zero-address is allowed (this is not documented but it is implemented and used like that) */
void usb_free_coherent(struct usb_device *dev, size_t size, void *addr, dma_addr_t dma);
	/*@ requires
		not_in_interrupt_context(currentThread) // might be unnecessarry
		&*& addr == 0 ?
			true
		:
			usb_alloc_coherent_block(addr, dev, size, dma)
			&*& uchars(addr, size, ?cs)
		;
	@*/
	//@ ensures not_in_interrupt_context(currentThread);

/*@
// fracsize is here because otherwise we would have to pass
// complete_t_pred_fam in the precondition to know fracsize.
// While that could work, it doesn't if the caller doesn't
// own complete_t_pred_fam itself before calling usb_submit_urb.
//
// Q: This way you can secretly put any fracsize you want? A: Not really,
// the fracsize is only used if complete_t_pred_fam is passed
// as well, which enforces correct fracsize. In other words:
// yes you can pass any fracsize you want, but only if it's unused.
// The reason we pass this is because VeriFast does not allow
// reusing my_ghost_argument in postcondition if it's passed
// in the precondition in the form similar to
// "condition ? predicate(?my_ghost_argument) : true"
predicate usb_submit_urb_ghost_arg(bool deferred_data_xfer, real fracsize) = true;
@*/

// You shouldn't submit URBs twice, according to http://kerneltrap.org/mailarchive/linux-usb/2008/9/19/3343094
int usb_submit_urb(struct urb *urb, gfp_t mem_flags);
/*@ requires
	// Possible in interrupt context.
	
	urb_struct(true,
		urb, ?usb_dev, ?buffer, ?buffer_dma, ?buffer_alloc_size, ?user_alloc_dma, ?complete, ?context, ?setup
	)
	
	&*& buffer != 0
	&*& permission_to_submit_urb(?urbs_submitted, ?inside_completion)
	&*& (mem_flags != GFP_ATOMIC ?
		not_in_interrupt_context(currentThread)
	:
		true
	)
	&*& usb_submit_urb_ghost_arg(?deferred_data_xfer, ?fracsize)
	&*& deferred_data_xfer ?
		current_thread_in_cb(currentThread, false)
	:
		complete_t_pred_fam(complete)(fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
	;
@*/
/*@ ensures
	(mem_flags != GFP_ATOMIC ?
		not_in_interrupt_context(currentThread)
	:
		true
	)
	
	&*& result == 0 ? // success
		permission_to_submit_urb(urbs_submitted+1, inside_completion)
		&*& deferred_data_xfer ?
			current_thread_in_cb(currentThread, true)
		:
			urb_submitted(
				fracsize,
				urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
			)
	: // failure
		permission_to_submit_urb(urbs_submitted, inside_completion)
		&*& urb_struct(true,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
		&*& deferred_data_xfer ?
			current_thread_in_cb(currentThread, false)
		:
			complete_t_pred_fam(complete)(
				fracsize,
				urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
			)
	;
@*/


/*@
predicate times_urb_submitted (int times, real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
	) =

	times >= 0
	&*& times == 0 ?
		true
	:
		urb_submitted(fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
		&*& times_urb_submitted(times-1, fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
;

predicate times_complete_t_pred_fam_out (int times, real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
	) =
	
	times >= 0
	&*& times == 0 ?
		true
	:
		complete_t_pred_fam_out(complete)(fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
		&*& times_complete_t_pred_fam_out(times-1,
			fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
;


@*/

// UNSAFE: We currently don't enforce that "This routine [usb_kill_urb] should
//         not be called by a driver after its disconnect method has returned."
//         -- urb.c
//         (this is not done because unload safety was not a target property)
//
// Note that this does not disallow killing URBs that have been sent but are already complete.
// It is unclear whether the intended official specifications allow killing an URB twice (without resubmitting).
// but http://www.spinics.net/lists/linux-input/msg01146.html states you can kill an unsubmitted URB,
// which is probably true (usbkbd does it by killing the URB twice: in _disconnect and in _close).
// It probably should be possible to kill an URB that's not "owned", i.e. one thread owns the URB and submits it and stuff,
// and another thread kills it somewhere in some cleanup function (e.g. _disconnect in usbkbd).
// To not make it more complex, we don't support that for now.
// In a "world of unverified drivers", it's probably safer to have that urb-kill in the _disconnect in usbkbd,
// because the "unverified world" might incorrectly not call _close and kill thus not kill the URB (?),
// but we when verifying we have to assume that other modules are correct (otherwise we can't verify at all if a module contains calls to other modules).
//
// No specs about calling it concurrently, but the implementation calls atomic_inc, and usb_hcd_unlink_urb which spinlocks,
// so we assume calling it concurrently is allowed (which doesn't mean the specs here support it).
//
// XXX update informal specs to formal specs.
//
void usb_kill_urb(struct urb *urb);
/*@ requires
	// We allow killing URBs that are submitted in completion handlers.
	// Note that this does not impose the get-data-back-twice (1x for the urb_submitted obtained for the URB
	// submitted outside the completion handler and 1x for the one submitted inside), because
	// the giveback-parameter must be false if the urb_submitted is not given back to the USB core,
	// (and yes you can kill twice but that must be allowed anyway, as long as you dan't get double-data).
	times_urb_submitted(?times, ?fracsize,
		urb, ?usb_dev, ?buffer, ?buffer_dma, ?buffer_alloc_size, ?user_alloc_dma, ?complete, ?context, ?setup
	)
	&*& not_in_interrupt_context(currentThread);
@*/
/*@ ensures
	not_in_interrupt_context(currentThread)
	&*& times_complete_t_pred_fam_out(times, fracsize,
		urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
	)
	;
@*/


// "context" is the context-field of the usb_struct.
// fracsize can be used to pass the fraction size _probe gets up to the completion handler,
// such that it can be passed back when killing the urb such that _disconnect
// can give the correc fraction size back. Yeah, it's a hack. It's ugly. It's no low coupling at all. XXX.
// data is the data of the URB.
/*@
predicate_family complete_t_pred_fam(usb_complete_t complete)(
	real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
	
);

predicate_family complete_t_pred_fam_out(usb_complete_t complete)(
	real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
	);
@*/

/* There is a problem that the precondition of usb_fill_int_urb
 * cannot just contain is_usb_complete_t_no_pointer(complete_fn)== true
 * because complete_fn is of the wrong type. We solve this by introducing the predicate
 * complete_t_ghost_param. This funny predicate just requires two arguments of
 * different types, and then states in its definition that the arguments must be the
 * same.
 */
/*@ predicate complete_t_ghost_param(usb_complete_t_no_pointer *complete_no_ptr, usb_complete_t complete;) =
	is_usb_complete_t_no_pointer(complete) == true
	&*& complete_no_ptr == complete;
	// There is no complete_t_pred_fam(complete)() here,
	// urb_struct owns complete_t_ghost_param, but complete_t_pred_fam is only
	// consumed when the URB is submitted, not just when it existst.
@*/

static inline void usb_fill_int_urb(struct urb *urb,
	struct usb_device *dev,
	/*unsigned*/ int pipe,
	void *transfer_buffer,
	int buffer_length,
	usb_complete_t complete_fn,
	void *context,
	int interval); // XXX negative intervals ok??
	/*@ requires urb_struct(_, urb, _, 0, ?data_dma, ?data_size, ?data_transfer_flags, ?original_complete_fn, ?original_context, ?setup_packet)
		&*& [?f]usb_device(dev, ?ep0)
		&*& [?f2]usb_endpoint_descriptor(?epd, USB_DIR_IN, ?xfer_type, pipe)
		&*& transfer_buffer != 0
		&*& uchars(transfer_buffer, ?length_transfer_buffer, ?cs)
		&*& length_transfer_buffer >= buffer_length
		&*& complete_t_ghost_param(complete_fn, complete_fn)
		;
	@*/
	// The length in the urb struct field is the amount of data allocated, which might
	// be different from the buffersize the URB thinks it has.
	/*@ ensures urb_struct(true, urb, dev, transfer_buffer, data_dma, length(cs), data_transfer_flags, complete_fn, context, setup_packet)
		&*& [f]usb_device(dev, ep0)
		&*& [f2]usb_endpoint_descriptor(epd, USB_DIR_IN, xfer_type, pipe);
	@*/

void usb_fill_control_urb(struct urb *urb,
	struct usb_device *dev,
	/*unsigned*/ int pipe,
	unsigned char *setup_packet,
	void *transfer_buffer,
	int buffer_length,
	usb_complete_t complete_fn,
	void *context);
// XXX this is becoming copy-pasteware from usb_fill_int_urb :(
// XXX "The setup_packet must always be set, so it cannot be located in highmem." -- usb.h. highmem??

/*@ requires urb_struct(_, urb, _, 0, ?data_dma, ?data_size, ?data_transfer_flags, ?original_complete_fn, ?original_context, 0)
		&*& [?f]usb_device(dev, ?ep0)
		
		// XXX is the direction always OUT for control? My master thesis said there was always
		// a "control ep0 in and a control ep0 out", so back then I thought no but it doesn't
		// argue why that was the case.
		&*& [?f2]usb_endpoint_descriptor(?epd, ?usb_dir, ?xfer_type, pipe)
		
		&*& transfer_buffer != 0
		&*& uchars(transfer_buffer, ?length_transfer_buffer, ?cs)
		&*& length_transfer_buffer >= buffer_length
		
		&*& complete_t_ghost_param(complete_fn, complete_fn)
		
		
		// control specific:
			&*& setup_packet != 0
			// usb.h does not state any requirements for the setup packet, but USB specs state that "Every Setup packet has eight bytes."
			// so let's enforce that.
			&*& uchars(setup_packet, 8 /* USB specs enforced here*/, ?setup_packet_cs)
	;
	@*/
	/*@ ensures urb_struct(true, urb, dev, transfer_buffer, data_dma, length(cs), data_transfer_flags, complete_fn, context, setup_packet)
		&*& [f]usb_device(dev, ep0)
		&*& [f2]usb_endpoint_descriptor(epd, usb_dir, xfer_type, pipe);
	@*/



/*@ predicate usb_host_interface(struct usb_host_interface *usb_host_interface) = 
	usb_interface_descriptor(& usb_host_interface->desc, ?bNumEndpoints, ?bInterfaceNumber) &*&
	bNumEndpoints > 0 ?
		// This is actually an array, we currently only support the
		// first element here (if there is a first element).
		[?f]usb_host_interface->endpoint |-> ?endpoint
		&*& usb_host_endpoint(endpoint)
	:
		true
	;
@*/

// _probe gets a fraction of probe_disconnect_userdate,
// _disconnect must give the same fraction back. But how does
// _disconnect know what fraction size it must give back?
// That's what probe_disconnect_fraction_size is for.
//@ predicate usb_interface_private(struct usb_interface *usb_interface, struct usb_device *usb_device, void *data, bool has_data, real probe_disconnect_fraction_size);
/*@ predicate usb_interface(
		vf_usb_operation_probe_t *probe_cb,
		vf_usb_operation_disconnect_t *disconnect_cb,
		struct usb_interface *usb_interface, struct usb_device *usb_device, void *data, bool has_data, real probe_disconnect_fraction_size
	) =
	// Fraction of specified size to disallow stealing fractions and writing.
	[1/2] usb_interface->cur_altsetting |-> ?cur_altsetting
	&*& usb_host_interface(cur_altsetting)
	
	&*& usb_device(usb_device, ?ep0)
	&*& usb_interface_private(usb_interface, usb_device, data, has_data, probe_disconnect_fraction_size)
	
	&*& has_data ?
		// Note that you cannot close an usb_interface with new data yourself instead of calling set_intfdata,
		// because then you would have to be able to close usb_interface_private.
		userdef_usb_interface_data(probe_cb, disconnect_cb)(usb_interface,usb_device, data, probe_disconnect_fraction_size)
	:
		true
	;
@*/

/* Te be filled in by kernel module developer.
   probe_disconnect_fraction_size: see predicate usb_interface.
*/
/*@ predicate_family userdef_usb_interface_data
	(
		vf_usb_operation_probe_t *probe_cb,
		vf_usb_operation_disconnect_t *disconnect_cb
	)
	(
	struct usb_interface *intf, struct usb_device *usb_device, void *data, real probe_disconnect_fraction_size
	);
@*/


/* First read vf_usb_operation_probe_t to understand that the data pointer
 * might be nonzero because of another kernel module.
 * For setting data here, null is interpreted as "no data". This restricts usage of
 * these specifications (having data with data==null is not supported here).
 * An alternative would be to have ghost parameters.
 * Note that it is not true that having a state (which is not the same as setting a state)
 * where data != 0 implies having data, see vf_usb_operation_probe_t.
 * You might want to set "data != 0" in userdef_usb_interface_data to help preving correctness
 * of your kernel module.
 */
static inline void usb_set_intfdata(struct usb_interface *intf, void *data);
/*@ requires
	not_in_interrupt_context(currentThread) // indirect GFP_KERNEL kmalloc.
	// The implementation does not do any synchronisation, so we require a full fraction of usb_interface.
	&*& usb_interface(?probe_cb, ?disconnect_cb, intf, ?dev, ?originalData, ?originalHasData, ?fracsize)
	&*& data != 0 ?
		userdef_usb_interface_data(probe_cb, disconnect_cb)(intf, dev, data, fracsize)
	:
		true
	;
@*/	
/*@ ensures
	not_in_interrupt_context(currentThread)
	&*& usb_interface(probe_cb, disconnect_cb, intf, dev, data, data != 0, fracsize)
	&*& ( originalHasData ?
		userdef_usb_interface_data(probe_cb, disconnect_cb)(intf, dev, originalData, fracsize)
	:
		true
	);
		
@*/


static inline void *usb_get_intfdata(struct usb_interface *intf);
/*@ requires usb_interface(?open_cb, ?close_cb, intf, ?dev, ?data, ?hasData, ?fracsize);
@*/
/*@ ensures usb_interface(open_cb, close_cb, intf, dev, data, hasData, fracsize) &*& result == data;
@*/


struct usb_device *interface_to_usbdev(struct usb_interface *intf);
	//@ requires [?frac_intf] usb_interface(?open_cb, ?close_cb, intf, ?usb_device, ?data, ?hasData, ?fracsize);
	/*@ ensures [frac_intf] usb_interface(open_cb, close_cb, intf, result, data, hasData, fracsize)
		&*& result != 0
		&*& result == usb_device
		;
	@*/

// usb_host_endpoint is a struct in usb.h that contains the usb_endpoint_descriptor struct.
// So this predicate just follows the same structure (it's not just to tie together other predicates).
/*@ predicate usb_host_endpoint(struct usb_host_endpoint *usb_host_endpoint) =
	usb_endpoint_descriptor(&usb_host_endpoint->desc, ?dir, ?xfer_type, ?pipe) &*&
	usb_endpoint_descriptor_data(&usb_host_endpoint->desc, _)
	;
@*/

/* Creates a pipe, thus returns a pipe (thus not a bool obviously) */
int usb_rcvintpipe (struct usb_device *dev, __u8 endpoint);
	//@ requires [?f]usb_device(dev, ?ep0) &*& [?f2]usb_endpoint_descriptor(?desc, USB_DIR_IN, USB_ENDPOINT_XFER_INT, ?pipe) &*& [?f3]usb_endpoint_descriptor_data(desc, endpoint);
	/*@ ensures
		[f]usb_device(dev, ep0)
		&*& [f2]usb_endpoint_descriptor(desc, USB_DIR_IN, USB_ENDPOINT_XFER_INT, pipe)
		&*& [f3]usb_endpoint_descriptor_data(desc, endpoint)
		&*& result == pipe
		;
	@*/

int usb_sndctrlpipe (struct usb_device *dev, __u8 endpoint);
	//@ requires [?f]usb_device(dev, ?ep0) &*& [?f2]usb_endpoint_descriptor(?desc, USB_DIR_OUT, USB_ENDPOINT_XFER_CONTROL, ?pipe) &*& [?f3]usb_endpoint_descriptor_data(desc, endpoint);
	/*@ ensures
		[f]usb_device(dev, ep0)
		&*& [f2]usb_endpoint_descriptor(desc, USB_DIR_OUT, USB_ENDPOINT_XFER_CONTROL, pipe)
		&*& [f3]usb_endpoint_descriptor_data(desc, endpoint)
		&*& result == pipe
		;
	@*/

static inline __u16 usb_maxpacket(struct usb_device *udev, int pipe, int is_out);
	/*@ requires [?f]usb_device(udev, ?ep0) &*& [?f2]usb_endpoint_descriptor(?desc, ?dir, ?xfer_type, ?pipeOption)
		&*& pipeOption == pipe

		// Linux's USB implementation does this check at runtime. We enforce it here.
		&*& is_out != 0 ?
			dir == USB_DIR_OUT
		:
			dir == USB_DIR_IN
		;
	@*/
	/*@ ensures
		[f]usb_device(udev, ep0) &*& [f2]usb_endpoint_descriptor(desc, dir, xfer_type, pipe);
	@*/

/* Is this an OUT pipe (instead of an IN pipe)? */
int usb_pipeout(int pipe);
	//@ requires [?f2]usb_endpoint_descriptor(?desc, ?dir, ?xfer_type, ?pipeOption);
	/*@ ensures
		[f2]usb_endpoint_descriptor(desc, dir, xfer_type, pipeOption)
		&*& result != 0 ? // True, it is an OUT pipe.
			dir == USB_DIR_OUT
		: // No, it is an IN pipe.
			dir == USB_DIR_IN
		;
	@*/


/*---------------------------------------------------------*
 * Structs and enums                                       *
 *---------------------------------------------------------*/



struct usb_driver {
	const char *name;

	// original: int (*probe) (struct usb_interface *intf, const struct usb_device_id *id);
	vf_usb_operation_probe_t *probe;

	// original: void (*disconnect) (struct usb_interface *intf);
	vf_usb_operation_disconnect_t *disconnect;
	
	//int (*unlocked_ioctl) (struct usb_interface *intf, unsigned int code, void *buf);

	//int (*suspend) (struct usb_interface *intf, pm_message_t message);
	//int (*resume) (struct usb_interface *intf);
	//int (*reset_resume)(struct usb_interface *intf);

	//int (*pre_reset)(struct usb_interface *intf);
	//int (*post_reset)(struct usb_interface *intf);

	const struct usb_device_id *id_table;

	//struct usb_dynids dynids;
	//struct usbdrv_wrap drvwrap;
	//unsigned int no_dynamic_id:1;
	//unsigned int supports_autosuspend:1;
	//unsigned int soft_unbind:1;
};


struct urb{
	//struct list_head urb_list;	/* list head for use by the urb's
	//				 * current owner */
	//struct list_head anchor_list;	/* the URB may be anchored */
	//struct usb_anchor *anchor;
	struct usb_device *dev;		/* (in) pointer to associated device */
	//struct usb_host_endpoint *ep;	/* (internal) pointer to endpoint */
	//unsigned int pipe;		/* (in) pipe information */
	//unsigned int stream_id;		/* (in) stream ID */
	int status;			/* (return) non-ISO status */
	
	// UNSAFE We do bit operations here (bitwise or, ...), but the data type is
	//     different (unsigned). If an if-then-else follows after an
	//     bit operation, verifast will look at it differently than GCC.
	
	/*unsigned*/ int transfer_flags;	/* (in) URB_SHORT_NOT_OK | ...*/
	//void *transfer_buffer;		/* (in) associated data buffer */
	dma_addr_t transfer_dma;	/* (in) dma addr for transfer_buffer */
	//struct scatterlist *sg;		/* (in) scatter gather buffer list */
	//int num_sgs;			/* (in) number of entries in the sg list */
	//u32 transfer_buffer_length;	/* (in) data buffer length */
	//u32 actual_length;		/* (return) actual transfer length */
	unsigned char *setup_packet;	/* (in) setup packet (control only) */
	//dma_addr_t setup_dma;		/* (in) dma addr for setup_packet */
	//int start_frame;		/* (modify) start frame (ISO) */
	//int number_of_packets;		/* (in) number of ISO packets */
	//int interval;			/* (modify) transfer interval
	//				 * (INT/ISO) */
	//int error_count;		/* (return) number of ISO errors */
	void *context;			/* (in) context for completion */
	//usb_complete_t complete;	/* (in) completion routine */
	//struct usb_iso_packet_descriptor iso_frame_desc[0];
	//				/* (in) ISO ONLY */
};


struct usb_host_interface{

// VeriFast crashes on this line:
	struct usb_interface_descriptor	desc;

//	/* array of desc.bNumEndpoint endpoints associated with this
//	 * interface setting.  these will be in no particular order.
//	 */
	struct usb_host_endpoint *endpoint;
//
//	char *string;		/* iInterface string, if present */
//	unsigned char *extra;   /* Extra descriptors */
//	int extralen;
	struct device dev;
};


struct usb_interface {
	/* array of alternate settings for this interface,
	 * stored in no particular order */
//	struct usb_host_interface *altsetting;

	struct usb_host_interface *cur_altsetting;	/* the currently
					 * active alternate setting */
//	unsigned num_altsetting;	/* number of alternate settings */
//
//	/* If there is an interface association descriptor then it will list
//	 * the associated interfaces */
//	struct usb_interface_assoc_descriptor *intf_assoc;
//
//	int minor;			/* minor number this interface is
//					 * bound to */
//	enum usb_interface_condition condition;		/* state of binding */
//	unsigned sysfs_files_created:1;	/* the sysfs attributes exist */
//	unsigned ep_devs_created:1;	/* endpoint "devices" exist */
//	unsigned unregistering:1;	/* unregistration is in progress */
//	unsigned needs_remote_wakeup:1;	/* driver requires remote wakeup */
//	unsigned needs_altsetting0:1;	/* switch to altsetting 0 is pending */
//	unsigned needs_binding:1;	/* needs delayed unbind/rebind */
//	unsigned reset_running:1;
//	unsigned resetting_device:1;	/* true: bandwidth alloc after reset */
//
//	struct device dev;		/* interface specific device info */
//	struct device *usb_dev;
//	atomic_t pm_usage_cnt;		/* usage counter for autosuspend */
//	struct work_struct reset_ws;	/* for resets in atomic context */
	struct device dev;
};


static inline int usb_make_path(struct usb_device *dev, char *buf, size_t size);
  //@ requires chars(buf, ?bufsize, ?old_text) &*& size <= bufsize &*& usb_device_private(dev);
  //@ ensures chars(buf, bufsize, ?new_text) &*& usb_device_private(dev) &*& ! mem('\0', old_text) || mem('\0', new_text);


#endif

