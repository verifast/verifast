/**********************************************************************************
 * usbkbd_verified.c                                                              *
 * -----------------                                                              *
 *                                                                                *
 * Linux' USB Boot Protocol Keyboard Driver, with verification-annotations.       *
 * http://people.cs.kuleuven.be/~willem.penninckx/usbkbd/                         *
 *                                                                                *
 * Please read ../readme.html                                                     *
 *                                                                                *
 * If vfide is slow, please use redux instead of Z3, e.g. launch with             *
 *   vfide -prover redux -I . usbkbd_verified.c                                   *
 *                                                                                *
 **********************************************************************************/
 
/*
 * This file, and the .h and .gh files with specifications written
 * for this file, are released under the GPL. The original header follows:
 */

/*
 *  Copyright (c) 1999-2001 Vojtech Pavlik
 *
 *  USB HIDBP Keyboard support
 */

/*
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 * Should you need to contact me, the author, you can do so either by
 * e-mail - mail your message to <vojtech@ucw.cz>, or by paper mail:
 * Vojtech Pavlik, Simunkova 1594, Prague 8, 182 00 Czech Republic
 */

#include <linux/kernel.h>
#include <linux/slab.h>
#include <linux/module.h>
#include <linux/init.h>
#include <linux/usb/input.h>
#include <linux/hid.h>
#include "vf_module_license_gpl.h"
#include "usbkbd_keycodes.h"

// Contains module_init and module_exit macro usage.
// This is unsupported by VeriFast, so there is a different
// version of this file for verification and compilation.
// (a better way to do this is the way Helloproc does it,
// but we already know that works so we didn't put time in it).
#include "initcode.h"

//@ #include "counting.gh"
//@ #include "ghost-fields.gh"
#include "ghost-facade.h"

//@ #include "arrays.gh"

/*
 * Version Information
 */
#define DRIVER_VERSION ""
#define DRIVER_AUTHOR "Vojtech Pavlik <vojtech@ucw.cz>"
#define DRIVER_DESC "USB HID Boot Protocol keyboard driver"
#define DRIVER_LICENSE "GPL"

//MODULE_AUTHOR(DRIVER_AUTHOR);
//MODULE_DESCRIPTION(DRIVER_DESC);
//MODULE_LICENSE(DRIVER_LICENSE);

/**
 * struct usb_kbd - state of each attached keyboard (usb interface)
 * @led_urb_submitted: indicates whether @led is in progress, i.e. it has been
 *	submitted and its completion handler has not returned yet (without
 *	resubmitting @led).
 * @leds_lock: spinlock that protects @newleds, and @led_urb_submitted.
 */
struct usb_kbd {
	struct input_dev *dev;
	struct usb_device *usbdev;
	unsigned char old[8];
	struct urb *irq
	/*, *led */ // <-- original
	;struct urb *led // <-- non-original
	;
	
	unsigned char newleds;
	char name[128];
	char phys[64];

	unsigned char *new;
	struct usb_ctrlrequest *cr;
	unsigned char *leds; // this is an URB buffer.
	
	spinlock_t leds_lock;
	bool led_urb_submitted;

	dma_addr_t new_dma;
	dma_addr_t leds_dma;
};

static unsigned char* usb_kbd_keycode;


/*@
// the usb_struct fields are shared between multiple other predicates,
// either because they are read (sometimes concurrently),
// or because a fraction is needed to prove later on that when getting
// "data back" that the data still has the same value.
// To prevent the hassle of who owns which fraction of which part of the usb_kbd_struct,
// we just share the whole struct
// (except old[8] because it is written in the completion handler)
//
// We choose better names ("dev" turns out to be a bit confusing (usb dev? input dev?). Same for "irq").
predicate usb_kbd_struct_shared(
	struct usb_kbd *kbd;
	struct input_dev *inputdev,
	struct usb_device *usbdev,
	unsigned char *old, // @deprecated
	struct urb *irq_urb,
	struct urb *led_urb,
	
	//unsigned char newleds, // Not shared.
	
	char *name, // @deprecated
	char *phys, // @deprecated

	unsigned char *new,
	struct usb_ctrlrequest *cr,
	unsigned char *leds,
	
	//spinlock_t leds_lock, // Not shared.
	//bool led_urb_submitted, // Not shared
	
	dma_addr_t new_dma,
	dma_addr_t leds_dma
) =
	kbd->dev |-> inputdev
	&*& kbd->usbdev |-> usbdev
	&*& kbd->irq |-> irq_urb
	&*& kbd->led |-> led_urb
	//&*& kbd->newleds |-> newleds // not shared, protected by spinlock.
	&*& kbd->new |-> new
	&*& kbd->cr |-> cr
	&*& kbd->leds |-> leds
	//&*& spinlock_t leds_lock; // not shared, owned by spinlock.
	//&*& bool led_urb_submitted; // not shared, protected by spinlock
	&*& kbd->new_dma |-> new_dma
	&*& kbd->leds_dma |-> leds_dma
	
	&*& irq_urb != 0
	&*& new != 0
	&*& kbd != 0
	
	// Fix deprecated output parameter (this is a precise predicate so we have to)
	&*& old == 0 
	&*& name == 0
	&*& phys == 0
	;
@*/

// embedded in complete_t_pred_fam.
// XXX complete data of _what_? (irq,led?) --> irq. Better naming please.
/*@ predicate complete_data_except_reportable(struct usb_kbd *kbd, real fracsize, void *new, int urb_data_size, struct input_dev *inputdev) =
	[1/5]usb_kbd_struct_shared(kbd, inputdev, ?usbdev, ?old, ?irq_urb,
		?led_urb, ?name, ?phys, new, ?cr, ?leds, ?new_dma, ?leds_dma)
	
	&*& [fracsize]probe_disconnect_userdata(usb_kbd_probe, usb_kbd_disconnect)()
	&*& urb_data_size == 8
	
	&*& uchars(kbd->old, 8, ?cs)
	
	// usb_kbd_irq needs the following because it does "kbd->old + 2", which overflows if it cannot prove that
	// kbd->old (as in: the address value) is not less than UINTPTR_MAX
	// Alternatively, usb_kbd_irq can write:
	//    unsigned char* kbd_old = kbd->old;
        //    //@ produce_limits(kbd_old); // produce_limits(kbd->old) doesn't work.
	&*& true == ((void *)0 <= kbd->old) &*& true == (((char*)kbd->old) + 8 <= (char *)UINTPTR_MAX);
	
	// reportable is taken from input's precondition, so is not here.
	// That's why there is both this predicate and complete_t_pred_fam. <-- XXX huh?
@*/

// flow: _open->usb_submit_urb, (usb)->usb_kbd_irq->usb_submit_urb, _close kills the urb and gets it back.
/*@ predicate_family_instance complete_t_pred_fam(usb_kbd_irq)(
	real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
) =
	complete_data_except_reportable(context, fracsize, buffer, buffer_alloc_size, ?inputdev)
	&*& [1/4]input_dev_reportable(inputdev, context)
	;
	
	
predicate_family_instance complete_t_pred_fam_out(usb_kbd_irq)(
	real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
)=
	complete_t_pred_fam(usb_kbd_irq)(fracsize,
		urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
	)
	&*& urb_struct(true,
		urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
	)
	;
@*/

/**
 * Representation of data that is protected by the spinlock called leds_lock.
 */
/*@
predicate_ctor leds_lock_data(struct usb_kbd *kbd)() =
	leds_lock_data_maybe_submitted(kbd, ?led_urb_submitted);
@*/

/*@
predicate leds_lock_data_maybe_submitted(struct usb_kbd *kbd; bool led_urb_submitted) =
	kbd->led_urb_submitted |-> led_urb_submitted
	&*& usb_kbd_newleds(kbd, ?newleds)
	&*& [1/5]usb_kbd_struct_shared(kbd, ?inputdev, ?usbdev, ?old, ?irq_urb,
		?led_urb, ?name, ?phys, ?new, ?cr, ?leds, ?new_dma, ?leds_dma)
	
	&*& [1/3]usbkbd_killcount(kbd, ?killcount)
	
	&*& [1/2]usbkbd_cb_out_count(kbd, ?cb_out_counter)
	
	&*& (led_urb_submitted ?
		killcount == cb_out_counter + 1
	:
		killcount == cb_out_counter
		&*& [1/3]usbkbd_killcount(kbd, killcount)
		&*& [1/2]usbkbd_cb_out_count(kbd, cb_out_counter)
	)
	&*& led_urb_submitted ?
		true
	:
		urb_struct(true, led_urb, usbdev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr)
		// to put in complete_t_pred_fam when submitting.
		// XXX seems we got problems if we fill in the arguments. Which shouldn't be the case.
		&*& [1/5]usb_kbd_struct_shared(kbd, ?_inputdev, ?_usbdev, ?_old, ?_irq_urb,
			?_led_urb, ?_name, ?_phys, ?_new, ?_cr, ?_leds, ?_new_dma, ?_leds_dma)
	;


// Representation of ownership of the spinlock leds_lock (not the data owned by that spinlock).
// This is actually just a workaround to cast the void pointer to a struct usb_kbd*.
predicate leds_lock(struct usb_kbd *kbd; unit u) =
	spinlock(&(kbd->leds_lock), leds_lock_data(kbd))
	&*& u == unit
;
@*/

// flow: ->input_register, (input)->_open->, (input)->_close->, (input)->_event->
/*@ predicate_family_instance userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(struct input_dev *inputdev, bool is_opened, void *kbd, real fracsize) =
	// We need to refer to these fields in order to prove that
	// these fields are the values of the urb-predicate (urb_struct and friends).
	[1/5]usb_kbd_struct_shared(kbd, inputdev, ?usbdev, ?old, ?irq_urb,
		?led_urb, ?name, ?phys, ?new, ?cr, ?leds, ?new_dma, ?leds_dma)
	
	&*& kmalloc_block(cr, sizeof(struct usb_ctrlrequest))
	&*& led_urb != 0
	&*& cr != 0
	&*& leds != 0
	
	&*& permission_to_submit_urb(_, false)
	
	
	// -- led urb -- //
		&*& times_urb_submitted(?killcount, fracsize,
			led_urb, usbdev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr
		)
		// +1 because we also have a fraction of the spinlock for ourself.
		// (so nb_spinlock_fractions = killcount+1).
		&*& counting<struct usb_kbd*, unit>(leds_lock, kbd, killcount+1, unit)
	
		&*& killcount >= 0 // to avoid openclose.

		//&*& [1/2]ghost_field(kmalloc_block_onearg, kmalloc_args(kbd, sizeof(struct usb_kbd)), killcount)
		&*& [1/3]usbkbd_killcount(kbd, killcount)

		// We also have a ticket ourself (so all but one tickets are in times_urb_submitted, and one is here):
		&*& ticket<struct usb_kbd*, unit>(leds_lock, kbd, ?ticket_frac)
		&*& [ticket_frac]leds_lock(kbd, unit)

	// end led urb
	
	&*& !is_opened ?
	
		
		// stuff to submit IRQ URB
		
			urb_struct(true, irq_urb, usbdev, new, new_dma, 8, true, usb_kbd_irq, kbd, 0)
			&*& new != 0
		
			// _open needs to build complete_t_pred_fam(usb_kbd_irq)(kbd, fracsize, ?new, 8)
			// in order to do so, we provide the following stuff to _open:
				&*& complete_data_except_reportable(kbd, fracsize, new, 8, inputdev)
				// reportable is taken from input's precondition, so is not here.
		
	:
	
		
	
		urb_submitted(fracsize, irq_urb, usbdev, new, new_dma, 8, true, usb_kbd_irq, kbd, 0)
		&*& new != 0
		&*& [1/4]input_dev_reportable(inputdev, kbd) // other [1/4] is in the URB.
	;
@*/

// Embedded in usb_interface if its data parameter != 0.
// flow usb_interface (NOT OF USERDEF_USB_...): ->register, (usb)->_probe->, (usb)->disconnect->
/*@ predicate_family_instance userdef_usb_interface_data(usb_kbd_probe, usb_kbd_disconnect)(struct usb_interface *intf, struct usb_device *usbdev, struct usb_kbd *kbd, real fracsize) =
	kbd != 0
	
	&*& [1/5]usb_kbd_struct_shared(kbd, ?inputdev, usbdev, ?old, ?irq_urb,
		?led_urb, ?name, ?phys, ?new, ?cr, ?leds, ?new_dma, ?leds_dma)

	&*& struct_usb_kbd_padding(kbd)
	//&*& kmalloc_block(kbd, sizeof(struct usb_kbd)) // abused as unique pred, so moved away from here.
	
	&*& input_dev_registered(inputdev, _, _, _, 0, _, _, usb_kbd_open, usb_kbd_close, usb_kbd_event, kbd, fracsize)
	&*& [1/2]input_dev_reportable(inputdev, kbd)
	
	&*& chars(kbd->name, 128, ?name_chars)
	&*& chars(kbd->phys, 64, ?phys_chars)
	;
@*/



// flow: init->probe, disconnect->exit
/*@ predicate_family_instance probe_disconnect_userdata(usb_kbd_probe, usb_kbd_disconnect)()
	=
	pointer(&usb_kbd_keycode, ?usb_kbd_keycode_ptr)
	&*& uchars(usb_kbd_keycode_ptr, 256, _)
	&*& kmalloc_block(usb_kbd_keycode_ptr, 256)
	&*& usb_kbd_keycode_ptr != 0 // just to prevent kfree to not consume kmalloc_block when cleaning up.
	;
@*/

//@ predicate_family_instance usb_probe_callback_link(usb_kbd_probe)(vf_usb_operation_disconnect_t *disconnect) = disconnect == usb_kbd_disconnect;
//@ predicate_family_instance usb_disconnect_callback_link(usb_kbd_disconnect)(vf_usb_operation_probe_t *probe) = probe == usb_kbd_probe;



static void usb_kbd_irq(struct urb *urb) //@ : usb_complete_t_no_pointer
/*@ requires
	urb_struct(true,
		urb, ?usb_dev, ?buffer, ?buffer_dma, ?buffer_alloc_size, ?user_alloc_dma, ?complete, ?context, ?setup
	)
	&*& buffer != 0 
	&*& permission_to_submit_urb(?urbs_submitted, true)
	&*& complete_t_pred_fam(usb_kbd_irq)(?fracsize,
		urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
	)
	&*& current_thread_in_cb(currentThread, false);
@*/
/*@ ensures
	current_thread_in_cb(currentThread, ?deferred_data_xfer)
	&*& permission_to_submit_urb(_, true)
	&*& deferred_data_xfer ?
		complete_t_pred_fam(usb_kbd_irq)(fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
	:
		complete_t_pred_fam_out(usb_kbd_irq)(fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
	;
	
@*/
{
	struct usb_kbd *kbd = urb->context;
	int i;
	
	switch (urb->status) {
	case 0:			/* success */
		break;
	case -ECONNRESET:	/* unlink */
		printk ("usb_kbd: irq: error status ECONNRESET\n");
	case -ENOENT:
		printk ("usb_kbd: irq: error status ENOENT\n");
	case -ESHUTDOWN:
		printk ("usb_kbd: irq: error status ESHUTDOWN\n");
		
		//@ open complete_t_pred_fam(usb_kbd_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		//@ close complete_t_pred_fam(usb_kbd_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		//@ close complete_t_pred_fam_out(usb_kbd_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		return;
	/* -EPIPE:  should clear the halt */
	default:		/* error */
		//@ open complete_t_pred_fam(usb_kbd_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		goto resubmit;
	}
	
	
	//@ open complete_t_pred_fam(usb_kbd_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
	//@ open complete_data_except_reportable(context, fracsize, buffer, buffer_alloc_size, ?inputdev);
	//@ open [fracsize]probe_disconnect_userdata(usb_kbd_probe, usb_kbd_disconnect)();
			
	
	//@ assert [1/5]usb_kbd_new(kbd, ?kbd_new);
	//@ assert kbd_new == buffer;
	
				
	//@ assert [fracsize]pointer(&usb_kbd_keycode, ?usb_kbd_keycode_ptr);
	//@ assert [fracsize]uchars(usb_kbd_keycode_ptr, 256, ?keycodes);
	for (i = 0; i < 8; i++)
		/*@ invariant
			[1/5]kbd->dev |-> ?kbd_dev	
			&*& [1/5]kbd->new |-> kbd_new
			&*& uchars(buffer, buffer_alloc_size, _)
			&*& [fracsize]pointer(&usb_kbd_keycode, usb_kbd_keycode_ptr)
			&*& [fracsize]uchars(usb_kbd_keycode_ptr, 256, keycodes)
			&*& i >= 0 // to allow array[i+224].
			&*& [1/4]input_dev_reportable(kbd_dev, kbd)
			;
		@*/
		input_report_key(kbd->dev, usb_kbd_keycode[i + 224], (kbd->new[0] >> i) & 1);
	
	for (i = 2; i < 8; i++)
		/*@ invariant
			[1/5]kbd->dev |-> ?kbd_dev	
			&*& [1/5]kbd->new |-> kbd_new
			&*& uchars(buffer, buffer_alloc_size, _)
			&*& [fracsize]pointer(&usb_kbd_keycode, usb_kbd_keycode_ptr)
			&*& [fracsize]uchars(usb_kbd_keycode_ptr, 256, keycodes)
			&*& i >= 0
			&*& [1/4]input_dev_reportable(kbd_dev, kbd)
			&*& uchars(kbd->old, 8, ?kbd_old_contents_in_loop)
			;
		@*/
	{
		//@ uchars_to_chars(buffer);
		//@ chars_limits(buffer);
		void *memscan_ret = memscan(kbd->new + 2, kbd->old[i], 6); // ISSUE 1455
		//@ chars_to_uchars(buffer);
		
		unsigned char kbd_old_i = kbd->old[i];
		//@ produce_limits(kbd_old_i);
		
		if (kbd->old[i] > 3 && memscan_ret == kbd->new + 8) {
			
			//@ assert kbd_old_i >= 0; // so we can read kbd->old[i], even though it's all signed chars.
			// ISSUE 1454
			if (usb_kbd_keycode[kbd->old[i]]   != 0)
				input_report_key(kbd->dev, usb_kbd_keycode[kbd->old[i]], 0);
			else{
				// ISSUE 1456
				printk ("unknown key released/pressed"); // not original code // XXX
				//dev_info(&urb->dev->dev,
				//		"Unknown key (scancode %#x) released.\n", kbd->old[i]);
			}
		}
		//@ uchars_to_chars(kbd->old);
		memscan_ret = memscan((void*)kbd->old + 2, kbd->new[i], 6);
		//@ chars_to_uchars(kbd->old);
		
		unsigned char kbd_new_i = kbd->new[i];
		//@ produce_limits(kbd_new_i);
		
		if (kbd->new[i] > 3 && memscan_ret == (void*)kbd->old + 8) {
			if (usb_kbd_keycode[kbd->new[i]]   != 0)
				input_report_key(kbd->dev, usb_kbd_keycode[kbd->new[i]], 1);
			else
				printk("unknown key released"); // not original code
				//dev_info(&urb->dev->dev,
				//		"Unknown key (scancode %#x) released.\n", kbd->new[i]);
		}
		
	}
	
	input_sync(kbd->dev);
	
	//@ close [fracsize]probe_disconnect_userdata(usb_kbd_probe, usb_kbd_disconnect)();
	
	//@ uchars_to_chars(kbd->old); // XXX why is this not automatically done? For the "close complete_..." it works automatically.
	//@ uchars_to_chars(kbd->new);
	memcpy(kbd->old, kbd->new, 8);
	//@ close complete_data_except_reportable(context, fracsize, buffer, buffer_alloc_size, ?inputdev2);
resubmit:
	
	//@ close urb_struct(true, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup); // Cannot remove.
	// Resend the URB to make sure this completion handler is called by next
	// time something happens and to keep bandwidth reserved.
	//@ close complete_t_pred_fam(usb_kbd_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
	//@ close usb_submit_urb_ghost_arg(true, fracsize);
	i = usb_submit_urb (urb, GFP_ATOMIC);
	if (i){
		//err_hid ("can't resubmit intr"); // replaced by printk to allow compiling on multiple kernel versions.
		printk("can't resubmit intr");
		//@ close complete_t_pred_fam_out(usb_kbd_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
	}
}

/* Used for data that might be and might not be allocated, and might be and might not be initialized. */
/*@ predicate usb_kbd_alloc_mem_result(int result, int stage, struct usb_device *dev, struct usb_kbd *usb_kbd) = 
	usb_kbd->dev |-> ?input_dev // XXX should we set to same value here?
	
	// Stage is in range.
	&*& true == ((stage >= 0 && stage <= 5) || (stage >=10 && stage <= 11))
	
	&*& (
		result == 0 ?
			stage >= 5
		:
			stage < 5
	)
	
	
	// Stages:
	// --- alloc_mem allocates:
	// 0 : nothing allocated
	// 1 : kbd->irq urb allocated
	// 2 : kbd->led urb allocated
	// 3 : kbd->new dma-mapped mem allocated
	// 4 : kbd->cr kmalloc sizeof struct usb_ctrlrequest
	// 5 : kbd->leds dma-mapped mem
	// --- probe does:
	// 10: kbd->irq initialized
	// 11: kbd->led initialized


	// --- IRQ URB --- //
	&*& usb_kbd->new |-> ?new
	&*& usb_kbd -> irq |-> ?irq
	&*& usb_kbd->new_dma |-> ?new_dma
	
	&*& urb_struct_maybe(?irq_field_initialized, irq, ?irq_field_dev, ?irq_field_data,
	                     ?irq_field_dma, ?irq_field_data_size, ?irq_field_has_dma, ?complete_fn, ?context, 0) // XXX state context==usb_kbd? why? why not?
	&*& (stage >= 1 ? // At least kbd->irq URB allocated
		irq != 0
		
		&*& (stage >= 3 ? // At least kbd->irq URB allocated, and kbd->new (irq URB's data) allocated.
			new != 0
			&*& (stage >= 10 ? // the irq URB has references to the data (and is initialized)
				irq_field_data == new
				&*& irq_field_dma == new_dma
				&*& irq_field_has_dma == true
				&*& irq_field_dev == dev
				&*& irq_field_data_size == 8
				
				&*& complete_fn == usb_kbd_irq
				
				// Do we need to have irq_field_initialized==true?
				// After usb_kbd_alloc_mem, initialized==false so there it
				// does not matter, before usb_kbd_free_mem it is true
				// that irq_field_initialized == true so there
				// it is correct (and accepted by VeriFast), and
				// usb_kbd_free_mem doesn't really need it. So
				// it works but we don't actually need it.
				&*& irq_field_initialized == true
					
				
			: // the data is allocated, but the URB has no references to it.
				// So the URB does not own the data, so we own it directly ourself:
				usb_alloc_coherent_block(new, dev, 8, new_dma)
				&*& uchars(new, 8, ?cs)
				&*& irq_field_data == 0
				&*& irq_field_has_dma == false
			)
		: // Only URB allocated, not data.
			new == 0
			
			// If data is not allocated, we also know for sure the urb has no references to it.
			&*& !irq_field_has_dma
			&*& irq_field_data == 0
			
		)
	: // IRQ URB not allocated.
		irq == 0
		&*& new == 0
		&*& result != 0
	)
	
	
	// ---- LED URB ---- //
	
	&*& usb_kbd->led |-> ?led
	&*& usb_kbd->leds |-> ?leds
	&*& usb_kbd->cr |-> ?cr
	&*& usb_kbd->leds_dma |-> ?leds_dma
	&*& urb_struct_maybe(?led_field_initialized, led, ?led_field_dev, ?led_field_data,
	                     ?led_field_dma, ?led_field_data_size, ?led_field_has_dma, ?led_complete_fn, ?led_context, ?led_setup_packet)
	
	&*& (stage >= 2 ? // LED URB allocated
		led != 0
		
		&*& (stage >= 4 ? // cr allocated
			cr != 0
			&*& kmalloc_block(cr, sizeof(struct usb_ctrlrequest))
			// XXX Works if we always consume chars. But it shouldn't work then!
			&*& (stage >= 11 ? // irq urb contains cr
				led_setup_packet == cr
			:
				led_setup_packet == 0
				&*& uchars((void*)cr, sizeof(struct usb_ctrlrequest), ?cr_chars)
			)

		:
			cr == 0
			&*& led_setup_packet == 0
		)
		
		&*& (stage >= 5 ? // leds buffer allocated
			leds != 0
			
			&*& (stage >= 11 ? // led urb initialized
			
				led_field_data == leds
				&*& led_field_dma == leds_dma
				&*& led_field_has_dma == true
				&*& led_field_dev == dev
				&*& led_field_data_size == 1
				&*& led_setup_packet == cr

			: // led urb not initialized
				// so it does not contain leds buffer, so we contain it here.
				usb_alloc_coherent_block(leds, dev, 1, leds_dma)
				&*& uchars(leds, 1, ?leds_cs)
				&*& led_field_data == 0
				&*& led_field_has_dma == false
				&*& led_setup_packet == 0
			)
			
		: // leds not allocated
			leds == 0
			&& !led_field_has_dma
			&& led_field_data == 0
		)
		
		
		
	:
		led == 0
		&*& leds == 0
		&*& cr == 0
	)
	;
@*/


/*
 * This allocates multiple things, but you can't see in the return value
 * what is allocated and what not. Since freeing nullpointers is OK this
 * implementation works, but what should the postcondition state that
 * is allocated? (some_predicate() || true) doesn't work, but we can
 * do something similar with a new predicate and wildcards ("_") <-- not a smiley.
 */
static int usb_kbd_alloc_mem(struct usb_device *dev, struct usb_kbd *kbd)
/*@ requires
	not_in_interrupt_context(currentThread)
	
	&*& kbd->dev |-> ?input_dev
	
	&*& kbd->irq |-> 0
	&*& kbd->new |-> 0
	&*& kbd->new_dma |-> ?new_dma
	
	&*& kbd->led |-> 0
	&*& kbd->leds |-> 0
	&*& kbd->leds_dma |-> ?leds_dma
	&*& kbd->cr |-> 0;
@*/
/*@ ensures usb_kbd_alloc_mem_result(result, ?stage, dev, kbd) &*& not_in_interrupt_context(currentThread)
	&*& stage < 10 // usb_kbd_alloc_mem does not initialize anything.
	;
@*/
{
	// --- Stage 0 --- //
	if (!(kbd->irq = usb_alloc_urb(0, GFP_KERNEL)))
	{ // extra "{"
		//@ close urb_struct_maybe(false, 0, 0, 0, 0, 0, false, 0, 0, 0); // Cannot remove.
		//@ close urb_struct_maybe(false, 0, 0, 0, 0, 0, false, 0, 0, 0);
		//@ close usb_kbd_alloc_mem_result(-1, 0, dev, kbd);
		return -1;
	}
	//@ assert urb_struct(false, ?kbd_irq, ?urb_dev, ?irq_data, ?irq_data_dma, ?irq_data_size, false, 0, 0, 0);
	//@ close urb_struct_maybe(false, kbd_irq, urb_dev, irq_data, irq_data_dma, irq_data_size, false, 0, 0, 0); // Cannot remove.
	
	// --- Stage 1 --- //
	if (!(kbd->led = usb_alloc_urb(0, GFP_KERNEL)))
	{ // extra "{"
		//@ close urb_struct_maybe(false, 0, 0, 0, 0, 0, false, 0, 0, 0);
		//@ close usb_kbd_alloc_mem_result(-1, 1, dev, kbd);
		return -1;
	}
	//@ assert urb_struct(false, ?kbd_led, ?led_dev, ?led_data, ?led_data_dma, ?led_data_size, false, 0, 0, 0);
	//@ close urb_struct_maybe(false, kbd_led, led_dev, led_data, led_data_dma, led_data_size, false, 0, 0, 0);

	// --- Stage 2 --- //
	
	/* "new" is the buffer where the data arrives that the completion callback can read. */
	//@ assert kbd->new_dma |-> ?new_dma2;
	if (!(kbd->new = usb_alloc_coherent(dev, 8, GFP_ATOMIC, &kbd->new_dma)))
	{ // extra "{"
		//@ close usb_kbd_alloc_mem_result(-1, 2, dev, kbd);
		return -1;
	}
	
	// --- Stage 3 --- //
	// original:
	if (!(kbd->cr = kmalloc(sizeof(struct usb_ctrlrequest), GFP_KERNEL)))
	{ // extra "{"
		//@ close usb_kbd_alloc_mem_result(-1, 3, dev, kbd);
		return -1;
	}

	// --- Stage 4 --- //
	if (!(kbd->leds = usb_alloc_coherent(dev, 1, GFP_ATOMIC, &kbd->leds_dma)))
	{ // extra "{"
		//@ close usb_kbd_alloc_mem_result(-1, 4, dev, kbd);
		return -1;
	}
	
	
	// --- Stage 5 --- //
	//@ close usb_kbd_alloc_mem_result(0, 5, dev, kbd);
	return 0;
}

static void usb_kbd_free_mem(struct usb_device *dev, struct usb_kbd *kbd)
/*@ requires
	usb_kbd_alloc_mem_result(?returncode, ?stage, dev, kbd)
	&*& not_in_interrupt_context(currentThread);
@*/
/*@ ensures
	not_in_interrupt_context(currentThread)
	
	&*& kbd->dev |-> ?input_dev
	
	&*& kbd->irq |-> _
	&*& kbd->new |-> _
	&*& kbd->new_dma |-> ?new_dma
	
	&*& kbd->led |-> _
	&*& kbd->leds |-> _
	&*& kbd->cr |-> _
	&*& kbd->leds_dma |-> _
	;
@*/
{
	//@ open usb_kbd_alloc_mem_result(returncode, stage, dev, kbd);
	//@ assert kbd->irq |-> ?irq;
	usb_free_urb(kbd->irq);
	usb_free_urb(kbd->led);
	usb_free_coherent(dev, 8, kbd->new, kbd->new_dma);
	//@ prove_sizeof_usb_ctrlrequest_eq_8();
	kfree(kbd->cr);
	usb_free_coherent(dev, 1, kbd->leds, kbd->leds_dma);
}


/* When calling destroy_ticket, the precondition "ticket(p, a, ?f) &*& [f]p(a, ?b2)"
 * might take the wrong ticket chunk, and then fail to consume the right-hand side
 * of the separating conjunction. To work around this, we could wrap the ticket
 * we don't want to be consumed in another predicate, like this:
 * predicate ticket_wrap<a, b>(predicate(a; b) p, a a, real frac) = ticket(p, a, frac);
 * but it is easyer to reason about what you want than about what you don't want,
 * and what you don't want might not exist, so we workaround it in a more ugly
 * but more convenient way.
 *
 * Code example if you like to experiment:
 *   //@ assert [?f_ticket_2]leds_lock(kbd, unit) &*& ticket(leds_lock, kbd, f_ticket_2); // <-- works
 *   //@ assert ticket(leds_lock, kbd, ?f_ticket_3) &*& [f_ticket_3]leds_lock(kbd, unit);  // <-- doesn't work.
 */
/*@
lemma void destroy_ticket_invert_args<a, b>(predicate(a; b) p, a a)
    requires counting(p, a, ?count, ?b1) &*& [?f]p(a, ?b2) &*& ticket(p, a, f) &*& 0 != count;
    ensures counting(p, a, count - 1, b1) &*& b2 == b1;
{
	destroy_ticket(p, a);
}
@*/

/*@
predicate_family_instance input_open_callback_link(usb_kbd_open)(input_close_t close_cb, input_event_t event_cb) = 
	close_cb == usb_kbd_close && event_cb == usb_kbd_event;
predicate_family_instance input_close_callback_link(usb_kbd_close)(input_open_t open_cb, input_event_t event_cb) =
	open_cb == usb_kbd_open && event_cb == usb_kbd_event;
predicate_family_instance input_event_callback_link(usb_kbd_event)(input_open_t open_cb, input_close_t close_cb) =
	open_cb == usb_kbd_open && close_cb == usb_kbd_close;
	
@*/


static int usb_kbd_event(struct input_dev *dev, unsigned int type,
			 unsigned int code, int value) //@ : input_event_t_no_pointer
	/*@ requires userdef_input_drvdata(?open_cb, ?close_cb, usb_kbd_event)(dev, true, ?data, ?fracsize)
		&*& input_event_callback_link(usb_kbd_event)(open_cb, close_cb)
		&*& [?f]dev->led |-> ?led
		&*& [f]uints(led, 1, _);
	@*/
	/*@ ensures  userdef_input_drvdata(open_cb, close_cb, usb_kbd_event)(dev, true, data, fracsize)
		&*& input_event_callback_link(usb_kbd_event)(open_cb, close_cb)
		&*& [f]dev->led |-> led
		&*& [f]uints(led, 1, _);
	@*/
{

	unsigned long flags;
	//@ open input_event_callback_link(usb_kbd_event)(open_cb, close_cb);
	//@ close input_event_callback_link(usb_kbd_event)(open_cb, close_cb);
	//@ open userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, true, data, fracsize);
	struct usb_kbd *kbd = input_get_drvdata(dev);

	if (type != EV_LED){
		//@ close userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, true, data, fracsize);
		return -1;
	}
	
	//@ open [?ticket_frac]leds_lock(kbd, unit);
	spin_lock_irqsave(&kbd->leds_lock, flags);
	//@ open leds_lock_data(kbd)();	

	// XXX multiple problems:
	// * potentially side-effecting expression while it is not side-effecting
	// * seems we can't parse "!!"
	// * "!" only works on bools
	// * implicit cast to (unsigned) char doesn't seem to work
	//@ assert [1]usb_kbd_newleds(kbd, _); // but we can write to it.
		
	//@ assert [f]input_dev_led(dev, ?input_dev_led);

	//@ uints_to_chars(dev->led);
	int tmp_left = test_bit(LED_KANA, dev->led);
	tmp_left = tmp_left == 0 ? 0 : 8;
	
	int tmp_right = test_bit(LED_COMPOSE, dev->led);
	tmp_right = tmp_right == 0 ? 0 : 8;
	
	tmp_left = tmp_left == 8 ? tmp_left : tmp_right;

	tmp_right = test_bit(LED_SCROLLL, dev->led);
	tmp_right = tmp_right == 0 ? 0 : 4;
	tmp_left = tmp_left + tmp_right;
	
	tmp_right = test_bit(LED_CAPSL, dev->led);
	tmp_right = tmp_right == 0 ? 0 : 2;
	tmp_left = tmp_left + tmp_right;
	
	tmp_right = test_bit(LED_NUML, dev->led);
	tmp_right = tmp_right == 0 ? 0 : 1;
	tmp_left = tmp_left + tmp_right;
	
	kbd->newleds = (unsigned char)tmp_left;
	
	// original code:
	/*kbd->newleds = (!!test_bit(LED_KANA,    dev->led) << 3) | (!!test_bit(LED_COMPOSE, dev->led) << 3) |
		       (!!test_bit(LED_SCROLLL, dev->led) << 2) | (!!test_bit(LED_CAPSL,   dev->led) << 1) |
		       (!!test_bit(LED_NUML,    dev->led));*/
	
	//@ chars_to_uints(dev->led, 1);
	
	if (kbd->led_urb_submitted){
		//@ close leds_lock_data_maybe_submitted(kbd, _); // Cannot remove.
		//@ close leds_lock_data(kbd)();
		spin_unlock_irqrestore(&kbd->leds_lock, flags);
		//@ close [ticket_frac]leds_lock(kbd, unit);
		//@ close userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, true, data, fracsize);
		return 0;
	}
	
	//@ open urb_struct(true, ?led_urb, ?usb_dev, ?leds, ?leds_dma, 1, true, usb_kbd_led, kbd, ?cr); // Cannot remove.
	//@ open uchars(leds, 1, _);
	if (*(kbd->leds) == kbd->newleds){
		//@ close uchars(leds, 1, _);
		//@ close leds_lock_data_maybe_submitted(kbd, _); // Cannot remove.
		//@ close leds_lock_data(kbd)();
		spin_unlock_irqrestore(&kbd->leds_lock, flags);
		//@ close [ticket_frac]leds_lock(kbd, unit);
		//@ close userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, true, data, fracsize);
		return 0;
	}
	
	
	*(kbd->leds) = kbd->newleds;
	

	kbd->led->dev = kbd->usbdev;
	
	//@ close urb_struct(true, led_urb, usb_dev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr); // Cannot remove.
	//@ close usb_submit_urb_ghost_arg(false, fracsize);

	//@ create_ticket<struct usb_kbd*, unit>(leds_lock, kbd);
	//@ assert ticket(leds_lock, kbd, ?f_ticket) &*& [f_ticket]leds_lock(kbd, _);
	//@ assert usbkbd_cb_out_count(kbd, ?cb_out_count);
	//@ assert usbkbd_killcount(kbd, ?killcount);
	//@ usbkbd_killcount_write(kbd, killcount, killcount+1);
	//@ assert ticket(leds_lock, kbd, f_ticket) &*& [f_ticket]leds_lock(kbd, _);

	//@ assert ticket(leds_lock, kbd, f_ticket) &*& [f_ticket]leds_lock(kbd, unit);
	
	//@ close complete_t_pred_fam(usb_kbd_led)(fracsize, kbd->led, usb_dev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr);	
	if (usb_submit_urb(kbd->led, GFP_ATOMIC)){
		//@ open complete_t_pred_fam(usb_kbd_led)(fracsize, kbd->led, usb_dev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr);
		//@ usbkbd_killcount_write(kbd, killcount+1, killcount); // restore.
		
		//@ destroy_ticket_invert_args<struct usb_kbd*, unit>(leds_lock, kbd);
		
		//err_hid("usb_submit_urb(leds) failed");
		printk("usb_submit_urb(leds) failed");
		
		//@ assert usbkbd_cb_out_count(kbd, cb_out_count);
		//@ assert [1/3]usbkbd_killcount(kbd, killcount);
		
	}else{
		kbd->led_urb_submitted = true;
		
		//@ assert times_urb_submitted(?times, fracsize, led_urb, usb_dev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr);
		//@ close times_urb_submitted(times+1, fracsize, led_urb, usb_dev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr);
		//@ assert [_]usbkbd_cb_out_count(kbd, cb_out_count);
	}
	
	//@ close leds_lock_data(kbd)();
	spin_unlock_irqrestore(&kbd->leds_lock, flags);
	
	//@ close userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, true, data, fracsize);
	return 0;
}

/*@
predicate_family_instance complete_t_pred_fam(usb_kbd_led)(
	real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
)=
	[?f]leds_lock(context, unit)
	&*& ticket<struct usb_kbd*, unit>(leds_lock, context, f)
	
	&*& [1/3]usbkbd_killcount(context, ?killcount)
	&*& [1/2]usbkbd_cb_out_count(context, ?cb_out_counter)
	&*& killcount == cb_out_counter+1
	
	&*& [1/5]usb_kbd_struct_shared(context, ?inputdev, usb_dev, ?old, ?irq_urb,
		urb, ?name, ?phys, ?new, setup, buffer, ?new_dma, buffer_dma)
	&*& buffer_alloc_size == 1
	&*& complete == usb_kbd_led
	&*& user_alloc_dma == true
;
	
	
predicate_family_instance complete_t_pred_fam_out(usb_kbd_led)(
	real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
)=
	// don't include complete_t_pred_fam, it uses [1/5]usb_kbbd_struct_shared which we don't want here.

	ticket<struct usb_kbd*, unit>(leds_lock, context, ?f)
	&*& [f]leds_lock(context, unit)
	&*& buffer_alloc_size == 1
	&*& complete == usb_kbd_led

	&*& usbkbd_cb_out_ticket(context)
	
	// Note that urb_struct predicate is in the spinlock.
;

@*/


static void usb_kbd_led(struct urb *urb)  //@ : usb_complete_t_no_pointer
/*@ requires
	urb_struct(true,
		urb, ?usb_dev, ?buffer, ?buffer_dma, ?buffer_alloc_size, ?user_alloc_dma, ?complete, ?context, ?setup
	)
	&*& buffer != 0 
	&*& permission_to_submit_urb(?urbs_submitted, true)
	&*& complete_t_pred_fam(usb_kbd_led)(?fracsize, 
		urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
	)
	&*& current_thread_in_cb(currentThread, false)
	;
@*/
/*@ ensures
	permission_to_submit_urb(_, true)
	&*& current_thread_in_cb(currentThread, ?deferred_data_xfer)
	&*& deferred_data_xfer ?
		complete_t_pred_fam(usb_kbd_led)(fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
	:
		complete_t_pred_fam_out(usb_kbd_led)(fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
	;
@*/
	
{
	unsigned long flags;
	
	struct usb_kbd *kbd = urb->context;

	if (urb->status)
		//dev_warn(&urb->dev->dev, "led urb status %d received\n",
		//	 urb->status);
		printk ("WARNING: error-status for led urb received\n"); // dev_warn and friends change API too often.

	//@ open complete_t_pred_fam(usb_kbd_led)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
	//@ assert /*we get [1/5]*/[1/5]usb_kbd_struct_shared(kbd, _, _, _, _, _, _, _, _,  _,  _,  _, _);

	//@ open leds_lock(kbd, _);
	spin_lock_irqsave(&kbd->leds_lock, flags);
	//@ open leds_lock_data(kbd)();
	//@ open leds_lock_data_maybe_submitted(kbd, _); // Cannot remove.
	//@ assert /*we get [1/5]*/[2/5]usb_kbd_struct_shared(kbd, _, _, _, _, _, _, _, _,  _,  _,  _, _);
	
	//@ assert kbd->led_urb_submitted |-> ?led_urb_submitted;
	
	// get values to debug later :)
	//@ assert [1/2]usbkbd_killcount(kbd, ?killcount);
	//@ assert usbkbd_cb_out_count(kbd, ?cb_out_counter);
	
	// We know because it is in complete_t_pred_fam, so we know !led_urb_submitted.
	//@ assert killcount == cb_out_counter + 1;

	//@ assert [_]kbd->leds |-> ?leds;
	//@ assert leds == buffer;
	
	//@ open uchars(leds, 1, _);
	if (*(kbd->leds) == kbd->newleds){
		kbd->led_urb_submitted = false;

		//@ close uchars(leds, 1, _);
		
		//@ usbkbd_cb_out_inc(kbd);
		
		//@ assert [1/2]usbkbd_killcount(kbd, killcount);
		//@ assert usbkbd_cb_out_count(kbd, cb_out_counter+1);
		//@ assert killcount == cb_out_counter + 1;
		
		//@ close urb_struct(true, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		//@ close leds_lock_data_maybe_submitted(kbd, _); // Cannot remove.
		//@ close leds_lock_data(kbd)(); // takes [2/5].
		
		spin_unlock_irqrestore(&kbd->leds_lock, flags);
		//@ close complete_t_pred_fam_out(usb_kbd_led)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		return;
	}	

	*(kbd->leds) = kbd->newleds;
	
	//@ close uchars(leds, 1, _);
	
	kbd->led->dev = kbd->usbdev;
	//@ close urb_struct(true, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup); // Cannot remove.
	//@ close usb_submit_urb_ghost_arg(true, fracsize);
	//@ bool led_submitted = false;
	if (usb_submit_urb(kbd->led, GFP_ATOMIC)){
		//err_hid("usb_submit_urb(leds) failed");
		printk ("usb_submit_urb(leds) failed");
		kbd->led_urb_submitted = false;
		//@ usbkbd_cb_out_inc(kbd);
		//@ close leds_lock_data_maybe_submitted(kbd, _); // Cannot remove.
		//@ close leds_lock_data(kbd)();
	}else{
		//@ led_submitted = true;
		//@ close leds_lock_data_maybe_submitted(kbd, _); // Cannot remove.
		//@ close leds_lock_data(kbd)();
	
	}
	
	spin_unlock_irqrestore(&kbd->leds_lock, flags);
	
	/*@
	if( ! led_submitted){
		close complete_t_pred_fam_out(usb_kbd_led)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
	}else{
		close complete_t_pred_fam(usb_kbd_led)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
	}
	@*/
	
	
	
}

static int usb_kbd_open(struct input_dev *dev) //@ : input_open_t_no_pointer
	/*@ requires userdef_input_drvdata(usb_kbd_open, ?close_cb, ?event_cb)(dev, false, ?context, ?fracsize)
		&*& input_open_callback_link(usb_kbd_open)(close_cb, event_cb)
		&*& [1/2]input_dev_reportable(dev, context)
		&*& not_in_interrupt_context(currentThread);
	@*/
	/*@ ensures
		not_in_interrupt_context(currentThread)
		&*& input_open_callback_link(usb_kbd_open)(close_cb, event_cb)
		&*& result == 0 ? // success
			userdef_input_drvdata(usb_kbd_open, close_cb, event_cb)(dev, true, context, fracsize)
		: // failure
			userdef_input_drvdata(usb_kbd_open, close_cb, event_cb)(dev, false, context, fracsize)
			&*& [1/2]input_dev_reportable(dev, context)
		;
	@*/
{
	//@ open input_open_callback_link(usb_kbd_open)(close_cb, event_cb);
	//@ close input_open_callback_link(usb_kbd_open)(close_cb, event_cb);
	//@ open userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, false, context, fracsize);
	
	struct usb_kbd *kbd = input_get_drvdata(dev);

	//@ assert [1/5]usb_kbd_struct_shared(?_kbd, ?_dev, ?usbdev, ?old, ?irq_urb, ?led_urb, ?name, ?phys, ?new, ?cr, ?leds, ?new_dma, ?leds_dma);
	
	//@ open urb_struct(true, irq_urb, ?usb_dev, ?buffer, ?buffer_dma, ?buffer_alloc_size, ?user_alloc_dma, ?complete, context, ?setup); // Cannot remove.
	// XXX get the permissions to do this. <s>We actually don't need it because it's already
	// done in _probe<s> update: probe doesn't do it, it did because _open was moved to probe... Ouch.
	// XXX why does it verify when this field is never set?
	kbd->irq->dev = kbd->usbdev;
	//@ close urb_struct(true, irq_urb, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup); // Cannot remove.
	
	
	//@ assert buffer_alloc_size == 8;
	//@ assert complete_data_except_reportable(context, fracsize, new, ?__buffer_alloc_size, ?__dev);
	
	//@ close complete_t_pred_fam(usb_kbd_irq)(fracsize, irq_urb, usb_dev, new, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
	//@ close usb_submit_urb_ghost_arg(false, fracsize);
	if (usb_submit_urb(kbd->irq, GFP_KERNEL)){
		//@ close [1/5]usb_kbd_struct_shared(kbd, _, _, _, _, _, _, _, _, _, _, _, _);  // XXX why is complete_data_except_reportable not consumable if this is auto-closed?
	
		//@ assert usb_kbd_close == close_cb;
		//@ open complete_t_pred_fam(usb_kbd_irq)(fracsize, irq_urb, usb_dev, new, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		
		// openclose to get the fraction of usb_kbd_struct_shared in order
		// to prove that dev == inputdev(last arg of complete_data_except_reportable).
		//@ open complete_data_except_reportable(context, fracsize, new, 8, ?inputdev);
		//@ close complete_data_except_reportable(context, fracsize, new, 8, inputdev);
		
		//@ close userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, false, context, fracsize);
		//@ assert inputdev == dev;
		//@ assert [1/4]input_dev_reportable(dev, context) &*& [1/4]input_dev_reportable(dev, context);
		// Even though we know the above assert and input_dev_reportable is precise,
		// we still don't obtain [1/2] of it...
		//@ assert true == ((real)1/2==(real)((real)1/4+(real)1/4)); // OK.
		// workaround: XXX
		/*@ {
			lemma void foo()
				requires [1/4]input_dev_reportable(dev, context) &*& [1/4]input_dev_reportable(dev, context);
				ensures [1/2]input_dev_reportable(dev, context);
			{
			}
			foo();
		}
		// problem is probably that dev == inputdev is proven after complete_data_except_reportable(inputdev, data) is obtained.
		@*/
		
		return -EIO;
	}

	//@ close userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, true, context, fracsize);
	return 0;
}

/*@
lemma void get_rid_of_countdiff()
	requires times_diffcount_ticket(?kbd, ?times) &*& usbkbd_cb_out_count(kbd, times) &*& times >= 0;
	ensures usbkbd_cb_out_count(kbd, 0);
{

	while (times > 0)
		invariant
			times_diffcount_ticket(kbd, times) &*& usbkbd_cb_out_count(kbd, times)
			&*& times > 0 || times == 0
		;
		decreases
			times
		;
		
	{
		open times_diffcount_ticket(kbd, times);
		// Somewhere the encapsulation broke. XXX
		open countdiff_tickets(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd), times);
		close usbkbd_cb_out_ticket(kbd);
		usbkbd_cb_out_dec(kbd);
		close times_diffcount_ticket(kbd, times-1);
		
		//auto-variant-detection of recursion didn't work. So we use loop.
		//get_rid_of_countdiff();
		
		times--;
	}

	open times_diffcount_ticket(kbd, 0);
	
}

lemma void get_rid_of_counting()
	requires
		times_complete_t_pred_fam_out(?times, ?fracsize, 
			?led_urb, ?usbdev, ?leds, ?leds_dma, 1, true, usb_kbd_led, ?kbd, ?cr
		)
		&*& counting(leds_lock, kbd, times, unit)
		
	;
	ensures
		leds_lock(kbd, unit)
		&*& times_diffcount_ticket(kbd, times)
	;
{
	int cur_times = times;

	// openclose to prove times >= 0.
	open times_complete_t_pred_fam_out(times, fracsize, led_urb, usbdev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr);
	close times_complete_t_pred_fam_out(times, fracsize, led_urb, usbdev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr);

	close countdiff_tickets(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd), times - cur_times); // times - cur_times == 0

	while (cur_times > 0)
		invariant 
			times_complete_t_pred_fam_out(cur_times, fracsize, 
				led_urb, usbdev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr
			)
			&*& countdiff_tickets(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd), times - cur_times)
			&*& cur_times >= 0
			&*& cur_times <= times
			&*& counting(leds_lock, kbd, cur_times, unit)
		;
		decreases cur_times;
	{
		open times_complete_t_pred_fam_out(cur_times, fracsize, led_urb, usbdev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr);	
		open complete_t_pred_fam_out(usb_kbd_led)(fracsize, led_urb, usbdev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr);
		destroy_ticket(leds_lock, kbd);
		

		cur_times--;
		
		open usbkbd_cb_out_ticket(kbd);
		close countdiff_tickets(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd), times - cur_times);
		
	}
	
	open times_complete_t_pred_fam_out(0, fracsize, led_urb, usbdev, leds, leds_dma, 1, true, usb_kbd_led, kbd, cr);
	stop_counting(leds_lock, kbd);
	close times_diffcount_ticket(kbd, times);
	
}


lemma void min_prove(int killcount, int cb_out_count)
	requires 
		( killcount == cb_out_count
			||
		  killcount == cb_out_count + 1
		)
		&*& cb_out_count >= killcount
		;
	ensures
		cb_out_count == killcount
		;
{
}

lemma void diffcount_tickets_minimum_prove()
	requires
		times_diffcount_ticket(?kbd, ?killcount)
		
		
		&*& [?f]usbkbd_cb_out_count(kbd, ?cb_out_count)
		
		&*& (
				killcount == cb_out_count
			||
				killcount == cb_out_count + 1
		)

		&*& killcount >= 0
	;
	ensures
	
		// to prove:
		// after taking killcount tickets from times_diffcount_tickets,
		// we know that cb_out_count >= killcount.
	
		[f]usbkbd_cb_out_count(kbd, killcount) // XXX what value to put here?
		&*& times_diffcount_ticket(kbd, killcount)
		&*& cb_out_count >= killcount
		
	;
{
	
	
	if (killcount != 0){
		// XXX hm where is our encapsulation?
		open times_diffcount_ticket(kbd, killcount);
	
		minimum_prove_countdiff(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd), killcount);
		close times_diffcount_ticket(kbd, killcount);
		
	}else{
		// just prove cb_out_count >= 0.
		// (then also cb_out_count >= killcount).
		close countdiff_tickets(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd), 0);
		
		// inc-dec would prove killcount>=0, but we can only do so if we have a full fraction.
		// So call a help function that doesn't require a full fraction.
		//usbkbd_cb_out_inc(kbd);
		//usbkbd_cb_out_dec(kbd);
		minimum_prove_countdiff(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd), killcount);
		
		open countdiff_tickets(_, _, 0);
		
	}
}
@*/


static void usb_kbd_close(struct input_dev *dev) //@ : input_close_t_no_pointer
	/*@ requires userdef_input_drvdata(?open_cb, usb_kbd_close, ?event_cb)(dev, true, ?data, ?fracsize)
		&*& input_close_callback_link(usb_kbd_close)(open_cb, event_cb)
		&*& not_in_interrupt_context(currentThread);
	@*/
	/*@ ensures  userdef_input_drvdata(open_cb, usb_kbd_close, event_cb)(dev, false, data, fracsize)
		&*& input_close_callback_link(usb_kbd_close)(open_cb, event_cb)
		&*& [1/2]input_dev_reportable(dev, data) &*& not_in_interrupt_context(currentThread);
	@*/
{
	//@ open input_close_callback_link(usb_kbd_close)(open_cb, event_cb);
	//@ close input_close_callback_link(usb_kbd_close)(open_cb, event_cb);
	//@ open userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, true, data, fracsize);
	
	struct usb_kbd *kbd = input_get_drvdata(dev);

	//@ assert [_]kbd->irq |-> ?kbd_irq;
	//@ assert urb_submitted(fracsize, kbd_irq, ?usb_dev, ?buffer, ?buffer_dma, ?buffer_alloc_size, ?user_alloc_dma, ?complete, ?context, ?setup);
	//@ close times_urb_submitted(0, fracsize, kbd_irq, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	//@ close times_urb_submitted(1, fracsize, kbd_irq, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	
	usb_kill_urb(kbd->irq);
	//@ close [1/5]usb_kbd_struct_shared(kbd, dev, _, _, _, _, _, _, _, _, _, _, _); // XXX why is complete_data_except_reportable not consumable if this is auto-closed?
	//@ open times_complete_t_pred_fam_out(1, fracsize, kbd_irq, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	//@ open complete_t_pred_fam_out(usb_kbd_irq)(fracsize, kbd_irq, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	//@ open complete_t_pred_fam(usb_kbd_irq)(fracsize, kbd_irq, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	
	// openclose to prove inputdev == dev.
	//@ open complete_data_except_reportable(data, fracsize, ?new, 8, ?inputdev);
	//@ close complete_data_except_reportable(data, fracsize, new, 8, inputdev);
	//@ assert inputdev == dev;
	
	//@ close [1/5]usb_kbd_struct_shared(kbd, dev, _, _, _, _, _, _, _, _, _, _, _); // Cannot remove, need to prove dev==inputdev.
	//@ assert [_]usb_kbd_struct_shared(kbd, dev, ?usbdev, ?old, ?irq_urb, ?led_urb, ?name, ?phys, new, ?cr, ?leds, ?new_dma, ?leds_dma);
	
	//@ close userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(dev, false, data, fracsize);
	
	//@ open times_complete_t_pred_fam_out(0, _, _, _, _,_, _, _, _, _, _);
	
	/*@ {
		lemma void foo()
			requires [1/4]input_dev_reportable(dev, data) &*& [1/4]input_dev_reportable(dev, data);
			ensures [1/2]input_dev_reportable(dev, data);
		{
		}
		foo();
	}
	@*/
	
	
}


/* because you can have multiple usb_endpoint_descriptor predicates, and VeriFast only looks at
 * the first one when pattern-matching, it might take the wrong one and halt verification
 * instead of retrying with the second one. To workaround this, we wrap the predicate in this
 * _hide predicate such that VeriFast will take the correct one.
 */
/*@
predicate usb_endpoint_descriptor_hide(struct usb_endpoint_descriptor *epd; int direction, int xfer_type, int pipe) =
	usb_endpoint_descriptor(epd, direction, xfer_type, pipe);


lemma void forall_equals_all_eq_char_of_uchar(list<unsigned char> ucs) 
    requires forall(ucs, (equals)(unit, 0)) == true; 
    ensures all_eq(map(char_of_uchar, ucs), 0) == true; 
{ 
    switch (ucs) { 
        case nil: 
        case cons(uc, ucs0): 
            forall_equals_all_eq_char_of_uchar(ucs0); 
    } 
}

@*/


static int usb_kbd_probe(struct usb_interface *iface,
			 const struct usb_device_id *id) //@ : vf_usb_operation_probe_t
/*@ requires
	usb_interface(usb_kbd_probe, ?disconnect, iface, _, ?originalData, false, ?fracsize)
	&*& permission_to_submit_urb(?urbs_submitted, false)
	&*& not_in_interrupt_context(currentThread)
	&*& [fracsize]probe_disconnect_userdata(usb_kbd_probe, disconnect)()
	&*& [?callback_link_f]usb_probe_callback_link(usb_kbd_probe)(disconnect);
@*/
/*@ ensures
	not_in_interrupt_context(currentThread)
	&*& [callback_link_f]usb_probe_callback_link(usb_kbd_probe)(disconnect)
	&*& result == 0 ? // success
		usb_interface(usb_kbd_probe, disconnect, iface, _, ?data, true, fracsize)
		&*& data != 0
	: // failure
		usb_interface(usb_kbd_probe, disconnect, iface, _, ?data, false, fracsize)
		&*& permission_to_submit_urb(_, false)
		&*& data == 0 || data == originalData
		&*& [fracsize]probe_disconnect_userdata(usb_kbd_probe, disconnect)()
	;
@*/
{

	//@ open [callback_link_f]usb_probe_callback_link(usb_kbd_probe)(disconnect);
	//@ close [callback_link_f]usb_probe_callback_link(usb_kbd_probe)(disconnect);

	struct usb_device *dev = interface_to_usbdev(iface);
	struct usb_host_interface *interface;
	struct usb_endpoint_descriptor *endpoint;
	struct usb_kbd *kbd;
	struct input_dev *input_dev;
	struct usb_host_endpoint* ep;
	int i, pipe, maxp;
	int error = -ENOMEM;
	
	/*
	 * An interface can have one or more altsettings. It is possible to switch between altsettings
	 * without restarting the USB device. (see e.g. http://www.beyondlogic.org/usbnutshell/usb5.shtml)
	 *
	 * Note:  It is uncertain whether the desired altsetting is set before
	 *        probe is entered. usbkbd seems to assume this.
	 *        usb.h states the probe function may call usb_set_interface
	 *        to set the altsetting, but does not specify whether probe
	 *        must set the altsetting back to 0 in case of -ENODEV
	 *        or whether the caller of probe does this.
	 *        It is thus unclear so far whether this assumption is correct.
         *        Even if the altsetting is actually wrong (so not the boot protocol),
         *        the driver still does the necessary checks, e.g. whether
         *        the endpoints exists, so it normally still shouldn't crash
         *        (but it might be functionally incorrect), so this should
         *        not be an unsafety in terms of crashfreeness.
	 *
	 * Note: The usbkbd driver seems to assume the USB specs state the
	 *       boot protocol must have 1 endpoint (excluding control endpoint 0).
	 *       (if not, some boot protocol keyboard just won't be supported)
	 */
	//@ open usb_interface(usb_kbd_probe, disconnect, iface, dev, originalData, false, fracsize);
	interface = iface->cur_altsetting;
	
	//@ open [?f2]usb_host_interface(interface);
	//@ open [?f3]usb_interface_descriptor(&interface->desc, ?bNumEndpoints, ?bInterfaceNumber);
	//@ struct usb_interface_descriptor* desc = &interface->desc;
	if (interface->desc.bNumEndpoints != 1){
		//@ close [f3]usb_interface_descriptor(desc, bNumEndpoints, bInterfaceNumber);
		//@ close [f2]usb_host_interface(interface);
		//@ close usb_interface(usb_kbd_probe, disconnect, iface, dev, originalData, false, fracsize);
		return -ENODEV;
	}
	
	//@ assert [_]interface->endpoint |-> ?host_endpoint;
	//@ open usb_host_endpoint(host_endpoint);

	/* The control endpoint 0 always exists: "All USB devices are required to
	 * implement a default control method that uses both the input and output
	 * endpoints with endpoint number zero" -- USB 2.0 specs page 34.
	 * Control endpoint 0 is implicit, i.e. endpoint 0 in code does not
	 * refer to the control endpoint 0.
	 * Indeed, usb.h states "each interface setting has zero or (usually) more endpoints",
	 * so if there are zero endpoints the control endpoint must be implicit.
	 */
	ep = interface->endpoint;
	endpoint = &ep->desc;
	//original: endpoint = &interface->endpoint[0].desc;
	
	if (!usb_endpoint_is_int_in(endpoint))
	{ // extra "{"
		//@ close usb_host_endpoint(host_endpoint);
		//@ close [f3]usb_interface_descriptor(desc, bNumEndpoints, _);
		//@ close [f2]usb_host_interface(interface);
		//@ close usb_interface(usb_kbd_probe, usb_kbd_disconnect, iface, dev, originalData, false, fracsize);
		return -ENODEV;
	}
	
	// We need both what is inside the predicate and the predicate itself.
	// So let's just get what we want.
	//@ open [1/2]usb_endpoint_descriptor_data(endpoint, ?bEndpointAddres);
	pipe = usb_rcvintpipe(dev, endpoint->bEndpointAddress);
	
	int usb_pipeout_ret = usb_pipeout(pipe);
	//@ assert usb_pipeout_ret == 0;  // in fact it is known that it's not a pipeout since we called usb_rcvintpipe (where "rcv" means "in", not "out")
	
	// original: maxp = usb_maxpacket(dev, pipe, usb_pipeout(pipe));
	__u16 maxp_ret = usb_maxpacket(dev, pipe, /*usb_pipeout(pipe)*/usb_pipeout_ret);
	maxp = maxp_ret;
	
	kbd = kzalloc(sizeof(struct usb_kbd), GFP_KERNEL);
	
	input_dev = input_allocate_device();
	
	if (!kbd || !input_dev){
		//@ close [1/2]usb_endpoint_descriptor_data(endpoint, bEndpointAddres);
		
		//@ close usb_host_endpoint(host_endpoint);
		//@ close [f3]usb_interface_descriptor(desc, bNumEndpoints, bInterfaceNumber);
		//@ close [f2]usb_host_interface(interface);
		//@ close usb_interface(usb_kbd_probe, disconnect, iface, dev, originalData, false, fracsize);
		
		goto fail1;
	}
	
	// --- Alloc kbd: continuation --- //
		// Because kbd is "kzalloced", their fields will be zero (if we assume a zero integer is represented by 0x00...)
		// In usb_kbd_free_mem we need some fields to be zero (and know this in verification),
		// because free'ing zero is a no-op.
		// In order to prove that these fields are zero, we need to prove it here, which we can't as far as I know.
		// So we set them to zero here.
		//
		// Can't do this before the if(kbd==0){goto fail1;} because open_struct only happens in fail2 (not in fail1,
		// because in fail1 kbd might be 0 and you can't open_struct a nullpointer).
		
		//@ assert uchars((void *)kbd, _, ?ucs);
		//@ uchars_to_chars(kbd);
		//@ forall_equals_all_eq_char_of_uchar(ucs);
		//@ close_struct_zero(kbd);
		kbd->irq = 0;
		kbd->new = 0;
		kbd->led = 0;
		kbd->leds = 0;
		kbd->cr = 0;
		kbd->led_urb_submitted = false;
	
	//@ open input_dev_unregistered(input_dev, _, _, _, _, _, _);
	
	if (usb_kbd_alloc_mem(dev, kbd)){
		//@ open usb_kbd_alloc_mem_result(?usb_kbd_alloc_mem_ret, ?stage, dev, kbd);

		//@ close [1/2]usb_endpoint_descriptor_data(endpoint, bEndpointAddres);
		
		//@ close usb_host_endpoint(host_endpoint);
		//@ close [f3]usb_interface_descriptor(desc, bNumEndpoints, _);
		//@ close [f2]usb_host_interface(interface);
		//@ close usb_interface(usb_kbd_probe, usb_kbd_disconnect, iface, dev, originalData, false, fracsize);
		
		//@ close usb_kbd_alloc_mem_result(usb_kbd_alloc_mem_ret, stage, dev, kbd);
		//@ close input_dev_unregistered(input_dev, _, _, _, _, _, _);
		goto fail2;
	}
	//@ open usb_kbd_alloc_mem_result(?usb_kbd_alloc_mem_ret, ?stage, dev, kbd);
	
	kbd->usbdev = dev;
	kbd->dev = input_dev;
	//@ close spin_lock_init_ghost_arg(leds_lock_data(kbd));
	//@ assert integer(&kbd->leds_lock, _);
	spin_lock_init(&kbd->leds_lock);
	
	// --- Fill input fields --- //
		// XXX Apparantly this is forgotten. Original code contains at least:
		// strlcat(kbd->phys, "/input0", sizeof(kbd->phys));
		// input_dev->name = kbd->name;
		// input_dev->phys = kbd->phys;
		
		input_dev->name = "usbkbd_verified keyboard";
		//@ string_to_chars(input_dev->name);
		//@ assert true;
	//@ close input_dev_unregistered(input_dev, ?some_string, _, _, _, _, 0);
	

	input_set_drvdata(input_dev, kbd);
	//@ open input_dev_unregistered(input_dev, _, _, _, _, _, kbd);

	// workaround "potentially side-effecting expression" error:
	int x = BIT_MASK(EV_KEY);
	int y = BIT_MASK(EV_LED);
	x = x | y;
	y = BIT_MASK(EV_REP);
	x = x | y;
	input_dev->evbit[0] = x; // original: BIT_MASK(EV_KEY) | BIT_MASK(EV_LED) |  BIT_MASK(EV_REP); 
	
	x = BIT_MASK(LED_NUML);
	y = BIT_MASK(LED_CAPSL);
	x = x | y;
	y = BIT_MASK(LED_SCROLLL);
	x = x | y;
	y = BIT_MASK(LED_COMPOSE);
	x = x | y;
	y = BIT_MASK(LED_KANA);
	x = x | y;
	input_dev->ledbit[0] = x; /* original: BIT_MASK(LED_NUML) | BIT_MASK(LED_CAPSL) |
		BIT_MASK(LED_SCROLLL) | BIT_MASK(LED_COMPOSE) | 
		BIT_MASK(LED_KANA);*/
	
	
	//@ open [callback_link_f]usb_probe_callback_link(usb_kbd_probe)(disconnect);
	//@ close [callback_link_f]usb_probe_callback_link(usb_kbd_probe)(disconnect);
	//@ open [fracsize]probe_disconnect_userdata(usb_kbd_probe, usb_kbd_disconnect)(); // for usb_kbd_keycodes
	//@ assert [fracsize]pointer(&usb_kbd_keycode, ?usb_kbd_keycode_ptr); // to prove it remains the same through the while.
	for (i = 0; i < 255; i++)
		/*@ invariant
			[fracsize]pointer(&usb_kbd_keycode, usb_kbd_keycode_ptr)
			&*& [fracsize]uchars(usb_kbd_keycode_ptr, 256, _)
			&*& input_dev->keybit |-> ?keybit
			&*& ints(keybit, 24, _)
			&*& i >= 0;
		@*/
	{
		unsigned char tmp = usb_kbd_keycode[i];
		//@ produce_limits (tmp);
		/*@ assert
			true == (
				(real) 1 < (real)(
					((real)24*(real)4)
					/
					8
				)
			);
		@*/
		//@ assert 1 * 8 < 24 * 4; // oh this works too...
		
		set_bit(usb_kbd_keycode[i], input_dev->keybit);
	}
	
	clear_bit(0, input_dev->keybit); 
	//@ close [fracsize]probe_disconnect_userdata(usb_kbd_probe, usb_kbd_disconnect)();
	
	input_dev->event = usb_kbd_event;
	input_dev->open = usb_kbd_open;
	input_dev->close = usb_kbd_close;
	//@ close input_dev_unregistered(input_dev, _, _, _, _, _, kbd);
	
	// (end fill input fields) //
	
	//@ assert [_]kbd->irq |-> ?irq;
	//@ assert [_]kbd->new |-> ?new;
	
	/*@ assert urb_struct_maybe(?urb_init, irq, ?urb_dev, ?urb_data,
		?urb_dma, ?urb_data_size, ?urb_has_dma, _, _, _); @*/
	
	/*@ open urb_struct_maybe(urb_init, irq, urb_dev, urb_data,
		urb_dma, urb_data_size, urb_has_dma, _, _, _); @*/
	
	//@ close complete_t_ghost_param(usb_kbd_irq, usb_kbd_irq);
	
	usb_fill_int_urb(kbd->irq,
		dev,
		pipe,
		kbd->new,
		(maxp > 8 ? 8 : maxp),
		usb_kbd_irq,
		kbd,
		endpoint->bInterval);
	
	//@ open urb_struct(true, irq, dev, new, _, 8, false, usb_kbd_irq, kbd, 0);
	kbd->irq->transfer_dma = kbd->new_dma;
	kbd->irq->transfer_flags /*|= URB_NO_TRANSFER_DMA_MAP*/
		= kbd->irq->transfer_flags | URB_NO_TRANSFER_DMA_MAP;

	
	/*@ urb_transfer_flags_add_no_transfer_dma_map(
		irq, new, kbd->new_dma, 8, kbd->irq->transfer_flags); @*/
	
	//@ close urb_struct(true, irq, dev, new, ?new_dma, 8, true, usb_kbd_irq, kbd, 0);
		
	//kbd->cr->bRequestType = USB_TYPE_CLASS | USB_RECIP_INTERFACE;
	//@ assert [_]kbd->cr |-> ?cr;
	
	//@ uchars_to_chars(cr);
	//@ close_struct(cr);
	kbd->cr->bRequestType = ((unsigned char) (USB_TYPE_CLASS + USB_RECIP_INTERFACE)); // ISSUE 1477.
	// was: kbd->cr->bRequestType = ((unsigned char) (USB_TYPE_CLASS | USB_RECIP_INTERFACE)); // ISSUE 1477.
	kbd->cr->bRequest = 0x09; // This is actually USB_REQ_SET_CONFIGURATION.
	__le16 tmp_le16 = cpu_to_le16(0x200);
	kbd->cr->wValue = /* cpu_to_le16(0x200); */ tmp_le16;
	
	tmp_le16 = cpu_to_le16(interface->desc.bInterfaceNumber);
	kbd->cr->wIndex = tmp_le16; /* cpu_to_le16(interface->desc.bInterfaceNumber desc->bInterfaceNumber);*/
	tmp_le16 = cpu_to_le16(1);
	kbd->cr->wLength = /*cpu_to_le16(1);*/ tmp_le16;
	//@ open_struct(cr);
	//@ assert chars_((void *)cr, sizeof(struct usb_ctrlrequest), ?cr_cs);
	//@ assume(cr_cs == map(some, map(the, cr_cs)));
	//@ chars__to_chars((void *)cr);
	//@ chars_to_uchars(cr);
	// XXX We don't have the USB endpoint descriptor of endpoint 0.
	// and the way endpoints are specified seems to suck a little now...
	//@ open [1/2]usb_device(dev, ?ep0);
	int usb_sndctrlpipe_dev = usb_sndctrlpipe(dev, 0);
	
	//@ assert [_]kbd->led |-> ?kbd_led;
	//@ assert kbd_led != 0;

	//@ open urb_struct_maybe(_, kbd->led, _, 0, _, _, _, _, _, _);

	//@ close complete_t_ghost_param(usb_kbd_led, usb_kbd_led);
	//@ prove_sizeof_usb_ctrlrequest_eq_8();
	
	// Workaround. See usb_endpoint_descriptor_hide
	// --> hmm workaround seems to break and now it works without. XXX
	///@ assert [?wrongone_f]usb_endpoint_descriptor(_, _, _, ?wrongone) &*& [_]usb_endpoint_descriptor(_, _, _, usb_sndctrlpipe_dev);
	///@ close [wrongone_f]usb_endpoint_descriptor_hide(_, _, _, wrongone);
	
	usb_fill_control_urb(kbd->led, dev, /*usb_sndctrlpipe(dev, 0) */ usb_sndctrlpipe_dev,
			     (void *) kbd->cr, kbd->leds, 1,
			     usb_kbd_led, kbd);
	///@ open [wrongone_f]usb_endpoint_descriptor_hide(_, _, _, wrongone);


	//@ open urb_struct (true, kbd->led, dev, kbd->leds, _, _, _, _, _, _);
	
	kbd->led->transfer_dma = kbd->leds_dma;
	//kbd->led->transfer_flags |= URB_NO_TRANSFER_DMA_MAP;
	kbd->led->transfer_flags = kbd->led->transfer_flags | URB_NO_TRANSFER_DMA_MAP;
	/*@ urb_transfer_flags_add_no_transfer_dma_map(
		kbd->led, kbd->leds, kbd->leds_dma, 1, kbd->led->transfer_flags); @*/
	//@ assert cr != 0;

	//@ close urb_struct(true, kbd->led, dev, kbd->leds, kbd->leds_dma, 1, true, usb_kbd_led, kbd, cr);
	
	// We must do this in _open, because the [1/2]reportable that is put in the URB
	// must come from the [1/2]reportable that _open gets.
	// If we take the other [1/2]reportable to put in the URB (the one that originally _probe owns),
	// then one [1/2] is gone into the URB and the other in the input-callback-system.
	// Meaning that we can't unregister the input device, because we need [1/2]reportable for that,
	// which is then unaccessible.
	// So we want to keep [1/2] in _open and _disconnect (thus in intfdata), such that
	// we can unregister the input device.
	// So we can't lose it here.
	///@ close complete_t_pred_fam(usb_kbd_irq)(kbd, fracsize, new, 8);
	
	//@ close input_open_t_ghost_param(usb_kbd_open, usb_kbd_open);
	//@ close input_close_t_ghost_param(usb_kbd_close, usb_kbd_close);
	//@ close input_event_t_ghost_param(usb_kbd_event, usb_kbd_event);

	//@ close [2/5]usb_kbd_struct_shared(kbd, _, _, _, _, _, _, _, _, _, _, _, _);

	//@ close complete_data_except_reportable(kbd, fracsize, new, 8, ?inputdev);
	
	//@ create_ghost_stuff(kbd);
	
	//@ input_ghost_register_device(input_dev, fracsize);
	//@ assert input_dev_ghost_registered(_, _, _, _, _, _, _, _, ?input_register_result);
	/*@
	if (input_register_result == 0){
	
		close times_urb_submitted(0, fracsize, kbd->led, kbd->usbdev, kbd->leds, kbd->leds_dma, 1, true, usb_kbd_led, kbd, cr);
	
		close leds_lock_data_maybe_submitted(kbd, false);
		close leds_lock_data(kbd)();
	
		spin_lock_ghost_init(&kbd->leds_lock);
		start_counting(leds_lock, kbd);
		create_ticket(leds_lock, kbd);
		close userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(input_dev, false, kbd, fracsize);
	
		// XXX automerge seems to fail. Don't know why.
		open [1/2]usb_device(dev, ep0);
		close usb_device(dev, ep0);
	}
	@*/
	
	// ---- Stage 11 ---- //
	//@ close input_open_callback_link(usb_kbd_open)(usb_kbd_close, usb_kbd_event);
	//@ close input_close_callback_link(usb_kbd_close)(usb_kbd_open, usb_kbd_event);
	//@ close input_event_callback_link(usb_kbd_event)(usb_kbd_open, usb_kbd_close);
	//@ assert input_dev_ghost_registered(_, ?somename, ?somephys, _, _, _, _, _, _);
	//@ close maybe_chars(1, somephys, 0, nil);
	error = input_register_device(kbd->dev);
	
	if (error){
		
		// new isn't provable the same since it's not an argument of userdef_input_drvdata.
		//@ open complete_data_except_reportable(kbd, fracsize, ?_new, 8, inputdev); 
		
		//@ open [2/5]usb_kbd_struct_shared(kbd, _, _, _, _, _, _, _, _, _, _, _, _);
		//@ close urb_struct_maybe(true, irq, dev, new, new_dma, 8, true, usb_kbd_irq, kbd, 0);
		
		//@ assert [_]usb_kbd_led(kbd, ?led) &*& [_]usb_kbd_leds(kbd, ?leds) &*& [_]usb_kbd_leds_dma(kbd, ?leds_dma);
		
		//@ close urb_struct_maybe(true, kbd->led, dev, kbd->leds, kbd->leds_dma, 1, true, usb_kbd_led, kbd, cr);
		
		//@ close usb_kbd_alloc_mem_result(0, 11 /* LED is initialized */, kbd->usbdev, kbd);
		//@ assert usb_kbd_usbdev(kbd, dev);
		
		// default closing stuff
			//@ close [1/2]usb_endpoint_descriptor_data(endpoint, bEndpointAddres);
		
			//@ close usb_host_endpoint(host_endpoint);
			//@ close [f3]usb_interface_descriptor(desc, bNumEndpoints, _);
			//@ close [f2]usb_host_interface(interface);
			
			//@ close [1/2]usb_device(dev, ep0);
			
			//@ close usb_interface(usb_kbd_probe, usb_kbd_disconnect, ?usb_kbd_iface, dev, originalData, false, fracsize);
		// end default closing stuff
		
		
		//@ open input_close_t_ghost_param(usb_kbd_close, usb_kbd_close);
		//@ open input_open_t_ghost_param(usb_kbd_open, usb_kbd_open);
		//@ open input_event_t_ghost_param(usb_kbd_event, usb_kbd_event);
		//@ open input_close_callback_link(usb_kbd_close)(_, _);
		//@ open input_open_callback_link(usb_kbd_open)(_,_);
		//@ open input_event_callback_link(usb_kbd_event)(_, _);
		//@ dispose_ghost_stuff(kbd);
		
		//@ spin_lock_dispose(&kbd->leds_lock);
		
		goto fail2;
	}
	
	//@ close [1/2]usb_endpoint_descriptor_data(endpoint, bEndpointAddres);
	
	//@ close usb_host_endpoint(host_endpoint);
	//@ close [f3]usb_interface_descriptor(desc, bNumEndpoints, _);
	//@ close [f2]usb_host_interface(interface);	
	
	//@ close usb_interface(usb_kbd_probe, disconnect, iface, dev, originalData, false, fracsize);

	//@ close [1/5]usb_kbd_struct_shared(kbd, _, _, _, _, _, _, _, _, _, _, _, _);

	//@ close userdef_usb_interface_data(usb_kbd_probe, usb_kbd_disconnect)(iface, dev, kbd, fracsize);
	usb_set_intfdata(iface, kbd);
	
	return 0;

fail2:
	//@ assert usb_kbd_alloc_mem_result(_, _, ?dev_, ?kbd_);
	//@ assert dev_ == dev;
	usb_kbd_free_mem(dev, kbd);
	
	//@ close usb_kbd_leds_lock(kbd, _);
	//@ open_struct(kbd); 
	//@ chars__to_uchars_(kbd);

fail1:
	input_free_device(input_dev);
	
	kfree(kbd);
	return error;
}



static void usb_kbd_disconnect(struct usb_interface *intf) //@ : vf_usb_operation_disconnect_t
	/*@ requires usb_interface(?probe_cb, usb_kbd_disconnect, intf, ?dev, ?data, true, ?fracsize)
		&*& [?callback_link_f]usb_disconnect_callback_link(usb_kbd_disconnect)(probe_cb)
		&*& not_in_interrupt_context(currentThread);
	@*/
	/*@ ensures
		usb_interface(probe_cb, usb_kbd_disconnect, intf, dev, 0, false, fracsize)
		&*& [callback_link_f]usb_disconnect_callback_link(usb_kbd_disconnect)(probe_cb)
		&*& not_in_interrupt_context(currentThread)
		&*& [fracsize]probe_disconnect_userdata(probe_cb, usb_kbd_disconnect)()
		&*& permission_to_submit_urb(_, false)
		;
	@*/
{
	//@ open [callback_link_f]usb_disconnect_callback_link(usb_kbd_disconnect)(probe_cb);
	//@ close [callback_link_f]usb_disconnect_callback_link(usb_kbd_disconnect)(probe_cb);

	struct usb_kbd *kbd = usb_get_intfdata (intf);

	usb_set_intfdata(intf, 0 /*NULL*/);
	
	// open here to prove kbd != 0.
	//@ open userdef_usb_interface_data(usb_kbd_probe, usb_kbd_disconnect)(intf, dev, kbd, fracsize);
	
	// usb_get_intfdata(intf) is always nonzero since it is set
	// with set_intfdata in the probe function, and probe is
	// always called before disconnect (see vf_usb_operation_disconnect_t and vf_usb_operation_probe_t)
	// It is unclear why the driver performs the if since it is not necessary.
	//@ assert kbd != 0;
	
	if (kbd) {
		
		// In fact this is the real kill, and the no-op kill happens when unregistering
		// the input device. In verification we look at it the other way around.
			//@ open usb_kbd_struct_shared(kbd, _, _, _, _, _, _, _, _, _, _, _, _);
			//@ close times_urb_submitted(0, 0, kbd->irq, 0, 0, 0, 0, true, 0, 0, 0);
			usb_kill_urb(kbd->irq); // no-op kill in verif, real kill in real.
			//@ open times_complete_t_pred_fam_out(0, _, _, _, _, _, _, _, _, _, _);
		
		input_unregister_device(kbd->dev);
		
		//@ open userdef_input_drvdata(usb_kbd_open, usb_kbd_close, usb_kbd_event)(_, false, _, _);
		
		// Moved from _close:
			//@ assert counting(leds_lock, kbd, ?counting_times, unit);
	
			//@ destroy_ticket<struct usb_kbd*, unit>(leds_lock, kbd); // Our own ticket (_event's)
	
			
		
		//@ assert [_]usb_kbd_led(kbd, ?led);
		//@ assert times_urb_submitted(?killcount, fracsize, ?led2, _, _, _, _, _, _, _, _);
		// Prove led == led2:
		//@ open usb_kbd_struct_shared(kbd, _, _, _, _, _, _, _, _, _, _, _, _);
		
		usb_kill_urb(kbd->led);
		
		// Get our data back after killing the URB, and dispose killcount-bookkeeping.
			//@ get_rid_of_counting();
	
			//@ open leds_lock(kbd, unit);
			//@ spin_lock_dispose_half(&kbd->leds_lock);
	
			//@ open leds_lock_data(kbd)();
	
			//@ assert [_]usbkbd_killcount(kbd, killcount);
			//@ assert [_]usbkbd_cb_out_count(kbd, ?cb_out_counter);
	
			//@ assert kbd->led_urb_submitted |-> ?led_urb_submitted;
			//@ diffcount_tickets_minimum_prove();
			//@ assert kbd->led_urb_submitted |->  false;

			//@ usbkbd_killcount_write(kbd, killcount, 0);

			//@ assert cb_out_counter >= killcount;
			//@ assert killcount == cb_out_counter || killcount == cb_out_counter + 1;
			//@ assert killcount == cb_out_counter;
	
			//@ get_rid_of_countdiff();
	
			//@ close leds_lock_data_maybe_submitted(kbd, false); // Cannot remove.
		
		//@ assert [_]usb_kbd_usbdev(kbd, dev);
		
		struct usb_device *interface_to_usbdev_ret = interface_to_usbdev(intf); // originally inside the next C line.
		//@ open usb_interface (usb_kbd_probe, usb_kbd_disconnect, intf, dev, 0, false, fracsize);
		
		//@ assert urb_struct(true, ?urb, dev, ?new, ?new_dma, 8, true, usb_kbd_irq, ?context, 0);
		//@ close urb_struct_maybe(true, urb, dev, new, new_dma, 8, true, usb_kbd_irq, context, 0); // Cannot remove.
		
		//@ open complete_data_except_reportable(data, fracsize, _, 8, _);
		
		//@ open leds_lock_data_maybe_submitted(kbd, false);
		
		//@ assert urb_struct(true, ?led3, ?dev3, ?leds, ?leds_dma, 1, true, usb_kbd_led, ?context_leds, ?cr); // XXX Would be cleaner if values would provable-remain-the-same. --> explain why they are not.
		//@ close urb_struct_maybe(true, led3, dev3, leds, leds_dma, 1, true, usb_kbd_led, context_leds, cr);
		
		//@ close usb_kbd_alloc_mem_result(0, 11 /* all allocated, all initialized */ , dev, kbd);
		usb_kbd_free_mem(/*interface_to_usbdev(intf)*/ interface_to_usbdev_ret, kbd);

		//@ assert interface_to_usbdev_ret == dev;
		
		//@ spin_lock_dispose(&kbd->leds_lock);
		//@ close usb_kbd_leds_lock(kbd, _);
		//@ open_struct(kbd);
		//@ chars__to_uchars_(kbd);
		//@ dispose_ghost_stuff(kbd);
		
		kfree(kbd);
		
		//@ close usb_interface(usb_kbd_probe, usb_kbd_disconnect, intf, dev, 0, false, fracsize);
		//@ open input_close_callback_link(usb_kbd_close)(_, _);
		//@ open input_open_callback_link(usb_kbd_open)(_,_);
		//@ open input_event_callback_link(usb_kbd_event)(_, _);
	}
	//@ assert [?f]chars(_, _, _);
	//@ leak [f]chars(_, _, _); // we know that [f] is a dummy fraction, but this information is not known here
	//@ open maybe_chars(_, _, _, _);
}


static struct usb_device_id *usb_kbd_id_table;
// original:
//static struct usb_device_id usb_kbd_id_table [] = {
//	{ USB_INTERFACE_INFO(USB_INTERFACE_CLASS_HID, USB_INTERFACE_SUBCLASS_BOOT,
//		USB_INTERFACE_PROTOCOL_KEYBOARD) },
//	{ }						/* Terminating entry */
//};


/*
 * Makes sure userspace applications know which devices this module supports.
 * See e.g. http://www.linuxjournal.com/node/5604/print
 */
// MODULE_DEVICE_TABLE (usb, usb_kbd_id_table);



static struct usb_driver usb_kbd_driver; // <-- not original
// original:
//static struct usb_driver usb_kbd_driver = {
//	.name =		"usbkbd",
//	.probe =	usb_kbd_probe,
//	.disconnect =	usb_kbd_disconnect,
//	.id_table =	usb_kbd_id_table,
//};


// flow: init->(kernel)->exit
/*@ predicate_family_instance module_state(usb_kbd_init, usb_kbd_exit)() =
	pointer(&usb_kbd_id_table, ?usb_kbd_id_table_ptr)
	&*& usb_kbd_id_table_ptr != 0
	&*& struct_usb_driver_padding(&usb_kbd_driver)
	&*& kmalloc_block(usb_kbd_id_table_ptr,2*sizeof(struct usb_device_id))
	&*& struct_usb_device_id_padding(usb_kbd_id_table_ptr)
	&*& struct_usb_device_id_padding(usb_kbd_id_table_ptr+sizeof(struct usb_device_id))
	&*& usb_driver_registered((void*)&usb_kbd_driver, usb_kbd_id_table_ptr, 1, usb_kbd_probe, usb_kbd_disconnect)
	;
@*/

// UNSAFE: there is no integration with the build and verification system of helloproc,
// which is unsafe because an unsafe contract for init and exit will be accepted.
// (but we already know we can do this safe - see helloproc - so we didn't put time in this)
//
static int /*__init*/ usb_kbd_init(void) //@ : module_setup_t(usbkbd_verified)
//@ requires module(usbkbd_verified, true) &*& not_in_interrupt_context(currentThread);
/*@ ensures
	not_in_interrupt_context(currentThread)
	&*& result == 0 ? // success
		module_state(usb_kbd_init, usb_kbd_exit)()
		&*& module_cleanup_callback_link(usb_kbd_exit)(usb_kbd_init)
	: // failure
		module(usbkbd_verified, _);
@*/
{

	//@ open_module();
	
	// --- Load keycodes --- //
		usb_kbd_keycode = kzalloc((unsigned int) 256 * sizeof(char), GFP_KERNEL);
		if (usb_kbd_keycode == 0) {
			//@ close_module();
			return -1;
		}
		
		//@ assert pointer(&usb_kbd_keycode, ?usb_kbd_keycode_ptr);
		load_keycodes(usb_kbd_keycode);
	
	//@ sizeof_of_usb_device_id_is_low();
 	usb_kbd_id_table = kzalloc((unsigned int)2*sizeof(struct usb_device_id), GFP_KERNEL); // not original code
	if (usb_kbd_id_table == 0){ // not original code
		kfree(usb_kbd_keycode);
		//@ close_module();
		return -1; // not original code
	}
	
	// UNSAFE Kernel oops if usb_kbd_driver is not properly null-initialized.
	//        Verification does not catch this.
	//        
	//        This is easy to solve by adding constraints that struct fields
	//        should be zero in the formal API specs. Because this is
	//        boring and time consuming and is not intresting from
	//        a research point of view, this was skipped.
	
	
	//@ assert pointer(&usb_kbd_id_table, ?usb_kbd_id_table_ptr);
	
	//@ uchars_to_chars(usb_kbd_id_table);
	//@ chars_limits((void*)usb_kbd_id_table);
	
	//@ chars_split((void *)usb_kbd_id_table, sizeof(struct usb_device_id));
	
	//@ close_struct(usb_kbd_id_table);
	//@ close_struct(usb_kbd_id_table+1);
	
	
	// VeriFast does not support struct initialization of the form struct something = {.x = y},
	// so we write the fields here (not exactly original code):
	usb_kbd_id_table->idVendor = 0;
	usb_kbd_id_table->idProduct = 0;
	usb_kbd_id_table->bDeviceClass = 0;
	usb_kbd_id_table->match_flags = USB_DEVICE_ID_MATCH_INT_INFO;
	usb_kbd_id_table->bInterfaceClass = USB_INTERFACE_CLASS_HID;
	usb_kbd_id_table->bInterfaceSubClass = USB_INTERFACE_SUBCLASS_BOOT;
	usb_kbd_id_table->bInterfaceProtocol = USB_INTERFACE_PROTOCOL_KEYBOARD;
	usb_kbd_id_table->driver_info = 0;
	//@ close usb_device_id(usb_kbd_id_table, false);
	
	// usb_kbd_id_table[1] is all zero.
	// We can prove this, but we need to prove that individual struct fields
	// are empty, which seems to be a bit harder... So for now just
	// fill them in by hand.
	// In fact, are we really sure having a struct initialized with zeros results
	// in the fields being zero? What if a zero-integer is not represented by 0x0000...,
	// do the C specs enforce this?
	(usb_kbd_id_table+1)->match_flags = 0;        // not original code
	(usb_kbd_id_table+1)->bInterfaceClass = 0;    // not original code
	(usb_kbd_id_table+1)->bInterfaceSubClass = 0; // not original code
	(usb_kbd_id_table+1)->bInterfaceProtocol = 0; // not original code
	(usb_kbd_id_table+1)->driver_info = 0;        // not original code
	(usb_kbd_id_table+1)->idVendor = 0;           // not original code
	(usb_kbd_id_table+1)->idProduct = 0;          // not original code
	(usb_kbd_id_table+1)->bDeviceClass = 0;       // not original code
	//@ close usb_device_id(usb_kbd_id_table+1, true);
	
	//@ close usb_device_id_table(0, usb_kbd_id_table+1);
	//@ close usb_device_id_table(1, usb_kbd_id_table);
	
	// Again writing fields instead of using struct initialization of the form struct something = {.x = y},
	usb_kbd_driver.name = "usbkbd"; // not original code
	//@ string_to_chars(usb_kbd_driver.name);
	usb_kbd_driver.probe =	usb_kbd_probe;             // not original code
	usb_kbd_driver.disconnect = usb_kbd_disconnect;   // not original code
	usb_kbd_driver.id_table = usb_kbd_id_table;       // not original code
	//@ close usb_driver(&usb_kbd_driver, usb_kbd_id_table, 1, usb_kbd_probe, usb_kbd_disconnect);
	
	//@ close probe_disconnect_userdata(usb_kbd_probe, usb_kbd_disconnect)();
	//@ close usb_probe_callback_link(usb_kbd_probe)(usb_kbd_disconnect);
	//@ close usb_disconnect_callback_link(usb_kbd_disconnect)(usb_kbd_probe);
	int result = usb_register(&usb_kbd_driver);
	if (result == 0){
		printk(/*KERN_INFO KBUILD_MODNAME ": " DRIVER_VERSION ":"
				DRIVER_DESC "\n"*/ "usbkbd_verified: loaded.\n");
		//@ close module_state(usb_kbd_init, usb_kbd_exit)();
		//@ close module_cleanup_callback_link(usb_kbd_exit)(usb_kbd_init);
		
	}else{ // not original code
		//@ open usb_driver(&usb_kbd_driver, usb_kbd_id_table_ptr, 1, usb_kbd_probe, usb_kbd_disconnect);
		
		//@ open usb_device_id_table(1, usb_kbd_id_table_ptr);
		//@ open usb_device_id_table(0, usb_kbd_id_table_ptr+sizeof(struct usb_device_id));
		//@ open usb_device_id(usb_kbd_id_table_ptr+sizeof(struct usb_device_id), true);
		//@ open usb_device_id(usb_kbd_id_table_ptr, false);
		//@ open_struct(usb_kbd_id_table);
		//@ open_struct(usb_kbd_id_table+1);
		//@ chars__join((void *)usb_kbd_id_table);
		//@ chars__to_uchars_(usb_kbd_id_table);
		kfree(usb_kbd_id_table);// not original code
		
		//@ open probe_disconnect_userdata(usb_kbd_probe, usb_kbd_disconnect)();
		//@ assert pointer(&usb_kbd_keycode, ?usb_kbd_keycode_ptr_2);
		kfree(usb_kbd_keycode); // not original code
		
		//@ open usb_disconnect_callback_link(usb_kbd_disconnect)(usb_kbd_probe);
		//@ open usb_probe_callback_link(usb_kbd_probe)(usb_kbd_disconnect);
		
		//@ close_module();
	}
	
	return result;

	
}

/*@
predicate_family_instance module_cleanup_callback_link(usb_kbd_exit)(module_setup_t *setup) =
	setup == usb_kbd_init;
@*/

static void /*__exit*/ usb_kbd_exit(void) //@ : module_cleanup_t(usbkbd_verified)
//@ requires module_state(?setup, usb_kbd_exit)() &*& not_in_interrupt_context(currentThread) &*& module_cleanup_callback_link(usb_kbd_exit)(setup);
//@ ensures module(usbkbd_verified, _)&*& not_in_interrupt_context(currentThread);
{
	//@ open module_cleanup_callback_link(usb_kbd_exit)(setup);

	//@ open module_state(usb_kbd_init, usb_kbd_exit)();
	usb_deregister(&usb_kbd_driver);
	
	//@ assert pointer(&usb_kbd_id_table, ?usb_kbd_id_table_ptr);
	//@ open usb_driver(&usb_kbd_driver, usb_kbd_id_table_ptr, 1, usb_kbd_probe, usb_kbd_disconnect);
	
	// XXX put all this in a lemma? It's probably both here and in _init.
	//@ open usb_device_id_table(1, usb_kbd_id_table_ptr);
	//@ open usb_device_id(usb_kbd_id_table_ptr, false);
	//@ open_struct(usb_kbd_id_table);
	//@ open usb_device_id_table(0, usb_kbd_id_table_ptr+sizeof(struct usb_device_id));
	//@ open usb_device_id(usb_kbd_id_table_ptr+sizeof(struct usb_device_id), true);
	//@ open_struct(usb_kbd_id_table+1);
	//@ chars__join((void*)usb_kbd_id_table);
	//@ chars__to_uchars_(usb_kbd_id_table);
	kfree(usb_kbd_id_table); // not original code
	
	//@ open probe_disconnect_userdata(usb_kbd_probe, usb_kbd_disconnect)();
	//@ assert pointer(&usb_kbd_keycode, ?usb_kbd_keycode_ptr_2);
	kfree(usb_kbd_keycode); // not original code
	
	//@ open usb_disconnect_callback_link(usb_kbd_disconnect)(usb_kbd_probe);
	//@ open usb_probe_callback_link(usb_kbd_probe)(usb_kbd_disconnect);
	
	
	//@ close_module();
}
