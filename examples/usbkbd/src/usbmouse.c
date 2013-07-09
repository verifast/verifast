/*
 *  Copyright (c) 1999-2001 Vojtech Pavlik
 *
 *  USB HIDBP Mouse support
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

#include <linux+kernel.h>
#include <linux+slab.h>
#include <linux+module.h>
#include <linux+init.h>
#include <linux+usb+input.h>
#include <linux+hid.h>

/* for apple IDs */
#ifdef CONFIG_USB_HID_MODULE
#include "../hid-ids.h"
#endif

/*
 * Version Information
 */
#define DRIVER_VERSION "v1.6"
#define DRIVER_AUTHOR "Vojtech Pavlik <vojtech@ucw.cz>"
#define DRIVER_DESC "USB HID Boot Protocol mouse driver"
#define DRIVER_LICENSE "GPL"

//MODULE_AUTHOR(DRIVER_AUTHOR);
//MODULE_DESCRIPTION(DRIVER_DESC);
//MODULE_LICENSE(DRIVER_LICENSE);

struct usb_mouse {
	/*char name[128];*/ char* name;
	/*char phys[64];*/ char* phys;
	struct usb_device *usbdev;
	struct input_dev *dev;
	struct urb *irq;

	signed char *data;
	dma_addr_t data_dma;
};
/*@
predicate_family_instance complete_t_pred_fam(usb_mouse_irq)(
	real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, struct usb_mouse *context, void *setup
) =
	[1/2]context->data |-> buffer &*&
	[1/2]context->dev |-> ?inputdev &*&
	buffer_alloc_size == 8 &*&
	[1/4]input_dev_reportable(inputdev, context);

predicate_family_instance complete_t_pred_fam_out(usb_mouse_irq)(real fracsize,
	struct urb *urb, struct usb_device *usb_dev, void *buffer, dma_addr_t buffer_dma, int buffer_alloc_size, bool user_alloc_dma, usb_complete_t complete, void *context, void *setup
)= complete_t_pred_fam(usb_mouse_irq)(fracsize, urb, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup) &*&
   urb_struct(true,
		urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
	);
@*/
static void usb_mouse_irq(struct urb *urb) //@: usb_complete_t_no_pointer
/*@ requires
		urb_struct(true,
			urb, ?usb_dev, ?buffer, ?buffer_dma, ?buffer_alloc_size, ?user_alloc_dma, ?complete, ?context, ?setup
		)
		&*& buffer != 0
		&*& permission_to_submit_urb(?urbs_submitted, true)
		&*& complete_t_pred_fam(usb_mouse_irq)(?fracsize,
			urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
		)
		&*& current_thread_in_cb(currentThread, false);
	@*/
	/*@ ensures 
		permission_to_submit_urb(_, true)
		&*& current_thread_in_cb(currentThread, ?deferred_data_xfer)
		&*& deferred_data_xfer ?
			complete_t_pred_fam(usb_mouse_irq)(fracsize,
				urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
			)
		:
			complete_t_pred_fam_out(usb_mouse_irq)(fracsize,
				urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup
			)
		;
	@*/
{
	//@ open urb_struct(true, urb, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	struct usb_mouse *mouse = urb->context;
	//@ open complete_t_pred_fam(usb_mouse_irq)(fracsize, urb, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	signed char *data = mouse->data;
	struct input_dev *dev = mouse->dev;
	int status;

	switch (urb->status) {
	case 0:			/* success */
		break;
	case -ECONNRESET:	/* unlink */
	case -ENOENT:
	case -ESHUTDOWN:
		////@ open complete_t_pred_fam(usb_mouse_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		//@ close complete_t_pred_fam(usb_mouse_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		//@ close complete_t_pred_fam_out(usb_mouse_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		return;
	/* -EPIPE:  should clear the halt */
	default:		/* error */
		goto resubmit;
	}
	//@ uchars_to_chars(data);
	input_report_key(dev, BTN_LEFT,   data[0] & 0x01);
	input_report_key(dev, BTN_RIGHT,  data[0] & 0x02);
	input_report_key(dev, BTN_MIDDLE, data[0] & 0x04);
	input_report_key(dev, BTN_SIDE,   data[0] & 0x08);
	input_report_key(dev, BTN_EXTRA,  data[0] & 0x10);

	input_report_rel(dev, REL_X,     data[1]);
	input_report_rel(dev, REL_Y,     data[2]);
	input_report_rel(dev, REL_WHEEL, data[3]);

	input_sync(dev);
resubmit:
	//@ close urb_struct(true, urb, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	//@ close usb_submit_urb_ghost_arg(true, fracsize);
	status = usb_submit_urb (urb, GFP_ATOMIC);
	//@ close complete_t_pred_fam(usb_mouse_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
	if (status != 0) {
		//@ close complete_t_pred_fam_out(usb_mouse_irq)(fracsize, urb, usb_dev, buffer, buffer_dma,buffer_alloc_size, user_alloc_dma, complete, context, setup);
		/*TODO: dev_err(&mouse->usbdev->dev,
			"can't resubmit intr, %s-%s/input0, status %d\n",
			mouse->usbdev->bus->bus_name,
			mouse->usbdev->devpath, status); */
	}
}

void usb_mouse_event_dummy()
  //@ requires true;
  //@ ensures true;
{
}

/*@
predicate_family_instance userdef_input_drvdata(usb_mouse_open, usb_mouse_close, usb_mouse_event_dummy)(struct input_dev *inputdev, bool is_opened, struct usb_mouse *mouse, real fracsize) =
  mouse->usbdev |-> ?usbdev &*&
  mouse->irq |-> ?irq_urb &*&
  mouse->data_dma |-> ?data_dma &*&
  [1/2]mouse->data |-> ?data &*&
  [1/4]mouse->dev |-> inputdev &*&
  ( is_opened == false ? 
    [1/2]mouse->dev |-> inputdev &*&
    [1/2]mouse->data |-> data //&*& uchars((void*) data, 8, _)
  : 
    true) &*&
  permission_to_submit_urb(_, false) &*&
  !is_opened ?	
    urb_struct(true, irq_urb, usbdev, data, data_dma, 8, true, usb_mouse_irq, mouse, 0) &*& data != 0
  :
    urb_submitted(fracsize, irq_urb, usbdev, data, data_dma, 8, true, usb_mouse_irq, mouse, 0) &*& data != 0 &*& [1/4]input_dev_reportable(inputdev, mouse)
;

predicate_family_instance input_open_callback_link(usb_mouse_open)(void* close_cb, void* event_cb) =
  close_cb == usb_mouse_close &*& event_cb == usb_mouse_event_dummy;
@*/

static int usb_mouse_open(struct input_dev *dev) //@: input_open_t_no_pointer
	/*@ requires userdef_input_drvdata(usb_mouse_open, ?close_cb, ?event_cb)(dev, false, ?context, ?fracsize)
		&*& input_open_callback_link(usb_mouse_open)(close_cb, event_cb)
		&*& [1/2]input_dev_reportable(dev, context)
		&*& not_in_interrupt_context(currentThread);
	@*/
	/*@ ensures
		not_in_interrupt_context(currentThread)
		&*& input_open_callback_link(usb_mouse_open)(close_cb, event_cb)
		&*& result == 0 ? // success
			userdef_input_drvdata(usb_mouse_open, close_cb, event_cb)(dev, true, context, fracsize)
		: // failure
			userdef_input_drvdata(usb_mouse_open, close_cb, event_cb)(dev, false, context, fracsize)
			&*& [1/2]input_dev_reportable(dev, context)
		;
	@*/
{
	//@ open input_open_callback_link(usb_mouse_open)(close_cb, event_cb);
	//@ close input_open_callback_link(usb_mouse_open)(close_cb, event_cb);
	struct usb_mouse *mouse = input_get_drvdata(dev);
	//@ open userdef_input_drvdata(usb_mouse_open, usb_mouse_close, usb_mouse_event_dummy)(dev, false, mouse, fracsize);
	mouse->irq->dev = mouse->usbdev;
	//@ void* buffer = mouse->data;
	//@ struct urb* urb = mouse->irq;
	//@ close urb_struct(true, mouse->irq, mouse->usbdev, mouse->data, mouse->data_dma, 8, true, usb_mouse_irq, mouse,  _);
	//@ close usb_submit_urb_ghost_arg(false, fracsize);
	/*@ close complete_t_pred_fam(usb_mouse_irq)(fracsize,
			mouse->irq, mouse->usbdev, mouse->data, mouse->data_dma, 8, true, usb_mouse_irq, mouse, 0
		); @*/
	//@ close urb_struct(true, mouse->irq, mouse->usbdev, buffer, mouse->data_dma, 8, true, usb_mouse_irq, mouse,  _);
	int usb_submit_urb_result = usb_submit_urb(mouse->irq, GFP_KERNEL);
	
	if (usb_submit_urb_result != 0) {
		/*@ open complete_t_pred_fam(usb_mouse_irq)(fracsize,
			mouse->irq, mouse->usbdev, mouse->data, mouse->data_dma, 8, true, usb_mouse_irq, mouse, 0
		); @*/
		//@ close urb_struct(true, urb, _, buffer, _, _, true, _, _, _);
		//@ close userdef_input_drvdata(usb_mouse_open, usb_mouse_close, usb_mouse_event_dummy)(dev, false, context, fracsize);
		return -EIO;
	}
	//@ close userdef_input_drvdata(usb_mouse_open, usb_mouse_close, usb_mouse_event_dummy)(dev, true, context, fracsize);
	////@ leak uchars(_, _, _);
	return 0;
}

/*@
predicate_family_instance input_close_callback_link(usb_mouse_close)(void* open_cb, void* event_cb) =
  open_cb == usb_mouse_open &*& event_cb == usb_mouse_event_dummy;
@*/

/*@
predicate_family_instance input_event_callback_link(usb_mouse_event_dummy)(void* open_cb, void* event_cb) =
  true;
@*/

static void usb_mouse_close(struct input_dev *dev) //@: input_close_t_no_pointer
/*@ requires userdef_input_drvdata(?open_cb, usb_mouse_close, ?event_cb)(dev, true, ?data, ?fracsize) &*& not_in_interrupt_context(currentThread)
		&*& input_close_callback_link(usb_mouse_close)(open_cb, event_cb);
	@*/
	/*@ ensures  userdef_input_drvdata(open_cb, usb_mouse_close, event_cb)(dev, false, data, fracsize)
		&*& input_close_callback_link(usb_mouse_close)(open_cb, event_cb)
		&*& [1/2]input_dev_reportable(dev, data)
		&*& not_in_interrupt_context(currentThread); // empirically confirmed with in_interrupt()
	@*/
{
	//@ open input_close_callback_link(usb_mouse_close)(open_cb, event_cb);
	//@ close input_close_callback_link(usb_mouse_close)(open_cb, event_cb);
	//@ open userdef_input_drvdata(usb_mouse_open, usb_mouse_close, usb_mouse_event_dummy)(dev, true, data, fracsize);
	//@ assert urb_submitted(fracsize, ?irq_urb, ?usb_dev, ?buffer, ?buffer_dma, ?buffer_alloc_size, ?user_alloc_dma, ?complete, ?context, ?setup);
	//@ close times_urb_submitted(0, fracsize, irq_urb, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	//@ close times_urb_submitted(1, fracsize, irq_urb, usb_dev, buffer, buffer_dma, buffer_alloc_size, user_alloc_dma, complete, context, setup);
	struct usb_mouse *mouse = input_get_drvdata(dev);
	////@ open complete_t_
	usb_kill_urb(mouse->irq);
	//@ open times_complete_t_pred_fam_out(1, _, _, _, _, _, _, _, _, _, _);
	//@ open complete_t_pred_fam_out(usb_mouse_irq)(_, _, _, _, _, _, _, _, _, _);
	//@ open complete_t_pred_fam(usb_mouse_irq)(_, _, _, _, _, _, _, _, _, _);
	//@ close userdef_input_drvdata(usb_mouse_open, usb_mouse_close, usb_mouse_event_dummy)(dev, false, data, fracsize);
	//@ open times_complete_t_pred_fam_out(0, _, _, _, _, _, _, _, _, _, _);
}

/*@
predicate_family_instance userdef_usb_interface_data(usb_mouse_probe, usb_mouse_disconnect)(struct usb_interface *intf, struct usb_device *usb_device, struct usb_mouse *mouse, real probe_disconnect_fraction_size) =
  input_dev_registered(?inputdev, ?mousename, usb_mouse_open, usb_mouse_close, usb_mouse_event_dummy, mouse, probe_disconnect_fraction_size) &*&
  [1/4]mouse->dev |-> ?dev  &*&
  [1/2]input_dev_reportable(_, _) &*&
  mouse->name |-> ?name &*&
  mouse->phys |-> ?phys &*&
  struct_usb_mouse_padding(mouse) &*&
  kmalloc_block(name, 128) &*&
  kmalloc_block(phys, 64) &*&
  chars(phys, 64, _) &*&
  kmalloc_block(mouse, sizeof(struct usb_mouse)) &*&
  [probe_disconnect_fraction_size]probe_disconnect_userdata(usb_mouse_probe, usb_mouse_disconnect)();
  
predicate_family_instance usb_probe_callback_link(usb_mouse_probe)(void* disconnect_cb) =
  usb_mouse_disconnect == disconnect_cb;
@*/ 

static int usb_mouse_probe(struct usb_interface *intf, const struct usb_device_id *id) //@: vf_usb_operation_probe_t
/*@ requires
		usb_interface(usb_mouse_probe, ?disconnect_cb, intf, _, ?originalData, false, ?fracsize)
		&*& permission_to_submit_urb(?urbs_submitted, false)
		&*& not_in_interrupt_context(currentThread)
		&*& [fracsize]probe_disconnect_userdata(usb_mouse_probe, disconnect_cb)()
		&*& [?callback_link_f]usb_probe_callback_link(usb_mouse_probe)(disconnect_cb);
	@*/
	/*@ ensures
		not_in_interrupt_context(currentThread)
		&*& [callback_link_f]usb_probe_callback_link(usb_mouse_probe)(disconnect_cb)
		&*& result == 0 ? // success
			// probe_disconnect_userdata is not returned, so the user "has to put it somewhere",
			// and give it back with _disconnect.
			// you can put it in usb_interface: it includes userdata which
			// can eat whatever probe_disconnect_userdata contains.
			usb_interface(usb_mouse_probe, disconnect_cb, intf, _, ?data, true, fracsize)
			//&*& permission_to_submit_urb(_, false)
		: // failure
			usb_interface(usb_mouse_probe, disconnect_cb, intf, _, ?data, false, fracsize)
			
			// XXX meh, the permission count thing is annoying and I don't think it actually
			// solves much at all, so made it "_" for now.
			&*& permission_to_submit_urb(_, false)
			&*& data == originalData || data == 0
			&*& [fracsize]probe_disconnect_userdata(usb_mouse_probe, _)()
		;
	@*/
{
	//@ open [callback_link_f]usb_probe_callback_link(usb_mouse_probe)(disconnect_cb);
	//@ close [callback_link_f]usb_probe_callback_link(usb_mouse_probe)(disconnect_cb);
	struct usb_device *dev = interface_to_usbdev(intf);
	struct usb_host_interface *interface;
	struct usb_endpoint_descriptor *endpoint;
	struct usb_mouse *mouse;
	struct input_dev *input_dev;
	int pipe, maxp;
	int error = -ENOMEM;
	bool free_mouse_name = true;
	
	//@ open usb_interface(usb_mouse_probe, _, _, _, _, _, _);

	interface = intf->cur_altsetting;
	
		// extra for VF parsing:
	struct usb_interface_descriptor *desc =
		vf_usb_get_interface_descriptor_of_host_interface(interface);
	
	//@ open [?f2]usb_host_interface(interface, _);
	//@ open [?f3]usb_interface_descriptor(desc, ?bNumEndpoints, ?bInterfaceNumber);

	if (desc->bNumEndpoints != 1) {
		//@ close [f3]usb_interface_descriptor(desc, bNumEndpoints, bInterfaceNumber);
		//@ close [f2]usb_host_interface(interface, desc);
		//@ close usb_interface(usb_mouse_probe, disconnect_cb, intf, _, originalData, false, fracsize);
		return -ENODEV;
	}

	endpoint = vf_usb_get_endpoint_descriptor_of_host_endpoint(interface->endpoint);
	//endpoint = &interface->endpoint[0].desc;
	//@ open usb_host_endpoint(interface->endpoint, endpoint);
	
	int usb_endpoint_is_int_in_res = usb_endpoint_is_int_in(endpoint);
	if (usb_endpoint_is_int_in_res == 0) {
	 	//@ close usb_host_endpoint(interface->endpoint, endpoint);
	 	//@ close [f3]usb_interface_descriptor(desc, bNumEndpoints, bInterfaceNumber);
		//@ close [f2]usb_host_interface(interface, desc);
		//@ close usb_interface(usb_mouse_probe, disconnect_cb, intf, _, originalData, false, fracsize);
		return -ENODEV;
	}

	pipe = usb_rcvintpipe(dev, endpoint->bEndpointAddress);
	
	int usb_pipeout_ret = usb_pipeout(pipe);
	maxp = usb_maxpacket(dev, pipe, usb_pipeout_ret);

	mouse = kzalloc(sizeof(struct usb_mouse), GFP_KERNEL);
	char *mouse_name = kzalloc(sizeof(char) * 128, GFP_KERNEL);
	char *mouse_phys = kzalloc(sizeof(char) * 64 , GFP_KERNEL);
	if (mouse_name == 0 || mouse_phys == 0){
		kfree(mouse);
		mouse = 0;
	}
	
	input_dev = input_allocate_device();
	if (mouse == 0 || input_dev == 0)
		goto fail1;
	
	//@ uchars_to_chars(mouse);
	//@ close_struct(mouse);
	
	//@ uchars_to_chars(mouse_name);	
	//@ uchars_to_chars(mouse_phys);
	*mouse_name = '\0';
	*mouse_phys = '\0';
	//@ close chars(mouse_name, 128, _);
	//@ close chars(mouse_phys, 64, _);
	mouse->name = mouse_name;
	mouse->phys = mouse_phys;
	
	mouse->usbdev = 0;
	mouse->dev = 0;
	mouse->irq = 0;
	mouse->data = 0;
	mouse->data_dma = 0;
	
	mouse->data = usb_alloc_coherent(dev, 8, GFP_ATOMIC, &mouse->data_dma);
	signed char* data_tmp = mouse->data;
	if (mouse->data == 0) {
		//@ open_struct(mouse);
		//@ chars_to_uchars(mouse);
		//@ chars_to_uchars(mouse_name);
		//@ chars_to_uchars(mouse_phys);
		goto fail1;
	}

	mouse->irq = usb_alloc_urb(0, GFP_KERNEL);
	if (mouse->irq == 0)
		goto fail2;

	mouse->usbdev = dev;
	mouse->dev = input_dev;

	if (dev->manufacturer != 0)
		strlcpy(mouse->name, dev->manufacturer, 128/*sizeof(mouse->name)*/);

	if (dev->product != 0) {
		if (dev->manufacturer != 0) {
			strlcat(mouse->name, " ", 128/*sizeof(mouse->name)*/);
		}
		strlcat(mouse->name, dev->product, 128/*sizeof(mouse->name)*/);
	}
	size_t mouse_name_length = strlen(mouse->name);
	if (mouse_name_length != 0)
	  	; 
	  	//TODO
		//snprintf(mouse->name, 128 /*sizeof(mouse->name)*/,
		//	 "USB HIDBP Mouse %04x:%04x",
		//	 le16_to_cpu(dev->descriptor.idVendor),
		//	 le16_to_cpu(dev->descriptor.idProduct));

	usb_make_path(dev, mouse->phys, 64/*sizeof(mouse->phys)*/);
	strlcat(mouse->phys, "/input0", 64/*sizeof(mouse->phys)*/);

	
	//@ open input_dev_unregistered(input_dev, _, _, _, _, _);
	
	input_dev->name = mouse->name;
	input_dev->phys = mouse->phys;
	//TODO: usb_to_input_id(dev, &input_dev->id);
	//TODO: input_dev->dev.parent = &intf->dev;
	//TODO:
	/*input_dev->evbit[0] = BIT_MASK(EV_KEY) | BIT_MASK(EV_REL);
	input_dev->keybit[BIT_WORD(BTN_MOUSE)] = BIT_MASK(BTN_LEFT) |
		BIT_MASK(BTN_RIGHT) | BIT_MASK(BTN_MIDDLE);
	input_dev->relbit[0] = BIT_MASK(REL_X) | BIT_MASK(REL_Y);
	input_dev->keybit[BIT_WORD(BTN_MOUSE)] |= BIT_MASK(BTN_SIDE) |
		BIT_MASK(BTN_EXTRA);
	input_dev->relbit[0] |= BIT_MASK(REL_WHEEL);*/
	
	//@ close input_dev_unregistered(input_dev, _, _, _, _, _);

	input_set_drvdata(input_dev, mouse);
	
	//@ open input_dev_unregistered(input_dev, _, _, _, _, _);

	input_dev->open = usb_mouse_open;
	input_dev->close = usb_mouse_close;
	input_dev->event = usb_mouse_event_dummy; // not used
	
	//@ close usb_device(dev, _);
	//@ close complete_t_ghost_param(usb_mouse_irq, usb_mouse_irq);

	usb_fill_int_urb(mouse->irq, dev, pipe, mouse->data,
			 (maxp > 8 ? 8 : maxp),
			 usb_mouse_irq, mouse, endpoint->bInterval);
	mouse->irq->transfer_dma = mouse->data_dma;
	mouse->irq->transfer_flags = mouse->irq->transfer_flags | URB_NO_TRANSFER_DMA_MAP;
	
	/*@ urb_transfer_flags_add_no_transfer_dma_map(
		mouse->irq, data_tmp, mouse->data_dma, 8, mouse->irq->transfer_flags); @*/
	//@ assert mouse->irq |-> ?irq;
	//@ close urb_struct(true, irq, _, data_tmp, mouse->data_dma, 8, true, usb_mouse_irq, mouse, 0);
	
	//@ close input_open_t_ghost_param(usb_mouse_open, usb_mouse_open);
	//@ close input_close_t_ghost_param(usb_mouse_close, usb_mouse_close);
	//@ assume(is_input_event_t_no_pointer(usb_mouse_event_dummy) == true); // HACK HACK HACK, there are no events for this driver
	//@ close input_event_t_ghost_param(usb_mouse_event_dummy, usb_mouse_event_dummy);
	
	//@ close input_dev_unregistered(input_dev, _, _, _, _, _);
	
	//@ input_ghost_register_device(input_dev, fracsize);
	//@ close input_open_callback_link(usb_mouse_open)(usb_mouse_close, usb_mouse_event_dummy);
	//@ close input_close_callback_link(usb_mouse_close)(usb_mouse_open, usb_mouse_event_dummy);
	//@ close input_event_callback_link(usb_mouse_event_dummy)(usb_mouse_open, usb_mouse_close);
	free_mouse_name = false;
	//@ assert input_dev_ghost_registered(_, _, _, _, _, _, _, ?input_register_result);
	/*@
	  if (input_register_result == 0){
	    close userdef_input_drvdata(usb_mouse_open, usb_mouse_close, usb_mouse_event_dummy)(input_dev, false, mouse, fracsize);
	  }
	@*/
	error = input_register_device(mouse->dev);
	if (error != 0) {
		//@ open input_open_callback_link(usb_mouse_open)(usb_mouse_close, usb_mouse_event_dummy);
		//@ open input_close_callback_link(usb_mouse_close)(usb_mouse_open, usb_mouse_event_dummy);
		//@ open input_event_callback_link(usb_mouse_event_dummy)(usb_mouse_open, usb_mouse_close);
		//@ open input_open_t_ghost_param(usb_mouse_open, usb_mouse_open);
		//@ open input_close_t_ghost_param(usb_mouse_close, usb_mouse_close);
		//@ open input_event_t_ghost_param(usb_mouse_event_dummy, usb_mouse_event_dummy);
		goto fail3;
	}
	//@ close usb_interface_descriptor(desc, 1, _);
	//@ close usb_host_endpoint(interface->endpoint, endpoint);
	//@ close [f2]usb_host_interface(interface, desc);
	//@ close usb_interface(usb_mouse_probe, usb_mouse_disconnect, intf, dev, originalData, false, fracsize);
	//@ close userdef_usb_interface_data(usb_mouse_probe, usb_mouse_disconnect)(intf, dev, mouse, fracsize);
	usb_set_intfdata(intf, mouse);
	return 0;

fail3:	
   	//@ close urb_struct_maybe(true, irq, _, _, _, _, _, _, _, _);
	usb_free_urb(mouse->irq);
fail2:	
	usb_free_coherent(dev, 8, mouse->data, mouse->data_dma);
	//@ open_struct(mouse);
	//@ chars_to_uchars(mouse);
fail1:	
	input_free_device(input_dev);
	kfree(mouse);
	kfree(mouse_name); kfree(mouse_phys); // not original code
	//@ close [f3]usb_interface_descriptor(desc, bNumEndpoints, bInterfaceNumber);
	//@ close usb_host_endpoint(interface->endpoint, endpoint);
	//@ close [f2]usb_host_interface(interface, desc);
	//@ close usb_interface(usb_mouse_probe, disconnect_cb, intf, _, originalData, false, fracsize);
	return error;
}

static void usb_mouse_disconnect(struct usb_interface *intf)
  //@ requires false;
  //@ ensures false;
{
	struct usb_mouse *mouse = usb_get_intfdata (intf);

	usb_set_intfdata(intf, NULL);
	if (mouse) {
		usb_kill_urb(mouse->irq);
		input_unregister_device(mouse->dev);
		usb_free_urb(mouse->irq);
		usb_free_coherent(interface_to_usbdev(intf), 8, mouse->data, mouse->data_dma);
		kfree(mouse);
	}
}

static struct usb_device_id usb_mouse_id_table [] = {
	{ USB_INTERFACE_INFO(USB_INTERFACE_CLASS_HID, USB_INTERFACE_SUBCLASS_BOOT,
		USB_INTERFACE_PROTOCOL_MOUSE) },
	{ }	/* Terminating entry */
};

//MODULE_DEVICE_TABLE (usb, usb_mouse_id_table);

/*static struct usb_driver usb_mouse_driver = {
	.name		= "usbmouse",
	.probe		= usb_mouse_probe,
	.disconnect	= usb_mouse_disconnect,
	.id_table	= usb_mouse_id_table,
};
*/
//module_usb_driver(usb_mouse_driver);
