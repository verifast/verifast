#include <linux/usb.h>
/*#include "linux+mod_devicetable.h"
 #include "linux+errno.h"
 #include "linux+usb+ch9.h"*/


// XXX static? nonstatic?
struct usb_interface_descriptor *vf_usb_get_interface_descriptor_of_host_interface(
			struct usb_host_interface *usb_host_interface)
{
	return &usb_host_interface->desc;
}

struct usb_endpoint_descriptor *vf_usb_get_endpoint_descriptor_of_host_endpoint(
			struct usb_host_endpoint *usb_host_endpoint)
{			
	return &usb_host_endpoint->desc;
}
