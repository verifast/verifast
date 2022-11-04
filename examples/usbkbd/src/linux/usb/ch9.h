#ifndef _LINUX_USB_CH9_H
#define _LINUX_USB_CH9_H

#include <linux/types.h>
#include <linux/compiler.h>

/*
 * Device and/or Interface Class codes
 * as found in bDeviceClass or bInterfaceClass
 * and defined by www.usb.org documents
 */
/* Verification: Note that the numbering is not arbitrary but has to
 * conform to the USB specs. See http://www.usb.org/developers/defined_class
 * for an easy overview.
 */
#define	USB_CLASS_PER_INTERFACE		0	/* for DeviceClass */
#define	USB_CLASS_AUDIO			1
#define	USB_CLASS_COMM			2
#define	USB_CLASS_HID			3
#define	USB_CLASS_PHYSICAL		5
#define	USB_CLASS_STILL_IMAGE		6
#define	USB_CLASS_PRINTER		7
#define	USB_CLASS_MASS_STORAGE		8
#define	USB_CLASS_HUB			9
#define	USB_CLASS_CDC_DATA		0x0a
#define	USB_CLASS_CSCID			0x0b	/* chip+ smart card */
#define	USB_CLASS_CONTENT_SEC		0x0d	/* content security */
#define	USB_CLASS_VIDEO			0x0e
#define	USB_CLASS_WIRELESS_CONTROLLER	0xe0
#define	USB_CLASS_MISC			0xef
#define	USB_CLASS_APP_SPEC		0xfe
#define	USB_CLASS_VENDOR_SPEC		0xff


struct usb_interface_descriptor {
         //__u8  bLength;
         //__u8  bDescriptorType;
 
         __u8  bInterfaceNumber;
         //__u8  bAlternateSetting;
         __u8  bNumEndpoints;
         //__u8  bInterfaceClass;
         //__u8  bInterfaceSubClass;
         //__u8  bInterfaceProtocol;
         //__u8  iInterface;
} /*__attribute__ ((packed))*/;

/*@ predicate usb_interface_descriptor(struct usb_interface_descriptor *desc, __u8 bNumEndpoints, __u8 bInterfaceNumber) = 
	// Fraction with specified size to avoid writing and stealing fractions.
	[1/2]desc->bNumEndpoints |-> bNumEndpoints
	&*& [1/2]desc->bInterfaceNumber |-> bInterfaceNumber;
@*/



#define USB_DIR_OUT                    0              /* to device */
#define USB_DIR_IN                     0x80            /* to host */


/*
 * USB types, the second of three bRequestType fields
 */
#define USB_TYPE_MASK                  96 // original: (0x03 << 5),
#define USB_TYPE_STANDARD              0  //= (0x00 << 5),
#define USB_TYPE_CLASS                 32 //= (0x01 << 5),
#define USB_TYPE_VENDOR                64 //= (0x02 << 5),
#define USB_TYPE_RESERVED              96 //= (0x03 << 5)


/*
 * USB recipients, the third of three bRequestType fields
 */
#define USB_RECIP_MASK                 0x1f
#define USB_RECIP_DEVICE               0x00
#define USB_RECIP_INTERFACE            0x01
#define USB_RECIP_ENDPOINT             0x02
#define USB_RECIP_OTHER                0x03
/* From Wireless USB 1.0 */
#define USB_RECIP_PORT                 0x04
#define USB_RECIP_RPIPE                0x05

/* xfer type */
#define USB_ENDPOINT_XFER_CONTROL       0
#define USB_ENDPOINT_XFER_ISOC          1
#define USB_ENDPOINT_XFER_BULK          2
#define USB_ENDPOINT_XFER_INT           3

struct usb_endpoint_descriptor {
	//__u8  bLength;
	//__u8  bDescriptorType;

	__u8 /*int*/  bEndpointAddress;
	//__u8  bmAttributes;
	//__le16 wMaxPacketSize;
	__u8 /*int*/  bInterval;

	///* NOTE:  these two are _only_ in audio endpoints. */
	///* use USB_DT_ENDPOINT*_SIZE in bLength, not sizeof. */
	//__u8  bRefresh;
	//__u8  bSynchAddress;
} /*__attribute__ ((packed))*/;

// XXX hmmm I dunno if I like the way this is done here...
/*@ predicate usb_endpoint_descriptor_data(struct usb_endpoint_descriptor *epd; __u8 bEndpointAddress) = 
	[1/2]epd->bEndpointAddress |-> bEndpointAddress
	&*& [1/2]epd->bInterval |-> ?bInterval;
@*/

/*@ 
  predicate usb_endpoint_descriptor(struct usb_endpoint_descriptor *epd; int direction, int xfer_type, int pipe);

lemma_auto void usb_endpoint_descriptor_inv();
    requires [?f]usb_endpoint_descriptor(?epd, ?dir, ?xfer_type, ?pipe);
    ensures [f]usb_endpoint_descriptor(epd, dir, xfer_type, pipe) &*& object_pointer_within_limits(epd, sizeof(struct usb_endpoint_descriptor)) == true;
@*/

static inline int usb_endpoint_is_int_in(const struct usb_endpoint_descriptor *epd);
	//@ requires [?f]usb_endpoint_descriptor(epd, ?dir, ?xfer_type, ?pipe);
	/*@ ensures
		[f]usb_endpoint_descriptor(epd, dir, xfer_type, pipe)
		&*& result != 0 ? // yes it is an INT IN endpoint.
			dir == USB_DIR_IN
			&*& xfer_type == USB_ENDPOINT_XFER_INT
		: // No it is not.
			(dir != USB_DIR_IN || xfer_type != USB_ENDPOINT_XFER_INT)
	;
	@*/


struct usb_ctrlrequest{
        __u8 bRequestType;
        __u8 bRequest;
        __le16 wValue;
        __le16 wIndex;
        __le16 wLength;
}/* __attribute__ ((packed))*/;

// API users need this when passing a buffer of a certain size that is actually a struct.
// API users can't prove this themselve, in fact vf should know that sizeof(struct x) >= sum of sizeof of struct fields. XXX
/*@ lemma void prove_sizeof_usb_ctrlrequest_eq_8();
	requires true;
	ensures sizeof(struct usb_ctrlrequest) == 8;
@*/

struct usb_device_descriptor {
	__u8  bLength;
	__u8  bDescriptorType;

	__le16 bcdUSB;
	__u8  bDeviceClass;
	__u8  bDeviceSubClass;
	__u8  bDeviceProtocol;
	__u8  bMaxPacketSize0;
	__le16 idVendor;
	__le16 idProduct;
	__le16 bcdDevice;
	__u8  iManufacturer;
	__u8  iProduct;
	__u8  iSerialNumber;
	__u8  bNumConfigurations;
};


#endif
