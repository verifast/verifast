#ifndef _WKBD_KEYCODES_H
#define _WKBD_KEYCODES_H

void load_keycodes(unsigned char *usb_kbd_keycode);
//@ requires uchars(usb_kbd_keycode, 256, ?keycodes_list);
//@ ensures uchars(usb_kbd_keycode, 256, ?keycodes_list_2);

#endif

