// On long terms this should be integrated with the buildsystem of helloproc.

/*
 * initcode.h must be included in begin of file (VeriFast parser can't handle #includes at the end
 * of the file). module_init(...) doesn't seem to work on forward declarations.
 * So we introduce extra functions usb_kbd_init_wrap and usb_kbd_exit_wrap.
 */

static int /*__init*/ usb_kbd_init(void);
static void /*__exit*/ usb_kbd_exit(void);

int __init usb_kbd_init_wrap(void){
	return usb_kbd_init();
}

void __exit usb_kbd_exit_wrap(void){
	usb_kbd_exit();
}

module_init(usb_kbd_init_wrap);
module_exit(usb_kbd_exit_wrap);
