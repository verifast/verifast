#include "usbkbd_keycodes.h"

void load_one_keycode(unsigned char *usb_kbd_keycode, int position, unsigned char code)
//@ requires array<unsigned char>(usb_kbd_keycode, 256, sizeof(unsigned char), u_character, ?keycodes_list) &*& 0 <= position &*& position <= 255;
//@ ensures array<unsigned char>(usb_kbd_keycode, 256, sizeof(unsigned char), u_character, ?keycodes_list_2);
{
	usb_kbd_keycode[position] = code;
}

void load_keycodes(unsigned char *usb_kbd_keycode)
//@ requires array<unsigned char>(usb_kbd_keycode, 256, sizeof(unsigned char), u_character, ?keycodes_list);
//@ ensures array<unsigned char>(usb_kbd_keycode, 256, sizeof(unsigned char), u_character, ?keycodes_list_2);
{

	// USB Keycodes can be found on USB HID Usage Tables 1.1 pdf-page 53.

	// Original code:
	/*
	static const unsigned char usb_kbd_keycode[256] = {
	  0,  0,  0,  0, 30, 48, 46, 32, 18, 33, 34, 35, 23, 36, 37, 38,
	 50, 49, 24, 25, 16, 19, 31, 20, 22, 47, 17, 45, 21, 44,  2,  3,
	  4,  5,  6,  7,  8,  9, 10, 11, 28,  1, 14, 15, 57, 12, 13, 26,
	 27, 43, 43, 39, 40, 41, 51, 52, 53, 58, 59, 60, 61, 62, 63, 64,
	 65, 66, 67, 68, 87, 88, 99, 70,119,110,102,104,111,107,109,106,
	105,108,103, 69, 98, 55, 74, 78, 96, 79, 80, 81, 75, 76, 77, 71,
	 72, 73, 82, 83, 86,127,116,117,183,184,185,186,187,188,189,190,
	191,192,193,194,134,138,130,132,128,129,131,137,133,135,136,113,
	115,114,  0,  0,  0,121,  0, 89, 93,124, 92, 94, 95,  0,  0,  0,
	122,123, 90, 91, 85,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
	  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
	  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
	  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
	  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
	 29, 42, 56,125, 97, 54,100,126,164,166,165,163,161,115,114,113,
	150,158,159,128,136,177,178,176,142,152,173,140
	};
	*/

	int i = 0;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 30); i++;
	load_one_keycode(usb_kbd_keycode, i, 48); i++;
	load_one_keycode(usb_kbd_keycode, i, 46); i++;
	load_one_keycode(usb_kbd_keycode, i, 32); i++;
	load_one_keycode(usb_kbd_keycode, i, 18); i++;
	load_one_keycode(usb_kbd_keycode, i, 33); i++;
	load_one_keycode(usb_kbd_keycode, i, 34); i++;
	load_one_keycode(usb_kbd_keycode, i, 35); i++;
	load_one_keycode(usb_kbd_keycode, i, 23); i++;
	load_one_keycode(usb_kbd_keycode, i, 36); i++;
	load_one_keycode(usb_kbd_keycode, i, 37); i++;
	load_one_keycode(usb_kbd_keycode, i, 38); i++;
	load_one_keycode(usb_kbd_keycode, i, 50); i++;
	load_one_keycode(usb_kbd_keycode, i, 49); i++;
	load_one_keycode(usb_kbd_keycode, i, 24); i++;
	load_one_keycode(usb_kbd_keycode, i, 25); i++;
	load_one_keycode(usb_kbd_keycode, i, 16); i++;
	load_one_keycode(usb_kbd_keycode, i, 19); i++;
	load_one_keycode(usb_kbd_keycode, i, 31); i++;
	load_one_keycode(usb_kbd_keycode, i, 20); i++;
	load_one_keycode(usb_kbd_keycode, i, 22); i++;
	load_one_keycode(usb_kbd_keycode, i, 47); i++;
	load_one_keycode(usb_kbd_keycode, i, 17); i++;
	load_one_keycode(usb_kbd_keycode, i, 45); i++;
	load_one_keycode(usb_kbd_keycode, i, 21); i++;
	load_one_keycode(usb_kbd_keycode, i, 44); i++;
	load_one_keycode(usb_kbd_keycode, i, 2); i++;
	load_one_keycode(usb_kbd_keycode, i, 3); i++;
	load_one_keycode(usb_kbd_keycode, i, 4); i++;
	load_one_keycode(usb_kbd_keycode, i, 5); i++;
	load_one_keycode(usb_kbd_keycode, i, 6); i++;
	load_one_keycode(usb_kbd_keycode, i, 7); i++;
	load_one_keycode(usb_kbd_keycode, i, 8); i++;
	load_one_keycode(usb_kbd_keycode, i, 9); i++;
	load_one_keycode(usb_kbd_keycode, i, 10); i++;
	load_one_keycode(usb_kbd_keycode, i, 11); i++;
	load_one_keycode(usb_kbd_keycode, i, 28); i++;
	load_one_keycode(usb_kbd_keycode, i, 1); i++;
	load_one_keycode(usb_kbd_keycode, i, 14); i++;
	load_one_keycode(usb_kbd_keycode, i, 15); i++;
	load_one_keycode(usb_kbd_keycode, i, 57); i++;
	load_one_keycode(usb_kbd_keycode, i, 12); i++;
	load_one_keycode(usb_kbd_keycode, i, 13); i++;
	load_one_keycode(usb_kbd_keycode, i, 26); i++;
	load_one_keycode(usb_kbd_keycode, i, 27); i++;
	load_one_keycode(usb_kbd_keycode, i, 43); i++;
	load_one_keycode(usb_kbd_keycode, i, 43); i++;
	load_one_keycode(usb_kbd_keycode, i, 39); i++;
	load_one_keycode(usb_kbd_keycode, i, 40); i++;
	load_one_keycode(usb_kbd_keycode, i, 41); i++;
	load_one_keycode(usb_kbd_keycode, i, 51); i++;
	load_one_keycode(usb_kbd_keycode, i, 52); i++;
	load_one_keycode(usb_kbd_keycode, i, 53); i++;
	load_one_keycode(usb_kbd_keycode, i, 58); i++;
	load_one_keycode(usb_kbd_keycode, i, 59); i++;
	load_one_keycode(usb_kbd_keycode, i, 60); i++;
	load_one_keycode(usb_kbd_keycode, i, 61); i++;
	load_one_keycode(usb_kbd_keycode, i, 62); i++;
	load_one_keycode(usb_kbd_keycode, i, 63); i++;
	load_one_keycode(usb_kbd_keycode, i, 64); i++;
	load_one_keycode(usb_kbd_keycode, i, 65); i++;
	load_one_keycode(usb_kbd_keycode, i, 66); i++;
	load_one_keycode(usb_kbd_keycode, i, 67); i++;
	load_one_keycode(usb_kbd_keycode, i, 68); i++;
	load_one_keycode(usb_kbd_keycode, i, 87); i++;
	load_one_keycode(usb_kbd_keycode, i, 88); i++;
	load_one_keycode(usb_kbd_keycode, i, 99); i++;
	load_one_keycode(usb_kbd_keycode, i, 70); i++;
	load_one_keycode(usb_kbd_keycode, i, 119); i++;
	load_one_keycode(usb_kbd_keycode, i, 110); i++;
	load_one_keycode(usb_kbd_keycode, i, 102); i++;
	load_one_keycode(usb_kbd_keycode, i, 104); i++;
	load_one_keycode(usb_kbd_keycode, i, 111); i++;
	load_one_keycode(usb_kbd_keycode, i, 107); i++;
	load_one_keycode(usb_kbd_keycode, i, 109); i++;
	load_one_keycode(usb_kbd_keycode, i, 106); i++;
	load_one_keycode(usb_kbd_keycode, i, 105); i++;
	load_one_keycode(usb_kbd_keycode, i, 108); i++;
	load_one_keycode(usb_kbd_keycode, i, 103); i++;
	load_one_keycode(usb_kbd_keycode, i, 69); i++;
	load_one_keycode(usb_kbd_keycode, i, 98); i++;
	load_one_keycode(usb_kbd_keycode, i, 55); i++;
	load_one_keycode(usb_kbd_keycode, i, 74); i++;
	load_one_keycode(usb_kbd_keycode, i, 78); i++;
	load_one_keycode(usb_kbd_keycode, i, 96); i++;
	load_one_keycode(usb_kbd_keycode, i, 79); i++;
	load_one_keycode(usb_kbd_keycode, i, 80); i++;
	load_one_keycode(usb_kbd_keycode, i, 81); i++;
	load_one_keycode(usb_kbd_keycode, i, 75); i++;
	load_one_keycode(usb_kbd_keycode, i, 76); i++;
	load_one_keycode(usb_kbd_keycode, i, 77); i++;
	load_one_keycode(usb_kbd_keycode, i, 71); i++;
	load_one_keycode(usb_kbd_keycode, i, 72); i++;
	load_one_keycode(usb_kbd_keycode, i, 73); i++;
	load_one_keycode(usb_kbd_keycode, i, 82); i++;
	load_one_keycode(usb_kbd_keycode, i, 83); i++;
	load_one_keycode(usb_kbd_keycode, i, 86); i++;
	load_one_keycode(usb_kbd_keycode, i, 127); i++;
	load_one_keycode(usb_kbd_keycode, i, 116); i++;
	load_one_keycode(usb_kbd_keycode, i, 117); i++;
	load_one_keycode(usb_kbd_keycode, i, 183); i++;
	load_one_keycode(usb_kbd_keycode, i, 184); i++;
	load_one_keycode(usb_kbd_keycode, i, 185); i++;
	load_one_keycode(usb_kbd_keycode, i, 186); i++;
	load_one_keycode(usb_kbd_keycode, i, 187); i++;
	load_one_keycode(usb_kbd_keycode, i, 188); i++;
	load_one_keycode(usb_kbd_keycode, i, 189); i++;
	load_one_keycode(usb_kbd_keycode, i, 190); i++;
	load_one_keycode(usb_kbd_keycode, i, 191); i++;
	load_one_keycode(usb_kbd_keycode, i, 192); i++;
	load_one_keycode(usb_kbd_keycode, i, 193); i++;
	load_one_keycode(usb_kbd_keycode, i, 194); i++;
	load_one_keycode(usb_kbd_keycode, i, 134); i++;
	load_one_keycode(usb_kbd_keycode, i, 138); i++;
	load_one_keycode(usb_kbd_keycode, i, 130); i++;
	load_one_keycode(usb_kbd_keycode, i, 132); i++;
	load_one_keycode(usb_kbd_keycode, i, 128); i++;
	load_one_keycode(usb_kbd_keycode, i, 129); i++;
	load_one_keycode(usb_kbd_keycode, i, 131); i++;
	load_one_keycode(usb_kbd_keycode, i, 137); i++;
	load_one_keycode(usb_kbd_keycode, i, 133); i++;
	load_one_keycode(usb_kbd_keycode, i, 135); i++;
	load_one_keycode(usb_kbd_keycode, i, 136); i++;
	load_one_keycode(usb_kbd_keycode, i, 113); i++;
	load_one_keycode(usb_kbd_keycode, i, 115); i++;
	load_one_keycode(usb_kbd_keycode, i, 114); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 121); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 89); i++;
	load_one_keycode(usb_kbd_keycode, i, 93); i++;
	load_one_keycode(usb_kbd_keycode, i, 124); i++;
	load_one_keycode(usb_kbd_keycode, i, 92); i++;
	load_one_keycode(usb_kbd_keycode, i, 94); i++;
	load_one_keycode(usb_kbd_keycode, i, 95); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 122); i++;
	load_one_keycode(usb_kbd_keycode, i, 123); i++;
	load_one_keycode(usb_kbd_keycode, i, 90); i++;
	load_one_keycode(usb_kbd_keycode, i, 91); i++;
	load_one_keycode(usb_kbd_keycode, i, 85); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 0); i++;
	load_one_keycode(usb_kbd_keycode, i, 29); i++;
	load_one_keycode(usb_kbd_keycode, i, 42); i++;
	load_one_keycode(usb_kbd_keycode, i, 56); i++;
	load_one_keycode(usb_kbd_keycode, i, 125); i++;
	load_one_keycode(usb_kbd_keycode, i, 97); i++;
	load_one_keycode(usb_kbd_keycode, i, 54); i++;
	load_one_keycode(usb_kbd_keycode, i, 100); i++;
	load_one_keycode(usb_kbd_keycode, i, 126); i++;
	load_one_keycode(usb_kbd_keycode, i, 164); i++;
	load_one_keycode(usb_kbd_keycode, i, 166); i++;
	load_one_keycode(usb_kbd_keycode, i, 165); i++;
	load_one_keycode(usb_kbd_keycode, i, 163); i++;
	load_one_keycode(usb_kbd_keycode, i, 161); i++;
	load_one_keycode(usb_kbd_keycode, i, 115); i++;
	load_one_keycode(usb_kbd_keycode, i, 114); i++;
	load_one_keycode(usb_kbd_keycode, i, 113); i++;
	load_one_keycode(usb_kbd_keycode, i, 150); i++;
	load_one_keycode(usb_kbd_keycode, i, 158); i++;
	load_one_keycode(usb_kbd_keycode, i, 159); i++;
	load_one_keycode(usb_kbd_keycode, i, 128); i++;
	load_one_keycode(usb_kbd_keycode, i, 136); i++;
	load_one_keycode(usb_kbd_keycode, i, 177); i++;
	load_one_keycode(usb_kbd_keycode, i, 178); i++;
	load_one_keycode(usb_kbd_keycode, i, 176); i++;
	load_one_keycode(usb_kbd_keycode, i, 142); i++;
	load_one_keycode(usb_kbd_keycode, i, 152); i++;
	load_one_keycode(usb_kbd_keycode, i, 173); i++;
	load_one_keycode(usb_kbd_keycode, i, 140); i++;
}
