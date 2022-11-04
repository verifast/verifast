#ifndef _LINUX_INPUT_H
#define _LINUX_INPUT_H

#include <linux/stddef.h> // for not_in_interrupt_context predicate
#include <linux/types.h>
#include <linux/device.h>

// "Calls to both callbacks [open, close] are serialized." -- input-programming.txt
// Calls to event are serialized ("The call [to @event] is protected by @event_lock and must not sleep" -- input.h)

// We assume that unregistering an input devices (by input_unregister_device) causes the close callback to
// be called if device is opened. This is undocumented in Linux but seems to be common accepted
// and has been tested empirically.
// Calling input_unregister_device calls the disconnect function of all input handlers (an input
// handler is a piece of software in kernelspace that reads the events from the driver and distributes
// them further to both kernelspace and userspace, i.e. it's the
// one that will call input_open_device (multiple such calls only results in one open call of the driver,
// the input layer takes care of that)). When the disconnect function of the input handler is called,
// the input handler will close the input device if it has opened it, and if all input handlers have closed
// the input device, the close callback of the device driver will be called. This of course is
// only true if the assumption that all input handlers properly call input_close_device, which is
// also undocumented, but we have to fill in the blank parts of the undocumented parts if we want
// to write specifications. If we do this too strict ("everything undocumented cannot be made any assumptions")
// then you cannot verify any driver because there are too many undocumented parts that people seem
// to rely on.

typedef int input_open_t_no_pointer (struct input_dev *dev);
	/*@ requires userdef_input_drvdata(this, ?close_cb, ?event_cb)(dev, false, ?data, ?fracsize)
		&*& input_open_callback_link(this)(close_cb, event_cb)
		&*& [1/2]input_dev_reportable(dev, data)
		&*& not_in_interrupt_context(currentThread); // empirically tested with in_interrupt()
	@*/
	/*@ ensures
		not_in_interrupt_context(currentThread)
		&*& input_open_callback_link(this)(close_cb, event_cb)
		&*& result == 0 ? // success
			userdef_input_drvdata(this, close_cb, event_cb)(dev, true, data, fracsize)
		: // failure
			userdef_input_drvdata(this, close_cb, event_cb)(dev, false, data, fracsize)
			&*& [1/2]input_dev_reportable(dev, data)
		;
	@*/
typedef input_open_t_no_pointer* input_open_t;
//@ predicate input_open_t_ghost_param(input_open_t_no_pointer *cb1, input_open_t cb2) = is_input_open_t_no_pointer(cb1) == true &*& cb1 == cb2;


typedef void input_close_t_no_pointer (struct input_dev *dev);
	/*@ requires userdef_input_drvdata(?open_cb, this, ?event_cb)(dev, true, ?data, ?fracsize) &*& not_in_interrupt_context(currentThread)
		&*& input_close_callback_link(this)(open_cb, event_cb);
	@*/
	/*@ ensures  userdef_input_drvdata(open_cb, this, event_cb)(dev, false, data, fracsize)
		&*& input_close_callback_link(this)(open_cb, event_cb)
		&*& [1/2]input_dev_reportable(dev, data)
		&*& not_in_interrupt_context(currentThread); // empirically confirmed with in_interrupt()
	@*/
typedef input_close_t_no_pointer* input_close_t;
//@ predicate input_close_t_ghost_param(input_close_t_no_pointer *cb1, input_close_t cb2) = is_input_close_t_no_pointer(cb1) == true &*& cb1 == cb2;


// event callback is, according to input.h's documentation for struct input_dev, locked by a lock called event_lock.
// This is the case: the event_callback is called by input_pass_event,
// which is called by input_handle_event (called by input_event (which locks event_lock), and input_inject_event (which locks)),
// input_repeat_key (which locks), input_disconnect_device (which locks), and input_set_keycode (which locks).
// So the event callback gets the event_lock.
// The input_dev->led fields is written by input_handle_event.
// So it is safe to read input_dev->led non-atomicly.
// This callback "must not sleep" (source: input.h). Empirically confirmed with in_interrupt().
typedef int input_event_t_no_pointer (struct input_dev *dev, unsigned int type, unsigned int code, int value);
	// XXX you can't have events on non-opened input devices I guess? Should double-check.
	/*@ requires userdef_input_drvdata(?open_cb, ?close_cb, this)(dev, true, ?data, ?fracsize)
		&*& input_event_callback_link(this)(open_cb, close_cb)
		&*& [?f]dev->led |-> ?led // fraction, I don't want to check if you're supposed to write.
		&*& [f]uints(led, 1, _);
	@*/
	/*@ ensures userdef_input_drvdata(open_cb, close_cb, this)(dev, true, data, fracsize)
		&*& input_event_callback_link(this)(open_cb, close_cb)
		&*& [f]dev->led |-> led
		&*& [f]uints(led, 1, _);
	@*/
typedef input_event_t_no_pointer* input_event_t;
//@ predicate input_event_t_ghost_param(input_event_t_no_pointer *cb1, input_event_t cb2) = is_input_event_t_no_pointer(cb1) == true &*& cb1 == cb2;


struct input_id {
	__u16 bustype;
	__u16 vendor;
	__u16 product;
	__u16 version;
};

struct input_dev {
	char *name; //"The dev->name should be set before registering the input device by the input device driver" -- input-programming.txt
	char* phys; // Should this be initialized by the driver or can it remain equal to 0? We currently assume the latter.
	struct input_id id;
	
	input_open_t open;
	input_close_t close;
	input_event_t event;
	
	// On 32bit and Linux 3.0.4, the size of the evbits array is:
	// BITS_TO_LONGS(EV_CNT)
	// -> DIV_ROUND_UP(EV_CNT, BITS_PER_BYTE * sizeof(long))
	// -> DIV_ROUND_UP(EV_CNT, 8 * 4)
	// -> DIV_ROUND_UP(0x1f+1, 8*4)
	// -> round_up(1)
	// -> 1.
	
	// We actually can't put unsigned longs, or even longs, here,
	// because VeriFast doesn't completely support it yet (no unsigned_long predicate).

	//unsigned long evbit[BITS_TO_LONGS(EV_CNT)]; // EV_CNT=0x1f+1 (linux 3.0.4) -> 1 longs.
	//unsigned long ledbit[BITS_TO_LONGS(LED_CNT)]; // LED_CNT=0x0f+1 (linux 3.0.4) -> 1 longs.
	//unsigned long keybit[BITS_TO_LONGS(KEY_CNT)]; // KEY_CNT=0x2ff+1 (linux 3.0.4) -> 24 longs.

	int *evbit;
	int *ledbit;
	int *keybit;
	
	//unsigned long led[BITS_TO_LONGS(LED_CNT)];
	unsigned int *led;
	
	// XXX I guess you can't just leave the above values to anything you like / garbage. This might have to be enforced in verification.
	struct device dev;
};

/*@
	// Predicate te make to enforce obtaining input_dev_unregistered via the API,
	// and setting userdata via the API.
	predicate input_dev_unregistered_private(struct input_dev *input_dev, void *userdata);

	predicate input_dev_unregistered(struct input_dev *input_dev, char *name,  char *phys, input_open_t open_callback, input_close_t close_cb, input_event_t event_cb, void *userdata) =
		input_dev_open(input_dev, open_callback) // "input_dev->open" conflicts with parsing of open ghost statement I guess.
		&*& input_dev_close(input_dev, close_cb)
		&*& input_dev->event |-> event_cb
		&*& input_dev->name |-> name
		&*& input_dev->phys |-> phys
		&*& input_dev->id.bustype |-> _
		&*& input_id_vendor(&input_dev->id, _)
		&*& input_id_product(&input_dev->id, _)
		&*& input_id_version(&input_dev->id, _)
		&*& input_dev_unregistered_private(input_dev, userdata)
		
		&*& input_dev->evbit |-> ?evbit
		&*& input_dev->ledbit |-> ?ledbit
		&*& input_dev->keybit |-> ?keybit
		&*& ints(evbit, 1, _)
		&*& ints(ledbit, 1, _)
		&*& ints(keybit, 24, _)
		
		&*& input_dev->led |-> ?led
		&*& uints(led, 1, _)
	;
	
	// fracsize for getting the correct fracsize userdef_input_drvdata back when destroying an input_dev.
	predicate input_dev_registered(struct input_dev *input_dev, char *name, int name_length, real name_frac, char *phys, int phys_length, real phys_frac, input_open_t open_callback, input_close_t close_cb, input_event_t event_cb, void *userdata, real fracsize);
	
	// To be defined by the user.
	// The callback-arguments can be used to make it possible to
	// have different data for different kind of devices,
	// this should probably be replaced by some kind of predicate_family XXX
	// is_opened allows the open callback to give some permissions to some other thread,
	// while giving some stuff to the close callback, which can then to the inverse.
	// The fracsize argument is for embedding predicates of _unknown_ fraction but where
	// the fraction must be known when reopening userdef_input_drvdata. This is ugly XXX.
	predicate_family userdef_input_drvdata
	(
		input_open_t *open_cb,
		input_close_t *close_cb,
		input_event_t *event_cb
	)(
		struct input_dev *input_dev, bool is_opened, void *data, real fracsize	
	);
	
	/**
	 * When a callback implementation tries to open the userdef_input_drvdata(this, ?close, ?event), it cannot
	 * do so if it can't prove that close and event equal the callbacks for which the predicaty family instance
	 * of userdef_input_drvdata is defined. To help such a callback implementation annotation to prove this,
	 * input_open_callback_link is passed, which is supposed to just contain constraints on what the
	 * other callbacks are. This predicate family instance is also "given back" to prevent unwanted leaking.
	 */
	
	predicate_family input_open_callback_link(input_open_t open_cb)(input_close_t close_cb, input_event_t event_t);
	predicate_family input_close_callback_link(input_close_t close_cb)(input_open_t open_cb, input_event_t event_t);
	predicate_family input_event_callback_link(input_event_t event_t)(input_open_t open_cb, input_close_t close_cb);
	
	
	// Permission to report key presses/releases to this device.
	// Do not self-define this predicate.
	// Constraints:
	// * _open must somehow access it, so _register must somehow eat/consume it
	// * outside _open it must be accessible to
	// * after unregistering, all fractions must be gone.
	// Note that it doesn't work if it we just let the user put it in userdata for not-opened-yet devices.
	// So we let register eat half a fraction, open get the fraction
	// (whether the user wants it or not, he can put it in opened-yet device userdata
	// if he wants to get rid of it), and destroy/unregister _not_ give that fraction back, but eat the fraction
	// that was left for use outside _open.
	// Note that once this predicate is produced, you can't change fields anymore (name, userdata, ...)
	// (according to our specs; input's original intention might be less strict).
	predicate input_dev_reportable(struct input_dev *input_dev, void *userdata;);
@*/

struct input_dev *input_allocate_device(void);
	//@ requires not_in_interrupt_context(currentThread); // implementation calls kzalloc with only GFP_KERNEL flag.
	/*@ ensures
		not_in_interrupt_context(currentThread)
		
		&*& result != 0 ?
			// You can already report keys before registering the device.
			input_dev_reportable(result,  0)
			
			&*& input_dev_unregistered(result, 0, 0, _, _, _, 0)
		:
			true
		;
		   @*/
	
void input_free_device(struct input_dev *dev);
	/*@ requires
		not_in_interrupt_context(currentThread) // see input_allocate_device
		&*& dev != 0 ?
			input_dev_unregistered(dev, ?name, ?phys, ?open_cb, ?close_cb, ?event_cb, ?userdata)
			&*& input_dev_reportable(dev, userdata)
		:
			true // no-op.
		;
	@*/
	//@ ensures not_in_interrupt_context(currentThread);



/**
 * 
 * Suppose, on registering a device, you would have to pass the userdef_input_drvdata.
 * If registering fails, you then would have to pass the data and then get it back.
 * But on failure this data is never used. And it can make verification hard, because
 * opening and closing an unprecise predicate might "loose data".
 * So you actually know nothing happened with the userdef-data on failure, but if it would
 * be passed to input_register_device, you would lose this statically-known info.
 * So we first register in ghostcode and then in C-code. Ghost-code already tells
 * you whether it will fail (but of course it is undefined what it will be, but you can
 * then case-split on it before the actual c-call to input_register_device).
 * Only if the ghost-register succeeds, you have to pass the userdata
 * to the c-register. Of course, you can't ghost-register twice.
 * In case of failure and retry, you will also have to "ghost-retry" of course.
 */
/*@
// fracsize is here only because we can't pass it with userdef_input_drvdata if this predicate is only consumed conditionally.
predicate input_dev_ghost_registered(struct input_dev *input_dev, char* name, char* phys, input_open_t open_cb, input_close_t close_cb, input_event_t event_cb, void *userdata, real fracsize, int return_value);
lemma int input_ghost_register_device(struct input_dev *dev, real fracsize);
	requires input_dev_unregistered(dev, ?name, ?phys, ?open_cb, ?close_cb, ?event_cb, ?userdata);
	ensures input_dev_ghost_registered(dev, name, phys, open_cb, close_cb, event_cb, userdata, fracsize, result);

predicate maybe_chars(real f, char* p, int length, list<char> data;) =
  p == 0 ?
    true
  :
    [f]chars(p, length, data); 
@*/

int input_register_device(struct input_dev *dev);
	/*@ requires input_dev_ghost_registered(dev, ?name, ?phys, ?open_cb, ?close_cb, ?event_cb, ?userdata, ?fracsize, ?ghost_result)
		&*& input_open_t_ghost_param(open_cb, open_cb)
		&*& input_close_t_ghost_param(close_cb, close_cb)
		&*& input_event_t_ghost_param(event_cb, event_cb)
		&*& input_open_callback_link(open_cb)(close_cb, event_cb)
		&*& input_close_callback_link(close_cb)(open_cb, event_cb)
		&*& input_event_callback_link(event_cb)(open_cb, close_cb)
		&*& [?f]chars(name, ?name_length, ?cs) &*& mem('\0', cs) == true
		&*& maybe_chars(?f2, phys, ?phys_length, ?cs2) &*& phys == 0 || mem('\0', cs2) == true
		
		&*& [1/2]input_dev_reportable(dev, userdata) // why [1/2]? See comments at predicate.
		
		// "input_register_device() may sleep" -- input-programming.txt
		&*& not_in_interrupt_context(currentThread)
		
		&*& ghost_result == 0 ?
			userdef_input_drvdata(open_cb, close_cb, event_cb)(dev, false, userdata, fracsize)
		: true
		;
	@*/
	/*@ ensures
		not_in_interrupt_context(currentThread)
		&*& result == ghost_result
		&*& result == 0 ? // success
			input_dev_registered(dev, name, name_length, f, phys, phys_length, f2, open_cb, close_cb, event_cb, userdata, fracsize)
		: // failure
			// give _unregistered and not _ghost_registered to enforce re-ghost-registering
			// on re-c-registering.
			input_dev_unregistered(dev, name, phys, open_cb, close_cb, event_cb, userdata)
			&*& input_open_t_ghost_param(open_cb, open_cb)
			&*& input_close_t_ghost_param(close_cb, close_cb)
			&*& input_event_t_ghost_param(event_cb, event_cb)
			&*& input_open_callback_link(open_cb)(close_cb, event_cb)
			&*& input_close_callback_link(close_cb)(open_cb, event_cb)
			&*& input_event_callback_link(event_cb)(open_cb, close_cb)
			&*& [f]chars(name, name_length, cs)
			&*& maybe_chars(f2, phys, phys_length, cs2)
			
			// Not consumed on failure, so also not given back. See input_dev_ghost_registered
			//&*& userdef_input_drvdata(dev, false, open_cb, close_cb, event_cb, userdata, fracsize)
			
			&*& [1/2]input_dev_reportable(dev, userdata)
		;
	@*/

// we assume disconnect causes _close to be called (see top of this file).
void input_unregister_device(struct input_dev *dev);
	/*@ requires
		input_dev_registered(dev, ?name, ?name_length, ?name_frac, ?phys, ?phys_length, ?phys_frac, ?open_cb, ?close_cb, ?event_cb, ?userdata, ?fracsize)
		
		// After unregistration, you can't do anything with the device anymore
		// even not freeing or reporting events (source: input's sourcecode specs).
		&*& [1/2]input_dev_reportable(dev, userdata);
	
	@*/
	/*@ ensures
		userdef_input_drvdata(open_cb, close_cb, event_cb)(dev, false, userdata, fracsize)
		&*& input_open_callback_link(open_cb)(close_cb, event_cb)
		&*& input_close_callback_link(close_cb)(open_cb, event_cb)
		&*& input_event_callback_link(event_cb)(open_cb, close_cb)
		&*& [name_frac]chars(name, name_length, _)
		&*& maybe_chars(phys_frac, phys, phys_length, _);
	@*/

void input_set_drvdata(struct input_dev *dev, void *data);
	/*@ requires
		input_dev_unregistered(dev, ?name, ?phys, ?open_cb, ?close_cb, ?event_cb, ?original_userdata)
		&*& input_dev_reportable(dev, original_userdata);
	@*/
	/*@ ensures
		input_dev_unregistered(dev, name, phys, open_cb, close_cb, event_cb, data)
		&*& input_dev_reportable(dev, data);
	
	@*/

// XXX should check whether this is synchronized (against e.g. unregister)
void *input_get_drvdata(struct input_dev *dev);
	//@ requires [?f]input_dev_reportable(dev, ?userdata);
	//@ ensures [f]input_dev_reportable(dev, userdata) &*& result == userdata;


// Can actually be called on an unregistered device that is not registered yet (according input_event's specs).
// But input_unregister_device's specs state that after unregistering a device, it should not be
// accessed anymore. So "unregistered"-state has substates "not-ever-registered-yet" and "already-registered-at-least-once"...
void input_report_key(struct input_dev *dev, /*unsigned*/ int code, int value);
	//@ requires [?f]input_dev_reportable(dev, ?userdata); // XXX hm I thought they synchronize but I should recheck this.
	//@ ensures [f]input_dev_reportable(dev, userdata);

static inline void input_report_rel(struct input_dev *dev, unsigned int code, int value);
	//@ requires [?f]input_dev_reportable(dev, ?userdata); // XXX hm I thought they synchronize but I should recheck this.
	//@ ensures [f]input_dev_reportable(dev, userdata);

void input_sync(struct input_dev *dev);
	//@ requires [?f]input_dev_reportable(dev, ?userdata); // XXX hm I thought they synchronize but I should recheck this.
	//@ ensures [f]input_dev_reportable(dev, userdata);


// Event types:
#define	EV_SYN                 0x00
#define	EV_KEY                 0x01
#define	EV_REL                 0x02
#define	EV_ABS                 0x03
#define	EV_MSC                 0x04
#define	EV_SW                  0x05
#define	EV_LED                 0x11
#define	EV_SND                 0x12
#define	EV_REP                 0x14
#define	EV_FF                  0x15
#define	EV_PWR                 0x16
#define	EV_FF_STATUS           0x17
#define	EV_MAX                 0x1f
// #define	EV_CNT		       0x20/* original: (EV_MAX+1)*/


// LEDs:
#define	LED_NUML                0x00
#define	LED_CAPSL               0x01
#define	LED_SCROLLL             0x02
#define	LED_COMPOSE             0x03
#define	LED_KANA                0x04
#define	LED_SLEEP               0x05
#define	LED_SUSPEND             0x06
#define	LED_MUTE                0x07
#define	LED_MISC                0x08
#define	LED_MAIL                0x09
#define	LED_CHARGING            0x0a
#define	LED_MAX                 0x0f
// #define	LED_CNT                 0x10 /* original: (LED_MAX+1)*/


// this should be moved to uapi/linux/input.h
#define BTN_MOUSE		0x110
#define BTN_LEFT		0x110
#define BTN_RIGHT		0x111
#define BTN_MIDDLE		0x112
#define BTN_SIDE		0x113
#define BTN_EXTRA		0x114
#define BTN_FORWARD		0x115
#define BTN_BACK		0x116
#define BTN_TASK		0x117

/*
 * Relative axes
 */

#define REL_X			0x00
#define REL_Y			0x01
#define REL_Z			0x02
#define REL_RX			0x03
#define REL_RY			0x04
#define REL_RZ			0x05
#define REL_HWHEEL		0x06
#define REL_DIAL		0x07
#define REL_WHEEL		0x08
#define REL_MISC		0x09
#define REL_MAX			0x0f
//#define REL_CNT			(REL_MAX+1) // crashes VERIFAST

#endif
