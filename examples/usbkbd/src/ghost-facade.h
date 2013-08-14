#ifndef __GHOST_FACADE_H
#define __GHOST_FACADE_H
#include <linux/slab_def.h>
//@ #include "ghost-fields.gh"

//########################################################################//
//##                                                                    ##//
//##                            PUBLIC API                              ##//
//##                                                                    ##//
//########################################################################//
/*@


// --- Predicates --- //

predicate usbkbd_killcount(struct usb_kbd *kbd; int count) =
	ghost_field(
		usb_kbd_unique_pred,
		usbkbd_killcount_args(kbd),
		count
	)
;

// Always unknown value. But proveable to have a minimum value.
predicate usbkbd_cb_out_count(struct usb_kbd *kbd; int count) =
	countdiff(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd), count)
	&*& count >= 0
;

// Always known value.
predicate usbkbd_cb_out_known_count(struct usb_kbd *kbd, int count;) =
	ghost_field(
		usb_kbd_unique_pred,
		usbkbd_cb_out_known_args(kbd),
		count
	)
;

predicate times_diffcount_ticket(struct usb_kbd *kbd, int times) =
	countdiff_tickets(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd), times)
;

predicate usbkbd_cb_out_ticket(struct usb_kbd *kbd;) =
	countdiff_ticket(usb_kbd_unique_pred, usbkbd_cb_out_args(kbd))
;



// --- cb out operations ---- //

lemma void usbkbd_cb_out_inc(struct usb_kbd *kbd)
	requires usbkbd_cb_out_count(kbd, ?count);// &*& usbkbd_cb_out_known_count(kbd, ?known_count);
	
	// usbkbd_cb_out_known_count(kbd, known_count+1) &*& 
	ensures usbkbd_cb_out_count(kbd, count+1) &*& usbkbd_cb_out_ticket(kbd) &*& count >= 0;
{
	open usbkbd_cb_out_count(kbd, count); // no auto-open? XXX
	inc_countdiff(
		usb_kbd_unique_pred,
		usbkbd_cb_out_args(kbd)
	);
	//write_ghost_field(usb_kbd_unique_pred, usbkbd_cb_out_known_args(kbd), known_count, known_count+1);
}

lemma void usbkbd_cb_out_dec(struct usb_kbd *kbd)
	// usbkbd_cb_out_known_count(kbd, ?known_count) &*& 
	requires usbkbd_cb_out_count(kbd, ?count) &*& usbkbd_cb_out_ticket(kbd);
	// usbkbd_cb_out_known_count(kbd, known_count-1) &*&
	ensures usbkbd_cb_out_count(kbd, count-1) &*&  count-1 >= 0;
{
	open usbkbd_cb_out_count(kbd, count); // no auto-open? XXX
	dec_countdiff(
		usb_kbd_unique_pred,
		usbkbd_cb_out_args(kbd)
	);
	//write_ghost_field(usb_kbd_unique_pred, usbkbd_cb_out_known_args(kbd), known_count, known_count-1);
}



// --- ghost field operations ---- //

lemma void usbkbd_killcount_write(struct usb_kbd *kbd, int old_count, int new_count)
	requires usbkbd_killcount(kbd, old_count);
	ensures usbkbd_killcount(kbd, new_count);
{
	write_ghost_field(usb_kbd_unique_pred, usbkbd_killcount_args(kbd), new_count);
}



// --- Create/dispose --- //


lemma void create_ghost_stuff(void *kbd);
	requires kmalloc_block(kbd, sizeof(struct usb_kbd));
	ensures
		usbkbd_killcount(kbd, 0)
		&*& usbkbd_cb_out_count(kbd, 0)
	;
	// implemented below.


lemma void dispose_ghost_stuff(struct usb_kbd *kbd);
	requires 			
		usbkbd_killcount(kbd, 0)
		&*& usbkbd_cb_out_count(kbd, 0)
	;
	ensures kmalloc_block(kbd, sizeof(struct usb_kbd));
	// implemented below.



@*/


//########################################################################//
//##                                                                    ##//
//##                          IMPLEMENTATION                            ##//
//##                                                                    ##//
//########################################################################//

struct usb_kbd;


/*@
inductive kmalloc_args = kmalloc_args(void *, int);
fixpoint void* kmalloc_addr(kmalloc_args args){
	switch (args) {
		case kmalloc_args(a, i): return a;
	}
}
fixpoint int kmalloc_size(kmalloc_args args){
	switch (args) {
		case kmalloc_args(a, i): return i;
	}
}

predicate kmalloc_block_onearg(kmalloc_args args;) = 
	kmalloc_block(kmalloc_addr(args), kmalloc_size(args));


lemma void lemma_kmalloc_block_unique_onearg(kmalloc_args args) //: pred_unique
	requires kmalloc_block_onearg(args) &*& kmalloc_block_onearg(args) &*& kmalloc_size(args) != 0;
	ensures false;
{
	open kmalloc_block_onearg(args);
	open kmalloc_block_onearg(args);
	kmalloc_block_unique(kmalloc_addr(args), kmalloc_size(args));
}

fixpoint bool kmalloc_size_nonzero(kmalloc_args args){
	return kmalloc_size(args) != 0;
}


fixpoint bool always_true<T>(T t){return true;}

// wrapper to get rid of generics such that we can pass this predicate as parameter.
predicate usb_kbd_unique_pred(pair<pair<kmalloc_args, predicate(kmalloc_args)>,int> args;) = uniq_child(args);


lemma void uniq_uniqueness_proof_kmalloc(pair<pair<kmalloc_args, predicate(kmalloc_args)>,int> args)
	requires usb_kbd_unique_pred(args) &*& usb_kbd_unique_pred(args);
	ensures false;
{
	//open uniq_child_kmalloc(args); // auto-open works ^.^
	//open uniq_child_kmalloc(args);
	uniq_uniqueness_proof(args);
}
@*/

// so sad... XXX
//inductive usbkbd_unique_pred_args_type = pair<pair<kmalloc_args, predicate(kmalloc_args)>,int>;


/*@

fixpoint pair<pair<kmalloc_args, predicate(kmalloc_args)>,int> usbkbd_ghoststuff_args(struct usb_kbd *kbd, int nb){
	return pair(
		pair(
			kmalloc_args(kbd, sizeof(struct usb_kbd)),
			kmalloc_block_onearg
		),
		nb
	);
}


fixpoint pair<pair<kmalloc_args, predicate(kmalloc_args)>,int> usbkbd_killcount_args(struct usb_kbd *kbd){
	return usbkbd_ghoststuff_args(kbd, 1);
}

fixpoint pair<pair<kmalloc_args, predicate(kmalloc_args)>,int> usbkbd_cb_out_args(struct usb_kbd *kbd){
	return usbkbd_ghoststuff_args(kbd, 2);
}

fixpoint pair<pair<kmalloc_args, predicate(kmalloc_args)>,int> usbkbd_cb_out_known_args(struct usb_kbd *kbd){
	return usbkbd_ghoststuff_args(kbd, 3);
}



// public api lemma impl
lemma void create_ghost_stuff(void *kbd)
	requires kmalloc_block(kbd, sizeof(struct usb_kbd));
	ensures
		usbkbd_killcount(kbd, 0)
		&*& usbkbd_cb_out_count(kbd, 0)
	;
		
{
	// --- split unique preds --- //
		produce_lemma_function_pointer_chunk(lemma_kmalloc_block_unique_onearg)
			: pred_unique<kmalloc_args>(kmalloc_block_onearg, kmalloc_size_nonzero)(args)
		{
			call(); // as in: (prepare precondition of callee) ; call ; (prepare postcondition of myself) ?
		}{
			assert is_pred_unique(lemma_kmalloc_block_unique_onearg, kmalloc_block_onearg, kmalloc_size_nonzero);
			
			close kmalloc_block_onearg(kmalloc_args(kbd, sizeof(struct usb_kbd)));
			uniq_produce(kmalloc_block_onearg, kmalloc_args(kbd, sizeof(struct usb_kbd)), 2,  kmalloc_size_nonzero, lemma_kmalloc_block_unique_onearg);
		}
		
		assert uniq_children(kmalloc_block_onearg, kmalloc_args(kbd, sizeof(struct usb_kbd)), 2, 1);
		open uniq_children(kmalloc_block_onearg, kmalloc_args(kbd, sizeof(struct usb_kbd)), 2, 1);
		open uniq_children(kmalloc_block_onearg, kmalloc_args(kbd, sizeof(struct usb_kbd)), 2, 2);
		//open uniq_children(kmalloc_block_onearg, kmalloc_args(kbd, sizeof(struct usb_kbd)), 3, 3);
		
		close usb_kbd_unique_pred(usbkbd_killcount_args(kbd));
		close usb_kbd_unique_pred(usbkbd_cb_out_args(kbd));
		//close usb_kbd_unique_pred(usbkbd_cb_out_known_args(kbd));
		
	// end.
	
	// --- create all ghost fields ---- //
		produce_lemma_function_pointer_chunk(uniq_uniqueness_proof_kmalloc)
		: pred_unique<
			pair<
				pair<
					kmalloc_args,
					predicate(kmalloc_args)
				>,
				int
			>
		>(usb_kbd_unique_pred, always_true)(args){
			call();
		}
		{
			create_ghost_field(
				usb_kbd_unique_pred,
				always_true,
				usbkbd_killcount_args(kbd),
				0, // ghost field value
				uniq_uniqueness_proof_kmalloc
			);
			/*
			create_ghost_field(
				usb_kbd_unique_pred,
				always_true,
				usbkbd_cb_out_known_args(kbd),
				0, // ghost field value
				uniq_uniqueness_proof_kmalloc
			);*/
			
		}
	// end.
	
	// ---- Create diffcounter ----- //
		produce_lemma_function_pointer_chunk(uniq_uniqueness_proof_kmalloc)
			: pred_unique<
				pair<
					pair<
						kmalloc_args,
						predicate(kmalloc_args)
					>,
					int
				>
			>(usb_kbd_unique_pred, always_true)(args){

				call();
		}{
			 start_countdiff(
				usb_kbd_unique_pred,
				always_true,
				usbkbd_cb_out_args(kbd),
				uniq_uniqueness_proof_kmalloc
			);
		}
	// end.
	
	close usbkbd_cb_out_count(kbd, ?unknown_init_value);
}
			
// public api lemma impl
lemma void dispose_ghost_stuff(struct usb_kbd *kbd)
	requires 			
		usbkbd_killcount(kbd, 0)
		&*& usbkbd_cb_out_count(kbd, 0)
	;

	ensures kmalloc_block(kbd, sizeof(struct usb_kbd));
{
	
	// no auto-open? XXX
	open usbkbd_cb_out_count(kbd, 0);
	
	stop_countdiff(
		usb_kbd_unique_pred,
		usbkbd_cb_out_args(kbd)
	);
	
	dispose_ghost_field(
		usb_kbd_unique_pred,
		usbkbd_killcount_args(kbd)
	);
	
	/*dispose_ghost_field(
		usb_kbd_unique_pred,
		usbkbd_cb_out_known_args(kbd),
		0
	);*/

	// no autoclose of inductive preds? XXX
	//close uniq_children(kmalloc_block_onearg, kmalloc_args(kbd, sizeof(struct usb_kbd)), 3, 3);
	close uniq_children(kmalloc_block_onearg, kmalloc_args(kbd, sizeof(struct usb_kbd)), 2, 2);

	uniq_destroy(kmalloc_block_onearg, kmalloc_args(kbd, sizeof(struct usb_kbd)), 2);
}
@*/


#endif