#ifndef _LINUX_STDDEF_H
#define _LINUX_STDDEF_H

#define NULL 0

// stddef.h might be the wrong place for this predicate.
// This predicate states that the current thread, which is threadId, is not
// running in interrupt context. This predicate is used as precondition of
// callbacks that are not allowed to be executed in interrupt context, i.e.
// that require in_interrupt() te return false.
// The threadId argument makes sure this predicate is not secretly passed
// to some other thread which then abuses it.
//@ predicate not_in_interrupt_context(int threadId);

#endif
