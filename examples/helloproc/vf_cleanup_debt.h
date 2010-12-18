#ifndef VF_CLEANUP_DEBT_H
#define VF_CLEANUP_DEBT_H
/*#
 * predicate vf_cleanup_debt
 *
 * Represents the amount of cleanup that is nececerry after creating
 * cleanup debt.  e.g. when creating a callback, this increases the
 * debt, when disposing the callback the debt is decreased again.
 *
 * cleanup_debt can be considered a way to force a free or dispose
 * while disallowing leaking.
 *
 * Hint: the exit prodecure of a kernel module requires a certain debt
 * and ensures a debt of 0.  Write the amount of debt in the
 * module_state predicate (see vf_initexit.h and vf_README.txt), e.g.
 * 
 *   predicate module_state() = ...&*& module_antileak_counter(N) &*&...;
 * 
 * where N is the "amount" of debts you create, i.e. the amount of
 * calls the init procedure makes to functions that create debt,
 * e.g. create a callback.  Do not worry, verification will fail if
 * the number is incorrect.
 */
//@ predicate vf_cleanup_debt(int debtCount);


#endif /* VF_CLEANUP_DEBTH_H */
