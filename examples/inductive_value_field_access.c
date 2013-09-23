/* Consider an inductive data type with only one constructor, like
 *
 *       //@ inductive my_datatype = my_datatype(int some_field, char some_other_field);
 *
 * For instantiations of this type, it is possible to write an expression
 * that reads a field:
 *
 *       my_datavalue->some_field
 *
 * This file demonstrates and tests this feature.
 */


/*@
inductive gender = male | female;

inductive person<t> = person(bool some_bool, gender gender, t value);
predicate person<t>(person<t> person);
@*/

void test_equality()
//@ requires person<int>(?pi) &*& pi->value == 2;
//@ ensures person<int>(pi) &*& pi->value == 2;
{
}

/* useful to test because some approaches to implement
 * inductive value field access crash on this. */
void test_other_type_argument()
//@ requires person<bool>(?pi) &*& pi->value == false;
//@ ensures person<bool>(pi) &*& pi->value == false;
{
}

void test_simple_reasoning()
//@ requires person<int>(?pi) &*& pi->value == 2;
//@ ensures person<int>(pi) &*& pi->value < 3;
{
}

/*@
lemma void test_imperative_assignment()
requires true;
ensures true;
{
	person<int> p1 = person(true, male, 8);
	assert p1->value == 8;
	p1 = person<int>(true, male, 7);
	assert p1->value == 7;
	assert p1->value == 8; //~ should-fail: old value is overwritten.
}
@*/

void test_equality_new_constructor_call()
//@ requires person<int>(?pi) &*& pi->some_bool == true &*& pi->gender == male &*& pi->value == 7;
//@ ensures person<int>(pi) &*& pi == person<int>(true, male, 7);
{
}

void test_equality_new_constructor_call_2()
//@ requires person<int>(?pi) &*& pi == person<int>(true, male, 7);
//@ ensures person<int>(pi) &*& pi->some_bool == true &*& pi->gender == male &*& pi->value == 7;
{
}

/*@
lemma void test_type_parameter_not_instantiated_with_basic_type<t>(t my_t)
requires person<t>(?pi) &*& pi->value == my_t;
ensures person<t>(pi) &*& pi->value == my_t;
{
}
@*/

/*@
// Also useful to test the case when there are no type parameters.
inductive dog = dog(list<char> name, int birthday);
@*/

/*@
lemma void test_multiple_instances(dog dog1, dog dog2)
requires dog1->birthday > 100 &*& dog2 == dog(_, ?birthday_dog2) &*& dog1->birthday > birthday_dog2;
ensures dog1->birthday > dog2->birthday;
{
}
@*/

void test_combine_with_switchexpr()
/*@ requires person<char>(?p1) &*& person<char>(?p2)
	&*& p1->gender != male
	&*& p1->gender == switch(p2){case person(b, gender, t): return gender;};@*/
//@ ensures person(p1) &*& person(p2) &*& p2-> gender != male;
{
}

void test_unprovable()
//@ requires person<int>(?p1) &*& person<int>(?p2) &*& p1->value > 10 &*& p2->value < p1->value;
/*@ ensures person<int>(p1) &*& person<int>(p2) &*&
	p2->value < 10; //~ should-fail: not implied.
@*/
{
}

/*@
inductive pet<t> = pet(person<t> owner, int age);
predicate pet<t>(pet<t> pet);
@*/
void test_field_of_field()
//@ requires pet<int>(?pet) &*& pet->owner->value == 123;
//@ ensures  pet<int>(pet) &*& pet->owner->value == 123;
{
}
