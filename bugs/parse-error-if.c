struct x
{
    struct x *next;
};

void foo(struct x *y)
{
	if(y->next != y)
	{
		y->next = y;
	}
}