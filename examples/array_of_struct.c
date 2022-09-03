#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

struct student {
    char name[100];
    int age;
};

/*@

predicate students(struct student *students, int count;) =
    count == 0 ?
        emp
    :
        students->name[..100] |-> ?cs &*& mem('\0', cs) == true &*& students->age |-> _ &*&
        struct_student_padding(students) &*&
        students(students + 1, count - 1);

@*/

struct student *read_students(int *count)
    //@ requires *count |-> _;
    //@ ensures *count |-> ?nb &*& students(result, nb) &*& malloc_block_chars((void *)result, nb * sizeof(struct student));
{
    printf("How many students?\n");
    scanf(" %d", count);
    //@ integer_limits(count);
    //@ assert *count |-> ?nb;
    if (*count < 0 || SIZE_MAX / sizeof(struct student) < (size_t)*count) abort();
    //@ div_rem_nonneg(SIZE_MAX, sizeof(struct student));
    //@ mul_mono_l(0, *count, sizeof(struct student));
    //@ mul_mono_l(*count, SIZE_MAX / sizeof(struct student), sizeof(struct student));
    struct student *result = malloc(*count * sizeof(struct student));
    if (result == 0) abort();
    for (int i = 0; i < *count; i++)
        //@ requires *count |-> nb &*& i <= nb &*& chars_((void *)(result + i), (nb - i) * sizeof(struct student), _);
        //@ ensures *count |-> nb &*& students(result + old_i, nb - old_i);
    {
        //@ mul_mono_l(1, nb - i, sizeof(struct student));
        //@ chars__split((void *)(result + i), sizeof(struct student));
        //@ close_struct(result + i);
        printf("Please enter the name of student %d:\n", i);
        if (scanf(" %99s", &result[i].name) != 1) abort();
        printf("Please enter the age of student %d:\n", i);
        scanf(" %d", &result[i].age);
    }
    return result;
}

struct point {
    int x;
    int y;
};

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    if (SIZE_MAX / 2 < sizeof(struct point)) abort();
    //@ div_rem_nonneg(SIZE_MAX, 2);
    struct point *points = malloc(2 * sizeof(struct point));
    if (points == 0) abort();
    //@ chars__split((void *)points, sizeof(struct point));
    //@ close_struct(points);
    //@ close_struct(points + 1);
    points[0].x = 10;
    points[0].y = 20;
    points[1].x = 30;
    points[1].y = 40;
    //@ open_struct(points);
    //@ open_struct(points + 1);
    //@ chars__join((void *)points);
    free((void *)points); 
    return 0;
}