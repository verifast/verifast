#ifndef QUEUES_H
#define QUEUES_H

struct queue;

/*@
predicate queue(struct queue *q, int size);
@*/

struct queue* create_queue();
    //@ requires true;
    //@ ensures queue(result,0);

void dispose_queue(struct queue* queue);
    //@ requires queue(queue,_);
    //@ ensures true;

int size_of(struct queue *q);
    //@ requires queue(q,?s);
    //@ ensures queue(q,s) &*& result == s;

int dequeue(struct queue *q);
    //@ requires queue(q,?s) &*& s >= 1;
    //@ ensures queue(q,s-1);

void enqueue(struct queue *q,int x);
    //@ requires queue(q,?s);
    //@ ensures queue(q,s+1);

#endif