#ifndef QUEUES_H
#define QUEUES_H

struct queue;
typedef struct queue *queue;

//@ predicate queue(struct queue *q, list<void *> values);

struct queue *create_queue();
    //@ requires true;
    //@ ensures queue(result, nil);
    //@ terminates;

void enqueue(struct queue *q, void *x);
    //@ requires queue(q, ?vs);
    //@ ensures queue(q, append(vs, {x}));
    //@ terminates;

void *dequeue(struct queue *q);
    //@ requires queue(q, cons(?v, ?vs));
    //@ ensures queue(q, vs) &*& result == v;
    //@ terminates;

void queue_dispose(struct queue *q);
    //@ requires queue(q, _);
    //@ ensures true;
    //@ terminates;
