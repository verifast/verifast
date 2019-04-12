#ifndef UNISTD_H
#define UNISTD_H

unsigned int sleep(unsigned int seconds);
/*@ requires seconds >= (unsigned int) 0
    && seconds <= UINT_MAX;
  @*/
/*@ ensures result <= seconds;
  @*/

#endif

