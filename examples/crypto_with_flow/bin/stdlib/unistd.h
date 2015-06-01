#ifndef UNISTD_H
#define UNISTD_H

unsigned int sleep(unsigned int seconds);
/*@ requires seconds >= (unsigned int) 0
    && seconds <= (unsigned int) 4294967295;
  @*/
/*@ ensures result <= seconds;
  @*/

#endif

