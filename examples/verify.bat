..\bin\verifast Composite.c
..\bin\verifast composite4.c
..\bin\verifast -disable_overflow_check counter.c
..\bin\verifast -disable_overflow_check counter_with_pred.c
..\bin\verifast iter.c
..\bin\verifast linkedlist.c
..\bin\verifast linkedlist2.c
..\bin\verifast sorted_bintree.c
..\bin\verifast -c contrib.c
cd chat
..\..\bin\verifast stringBuffers.c sockets.o threading.o lists.o -allow_assume chat.c
cd ..
cd chatbot
..\..\bin\verifast -c bot.c
cd ..
cd incr_box
..\..\bin\verifast -c incr_box.c
cd ..
cd java
..\..\bin\verifast -disable_overflow_check -c Counter.java
..\..\bin\verifast -c Tree.java
..\..\bin\verifast -c Tree2.java
..\..\bin\verifast -c Tree3.java
..\..\bin\verifast -c Iterator.java
cd iterator
..\..\..\bin\verifast -c it.jarsrc
cd ..
cd ..
