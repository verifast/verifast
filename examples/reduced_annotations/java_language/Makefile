all: verify run

verify:
	mysh < verify.mysh

compile:
	javac PartiallyAnnotatedInterface2.java PartiallyAnnotated2.java; \
	jar cvf submodule2.jar PartiallyAnnotatedInterface2.class PartiallyAnnotated2.class; \
	rm -f *.class; \
	javac -cp submodule2.jar PartiallyAnnotatedInterface1.java PartiallyAnnotated1.java Main.java; \

run: compile 
	java -cp submodule2.jar:. Main

clean:
	rm -f *.class
	rm -f main_provide0*.java
	rm submodule2.jar
