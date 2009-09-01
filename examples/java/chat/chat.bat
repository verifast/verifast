javac -classpath .;..\..\..\src\rt\wrappers *.java
if errorlevel 1 goto end
java -cp ..\;..\..\..\src\rt\wrappers chat.Program
:end
