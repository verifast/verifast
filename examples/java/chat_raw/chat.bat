javac *.java
if errorlevel 1 goto end
java -cp .. chat.Program
:end
