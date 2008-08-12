time < crlf.txt
for /L %%i in (1, 1, 10) do verifast.opt %1 > null
time < crlf.txt
