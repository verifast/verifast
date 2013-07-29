// Parameters are separated by ",", so this is invalid syntax.
// The lexer should recognise it as such and should not crash.
/*~*/#define SUM(x|y) (x+y)
