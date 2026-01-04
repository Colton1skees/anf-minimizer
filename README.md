# anf-minimizer

`anf-minimizer` accepts boolean expressions, encodes them as a system of equations over GF(2), and returns the minimized system after converting it back to a boolean expression.


## Example
Input:
```
(x3 & (1 ^ x0 ^ x1 ^ x2)) | (x4 & (x0 ^ x1 ^ x2 ^ x3)) | (x2 & x3 & (x0 ^ x1)) | x3
```

Output:
```
(x3)|(x0*x4 + x1*x4 + x2*x4)
```

## Use cases
Investigating some ways to improve the quality of [[1]](https://ceur-ws.org/Vol-3455/short4.pdf) on booleans with large groebner bases. 

## References
[1] [Gröbner Bases for Boolean Function Minimization](https://ceur-ws.org/Vol-3455/short4.pdf)