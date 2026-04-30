Alg 0:

For n:
enum all terms of size n
for each term l:
synthesize kbo minimal term r, add rule l -> r


Alg 1:
Simplify with R n, if smaller size, discard
otherwise: smt


Alg 2:
Enumerate terms only from the irreducible set of previous iterations.


Alg 3:
Enumerate terms only with lexicographic order on variables.
rename each rule for all permutations