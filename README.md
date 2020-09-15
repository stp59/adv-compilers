# adv-compilers

For all projects 6120-related.

Credit to Adrian Sampson et. al. for all the code in the `bril` subdirectory.
This includes types for the bril AST and a parser from the json format.

# contrived.ml

A simple program that traverses a bril AST and sums the integer and boolean
constants appearing in the program, treating `true` as `1` and `false` as `0`.
It is also equipped with a test suite making use of Turnt. The tests consist of
a small subset of the benchmark from the bril repository.