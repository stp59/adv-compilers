# adv-compilers

For all projects 6120-related.

Credit to Adrian Sampson et. al. for the code in the `bril` subdirectory, which
is a customized version of the bril AST and parser/deparser for bril <=> json
adapted from the repository sampsyo/bril.

Run `make` to build. This done, the `./bril-opt` supports the following CLI:

* `--help`: display the help menu
* `--contrived`: input text (expects a json representation of a bril program) and
run the contrived "sum all constants" routine.
* `--nop`: input text (expects json rep of bril), parse into the bril.mli types,
and deparse back into the json format with no changes.
* `--tdce`: input text (expects json rep of bril), parse into bril AST, run
trivial dead code elimination, and output modified json string
* `--lvn`: input text (expects json rep of bril), parse into bril ASt, run
local value numbering optimizations followed by tdce, and output modified json string

# contrived.ml

A simple program that traverses a bril AST and sums the integer and boolean
constants appearing in the program, treating `true` as `1` and `false` as `0`.
It is also equipped with a test suite making use of Turnt. The tests consist of
a small subset of the benchmark from the bril repository.

# tdce.ml & lvn.ml

tdce.ml implements trivial dead code elimination as presented in Lesson 3. It
removes definitions that are unused globally and iterates to convergence. It also
eliminates definitions that are killed locally (i.e. within a single basic block).
I have run this on the tdce test suite from the bril repository and found that it
meets the suite's standard for code eliminations. I have also run it on the
benchmark suite and found that it behaves the same as `--nop` in terms of
input/expected output. The total dynamic instruction count with tdce is consistently
less than or equal to the same figures with `--nop`.

lvn.ml implements local value numbering as presented in Lesson 3. That is, it
performs a semantics-blind version of common sub-expression elimination and copy propogation within single basic blocks. Running the same experiments as with tdce
revealed similar results -- lvn has the same correctness results as `--nop` on the
benchmark suite with a uniform decrease in dynamic instructions executed. It also
behaves as expected according to the lvn test suite on the bril repository with a
few exceptions due to the fact that the lvn on the repository incorporates some
semantics-specific transformations (e.g. commutivity of addition, semantics of id, etc).