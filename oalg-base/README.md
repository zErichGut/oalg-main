Basic definition of algebraic structures, viewing through the lens of categories.

- Most algebraic operations, e.g. multiplication, addition etc, are partially defined operators,
but have precise definition for there applicability.

- Limits serve as a backbone for solving algebraic problems, e. g. finding all solutions of the
equation a * x == 0 is given by the kernel of a.

The actual release contains a minimum of functionality to define finitely generated abelian groups
and the kernels and cokernels respectively. As such, a lot of more work has to be done to get a
complete base for solving algebraic problems.

To Do:

- Property for Generator more precise.

- Exact sequences.

- Kernel and cokernels for matrices over a field.

- As Double is not implemented as an algebraic structure here (it dose not comply to the stated
properties),it is not so obvious how to handle reals.

- More statements for validation.