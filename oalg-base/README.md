A package for solving algebraic problems purely written in Haskell.

First of all we define entities. Based on them and since we look at algebra through the lens of
categories, we define oriented structures on which, by means of a suitable partially defined
multiplication, multiplicative structures are defined. If one provides such a multiplicative structure
with a matching additive structure, one obtains distributive structures on which matrices are build.
If an additive structure is provided with a matching scalar multiplication, vectorial structures are
obtained, which then form the basis for algebraic structures together with the distributive
structures.

Limits - in context of categories - serve as a backbone for solving algebraic problems, e. g.
finding all solutions of the equation a * x == 0 is given by the kernel of a.

Particular attention is paid to the duality of concepts - viewed through the lens of categories - so
that the implementation of the dual concept could be traced back to the original one to avoid
duplicate or redundant implementation efforts.
  
A central feature in this package is that all functions defined here - unless otherwise stated - are
total and means 'if the input values are valid then the resulting value is also valid'. Most
functions do not check their preconditions. Therefore, all data structures defined here are provided
with a property section that is translated into a corresponding statement so that they can be
validated as needed. If there is an exception to this rule - such as for partially defined algebraic
operators - the rule is extended by 'if the input values are valid and fulfill the additional
required properties, the resulting value is also valid'. Most of the algebraic operators do check
there additional required preconditions.

Since the algebraic operators - such as (*), (+), (.) ... - have been redefined here, one should
exclude the standard Prelude when using this package, to avoid ambiguity, and use Prelude provided
here.

Throughout the descripitions in this package we denote type variables in lower case bold letters to
distinguishing them from variables for values of a type.
  
Since we take the view that a value of a data structure or an instance of a class must strictly
fulfill the required properties to be valid, Double, for example, has not been implemented as a
numerical type.


