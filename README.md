This repository contains Isabelle formalization of binding-aware (co)datatypes
and (co)recursors related to the paper

> **Bindings as Bounded Natural Functors**<br/>
> Jasmin Christian Blanchette, Lorenzo Gheri, Andrei Popescu, Dmitriy Traytel

The formal development can be browsed as a generated HTML page
(html/index.html). A better way to study the theory files, however, is to open
them in Isabelle/jEdit.

The raw Isabelle sources are included in a separate directory called thys.

### Installation

The formalization can been processed with Isabelle2018, which can be downloaded
from

[https://isabelle.in.tum.de/website-Isabelle2018/](http://isabelle.in.tum.de/website-Isabelle2018/)

and installed following the standard instructions from

[https://isabelle.in.tum.de/website-Isabelle2018/installation.html](http://isabelle.in.tum.de/website-Isabelle2018/installation.html)

(With such a cold start it takes about 15 minutes until the opened theory is
processed. With Isabelle up and running it should take only 2 minutes.)

### Organization

The formalization is organized in the following theory files:

1. ```Prelim.thy``` and ```Card_Prelim.thy```:
  Background libraries for various auxiliary notions and theorems.

2. ```Template.thy```: An axiomatic implementation of polymorphic locales. We
have developed this axiomatic experimental command to avoid copy-pasting the
polymorphic axiomatizations and the derived proofs. Templates can be thought of
as polymorphic locales (Isabelle's monomorphic modules) that can also abstract
over type constructors. The templates are used for the (co)recursors and their
instantiation to obtain the substitution operators.

3. ```Common_Data_Codata_Bindings.thy```: The axiomatization of a sufficiently
diverse abstract MRBNF ```('a, 'b, 'c, 'd) F``` (following Proposal 5) of fixed
arity and with

  * ```'a``` being the top-free variable
    (the corresponding set function is called ```set1_F```),
  * ```'b``` being the top-binding variable
    (the corresponding set function is called ```set2_F```), and
  * ```'c``` and ```'d``` being the recursive variables
    (the corresponding set functions are called ```set3_F``` and ```set4_F```).

  Working with abstract axiomatic examples is the usual first step of our
  methodology of developing and implementing foundational constructions in
  Isabelle/HOL (compare this, e.g., to [our construction of standard datatypes](https://devel.isa-afp.org/browser_info/current/AFP/BNF_Operations/index.html)). In the implementations, all axioms are replaced by proofs which are provided by the user for atomic type constructors (e.g., sums and products) and discharged automatically by tactics for types constructed by the commands in question (e.g., datatypes and codatatypes).

4. ```Make_Nonrep.thy```: The nonrepetitiveness construction (Theorem 2), which
turns the recursive variable ```'c``` into a top-binding variable.

5. ```Datatype_Bindings.thy``` and ```Codatatype_Bindings.thy```: The
constructions of binding datatypes (Section 5.3) and codatatypes (Section 5.4)
as the binding-aware fixpoints

      ```'a TT == ('a, 'a, 'a TT, 'a TT) F```

   The implicit ```theta``` is for both datatype and codatatypes ```{(1,2)}```,
i.e., ```'b``` binds variables in ```'d```. The theory files also contain the
corresponding reasoning principles of fresh induction
(```TT_fresh_induct_param```, Theorem 13), fresh coinduction
(```TT_fresh_coinduct_param```, Theorem 15), and existential coinduction
(```TT_existential_coinduct```, Theorem 16).


6. ```Datatype_Bindings.thy``` and ```Codatatype_Bindings.thy```: The
constructions of binding datatypes (Section 5.3) and codatatypes (Section 5.4)
as the binding-aware fixpoints

      ```'a TT == ('a, 'a, 'a TT, 'a TT) F```

   The implicit ```theta``` is for both datatype and codatatypes ```{(1,2)}```,
   i.e., ```'b``` binds variables in ```'d```. The theory files also contain
   the corresponding reasoning principles of fresh induction
   (```TT_fresh_induct_param```, Theorem 13), fresh coinduction
   (```TT_fresh_coinduct_param```, Theorem 15), and existential coinduction
   (```TT_existential_coinduct```, Theorem 16)

7. ```More_Datatype_Bindings.thy``` and ```More_Codatatype_Bindings.thy```:
Additional helpful auxiliary theorems following from ```TT```'s construction.

8. ```Datatype_Recursion_Template.thy``` and
```Codatatype_Corecursion_Template.thy```: The constructions of the
binding-aware recursor (Section 7.1) and corecursor (Section 7.2), both
implemented as templates. Our formalization support full-fledged (co)recursion,
and not just (co)iteration. The latter is preferred in the paper because it is
more lightweight. The templates' assumptions correspond to the definitions of
term-like-structures (various ```swapping``` assumptions and predicates
reflecting Definitions 17 and 18) and (co)models (Definitions 19 and 22). The
(co)recursors characteristic properties are the theorems ```ff0_cctor```,
```ff0_DDTOR```, ```ff0_mmapD```, and ```ff0_FFVarsD``` (properties C, D, M, V
from Section 7).

9. ```Datatype_VVsubst.thy``` and ```Codatatype_VVsubst.thy```: The
instantiation of the (co)recursors to obtain a variable-for-variable
substitution operator (Theorem 8). These files also prove and summarize at the end the MRBNF properties of ```TT``` (Theorem 12).

10. ```Datatype_TVsubst.thy``` and ```Codatatype_TVsubst.thy```: The
instantiation of the (co)recursors to obtain a term-for-variable substitution
operator, assuming that ```F``` provides a suitable injection of free
variables (Theorem 9).

The terminology in the formalization slightly deviates from the one used in the
paper. Notable points are:

* Concepts on raw terms have the expected names, while the ```alpha```-quotiented
  concepts "stutter", e.g. ```'a T```, ```FVars```, ```map_T``` (raw) vs. ```'a TT```, ```FFVars```, ```map_TT```
  (quotiented).

* The variable ```u``` is commonly used for small support
  endo-bijections/endo-functions in the formalization, whereas in the paper it
  is used for models.

* ```vvsubst``` is variable-for-variable substitution, ```tvsubst``` is
  term-for-variable substitution; ```uvsubst``` and ```usubst``` are the
  corresponding unary versions of substitution (replacing a single variable by
  another or by another term)

* terminology mapping for (co)recursion (formalization&mdash;paper):<br/>
```CCTOR```&mdash;```Uctor```<br/>
```mmapC```&mdash;```Umap```<br/>
```FFVarsC```&mdash;```UFVars```<br/>
```mapP```&mdash;```Pmap```<br/>
```FVarsP```&mdash;```PFVars```<br/>
```DDTOR```&mdash;```Udtor```<br/>
```mmapD```&mdash;```Umap```<br/>
```FFVarsD```&mdash;```UFVars```<br/>


