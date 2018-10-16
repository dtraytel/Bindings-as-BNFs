This repository contains Isabelle formalization of binding-aware (co)datatypes
and (co)recursors related to the paper

> **Bindings as Bounded Natural Functors**<br/>
> Jasmin Christian Blanchette, Lorenzo Gheri, Andrei Popescu, Dmitriy Traytel

The repository also contains an appendix to the paper (```appendix.pdf```),
which was included in the supplementary material of the original submission.
Here, we restricted this appendix to the part, which is directly relevant for
(and referenced in) the formalization artifact.

The formal development can be browsed as a [generated HTML page](https://htmlpreview.github.io/?https://github.com/dtraytel/Bindings-as-BNFs/blob/master/html/index.html) (see also the html directory). A better way to study the theory files, however, is to open
them in Isabelle/jEdit.

The raw Isabelle sources are included in a separate directory called thys.

### Installation

The formalization can been processed with Isabelle2018, which can be downloaded
from

[https://isabelle.in.tum.de/website-Isabelle2018/](http://isabelle.in.tum.de/website-Isabelle2018/)

and installed following the standard instructions from

[https://isabelle.in.tum.de/website-Isabelle2018/installation.html](http://isabelle.in.tum.de/website-Isabelle2018/installation.html)

With such a cold start it takes about 15 minutes until the opened theory is
processed. With Isabelle up and running it should take only 2 minutes.

### Organization

The formalization is organized in the following theory files:

1. ```Prelim.thy``` and ```Card_Prelim.thy```:
  Background libraries for various auxiliary notions and theorems.

2. ```Template.thy```: An axiomatic implementation of polymorphic locales
(which are Isabelle's monomorphic modules). We have developed this axiomatic
experimental command to avoid copy-pasting the polymorphic axiomatizations and
the derived proofs. (See a detailed explanation and example below.)
In our setting, the templates are used for the (co)recursors and their
instantiation to obtain the substitution operators.

3. ```Common_Data_Codata_Bindings.thy```: The axiomatization of a sufficiently
diverse abstract MRBNF ```('a, 'b, 'c, 'd) F``` (following Proposal 5) of fixed
arity and with

  * ```'a``` being the free-variable input
    (the corresponding set function is called ```set1_F```),
  * ```'b``` being the binding-variable input
    (the corresponding set function is called ```set2_F```), and
  * ```'c``` and ```'d``` being the unconstrained (potential term) inputs
    (the corresponding set functions are called ```set3_F``` and ```set4_F```).

  Working with abstract axiomatic examples is the usual first step of our
  methodology of developing and implementing foundational constructions in
  Isabelle/HOL (compare this, e.g., to [our construction of standard datatypes](https://devel.isa-afp.org/browser_info/current/AFP/BNF_Operations/index.html)). In the implementation, all axioms will be replaced by proofs
  which are supplied by the user for atomic type constructors (e.g., sums and
  products) or synthesized automatically by tactics for types constructed by
  the commands in question (e.g., datatypes and codatatypes).

4. ```Make_Nonrep.thy```: The nonrepetitiveness construction (Theorem 2), which
turns the unconstrained variable ```'c``` into a binding-variable input.

5. ```Datatype_Bindings.thy``` and ```Codatatype_Bindings.thy```: The
constructions of binding datatypes (Section 5.3) and codatatypes (Section 5.4)
as the binding-aware fixpoints

      ```'a TT == ('a, 'a, 'a TT, 'a TT) F```

   The implicit ```theta``` is for both datatypes and codatatypes ```{(1,2)}```,
i.e., ```'b``` binds variables in ```'d```. The theory files also contain the
corresponding reasoning principles of fresh induction
(```TT_fresh_induct_param```, Theorem 13), fresh coinduction
(```TT_fresh_coinduct_param```, Theorem 15), and existential coinduction
(```TT_existential_coinduct```, Theorem 16).

6. ```More_Datatype_Bindings.thy``` and ```More_Codatatype_Bindings.thy```:
Additional helpful lemmas following from ```TT```'s construction.

7. ```Datatype_Recursion_Template.thy``` and
```Codatatype_Corecursion_Template.thy```: The constructions of the
binding-aware recursor (Section 7.1) and corecursor (Section 7.2), both
implemented as templates. Our formalization supports full-fledged
(co)recursion, and not just (co)iteration (see ```appendix.pdf``` for details).
The latter is preferred in the paper because it is more lightweight. The
templates' assumptions correspond to the definitions of term-like-structures
(various ```termLikeStr``` assumptions and predicates reflecting Definitions 17
and 18) and (co)models (Definitions 19 and 22). The (co)recursors
characteristic properties are the theorems ```ff0_cctor```, ```ff0_DDTOR```,
```ff0_mmapD```, and ```ff0_FFVarsD``` (properties C, D, M, V from Section 7).

8. ```Datatype_VVsubst.thy``` and ```Codatatype_VVsubst.thy```: The
instantiation of the (co)recursor to obtain a variable-for-variable
substitution operator (Theorem 8). These files also prove and summarize at the end the MRBNF properties of ```TT``` (Theorem 12).

9. ```Datatype_TVsubst.thy``` and ```Codatatype_TVsubst.thy```: The
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
  is used for elements of models.

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

### Templates

  A template fixes a type constructor and some polymorphic constants and
assumes some polymorphic theorems about them. Under these assumptions the user
can then prove further theorems. For example here is the template for functors
and we prove the injectivity of the functorial action.

        template Functor =
          'a F
          fixes map_F :: "('a ⇒ 'b) ⇒ 'a F ⇒ 'b F"
          assumes map_F_id: "map_F id = id"
          and map_F_comp: "⋀f g x. map_F (f o g) x = map_F f (map_F g x)"
        begin

        lemma inj_map_F: "inj f ⟹ inj (map_F f)"
          by (rule injI, drule arg_cong[of _ _ "map_F (inv f)"])
            (auto simp: map_F_comp[symmetric] map_F_id)

        end

  A template instantiations maps the fixed type constructors and constants to
  concrete type constructors/values, lets the user prove the assumptions, and
  after that axiomatized all the theorems proved in the context of a template,
  but with the fixed type constructors and constants being replaced by the
  concrete type constructors/values. For example,

        template_instance list : Functor
          where 'a Functor.F = "'a list"
          for Functor.map_F = map
          by auto

  will axiomatize the theorem ```inj_map_F: "inj f ⟹ inj (map f)"```.

  Templates lack many conveniences of locales (e.g., extensibility), however,
  their support for polymorphism is a likely useful contribution to
  Isabelle/HOL beyond the scope of this paper (even though the formalization
  accompanying this paper was the primary motivation for developing this
  feature).

  The use of templates is not necessary for our development, but it saves us a
  lot of copy-pasting and search&replace in this pre-implementation stage.


