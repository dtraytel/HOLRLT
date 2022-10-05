This is the artifact accompanying the paper:

Admissible Types-To-PERs Relativization in Higher-Order Logic
Andrei Popescu, Dmitriy Traytel

### How To Run?

The artifact contains the tool support we developed to experiment with relativization in Isabelle/HOL.
It works with the latest released version Isabelle2021-1, which can be downloaded here:

[https://isabelle.in.tum.de/website-Isabelle2021-1/](https://isabelle.in.tum.de/website-Isabelle2021-1/)

After downloading Isabelle, a good starting point is to issue the following command

```
/<Isabelle/installation/path>/bin/isabelle jedit -d . HOLRLT/Complex_MainRLT.thy
```

in the folder of the artifact. This will open Isabelle/jEdit and load Isabelle's "main" theories. The
`HOLRLT/Complex_MainRLT.thy` theory also contains a few examples of relativization as well as the registration of the
`filter` and the `biject` types as wide.

To let Isabelle check all relevant theories (from the command line, i.e., without running Isabelle/jEdit), one can use the command

```
/<Isabelle/installation/path>/bin/isabelle build -vd . HOLRLT HOLRLT-Library HOLRLT-Computational_Algebra Misc
```

### Overall Structure

For further orientation, the artifact contains the following Isabelle theories / ML files implementing the
relativization:

```
├── HOLRLT                   -- copy of the Isabelle/HOL distribution + our relativization infrastructure
    ├── Types_to_PERs.thy    -- theory loading our relativization infrastructure
    ├── MainRLT.thy          -- standard entrypoint + relativization of the finiteness predicate
    ├── Complex_MainRLT.thy  -- standard entrypoint + wideness of filter and biject + some relativization examples
	...

├── Misc                     -- additional theory files
    ├── LFP.thy and GFP.thy  -- the proofs of wideness for the datatype and codatatype construction discussed in the paper's Section 6.1
    ├── Group_Example.thy    -- the formalization of the paper's running example from Sections 3.1, 4.3, and 6.2
    └── Counterexample.thy   -- the formalization of the paper's Example 6 (the existence of a non-wide type)
└── Tools                    -- implementation of relativization
    ├── relativization.ML    -- relativization of types (RIN), terms (RLT), and theorems (RLTHM)
    ├── wide_database.ML     -- database of types registered as wide
    ├── wide_typedef.ML      -- command to register a type as wide (with user-supplied proof) 
    └── wide_datatype.ML     -- automatic registration of (co)datatypes as wide
```

Types that we have manually proved to be wide, including the ones from the paper's Figure 2 and more, can be easiest found using grep:

```
grep -r ^wide_typedef HOLRLT
```

(The type `comm` in Figure 2 is actually called `commute` in the formalization. All other types have the same names as shown in the
paper.)

As we explain in the paper, in cases where these types already had relation-lifting operators defined for them, we were able to (re)use
them as relational witnesses in our wide-typedness proofs. The proofs are often laborious, and sometimes require alternative
characterizations of the relation-lifting operators (as, e.g., in the case of the `filter` type constructor), or of the relativization of
the defining predicate (as, e.g., in the case of the `fset` (finite sets) type constructor).

### Detailed Overview

Our implementation of relativization consists of the ML files in the Tools folder. The mutually recursive ML functions `RIN` and `RLT` in
Tools/relativization.ML constitute the core of the implementation. They incorporate the extensions from Appendix G to cover Isabelle/HOL's
declared-only constants and overloading.

The theory file `HOLRLT/ComplexMainRLT.thy` contains some examples of relativized theorems, e.g., `Cantors_paradox` and its
relativization `Cantors_paradox_rlt`. There, one can also see an invocation of the ML command for relativizing theorems:

```
local_setup ‹RLTHM @{binding Cantors_paradox_rlt} @{thm Cantors_paradox}›
```

This command is defined in `HOLRLT/Types_to_PERs.thy` as a thin wrapper around the homonymous function from `Tools/relativization.ML`.

The second example in the `HOLRLT/ComplexMainRLT.thy` theory involves declared-only constants (introduced via the `comm_semiring_1` type
class):

```
local_setup ‹RLTHM @{binding binomial_ring_rlt} @{thm binomial_ring}›
```

A second "end-user" command is the ML function `RLCST` (also defined in `HOLRLT/Types_to_PERs.thy`) that relativizes a single constant.
E.g., see the relativizations of the logical connectives in `HOLRLT/Types_to_PERs.thy`

```
local_setup ‹ RLCST @{term "True"} ›
local_setup ‹ RLCST @{term "False"} ›
local_setup ‹ RLCST @{term "(∧)"} ›
local_setup ‹ RLCST @{term "(∨)"} ›
local_setup ‹ RLCST @{term "Not"} ›
local_setup ‹ RLCST @{term All} ›
local_setup ‹ RLCST @{term Ex} ›
local_setup ‹ RLCST @{term Ex1} ›
```

We could have wrapped `RLTHM` and `RLCST` into proper Isabelle commands that hide the ML from the user, but we did not to do so yet in
our prototype.

Our tool introduces relativized versions of given theorems as axioms, relying on our paper's main Admissibility result (theorem 19 from
the paper) as a meta-justification. Our theoretical results in principle allow for an axiom-free implementation of relativization. (The
main purpose of this tool was to test our empirical hypothesis that wide-typedness holds pervasively in HOL developments. In order for us
to prove wide-typedness of a type definition, everything before it -- constants or types -- had to be relativized and proved wide. We
axiomatized relativization counting on our Admissibility meta-theorem, and only proved wide-typedness.)

More specifically, whenever relativization encounters a defined type (e.g., those introduced using the `typedef` command), it looks up
its relational witness in the database of widely-typed types and fails if none exists. After encountering the failure, the user may
register the type as widely-typed by providing the relational witness and exhibiting the desired bijection-up-to (and proving their
properties). We currently only automate the registration and the proofs (without any user involvement) for type copies, i.e., types
defined using the `%_. True` predicate. Such automation should in principle also be easy to provide for monomorphic types (e.g., `int`,
`real`), but currently these have to be proved wide manually.

(To go axiom-free for relativization, we would need to analyze the proofs of non-relativized theorems. However, by default Isabelle does
not store/record proofs. There is a facility for enabling proof terms due to Berghofer and Nipkow: *Proof Terms for Simply Typed Higher
Order Logic*, TPHOLs 2000. A future axiom-free implementation of relativization could take advantage of that work: either by a
comprehensive translation of the proof terms following our paper proof of Admissibility, or by only looking at the facts used in the
proof term and performing proof reconstruction in the style of Sledgehammer, hopefully even reusing the existing Sledgehammer
infrastructure. Since (in spite of aggressive compression techniques employed by Berghofer and Nipkow) proof terms are currently severely
hampering Isabelle's performance hence cannot be used in day-to-day developments, for the future we envision (1) lightweight (axiomatic)
relativization as the default combined with (2) full proofs as an extra check that can be left to run overnight.)

### Datatypes and Codatatypes

Our tool automatically registers datatypes and codatatypes as widely-typed, by axiomatizing the required properties. As with
Admissibility, this is a compromise --- this time based on our Compatibility result (theorem 23 from the paper) as meta-justification. We
formalized in Isabelle the main step involved in the Compatibility theorem, proving that, *if* a BNF (bounded natural functor) has a wide
type definition, then its initial algebra (least fixed point) and final coalgebra (greatest fixed point) also have wide type definitions.
This was done in the theories `Misc/LFP.thy` and `Misc/GFP.thy`. Since these theories correspond to the internal constructions of
(co)datatypes in Isabelle/HOL, in the future it will be possible to turn our proofs into Isabelle/ML tactics that are applied dynamically
to any user-defined (co)datatype, and thus remove our reliance on the Compatibility meta-justification.

The internal constructions of (co)datatypes as fixpoints of type equations shown in the files `Misc/LFP.thy` and `Misc/GFP.thy` are taken
from the Archive of Formal Proofs entry [`BNF_Operations`](https://www.isa-afp.org/entries/BNF_Operations.html), which documents what
Isabelle's `datatype` and `codatatype` commands do internally. Here, we extend these construction with the proofs of wideness for the
resulting fixpoints. To run these theories (in the artifact's main folder) start Isabelle using the commands:

```
/<Isabelle/installation/path>/bin/isabelle jedit -d . -l HOLRLT Misc/LFP.thy
/<Isabelle/installation/path>/bin/isabelle jedit -d . -l HOLRLT Misc/GFP.thy
```

(The `-l` flag is optional but recommended.)


### Paper Examples

We also include two small Isabelle theories formalizing the examples from the paper:
* `Misc/Group_Example.thy` formalizes our working examples (introduced in Section 3.1 and revisited in Sections 4.3 and 6.2);
* `Misc/Counterexample.thy` formalizes the wide-typedness counterexample (Example 6). 
To run these theories (in the artifact's main folder) start Isabelle using the commands: 

```
/<Isabelle/installation/path>/bin/isabelle jedit -d . -l HOLRLT Misc/Group_Example.thy
/<Isabelle/installation/path>/bin/isabelle jedit -d . -l HOLRLT Misc/Counterexample.thy
```

(The `-l` flag is optional but recommended.)
