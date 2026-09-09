# NL: general matrix semantics and Lean source

## Verification status

**The Lean files have not been executed or kernel-checked in this environment.**
A Lean executable was unavailable, and attempts to obtain a compiler did not
succeed. `lean_attempt.txt` records the failed local invocation. Do not treat
this package as an already kernel-verified result.

The mathematical soundness and completeness proof is given below. The Lean
files contain complete proof scripts with no `sorry`, `admit`, extra `axiom`
declarations, `unsafe` declarations, or `native_decide`. Their compilation
remains to be checked with Lean. The target toolchain is pinned in
`lean-toolchain` to Lean 4.19.0; only the standard library is imported.

Independent Python exhaustive checks *were* executed. Both finite matrices
passed every instance of the seven axioms and two rule-preservation conditions:
40 instances for the Boolean matrix and 624 for the six-element matrix.
These finite checks are not a verification of the general completeness theorem.

## Files

| File | Purpose |
|---|---|
| `NLPrimitive.lean` | Exact displayed calculus, treating implication as primitive; general matrix soundness, strong completeness, a canonical countermodel, a Boolean model, and nonderivability of Aristotle's first thesis. |
| `NLDefined.lean` | Same seven axioms and two rules, but implication is defined as `neg (compat A (neg B))`; analogous matrix results, a six-element model, and derivations of both Aristotle theses. |
| `check_finite_models.py` | Standalone exhaustive finite-model tests using Python's standard library. |
| `finite_checks.json` | Actual output of the executed Python tests. |
| `check.sh` | Runs Lean on both files and then reruns the Python tests. |
| `lean-toolchain` | Target Lean version, for use with elan. |
| `lean_attempt.txt` | Actual unsuccessful Lean invocation in the authoring environment. |

With Lean available, run from this directory:

```sh
./check.sh
```

Or run the files separately:

```sh
lean NLPrimitive.lean
lean NLDefined.lean
python3 check_finite_models.py
```

The `#print axioms` commands ask Lean to report dependencies of the principal
theorems. There is no claimed or fabricated output from these commands here.

## Exact scope

The construction is a general algebraic logical-matrix semantics, not an
NL-specific relational representation theorem or a finite truth-table
completeness theorem. The model conditions are a finite universal-Horn
translation of the displayed axioms and rules. They do not mention derivations.
The completeness argument uses a canonical term-algebra matrix.

The historical definition of implication is absent from the question's list of
definitions, so both readings are kept separate. Neither file adds conjunction
elimination, replacement of provable equivalents, associativity, unrestricted
transitivity of object-language implication, or a deduction theorem.

The abbreviation for three inequalities is left-associated, in the order
AB, BC, AC. Right association would define a different displayed schema unless
associativity is independently established; the same construction would work
with that choice after changing `Ops.distinct3`.

For nonempty premise sets, `Derives` is the natural local extension of the two
rules. For the empty premise set, it is precisely the theorem-generating
calculus specified by the corresponding reading.

## Semantic specification

For the primitive reading, an algebra has a nonempty carrier X and operations
`neg`, `conj`, `compat`, and `arr`, of arities 1, 2, 2, and 2. In the defined
reading it has only the first three, with

```text
arr(a,b) = neg(compat(a,neg(b))).
```

In either case define algebraic terms

```text
inc(a,b)         = neg(compat(a,b))
eqv(a,b)         = conj(arr(a,b),arr(b,a))
neq(a,b)         = neg(eqv(a,b))
distinct3(a,b,c) = conj(conj(neq(a,b),neq(b,c)),neq(a,c)).
```

The terms `s1` through `s7` in each Lean file are exactly the seven axiom
patterns, with these expansions. A matrix consists of such an algebra and a
predicate D on its carrier, satisfying universally:

```text
D(s1(a))                         D(s2(a,b))
D(s3(a))                         D(s4(a,b))
D(s5(a,b,c))                     D(s6(a,b))
D(s7(a,b,c))
D(a) and D(arr(a,b)) imply D(b)
D(a) and D(b) imply D(conj(a,b)).
```

The term `eqv(a,b)` is an algebra element, not actual equality. The term
`neq(a,b)` is not actual inequality. In particular, `s6` does not impose literal
commutativity of the algebra operation, and the premise in `s5` is not a
metatheoretic distinctness condition.

A valuation sends variables to carrier elements and evaluates formulas
homomorphically. A formula is satisfied when its value belongs to D. Semantic
consequence quantifies over every such matrix and every valuation, preserving
satisfaction of premises. This definition does not mention `Derives`.

## Soundness and completeness proof

**Soundness.** Induct on a derivation. An assumption is designated by premise
satisfaction. Each axiom instance is designated by the corresponding universal
matrix condition. Modus ponens and adjunction preserve designation by the last
two conditions. Thus derivability implies semantic consequence.

**Completeness.** Fix a premise predicate Gamma. Let the carrier be the set of
formulas in the relevant primitive signature; use the formula constructors as
its algebra operations. Designate exactly those formulas derivable from Gamma.
This is a matrix: all seven axiom patterns are designated, and the designated
set is closed under the two rules. Let the canonical valuation map each
variable to itself. Structural induction gives `eval(A) = A`, so a formula is
satisfied under this valuation exactly when it is derivable from Gamma.
Every premise is satisfied. If Gamma semantically entails A, apply that
entailment to this particular matrix and valuation to conclude that A is
derivable. Equivalently, every nonderivable formula has this canonical
countermodel relative to Gamma.

The model class is defined independently of derivability. Using derivability
to construct a witness *within* that class in the completeness proof is not a
definition of semantic validity as provability.

## Finite models and the missing implication definition

For the primitive reading, use Boolean negation and conjunction, material
implication, constant-true compatibility, and designated value true. This
satisfies all the displayed axioms and rules. At p=false, however,
`neg(arr(p,neg(p)))` is false. Consequently Aristotle's first thesis is not a
theorem of the primitive-implication reading. This matrix does not satisfy the
additional definition of implication used by Nelson.

For the defined reading, the supplied six-element operation tables are taken
from Davide Fazio and Raffaele Mascella, *Considerations on Everett J. Nelson's
connexive logic*, arXiv:2506.10893v1 (12 June 2025), Example 4.1. The designated
values are a, c, e. The Python test checks these tables against the axioms in
the question, not merely against the paper's presentation. In particular, it
checks inconsistency symmetry and conjunctive guarded transitivity exactly as
encoded by `s2` and `s5` here. No completeness theorem from the paper is assumed.

The same preprint uses the historical implication definition in Section 3 and
studies presentations with further inference rules. Its richer
algebraic-relational completeness results are not being silently transferred
to the two-rule systems in this package.
