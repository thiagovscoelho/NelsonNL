# NelsonNL: matrix semantics for Nelson's logic in Lean

This project formalizes soundness and strong completeness for two readings of
the seven-axiom, two-rule presentation of Everett J. Nelson's logic NL. Both
developments prove, for any set of premises Γ and formula A,

$$
\Gamma \vdash A \quad\Longleftrightarrow\quad \Gamma \models A.
$$

The semantics uses algebras with designated values (logical matrices). The
repository also supplies finite models, proofs that both calculi are
nontrivial, and results showing why the definition of implication matters.

**Verified:** a fresh `lake build` succeeded with Lean **4.24.0**, compiling
both source modules with no errors. `NLDefined.lean` emits non-fatal linter
warnings about local names resembling constructors. Both files import only
`Std`; no Mathlib or other external Lean packages are required.

## Build and check

With Lean's `elan` toolchain manager installed and `lake` on your PATH, run
these commands from the repository root:

```sh
lean --version
lake build
```

[lean-toolchain](lean-toolchain) pins `leanprover/lean4:v4.24.0`.
[lakefile.toml](lakefile.toml) makes both `NLPrimitive` and `NLDefined` roots
of the default library target. A successful build ends with
`Build completed successfully`. To rebuild from scratch, run `lake clean`
followed by `lake build`.

To check one source file directly and see its theorem-dependency reports:

```sh
lake env lean NLPrimitive.lean
lake env lean NLDefined.lean
```

The optional Python checks require Python 3.9 or newer and no third-party
packages:

```sh
python3 check_finite_models.py
```

On Windows, use `python check_finite_models.py` if that is your Python command.
The output should contain empty `failures` objects for both models, with
`total_checks` equal to **40** and **624**, respectively. These results have
been reproduced locally and agree with [finite_checks.json](finite_checks.json).
Inspect both `failures` objects: the script currently asserts success only for
the Boolean model. These checks supplement the Lean proofs; they do not prove
general completeness.

In a Bash environment with `lean` and `python3` on PATH, `bash check.sh` runs
both Lean files and the Python checks together.

## Two readings of implication

The project began with the presentation of NL copied from Section 3.6 of the
Stanford Encyclopedia of Philosophy's [“Connexive Logic” article](https://plato.stanford.edu/entries/logic-connexive/).
That passage describes finding a sound and complete semantics for NL as an
open problem, which motivated this project's attempt to construct and verify
one.

The copied presentation lists seven axiom schemas and two rules but omits
the definition of implication. Read literally, that omission gives a different
calculus from the intended one. The project therefore treats both the
incomplete specification as written and the same calculus with Nelson's
implication definition restored:

$$
A \to B := \neg(A \circ \neg B).
$$

Here `◦` is the primitive consistency/compatibility connective, named `compat`
in Lean.

| Module | Primitive connectives | Distinguishing result |
|---|---|---|
| [NLPrimitive.lean](NLPrimitive.lean) | Negation, conjunction, compatibility, implication | `¬(p → ¬p)` is not derivable. |
| [NLDefined.lean](NLDefined.lean) | Negation, conjunction, compatibility; implication is defined above | Both Aristotle theses, `¬(A → ¬A)` and `¬(¬A → A)`, are derivable for every formula A. |

Each module has its own syntax and namespace. Start with `NLDefined` for the
defined-implication reading, or `NLPrimitive` to study the effect of leaving
implication unconstrained by that definition. This difference changes the
theorems, not just their notation.

The Lean results supply sound-and-complete general matrix semantics for both
versions: the problem arising from the omitted definition and the intended
seven-axiom, two-rule problem with that definition included. This answers the
request for semantics in the general matrix sense explained below; it is not
a claim to settle every stronger semantic or historical reconstruction
question associated with the SEP's open-problem statement.

## The exact calculus

The following abbreviations are used in both developments:

```text
A | B       := ¬(A ◦ B)
A = B       := (A → B) ∧ (B → A)
A ≠ B       := ¬(A = B)
A ≠ B ≠ C   := ((A ≠ B) ∧ (B ≠ C)) ∧ (A ≠ C)
```

The equality and inequality symbols here denote formulas, not Lean equality
or inequality. The last abbreviation is left-associated in the order AB,
BC, AC; no associativity law is assumed.

The schemas `s1` through `s7` encode:

```text
1.1  A → A
1.2  (A | B) → (B | A)
1.3  A → ¬¬A
1.4  (A → B) → (A ◦ B)
1.5  (A ≠ B ≠ C) → (((A → B) ∧ (B → C)) → (A → C))
1.6  (A ∧ B) = (B ∧ A)
1.7  ((A ∧ B) → C) → ((A ∧ ¬C) → ¬B)
```

There are two inference rules:

- **Modus ponens:** from A and A → B, infer B.
- **Adjunction:** from A and B, infer A ∧ B.

`Derives Γ A` extends these rules to proofs from premises in Γ. With Γ empty,
it gives theoremhood. Conjunction elimination, replacement of provable
equivalents, associativity, unrestricted transitivity of implication, and a
deduction theorem are not added as rules or assumptions.

## How the semantics works

A `Matrix α` consists of a nonempty carrier, operations interpreting the
primitive connectives, and a predicate `D : α → Prop` selecting designated
values. Its conditions require every instance of `s1`–`s7` to be designated,
and designation to be preserved by modus ponens and adjunction. These are
finitely many universally quantified conditions on operations and `D`;
the definition does not mention derivability.

A valuation assigns carrier elements to propositional variables, indexed by
`Nat`. `eval` extends this assignment recursively to formulas. A formula is
satisfied when its value is designated. `Entails Γ A` says that every matrix
and valuation satisfying all premises in Γ also satisfies A.

The operations need not behave like Boolean connectives. In particular,
schema 1.6 requires a designated equivalence formula, not literal equality
of the values of A ∧ B and B ∧ A. The guard in 1.5 uses the formula `≠`,
not actual distinctness of carrier elements.

Soundness follows by induction on derivations: matrix conditions validate
axioms and preserve designation at each rule application.

For completeness, fix Γ and take formulas themselves as the carrier, with
formula constructors as operations and Γ-derivable formulas as designated
values. This is the **canonical matrix**. Under the valuation sending each
variable to itself, evaluation returns the original formula. The resulting
truth lemma identifies satisfaction in this matrix with derivability from Γ.
Applying semantic consequence to this matrix proves completeness; a formula
not derivable from Γ has the same matrix as a countermodel.

The construction takes no quotient by provable equivalence and therefore
needs no replacement or congruence assumption. Derivability is used to
construct this particular model, while the model class and semantic
consequence are defined independently of it.

This establishes general matrix completeness for the displayed calculi.
It does not establish completeness for a single finite truth table, a
decision procedure, or an algebraic-relational representation theorem.

## Finding and using the Lean results

Both modules follow the same order: syntax and operations, axiom schemas,
derivations, matrices and evaluation, soundness, the canonical construction,
completeness, then finite models and examples.

| Declaration in each namespace | Result |
|---|---|
| `sound`, `complete` | The two directions relating `Derives` and `Entails`. |
| `sound_complete` | `Derives Γ A ↔ Entails Γ A` for arbitrary premise predicates. |
| `theorem_iff_valid` | The empty-premise case: `Theorem A ↔ Valid A`. |
| `canonical_truth` | Satisfaction under the canonical valuation iff derivability. |
| `canonical_countermodel` | A countermodel for any formula not derivable from Γ. |
| `nontrivial` | Variable 0 is not a theorem. |

After building, import the modules by their names, rather than `NelsonNL`:

```lean
import NLPrimitive
import NLDefined

#check NLPrimitive.sound_complete
#check NLDefined.sound_complete
#check NLPrimitive.aristotle_not_derivable
#check NLDefined.aristotle1
#check NLDefined.aristotle2
```

The files contain no `sorry`, `admit`, additional `axiom` declarations,
`unsafe` declarations, or `native_decide`. Their `#print axioms` commands
report `[propext]` for `sound_complete`, `theorem_iff_valid`, and
`canonical_countermodel` in both namespaces. `propext` is Lean's standard
propositional extensionality axiom. The reported nontriviality and Aristotle
results have no axiom dependencies.

## Finite models and references

`NLPrimitive.boolMatrix` uses Boolean negation and conjunction, material
implication, constant-true compatibility, and designated value `true`.
All matrix conditions hold. At p = false, `¬(p → ¬p)` evaluates to false,
giving the countermodel used by `aristotle_not_derivable`. This matrix does
not satisfy the additional definition of implication, as proved by
`bool_implication_not_defined`.

`NLDefined.sixMatrix` has values a, b, c, d, e, f, with a, c, e designated.
Its operation tables come from Example 4.1 of Davide Fazio and Raffaele
Mascella, [*Considerations on Everett J. Nelson's connexive logic*,
arXiv:2506.10893v1](https://arxiv.org/html/2506.10893v1#S4.Ex1)
(12 June 2025). The paper also discusses Nelson's implication definition
and systems with additional inference rules. Here the tables are verified
against this repository's seven schemas and two rules; no completeness
theorem from the paper is assumed.

Both finite matrices are verified in Lean by exhaustive cases and `decide`.
The standalone [Python script](check_finite_models.py) provides a second
implementation of the finite checks.

## Repository notes

The old failure log [lean_attempt.txt](lean_attempt.txt) and verification
comments at the top of the Lean files describe the original authoring
environment. They predate the successful Lean 4.24.0 build reported here.
[SHA256SUMS.json](SHA256SUMS.json) records the original source bundle's
checksums; it is not a current-worktree integrity manifest after the Lake
reinitialization and README update.

The repository includes a [GitHub Actions workflow](.github/workflows/lean_action_ci.yml)
for Lean builds. The build result reported above is from local verification.
The project is released under [CC0 1.0 Universal](LICENSE).
