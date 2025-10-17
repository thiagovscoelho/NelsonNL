# NelsonNL

Providing a sound and complete semantics for NL is an open problem in connexive logic.

The goal of this project is to verify [a semantics that ChatGPT made up](https://thiago-gpt.blogspot.com/2025/10/semantics-for-e-nelsons-connexive-logic.html) to solve this problem. ChatGPT is basically the only real author of the project as of now, since I don’t know any math and I don’t know any Lean.

Acknowledgements: Thanks to math-understanding friends who reassured me that this stuff is at least not obviously meaningless garbage so that I’m not some sort of case of “LLM psychosis”. If this turns out to be wrong, that’s fine, but at least it wasn’t obvious.

The following is what ChatGPT thinks the status of the project is. I have no idea how accurate it is.

## What’s already done (and where)

### `NL/Semantics.lean` (core, stable)

* Object language (`Formula α`) + notations: `¬ₗ`, `∧ₗ`, `→ₗ`, primitive `◦`; abbrevs `|ₗ`, `=ₗ`, `neq`, `neq3`.
* Frames and models:

  * `Frame` with NL frame laws wired in: `Id`, `Mon`, `Succ`, `NE`, `Bo`, `Contra`, helper `Cut`; and compatibility laws `C_symm`, `C_coh`.
  * `Model` with truth-sets `tset`, satisfaction `Sat`, validity `Valid`.
* Handy `[simp]`/rewrites: `tset_*` for all connectives, `tset_inc_symm`, `tset_neg_neg`, `tset_conj_comm`.

### `NL/Soundness.lean` (sanity/regression)

* Fully mechanized semantic validity of all axioms 1.1–1.7 and rules R1 (MP), R2 (Adjunction) **for any frame** satisfying the NL laws in `Semantics.lean`.

### `NL/ProofSystem.lean` (Hilbert interface)

* Minimal class `NLProofSystem` exposing:

  * `Provable`
  * meta-rules `mp`, `adj`
  * axiom schemata `ax11`..`ax17` matching 1.1–1.7.

### `NL/Lindenbaum.lean` (worlds + witnesses) — **completed**

* Local derivability `Derives Γ A` (provables + hypotheses + MP + Adj) with monotonicity and `finite_support`.
* Chain lemmas:

  * `union_closed_of_chain` and `union_consistent_of_chain` (no admits).
* Zorn step:

  * `exists_maximal_closed_consistent` (closed, consistent, ⊇ Γ₀, maximal).
* Full Lindenbaum extension:

  * `extend_to_world` producing a **World**: closed, consistent, negation-complete and exclusive.
* Detachment machinery for the canonical conditional:

  * `Fset Γ A` (the detachment set of worlds),
  * `F_nonempty` (nonemptiness),
  * `detachment_witness` (if `(A →ₗ B) ∉ Γ` then ∃Δ ∈ F_Γ(A) with `B ∉ Δ`).

> These lemmas are the backbone of NE, Bo, the conditional monotonicity proof on truth-sets, and the Truth Lemma → completeness pipeline.

### `NL/Canonical.lean` (canonical model, laws, truth lemma, completeness) — **completed**

* Canonical worlds/valuation:

  * `WCan α` (a set with its `World` certificate),
  * `Vcan`, `Canonical.tsetCan`.
* Canonical selection/compatibility:

  * `Fcan` (detachment as sets of canonical worlds),
  * `fcan` (selection restricted to truth-sets; identity off them),
  * `Ccan` (witnessed, symmetry-friendly compatibility).
* Canonical frame/model:

  * `frameCan` implements **all** NL frame fields: `Id`, `Mon` (on truth-sets, via witness-contradiction), `Succ`, `NE`, `Bo` (via `detachment_witness`), `Contra` (semantic use of axiom 1.7), `Cut`, `C_symm`, `C_coh` (via axiom 1.4).
  * `modelCan`.
* **Truth Lemma** (structural induction, all cases closed).
* **Completeness**: `Model.Valid A → Provable A` (strong completeness for the listed Hilbert system).

### `NL/Examples.lean` (placeholder)

* Tiny scaffold showing how to build a concrete `Frame`. Ready to host regression/countermodel snippets.

### `NL/Utils.lean` (optional helpers)

* Still contains light automation helpers if you kept it (`valid_imp_preserves_truth`, `valid_eqv_truthset_eq`). Nothing changes here.

---

## What to do next (and where)

#### 1) Regression frames & countermodels — `NL/Examples.lean`

Goal: exhibit that each frame law is **needed**.

* Build tiny finite frames witnessing:

  * Drop **NE** ⇒ force a model where Boethius fails (get `(A→B)` true vacuously while also `f[[B]] ⊆ [[¬A]]`).
  * Drop **Cut** (or weaken Mon) ⇒ break axiom **1.5**.
  * Drop **Contra** ⇒ break axiom **1.7**.
* Add `#eval`/`#check`-style smoke tests that the canonical model validates 1.1–1.7 by `Model.Valid` (just for peace of mind, soundness already covers this).

#### 2) Developer UX polish — `NL/Semantics.lean`, `NL/Canonical.lean`

* Add a couple more `[simp]` facts to trim proof noise (harmless but nice):

  * `@[simp]` for `Canonical.tsetCan` membership,
  * small extensionality facts for `WCan`.
* Tighten comments around the `Mon` proof to point future readers to the “detachment-witness” technique we used to avoid circular reliance on the Truth Lemma.

#### 3) Optional intensional variant of `◦` — new file `NL/IntensionalCirc.lean`

* Define the “intensional” reading:

  ```
  C_intensional w X Y :⇔ ¬(f w X ⊆ Yᶜ) ∧ ¬(f w Y ⊆ Xᶜ)
  ```
* Show it satisfies `C_symm` and `C_coh` (given NE), and re-run the soundness of 1.2, 1.4 automatically.
* (Optional) Prove that the Hilbert list 1.1–1.7 is still sound & complete **if** you swap `C_coh` for the biconditional definition and keep `NE` (the spec mentions this).

#### 4) CI & docs

* Add a short doc-comment block at the top of each file summarizing the invariants for quick onboarding.
* Set up a minimal CI job that builds the project and runs a tiny example script (e.g., `lean --make NL` and a `#eval` block in `Examples.lean`).

#### 5) Nice-to-haves (future work)

* Derived proof rules (e.g., a library of NL theorems) in a new `NL/Derived.lean`, proven once against `ProofSystem.NLProofSystem`.
* Explore compactness/finite model property for the selection+compatibility frames (not required for the NL result, but interesting).
* A small “model checker” for finite frames: given a finite `W` with `f`/`C`, decide truth of a closed formula (handy for pedagogy).

---

## TL;DR

* **Core semantics** + **soundness** are stable.
* **Lindenbaum**, **canonical model**, **Truth Lemma**, and **completeness** are **all proved** (no admits).
* Next up: add **finite countermodels** in `Examples.lean`, optional **intensional `◦`** variant, and light **dev polish/CI**.