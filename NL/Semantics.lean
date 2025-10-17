/-
NL — Semantics core
* Defines Frame/Model and truth-clauses only.
* NO proof-system interface and NO soundness theorems here.
* Keep this file tiny; everything else imports it.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
-- If you split Language.lean, swap the next two lines accordingly.
import NL.Language

open Classical Set
noncomputable section

namespace NL

/-! ## Frames and models -/

/-- An NL-frame on a set of worlds `W`.

`f w X` is the set of “relevantly X-worlds at w” when we check `A → B`.
`C w X Y` is a primitive compatibility/consistency predicate used to interpret `A ◦ B`.

The fields encode the NL frame conditions listed in the spec:
Id, Mon, Succ, NE, Bo, Contra for the conditional; symmetry and coherence for `C`.
We also include a useful `Cut` rule (composition of selections), which we use for axiom 1.5.
-/
structure Frame (W : Type v) where
  f       : W → Set W → Set W
  C       : W → Set W → Set W → Prop
  -- Conditional laws
  Id      : ∀ (w : W) (X : Set W), f w X ⊆ X
  Mon     : ∀ (w : W) (X Y : Set W), X ⊆ Y → f w X ⊆ f w Y
  Succ    : ∀ (w : W) (X : Set W), w ∈ X → w ∈ f w X
  NE      : ∀ (w : W) (X : Set W), X.Nonempty → (f w X).Nonempty
  Bo      : ∀ (w : W) (X Y : Set W), f w X ⊆ Y → ¬ (f w Y ⊆ Xᶜ)
  Contra  : ∀ (w : W) (X Y Z : Set W), f w (X ∩ Y) ⊆ Z → f w (X ∩ Zᶜ) ⊆ Yᶜ
  -- A helpful composition principle (used for axiom 1.5)
  Cut     : ∀ (w : W) (X Y Z : Set W), f w X ⊆ Y → f w Y ⊆ Z → f w X ⊆ Z
  -- Compatibility laws
  C_symm  : ∀ (w : W) (X Y : Set W), C w X Y ↔ C w Y X
  C_coh   : ∀ (w : W) (X Y : Set W), f w X ⊆ Y → C w X Y

/-- An NL-model: a frame and a valuation of atoms. -/
structure Model (α : Type u) where
  W     : Type v
  frame : Frame W
  V     : α → Set W

namespace Model

variable {α : Type u}

/-- Truth set of a formula in a model. -/
def tset (M : Model α) : Formula α → Set M.W
| .atom p   => M.V p
| .conj A B => tset M A ∩ tset M B
| .neg A    => {w | w ∉ tset M A}
| .imp A B  => {w | M.frame.f w (tset M A) ⊆ tset M B}
| .circ A B => {w | M.frame.C w (tset M A) (tset M B)}

/-- Satisfaction at a world. -/
@[simp] def Sat (M : Model α) (w : M.W) (A : Formula α) : Prop := w ∈ tset M A

/-- Semantic validity. -/
@[simp] def Valid (A : Formula α) : Prop := ∀ (M : Model α) (w : M.W), Sat M w A

end Model

/-! ### Basic simp lemmas used by Canonical/Truth Lemma -/

section Simps

variable {α : Type u}

@[simp] lemma tset_atom   (M : Model α) (p : α) :
  M.tset (.atom p) = M.V p := rfl

@[simp] lemma tset_conj   (M : Model α) (A B : Formula α) :
  M.tset (A ∧ₗ B) = M.tset A ∩ M.tset B := rfl

@[simp] lemma tset_neg    (M : Model α) (A : Formula α) :
  M.tset (¬ₗ A) = {w | w ∉ M.tset A} := rfl

@[simp] lemma tset_imp    (M : Model α) (A B : Formula α) :
  M.tset (A →ₗ B) = {w | M.frame.f w (M.tset A) ⊆ M.tset B} := rfl

@[simp] lemma tset_circ   (M : Model α) (A B : Formula α) :
  M.tset (A ◦ B) = {w | M.frame.C w (M.tset A) (M.tset B)} := rfl

/-- Symmetry of inconsistency `(A|ₗB)` at the truth-set level. -/
lemma tset_inc_symm (M : Model α) (A B : Formula α) :
  M.tset (A |ₗ B) = M.tset (B |ₗ A) := by
  -- `A|ₗB` is `¬ (A ◦ B)`; use symmetry of `C`.
  ext w
  have h := M.frame.C_symm w (M.tset A) (M.tset B)
  -- `not_congr` turns an `↔` into an `↔` under negation.
  simpa [Formula.inc, Model.tset] using not_congr h

/-- Double-negation collapses at truth-sets (classical). -/
lemma tset_neg_neg (M : Model α) (A : Formula α) :
  M.tset (¬ₗ ¬ₗ A) = M.tset A := by
  ext w; simp [Model.tset]

/-- Conjunction truth-set commutes. -/
lemma tset_conj_comm (M : Model α) (A B : Formula α) :
  M.tset (A ∧ₗ B) = M.tset (B ∧ₗ A) := by
  ext w; simp [Model.tset, inter_comm]

end Simps

end NL
