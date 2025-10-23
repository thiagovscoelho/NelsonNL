/-
NL — Semantics core
* Defines Frame/Model and truth-clauses only.
* NO proof-system interface and NO soundness theorems here.
* Keep this file tiny; everything else imports it.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import NL.Language

open Classical Set
noncomputable section

universe u v

namespace NL

/-- Intuitionistic (Kripke) negation at the set level for an arbitrary preorder `le`.
`iNeg le X` is the set of worlds whose upward cone avoids `X`.

Important: make the world universe explicit to avoid unsolved universe metas. -/
def iNeg {W : Type v} (le : W → W → Prop) (X : Set W) : Set W :=
  { w | ∀ v', le w v' → v' ∉ X }

/-! ## Frames and models -/

/-- An NL-frame on a set of worlds `W` (universe `v`).

* `le` is the intuitionistic accessibility (a preorder: reflexive & transitive).
* `f w X` is the set of “relevantly `X`-worlds at `w`” when we check `A → B`.
* `C w X Y` is a primitive compatibility/consistency predicate used to interpret `A ◦ B`.

The fields encode the NL frame conditions from the spec:
`Id`, `Her`, `Succ`, `Contra` for the conditional; symmetry and coherence for `C`;
`C_her` so that `◦` is upward persistent; and `Cut` (Hypothetical Syllogism),
which immediately validates axiom 1.5 (stronger than the guarded version, but compatible with NL).
-/
structure Frame (W : Type v) where
  -- Intuitionistic accessibility
  le       : W → W → Prop
  le_refl  : ∀ w, le w w
  le_trans : ∀ {w x y}, le w x → le x y → le w y
  -- Semantics of → and ◦
  f        : W → Set W → Set W
  C        : W → Set W → Set W → Prop
  -- Conditional laws
  Id       : ∀ (w : W) (X : Set W), f w X ⊆ X
  Her      : ∀ {w x : W} (X : Set W), le w x → f x X ⊆ f w X
  Succ     : ∀ (w : W) (X : Set W), w ∈ X → w ∈ f w X
  Contra   : ∀ (w : W) (X Y Z : Set W),
               f w (X ∩ Y) ⊆ Z → f w (X ∩ iNeg le Z) ⊆ iNeg le Y
  -- Compatibility laws
  C_symm   : ∀ (w : W) (X Y : Set W), C w X Y ↔ C w Y X
  C_coh    : ∀ (w : W) (X Y : Set W), f w X ⊆ Y → C w X Y
  -- Upward persistence for ◦
  C_her    : ∀ {w x : W} (X Y : Set W), le w x → C w X Y → C x X Y
  -- Strong hypothetical syllogism (Cut) for `f`
  Cut      : ∀ (w : W) (X Y Z : Set W), f w X ⊆ Y → f w Y ⊆ Z → f w X ⊆ Z

/-- An NL-model: a frame and a valuation of atoms **by up-sets** (persistence). -/
structure Model (α : Type u) where
  W     : Type v
  frame : Frame W
  V     : α → Set W
  -- Up-set valuation of atoms: if `w ∈ V p` and `w ≤ x`, then `x ∈ V p`.
  V_mono : ∀ (p : α) {w x : W}, w ∈ V p → frame.le w x → x ∈ V p

namespace Model

variable {α : Type u}

/-- Truth set. -/
def tset (M : Model.{u, v} α) : Formula α → Set M.W
| .atom p   => M.V p
| .conj A B => tset M A ∩ tset M B
| .neg A    => {w | ∀ x, M.frame.le w x → x ∉ tset M A}
| .imp A B  => {w | M.frame.f w (tset M A) ⊆ tset M B}
| .circ A B => {w | M.frame.C w (tset M A) (tset M B)}

/-- Satisfaction. -/
@[simp] def Sat (M : Model.{u, v} α) (w : M.W) (A : Formula α) : Prop :=
  w ∈ tset M A

/-- Semantic validity across **all** models/worlds (universes `u` and `v`). -/
def Valid (A : Formula α) : Prop :=
  ∀ (M : Model.{u, v} α) (w : M.W), Sat (M := M) w A

end Model

/-! ### Basic simp/utility lemmas used by Canonical/Truth Lemma -/

section Simps

variable {α : Type u}

@[simp] lemma tset_atom   (M : Model.{u, v} α) (p : α) :
  M.tset (.atom p) = M.V p := rfl

@[simp] lemma tset_conj   (M : Model.{u, v} α) (A B : Formula α) :
  M.tset (A ∧ₗ B) = M.tset A ∩ M.tset B := rfl

/-- Intuitionistic negation truth-set. -/
@[simp] lemma tset_neg    (M : Model.{u, v} α) (A : Formula α) :
  M.tset (¬ₗ A) = {w | ∀ x, M.frame.le w x → x ∉ M.tset A} := rfl

@[simp] lemma tset_imp    (M : Model.{u, v} α) (A B : Formula α) :
  M.tset (A →ₗ B) = {w | M.frame.f w (M.tset A) ⊆ M.tset B} := rfl

@[simp] lemma tset_circ   (M : Model.{u, v} α) (A B : Formula α) :
  M.tset (A ◦ B) = {w | M.frame.C w (M.tset A) (M.tset B)} := rfl

/-- Symmetry of inconsistency `(A|ₗB)` at the truth-set level. -/
lemma tset_inc_symm (M : Model.{u, v} α) (A B : Formula α) :
  M.tset (A |ₗ B) = M.tset (B |ₗ A) := by
  -- `A|ₗB` is `¬ₗ (A ◦ B)`. Unfold and use symmetry of `C` pointwise above each world.
  ext w; constructor
  · intro hw
    have : ∀ (x : M.W), M.frame.le w x → ¬ M.frame.C x (M.tset B) (M.tset A) := by
      intro x hwx
      have h1 : ¬ M.frame.C x (M.tset A) (M.tset B) := by
        simpa [Formula.inc, Model.tset] using hw x hwx
      intro hBA
      exact h1 ((M.frame.C_symm x (M.tset A) (M.tset B)).mpr hBA)
    simpa [Formula.inc, Model.tset] using this
  · intro hw
    have : ∀ (x : M.W), M.frame.le w x → ¬ M.frame.C x (M.tset A) (M.tset B) := by
      intro x hwx
      have h1 : ¬ M.frame.C x (M.tset B) (M.tset A) := by
        simpa [Formula.inc, Model.tset] using hw x hwx
      intro hAB
      exact h1 ((M.frame.C_symm x (M.tset A) (M.tset B)).mp hAB)
    simpa [Formula.inc, Model.tset] using this

/-- Upward persistence of truth for all formulas. -/
lemma persist (M : Model.{u, v} α) :
  ∀ (A : Formula α) {w x : M.W}, w ∈ M.tset A → M.frame.le w x → x ∈ M.tset A
| .atom p, w, x, hw, hwx =>
    M.V_mono p hw hwx
| .conj A B, w, x, hw, hwx =>
    by
      rcases hw with ⟨hA, hB⟩
      exact And.intro (persist M A hA hwx) (persist M B hB hwx)
| .neg A, w, x, hw, hwx =>
    by
      change (∀ u, M.frame.le w u → u ∉ M.tset A) at hw
      change (∀ t, M.frame.le x t → t ∉ M.tset A)
      intro t hxt
      apply hw t
      exact M.frame.le_trans hwx hxt
| .imp A B, w, x, hw, hwx =>
    by
      change M.frame.f w (M.tset A) ⊆ M.tset B at hw
      change M.frame.f x (M.tset A) ⊆ M.tset B
      intro y hy
      have hy' : y ∈ M.frame.f w (M.tset A) := (M.frame.Her (M.tset A) hwx) hy
      exact hw hy'
| .circ A B, w, x, hw, hwx =>
    by
      change M.frame.C w (M.tset A) (M.tset B) at hw
      change M.frame.C x (M.tset A) (M.tset B)
      exact M.frame.C_her (M.tset A) (M.tset B) hwx hw

/-- Kripke double-negation expansion: `⟦A⟧ ⊆ ⟦¬¬A⟧`. -/
lemma tset_subset_negneg (M : Model.{u, v} α) (A : Formula α) :
  M.tset A ⊆ M.tset (¬ₗ ¬ₗ A) := by
  intro w hwA
  change ∀ x, M.frame.le w x → x ∉ M.tset (¬ₗ A)
  intro x hwx
  have hxA : x ∈ M.tset A := persist M A hwA hwx
  intro hneg
  have : x ∉ M.tset A := by
    have h := hneg x (M.frame.le_refl x)
    exact h
  exact this hxA

/-- Conjunction truth-set commutes. -/
lemma tset_conj_comm (M : Model.{u, v} α) (A B : Formula α) :
  M.tset (A ∧ₗ B) = M.tset (B ∧ₗ A) := by
  ext w; simp [Model.tset, inter_comm]

end Simps

end NL
