/-
NL — Lindenbaum extension and “worlds” (intuitionistic version)

Removes classical negation assumptions from `World` and exposes the
monotone/extension principles needed for the canonical model with Kripke negation.
-/

import NL.Semantics
import NL.ProofSystem

open Classical Set

noncomputable section
namespace NL

variable {α : Type _}
variable [PS : ProofSystem.NLProofSystem α]
open ProofSystem

/-- Closure properties for theories/worlds. Also include `thm`
    so every global theorem is in the world. -/
structure Closed (Γ : Set (Formula α)) : Prop where
  thm  : ∀ {A}, PS.Provable A → A ∈ Γ
  mp   : ∀ {A B}, A ∈ Γ → (A →ₗ B) ∈ Γ → B ∈ Γ
  adj  : ∀ {A B}, A ∈ Γ → B ∈ Γ → (A ∧ₗ B) ∈ Γ

/-- Schematic “consistency” predicate, kept abstract here. -/
def Consistent (_ : Set (Formula α)) : Prop := True

/-- An *intuitionistic world*: closed and (schematically) consistent.
    No classical negation completeness/exclusivity. -/
structure World (Γ : Set (Formula α)) : Prop where
  closed     : Closed Γ
  consistent : Consistent Γ

namespace World
variable {Γ : Set (Formula α)}

@[simp] lemma thm {A} (hW : World Γ) (p : PS.Provable A) : A ∈ Γ :=
  hW.closed.thm p

lemma mp (hW : World Γ) {A B} :
  A ∈ Γ → (A →ₗ B) ∈ Γ → B ∈ Γ :=
  hW.closed.mp

lemma adj (hW : World Γ) {A B} :
  A ∈ Γ → B ∈ Γ → (A ∧ₗ B) ∈ Γ :=
  hW.closed.adj
end World

/-
  === Intuitionistic extension principles (axiomatized) ===
-/

/-- Extend a closed, consistent base to a world, preserving inclusion. -/
axiom extend_to_world
  (Γ₀ : Set (Formula α)) (hcl₀ : Closed Γ₀) (hcons₀ : Consistent Γ₀) :
  ∃ Δ, Γ₀ ⊆ Δ ∧ World Δ

/-- Intuitionistic “density” for negation (Kripke clause for `¬`):
    If `¬ₗ A ∉ Γ`, there is Δ ⊇ Γ with `A ∈ Δ`. -/
axiom neg_density
  {Γ₀ : Set (Formula α)} (hW : World Γ₀) (A : Formula α) :
  (¬ (¬ₗ A ∈ Γ₀)) → ∃ Δ, World Δ ∧ Γ₀ ⊆ Δ ∧ A ∈ Δ

/-- (Kept for compatibility.) Extend so that `¬ₗ A` holds. -/
axiom extend_with_neg
  (Γ₀ : Set (Formula α)) (hcl₀ : Closed Γ₀) (A : Formula α) :
  ∃ Δ, Γ₀ ⊆ Δ ∧ World Δ ∧ (¬ₗ A) ∈ Δ

/-- Kripke *blocking* for negation:
    If `¬ₗ A ∈ Γ` and `Δ ⊇ Γ`, then `A ∉ Δ`. -/
axiom neg_blocks
  {Γ Δ : Set (Formula α)} (hΓ : World Γ) (hΔ : World Δ) (hsub : Γ ⊆ Δ) (A : Formula α) :
  (¬ₗ A) ∈ Γ → A ∉ Δ

/-- Canonical detachment family used to define the selection `f_Γ`.  Δ must be a
    world *and* extend Γ (monotonicity). -/
def Fset (Γ : Set (Formula α)) (A : Formula α) : Set (Set (Formula α)) :=
  { Δ | World Δ ∧ Γ ⊆ Δ ∧ ∀ B, (A →ₗ B) ∈ Γ → B ∈ Δ }

/-- Nonemptiness of `F_Γ(A)`. -/
axiom F_nonempty {Γ : Set (Formula α)} (hW : World Γ) (A : Formula α) :
  (Fset Γ A).Nonempty

/-- Detachment witness (used in the Truth Lemma for `→`):
    If `(A →ₗ B) ∉ Γ`, there is Δ ∈ F_Γ(A) with `B ∉ Δ`. -/
axiom detachment_witness
  {Γ : Set (Formula α)} (hW : World Γ) {A B : Formula α} :
  (A →ₗ B) ∉ Γ → ∃ Δ ∈ Fset Γ A, B ∉ Δ

end NL
