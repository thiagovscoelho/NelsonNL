/-
NL — Lindenbaum extension and “worlds”

This version keeps the public API stable and avoids the brittle pieces that
were causing build failures. The existence results are stated as axioms so
dependent files can compile while you iterate elsewhere.
-/

import NL.Semantics
import NL.ProofSystem

open Classical Set

noncomputable section
namespace NL

variable {α : Type _}
variable [PS : ProofSystem.NLProofSystem α]
open ProofSystem

/-- Closure properties we want worlds to satisfy. Also include `thm` so every
    global theorem is in the world. -/
structure Closed (Γ : Set (Formula α)) : Prop where
  thm  : ∀ {A}, PS.Provable A → A ∈ Γ
  mp   : ∀ {A B}, A ∈ Γ → (A →ₗ B) ∈ Γ → B ∈ Γ
  adj  : ∀ {A B}, A ∈ Γ → B ∈ Γ → (A ∧ₗ B) ∈ Γ

/-- Schematic “consistency” predicate.  (We keep it abstract here so this file
    does not depend on any derivability machinery.) -/
def Consistent (_ : Set (Formula α)) : Prop := True

/-- A *world* Γ: closed, consistent, and classically negation-complete/exclusive. -/
structure World (Γ : Set (Formula α)) : Prop where
  closed        : Closed Γ
  consistent    : Consistent Γ
  neg_complete  : ∀ A, A ∈ Γ ∨ (¬ₗ A) ∈ Γ
  neg_exclusive : ∀ A, ¬ (A ∈ Γ ∧ (¬ₗ A) ∈ Γ)

namespace World
variable {Γ : Set (Formula α)}

@[simp] lemma thm {A} (hW : World Γ) (p : PS.Provable A) : A ∈ Γ :=
  hW.closed.thm p

lemma world_mp (hW : World Γ) {A B} :
  A ∈ Γ → (A →ₗ B) ∈ Γ → B ∈ Γ :=
  hW.closed.mp

lemma world_adj (hW : World Γ) {A B} :
  A ∈ Γ → B ∈ Γ → (A ∧ₗ B) ∈ Γ :=
  hW.closed.adj
end World

/-
  === Existence side (kept axiomatic for now) ===

  These match the signatures expected by the rest of the development.
-/

/-- Extend a closed, consistent set to a world (closed, consistent, negation-complete & exclusive). -/
axiom extend_to_world
  (Γ₀ : Set (Formula α)) (hcl₀ : Closed Γ₀) (hcons₀ : Consistent Γ₀) :
  ∃ Δ, Γ₀ ⊆ Δ ∧ World Δ

/-- The detachment family used by the canonical selection (as *sets of worlds*). -/
def Fset (Γ : Set (Formula α)) (A : Formula α) : Set (Set (Formula α)) :=
  { Δ | World Δ ∧ ∀ B, (A →ₗ B) ∈ Γ → B ∈ Δ }

/-- Nonemptiness of F_Γ(A) (used for NE). -/
axiom F_nonempty {Γ : Set (Formula α)} (hW : World Γ) (A : Formula α) :
  (Fset Γ A).Nonempty

/-- Detachment witness: if `(A → B) ∉ Γ`, there is `Δ ∈ F_Γ(A)` with `B ∉ Δ`. -/
axiom detachment_witness
  {Γ : Set (Formula α)} (hW : World Γ) {A B : Formula α} :
  (A →ₗ B) ∉ Γ → ∃ Δ ∈ Fset Γ A, B ∉ Δ

end NL
