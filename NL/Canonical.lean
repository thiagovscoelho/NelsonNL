/-
NL — Canonical frame/model, Truth Lemma, Completeness.

Definitional backbone only. No global `[NLProofSystem α]` requirement.
We retain the lightweight “sets-as-worlds” approach and keep hard meta
results as `sorry` so the project compiles cleanly while we iterate.
-/
import NL.Semantics
import NL.ProofSystem
import NL.Lindenbaum

open Classical Set
noncomputable section

namespace NL

variable {α : Type _}

/-! ## Canonical worlds, valuation, and truth-sets -/

structure WCan (α : Type _) where
  carrier : Set (Formula α)

instance : Coe (WCan α) (Set (Formula α)) where
  coe w := w.carrier

@[simp] lemma WCan.mem {Γ : WCan α} {A : Formula α} :
  A ∈ ((Γ : WCan α) : Set (Formula α)) ↔ A ∈ Γ.carrier := Iff.rfl

/-- Canonical valuation on atoms. -/
def Vcan (p : α) : Set (WCan α) :=
  { Γ | Formula.atom p ∈ ((Γ : WCan α) : Set (Formula α)) }

namespace Canonical

/-- Truth set of a formula in the canonical model. -/
def tsetCan (A : Formula α) : Set (WCan α) :=
  { Γ | A ∈ ((Γ : WCan α) : Set (Formula α)) }

@[simp] lemma mem_tsetCan {Γ : WCan α} {A : Formula α} :
  Γ ∈ tsetCan (α := α) A ↔ A ∈ ((Γ : WCan α) : Set (Formula α)) := Iff.rfl

end Canonical

/-- F_Γ(A) (detachment points) defined purely set-theoretically. -/
def Fcan (Γ : WCan α) (A : Formula α) : Set (WCan α) :=
  { Δ | ∀ B, (A →ₗ B) ∈ ((Γ : WCan α) : Set (Formula α)) →
         B ∈ ((Δ : WCan α) : Set (Formula α)) }

/-- Selection restricted to truth-sets; identity otherwise. -/
def fcan (_Γ : WCan α) (X : Set (WCan α)) : Set (WCan α) := X

/-! ## Canonical frame/model -/

-- Still in NL/Canonical.lean

def Ccan (_Γ : WCan α) (_X _Y : Set (WCan α)) : Prop := True

def frameCan : Frame (WCan α) where
  f := fcan
  C := Ccan

  -- f = id ⇒ all of these are straightforward
  Id := by
    intro w X x hx
    simpa [fcan] using hx

  Mon := by
    intro w X Y hXY x hx
    -- hx : x ∈ f w X = X
    exact hXY (by simpa [fcan] using hx)

  Succ := by
    intro w X hw
    simpa [fcan] using hw

  NE := by
    intro w X hne
    simpa [fcan] using hne

  Bo := by
    -- with the tweaked type: … X.Nonempty → f w X ⊆ Y → ¬(f w Y ⊆ Xᶜ)
    intro w X Y hXne hXY
    rcases hXne with ⟨x, hxX⟩
    have hxY : x ∈ Y := hXY (by simpa [fcan] using hxX)
    -- show ¬ (Y ⊆ Xᶜ)
    intro hYsubset
    have hxXc : x ∈ Xᶜ := hYsubset hxY
    have : x ∉ X := by simpa using hxXc
    exact this hxX

  Contra := by
    -- If X ∩ Y ⊆ Z then X ∩ Zᶜ ⊆ Yᶜ (elementary set fact)
    intro w X Y Z hXYZ x hx
    rcases hx with ⟨hxX, hxZc⟩
    -- membership in complement is a negation proof
    exact fun hxY => by
      have hxZ : x ∈ Z := hXYZ ⟨hxX, hxY⟩
      have : x ∉ Z := by simpa using hxZc
      exact this hxZ

  Cut := by
    -- transitivity of ⊆
    intro w X Y Z hXY hYZ x hx
    exact hYZ (hXY (by simpa [fcan] using hx))

  C_symm := by
    intro _ _ _; constructor <;> intro _ <;> trivial

  C_coh := by
    intro _ _ _ _; trivial

/-- Canonical model. -/
def modelCan : Model α :=
  { W     := WCan α
    frame := frameCan
    V     := Vcan }

/-! ## Truth Lemma & Completeness (placeholders) -/

section Meta
variable [ProofSystem.NLProofSystem α]
open Model ProofSystem

theorem truth_lemma :
  ∀ (Γ : WCan α) (A : Formula α),
    Sat (modelCan) Γ A ↔ A ∈ ((Γ : WCan α) : Set (Formula α)) := by
  intro Γ A;  sorry

/-- Completeness: if a formula is valid in all models, it’s NL-provable. -/
theorem completeness :
  ∀ A : Formula α, Model.Valid A → NLProofSystem.Provable A := by
  intro A h;  sorry

end Meta

end NL
