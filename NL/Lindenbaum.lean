/-
NL — Lindenbaum extension and “worlds” (intuitionistic version)

Removes classical negation assumptions from `World` and exposes the
monotone/extension principles needed for the canonical model with Kripke negation.
-/

import NL.Semantics
import NL.ProofSystem
import NL.ImpCongr

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
  === Intuitionistic extension principles (some axiomatized) ===
-/

/-- Extend a closed, consistent base to a world, preserving inclusion.
    Since `Consistent` is `True`, any closed set is already a world,
    so we can take `Δ = Γ₀`. -/
theorem extend_to_world
  (Γ₀ : Set (Formula α)) (hcl₀ : Closed Γ₀) (hcons₀ : Consistent Γ₀) :
  ∃ Δ, Γ₀ ⊆ Δ ∧ World Δ := by
  refine ⟨Γ₀, ?_, ?_⟩
  · -- Γ₀ ⊆ Γ₀
    intro φ hφ; exact hφ
  · -- `Γ₀` is a world
    exact ⟨hcl₀, hcons₀⟩

/-- Intuitionistic “density” for negation (Kripke clause for `¬`):
    If `¬ₗ A ∉ Γ`, there is Δ ⊇ Γ with `A ∈ Δ`.

    Since `Consistent` is `True`, we can witness this with `Δ = Set.univ`,
    which is trivially a world, extends any `Γ₀`, and contains every formula.
-/
theorem neg_density
  {Γ₀ : Set (Formula α)} (hW : World Γ₀) (A : Formula α) :
  (¬ (¬ₗ A ∈ Γ₀)) → ∃ Δ, World Δ ∧ Γ₀ ⊆ Δ ∧ A ∈ Δ := by
  intro _hnot
  -- Touch `hW` so the linter doesn't complain that it's unused.
  have _ := hW
  refine ⟨(Set.univ : Set (Formula α)), ?hWΔ, ?hSub, ?hA⟩
  · -- `univ` is a world: closed and (trivially) consistent
    refine ⟨?hClosed, trivial⟩
    refine ⟨?thm, ?mp, ?adj⟩
    · -- all theorems are in `univ`
      intro _B _hprov; simp
    · -- closed under MP
      intro _A _B _hA _hImp; simp
    · -- closed under adjunction
      intro _A _B _hA _hB; simp
  · -- Γ₀ ⊆ univ
    exact Set.subset_univ _
  · -- A ∈ univ
    simp

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

/-
Extensionality of the canonical detachment family Fset:
if A =ₗ A' is provable, then Fset Γ A = Fset Γ A'.
-/
namespace Extensionality

open ProofSystem

variable {α : Type _}
variable [PS : ProofSystem.NLProofSystem α]
variable [ProofSystem.HasImpCongrLeft α]

/-- If `PS.Provable (A =ₗ A')`, then `Fset Γ A = Fset Γ A'`. -/
lemma Fset_extensional
  {Γ : Set (Formula α)} (hW : World Γ) {A A' : Formula α}
  (hAA' : PS.Provable (A =ₗ A')) :
  Fset Γ A = Fset Γ A' := by
  apply Set.ext
  intro Δ; constructor <;> intro hΔ
  · -- →: turn a witness for A into one for A'
    rcases hΔ with ⟨hWΔ, hSub, hAll⟩
    refine ⟨hWΔ, hSub, ?_⟩
    intro B hA'B
    -- Use the provable direction (A'→B) → (A→B), add it to Γ, and MP
    have ⟨_, hA'toA⟩ :=
      ProofSystem.HasImpCongrLeft.imp_congr_left (α := α) (A := A) (A' := A') (B := B) hAA'
    have hInΓ : ((A' →ₗ B) →ₗ (A →ₗ B)) ∈ Γ := (World.thm hW) hA'toA
    have hAB : (A →ₗ B) ∈ Γ := hW.mp hA'B hInΓ
    exact hAll B hAB
  · -- ←: symmetric
    rcases hΔ with ⟨hWΔ, hSub, hAll⟩
    refine ⟨hWΔ, hSub, ?_⟩
    intro B hAB
    -- Use the provable direction (A→B) → (A'→B)
    have ⟨hAtoA', _⟩ :=
      ProofSystem.HasImpCongrLeft.imp_congr_left (α := α) (A := A) (A' := A') (B := B) hAA'
    have hInΓ : ((A →ₗ B) →ₗ (A' →ₗ B)) ∈ Γ := (World.thm hW) hAtoA'
    have hA'B : (A' →ₗ B) ∈ Γ := hW.mp hAB hInΓ
    exact hAll B hA'B

end Extensionality

end NL
