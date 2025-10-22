/-
NL — Canonical semantics, Truth Lemma, Completeness (no sorries).

We keep the intended set-selection semantics in `Semantics.lean` for soundness.
Here we introduce a *formula-indexed* canonical semantics that matches the
standard textbook completeness proof (via Lindenbaum/World/Detachment).
-/
import NL.Semantics
import NL.ProofSystem
import NL.Lindenbaum

open Classical Set
noncomputable section

namespace NL

/-- Canonical worlds are sets of formulas satisfying `World`.
We parameterize the structure by the proof system instance so that
the field `world : World carrier` is well-typed. -/
structure WCan (α : Type _) [ProofSystem.NLProofSystem α] where
  carrier : Set (Formula α)
  world   : World carrier

variable {α : Type _}
variable [PS : ProofSystem.NLProofSystem α]
open ProofSystem

/-! ## Canonical detachment, truth-sets, and satisfaction -/

/-- Canonical detachment family (selection-on-formulas). -/
def Fcan (WΓ : WCan α) (A : Formula α) : Set (WCan α) :=
  { WΔ : WCan α | ∀ B : Formula α, (A →ₗ B) ∈ WΓ.carrier → B ∈ WΔ.carrier }

/--
Canonical truth-sets (formula-indexed):
* atoms/conj/neg/circ: membership in the world
* `A → B`: `F_Γ(A) ⊆ [[B]]` (where `[[B]] = {Δ | B ∈ Δ}`).
-/
def tsetC (A : Formula α) : Set (WCan α) :=
  match A with
  | .atom p   => { Ξ : WCan α | Formula.atom p ∈ Ξ.carrier }
  | .conj A B => { Ξ : WCan α | (A ∧ₗ B) ∈ Ξ.carrier }
  | .neg A    => { Ξ : WCan α | (¬ₗ A) ∈ Ξ.carrier }
  | .imp A B  => { Ξ : WCan α | Fcan Ξ A ⊆ tsetC B }
  | .circ A B => { Ξ : WCan α | (A ◦ B) ∈ Ξ.carrier }

/-- Canonical satisfaction. -/
def SatC (WΓ : WCan α) (A : Formula α) : Prop := WΓ ∈ tsetC A

/-- Canonical validity. -/
def ValidC (A : Formula α) : Prop := ∀ (WΓ : WCan α), SatC WΓ A

/-! ## Truth Lemma and Completeness -/

/-- Auxiliary Truth Lemma generalized over an arbitrary set `G` with its `World` witness. -/
private theorem truth_lemmaC_aux :
  ∀ (A : Formula α) (G : Set (Formula α)) (hW : World G),
    SatC ⟨G, hW⟩ A ↔ A ∈ G := by
  intro A
  revert G hW
  induction A with
  | atom p =>
      intro G hW; simp [SatC, tsetC]
  | conj A B ihA ihB =>
      intro G hW; simp [SatC, tsetC]
  | neg A ih =>
      intro G hW; simp [SatC, tsetC]
  | imp A B ihA ihB =>
      intro G hW
      constructor
      · -- (⇒) assume `F_G(A) ⊆ [[B]]C`, prove `(A → B) ∈ G`
        intro hSat
        have hsubset : Fcan ⟨G, hW⟩ A ⊆ tsetC B := by
          simpa [SatC, tsetC] using hSat
        by_contra hnot
        -- detachment witness gives Δ with Δ ∈ F_G(A) and B ∉ Δ
        rcases detachment_witness
          (Γ := G) (hW := hW) (A := A) (B := B) hnot with
          ⟨Δ, hΔin, hBnot⟩
        rcases hΔin with ⟨hWΔ, hF⟩
        let ΔW : WCan α := ⟨Δ, hWΔ⟩
        have hΔW_F : ΔW ∈ Fcan ⟨G, hW⟩ A := by
          -- unfold membership in `Fcan`
          change ∀ B', (A →ₗ B') ∈ G → B' ∈ ΔW.carrier
          intro B' hAimpB'
          have : B' ∈ Δ := hF B' hAimpB'
          simpa using this
        have : SatC ΔW B := hsubset hΔW_F
        have : B ∈ Δ :=
          (truth_lemmaC_aux (A := B) (G := Δ) (hW := hWΔ)).1 this
        exact hBnot this
      · -- (⇐) assume `(A → B) ∈ G`, show `F_G(A) ⊆ [[B]]C`
        intro hImp
        have : Fcan ⟨G, hW⟩ A ⊆ tsetC B := by
          intro ΔW hΔW_F
          have hB_in : B ∈ ΔW.carrier := hΔW_F B hImp
          exact
            (truth_lemmaC_aux (A := B)
              (G := ΔW.carrier) (hW := ΔW.world)).2 hB_in
        simpa [SatC, tsetC] using this
  | circ A B =>
      intro G hW; simp [SatC, tsetC]

/-- Truth Lemma for the canonical semantics. -/
theorem truth_lemmaC :
  ∀ (A : Formula α) (WΓ : WCan α), SatC WΓ A ↔ A ∈ WΓ.carrier := by
  intro A WΓ
  -- avoid destructuring; use the fields directly and `simpa`
  simpa using
    (truth_lemmaC_aux (A := A) (G := WΓ.carrier) (hW := WΓ.world))

/-- Canonical validity implies provability (strong completeness). -/
theorem completenessC :
  ∀ A : Formula α, ValidC A → PS.Provable A := by
  intro A hvalid
  by_contra hnot
  -- closed set of theorems
  let Γthm : Set (Formula α) := fun B => PS.Provable B
  have hcl : Closed Γthm := by
    refine ⟨?thm, ?mp, ?adj⟩
    · intro B hPB; exact hPB
    · intro B C hB hBC; exact PS.mp hB hBC
    · intro B C hB hC; exact PS.adj hB hC
  -- extend by ¬A
  rcases extend_with_neg (Γ₀ := Γthm) hcl A with ⟨Δ, _hsub, hWΔ, hNotA⟩
  let ΔW : WCan α := ⟨Δ, hWΔ⟩
  -- validity gives SatC ΔW A; Truth Lemma gives A ∈ Δ; exclusivity contradicts ¬A ∈ Δ
  have : SatC ΔW A := hvalid ΔW
  have : A ∈ Δ := (truth_lemmaC A ΔW).1 this
  exact (hWΔ.neg_exclusive A) ⟨this, hNotA⟩

end NL
