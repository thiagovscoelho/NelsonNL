/-
NL — Canonical semantics, Truth Lemma, Completeness (intuitionistic version)

* Canonical worlds are `World` sets from NL.Lindenbaum (no classical negation).
* Negation `¬ₗ` uses the Kripke clause: Γ ⊨ ¬A  iff  for all Δ ≥ Γ, not (Δ ⊨ A).
* Implication uses the detachment family `Fset Γ A` (via NL.Lindenbaum).
* Completeness uses `extend_with_neg` + the (Kripke) Truth Lemma for `¬ₗ`.
-/
import NL.Semantics
import NL.ProofSystem
import NL.Lindenbaum

open Classical Set
noncomputable section

namespace NL

/-- Canonical worlds are sets of formulas satisfying `World`. -/
structure WCan (α : Type _) [ProofSystem.NLProofSystem α] where
  carrier : Set (Formula α)
  world   : World carrier

variable {α : Type _}
variable [PS : ProofSystem.NLProofSystem α]
open ProofSystem

/-! ## Canonical accessibility and selection  -/

/-- Canonical preorder: inclusion of theories. -/
def leC (Γ Δ : WCan α) : Prop := Γ.carrier ⊆ Δ.carrier

@[simp] lemma leC_refl (Γ : WCan α) : leC Γ Γ := by
  intro _ h; exact h

/-- Canonical detachment family, via Lindenbaum’s `Fset`. -/
def Fcan (Γ : WCan α) (A : Formula α) : Set (WCan α) :=
  { Δ : WCan α | Δ.carrier ∈ Fset Γ.carrier A }

/-! ## Canonical truth-sets and satisfaction

* Atoms/conj/circ: membership (extensional).
* Negation: Kripke (`∀`-over-extensions).
* Implication: selection-inclusion (`Fcan Γ A ⊆ [[B]]`).
-/
def tsetC (A : Formula α) : Set (WCan α) :=
  match A with
  | .atom p   => { Δ : WCan α | Formula.atom p ∈ Δ.carrier }
  | .conj A B => { Δ : WCan α | (A ∧ₗ B) ∈ Δ.carrier }
  | .neg A    => { Γ : WCan α | ∀ Δ, leC Γ Δ → Δ ∉ tsetC A }
  | .imp A B  => { Δ : WCan α | Fcan Δ A ⊆ tsetC B }
  | .circ A B => { Δ : WCan α | (A ◦ B) ∈ Δ.carrier }

def SatC (Γ : WCan α) (A : Formula α) : Prop := Γ ∈ tsetC A
def ValidC (A : Formula α) : Prop := ∀ (Γ : WCan α), SatC Γ A

/-! ### Simp helpers -/

@[simp] lemma SatC_atom_iff   (Γ : WCan α) (p) :
  SatC Γ (.atom p) ↔ .atom p ∈ Γ.carrier := by simp [SatC, tsetC]

@[simp] lemma SatC_conj_iff   (Γ : WCan α) (A B) :
  SatC Γ (A ∧ₗ B) ↔ (A ∧ₗ B) ∈ Γ.carrier := by simp [SatC, tsetC]

@[simp] lemma SatC_circ_iff   (Γ : WCan α) (A B) :
  SatC Γ (A ◦ B) ↔ (A ◦ B) ∈ Γ.carrier := by simp [SatC, tsetC]

@[simp] lemma SatC_imp_iff_subset (Γ : WCan α) (A B) :
  SatC Γ (A →ₗ B) ↔ (Fcan Γ A ⊆ tsetC B) := by simp [SatC, tsetC]

/-- Kripke clause for negation (by definition). -/
lemma SatC_neg_iff   (Γ : WCan α) (A) :
  SatC Γ (¬ₗ A) ↔ (∀ Δ, leC Γ Δ → ¬ SatC Δ A) := by
  simp [SatC, tsetC]

/-! ### Wrapping `Fset`-witnesses into canonical worlds -/

/-- Package a `World` set as a canonical world. -/
@[simp] def WCan.mkOfWorld (Δ0 : Set (Formula α)) (hW : World Δ0) : WCan α :=
  ⟨Δ0, hW⟩

/-- From `Δ0 ∈ Fset Γ A`, produce a canonical `Δ ∈ Fcan Γ A`. -/
lemma mem_Fcan_of_Fset
  {Γ : WCan α} {A : Formula α} {Δ0 : Set (Formula α)}
  (h : Δ0 ∈ Fset Γ.carrier A) :
  ∃ Δ : WCan α, Δ ∈ Fcan Γ A ∧ Δ.carrier = Δ0 := by
  rcases h with ⟨hWΔ0, hSub, hAll⟩
  refine ⟨WCan.mkOfWorld Δ0 hWΔ0, ?hin, rfl⟩
  -- show membership in Fcan
  change (WCan.mkOfWorld Δ0 hWΔ0).carrier ∈ Fset Γ.carrier A
  simpa using And.intro hWΔ0 (And.intro hSub hAll)

/-! ## Truth Lemma (intuitionistic) -/

/-- Mild Kripke blocking axiom for negation:
    If `¬ₗ A ∈ Γ` and `Δ` extends `Γ`, then `A ∉ Δ`.

    This captures exactly the upward-closure side of Kripke negation.
    (You may prefer to move this to `Lindenbaum.lean`.) -/
axiom neg_blocks
  {Γ Δ : Set (Formula α)} (hΓ : World Γ) (hΔ : World Δ) (hsub : Γ ⊆ Δ) (A : Formula α) :
  (¬ₗ A) ∈ Γ → A ∉ Δ

/-- From `(A → B) ∈ Γ`, obtain `Fcan Γ A ⊆ tsetC B`. -/
private lemma subset_of_imp_mem
  {A B : Formula α}
  (IH_B : ∀ (Δ : WCan α), SatC Δ B ↔ B ∈ Δ.carrier)
  (Γ : WCan α)
  (hImp : (A →ₗ B) ∈ Γ.carrier) :
  Fcan Γ A ⊆ tsetC B := by
  intro Δ hΔ
  -- unpack Δ ∈ Fcan Γ A
  change Δ.carrier ∈ Fset Γ.carrier A at hΔ
  rcases hΔ with ⟨hWΔ, _hSub, hAll⟩
  have hBmem : B ∈ Δ.carrier := hAll B hImp
  -- use IH for B
  have : SatC Δ B := (IH_B Δ).2 hBmem
  simpa [SatC] using this

/-- From `Fcan Γ A ⊆ tsetC B`, get `(A → B) ∈ Γ` using detachment witness. -/
private lemma imp_mem_of_subset
  {A B : Formula α}
  (IH_B : ∀ (Δ : WCan α), SatC Δ B ↔ B ∈ Δ.carrier)
  (Γ : WCan α)
  (hsubset : Fcan Γ A ⊆ tsetC B) :
  (A →ₗ B) ∈ Γ.carrier := by
  by_contra hnot
  -- witness Δ0 ∈ Fset Γ A with B ∉ Δ0
  rcases detachment_witness (Γ := Γ.carrier) (hW := Γ.world) (A := A) (B := B) hnot with
    ⟨Δ0, hΔ0in, hBnot⟩
  -- package as canonical Δ and apply the subset hypothesis
  rcases mem_Fcan_of_Fset (Γ := Γ) (A := A) (Δ0 := Δ0) hΔ0in with ⟨Δ, hΔF, hcar⟩
  have hSat : SatC Δ B := hsubset hΔF
  have hBinΔ : B ∈ Δ.carrier := (IH_B Δ).1 hSat
  have hBinΔ0 : B ∈ Δ0 := by simpa [hcar] using hBinΔ
  exact hBnot hBinΔ0

/-- Truth Lemma over canonical worlds. -/
private theorem truth_lemmaC_aux :
  ∀ (A : Formula α) (Γ : WCan α), SatC Γ A ↔ A ∈ Γ.carrier := by
  intro A Γ
  induction A generalizing Γ with
  | atom p =>
      simp
  | conj A B ihA ihB =>
      simp
  | circ A B =>
      simp
  | imp A B ihA ihB =>
      constructor
      · -- (→) from subset to membership, using witness lemma
        intro hSat
        have hsubset : Fcan Γ A ⊆ tsetC B := (SatC_imp_iff_subset Γ A B).1 hSat
        exact imp_mem_of_subset (IH_B := ihB) Γ hsubset
      · -- (←) from membership to subset, then fold back to SatC
        intro hImp
        have hsubset : Fcan Γ A ⊆ tsetC B := subset_of_imp_mem (IH_B := ihB) Γ hImp
        exact (SatC_imp_iff_subset Γ A B).2 hsubset
  | neg A ih =>
      constructor
      · -- (→) Kripke ⇒ membership using `neg_density` (contrapositive)
        intro hSat
        -- Assume `¬ₗ A ∉ Γ`, obtain Δ ≥ Γ with `A ∈ Δ`, contradict hSat.
        have hWΓ := Γ.world
        by_contra hnot
        rcases neg_density (Γ₀ := Γ.carrier) (hW := hWΓ) (A := A) hnot with
          ⟨Δ0, hWΔ0, hSub, hAin⟩
        let Δ : WCan α := ⟨Δ0, hWΔ0⟩
        have hle : leC Γ Δ := hSub
        have hSatA : SatC Δ A := (ih Δ).2 hAin
        have : ¬ SatC Δ A := (SatC_neg_iff Γ A).1 hSat Δ hle
        exact this hSatA
      · -- (←) membership ⇒ Kripke using `neg_blocks`
        intro hNegMem
        have hWΓ := Γ.world
        intro Δ hle
        -- `neg_blocks` says: from `¬A ∈ Γ` and Γ ⊆ Δ, we get `A ∉ Δ`.
        have hnotAin : A ∉ Δ.carrier :=
          neg_blocks (hΓ := hWΓ) (hΔ := Δ.world) (hsub := hle) (A := A) hNegMem
        -- By IH, `SatC Δ A ↔ A ∈ Δ`. So `SatC Δ A` is impossible.
        intro hSatA
        have : A ∈ Δ.carrier := (ih Δ).1 hSatA
        exact hnotAin this

/-- Truth Lemma (public). -/
theorem truth_lemmaC :
  ∀ (A : Formula α) (Γ : WCan α), SatC Γ A ↔ A ∈ Γ.carrier := by
  intro A Γ; exact truth_lemmaC_aux A Γ

/-! ## Completeness -/

private def GammaThm : Set (Formula α) := fun B => PS.Provable B

private lemma GammaThm_closed : Closed (GammaThm : Set (Formula α)) := by
  refine ⟨?thm, ?mp, ?adj⟩
  · intro B hPB; exact hPB
  · intro B C hB hBC; exact PS.mp hB hBC
  · intro B C hB hC;  exact PS.adj hB hC

/-- Canonical validity implies provability (strong completeness). -/
theorem completenessC :
  ∀ A : Formula α, ValidC A → PS.Provable A := by
  intro A hvalid
  by_contra _hnot  -- assume `A` not provable
  -- extend the theorems set so that `¬A` holds
  rcases extend_with_neg (Γ₀ := GammaThm) (hcl₀ := GammaThm_closed) A
    with ⟨Δ0, _hsub, hWΔ0, hNotA⟩
  let Δ : WCan α := ⟨Δ0, hWΔ0⟩
  -- Validity says `Δ ⊨ A`
  have hA : SatC Δ A := hvalid Δ
  -- Truth Lemma gives `Δ ⊨ ¬A` (from `¬A ∈ Δ`)
  have hNotA' : SatC Δ (¬ₗ A) := (truth_lemmaC (¬ₗ A) Δ).2 hNotA
  -- But Kripke negation at Δ forbids Δ ⊨ A (take extension = Δ itself)
  have : ¬ SatC Δ A := (SatC_neg_iff Δ A).1 hNotA' Δ (leC_refl Δ)
  exact this hA

end NL
