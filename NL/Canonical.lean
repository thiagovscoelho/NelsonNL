/-
NL — Canonical semantics, Truth Lemma, Completeness (intuitionistic version)

* Canonical worlds are `World` sets from NL.Lindenbaum (no classical negation).
* Negation `¬ₗ` uses the Kripke clause: Γ ⊨ ¬A  iff  for all Δ ≥ Γ, not (Δ ⊨ A).
* Implication uses the detachment family `Fset Γ A` (via NL.Lindenbaum).
-/
import NL.Semantics
import NL.ProofSystem
import NL.ImpCongr
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
  change (WCan.mkOfWorld Δ0 hWΔ0).carrier ∈ Fset Γ.carrier A
  simpa using And.intro hWΔ0 (And.intro hSub hAll)

/-! ## Truth Lemma (intuitionistic) -/

/-- From `(A → B) ∈ Γ`, obtain `Fcan Γ A ⊆ tsetC B`. -/
private lemma subset_of_imp_mem
  {A B : Formula α}
  (IH_B : ∀ (Δ : WCan α), SatC Δ B ↔ B ∈ Δ.carrier)
  (Γ : WCan α)
  (hImp : (A →ₗ B) ∈ Γ.carrier) :
  Fcan Γ A ⊆ tsetC B := by
  intro Δ hΔ
  change Δ.carrier ∈ Fset Γ.carrier A at hΔ
  rcases hΔ with ⟨hWΔ, _hSub, hAll⟩
  have hBmem : B ∈ Δ.carrier := hAll B hImp
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
  rcases detachment_witness (Γ := Γ.carrier) (hW := Γ.world) (A := A) (B := B) hnot with
    ⟨Δ0, hΔ0in, hBnot⟩
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
      · intro hSat
        have hsubset : Fcan Γ A ⊆ tsetC B := (SatC_imp_iff_subset Γ A B).1 hSat
        exact imp_mem_of_subset (IH_B := ihB) Γ hsubset
      · intro hImp
        have hsubset : Fcan Γ A ⊆ tsetC B := subset_of_imp_mem (IH_B := ihB) Γ hImp
        exact (SatC_imp_iff_subset Γ A B).2 hsubset
  | neg A ih =>
      constructor
      · -- (→) Kripke ⇒ membership using `neg_density` (contrapositive)
        intro hSat
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
        have hnotAin : A ∉ Δ.carrier :=
          neg_blocks (hΓ := hWΓ) (hΔ := Δ.world) (hsub := hle) (A := A) hNegMem
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
  by_contra _hnot
  rcases extend_with_neg (Γ₀ := GammaThm) (hcl₀ := GammaThm_closed) A
    with ⟨Δ0, _hsub, hWΔ0, hNotA⟩
  let Δ : WCan α := ⟨Δ0, hWΔ0⟩
  have hA : SatC Δ A := hvalid Δ
  have hNotA' : SatC Δ (¬ₗ A) := (truth_lemmaC (¬ₗ A) Δ).2 hNotA
  have : ¬ SatC Δ A := (SatC_neg_iff Δ A).1 hNotA' Δ (leC_refl Δ)
  exact this hA

/-! ## Adequacy: canonical validity ⇔ provability -/

section Adequacy

variable {α : Type _}
variable [PS : ProofSystem.NLProofSystem α]
open ProofSystem

/-- Every theorem holds in every canonical world (hence is canonically valid). -/
theorem provable_validC (A : Formula α) :
  PS.Provable A → ValidC A := by
  intro hA Γ
  -- Theorems belong to every world Γ…
  have hmem : A ∈ Γ.carrier := (World.thm (Γ.world) hA)
  -- …and Truth Lemma turns membership into satisfaction.
  exact (truth_lemmaC A Γ).2 hmem

/-- Canonical adequacy: canonical validity if and only if provability. -/
theorem validC_iff_provable (A : Formula α) :
  ValidC A ↔ PS.Provable A :=
by
  constructor
  · -- completeness (already proved)
    exact fun h => completenessC A h
  · -- sound direction into canonical semantics
    exact fun h => provable_validC A h

end Adequacy


open ProofSystem

-- Extensionality of `Fcan` (depends on `Fset` extensionality proved in Lindenbaum)
section Extensionality

variable {α : Type _}
variable [PS : ProofSystem.NLProofSystem α]
variable [ProofSystem.HasImpCongrLeft α]

/-- If `PS.Provable (A =ₗ A')`, then `Fcan Γ A = Fcan Γ A'` for every canonical `Γ`. -/
lemma Fcan_extensional (Γ : WCan α) {A A' : Formula α}
  (hAA' : PS.Provable (A =ₗ A')) :
  Fcan Γ A = Fcan Γ A' := by
  -- Work elementwise; rewrite memberships to the underlying Fset
  apply Set.ext
  intro Δ
  constructor
  · intro h
    -- h : Δ ∈ Fcan Γ A
    change Δ.carrier ∈ Fset Γ.carrier A at h
    -- goal: Δ ∈ Fcan Γ A'
    change Δ.carrier ∈ Fset Γ.carrier A'
    have hF := NL.Extensionality.Fset_extensional
                 (α := α) (hW := Γ.world) (A := A) (A' := A') hAA'
    simpa [hF] using h
  · intro h
    -- h : Δ ∈ Fcan Γ A'
    change Δ.carrier ∈ Fset Γ.carrier A' at h
    -- goal: Δ ∈ Fcan Γ A
    change Δ.carrier ∈ Fset Γ.carrier A
    have hF := NL.Extensionality.Fset_extensional
                 (α := α) (hW := Γ.world) (A := A) (A' := A') hAA'
    simpa [hF] using h

end Extensionality

/-- ### Helpers for the canonical selection

Fcan Γ A ⊆ [[A]]: follows from axiom 1.1 in Γ (A → A) and `World.mp`. -/
lemma Fcan_subset_A {α} [PS : ProofSystem.NLProofSystem α]
  (Γ : WCan α) (A : Formula α) :
  Fcan Γ A ⊆ tsetC A := by
  intro Δ hΔ
  -- Δ ∈ Fcan Γ A means: Δ.carrier ∈ Fset Γ.carrier A
  change Δ.carrier ∈ Fset Γ.carrier A at hΔ
  rcases hΔ with ⟨hWΔ, hSub, hAll⟩
  -- axiom 1.1 : (A → A) ∈ Γ
  have hAA : (A →ₗ A) ∈ Γ.carrier := (World.thm Γ.world) (PS.ax11 A)
  -- then B := A gives A ∈ Δ
  have hAinΔ : A ∈ Δ.carrier := hAll A hAA
  -- Truth Lemma: membership ↔ canonical truth
  exact (truth_lemmaC A Δ).2 hAinΔ

/-- Base monotonicity: if Γ ≤ Γ' then Fcan Γ' A ⊆ Fcan Γ A. -/
lemma Fcan_mono_base {α} [PS : ProofSystem.NLProofSystem α]
  {Γ Γ' : WCan α} (hle : leC Γ Γ') (A : Formula α) :
  Fcan Γ' A ⊆ Fcan Γ A := by
  intro Δ hΔ
  change Δ.carrier ∈ Fset Γ'.carrier A at hΔ
  rcases hΔ with ⟨hWΔ, hSub', hAll'⟩
  -- Γ ⊆ Γ' ⊆ Δ
  have hSub : Γ.carrier ⊆ Δ.carrier :=
    Set.Subset.trans hle hSub'
  -- obligations for Fset Γ A
  refine ?goal
  change Δ.carrier ∈ Fset Γ.carrier A
  refine And.intro hWΔ (And.intro hSub ?_)
  intro B hAB
  -- If (A→B) ∈ Γ, then (A→B) ∈ Γ' by inclusion, then B ∈ Δ by hAll'
  have hAB' : (A →ₗ B) ∈ Γ'.carrier := hle hAB
  exact hAll' B hAB'

/-- If Γ ⊨ A, then Γ ∈ Fcan Γ A. -/
lemma self_in_Fcan_if_A {α} [PS : ProofSystem.NLProofSystem α]
  (Γ : WCan α) (A : Formula α)
  (hA : SatC Γ A) : Γ ∈ Fcan Γ A := by
  -- We need Γ.carrier ∈ Fset Γ.carrier A
  have hA' : A ∈ Γ.carrier := (truth_lemmaC A Γ).1 hA
  have hWΓ := Γ.world
  change Γ.carrier ∈ Fset Γ.carrier A
  refine And.intro hWΓ (And.intro (by intro φ h; exact h) ?_)
  intro B hAB
  -- With A ∈ Γ and (A→B) ∈ Γ, closure under MP yields B ∈ Γ.
  exact (World.mp Γ.world) hA' hAB

end NL
