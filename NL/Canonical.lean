/-
NL — Canonical semantics, Truth Lemma, Completeness (refactored into small lemmas).

We keep the intended set-selection semantics in `Semantics.lean` for soundness.
Here we introduce a *formula-indexed* canonical semantics that matches the
standard textbook completeness proof (via Lindenbaum/World/Detachment),
but we factor the long proofs into short, reusable lemmas.
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
def Fcan (Γ : WCan α) (A : Formula α) : Set (WCan α) :=
  { Δ : WCan α | ∀ B : Formula α, (A →ₗ B) ∈ Γ.carrier → B ∈ Δ.carrier }

/--
Canonical truth-sets (formula-indexed):
* atoms/conj/neg/circ: membership in the world
* `A → B`: `F_Γ(A) ⊆ [[B]]` (where `[[B]] = {Δ | B ∈ Δ}`).
-/
def tsetC (A : Formula α) : Set (WCan α) :=
  match A with
  | .atom p   => { Δ : WCan α | Formula.atom p ∈ Δ.carrier }
  | .conj A B => { Δ : WCan α | (A ∧ₗ B) ∈ Δ.carrier }
  | .neg A    => { Δ : WCan α | (¬ₗ A) ∈ Δ.carrier }
  | .imp A B  => { Δ : WCan α | Fcan Δ A ⊆ tsetC B }
  | .circ A B => { Δ : WCan α | (A ◦ B) ∈ Δ.carrier }

/-- Canonical satisfaction. -/
def SatC (Γ : WCan α) (A : Formula α) : Prop := Γ ∈ tsetC A

/-- Canonical validity. -/
def ValidC (A : Formula α) : Prop := ∀ (Γ : WCan α), SatC Γ A

/-! ### Small simp facts that hide definitional noise -/

@[simp] lemma SatC_atom_iff   (Γ : WCan α) (p) :
  SatC Γ (.atom p) ↔ .atom p ∈ Γ.carrier := by
  simp [SatC, tsetC]

@[simp] lemma SatC_conj_iff   (Γ : WCan α) (A B) :
  SatC Γ (A ∧ₗ B) ↔ (A ∧ₗ B) ∈ Γ.carrier := by
  simp [SatC, tsetC]

@[simp] lemma SatC_neg_iff    (Γ : WCan α) (A) :
  SatC Γ (¬ₗ A) ↔ (¬ₗ A) ∈ Γ.carrier := by
  simp [SatC, tsetC]

@[simp] lemma SatC_circ_iff   (Γ : WCan α) (A B) :
  SatC Γ (A ◦ B) ↔ (A ◦ B) ∈ Γ.carrier := by
  simp [SatC, tsetC]

@[simp] lemma SatC_imp_iff_subset (Γ : WCan α) (A B) :
  SatC Γ (A →ₗ B) ↔ (Fcan Γ A ⊆ tsetC B) := by
  simp [SatC, tsetC]

/-! ### Tiny utilities to build WCan points out of `Fset` witnesses -/

/-- Package a set of formulas with a `World` proof as a canonical world. -/
@[simp] def WCan.mkOfWorld (Δ0 : Set (Formula α)) (hW : World Δ0) : WCan α := ⟨Δ0, hW⟩

/-- From `Δ0 ∈ Fset Γ A`, produce a canonical `Δ : WCan α` in `Fcan Γ A`. -/
lemma mem_Fcan_of_Fset
  {Γ : WCan α} {A : Formula α} {Δ0 : Set (Formula α)}
  (h : Δ0 ∈ Fset Γ.carrier A) :
  ∃ Δ : WCan α, Δ ∈ Fcan Γ A ∧ Δ.carrier = Δ0 := by
  rcases h with ⟨hWΔ0, hF⟩
  refine ⟨WCan.mkOfWorld Δ0 hWΔ0, ?_, rfl⟩
  intro B hAimpB
  simpa using hF B hAimpB

/-! ### The →-case helpers for the Truth Lemma -/

/-- From `(A → B) ∈ Γ`, we get `Fcan Γ A ⊆ tsetC B`. -/
private lemma subset_of_imp_mem
  {A B : Formula α}
  (IH_B : ∀ (Δ : WCan α), SatC Δ B ↔ B ∈ Δ.carrier)
  (Γ : WCan α)
  (hImp : (A →ₗ B) ∈ Γ.carrier) :
  Fcan Γ A ⊆ tsetC B := by
  intro Δ hΔ
  have hBmem : B ∈ Δ.carrier := hΔ B hImp
  have : SatC Δ B := (IH_B Δ).2 hBmem
  simpa [SatC] using this

/-- From `Fcan Γ A ⊆ tsetC B`, we get `(A → B) ∈ Γ` (using the detachment witness). -/
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
  -- package as a canonical world Δ and use the subset hypothesis
  rcases mem_Fcan_of_Fset (h := hΔ0in) with ⟨Δ, hΔF, hcar⟩
  have hSat : SatC Δ B := hsubset hΔF
  -- Truth lemma for B (IH) yields B ∈ Δ.carrier = Δ0, contradiction
  have hBinΔ : B ∈ Δ.carrier := (IH_B Δ).1 hSat
  have hBinΔ0 : B ∈ Δ0 := by simpa [hcar] using hBinΔ
  exact hBnot hBinΔ0

/-! ## Truth Lemma and Completeness -/

/-- Auxiliary Truth Lemma over canonical worlds (ASCII identifiers only). -/
private theorem truth_lemmaC_aux :
  ∀ (A : Formula α) (Γ : WCan α), SatC Γ A ↔ A ∈ Γ.carrier := by
  intro A
  induction A generalizing Γ with
  | atom p =>
      intro Γ; simpa
  | conj A B ihA ihB =>
      intro Γ; simpa
  | neg A ih =>
      intro Γ; simpa
  | imp A B ihA ihB =>
      intro Γ
      constructor
      · -- (→) from subset to membership, using witness lemma
        intro hSat
        have hsubset : Fcan Γ A ⊆ tsetC B := (SatC_imp_iff_subset Γ A B).1 hSat
        exact imp_mem_of_subset (IH_B := ihB) Γ hsubset
      · -- (←) from membership to subset, then fold back to SatC
        intro hImp
        have hsubset : Fcan Γ A ⊆ tsetC B := subset_of_imp_mem (IH_B := ihB) Γ hImp
        exact (SatC_imp_iff_subset Γ A B).2 hsubset
  | circ A B =>
      intro Γ; simpa

/-- Truth Lemma for the canonical semantics. -/
theorem truth_lemmaC :
  ∀ (A : Formula α) (Γ : WCan α), SatC Γ A ↔ A ∈ Γ.carrier := by
  intro A Γ
  exact truth_lemmaC_aux A Γ

/-! ### Completeness (split into tiny helpers) -/

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
  by_contra _hnot  -- assumption not used explicitly
  -- extend the theorems set by ¬A
  rcases extend_with_neg (Γ₀ := GammaThm) (hcl₀ := GammaThm_closed) A
    with ⟨Δ0, _hsub, hWΔ0, hNotA⟩
  let Δ : WCan α := ⟨Δ0, hWΔ0⟩
  -- validity says SatC Δ A; Truth Lemma gives A ∈ Δ0; exclusivity contradicts ¬A ∈ Δ0
  have : SatC Δ A := hvalid Δ
  have : A ∈ Δ0 := (truth_lemmaC A Δ).1 this
  exact (hWΔ0.neg_exclusive A) ⟨this, hNotA⟩

end NL
