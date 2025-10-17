/-
NL — Soundness of 1.1–1.7 and R1/R2
* Depends only on NL.Semantics.
* Safe to exclude from the canonical/completeness build if desired.
-/
import NL.Semantics

namespace NL

/-! ## Soundness: each axiom schema and rule is valid on NL-frames -/

section Soundness

variable {α : Type u}

/-- 1.1  `A → A`. -/
theorem ax_1_1_valid (A : Formula α) : Model.Valid (A →ₗ A) := by
  intro M w
  simpa [Model.Sat, Model.tset] using (M.frame.Id w (M.tset A))

/-- 1.3  `A → ¬¬A` (classical negation). -/
theorem ax_1_3_valid (A : Formula α) : Model.Valid (A →ₗ (¬ₗ ¬ₗ A)) := by
  intro M w
  have : M.tset (¬ₗ ¬ₗ A) = M.tset A := tset_neg_neg M A
  simpa [Model.Sat, Model.tset, this] using (M.frame.Id w (M.tset A))

/-- 1.2  `(A|B) → (B|A)`. -/
theorem ax_1_2_valid (A B : Formula α) : Model.Valid ((A |ₗ B) →ₗ (B |ₗ A)) := by
  intro M w
  have hsym : M.tset (A |ₗ B) = M.tset (B |ₗ A) := tset_inc_symm M A B
  have hsub : M.frame.f w (M.tset (A |ₗ B)) ⊆ M.tset (A |ₗ B) :=
    M.frame.Id w (M.tset (A |ₗ B))
  simpa [Model.Sat, Model.tset, hsym] using hsub

/-- 1.4  `(A→B) → (A◦B)` via coherence of `C`. -/
theorem ax_1_4_valid (A B : Formula α) : Model.Valid ((A →ₗ B) →ₗ (A ◦ B)) := by
  intro M w
  change M.frame.f w (M.tset (A →ₗ B)) ⊆ M.tset (A ◦ B)
  intro v hv
  -- From Id, `v ∈ [[A→B]]`.
  have hvX : v ∈ M.tset (A →ₗ B) := (M.frame.Id w (M.tset (A →ₗ B))) hv
  -- Unfold implication at `v`: `f_v [[A]] ⊆ [[B]]`.
  have hsub : M.frame.f v (M.tset A) ⊆ M.tset B := by simpa [Model.tset] using hvX
  -- Coherence yields `C_v([[A]],[[B]])`.
  have hC : M.frame.C v (M.tset A) (M.tset B) := M.frame.C_coh v (M.tset A) (M.tset B) hsub
  simpa [Model.tset] using hC

/-- 1.6 packaged as an equality: `(A ∧ B) = (B ∧ A)`. -/
theorem ax_1_6_valid (A B : Formula α) :
    Model.Valid ((A ∧ₗ B) =ₗ (B ∧ₗ A)) := by
  intro M w
  -- Need `w ⊨ (A∧B → B∧A) ∧ (B∧A → A∧B)`.
  have h₁ : M.Sat w ((A ∧ₗ B) →ₗ (B ∧ₗ A)) := by
    -- from `Id` plus equality of truth-sets
    have := M.frame.Id w (M.tset (A ∧ₗ B))
    have : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset (B ∧ₗ A) := by
      simpa [tset_conj_comm (M := M) A B] using this
    simpa [Model.Sat, Model.tset] using this
  have h₂ : M.Sat w ((B ∧ₗ A) →ₗ (A ∧ₗ B)) := by
    have := M.frame.Id w (M.tset (B ∧ₗ A))
    have : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset (A ∧ₗ B) := by
      simpa [tset_conj_comm (M := M) B A] using this
    simpa [Model.Sat, Model.tset] using this
  simpa [Model.Sat, Model.tset] using And.intro h₁ h₂

/-- 1.7  `((A ∧ B) → C) → ((A ∧ ¬C) → ¬B)` via the frame law `Contra`. -/
theorem ax_1_7_valid (A B C : Formula α) :
  Model.Valid (((A ∧ₗ B) →ₗ C) →ₗ ((A ∧ₗ (¬ₗ C)) →ₗ (¬ₗ B))) := by
  intro M w
  change M.frame.f w (M.tset ((A ∧ₗ B) →ₗ C)) ⊆ M.tset ((A ∧ₗ ¬ₗ C) →ₗ ¬ₗ B)
  intro v hv
  -- From Id, `v ∈ [[(A∧B)→C]]`, so at `v` we have `f_v [[A∧B]] ⊆ [[C]]`.
  have hvX : v ∈ M.tset ((A ∧ₗ B) →ₗ C) := (M.frame.Id w (M.tset ((A ∧ₗ B) →ₗ C))) hv
  have hsub : M.frame.f v (M.tset (A ∧ₗ B)) ⊆ M.tset C := by simpa [Model.tset] using hvX
  -- Use `Contra` at `v` with intersections.
  have hcontra : M.frame.f v (M.tset A ∩ (M.tset C)ᶜ) ⊆ (M.tset B)ᶜ :=
    M.frame.Contra v (M.tset A) (M.tset B) (M.tset C) (by simpa [Model.tset] using hsub)
  -- This is exactly `[[ (A ∧ ¬C) → ¬B ]]` at `v`.
  simpa [Model.tset] using hcontra

/-- R1 (modus ponens) is sound on NL-frames. -/
lemma R1_modus_ponens {M : Model α} {w : M.W} {A B : Formula α}
    (hA  : M.Sat w A) (hImp : M.Sat w (A →ₗ B)) : M.Sat w B := by
  have hwf : w ∈ M.frame.f w (M.tset A) := M.frame.Succ w (M.tset A) hA
  have hsub : M.frame.f w (M.tset A) ⊆ M.tset B := by simpa [Model.Sat, Model.tset] using hImp
  exact hsub hwf

/-- R2 (adjunction) is sound: if `w ⊨ A` and `w ⊨ B` then `w ⊨ A ∧ B`. -/
lemma R2_adjunction {M : Model α} {w : M.W} {A B : Formula α}
    (hA : M.Sat w A) (hB : M.Sat w B) : M.Sat w (A ∧ₗ B) := by
  simpa [Model.Sat, Model.tset] using And.intro hA hB

/-- 1.5  `(A ≠ B ≠ C) → (((A → B) ∧ (B → C)) → (A → C))`.

We discharge this using the frame law `Cut` (composition for the selection).  The outer
antecedent `A ≠ B ≠ C` does not affect the set-theoretic reasoning; we keep it to match
the object-language statement.
-/
theorem ax_1_5_valid (A B C : Formula α) :
  Model.Valid ((Formula.neq3 A B C) →ₗ (((A →ₗ B) ∧ₗ (B →ₗ C)) →ₗ (A →ₗ C))) := by
  intro M w
  change M.frame.f w (M.tset (Formula.neq3 A B C)) ⊆
         M.tset (((A →ₗ B) ∧ₗ (B →ₗ C)) →ₗ (A →ₗ C))
  intro v _hv  -- the neq3 antecedent plays no role semantically here
  change M.frame.f v (M.tset ((A →ₗ B) ∧ₗ (B →ₗ C))) ⊆ M.tset (A →ₗ C)
  intro u hu
  -- From Id, `u ∈ [[(A→B) ∧ (B→C)]]`, so both inclusions hold at `u`.
  have hu' : u ∈ M.tset ((A →ₗ B) ∧ₗ (B →ₗ C)) :=
    (M.frame.Id v (M.tset ((A →ₗ B) ∧ₗ (B →ₗ C)))) hu
  have hpair : u ∈ M.tset (A →ₗ B) ∩ M.tset (B →ₗ C) := by
    simpa [Model.tset] using hu'
  have hAB : M.frame.f u (M.tset A) ⊆ M.tset B := by
    simpa [Model.tset] using hpair.left
  have hBC : M.frame.f u (M.tset B) ⊆ M.tset C := by
    simpa [Model.tset] using hpair.right
  -- Compose by `Cut`.
  have hAC : M.frame.f u (M.tset A) ⊆ M.tset C :=
    M.frame.Cut u (M.tset A) (M.tset B) (M.tset C) hAB hBC
  simpa [Model.tset] using hAC

end Soundness

end NL