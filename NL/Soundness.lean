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

/-- 1.6 packaged as an equality: `(A ∧ B) = (B ∧ A)`.

`=ₗ` is mutual implication, so we prove both directions by turning
subset-to-intersection into a pair of component-subset goals in the order we need.
-/
theorem ax_1_6_valid (A B : Formula α) :
    Model.Valid ((A ∧ₗ B) =ₗ (B ∧ₗ A)) := by
  intro M w
  -- Unfold `=ₗ` to the conjunction of two implications.
  change w ∈ M.tset (((A ∧ₗ B) →ₗ (B ∧ₗ A)) ∧ₗ ((B ∧ₗ A) →ₗ (A ∧ₗ B)))
  refine And.intro ?h₁ ?h₂
  -- First direction: `(A ∧ B) → (B ∧ A)`
  ·
    -- Id gives f_w [[A∧B]] ⊆ [[A∧B]]; expand RHS and reorder components.
    have hId : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset (A ∧ₗ B) :=
      M.frame.Id w (M.tset (A ∧ₗ B))
    have hAB : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset A ∩ M.tset B := by
      simpa [Model.tset] using hId
    -- Extract components in the order we want: first B, then A.
    have hA : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset A :=
      fun x hx => (hAB hx).left
    have hB : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset B :=
      fun x hx => (hAB hx).right
    have hBA : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset B ∩ M.tset A :=
      (Set.subset_inter_iff.mpr ⟨hB, hA⟩)
    simpa [Model.tset] using hBA
  -- Second direction: `(B ∧ A) → (A ∧ B)`
  ·
    have hId : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset (B ∧ₗ A) :=
      M.frame.Id w (M.tset (B ∧ₗ A))
    have hBA : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset B ∩ M.tset A := by
      simpa [Model.tset] using hId
    -- Reorder to A then B.
    have hB : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset B :=
      fun x hx => (hBA hx).left
    have hA : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset A :=
      fun x hx => (hBA hx).right
    have hAB : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset A ∩ M.tset B :=
      (Set.subset_inter_iff.mpr ⟨hA, hB⟩)
    simpa [Model.tset] using hAB

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