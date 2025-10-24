/-
NL — Soundness of 1.1–1.7 and R1/R2
* Depends only on NL.Semantics.
-/
import NL.Semantics

namespace NL

/-! ## Soundness: each axiom schema and rule is valid on NL-frames -/

universe u v
section Soundness

variable {α : Type u}

/-- 1.1  `A → A`. -/
theorem ax_1_1_valid (A : Formula α) :
    Model.Valid.{u, v} (A →ₗ A) := by
  intro M w
  simpa [Model.Sat, Model.tset] using (M.frame.Id w (M.tset A))

/-- 1.2  `(A|B) → (B|A)` (symmetry of inconsistency). -/
theorem ax_1_2_valid (A B : Formula α) :
    Model.Valid.{u, v} ((A |ₗ B) →ₗ (B |ₗ A)) := by
  intro M w
  change M.frame.f w (M.tset (A |ₗ B)) ⊆ M.tset (B |ₗ A)
  intro v' hv
  have hv0 : v' ∈ M.tset (A |ₗ B) := (M.frame.Id w (M.tset (A |ₗ B))) hv
  have hsym : M.tset (A |ₗ B) = M.tset (B |ₗ A) := tset_inc_symm M A B
  simpa [hsym] using hv0

/-- 1.3  `A → ¬¬A` (intuitionistic; uses Kripke double-negation *expansion*). -/
theorem ax_1_3_valid (A : Formula α) :
    Model.Valid.{u, v} (A →ₗ (¬ₗ ¬ₗ A)) := by
  intro M w
  change M.frame.f w (M.tset A) ⊆ M.tset (¬ₗ ¬ₗ A)
  intro v' hv
  have hvA : v' ∈ M.tset A := (M.frame.Id w (M.tset A)) hv
  have hsub : M.tset A ⊆ M.tset (¬ₗ ¬ₗ A) := tset_subset_negneg M A
  exact hsub hvA

/-- 1.4  `(A→B) → (A◦B)` via coherence of `C`. -/
theorem ax_1_4_valid (A B : Formula α) :
    Model.Valid.{u, v} ((A →ₗ B) →ₗ (A ◦ B)) := by
  intro M w
  change M.frame.f w (M.tset (A →ₗ B)) ⊆ M.tset (A ◦ B)
  intro v' hv
  have hvX : v' ∈ M.tset (A →ₗ B) := (M.frame.Id w (M.tset (A →ₗ B))) hv
  have hsub : M.frame.f v' (M.tset A) ⊆ M.tset B := by
    simpa [Model.tset] using hvX
  have hC : M.frame.C v' (M.tset A) (M.tset B) :=
    M.frame.C_coh v' (M.tset A) (M.tset B) hsub
  simpa [Model.tset] using hC

/-- 1.6  `(A ∧ B) = (B ∧ A)` packaged as mutual implication. -/
theorem ax_1_6_valid (A B : Formula α) :
    Model.Valid.{u, v} ((A ∧ₗ B) =ₗ (B ∧ₗ A)) := by
  intro M w
  change w ∈ M.tset (((A ∧ₗ B) →ₗ (B ∧ₗ A)) ∧ₗ ((B ∧ₗ A) →ₗ (A ∧ₗ B)))
  refine And.intro ?h₁ ?h₂
  ·
    have hId : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset (A ∧ₗ B) :=
      M.frame.Id w (M.tset (A ∧ₗ B))
    have hAB : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset A ∩ M.tset B := by
      simpa [Model.tset] using hId
    have hA : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset A :=
      fun x hx => (hAB hx).left
    have hB : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset B :=
      fun x hx => (hAB hx).right
    have hBA : M.frame.f w (M.tset (A ∧ₗ B)) ⊆ M.tset B ∩ M.tset A :=
      (Set.subset_inter_iff.mpr ⟨hB, hA⟩)
    simpa [Model.tset] using hBA
  ·
    have hId : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset (B ∧ₗ A) :=
      M.frame.Id w (M.tset (B ∧ₗ A))
    have hBA : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset B ∩ M.tset A := by
      simpa [Model.tset] using hId
    have hB : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset B :=
      fun x hx => (hBA hx).left
    have hA : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset A :=
      fun x hx => (hBA hx).right
    have hAB : M.frame.f w (M.tset (B ∧ₗ A)) ⊆ M.tset A ∩ M.tset B :=
      (Set.subset_inter_iff.mpr ⟨hA, hB⟩)
    simpa [Model.tset] using hAB

/-- 1.7  `((A ∧ B) → C) → ((A ∧ ¬C) → ¬B)` (frame law `Contra`). -/
theorem ax_1_7_valid (A B C : Formula α) :
    Model.Valid.{u, v} (((A ∧ₗ B) →ₗ C) →ₗ ((A ∧ₗ (¬ₗ C)) →ₗ (¬ₗ B))) := by
  intro M w
  change M.frame.f w (M.tset ((A ∧ₗ B) →ₗ C)) ⊆ M.tset ((A ∧ₗ (¬ₗ C)) →ₗ (¬ₗ B))
  intro v' hv
  have hvX : v' ∈ M.tset ((A ∧ₗ B) →ₗ C) :=
    (M.frame.Id w (M.tset ((A ∧ₗ B) →ₗ C))) hv
  have hsub : M.frame.f v' (M.tset (A ∧ₗ B)) ⊆ M.tset C := by
    simpa [Model.tset] using hvX
  have hsub' : M.frame.f v' (M.tset A ∩ M.tset B) ⊆ M.tset C := by
    simpa [Model.tset] using hsub
  have hcontra :
      M.frame.f v' (M.tset A ∩ iNeg M.frame.le (M.tset C))
        ⊆ iNeg M.frame.le (M.tset B) :=
    M.frame.Contra v' (M.tset A) (M.tset B) (M.tset C) hsub'
  have : M.frame.f v' (M.tset (A ∧ₗ (¬ₗ C))) ⊆ M.tset (¬ₗ B) := by
    simpa [Model.tset] using hcontra
  simpa [Model.tset] using this

/-- (Local) modus ponens: if `w ⊨ A` and `w ⊨ A→B` then `w ⊨ B`. -/
lemma mp_at {A B : Formula α} :
    ∀ (M : Model.{u, v} α) (w : M.W), M.Sat w A → M.Sat w (A →ₗ B) → M.Sat w B := by
  intro M w hA hImp
  have hAB : M.frame.f w (M.tset A) ⊆ M.tset B := by
    simpa [Model.Sat, Model.tset] using hImp
  have : w ∈ M.frame.f w (M.tset A) :=
    M.frame.Succ w (M.tset A) (by simpa [Model.Sat] using hA)
  exact hAB this

/-- R1 (modus ponens): if `⊨ A` and `⊨ (A→B)` then `⊨ B`. -/
theorem rule_R1_sound (A B : Formula α)
    (hA : Model.Valid.{u, v} A) (hImp : Model.Valid.{u, v} (A →ₗ B)) :
    Model.Valid.{u, v} B := by
  intro M w
  exact mp_at (M := M) (w := w) (hA M w) (hImp M w)

/-- R2 (adjunction): if `⊨ A` and `⊨ B` then `⊨ (A ∧ B)`. -/
theorem rule_R2_sound (A B : Formula α)
    (hA : Model.Valid.{u, v} A) (hB : Model.Valid.{u, v} B) :
    Model.Valid.{u, v} (A ∧ₗ B) := by
  intro M w
  exact And.intro (hA M w) (hB M w)

-- in NL.Soundness

/-- If `u ⊨ ¬((A→B) ∧ (B→A))`, then at `u` we do **not** have local equivalence
    `f_u ⟦A⟧ ⊆ ⟦B⟧` and `f_u ⟦B⟧ ⊆ ⟦A⟧`. -/
private lemma not_equiv_at_of_negEq
  {α : Type u} {M : Model α} {u : M.W} {A B : Formula α} :
  u ∈ M.tset (¬ₗ ((A →ₗ B) ∧ₗ (B →ₗ A))) →
  ¬ ((M.frame.f u (M.tset A) ⊆ M.tset B) ∧ (M.frame.f u (M.tset B) ⊆ M.tset A)) := by
  intro hneg hboth
  -- From both inclusions we get membership in `(A→B) ∧ (B→A)` at `u`
  have hu_eq : u ∈ M.tset ((A →ₗ B) ∧ₗ (B →ₗ A)) := by
    simp [Set.subset_def] at hboth
    -- expand: having each inclusion at `u` is exactly forcing each implication at `u`
    -- so we can just rewrite:
    simpa [Model.tset] using And.intro hboth.left hboth.right
  -- But `¬` says no ≥-extension of `u` can have that; in particular `u` itself.
  have : u ∉ M.tset ((A →ₗ B) ∧ₗ (B →ₗ A)) :=
    hneg u (M.frame.le_refl u)
  exact this hu_eq

/-- 1.5  Guarded HS without `Cut`. -/
theorem ax_1_5_valid (A B C : Formula α) :
    Model.Valid.{u, v}
      ((Formula.neq3 A B C) →ₗ (((A →ₗ B) ∧ₗ (B →ₗ C)) →ₗ (A →ₗ C))) := by
  intro M w
  -- Outer implication: step to a world `v` selected by `f_w` on the guard
  change M.frame.f w (M.tset (Formula.neq3 A B C)) ⊆
         M.tset (((A →ₗ B) ∧ₗ (B →ₗ C)) →ₗ (A →ₗ C))
  intro v hv
  -- From Id, `v` actually satisfies the guard conjuncts
  have hv_guard : v ∈ M.tset (Formula.neq3 A B C) :=
    (M.frame.Id w (M.tset (Formula.neq3 A B C))) hv

  -- Write out the three guarded negations at `v`
  -- `neq3` abbreviates `(A≠B) ∧ (B≠C) ∧ (A≠C)` and `X≠Y` is `¬((X→Y) ∧ (Y→X))`
  rcases hv_guard with ⟨hABne_v, hBCne_v, hACne_v⟩

  -- Now show: at `v`, `((A→B) ∧ (B→C)) → (A→C)`
  change M.frame.f v (M.tset ((A →ₗ B) ∧ₗ (B →ₗ C))) ⊆ M.tset (A →ₗ C)
  intro u hu
  -- `u` is the inner selection point; first, push the guard up to `u` using `f_up` + persistence
  have hvu : M.frame.le v u := M.frame.f_up (X := M.tset ((A →ₗ B) ∧ₗ (B →ₗ C))) hu
  have hABne_u : u ∈ M.tset (¬ₗ ((A →ₗ B) ∧ₗ (B →ₗ A))) :=
    (persist M (¬ₗ ((A →ₗ B) ∧ₗ (B →ₗ A))) hABne_v hvu)
  have hBCne_u : u ∈ M.tset (¬ₗ ((B →ₗ C) ∧ₗ (C →ₗ B))) :=
    (persist M (¬ₗ ((B →ₗ C) ∧ₗ (C →ₗ B))) hBCne_v hvu)
  have hACne_u : u ∈ M.tset (¬ₗ ((A →ₗ C) ∧ₗ (C →ₗ A))) :=
    (persist M (¬ₗ ((A →ₗ C) ∧ₗ (C →ₗ A))) hACne_v hvu)

  -- From membership of the antecedent at `u` we read off the two inclusions at `u`
  have hu_AB_BC : u ∈ M.tset (A →ₗ B) ∧ u ∈ M.tset (B →ₗ C) := by
    simpa [Model.tset] using
      (M.frame.Id v (M.tset ((A →ₗ B) ∧ₗ (B →ₗ C))) hu)
  have hAB_u : M.frame.f u (M.tset A) ⊆ M.tset B := by
    simpa [Model.tset] using hu_AB_BC.left
  have hBC_u : M.frame.f u (M.tset B) ⊆ M.tset C := by
    simpa [Model.tset] using hu_AB_BC.right

  -- The three local non-equivalences at `u`
  have hNeq_AB_u :
    ¬ ((M.frame.f u (M.tset A) ⊆ M.tset B) ∧ (M.frame.f u (M.tset B) ⊆ M.tset A)) :=
    not_equiv_at_of_negEq (M := M) (u := u) (A := A) (B := B) hABne_u
  have hNeq_BC_u :
    ¬ ((M.frame.f u (M.tset B) ⊆ M.tset C) ∧ (M.frame.f u (M.tset C) ⊆ M.tset B)) :=
    not_equiv_at_of_negEq (M := M) (u := u) (A := B) (B := C) hBCne_u
  have hNeq_AC_u :
    ¬ ((M.frame.f u (M.tset A) ⊆ M.tset C) ∧ (M.frame.f u (M.tset C) ⊆ M.tset A)) :=
    not_equiv_at_of_negEq (M := M) (u := u) (A := A) (B := C) hACne_u

  -- Apply the guarded frame law **at u**
  have hAC_u : M.frame.f u (M.tset A) ⊆ M.tset C :=
    M.frame.TrNeq u (M.tset A) (M.tset B) (M.tset C)
      hNeq_AB_u hNeq_BC_u hNeq_AC_u hAB_u hBC_u

  -- Conclude `u ⊨ A→C`
  simpa [Model.tset] using hAC_u

end Soundness

end NL
