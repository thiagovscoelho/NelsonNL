/-
NL — Examples / regression scaffolding.

A few tiny lemmas and smoke tests that compile and touch the key
APIs (truth sets, persistence, and soundness theorems).
-/
import NL.Semantics
import NL.Soundness

namespace NL

open Set

universe u v
variable {α : Type u}

/-! ## Truth-set level sanity checks -/

-- Symmetry of inconsistency at the semantic level (reuses the lemma from Semantics).
example (M : Model α) (A B : Formula α) :
    M.tset (A |ₗ B) = M.tset (B |ₗ A) :=
  tset_inc_symm M A B

-- Conjunction commutes at the truth-set level.
example (M : Model α) (A B : Formula α) :
    M.tset (A ∧ₗ B) = M.tset (B ∧ₗ A) :=
  tset_conj_comm M A B

/-! ## Persistence helpers in terms of `Sat` -/

-- Upward persistence phrased with `Sat`.
lemma sat_persist {M : Model α} {A : Formula α} {w x : M.W}
    (hw : M.Sat w A) (hle : M.frame.le w x) : M.Sat x A := by
  -- `persist` is stated for truth-sets; rewrite to `Sat` and apply it.
  simpa [Model.Sat] using
    (persist (M := M) A (by simpa [Model.Sat] using hw) hle)

-- Kripke double-negation expansion as a quick corollary on `Sat`.
lemma sat_double_neg {M : Model α} {A : Formula α} {w : M.W}
    (hw : M.Sat w A) : M.Sat w (¬ₗ ¬ₗ A) := by
  have hsub := tset_subset_negneg (M := M) A
  simpa [Model.Sat] using hsub (by simpa [Model.Sat] using hw)

/-! ## Tiny uses of soundness theorems -/

-- Direct aliases of axiom validities (useful as “compiles” checks).
theorem valid_id (A : Formula α) : Model.Valid (A →ₗ A) :=
  ax_1_1_valid A

theorem valid_inc_symm (A B : Formula α) :
    Model.Valid ((A |ₗ B) →ₗ (B |ₗ A)) :=
  ax_1_2_valid A B

-- Combine two validities with R2 (adjunction): (A→A) ∧ (B→B) is valid.
theorem valid_pair_ids (A B : Formula α) :
    Model.Valid ((A →ₗ A) ∧ₗ (B →ₗ B)) := by
  exact rule_R2_sound (A := (A →ₗ A)) (B := (B →ₗ B))
    (ax_1_1_valid A) (ax_1_1_valid B)

-- Local modus ponens packaged as a handy lemma on `Sat`.
example {M : Model α} {w : M.W} {A B : Formula α} :
    M.Sat w A → M.Sat w (A →ₗ B) → M.Sat w B :=
  mp_at (M := M) (w := w)

-- Quick `#check`s to keep APIs in view (also ensures names are in scope).
#check ax_1_7_valid
#check ax_1_5_valid
#check mp_at
#check rule_R2_sound

end NL
