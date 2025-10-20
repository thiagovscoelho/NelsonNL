/-
NL — Utilities (extensionality helpers)
-/
import NL.Semantics

namespace NL

/-! ## Small extensionality helpers (useful for automation) -/

universe u v

section Extensionality

variable {α : Type u}

/-- If `A → B` is valid, it preserves truth at every world (uses `Succ`). -/
lemma valid_imp_preserves_truth {A B : Formula α}
    (h : Model.Valid.{u, v} (A →ₗ B)) :
    ∀ {M : Model.{u, v} α} {w : M.W}, M.Sat w A → M.Sat w B := by
  intro M w hA
  have hw : w ∈ M.frame.f w (M.tset A) := M.frame.Succ w (M.tset A) hA
  have hsub : M.frame.f w (M.tset A) ⊆ M.tset B := by
    -- Specialize validity at this exact `M, w` with matching universes `{u, v}`.
    simpa [Model.Sat, Model.tset] using (h (M := M) (w := w))
  exact hsub hw

/-- If `(A =ₗ B)` is valid, then `[[A]] = [[B]]` in every model. -/
lemma valid_eqv_truthset_eq {A B : Formula α}
    (h : Model.Valid.{u, v} (A =ₗ B)) :
    ∀ (M : Model.{u, v} α), M.tset A = M.tset B := by
  intro M
  -- Get the two valid implications, keeping the same universes `{u, v}`.
  have h₁ : Model.Valid.{u, v} (A →ₗ B) := by
    intro M' w'
    have hAB := h (M := M') (w := w')
    simpa [Model.Sat, Model.tset] using hAB.left
  have h₂ : Model.Valid.{u, v} (B →ₗ A) := by
    intro M' w'
    have hAB := h (M := M') (w := w')
    simpa [Model.Sat, Model.tset] using hAB.right
  -- Mutual inclusion via the preservation lemma.
  ext w
  constructor
  · intro hAw
    exact valid_imp_preserves_truth (A := A) (B := B) h₁ (M := M) (w := w) hAw
  · intro hBw
    exact valid_imp_preserves_truth (A := B) (B := A) h₂ (M := M) (w := w) hBw

end Extensionality

end NL
