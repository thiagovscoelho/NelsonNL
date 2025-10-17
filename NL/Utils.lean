/-
NL — Utilities (extensionality helpers)
-/
import NL.Semantics

namespace NL

/-! ## Small extensionality helpers (useful for automation) -/

section Extensionality

variable {α : Type u}

/-- If `A → B` is valid, it preserves truth at every world (uses `Succ`). -/
lemma valid_imp_preserves_truth {A B : Formula α}
    (h : Model.Valid (A →ₗ B)) :
    ∀ (M : Model α) (w : M.W), M.Sat w A → M.Sat w B := by
  intro M w hA
  have hw : w ∈ M.frame.f w (M.tset A) := M.frame.Succ w (M.tset A) hA
  have hsub : M.frame.f w (M.tset A) ⊆ M.tset B := by
    simpa [Model.Sat, Model.tset] using h M w
  exact hsub hw

/-- If `(A =ₗ B)` is valid, then `[[A]] = [[B]]` in every model. -/
lemma valid_eqv_truthset_eq {A B : Formula α}
    (h : Model.Valid (A =ₗ B)) :
    ∀ (M : Model α), M.tset A = M.tset B := by
  intro M
  -- From validity, we have both valid implications.
  have h₁ : Model.Valid (A →ₗ B) := by
    intro M' w; have := h M' w; simpa [Model.Sat, Model.tset] using (And.left this)
  have h₂ : Model.Valid (B →ₗ A) := by
    intro M' w; have := h M' w; simpa [Model.Sat, Model.tset] using (And.right this)
  -- Now show mutual subset using the preservation lemma.
  ext w; constructor
  · intro hAw; exact valid_imp_preserves_truth (A:=A) (B:=B) h₁ M w hAw
  · intro hBw; exact valid_imp_preserves_truth (A:=B) (B:=A) h₂ M w hBw

end Extensionality


end NL