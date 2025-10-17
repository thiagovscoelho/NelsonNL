/-
NL — Examples / regression scaffolding.

This file sets up the stubs for finite-frame countermodels and quick checks.
Real examples can be added once `Canonical.lean` is finished.
-/
import NL.Semantics
import NL.Soundness
-- eventually: import NL.Canonical

namespace NL

/-- Placeholder example: a tiny frame skeleton to illustrate how to instantiate Frame. -/
def tinyFrame : Frame Unit where
  f _ X := X
  C _ _ _ := True
  Id _ _ := by intro _ hx; exact hx
  Mon _ _ _ hXY := by intro w hw; exact hXY hw
  Succ _ _ hw := hw
  NE _ X h := h
  Bo _ _ _ h := by intro hcontra; exact by cases hcontra (by intro; exact True.intro)
  Contra _ _ _ _ h := by intro w hw; cases hw
  Cut _ _ _ _ h1 h2 := fun w hw => h2 (h1 hw)
  C_symm _ _ _ := by constructor <;> intro _; trivial
  C_coh _ _ _ _ := True.intro

end NL
