/-! ## Object language -/

universe u v

/-- Formulas over a set of atoms `α`. -/
inductive Formula (α : Type u) : Type u
| atom : α → Formula
| neg  : Formula → Formula
| conj : Formula → Formula → Formula
| imp  : Formula → Formula → Formula
| circ : Formula → Formula → Formula
deriving DecidableEq

namespace Formula

variable {α : Type u}

notation "¬ₗ" A => Formula.neg A
infixr:52  " ∧ₗ " => Formula.conj
infixr:51  " →ₗ " => Formula.imp
infix:50   " ◦ "  => Formula.circ

/-- Inconsistency (object-language abbreviation): `A |ₗ B := ¬ (A ◦ B)`. -/
def inc (A B : Formula α) : Formula α := ¬ₗ (A ◦ B)
notation:50 A " |ₗ " B => Formula.inc A B

/-- Object-language extensional equality and its negation. -/
def eqv (A B : Formula α) : Formula α := (A →ₗ B) ∧ₗ (B →ₗ A)
notation:50 A " =ₗ " B => Formula.eqv A B

def neq (A B : Formula α) : Formula α := ¬ₗ (A =ₗ B)

/-- Shorthand for `A ≠ B ≠ C`. -/
def neq3 (A B C : Formula α) : Formula α := (neq A B) ∧ₗ (neq B C) ∧ₗ (neq A C)

end Formula

