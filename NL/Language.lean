/-! ## Object language -/

universe u v

/-- Formulas over a set of atoms `α`. -/
inductive Formula (α : Type u) : Type u where
  | atom : α → Formula α
  | neg  : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | imp  : Formula α → Formula α → Formula α
  | circ : Formula α → Formula α → Formula α
deriving DecidableEq

namespace Formula

variable {α : Type u}

/-- Inconsistency (object-language abbreviation): `A |ₗ B := ¬ₗ (A ◦ B)`. -/
def inc (A B : _root_.Formula α) : _root_.Formula α :=
  neg (circ A B)

/-- Object-language extensional equality. -/
def eqv (A B : _root_.Formula α) : _root_.Formula α :=
  conj (imp A B) (imp B A)

/-- Negation of extensional equality. -/
def neq (A B : _root_.Formula α) : _root_.Formula α :=
  neg (eqv A B)

/-- Shorthand for `A ≠ B ≠ C`. -/
def neq3 (A B C : _root_.Formula α) : _root_.Formula α :=
  conj (neq A B) (conj (neq B C) (neq A C))

end Formula

/-! ### Notation (at the root to avoid namespace/elab issues) -/
prefix:60  "¬ₗ" => Formula.neg
infixr:52  " ∧ₗ " => Formula.conj
infixr:51  " →ₗ " => Formula.imp
infix:50   " ◦ "  => Formula.circ
notation:50 A " |ₗ " B => Formula.inc A B
notation:50 A " =ₗ " B => Formula.eqv A B