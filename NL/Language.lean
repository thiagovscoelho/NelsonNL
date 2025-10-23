/-! ## Object language -/

universe u

/-- Formulas over a set of atoms `α`. -/
inductive Formula (α : Type u) : Type u where
  | atom : α → Formula α
  | neg  : Formula α → Formula α
  | conj : Formula α → Formula α → Formula α
  | imp  : Formula α → Formula α → Formula α
  | circ : Formula α → Formula α → Formula α
deriving DecidableEq, Repr

namespace Formula

variable {α : Type u}

/-- Inconsistency (object-language abbreviation): `A |ₗ B := ¬ₗ (A ◦ B)`. -/
def inc (A B : Formula α) : Formula α :=
  neg (circ A B)

/-- Object-language extensional equality. -/
def eqv (A B : Formula α) : Formula α :=
  conj (imp A B) (imp B A)

/-- Negation of extensional equality. -/
def neq (A B : Formula α) : Formula α :=
  neg (eqv A B)

/-- Shorthand for `A ≠ B ≠ C`. -/
def neq3 (A B C : Formula α) : Formula α :=
  conj (neq A B) (conj (neq B C) (neq A C))

end Formula

/-! ### Notation (at the root to avoid namespace/elab issues) -/
prefix:70  "¬ₗ" => Formula.neg
infixr:60  " ∧ₗ " => Formula.conj
infix:58   " ◦ "  => Formula.circ     -- non-assoc: avoid chaining
infix:58   " |ₗ " => Formula.inc      -- non-assoc
infix:55   " =ₗ " => Formula.eqv      -- non-assoc
notation:55 A " ≠ₗ " B => Formula.neq A B
notation:55 A " ≠ₗ " B " ≠ₗ " C => Formula.neq3 A B C
infixr:50  " →ₗ " => Formula.imp      -- lowest precedence
