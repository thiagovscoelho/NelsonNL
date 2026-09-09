import Std

/-!
A general algebraic-matrix semantics for the SEVEN AXIOMS AND TWO RULES
in the question, with no additional structural or replacement rules.

The conjunction in the abbreviation for three inequalities is LEFT
associated, with conjuncts in the order AB, BC, AC.

STATUS: This source was written and manually reviewed, but a Lean executable
was not available in the authoring environment. It has NOT been kernel-checked
in that environment. There are no proof placeholders or extra axiom declarations.
-/

set_option autoImplicit false

namespace NLPrimitive

inductive Formula where
  | var : Nat → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | compat : Formula → Formula → Formula
  | arr : Formula → Formula → Formula
  deriving DecidableEq, Repr

structure Ops (α : Type) where
  neg : α → α
  conj : α → α → α
  compat : α → α → α
  arr : α → α → α


def formulaOps : Ops Formula where
  neg := Formula.neg
  conj := Formula.conj
  compat := Formula.compat
  arr := Formula.arr

-- These are object-language terms, NOT Lean equality or inequality.
def Ops.inc {α : Type} (o : Ops α) (a b : α) : α :=
  o.neg (o.compat a b)

def Ops.eqv {α : Type} (o : Ops α) (a b : α) : α :=
  o.conj (o.arr a b) (o.arr b a)

def Ops.neq {α : Type} (o : Ops α) (a b : α) : α :=
  o.neg (o.eqv a b)

def Ops.distinct3 {α : Type} (o : Ops α) (a b c : α) : α :=
  o.conj (o.conj (o.neq a b) (o.neq b c)) (o.neq a c)

-- Each schema is defined once and instantiated both syntactically and
-- semantically. No assertion of derivability occurs in these definitions.
def s1 {α : Type} (o : Ops α) (a : α) : α :=
  o.arr a a

def s2 {α : Type} (o : Ops α) (a b : α) : α :=
  o.arr (o.inc a b) (o.inc b a)

def s3 {α : Type} (o : Ops α) (a : α) : α :=
  o.arr a (o.neg (o.neg a))

def s4 {α : Type} (o : Ops α) (a b : α) : α :=
  o.arr (o.arr a b) (o.compat a b)

def s5 {α : Type} (o : Ops α) (a b c : α) : α :=
  o.arr (o.distinct3 a b c)
    (o.arr (o.conj (o.arr a b) (o.arr b c)) (o.arr a c))

def s6 {α : Type} (o : Ops α) (a b : α) : α :=
  o.eqv (o.conj a b) (o.conj b a)

def s7 {α : Type} (o : Ops α) (a b c : α) : α :=
  o.arr (o.arr (o.conj a b) c)
    (o.arr (o.conj a (o.neg c)) (o.neg b))

inductive Axiom : Formula → Prop where
  | a1 (a : Formula) : Axiom (s1 formulaOps a)
  | a2 (a b : Formula) : Axiom (s2 formulaOps a b)
  | a3 (a : Formula) : Axiom (s3 formulaOps a)
  | a4 (a b : Formula) : Axiom (s4 formulaOps a b)
  | a5 (a b c : Formula) : Axiom (s5 formulaOps a b c)
  | a6 (a b : Formula) : Axiom (s6 formulaOps a b)
  | a7 (a b c : Formula) : Axiom (s7 formulaOps a b c)

-- With Γ empty, these are exactly the two theorem-generating rules given.
-- For nonempty Γ, this defines their local, premise-allowing extension.
inductive Derives (Γ : Formula → Prop) : Formula → Prop where
  | hyp {a : Formula} : Γ a → Derives Γ a
  | ax {a : Formula} : Axiom a → Derives Γ a
  | mp {a b : Formula} :
      Derives Γ a → Derives Γ (formulaOps.arr a b) → Derives Γ b
  | adj {a b : Formula} :
      Derives Γ a → Derives Γ b → Derives Γ (Formula.conj a b)

-- A syntax-independent, finite universal-Horn specification of matrices.
-- In particular, this definition does NOT refer to Derives or Axiom.
structure Matrix (α : Type) where
  nonempty : Nonempty α
  op : Ops α
  D : α → Prop
  a1 : ∀ a, D (s1 op a)
  a2 : ∀ a b, D (s2 op a b)
  a3 : ∀ a, D (s3 op a)
  a4 : ∀ a b, D (s4 op a b)
  a5 : ∀ a b c, D (s5 op a b c)
  a6 : ∀ a b, D (s6 op a b)
  a7 : ∀ a b c, D (s7 op a b c)
  mp : ∀ a b, D a → D (op.arr a b) → D b
  adj : ∀ a b, D a → D b → D (op.conj a b)

def eval {α : Type} (o : Ops α) (v : Nat → α) : Formula → α
  | .var n => v n
  | .neg a => o.neg (eval o v a)
  | .conj a b => o.conj (eval o v a) (eval o v b)
  | .compat a b => o.compat (eval o v a) (eval o v b)
  | .arr a b => o.arr (eval o v a) (eval o v b)

-- Semantic consequence is defined independently of proof-theoretic closure.
def Entails (Γ : Formula → Prop) (a : Formula) : Prop :=
  ∀ (α : Type) (M : Matrix α) (v : Nat → α),
    (∀ b, Γ b → M.D (eval M.op v b)) → M.D (eval M.op v a)

theorem axiom_sound {α : Type} (M : Matrix α) (v : Nat → α)
    {a : Formula} (h : Axiom a) : M.D (eval M.op v a) := by
  cases h with
  | a1 a => exact M.a1 (eval M.op v a)
  | a2 a b => exact M.a2 (eval M.op v a) (eval M.op v b)
  | a3 a => exact M.a3 (eval M.op v a)
  | a4 a b => exact M.a4 (eval M.op v a) (eval M.op v b)
  | a5 a b c => exact M.a5 (eval M.op v a) (eval M.op v b) (eval M.op v c)
  | a6 a b => exact M.a6 (eval M.op v a) (eval M.op v b)
  | a7 a b c => exact M.a7 (eval M.op v a) (eval M.op v b) (eval M.op v c)

theorem sound {Γ : Formula → Prop} {a : Formula}
    (h : Derives Γ a) : Entails Γ a := by
  intro α M v hΓ
  induction h with
  | hyp hb => exact hΓ _ hb
  | ax hb => exact axiom_sound M v hb
  | mp ha hab iha ihab => exact M.mp _ _ iha ihab
  | adj ha hb iha ihb => exact M.adj _ _ iha ihb

-- The term algebra with a designated deductive filter is used ONLY to prove
-- completeness. It is a witness for the independently defined Matrix type.
def canonical (Γ : Formula → Prop) : Matrix Formula where
  nonempty := ⟨Formula.var 0⟩
  op := formulaOps
  D := Derives Γ
  a1 := fun a => Derives.ax (Axiom.a1 a)
  a2 := fun a b => Derives.ax (Axiom.a2 a b)
  a3 := fun a => Derives.ax (Axiom.a3 a)
  a4 := fun a b => Derives.ax (Axiom.a4 a b)
  a5 := fun a b c => Derives.ax (Axiom.a5 a b c)
  a6 := fun a b => Derives.ax (Axiom.a6 a b)
  a7 := fun a b c => Derives.ax (Axiom.a7 a b c)
  mp := fun _ _ ha hab => Derives.mp ha hab
  adj := fun _ _ ha hb => Derives.adj ha hb

theorem eval_formulaOps (a : Formula) :
    eval formulaOps Formula.var a = a := by
  induction a <;> simp_all [eval, formulaOps]

theorem canonical_truth (Γ : Formula → Prop) (a : Formula) :
    (canonical Γ).D (eval (canonical Γ).op Formula.var a) ↔ Derives Γ a := by
  change Derives Γ (eval formulaOps Formula.var a) ↔ Derives Γ a
  rw [eval_formulaOps]

theorem complete {Γ : Formula → Prop} {a : Formula}
    (h : Entails Γ a) : Derives Γ a := by
  have hΓ : ∀ b, Γ b →
      (canonical Γ).D (eval (canonical Γ).op Formula.var b) := by
    intro b hb
    exact (canonical_truth Γ b).mpr (Derives.hyp hb)
  exact (canonical_truth Γ a).mp (h Formula (canonical Γ) Formula.var hΓ)

theorem sound_complete (Γ : Formula → Prop) (a : Formula) :
    Derives Γ a ↔ Entails Γ a :=
  ⟨sound, complete⟩

theorem canonical_countermodel {Γ : Formula → Prop} {a : Formula}
    (h : ¬ Derives Γ a) :
    (∀ b, Γ b → (canonical Γ).D (eval (canonical Γ).op Formula.var b)) ∧
    ¬ (canonical Γ).D (eval (canonical Γ).op Formula.var a) := by
  constructor
  · intro b hb
    exact (canonical_truth Γ b).mpr (Derives.hyp hb)
  · intro ha
    exact h ((canonical_truth Γ a).mp ha)

def Theorem (a : Formula) : Prop := Derives (fun _ => False) a

def Valid (a : Formula) : Prop := Entails (fun _ => False) a

theorem theorem_iff_valid (a : Formula) : Theorem a ↔ Valid a :=
  sound_complete (fun _ => False) a

/- A nontrivial two-element matrix of the primitive-implication calculus. -/
def boolOps : Ops Bool where
  neg := Bool.not
  conj := fun a b => a && b
  compat := fun _ _ => true
  arr := fun a b => (!a) || b

def boolMatrix : Matrix Bool where
  nonempty := ⟨false⟩
  op := boolOps
  D := fun a => a = true
  a1 := by intro a; cases a <;> decide
  a2 := by intro a b; cases a <;> cases b <;> decide
  a3 := by intro a; cases a <;> decide
  a4 := by intro a b; cases a <;> cases b <;> decide
  a5 := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  a6 := by intro a b; cases a <;> cases b <;> decide
  a7 := by intro a b c; cases a <;> cases b <;> cases c <;> decide
  mp := by intro a b; cases a <;> cases b <;> decide
  adj := by intro a b; cases a <;> cases b <;> decide

def aristotle : Formula :=
  Formula.neg (formulaOps.arr (Formula.var 0) (Formula.neg (Formula.var 0)))

theorem aristotle_not_derivable : ¬ Theorem aristotle := by
  intro h
  have hv := sound h Bool boolMatrix (fun _ => false)
    (by intro b hb; exact False.elim hb)
  change (false : Bool) = true at hv
  cases hv

theorem nontrivial : ¬ Theorem (Formula.var 0) := by
  intro h
  have hv := sound h Bool boolMatrix (fun _ => false)
    (by intro b hb; exact False.elim hb)
  change (false : Bool) = true at hv
  cases hv

-- The Boolean matrix does NOT satisfy Nelson's additional definition.
theorem bool_implication_not_defined :
    boolOps.arr false false ≠
    boolOps.neg (boolOps.compat false (boolOps.neg false)) := by
  decide

end NLPrimitive

#print axioms NLPrimitive.sound_complete
#print axioms NLPrimitive.theorem_iff_valid
#print axioms NLPrimitive.canonical_countermodel
#print axioms NLPrimitive.nontrivial
#print axioms NLPrimitive.aristotle_not_derivable
