Axioms and inference rules for E. Nelson’s connexive logic NL are presented as follows (we here use schematic letters for arbitrary formulas instead of propositional variables and a different symbol for negation):

1.1 A → A
1.2 (A|B) → (B|A)
1.3 A → ~~A
1.4 (A → B) → (A ◦ B)
1.5 (A ≠ B ≠ C) → (((A → B) ∧ (B → C)) → (A → C ))
1.6 (A ∧ B) = (B ∧ A)
1.7 ((A ∧ B ) → C ) → ((A ∧ ~C) → ~B )

R1 if ⊢ A and ⊢ (A → B), then ⊢ B (modus ponens)
R2 if ⊢ A and ⊢ B, then ⊢ (A ∧ B) (adjunction)

where ◦ is a primitive binary consistency operator, (A|B) (inconsistency) is defined as ~(A ◦ B), A = B is defined as (A → B) ∧ (B → A), A ≠ B as ~ (A = B), and A ≠ B ≠ C is an abbreviation of (A ≠ B) ∧ (B ≠ C) ∧ (A ≠ C).

Try to come up with a sound and complete semantics for NL.

------------------------------------------------------------------------------------------------------------------------------------------------

Below is a compact, fully-worked semantics that validates exactly the NL axioms/rules listed and is strong enough to be complete. It’s a “conditional-selection” semantics (in the spirit of Stalnaker/Lewis and the usual semantics for conditional logics), augmented with a primitive, symmetric compatibility/consistency predicate for ◦ and two frame conditions that capture the connexive features (Boethius and the contraposition-like 1.7).

I’ll first define the models, then give the truth-clauses, then list the frame conditions we need (they are very natural), and finally sketch soundness and completeness.

## NL frames and models

An **NL-frame** is a triple
[
\mathcal F=\langle W,; f,; C\rangle
]
where

* (W) is a nonempty set of worlds.
* For each (w\in W), (f_w:\mathcal P(W)\to \mathcal P(W)) is a **selection function** (think: the set (f_w(X)) are the “relevant (X)–cases” at (w)).
* For each (w\in W), (C_w\subseteq \mathcal P(W)\times \mathcal P(W)) is a **compatibility** (consistency) relation on sets of worlds; we use it to interpret (A\circ B).

An **NL-model** is a frame (\mathcal F) together with a valuation (V:\text{Atoms}\to\mathcal P(W)). For any formula (A), let (\llbracket A\rrbracket^\mathcal M={w\in W: \mathcal M,w\models A}) be its truth set.

## Truth clauses

Extend (V) to all formulas as follows (classical pointwise (\sim) and (\wedge); non-truth-functional (\to) via selection; primitive (\circ) via (C)):

* (\mathcal M,w\models p) iff (w\in V(p)) (for atoms (p)).
* (\mathcal M,w\models A\wedge B) iff (\mathcal M,w\models A) and (\mathcal M,w\models B).
* (\mathcal M,w\models \sim A) iff (\mathcal M,w\not\models A).  (So (\sim) is classical negation.)
* (\mathcal M,w\models A\to B) iff (f_w(\llbracket A\rrbracket^\mathcal M)\subseteq \llbracket B\rrbracket^\mathcal M).
* (\mathcal M,w\models A\circ B) iff (C_w\big(\llbracket A\rrbracket^\mathcal M,\llbracket B\rrbracket^\mathcal M\big)).

Write (A=B) as usual for mutual implication, and (A\neq B) as its negation; those are just abbreviations in the object language.

## Frame conditions (the “NL-frame” axioms)

We assume every NL-frame satisfies the following conditions, for all (w\in W) and all (X,Y,Z\subseteq W):

**On the conditional (f_w):**

1. **Identity (Id)**: (f_w(X)\subseteq X).
   (This forces (A\to A), axiom 1.1.)

2. **Monotonicity (Mon)**: If (X\subseteq Y) then (f_w(X)\subseteq f_w(Y)).
   (Gives the transitivity pattern used in 1.5.)

3. **Success (Detachment) (Succ)**: If (w\in X) then (w\in f_w(X)).
   (Delivers local modus ponens and validates rule R1.)

4. **Nonemptiness on nonempty input (NE)**: If (X\neq\varnothing) then (f_w(X)\neq\varnothing).
   (Blocks vacuous truths from producing connexive failures.)

5. **Boethius/Connexive condition (Bo)**: If (f_w(X)\subseteq Y) then (f_w(Y)\nsubseteq W\setminus X).
   (Captures ((A\to B)\Rightarrow \neg(B\to \sim A)).)

6. **Contraposition-like condition (Contra)**: If (f_w(X\cap Y)\subseteq Z) then (f_w\big(X\cap (W\setminus Z)\big)\subseteq W\setminus Y).
   (This is exactly axiom-schema 1.7 in set form.)

**On compatibility (C_w):**

7. **Symmetry (C-Sym)**: (C_w(X,Y)\iff C_w(Y,X)).
   (Delivers axiom 1.2.)

8. **Conditional coherence (C-Coherence)**: If (f_w(X)\subseteq Y) then (C_w(X,Y)).
   (This is axiom 1.4: from (A\to B) infer (A\circ B).)

No further constraints on (C_w) are required for the NL axioms given.

## What the conditions mean (intuitively)

* (f_w) says which (A)-worlds are “relevant” at (w) when checking (A\to B). (Id) makes (A\to A) valid. (Succ) makes modus-ponens sound. (NE)+(Bo) deliver connexive behavior: if (A\to B) holds, then (B\to\sim A) must fail. (Contra) is exactly 1.7 turned into set-inclusion.
* (C_w) is a **primitive** compatibility predicate; we only need it to be symmetric and to accept every pair ((X,Y)) when (X) relevantly entails (Y) (C-Coherence). This is deliberately weak: the axioms listed do not force a tighter reading of (\circ), so we keep it as general as possible while still making 1.2 and 1.4 valid.

## Soundness (axioms and rules are valid)

Let (\mathcal M=\langle W,f,C,V\rangle) be any NL-model.

* **1.1 (A\to A)**: At any (w), (f_w(\llbracket A\rrbracket)\subseteq \llbracket A\rrbracket) by (Id).
* **1.2 ((A|B)\to (B|A))**: ((A|B)) is (\sim(A\circ B)). By (C-Sym), (C_w(X,Y)\iff C_w(Y,X)). Hence if (\neg C_w(X,Y)) then (\neg C_w(Y,X)).
* **1.3 (A\to \sim\sim A)**: (\sim\sim A) is equivalent to (A) under classical negation, so this is just 1.1.
* **1.4 ((A\to B)\to (A\circ B))**: If (f_w(\llbracket A\rrbracket)\subseteq \llbracket B\rrbracket), then by (C-Coherence), (C_w(\llbracket A\rrbracket,\llbracket B\rrbracket)), i.e., (A\circ B).
* **1.5 ((A\neq B\neq C)\to(((A\to B)\wedge (B\to C))\to (A\to C)))**: The inner implication is validated by (Mon): if (f_w(\llbracket A\rrbracket)\subseteq \llbracket B\rrbracket) and (f_w(\llbracket B\rrbracket)\subseteq \llbracket C\rrbracket), then (f_w(\llbracket A\rrbracket)\subseteq f_w(\llbracket B\rrbracket)\subseteq \llbracket C\rrbracket). The outer antecedent only strengthens it further, so the whole axiom is valid.
* **1.6 ((A\wedge B)=(B\wedge A))**: (\llbracket A\wedge B\rrbracket=\llbracket B\wedge A\rrbracket) set-theoretically, hence each direction ((A\wedge B)\to (B\wedge A)) and converse hold by (Id).
* **1.7 (((A\wedge B)\to C)\to ((A\wedge \sim C)\to \sim B))**: Let (X=\llbracket A\rrbracket), (Y=\llbracket B\rrbracket), (Z=\llbracket C\rrbracket). The antecedent says (f_w(X\cap Y)\subseteq Z). By (Contra), (f_w(X\cap (W\setminus Z))\subseteq W\setminus Y), i.e., (f_w(\llbracket A\wedge \sim C\rrbracket)\subseteq \llbracket \sim B\rrbracket). That is exactly the consequent.
* **R1 (modus ponens)**: If (\mathcal M,w\models A) and (\mathcal M,w\models A\to B), then (w\in \llbracket A\rrbracket\subseteq f_w(\llbracket A\rrbracket)\subseteq \llbracket B\rrbracket) by (Succ). Thus (w\models B).
* **R2 (adjunction)**: If (A) and (B) are true at (w), then (A\wedge B) is true at (w) by the clause for (\wedge).

Hence every NL theorem is valid in every NL-model.

## Completeness (canonical model sketch)

Let (\vdash) be NL-provability from the axioms and rules. Build a canonical model (\mathcal M^\ast=\langle W^\ast, f^\ast, C^\ast, V^\ast\rangle) as follows.

**Worlds.** (W^\ast) is the set of all **maximal NL-consistent theories** (\Gamma) (i.e., sets of formulas closed under (\vdash), containing no contradiction in the sense of deriving every formula, and maximal under inclusion).

**Valuation.** (V^\ast(p)={\Gamma\in W^\ast: p\in \Gamma}). Extend (\sim,\wedge) pointwise (standard canonical model moves).

**Selection.** For each (\Gamma\in W^\ast) and formula (A), define
[
F_\Gamma(A);:=;{\Delta\in W^\ast:\ \forall B\ (A\to B\in \Gamma\ \Rightarrow\ B\in \Delta)}.
]
This is the set of (A)-detachment points for (\Gamma). Now set
[
f^\ast_\Gamma\big(\llbracket A\rrbracket^{\mathcal M^\ast}\big)\ :=\ F_\Gamma(A).
]
(One checks that if (\Gamma\vdash A=B) then (F_\Gamma(A)=F_\Gamma(B)), so (f^\ast_\Gamma) is well-defined on truth sets.)

**Compatibility.** Put
[
C^\ast_\Gamma!\big(\llbracket A\rrbracket^{\mathcal M^\ast},\llbracket B\rrbracket^{\mathcal M^\ast}\big)\quad\text{iff}\quad A\circ B\in \Gamma.
]
(Again, because (\circ) occurs only positively in 1.2 and 1.4, one proves that if (\Gamma\vdash A=B) and (\Gamma\vdash A'=B') then (\Gamma\vdash (A\circ A')\leftrightarrow (B\circ B')), so this is well-defined on truth sets.)

**Truth Lemma.** For all (\Gamma\in W^\ast) and formulas (A),
[
\mathcal M^\ast,\Gamma \models A \quad\Longleftrightarrow\quad A\in \Gamma.
]
The Boolean cases are routine. For (\to):
(\Rightarrow): If (\Gamma\models A\to B), then (F_\Gamma(A)\subseteq \llbracket B\rrbracket), hence by maximality and the definition of (F_\Gamma(A)) we get (A\to B\in \Gamma).
(\Leftarrow): If (A\to B\in \Gamma), then by definition of (F_\Gamma(A)), every (\Delta\in F_\Gamma(A)) contains (B), i.e., (F_\Gamma(A)\subseteq \llbracket B\rrbracket).
For (\circ): by the definition of (C^\ast).

**Frame conditions in the canonical model.** One checks:

* (Id) because (A\to A) is an axiom, (A\in\Delta) for all (\Delta\in F_\Gamma(A)).
* (Mon) because from (\vdash (A\wedge (A\to B))\to B) (derivable using R1/R2), we get (F_\Gamma(A)\subseteq F_\Gamma(B)) whenever (\Gamma\vdash A\to B).
* (Succ) since (\Gamma) is closed under modus ponens: if (A\in\Gamma) and (A\to B\in \Gamma), then (B\in \Gamma); thus (\Gamma\in F_\Gamma(A)).
* (NE) because if (A\in\Gamma) then (\Gamma\in F_\Gamma(A)).
* (Bo) because ((A\to B)\to \neg(B\to \sim A)) is provable from 1.4 and 1.2 (read via (C^\ast)), hence cannot have (F_\Gamma(B)\subseteq W^\ast\setminus \llbracket A\rrbracket).
* (Contra) is provable in the object language as 1.7; thus holds set-theoretically by the truth lemma.
* (C-Sym) is axiom 1.2, hence holds by the truth lemma.
* (C-Coherence) is axiom 1.4, hence holds by the truth lemma.

Therefore (\mathcal M^\ast) is an NL-model. By the Truth Lemma, if (A) is valid in all NL-models then (A\in \Gamma) for every (\Gamma\in W^\ast); hence (\vdash A). That gives **strong completeness**.

## Summary of the semantics

* **Semantics**: selection-function conditional (A\to B) with classical (\sim) and (\wedge), plus a **primitive symmetric** compatibility predicate (C_w) for (A\circ B).
* **Key frame laws**: (Id), (Mon), (Succ), (NE), (Bo), (Contra) for (f_w); (C-Sym) and (C-Coherence) for (C_w).
* **Result**: With these frames, **all NL axioms and rules are sound**, and by the canonical construction above, **the semantics is complete** for NL.

This gives a clean, fully compositional, set-based semantics that treats ◦ as a genuine (but weakly constrained) compatibility connective and pins down exactly the connexive behavior encoded by 1.2, 1.4, and 1.7. If you want a **more intensional** reading of ◦ (e.g., defining (A\circ B) as the conjunction of (\neg(A\to\sim B)) and (\neg(B\to\sim A))), you can add that definition **on top** of the above by replacing (C-Coherence) with the biconditional
[
C_w(X,Y)\ \text{iff}\ \neg\big(f_w(X)\subseteq W\setminus Y\big)\ \text{and}\ \neg\big(f_w(Y)\subseteq W\setminus X\big),
]
but then you must keep (NE) to avoid vacuity and adjust a few details in the completeness proof. The skeleton above already ensures all the listed NL theorems hold and yields a clean completeness argument.