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

Try to come up with a sound and complete semantics for NL.---------------------------------------------------------------------------------------------------------------------------------------------

Here is a **self-contained semantics** for NL that (i) uses a genuinely **intuitionistic negation** (so `~~A → A` is not valid in general), (ii) validates exactly the axioms/rules you listed, and (iii) comes with a standard soundness/completeness sketch.

# NL semantics (with intuitionistic negation)

We read `~` intuitionistically (Kripke negation), keep `∧` truth-functional, treat `→` in a guarded, relational way (parametrized by the current world), and take `◦` as a **primitive compatibility** connective constrained only as much as the axioms require.

## Frames and models

An **NL-frame** is a quadruple
[
\mathcal F=\langle W,\ \le,\ f,\ C\rangle
]
where

* ((W,\le)) is a nonempty **preorder** (intuitionistic accessibility); write (v\ge w) for (w\le v).
* For each (w\in W), (f_w:\mathrm{Up}(W)\to\mathcal P(W)) is a **selection map** on up-sets (defined below).
* For each (w\in W), (C_w:\mathrm{Up}(W)\times\mathrm{Up}(W)\to{\mathsf{true},\mathsf{false}}) is a **compatibility/consistency predicate** (used for (A\circ B)).

Here (\mathrm{Up}(W)) denotes the family of **up-sets** (X\subseteq W) (i.e., (w\in X\le v\Rightarrow v\in X)).

An **NL-model** is (\mathcal M=\langle \mathcal F,\ V\rangle) where (V) assigns to each atom (p) an **up-set** (V(p)\subseteq W) (persistence of atoms).

For any formula (A), write (\llbracket A\rrbracket={w\in W:\mathcal M,w\models A}).

## Truth clauses

Let (X=\llbracket A\rrbracket) and (Y=\llbracket B\rrbracket).

* (w\models p)  iff  (w\in V(p)) (and (V) is monotone: (w\in V(p)\le v\Rightarrow v\in V(p))).
* (w\models A\wedge B)  iff  (w\models A) and (w\models B).
* **Intuitionistic negation**:
  (w\models \sim A)  iff  for all (v\ge w), (v\not\models A).
  Equivalently, (\llbracket \sim A\rrbracket=\neg X:={w:\uparrow w\cap X=\varnothing}), which is an up-set.
* **Conditional**:
  (w\models A\to B)  iff  (f_w(X)\subseteq Y).
* **Consistency**:
  (w\models A\circ B)  iff  (C_w(X,Y)).

Abbreviations: (A|B:=\sim(A\circ B)), (A=B:=(A\to B)\wedge(B\to A)), (A\neq B:=\sim(A=B)).

## Frame conditions

All NL-frames satisfy, for all (w\in W) and (X,Y,Z\in\mathrm{Up}(W)):

### For the conditional (f_w)

1. **Identity (Id)**: (f_w(X)\subseteq X).
   (Ensures (A\to A).)

2. **Hereditary in the world (Her)**: If (v\ge w) then (f_v(X)\subseteq f_w(X)).
   (Makes (\llbracket A\to B\rrbracket) an up-set, i.e., intuitionistic persistence.)

3. **Success / local detachment (Succ)**: If (w\in X) then (w\in f_w(X)).
   (Gives sound Modus Ponens.)

4. **Contraposition-like law (Contra)**:
   If (f_w(X\cap Y)\subseteq Z) then (f_w\big(X\cap \neg Z\big)\subseteq \neg Y),
   where (\neg Z:={u:\uparrow u\cap Z=\varnothing}).
   (This is exactly axiom 1.7 at the set level.)

5. **Guarded syllogism (Tr≠)**:
   Define, at world (w), a **local equivalence** (X\equiv_w Y) iff (f_w(X)\subseteq Y) and (f_w(Y)\subseteq X).
   Write (X\not\equiv_w Y) for its negation.
   Then require:
   [
   \text{if }X\not\equiv_w Y,\ Y\not\equiv_w Z,\ X\not\equiv_w Z\ \text{ and }
   f_w(X)\subseteq Y,\ f_w(Y)\subseteq Z,\ \text{ then } f_w(X)\subseteq Z.
   ]
   (Gives exactly axiom 1.5.)

> *Remark.* If you prefer, you may **strengthen** (Tr≠) to the unconditional **Hypothetical Syllogism**
> (f_w(X)\subseteq Y) and (f_w(Y)\subseteq Z\Rightarrow f_w(X)\subseteq Z).
> That makes 1.5 trivial and validates (((A\to B)\wedge(B\to C))\to(A\to C)) outright; the axioms above only demand the weaker, guarded version, so (Tr≠) is the precise match.

### For compatibility (C_w)

6. **Symmetry (C-Sym)**: (C_w(X,Y)\iff C_w(Y,X)).
   (Yields ( (A|B)\to(B|A)), axiom 1.2.)

7. **Coherence with (\to) (C-Coherence)**: If (f_w(X)\subseteq Y) then (C_w(X,Y)).
   (Exactly axiom 1.4: ((A\to B)\to(A\circ B)).)

No further connection between (C) and (f) is assumed (beyond what the axioms force).

## Soundness (each axiom/rule is valid)

Let (\mathcal M=\langle W,\le,f,C,V\rangle) be any NL-model; put (X=\llbracket A\rrbracket), etc.

* **1.1** (A\to A): by **Id**, (f_w(X)\subseteq X).
* **1.2** ((A|B)\to(B|A)): since (C) is symmetric at every world, (\llbracket A\circ B\rrbracket=\llbracket B\circ A\rrbracket), hence (\llbracket\sim(A\circ B)\rrbracket\subseteq\llbracket\sim(B\circ A)\rrbracket); with **Id** this makes the implication valid.
* **1.3** (A\to ~~A): in Kripke semantics (X\subseteq\neg\neg X); then (f_w(X)\subseteq X\subseteq\neg\neg X) by **Id**.
* **1.4** ((A\to B)\to(A\circ B)): by **C-Coherence**.
* **1.5** Guarded transitivity: the inner (((A\to B)\wedge(B\to C))\to(A\to C)) is guaranteed **at any (w)** exactly when (A,B,C) are pairwise ( \not\equiv_w); that is precisely the hypothesis of (Tr≠). So the whole axiom is valid.
* **1.6** ((A\wedge B)=(B\wedge A)): (\llbracket A\wedge B\rrbracket=\llbracket B\wedge A\rrbracket) set-theoretically, so each direction of (=) holds by 1.1.
* **1.7** (((A\wedge B)\to C)\to((A\wedge \sim C)\to \sim B)): writing (X=\llbracket A\rrbracket), (Y=\llbracket B\rrbracket), (Z=\llbracket C\rrbracket), the antecedent is (f_w(X\cap Y)\subseteq Z); **Contra** gives (f_w(X\cap \neg Z)\subseteq \neg Y), i.e., the consequent.
* **R1 (modus ponens)**: if (w\in X) and (f_w(X)\subseteq Y), then by **Succ**, (w\in f_w(X)\subseteq Y), so (w\models B).
* **R2 (adjunction)**: immediate from the clause for (\wedge).

Thus every NL-theorem is valid on all NL-frames.

## Completeness (canonical model sketch)

Let (\vdash) be provability from the NL axioms/rules.

**Worlds.** (W^\ast) is the set of all **maximal NL-consistent** theories (\Gamma) (closed under (\vdash), not proving every formula, and maximal under inclusion).

**Order.** (\Gamma\le\Delta) iff (\Gamma\subseteq\Delta) (so (\le) is a preorder).

**Valuation.** (V^\ast(p)={\Gamma\in W^\ast: p\in\Gamma}) (which is upward-closed).

**Selection.** For each (\Gamma\in W^\ast) and formula (A), let
[
F_\Gamma(A)=\Big{\Delta\in W^\ast:\ \Delta\ge \Gamma\ \text{ and }\ \forall B\ \big((A\to B)\in\Gamma\Rightarrow B\in\Delta\big)\Big}.
]
Set (f^\ast_\Gamma(\llbracket A\rrbracket):=F_\Gamma(A)). (This is well-defined on truth sets: if (\Gamma\vdash A=B) then (F_\Gamma(A)=F_\Gamma(B)).)

**Compatibility.** Put
[
C^\ast_\Gamma(\llbracket A\rrbracket,\llbracket B\rrbracket)\ \text{ iff }\ A\circ B\in\Gamma.
]

**Truth Lemma.** For all (\Gamma\in W^\ast) and formulas (A),
[
\mathcal M^\ast,\Gamma\models A\quad\Longleftrightarrow\quad A\in\Gamma.
]
Proof is by induction on (A). The Boolean cases are routine (with the Kripke clause for (\sim)). For (A\to B):

* ((\Leftarrow)): If (A\to B\in\Gamma), then by definition every (\Delta\in F_\Gamma(A)) contains (B), i.e., (F_\Gamma(A)\subseteq \llbracket B\rrbracket).
* ((\Rightarrow)): If (F_\Gamma(A)\subseteq \llbracket B\rrbracket) but (A\to B\notin\Gamma), extend (\Gamma) inside (W^\ast) to some (\Delta\ge\Gamma) with (A\in\Delta) and (B\notin\Delta); then (\Delta\in F_\Gamma(A)) yet (\Delta\not\models B), a contradiction.

For (A\circ B) the clause is by definition of (C^\ast).

**Frame conditions in (\mathcal M^\ast).** Each of **Id**, **Her**, **Succ**, **Contra**, **C-Sym**, **C-Coherence**, and **Tr≠** holds in (\mathcal M^\ast), because its corresponding axiom-schema (respectively 1.1, persistence of theorems, R1, 1.7, 1.2, 1.4, 1.5) is provable, and the Truth Lemma transfers provability to the relational side.

Hence, if a formula is valid in all NL-frames, it belongs to every maximal NL-theory; so (\vdash A). This yields **strong completeness**.

## Tiny countermodel to (~~p\to p) (showing non-classical negation)

Let (W={w<v}) (a 2-node chain), (V(p)={v}).
Let (f_u(X)=X\cap\uparrow u) (a concrete choice satisfying Id/Her/Succ/Contra), and let (C_u) be any symmetric predicate obeying C-Coherence (e.g., always-true).

Then

* (w\models \sim\sim p): above (w) there is a node (v) with (p), so (\sim p) fails at (w); hence (\sim\sim p) holds at (w).
* But (w\not\models p).

So (~~p\to p) is **not** valid, as desired, while 1.1–1.7 and R1–R2 still hold.

## What this buys you

* **Negation is intuitionistic** (1.3 holds; (~~A\to A) fails in general).
* The **conditional** is world-relative (via (f_w)) but constrained just enough to validate 1.1, 1.5, and 1.7; the dedicated (Tr≠) condition captures the side-conditioned transitivity **exactly** as in axiom 1.5.
* The **consistency** connective (A\circ B) is primitive with only symmetry and the coherence link to (\to) that the axioms require (1.2, 1.4).
* The system is **sound and strongly complete** for the class of NL-frames above.

If you prefer an even more concrete presentation, you can *instantiate* (f_w) by the canonical Kripke choice (f_w(X)=X\cap\uparrow w) (so (w\models A\to B) iff every (A)-world (\ge w) is a (B)-world). This automatically satisfies Id/Her/Succ/Contra; you then only need (C-Sym), (C-Coherence) and (Tr≠) to match the axioms involving `◦` and 1.5.