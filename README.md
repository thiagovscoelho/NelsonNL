# NelsonNL

“Providing a sound and complete semantics for NL is an open problem in connexive logic.” —Heinrich Wansing, [SEP](https://plato.stanford.edu/entries/logic-connexive/)

This project is a vibe-specified, vibecoded attempt to solve this open problem. I only began this because, when I threw the problem at ChatGPT for kicks, it spat out something that looked correct even to my math-understanding friends. Now I’m trying to finish it so as to give humanity a working semantics for these axioms.

The project consists of a semantics in Markdown+Latex which is at `ChatGPT_semantics.md`, and a Lean attempt to formalize it. At first, the project wrongly had classical negation. The current version seems to have successfully fixed this, but now I noticed that the Lean code validates the unconditional version of hypothetical syllogism, `(((A → B) ∧ (B → C)) → (A → C))`, instead of the “guarded” hypothetical syllogism `(A ≠ B ≠ C) → (((A → B) ∧ (B → C)) → (A → C))` from the original axioms. This is something I am looking into how to fix. Also, is the antecedent `A ≠ B ≠ C` meant to allow `A = C`? I might have to look into a primary source instead of relying on the SEP.