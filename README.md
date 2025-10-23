# NelsonNL

“Providing a sound and complete semantics for NL is an open problem in connexive logic.” —Heinrich Wansing, [SEP](https://plato.stanford.edu/entries/logic-connexive/)

This project is a vibe-specified, vibecoded attempt to solve this open problem. I only began this because, when I threw the problem at ChatGPT for kicks, it spat out something that looked correct even to my math-understanding friends. Now I’m trying to finish it so as to give humanity a working semantics for these axioms.

The project consists of a semantics in Markdown+Latex which is at `ChatGPT_semantics.md`, and a Lean attempt to formalize it. At first, the project wrongly had classical negation. The current version seems to have successfully fixed this, but I am reviewing it. In particular, `Semantics.lean` seems to be somewhat stronger than specified by `ChatGPT_semantics.md`, which might mean it’s wrong.