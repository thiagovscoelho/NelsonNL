# NelsonNL

Providing a sound and complete semantics for NL is an open problem in connexive logic.

This project is a vibe-specified, vibecoded attempt to solve it. I only began this because, when I threw the problem at ChatGPT for kicks, it spat out something that looked correct even to my math-understanding friends. Now I’m trying to finish it so as to give humanity a working semantics for these axioms.

The project consists of a semantics in Markdown+Latex which is at `ChatGPT_semantics.md`, and a Lean attempt to formalize it. At first, the project wrongly had classical negation. The current version is in the process of fixing this.

Current project status (AFAICT):
- `Language.lean` seems OK.
- `Semantics.lean` seems OK. It is somewhat stronger than specified by `ChatGPT_semantics.md`, which should be edited later to reflect it.
- `Soundness.lean` also seems accurate.
- The files `ProofSystem.lean`, `Lindenbaum.lean`, and `Canonical.lean` are still as they were when I was wrongly assuming negation was classical in NL, so they are probably wrong.
- The files `Examples.lean`, `Utils.lean`, and `Main.lean` have also not been reviewed for compliance yet, but they are just scaffolding.

Despite all the wrong files, the current build mysteriously compiles. It is still not ready, however.