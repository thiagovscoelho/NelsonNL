/-
NL — Canonical model, Truth Lemma, completeness
* This is the file you'll implement next.
* It **depends** on Semantics and ProofSystem.
-/
import NL.Semantics
import NL.ProofSystem
-- If you split Language.lean, Semantics already brings it in.

open Classical Set
noncomputable section

namespace NL

-- Worlds = maximal NL-theories (to be developed in NL.Lindenbaum)
-- import NL.Lindenbaum  -- when ready

-- def WCan := …      -- canonical worlds
-- def frameCan : Frame WCan := …
-- def modelCan (α) : Model α := …
-- theorem truth_lemma : ∀ Γ A, Sat (modelCan _) Γ A ↔ A ∈ Γ := …
-- theorem completeness {α} [ProofSystem.NLProofSystem α] :
--   Model.Valid (A : Formula α) → ProofSystem.NLProofSystem.Provable A := …

end NL
