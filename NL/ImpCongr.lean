/-
Congruence for → on the antecedent (needed for extensionality of F_Γ(·)).
We require both directions as provable implications when A =ₗ A' is provable.
-/
import NL.ProofSystem

namespace NL
namespace ProofSystem

/-- Left-congruence of implication under provable extensional equality.

From `Provable (A =ₗ A')` we get *both* directions:
`Provable ((A →ₗ B) →ₗ (A' →ₗ B))` and
`Provable ((A' →ₗ B) →ₗ (A →ₗ B))`. -/
class HasImpCongrLeft (α : Type _) [NLProofSystem α] : Prop where
  imp_congr_left :
    ∀ {A A' B : Formula α},
      NLProofSystem.Provable (A =ₗ A') →
      ( NLProofSystem.Provable ((A →ₗ B)  →ₗ (A' →ₗ B))
      ∧ NLProofSystem.Provable ((A' →ₗ B) →ₗ (A  →ₗ B)) )

end ProofSystem
end NL
