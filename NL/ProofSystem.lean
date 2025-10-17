/-
NL — Hilbert interface (used by Canonical/completeness)
* Kept separate to avoid circular deps.
-/
import NL.Language

namespace NL
namespace ProofSystem

class NLProofSystem (α : Type _) where
  Provable : Formula α → Prop
  mp       : ∀ {A B}, Provable A → Provable (A →ₗ B) → Provable B
  adj      : ∀ {A B}, Provable A → Provable B → Provable (A ∧ₗ B)
  ax11     : ∀ A, Provable (A →ₗ A)
  ax12     : ∀ A B, Provable ((A |ₗ B) →ₗ (B |ₗ A))
  ax13     : ∀ A, Provable (A →ₗ (¬ₗ ¬ₗ A))
  ax14     : ∀ A B, Provable ((A →ₗ B) →ₗ (A ◦ B))
  ax15     : ∀ A B C, Provable ((Formula.neq3 A B C) →ₗ (((A →ₗ B) ∧ₗ (B →ₗ C)) →ₗ (A →ₗ C)))
  ax16     : ∀ A B, Provable ((A ∧ₗ B) =ₗ (B ∧ₗ A))
  ax17     : ∀ A B C, Provable (((A ∧ₗ B) →ₗ C) →ₗ ((A ∧ₗ (¬ₗ C)) →ₗ (¬ₗ B)))

end ProofSystem
end NL
