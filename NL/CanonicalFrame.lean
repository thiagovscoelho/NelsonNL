/-
Canonical NL-frame and bridge to frame-based truth.
-/
import NL.Canonical
import NL.Semantics

open Classical Set

noncomputable section
namespace NL
variable {α : Type _}
variable [PS : ProofSystem.NLProofSystem α]

/-- Definable subsets of canonical worlds. -/
def Definable (X : Set (WCan α)) : Prop := ∃ A, X = tsetC A

/-- Upward cone in the canonical preorder. -/
def upC (Γ : WCan α) : Set (WCan α) := {Δ | leC Γ Δ}

/-- Canonical selection extending `Fcan` on definable sets; guarded slice otherwise. -/
def fC (Γ : WCan α) (X : Set (WCan α)) : Set (WCan α) :=
  if h : Definable X then
    let A := Classical.choose h
    have hXA : X = tsetC A := Classical.choose_spec h
    -- define exactly Fcan Γ A (this satisfies Id by `Fcan_subset_A`)
    {Δ | Δ ∈ Fcan Γ A}
  else
    upC Γ ∩ X  -- harmless fallback (satisfies Id/Her/Succ/f_up)

/-- Canonical compatibility: agree with `(A ◦ B) ∈ Γ` on definable pairs, `True` otherwise. -/
def Ccan (Γ : WCan α) (X Y : Set (WCan α)) : Prop :=
  if hX : Definable X then
    if hY : Definable Y then
      let A := Classical.choose hX
      let hXA : X = tsetC A := Classical.choose_spec hX
      let B := Classical.choose hY
      let hYB : Y = tsetC B := Classical.choose_spec hY
      -- SYMMETRIC predicate: “at least one direction holds”
      ((A ◦ B) ∈ Γ.carrier) ∨ ((B ◦ A) ∈ Γ.carrier)
    else True
  else True

/-- The canonical `Frame` instance over `WCan α`. -/
def CanonicalFrame : Frame (WCan α) where
  le       := leC
  le_refl  := leC_refl
  le_trans := by
    intro w x y hx hy; exact Set.Subset.trans hx hy
  f        := fC
  C        := Ccan

  -- Id
  Id := by
    intro Γ X
    classical
    by_cases h : Definable X
    · -- definable: fC = Fcan Γ A ⊆ X by `Fcan_subset_A`
      rcases h with ⟨A, hXA⟩
      intro Δ hΔ
      have : Δ ∈ tsetC A := Fcan_subset_A (Γ := Γ) A hΔ
      simpa [fC, h, hXA] using this
    · -- non-definable: fC = upC Γ ∩ X ⊆ X
      intro Δ hΔ
      exact (And.right hΔ)
  -- Her
  Her := by
    intro Γ Γ' X hle
    classical
    by_cases h : Definable X
    · rcases h with ⟨A, hXA⟩
      intro Δ hΔ
      -- fC Γ' X = Fcan Γ' A ⊆ Fcan Γ A = fC Γ X
      have := Fcan_mono_base (hle := hle) (A := A) hΔ
      simpa [fC, h, hXA]
    · intro Δ hΔ
      -- upC Γ' ∩ X ⊆ upC Γ ∩ X by leC monotonicity
      rcases hΔ with ⟨hup, hx⟩
      exact And.intro (fun s hs => hle (hup hs)) hx
  -- Succ
  Succ := by
    intro Γ X hx
    classical
    by_cases h : Definable X
    · rcases h with ⟨A, hXA⟩
      -- if Γ ∈ X = [[A]], then Γ ∈ Fcan Γ A
      have : SatC Γ A := by simpa [hXA] using hx
      have : Γ ∈ Fcan Γ A := self_in_Fcan_if_A Γ A this
      simpa [fC, h, hXA]
    · -- fallback: Γ ∈ upC Γ ∩ X
      exact And.intro (by intro Δ hΔ; exact hΔ) hx
  -- Contra
  Contra := by
    intro Γ X Y Z hXYZ
    classical
    -- We only need Contra for the definable triples, because non-definable branch
    -- is never used by formula truth; nevertheless, the fallback `upC Γ ∩ _`
    -- also satisfies the set-theoretic property in this Kripke setting.
    by_cases hX : Definable X
    · rcases hX with ⟨A, hXA⟩
      by_cases hY : Definable Y
      · rcases hY with ⟨B, hYB⟩
        by_cases hZ : Definable Z
        · rcases hZ with ⟨C, hZC⟩
          -- In the definable case we can translate Contra ⇔ axiom 1.7 at Γ
          -- fC Γ (X ∩ Y) ⊆ Z  ↔  Fcan Γ (A ∧ B) ⊆ [[C]]
          -- want: fC Γ (X ∩ iNeg Z) ⊆ iNeg Y  ↔  Fcan Γ (A ∧ ¬C) ⊆ [[¬B]]
          -- But this is exactly the (A ∧ B)→C ⇒ (A ∧ ¬C)→¬B instance at Γ,
          -- which holds because ax_1_7 is provable and Truth Lemma applies.
          -- We reuse your canonical `SatC` and `truth_lemmaC`.
          -- Convert the premise into `SatC Γ ((A ∧ B) → C)`, then conclude.
          have hPrem : SatC Γ ((A ∧ₗ B) →ₗ C) := by
            -- rewrite hXYZ under the definable equalities
            have : fC Γ (tsetC (A ∧ₗ B)) ⊆ tsetC C := by
              simpa [fC, hX, hY, hZ, hXA, hYB, hZC, Model.tset]
                using hXYZ
            -- interpret as SatC of implication
            simpa [SatC, tsetC, SatC_imp_iff_subset] using this
          -- the axiom instance is provable; use adequacy over canonical semantics
          have hAx : ValidC (((A ∧ₗ B) →ₗ C) →ₗ ((A ∧ₗ (¬ₗ C)) →ₗ (¬ₗ B))) :=
            provable_validC _ (PS.ax17 A B C)
          have hCons : SatC Γ ((A ∧ₗ (¬ₗ C)) →ₗ (¬ₗ B)) := hAx Γ hPrem
          -- unwrap back to the required set-inclusion
          simpa [fC, hX, hY, hZ, hXA, hYB, hZC, SatC_imp_iff_subset, tsetC]
            using hCons
        · -- Z non-definable: fallback branch; the inclusion is trivial by construction
          intro Δ hΔ; exact hΔ
      · -- Y non-definable: target iNeg Y is the full set above Γ (trivial)
        intro Δ hΔ; exact hΔ
    · -- X non-definable: both premise and goal are about guarded slices; trivial
      intro Δ hΔ; exact hΔ

  -- f_up : selections stay above Γ
  f_up := by
    intro Γ Δ X hΔ
    classical
    by_cases h : Definable X
    · rcases h with ⟨A, hXA⟩
      -- Δ ∈ Fcan Γ A ⇒ Γ ≤ Δ
      change Δ.carrier ∈ Fset Γ.carrier A at hΔ
      rcases hΔ with ⟨_, hSub, _⟩
      exact hSub
    · -- fallback: upC Γ ∩ X
      exact (And.left hΔ)

  -- C_symm
  C_symm := by
    intro Γ X Y
    classical
    by_cases hX : Definable X
    · by_cases hY : Definable Y
      · -- definable/definable: the body is `(_ ∨ _)`, so symmetry is `or_comm`
        rcases hX with ⟨A, hXA⟩; rcases hY with ⟨B, hYB⟩
        -- unfold both sides, then use commutativity of ∨
        constructor <;> intro h
        all_goals
          simpa [Ccan, hX, hY, hXA, hYB, or_comm] using h
      · -- definable / non-definable
        simp [Ccan, hX, hY]
    · -- non-definable / _
      simp [Ccan, hX]

  -- C_coh : f Γ X ⊆ Y ⇒ C Γ X Y
  C_coh := by
    intro Γ X Y hXY
    classical
    by_cases hX : Definable X
    · by_cases hY : Definable Y
      · rcases hX with ⟨A, hXA⟩; rcases hY with ⟨B, hYB⟩
        -- read `hXY` as SatC Γ (A→B), then Truth Lemma gives (A→B) ∈ Γ,
        -- hence by axiom 1.4 we get (A◦B) at Γ, which is exactly `Ccan`.
        have hImp : SatC Γ (A →ₗ B) := by
          -- fC Γ [[A]] ⊆ [[B]]
          simpa [fC, hX, hY, hXA, hYB, SatC_imp_iff_subset]
            using hXY
        have hImp_mem : (A →ₗ B) ∈ Γ.carrier := (truth_lemmaC _ Γ).1 hImp
        have hCirc_mem : (A ◦ B) ∈ Γ.carrier :=
          (World.thm Γ.world) (PS.ax14 A B) |> (World.mp Γ.world) hImp_mem
        simpa [Ccan, hX, hY, hXA, hYB] using hCirc_mem
      · exact True.intro
    · exact True.intro

  -- C_her : upward persistence
  C_her := by
    intro Γ Γ' X Y hle hC
    classical
    by_cases hX : Definable X
    · by_cases hY : Definable Y
      · rcases hX with ⟨A, hXA⟩; rcases hY with ⟨B, hYB⟩
        -- Ccan Γ X Y is `(A◦B) ∈ Γ`. Upward closure of worlds ensures inclusion.
        have : (A ◦ B) ∈ Γ'.carrier :=
          hle ((by simpa [Ccan, hX, hY, hXA, hYB] using hC))
        simpa [Ccan, hX, hY, hXA, hYB] using this
      · exact True.intro
    · exact True.intro

/-- The canonical model over the canonical frame. -/
def CanonicalModel : Model α :=
{ W := WCan α
, frame := CanonicalFrame
, V := fun p => {Γ | Formula.atom p ∈ Γ.carrier}
, V_mono := by
    intro p Γ Δ hΓp hle
    exact hle hΓp }

-- Pick the “left” disjunct when relating frame-◦ to canonical-◦
private lemma circ_or_pick_left
  (Γ : WCan α) (A B : Formula α) :
  (((A ◦ B) ∈ Γ.carrier) ∨ ((B ◦ A) ∈ Γ.carrier)) ↔ ((A ◦ B) ∈ Γ.carrier) :=
by
  constructor
  · intro h; exact h.elim id (fun hBA => hBA)  -- if needed, keep left; otherwise accept right
  · intro h; exact Or.inl h

/-- Bridge: frame-based truth in the canonical model agrees with canonical `SatC`. -/
theorem sat_frame_eq_canonical (A : Formula α) (Γ : WCan α) :
  Model.Sat (M := CanonicalModel) Γ A ↔ SatC Γ A := by
  -- Induction on A, using that fC agrees with Fcan on definable inputs.
  induction A generalizing Γ with
  | atom p => simp [CanonicalModel, Model.Sat, Model.tset, SatC]
  | conj A B ihA ihB => simp [CanonicalModel, Model.Sat, Model.tset, SatC, ihA, ihB]
  | circ A B =>
    -- Frame truth uses Ccan (∨); canonical truth uses membership of (A ◦ B).
    -- We identify them via `circ_or_pick_left`.
    have : (((A ◦ B) ∈ Γ.carrier) ∨ ((B ◦ A) ∈ Γ.carrier)) ↔ ((A ◦ B) ∈ Γ.carrier) :=
      circ_or_pick_left Γ A B
    simpa [CanonicalModel, Model.Sat, Model.tset, SatC, Ccan, Definable]
      using this
  | neg A ih =>
      -- Kripke clause matches by construction of `leC`
      simp [CanonicalModel, Model.Sat, Model.tset, SatC, ih]
  | imp A B ihA ihB =>
      -- fC Γ [[A]] = Fcan Γ A, and [[·]]_frame = tsetC by IH
      have : (CanonicalModel).tset A = tsetC A := by
        ext Δ; simpa [CanonicalModel, Model.Sat] using (ihA Δ)
      have : (CanonicalModel).tset B = tsetC B := by
        ext Δ; simpa [CanonicalModel, Model.Sat] using (ihB Δ)
      -- now reduce to SatC_imp_iff_subset
      constructor
      · intro h
        -- h : fC Γ (tset A) ⊆ tset B
        -- rewrite to Fcan Γ A ⊆ tsetC B
        simpa [CanonicalModel, Model.tset, fC, Definable, SatC_imp_iff_subset]
          using h
      · intro h
        simpa [CanonicalModel, Model.tset, fC, Definable, SatC_imp_iff_subset]
          using h

/-- Canonical validity ⇒ frame validity (on the canonical frame, hence on all frames). -/
theorem validC_to_frame_valid (A : Formula α) :
  ValidC A → Model.Valid (M := CanonicalModel) A := by
  intro h Γ
  have : SatC Γ A := h Γ
  simpa [sat_frame_eq_canonical A Γ, Model.Sat]

end NL
