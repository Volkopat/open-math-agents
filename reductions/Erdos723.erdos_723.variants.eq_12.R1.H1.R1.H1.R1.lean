import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1

/-!
# A 139-block seed for the 140-block existence step

The parent step is the 140-block seed in @seanm27lol's reduction of
@ian139's order-twelve reduction. The construction below needs an arbitrary
139-block seed and a theorem extending every such seed on the same points.
The latter extension has also been reported by @laurilehtinen.
-/

namespace OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1_H1_R1

/-- Existence of 139 blocks of size thirteen, each pair meeting once. -/
def H1 : Prop :=
  ∃ S : Finset (Finset (Fin 157)), S.card = 139 ∧ (∀ b ∈ S, b.card = 13) ∧
    ∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

/-- Extend every 139-block seed to 140 blocks while retaining every old block. -/
def H2 : Prop :=
  ∀ S : Finset (Finset (Fin 157)), S.card = 139 →
    (∀ b ∈ S, b.card = 13) →
    (∀ b ∈ S, ∀ c ∈ S, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c) →
    ∃ T : Finset (Finset (Fin 157)), S ⊆ T ∧ T.card = 140 ∧
      (∀ b ∈ T, b.card = 13) ∧ ∀ b ∈ T, ∀ c ∈ T, b ≠ c → ∃! x, x ∈ b ∧ x ∈ c

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1.H1 := by
  rintro ⟨S, size, blocks, meets⟩ extend
  obtain ⟨T, _, count, sizes, intersections⟩ := extend S size blocks meets
  exact ⟨T, count, sizes, intersections⟩

end OMA.R_Erdos723_erdos_723_variants_eq_12_R1_H1_R1_H1_R1
