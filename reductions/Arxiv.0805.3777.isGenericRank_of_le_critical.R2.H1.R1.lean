import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2

-- Credit: @kumagi

/-!
The width-two increment for the expected rank of (5,m,m+1) is already
constant from m = 7. The formats at m = 5 through 8 are the only seeds
needed if the tangent-space witness can be extended with five new terms.
-/

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2_H1_R1

private def expectedRank (m : ℕ) : ℕ := 5 * m * (m + 1) ⌈/⌉ (5 + m + (m + 1) - 2)

private lemma ceil_eq_of_bounds {D N q : ℕ} (hD : 0 < D)
    (hlo : D * q < N) (hhi : N ≤ D * (q + 1)) : N ⌈/⌉ D = q + 1 := by
  apply le_antisymm ((ceilDiv_le_iff_le_mul hD).mpr hhi)
  by_contra! hn
  exact (not_lt_of_ge ((ceilDiv_le_iff_le_mul hD).mp (show N ⌈/⌉ D ≤ q by omega))) hlo

theorem expectedRank_odd (k : ℕ) : expectedRank (2 * (k + 2) + 1) = 5 * k + 11 := by
  unfold expectedRank
  rw [show 5 + (2 * (k + 2) + 1) + (2 * (k + 2) + 1 + 1) - 2 = 4 * k + 14 by omega,
    show 5 * k + 11 = (5 * k + 10) + 1 by omega]
  exact ceil_eq_of_bounds (by omega) (by nlinarith) (by nlinarith)

theorem expectedRank_even (k : ℕ) : expectedRank (2 * (k + 4)) = 5 * k + 18 := by
  unfold expectedRank
  rw [show 5 + 2 * (k + 4) + (2 * (k + 4) + 1) - 2 = 4 * k + 20 by omega,
    show 5 * k + 18 = (5 * k + 17) + 1 by omega]
  exact ceil_eq_of_bounds (by omega) (by nlinarith) (by nlinarith)

theorem expectedRank_add_two {m : ℕ} (hm : 7 ≤ m) :
    expectedRank (m + 2) = expectedRank m + 5 := by
  by_cases h : m % 2 = 0
  · let k := (m - 8) / 2
    have hk : m = 2 * (k + 4) := by dsimp [k]; omega
    rw [hk, show 2 * (k + 4) + 2 = 2 * ((k + 1) + 4) by omega,
      expectedRank_even, expectedRank_even]
    omega
  · let k := (m - 5) / 2
    have hk : m = 2 * (k + 2) + 1 := by dsimp [k]; omega
    rw [hk, show 2 * (k + 2) + 1 + 2 = 2 * ((k + 1) + 2) + 1 by omega,
      expectedRank_odd, expectedRank_odd]
    omega

private def Spans (m r : ℕ) : Prop :=
  ∃ x : Fin r → Fin 5 → ℂ, ∃ y : Fin r → Fin m → ℂ, ∃ z : Fin r → Fin (m + 1) → ℂ,
    ∀ T : Fin 5 → Fin m → Fin (m + 1) → ℂ, ∃ u : Fin r → Fin 5 → ℂ,
      ∃ v : Fin r → Fin m → ℂ, ∃ w : Fin r → Fin (m + 1) → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i * (y t j * z t k) + x t i * (v t j * z t k) +
          x t i * (y t j * w t k))

/-- Four finite Jacobian rank tests. -/
def H1 : Prop :=
  Spans 5 11 ∧ Spans 6 14 ∧ Spans 7 16 ∧ Spans 8 18

/-- A width-two extension of the witness with five additional points. -/
def H2 : Prop :=
  ∀ m : ℕ, 7 ≤ m → Spans m (expectedRank m) → Spans (m + 2) (expectedRank m + 5)

theorem main : H1 → H2 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2.H1 := by
  intro hseed hstep m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    change Spans m (expectedRank m)
    by_cases hsmall : m ≤ 8
    · obtain ⟨h5, h6, h7, h8⟩ := hseed
      interval_cases m
      · exact h5
      · exact h6
      · exact h7
      · exact h8
    · have hprev : 7 ≤ m - 2 := by omega
      have hEq : m - 2 + 2 = m := by omega
      have hRank : expectedRank (m - 2) + 5 = expectedRank m := by
        rw [← expectedRank_add_two hprev, hEq]
      have hw : Spans (m - 2) (expectedRank (m - 2)) :=
        ih (m - 2) (by omega) (by omega)
      have hh := hstep (m - 2) hprev hw
      rw [hEq, hRank] at hh
      exact hh

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R2_H1_R1
