import OMAReductions.R_oeis_a386703_R1_H3_R1

/-!
# Distinct partitions modulo eight and the positive-one residue

Source: https://oeis.org/A386703
Credit: @Dolcruz

At indices where four divides the strict partition count, a counterexample
would either descend to divisibility after division by eight or give an
integral representation of the discriminant by one of two quadratic forms.
-/

namespace OMA.R_oeis_a386703_R1_H3_R1_H2_R1

open OMA.S_oeis_a386703

/-- The support of the strict partition series modulo eight. -/
def H1 : Prop :=
  ∀ n : ℕ, (¬ ∃ u v : ℕ, 24*n+1 = u^2 + 24*v^2) →
    (¬ ∃ u v : ℕ, 24*n+1 = u^2 + 48*v^2) → 8 ∣ q n

/-- With eight dividing the modulus, only the one class for p modulo eight remains. -/
def H2 : Prop :=
  ∀ n : ℕ, 4096 < n → ¬ IsSquare (24*n+1) → p n % 8 = 1 → 8 ∣ q n →
    ¬ (q n / 8) ∣ ((p n - 1) / 8)

/-- At residue four the discriminant must be represented, with positive second coordinate. -/
def H3 : Prop :=
  ∀ n : ℕ, 4096 < n → ¬ IsSquare (24*n+1) → p n % 4 = 1 → q n % 8 = 4 →
    (∃ u v : ℕ, 0 < v ∧ (24*n+1 = u^2 + 24*v^2 ∨ 24*n+1 = u^2 + 48*v^2)) →
    ¬ (q n / 4) ∣ ((p n - 1) / 4)

theorem main : H1 → H2 → H3 → OMA.R_oeis_a386703_R1_H3_R1.H2 := by
  intro support eight four n hn nonsquare hp hq dvd
  have full : q n ∣ p n - 1 := by
    obtain ⟨k, hk⟩ := dvd
    exact ⟨k, by
      calc p n - 1 = 4 * ((p n - 1) / 4) := by omega
           _ = 4 * (q n / 4) * k := by rw [hk]; ring
           _ = q n * k := by rw [Nat.mul_div_cancel' hq]⟩
  by_cases h8 : 8 ∣ q n
  · have div8 := dvd_trans h8 full
    exact eight n hn nonsquare (by omega) h8
      (OMA.R_oeis_a386703_R1_H3_R1.divide_obstruction (by decide) h8 full)
  · apply four n hn nonsquare hp (by omega) _ dvd
    have repr : (∃ u v : ℕ, 24*n+1 = u^2 + 24*v^2) ∨
        (∃ u v : ℕ, 24*n+1 = u^2 + 48*v^2) := by
      by_contra absent
      exact h8 (support n (fun e => absent (Or.inl e)) (fun e => absent (Or.inr e)))
    rcases repr with ⟨u, v, e⟩ | ⟨u, v, e⟩
    all_goals
      have hv : v ≠ 0 := by
        rintro rfl
        exact nonsquare ⟨u, by simpa [pow_two] using e⟩
    · exact ⟨u, v, Nat.pos_of_ne_zero hv, Or.inl e⟩
    · exact ⟨u, v, Nat.pos_of_ne_zero hv, Or.inr e⟩

end OMA.R_oeis_a386703_R1_H3_R1_H2_R1
