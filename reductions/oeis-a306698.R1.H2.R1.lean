import OMAReductions.R_oeis_a306698_R1

-- Reduction oeis-a306698.R1.H2.R1 of the coverage half of the Recaman-like range conjecture.
-- Credit: @Ciphore
-- The two residue classes have different production mechanisms in the sequence, so the
-- coverage claim is split into the multiples of three and the numbers one above a multiple of three.

namespace OMA.R_oeis_a306698_R1_H2_R1

open OMA.S_oeis_a306698

/-- Every nonnegative multiple of three occurs in the sequence. -/
def H1 : Prop := ∀ k : ℕ, 3 * k ∈ Set.range sequence

/-- Every nonnegative integer congruent to one modulo three occurs in the sequence. -/
def H2 : Prop := ∀ k : ℕ, 3 * k + 1 ∈ Set.range sequence

theorem main : H1 → H2 → OMA.R_oeis_a306698_R1.H2 := by
  intro h0 h1 m hm
  rcases hm with hm0 | hm1
  · have hdvd : 3 ∣ m := Nat.dvd_of_mod_eq_zero hm0
    rcases hdvd with ⟨k, rfl⟩
    exact h0 k
  · have hk : m = 3 * (m / 3) + 1 := by omega
    rw [hk]
    exact h1 (m / 3)

end OMA.R_oeis_a306698_R1_H2_R1
