import OMAStatements.S_oeis_a123167

-- Problem oeis-a123167: for n >= 1 the numerator of the reduced fraction 4/n - 2/n^2 is a(n), where
-- a(2j+1) = 8j + 2 and a(2j) = 4j - 1.
-- Upstream: statements/oeis-a123167.lean (declaration OMA.S_oeis_a123167.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: 4/n - 2/n^2 = (4n - 2)/n^2. For n = 2j + 1 this is (8j + 2)/(2j + 1)^2, already in lowest terms because
-- j (8j + 2) + (1 - 4j)(2j + 1) = 1. For n = 2(i + 1) it equals (4i + 3)/(2 (i + 1)^2), in lowest terms because
-- 4i + 3 is odd and (4i + 3) - 4 (i + 1) = -1.

open OMA.S_oeis_a123167

theorem OMA.solution : type_of% @OMA.S_oeis_a123167.main := by
  intro n hn
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hc' : ¬ (2 * (i + 1) % 2 = 1) := by omega
    have ha : a (2 * (i + 1)) = 4 * i + 3 := by
      unfold a
      rw [if_neg hc']
      omega
    have hx : (4 / ((2 * (i + 1) : ℕ) : ℚ) - 2 / ((2 * (i + 1) : ℕ) : ℚ) ^ 2 : ℚ)
        = ((4 * i + 3 : ℤ) : ℚ) / ((2 * (i + 1) ^ 2 : ℤ) : ℚ) := by
      push_cast
      field_simp
      ring
    have h2 : IsCoprime (4 * (i : ℤ) + 3) 2 := ⟨1, -(2 * (i : ℤ) + 1), by ring⟩
    have h3 : IsCoprime (4 * (i : ℤ) + 3) ((i : ℤ) + 1) := ⟨-1, 4, by ring⟩
    have hc : IsCoprime (4 * (i : ℤ) + 3) (2 * ((i : ℤ) + 1) ^ 2) := h2.mul_right h3.pow_right
    rw [hx, ha, Rat.num_div_eq_of_coprime (by positivity) (Int.isCoprime_iff_gcd_eq_one.mp hc)]
    omega
  · have hc' : (2 * j + 1) % 2 = 1 := by omega
    have ha : a (2 * j + 1) = 8 * j + 2 := by
      unfold a
      rw [if_pos hc']
      omega
    have hx : (4 / ((2 * j + 1 : ℕ) : ℚ) - 2 / ((2 * j + 1 : ℕ) : ℚ) ^ 2 : ℚ)
        = ((8 * j + 2 : ℤ) : ℚ) / (((2 * j + 1) ^ 2 : ℤ) : ℚ) := by
      push_cast
      field_simp
      ring
    have h1 : IsCoprime (8 * (j : ℤ) + 2) (2 * (j : ℤ) + 1) := ⟨j, 1 - 4 * (j : ℤ), by ring⟩
    have hc : IsCoprime (8 * (j : ℤ) + 2) ((2 * (j : ℤ) + 1) ^ 2) := h1.pow_right
    rw [hx, ha, Rat.num_div_eq_of_coprime (by positivity) (Int.isCoprime_iff_gcd_eq_one.mp hc)]
    omega
