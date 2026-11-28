import OMAStatements.S_oeis_a351858

-- Problem: OEIS A351858, Bala's conjecture a(n) = Sum_{k=0..floor(n/2)} C(3n,k) C(n-k,k)
-- Statement: statements/oeis-a351858.lean (declaration OMA.S_oeis_a351858.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Write 1 + x + x^2 = x^2 + (1 + x). The binomial theorem gives
--     (1 + x + x^2)^(3n) = Sum_k C(3n,k) x^(2k) (1 + x)^(3n-k).
-- After division by (1 + x)^(2n), the term k is C(3n,k) x^(2k) (1 + x)^(n-k) when k <= n, and
-- each term with 2k > n has no coefficient of x^n. For 2k <= n the coefficient of x^n is
-- C(3n,k) C(n-k, n-2k) = C(3n,k) C(n-k,k).

namespace OMA.A351858

open PowerSeries

lemma coeff_one_add_X_pow (d k : ℕ) :
    coeff k (((1 : ℚ⟦X⟧) + X) ^ d) = (d.choose k : ℚ) := by
  have h : ((1 : ℚ⟦X⟧) + X) ^ d
      = (((1 : Polynomial ℚ) + Polynomial.X) ^ d).toPowerSeries := by
    simp
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

lemma unit_cancel (m : ℕ) :
    ((1 : ℚ⟦X⟧) + X) ^ m * (((1 : ℚ⟦X⟧) + X) ^ m)⁻¹ = 1 := by
  apply PowerSeries.mul_inv_cancel
  simp

theorem formula (n : ℕ) :
    OMA.S_oeis_a351858.a n
      = ∑ k ∈ Finset.range (n / 2 + 1), ((3 * n).choose k : ℚ) * ((n - k).choose k : ℚ) := by
  unfold OMA.S_oeis_a351858.a
  have hsplit : ((1 : ℚ⟦X⟧) + X + X ^ 2) ^ (3 * n)
      = ∑ k ∈ Finset.range (3 * n + 1),
          (X ^ 2) ^ k * ((1 : ℚ⟦X⟧) + X) ^ (3 * n - k) * ((3 * n).choose k : ℚ⟦X⟧) := by
    rw [show ((1 : ℚ⟦X⟧) + X + X ^ 2) = X ^ 2 + (1 + X) by ring, add_pow]
  rw [hsplit, Finset.sum_mul, map_sum]
  have hterm : ∀ k ∈ Finset.range (3 * n + 1),
      coeff n ((X ^ 2) ^ k * ((1 : ℚ⟦X⟧) + X) ^ (3 * n - k) * ((3 * n).choose k : ℚ⟦X⟧)
          * (((1 : ℚ⟦X⟧) + X) ^ (2 * n))⁻¹)
        = if k ∈ Finset.range (n / 2 + 1)
            then ((3 * n).choose k : ℚ) * ((n - k).choose k : ℚ) else 0 := by
    intro k hk
    have hre : (X ^ 2) ^ k * ((1 : ℚ⟦X⟧) + X) ^ (3 * n - k) * ((3 * n).choose k : ℚ⟦X⟧)
          * (((1 : ℚ⟦X⟧) + X) ^ (2 * n))⁻¹
        = X ^ (2 * k) * (((3 * n).choose k : ℚ⟦X⟧) * (((1 : ℚ⟦X⟧) + X) ^ (3 * n - k)
            * (((1 : ℚ⟦X⟧) + X) ^ (2 * n))⁻¹)) := by
      rw [← pow_mul]
      ring
    rw [hre, coeff_X_pow_mul']
    by_cases h2 : 2 * k ≤ n
    · have hmem : k ∈ Finset.range (n / 2 + 1) := by
        rw [Finset.mem_range]
        omega
      rw [if_pos h2, if_pos hmem]
      have hpow : ((1 : ℚ⟦X⟧) + X) ^ (3 * n - k) * (((1 : ℚ⟦X⟧) + X) ^ (2 * n))⁻¹
          = ((1 : ℚ⟦X⟧) + X) ^ (n - k) := by
        have : 3 * n - k = (n - k) + 2 * n := by omega
        rw [this, pow_add, mul_assoc, unit_cancel, mul_one]
      rw [hpow, ← map_natCast (C (R := ℚ)), coeff_C_mul, coeff_one_add_X_pow]
      congr 1
      have : n - 2 * k = (n - k) - k := by omega
      rw [this, Nat.choose_symm (by omega)]
    · have hmem : k ∉ Finset.range (n / 2 + 1) := by
        rw [Finset.mem_range]
        omega
      rw [if_neg h2, if_neg hmem]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem]
  congr 1
  ext k
  simp only [Finset.mem_inter, Finset.mem_range]
  omega

end OMA.A351858

theorem OMA.solution : type_of% @OMA.S_oeis_a351858.main :=
  OMA.A351858.formula
