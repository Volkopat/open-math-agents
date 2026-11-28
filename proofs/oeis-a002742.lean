import OMAStatements.S_oeis_a002742

/- Congruences for the logarithmic numbers, conjectured by Peter Bala in OEIS A002742.
   Proof and Lean formalization by KoaOkano with OpenAI Codex. -/

namespace A002742

open Finset PowerSeries OMA.S_oeis_a002742

private def weight (j : ℕ) : ℕ :=
  if j = 0 then 0 else if j % 2 = 1 then 2 * j.factorial else 2 * (j - 1).factorial

private def B (n : ℕ) : ℕ := ∑ j ∈ range (n + 1), n.choose j * weight j

private theorem coeffWeight (j : ℕ) :
    (j.factorial : ℚ) * coeff j G = -(-1 : ℚ) ^ j * (weight j : ℚ) := by
  cases j with
  | zero => norm_num [G, weight]
  | succ i =>
    by_cases ho : (i + 1) % 2 = 1
    · have h : Odd (i + 1) := Nat.odd_iff.mpr ho
      simp [G, weight, ho, h.neg_one_pow, mul_comm]
    · have h : Even (i + 1) := Nat.even_iff.mpr (by omega)
      have hn : (i : ℚ) + 1 ≠ 0 := by positivity
      simp [G, weight, ho, h.neg_one_pow, Nat.factorial_succ]
      field_simp

private theorem binomialFormula (n : ℕ) : a n = -(-1 : ℚ) ^ n * (B n : ℚ) := by
  rw [a, egf, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, mul_sum]
  simp only [coeff_mk, B, Nat.cast_sum, Nat.cast_mul, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simpa using mem_range.mp hj
  have fac : (n.factorial : ℚ) = (n.choose j : ℚ) * j.factorial * (n - j).factorial := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjn).symm
  have sign : (-1 : ℚ) ^ n = (-1 : ℚ) ^ j * (-1 : ℚ) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hjn]
  calc
    _ = (n.choose j : ℚ) * ((j.factorial : ℚ) * coeff j G) * (-1 : ℚ) ^ (n - j) := by
      rw [fac]
      have hn : ((n - j).factorial : ℚ) ≠ 0 := by positivity
      field_simp
    _ = _ := by rw [coeffWeight, sign]; ring

-- Every positive index i ≤ j divides the j-th binomial weight.
private theorem dividesWeight {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) : i ∣ weight j := by
  have hj : j ≠ 0 := by omega
  by_cases ho : j % 2 = 1
  · simpa [weight, hj, ho] using dvd_mul_of_dvd_right (Nat.dvd_factorial hi hij) 2
  rw [weight, if_neg hj, if_neg ho]
  by_cases heq : i = j
  · subst i
    have twice : 2 * (j / 2) = j := by omega
    obtain ⟨q, hq⟩ := Nat.dvd_factorial (show 0 < j / 2 by omega) (show j / 2 ≤ j - 1 by omega)
    exact ⟨q, by rw [hq, ← mul_assoc, twice]⟩
  · exact dvd_mul_of_dvd_right (Nat.dvd_factorial hi (by omega)) 2

private theorem weightedChoose (n m j : ℕ) :
    (n + m).choose j * weight j ≡ n.choose j * weight j [MOD m] := by
  rw [Nat.add_comm n m, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_mul]
  let f (i : ℕ) := m.choose i * n.choose (j - i) * weight j
  have onlyZero : ∀ i ∈ range (j + 1), i ≠ 0 → f i ≡ 0 [MOD m] := by
    intro i hi hpos
    apply Nat.modEq_zero_iff_dvd.mpr
    obtain ⟨q, hq⟩ := dividesWeight (Nat.pos_of_ne_zero hpos) (Nat.le_of_lt_succ (mem_range.mp hi))
    cases i with
    | zero => contradiction
    | succ t =>
      cases m with
      | zero => simp [f]
      | succ u =>
        refine ⟨u.choose t * n.choose (j - (t + 1)) * q, ?_⟩
        dsimp [f]
        rw [hq, show (u + 1).choose (t + 1) * n.choose (j - (t + 1)) * ((t + 1) * q) =
          ((u + 1).choose (t + 1) * (t + 1)) * n.choose (j - (t + 1)) * q by ring,
          ← Nat.add_one_mul_choose_eq]
        ring
  simpa [f] using Nat.sum_modEq_single (a := 0) (by simp) onlyZero

private theorem period (n m : ℕ) : B (n + m) ≡ B n [MOD m] := by
  have extend : B n = ∑ j ∈ range (n + m + 1), n.choose j * weight j := by
    apply sum_subset (range_mono (by omega : n + 1 ≤ n + m + 1))
    intro j _ hj
    have h : n < j := by simpa using hj
    rw [Nat.choose_eq_zero_of_lt h, zero_mul]
  rw [extend]
  exact Nat.ModEq.sum fun j _ => weightedChoose n m j

private theorem shifted (n m : ℕ) :
    ∃ z : ℤ, a (n + m) - (-1 : ℚ) ^ m * a n = (m : ℚ) * z := by
  obtain ⟨q, hq⟩ := (period n m).symm.dvd
  have diff : (B (n + m) : ℚ) - (B n : ℚ) = (m : ℚ) * (q : ℚ) := by exact_mod_cast hq
  refine ⟨-(-1 : ℤ) ^ (n + m) * q, ?_⟩
  simp only [binomialFormula, Int.cast_mul, Int.cast_neg, Int.cast_pow, Int.cast_one, pow_add]
  linear_combination -((-1 : ℚ) ^ n * (-1 : ℚ) ^ m) * diff

end A002742

theorem OMA.solution : type_of% @OMA.S_oeis_a002742.main := by
  constructor
  · intro k n _ _
    simpa [pow_mul] using A002742.shifted n (2 * k)
  · intro k n _ _
    simpa [pow_add, pow_mul, Nat.add_assoc] using A002742.shifted n (2 * k + 1)
