import OMAStatements.S_oeis_a287469

namespace OMA.S_oeis_a287469

open PowerSeries

private def lit (n x y : ℤ) : Bool :=
  decide (|x| + |y| ≤ n ∧ (x + y - n) % 2 = 0)

private theorem lit_step (n x y : ℤ) (hn : 0 ≤ n) :
    step (lit n) x y = lit (n + 1) x y := by
  have parity : ∀ t : ℤ, |t| % 2 = t % 2 := by
    intro t
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (by omega : t < 0)]
      omega
  have px := parity x
  have py := parity y
  by_cases h : (x + y - (n + 1)) % 2 = 0
  · have hc : lit n x y = false := by simp [lit, show (x + y - n) % 2 ≠ 0 by omega]
    have hl (u v : ℤ) (hh : u + v = x + y - 1 ∨ u + v = x + y + 1) :
        lit n u v = decide (|u| + |v| ≤ n) := by
      simp [lit, show (u + v - n) % 2 = 0 by omega]
    unfold step
    rw [hc, hl (x - 1) y (Or.inl (by omega)), hl (x + 1) y (Or.inr (by omega)),
      hl x (y - 1) (Or.inl (by omega)), hl x (y + 1) (Or.inr (by omega))]
    simp only [Bool.toNat_false, zero_add, lit, h, and_true]
    have normParity : (|x| + |y| - (n + 1)) % 2 = 0 := by omega
    by_cases hin : |x| + |y| ≤ n - 1
    · have h1 : |x - 1| + |y| ≤ n := by
        have := abs_sub_abs_le_abs_sub (x - 1) x
        have ht : x - 1 - x = -1 := by ring
        rw [ht] at this
        norm_num at this
        omega
      have h2 : |x + 1| + |y| ≤ n := by
        have := abs_sub_abs_le_abs_sub (x + 1) x
        norm_num at this
        omega
      have h3 : |x| + |y - 1| ≤ n := by
        have := abs_sub_abs_le_abs_sub (y - 1) y
        have ht : y - 1 - y = -1 := by ring
        rw [ht] at this
        norm_num at this
        omega
      have h4 : |x| + |y + 1| ≤ n := by
        have := abs_sub_abs_le_abs_sub (y + 1) y
        norm_num at this
        omega
      simp [h1, h2, h3, h4, show |x| + |y| ≤ n + 1 by omega]; decide
    · by_cases hb : |x| + |y| = n + 1
      · rcases lt_trichotomy x 0 with hx | hx | hx <;>
          rcases lt_trichotomy y 0 with hy | hy | hy <;>
          simp (disch := omega) only [abs_of_nonneg, abs_of_nonpos] at * <;>
          simp (disch := omega) only [decide_eq_true, decide_eq_false] <;> decide
      · have hfar : n + 1 < |x| + |y| := by omega
        have h1 : ¬ |x - 1| + |y| ≤ n := by
          have := abs_sub_abs_le_abs_sub x (x - 1)
          norm_num at this
          omega
        have h2 : ¬ |x + 1| + |y| ≤ n := by
          have := abs_sub_abs_le_abs_sub x (x + 1)
          have ht : x - (x + 1) = -1 := by ring
          rw [ht] at this
          norm_num at this
          omega
        have h3 : ¬ |x| + |y - 1| ≤ n := by
          have := abs_sub_abs_le_abs_sub y (y - 1)
          norm_num at this
          omega
        have h4 : ¬ |x| + |y + 1| ≤ n := by
          have := abs_sub_abs_le_abs_sub y (y + 1)
          have ht : y - (y + 1) = -1 := by ring
          rw [ht] at this
          norm_num at this
          omega
        simp [h1, h2, h3, h4, show ¬ |x| + |y| ≤ n + 1 by omega]

  · have hnbr (u v : ℤ) (hh : u + v = x + y - 1 ∨ u + v = x + y + 1) :
        lit n u v = false := by simp [lit, show (u + v - n) % 2 ≠ 0 by omega]
    unfold step
    rw [hnbr (x - 1) y (Or.inl (by omega)), hnbr (x + 1) y (Or.inr (by omega)),
      hnbr x (y - 1) (Or.inl (by omega)), hnbr x (y + 1) (Or.inr (by omega))]
    rw [show lit (n + 1) x y = false by simp [lit, h]]
    cases lit n x y <;> decide

private theorem state_eq (n : ℕ) (x y : ℤ) : state n x y = lit n x y := by
  induction n generalizing x y with
  | zero =>
    simp only [state, lit, Nat.cast_zero]
    congr 1
    apply propext
    constructor
    · rintro ⟨rfl, rfl⟩
      decide
    · intro hh
      have hx := abs_nonneg x
      have hy := abs_nonneg y
      have hx' : |x| = 0 := by omega
      have hy' : |y| = 0 := by omega
      exact ⟨abs_eq_zero.mp hx', abs_eq_zero.mp hy'⟩
  | succ n ih =>
    simp only [state, Nat.cast_succ]
    have hh : state n = lit n := by funext x y; exact ih x y
    rw [hh]
    exact lit_step n x y (by positivity)


private theorem diag (n i : ℕ) :
    state n (i : ℤ) (i : ℤ) = decide (i ≤ n / 2 ∧ n % 2 = 0) := by
  rw [state_eq]
  unfold lit
  congr 1
  apply propext
  simp only [abs_of_nonneg (show 0 ≤ (i : ℤ) by positivity)]
  omega

private theorem geometric (n k : ℕ) (hk : k ≤ n + 1) :
    9 * (∑ i ∈ Finset.range k, (10 : ℤ) ^ (n - i)) =
      10 ^ (n + 1) - 10 ^ (n + 1 - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih (by omega)]
    rw [show n + 1 - k = n - k + 1 by omega,
      show n + 1 - (k + 1) = n - k by omega, pow_succ]
    ring

private theorem even_scaled (n : ℕ) (hn : n % 2 = 0) :
    9 * (a n : ℤ) = 10 ^ (n + 1) - 10 ^ (n / 2) := by
  unfold a
  push_cast
  have hs : Finset.range (n / 2 + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (Nat.succ_le_succ (Nat.div_le_self n 2))
  rw [← Finset.sum_subset hs (by
    intro i _ hi
    have h : ¬ i ≤ n / 2 := by simp only [Finset.mem_range] at hi; omega
    simp [diag, h])]
  simp only [diag, hn, and_true]
  have hf : (∑ i ∈ Finset.range (n / 2 + 1),
       (((decide (i ≤ n / 2)).toNat : ℕ) : ℤ) * 10 ^ (n - i)) =
       ∑ i ∈ Finset.range (n / 2 + 1), (10 : ℤ) ^ (n - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [show i ≤ n / 2 by omega]
  rw [hf, geometric n _ (by omega), show n + 1 - (n / 2 + 1) = n / 2 by omega]

private theorem even_value (n : ℕ) (hn : n % 2 = 0) :
    (a n : ℤ) = (10 ^ (n + 1) - 10 ^ (n / 2)) / 9 := by
  have h := even_scaled n hn
  omega

private theorem odd_value (n : ℕ) (hn : n % 2 = 1) : a n = 0 := by
  simp [a, diag, hn]

private theorem recurrence (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 110 * a (n - 2) - 1000 * a (n - 4) := by
  by_cases h : n % 2 = 0
  · have h0 := even_scaled n h
    have h2 := even_scaled (n - 2) (by omega)
    have h4 := even_scaled (n - 4) (by omega)
    rw [show n + 1 = (n - 4 + 1) + 4 by omega, show n / 2 = (n - 4) / 2 + 2 by omega,
      pow_add, pow_add] at h0
    rw [show n - 2 + 1 = (n - 4 + 1) + 2 by omega,
      show (n - 2) / 2 = (n - 4) / 2 + 1 by omega, pow_add, pow_add] at h2
    simp only [pow_succ] at h0 h2 h4
    norm_num at h0 h2 h4
    linarith only [h0, h2, h4]
  · simp [odd_value n (by omega), odd_value (n - 2) (by omega), odd_value (n - 4) (by omega)]

private theorem generating :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) = 1 := by
  let F : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  change F * _ = _
  have hmul : F * ((1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      F - C 110 * (X ^ 2 * F) + C 1000 * (X ^ 4 * F) := by
    simp only [map_ofNat]
    ring
  rw [hmul]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_one, F, coeff_mk]
  by_cases hn : 3 < n
  · simp only [if_pos (show 2 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_neg (show n ≠ 0 by omega)]
    linarith [recurrence n hn]
  · have h0 := even_scaled 0 (by decide)
    have h2 := even_scaled 2 (by decide)
    norm_num at h0 h2
    interval_cases n <;> norm_num [odd_value 1 (by decide), odd_value 3 (by decide)] <;> omega

end OMA.S_oeis_a287469

theorem OMA.solution : type_of% @OMA.S_oeis_a287469.main :=
  ⟨OMA.S_oeis_a287469.generating, OMA.S_oeis_a287469.even_value,
    OMA.S_oeis_a287469.odd_value, OMA.S_oeis_a287469.recurrence⟩

