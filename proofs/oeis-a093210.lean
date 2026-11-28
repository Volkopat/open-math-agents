import OMAStatements.S_oeis_a093210

-- Problem: A093210: Row sums of A092964.
-- Upstream: formal-conjectures statements/oeis-a093210.lean:0 (declaration OMA.S_oeis_a093210.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let m = n + 4 and S(m, j) = m * A051168(m, j). Summing S(m, j) over j = 0..m and
-- swapping the two sums (d runs over the divisors of m, j over the multiples d*i, i = 0..m/d)
-- gives Sum_{d | m} mu(d) * 2^(m/d). The terms j = 0 and j = m are Sum_{d | m} mu(d) = 0 (m > 1),
-- the terms j = 1 and j = m - 1 are m (gcd 1), and row n of A092964 is j = 2..m-2. So
-- m * a(n) = Sum_{d | m} mu(d) 2^(m/d) - 2m = m * (A060477(m) - 2).

namespace R09A093210

open OMA.S_oeis_a093210

/-- m times A051168(m, j). -/
def S (m j : ℕ) : ℚ :=
  ∑ d ∈ (Nat.gcd m j).divisors,
    (ArithmeticFunction.moebius d : ℚ) * ((Nat.choose (m / d) (j / d) : ℕ) : ℚ)

theorem moeb_sum (m : ℕ) (hm : m ≠ 1) :
    ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℚ) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply_ne hm] at h
  exact_mod_cast h

theorem S_zero (m : ℕ) : S m 0 = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℚ) := by
  simp only [S, Nat.gcd_zero_right, Nat.zero_div, Nat.choose_zero_right, Nat.cast_one, mul_one]

theorem S_self (m : ℕ) : S m m = ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℚ) := by
  simp only [S, Nat.gcd_self, Nat.choose_self, Nat.cast_one, mul_one]

theorem S_one (m : ℕ) : S m 1 = (m : ℚ) := by
  simp only [S, Nat.gcd_one_right, Nat.divisors_one, Finset.sum_singleton,
    ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, Nat.div_one, Nat.choose_one_right]

theorem S_pred (N : ℕ) : S (N + 4) (N + 3) = ((N + 4 : ℕ) : ℚ) := by
  have hg : Nat.gcd (N + 4) (N + 3) = 1 := by
    have h1 : Nat.gcd (N + 4) (N + 3) ∣ N + 4 := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd (N + 4) (N + 3) ∣ N + 3 := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd (N + 4) (N + 3) ∣ N + 4 - (N + 3) := Nat.dvd_sub h1 h2
    have h4 : N + 4 - (N + 3) = 1 := by omega
    rw [h4] at h3
    exact Nat.dvd_one.mp h3
  have hc : (N + 4).choose (N + 3) = N + 4 := Nat.choose_succ_self_right (N + 3)
  simp only [S, hg, Nat.divisors_one, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one,
    Int.cast_one, one_mul, Nat.div_one, hc]

theorem sum_total (m : ℕ) (hm : 0 < m) :
    ∑ j ∈ Finset.range (m + 1), S m j =
      ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℚ) * (2 : ℚ) ^ (m / d) := by
  have hcomm : ∀ j d, (j ∈ Finset.range (m + 1) ∧ d ∈ (Nat.gcd m j).divisors) ↔
      (j ∈ (Finset.range (m / d + 1)).image (fun i => d * i) ∧ d ∈ m.divisors) := by
    intro j d
    simp only [Finset.mem_range, Nat.mem_divisors, Finset.mem_image, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨hj, ⟨hdm, hdj⟩, _⟩
      exact ⟨⟨j / d, Nat.lt_add_one_of_le (Nat.div_le_div_right (Nat.lt_add_one_iff.mp hj)),
        Nat.mul_div_cancel' hdj⟩, hdm, by omega⟩
    · rintro ⟨⟨i, hi, rfl⟩, hdm, _⟩
      refine ⟨Nat.lt_add_one_of_le (le_trans (Nat.mul_le_mul_left d (Nat.lt_add_one_iff.mp hi))
        (Nat.mul_div_le m d)), ⟨hdm, Nat.dvd_mul_right d i⟩, ?_⟩
      have hpos := Nat.gcd_pos_of_pos_left (d * i) hm
      omega
  unfold S
  rw [Finset.sum_comm' hcomm]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [Finset.sum_image]
  · simp_rw [Nat.mul_div_cancel_left _ hd0]
    rw [← Finset.mul_sum]
    congr 1
    exact_mod_cast Nat.sum_range_choose (m / d)
  · intro x _ y _ hxy
    exact Nat.eq_of_mul_eq_mul_left hd0 hxy

theorem sum_split5 (f : ℕ → ℚ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 5), f j =
      f 0 + f 1 + ∑ k ∈ Finset.range (n + 1), f (k + 2) + f (n + 3) + f (n + 4) := by
  have e1 : ∑ j ∈ Finset.range (n + 5), f j = ∑ j ∈ Finset.range (n + 4), f j + f (n + 4) :=
    Finset.sum_range_succ f (n + 4)
  have e2 : ∑ j ∈ Finset.range (n + 4), f j = ∑ j ∈ Finset.range (n + 3), f j + f (n + 3) :=
    Finset.sum_range_succ f (n + 3)
  have e3 : ∑ j ∈ Finset.range (n + 3), f j = ∑ j ∈ Finset.range (n + 2), f (j + 1) + f 0 :=
    Finset.sum_range_succ' f (n + 2)
  have e4 : ∑ j ∈ Finset.range (n + 2), f (j + 1) =
      ∑ k ∈ Finset.range (n + 1), f (k + 2) + f 1 :=
    Finset.sum_range_succ' (fun j => f (j + 1)) (n + 1)
  linear_combination e1 + e2 + e3 + e4

theorem main_eq (n : ℕ) : a n = A060477 (n + 4) - 2 := by
  have hm : 0 < n + 4 := by omega
  have htot : ∑ j ∈ Finset.range (n + 5), S (n + 4) j =
      ∑ d ∈ (n + 4).divisors, (ArithmeticFunction.moebius d : ℚ) * (2 : ℚ) ^ ((n + 4) / d) :=
    sum_total (n + 4) hm
  rw [sum_split5 (S (n + 4)) n, S_zero, S_one, S_pred, S_self,
    moeb_sum (n + 4) (by omega)] at htot
  have ha : a n = (∑ k ∈ Finset.range (n + 1), S (n + 4) (k + 2)) / ((n + 4 : ℕ) : ℚ) := by
    rw [Finset.sum_div]
    rfl
  have e : ∑ d ∈ (n + 4).divisors,
      (ArithmeticFunction.moebius d : ℚ) * ((2 : ℚ) ^ ((n + 4) / d) + 1) =
      ∑ d ∈ (n + 4).divisors, (ArithmeticFunction.moebius d : ℚ) * (2 : ℚ) ^ ((n + 4) / d) +
        ∑ d ∈ (n + 4).divisors, (ArithmeticFunction.moebius d : ℚ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hA : A060477 (n + 4) =
      (∑ d ∈ (n + 4).divisors, (ArithmeticFunction.moebius d : ℚ) * (2 : ℚ) ^ ((n + 4) / d) +
        ∑ d ∈ (n + 4).divisors, (ArithmeticFunction.moebius d : ℚ)) / ((n + 4 : ℕ) : ℚ) := by
    rw [A060477, e]
  rw [ha, hA, moeb_sum (n + 4) (by omega)]
  have hm0 : ((n + 4 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hinv : ((n + 4 : ℕ) : ℚ) * ((n + 4 : ℕ) : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hm0
  linear_combination ((n + 4 : ℕ) : ℚ)⁻¹ * htot + (-2 : ℚ) * hinv

end R09A093210

open OMA.S_oeis_a093210 R09A093210 in
theorem OMA.solution : type_of% @OMA.S_oeis_a093210.main := by
  intro n
  exact main_eq n
