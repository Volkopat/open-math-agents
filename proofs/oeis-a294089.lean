import OMAStatements.S_oeis_a294089

namespace OMA.S_oeis_a294089

open Real
open scoped Nat






open Classical in

/-- The conjecture of the first %C line, as worded: for each n = 1, 2, 3, ... the number
`s(n) * sqrt(5) / Pi^(2n)` is rational; moreover, `a(n)` is a nonzero integer for every positive
integer `n`. -/
def Conjecture : Prop :=
  (∀ n : ℕ, 0 < n → ∃ q : ℚ, s n * Real.sqrt 5 / π ^ (2 * n) = q) ∧
  (∀ n : ℕ, 0 < n → a n ≠ 0)

/-! ### The Legendre symbol through cosines -/

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma cos_two_pi_div_five : Real.cos (2 * (π / 5)) = (Real.sqrt 5 - 1) / 4 := by
  rw [Real.cos_two_mul, Real.cos_pi_div_five]
  linear_combination (1 / 8 : ℝ) * sqrt5_sq

lemma chi_mod (k : ℕ) : chi k = chi (k % 5) := by
  unfold chi
  congr 1
  rw [Int.natCast_mod]
  exact legendreSym.mod 5 (k : ℤ)

lemma chi_zero : chi 0 = 0 := by norm_num [chi]
lemma chi_one : chi 1 = 1 := by norm_num [chi]
lemma chi_two : chi 2 = -1 := by norm_num [chi]
lemma chi_three : chi 3 = -1 := by norm_num [chi]
lemma chi_four : chi 4 = 1 := by norm_num [chi]

lemma cos_diff_small (r : ℕ) (hr : r < 5) :
    Real.cos (2 * π * r * (1 / 5)) - Real.cos (2 * π * r * (2 / 5)) = Real.sqrt 5 / 2 * chi r := by
  have c1 := Real.cos_pi_div_five
  have c2 := cos_two_pi_div_five
  obtain rfl | rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  · rw [chi_zero]; simp
  · rw [show 2 * π * ((1 : ℕ) : ℝ) * (1 / 5) = 2 * (π / 5) by push_cast; ring,
      show 2 * π * ((1 : ℕ) : ℝ) * (2 / 5) = π - π / 5 by push_cast; ring,
      Real.cos_pi_sub, c1, c2, chi_one]
    ring
  · rw [show 2 * π * ((2 : ℕ) : ℝ) * (1 / 5) = π - π / 5 by push_cast; ring,
      show 2 * π * ((2 : ℕ) : ℝ) * (2 / 5) = 2 * π - 2 * (π / 5) by push_cast; ring,
      Real.cos_pi_sub, Real.cos_two_pi_sub, c1, c2, chi_two]
    ring
  · rw [show 2 * π * ((3 : ℕ) : ℝ) * (1 / 5) = π / 5 + π by push_cast; ring,
      show 2 * π * ((3 : ℕ) : ℝ) * (2 / 5) = 2 * (π / 5) + 2 * π by push_cast; ring,
      Real.cos_add_pi, Real.cos_add_two_pi, c1, c2, chi_three]
    ring
  · rw [show 2 * π * ((4 : ℕ) : ℝ) * (1 / 5) = 2 * π - 2 * (π / 5) by push_cast; ring,
      show 2 * π * ((4 : ℕ) : ℝ) * (2 / 5) = (π / 5 + π) + 2 * π by push_cast; ring,
      Real.cos_two_pi_sub, Real.cos_add_two_pi, Real.cos_add_pi, c1, c2, chi_four]
    ring

lemma cos_diff (k : ℕ) :
    Real.cos (2 * π * k * (1 / 5)) - Real.cos (2 * π * k * (2 / 5)) = Real.sqrt 5 / 2 * chi k := by
  have hk : (k : ℝ) = 5 * ((k / 5 : ℕ) : ℝ) + ((k % 5 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod k 5).symm
  have e1 : 2 * π * (k : ℝ) * (1 / 5) =
      2 * π * ((k % 5 : ℕ) : ℝ) * (1 / 5) + ((k / 5 : ℕ) : ℝ) * (2 * π) := by
    rw [hk]; ring
  have e2 : 2 * π * (k : ℝ) * (2 / 5) =
      2 * π * ((k % 5 : ℕ) : ℝ) * (2 / 5) + ((2 * (k / 5) : ℕ) : ℝ) * (2 * π) := by
    rw [hk]; push_cast; ring
  rw [e1, e2, Real.cos_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi, chi_mod k]
  exact cos_diff_small _ (Nat.mod_lt _ (by norm_num))

/-! ### The series `s n` and the Bernoulli polynomials -/

/-- `B_2n(1/5) - B_2n(2/5)`, a rational number. -/
noncomputable def D (n : ℕ) : ℚ :=
  (Polynomial.bernoulli (2 * n)).eval (1 / 5) - (Polynomial.bernoulli (2 * n)).eval (2 / 5)

lemma eval_cast (p : Polynomial ℚ) (q : ℚ) :
    (Polynomial.map (algebraMap ℚ ℝ) p).eval (q : ℝ) = ((p.eval q : ℚ) : ℝ) := by
  rw [Polynomial.eval_map, ← eq_ratCast (algebraMap ℚ ℝ) q, Polynomial.eval₂_at_apply, eq_ratCast]

lemma D_cast (n : ℕ) :
    (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n))).eval (1 / 5) -
      (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * n))).eval (2 / 5) =
      (D n : ℝ) := by
  have h1 : (1 / 5 : ℝ) = ((1 / 5 : ℚ) : ℝ) := by push_cast; ring
  have h2 : (2 / 5 : ℝ) = ((2 / 5 : ℚ) : ℝ) := by push_cast; ring
  rw [h1, h2, eval_cast, eval_cast, D, Rat.cast_sub]

lemma hasSum_chi (n : ℕ) (hn : n ≠ 0) :
    HasSum (fun k : ℕ => chi k / (k : ℝ) ^ (2 * n))
      (2 / Real.sqrt 5 * ((-1 : ℝ) ^ (n + 1) * (2 * π) ^ (2 * n) / 2 / (2 * n)! * (D n : ℝ))) := by
  have h1 := hasSum_one_div_nat_pow_mul_cos hn (x := 1 / 5) ⟨by norm_num, by norm_num⟩
  have h2 := hasSum_one_div_nat_pow_mul_cos hn (x := 2 / 5) ⟨by norm_num, by norm_num⟩
  have h3 := (h1.sub h2).mul_left (2 / Real.sqrt 5)
  have hs1 : 2 / Real.sqrt 5 * (Real.sqrt 5 / 2) = 1 := by
    have hs : Real.sqrt 5 ≠ 0 := by positivity
    field_simp
  have hf : (fun k : ℕ => chi k / (k : ℝ) ^ (2 * n)) = fun i : ℕ =>
      2 / Real.sqrt 5 * (1 / (i : ℝ) ^ (2 * n) * Real.cos (2 * π * i * (1 / 5)) -
        1 / (i : ℝ) ^ (2 * n) * Real.cos (2 * π * i * (2 / 5))) := by
    funext k
    rw [← mul_sub, cos_diff k]
    calc chi k / (k : ℝ) ^ (2 * n)
        = (2 / Real.sqrt 5 * (Real.sqrt 5 / 2)) * (chi k * (1 / (k : ℝ) ^ (2 * n))) := by
          rw [hs1]; ring
      _ = _ := by ring
  rw [hf, ← D_cast, mul_sub]
  exact h3

lemma s_eq (n : ℕ) (hn : n ≠ 0) :
    s n = 2 / Real.sqrt 5 * ((-1 : ℝ) ^ (n + 1) * (2 * π) ^ (2 * n) / 2 / (2 * n)! * (D n : ℝ)) := by
  have h := hasSum_chi n hn
  rw [← hasSum_nat_add_iff' 1] at h
  have h0 : (∑ i ∈ Finset.range 1, chi i / (i : ℝ) ^ (2 * n)) = 0 := by simp [chi_zero]
  rw [h0, sub_zero] at h
  exact h.tsum_eq

/-- The first half of the conjecture holds for every `n ≥ 1`. -/
theorem rational_part (n : ℕ) (hn : 0 < n) :
    ∃ q : ℚ, s n * Real.sqrt 5 / π ^ (2 * n) = q := by
  refine ⟨(-1) ^ (n + 1) * 2 ^ (2 * n) / (2 * n)! * D n, ?_⟩
  rw [s_eq n hn.ne']
  have hs : Real.sqrt 5 ≠ 0 := by positivity
  have hp : π ≠ 0 := Real.pi_ne_zero
  push_cast
  rw [mul_pow]
  field_simp

/-! ### The closed form of `b n` -/

lemma e_odd (n : ℕ) (hn : n ≠ 0) : e n = 2 * ((e n - 1) / 2) + 1 := by
  unfold e
  have h1 : (n + 11) / 2 = (n + 1) / 2 + 5 := by omega
  rw [h1]
  have hm1 : 1 ≤ (n + 1) / 2 := by omega
  generalize (n + 1) / 2 = m at hm1 ⊢
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
  have h2 : m * (m + 5) = t + t + 4 * m := by
    rw [show m * (m + 5) = m * (m + 1) + 4 * m by ring, ht]
  rw [h2]
  omega

lemma zeta_eq (n : ℕ) (hn : n ≠ 0) :
    riemannZeta (2 * n) = (((-1 : ℝ) ^ (n + 1) * 2 ^ (2 * n - 1) * π ^ (2 * n) *
      (bernoulli (2 * n) : ℝ) / (2 * n)! : ℝ) : ℂ) := by
  rw [riemannZeta_two_mul_nat hn]
  push_cast
  ring

/-- For every `n ≥ 1`, `b n = 2 * 5^((e n - 1)/2) * (B_2n(1/5) - B_2n(2/5)) / (24 * B_2n)`. -/
theorem b_eq (n : ℕ) (hn : n ≠ 0) :
    b n = ((2 * 5 ^ ((e n - 1) / 2) * D n / (24 * bernoulli (2 * n)) : ℚ) : ℂ) := by
  have he := e_odd n hn
  generalize (e n - 1) / 2 = j at he ⊢
  have hreal : s n * Real.sqrt 5 ^ e n / (24 * ((-1 : ℝ) ^ (n + 1) * 2 ^ (2 * n - 1) *
      π ^ (2 * n) * (bernoulli (2 * n) : ℝ) / (2 * n)!)) =
      2 * 5 ^ j * (D n : ℝ) / (24 * (bernoulli (2 * n) : ℝ)) := by
    have hw : Real.sqrt 5 ^ (2 * j + 1) = 5 ^ j * Real.sqrt 5 := by
      rw [pow_succ, pow_mul, sqrt5_sq]
    have h2 : (2 : ℝ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [s_eq n hn, he, hw, mul_pow (2 : ℝ) π (2 * n), h2]
    have hs : Real.sqrt 5 ≠ 0 := by positivity
    have hp : π ≠ 0 := Real.pi_ne_zero
    have hm : (-1 : ℝ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hf : ((2 * n)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rcases eq_or_ne (bernoulli (2 * n)) 0 with hB | hB
    · simp [hB]
    have hB' : ((bernoulli (2 * n) : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hB
    field_simp
  have hq : ((2 * 5 ^ j * D n / (24 * bernoulli (2 * n)) : ℚ) : ℂ) =
      ((2 * 5 ^ j * (D n : ℝ) / (24 * (bernoulli (2 * n) : ℝ)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hq, ← hreal]
  unfold b
  rw [zeta_eq n hn]
  push_cast
  ring

/-! ### Bernoulli numbers and the values of `D` -/

lemma B0 : bernoulli 0 = 1 := bernoulli_zero
lemma B1 : bernoulli 1 = -1 / 2 := bernoulli_one
lemma B2 : bernoulli 2 = 1 / 6 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_two]
lemma B3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
lemma B4 : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
lemma B5 : bernoulli 5 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
lemma B7 : bernoulli 7 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
lemma B9 : bernoulli 9 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
lemma B11 : bernoulli 11 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)

lemma B6 : bernoulli 6 = 1 / 42 := by
  have h := sum_bernoulli 7
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [B0, B1, B2, B3, B4, B5] at h
  norm_num [Nat.choose_eq_factorial_div_factorial] at h
  linarith

lemma B8 : bernoulli 8 = -1 / 30 := by
  have h := sum_bernoulli 9
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [B0, B1, B2, B3, B4, B5, B6, B7] at h
  norm_num [Nat.choose_eq_factorial_div_factorial] at h
  linarith

lemma B10 : bernoulli 10 = 5 / 66 := by
  have h := sum_bernoulli 11
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9] at h
  norm_num [Nat.choose_eq_factorial_div_factorial] at h
  linarith

lemma B12 : bernoulli 12 = -691 / 2730 := by
  have h := sum_bernoulli 13
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11] at h
  norm_num [Nat.choose_eq_factorial_div_factorial] at h
  linarith

lemma P_eval (m : ℕ) (x : ℚ) :
    (Polynomial.bernoulli m).eval x =
      ∑ i ∈ Finset.range (m + 1), bernoulli i * (m.choose i : ℚ) * x ^ (m - i) := by
  simp [Polynomial.bernoulli, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

lemma D1 : D 1 = 2 / 25 := by
  rw [D, P_eval, P_eval]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [B0, B1, B2]

lemma D2 : D 2 = -4 / 125 := by
  rw [D, P_eval, P_eval]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [B0, B1, B2, B3, B4, Nat.choose_eq_factorial_div_factorial]

lemma D3 : D 3 = 402 / 15625 := by
  rw [D, P_eval, P_eval]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [B0, B1, B2, B3, B4, B5, B6, Nat.choose_eq_factorial_div_factorial]

lemma D4 : D 4 = -2888 / 78125 := by
  rw [D, P_eval, P_eval]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, Nat.choose_eq_factorial_div_factorial]

lemma D5 : D 5 = 825502 / 9765625 := by
  rw [D, P_eval, P_eval]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, Nat.choose_eq_factorial_div_factorial]

lemma D6 : D 6 = -13811052 / 48828125 := by
  rw [D, P_eval, P_eval]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [B0, B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12,
    Nat.choose_eq_factorial_div_factorial]

/-! ### The values -/

lemma b_val {n : ℕ} (hn : n ≠ 0) {q : ℚ}
    (h : 2 * 5 ^ ((e n - 1) / 2) * D n / (24 * bernoulli (2 * n)) = q) : b n = (q : ℂ) := by
  rw [b_eq n hn, h]

lemma b1 : b 1 = ((1 : ℚ) : ℂ) := b_val (by norm_num) (by norm_num [e, D1, B2])
lemma b2 : b 2 = ((2 : ℚ) : ℂ) := b_val (by norm_num) (by norm_num [e, D2, B4])
lemma b3 : b 3 = ((1407 : ℚ) : ℂ) := b_val (by norm_num) (by norm_num [e, D3, B6])
lemma b4 : b 4 = ((1444 : ℚ) : ℂ) := b_val (by norm_num) (by norm_num [e, D4, B8])
lemma b5 : b 5 = ((4540261 : ℚ) : ℂ) := b_val (by norm_num) (by norm_num [e, D5, B10])
lemma b6 : b 6 = ((3142014330 / 691 : ℚ) : ℂ) := b_val (by norm_num) (by norm_num [e, D6, B12])

lemma a_of_eq_int {n : ℕ} {z : ℤ} (h : b n = ((z : ℚ) : ℂ)) : a n = z := by
  have h' : b n = (z : ℂ) := by rw [h, Rat.cast_intCast]
  have hex : ∃ m : ℤ, b n = m := ⟨z, h'⟩
  unfold a
  rw [dif_pos hex]
  have hc : (hex.choose : ℂ) = z := by rw [← hex.choose_spec, h']
  exact_mod_cast hc

lemma b6_not_int : ¬ ∃ m : ℤ, b 6 = m := by
  rintro ⟨m, hm⟩
  rw [b6, ← Rat.cast_intCast (α := ℂ)] at hm
  have h2 : (3142014330 / 691 : ℚ) = m := Rat.cast_injective hm
  have h3 : (3142014330 : ℚ) = 691 * m := by rw [← h2]; norm_num
  have h4 : (3142014330 : ℤ) = 691 * m := by exact_mod_cast h3
  omega

theorem a6 : a 6 = 0 := by
  unfold a
  rw [dif_neg b6_not_int]

theorem not_conjecture : ¬ Conjecture := fun h => h.2 6 (by norm_num) a6

lemma s_val {n : ℕ} (hn : n ≠ 0) {c : ℝ}
    (h : (-1 : ℝ) ^ (n + 1) * 2 ^ (2 * n) / (2 * n)! * (D n : ℝ) = c) :
    s n = c * π ^ (2 * n) / Real.sqrt 5 := by
  rw [s_eq n hn, ← h, mul_pow]
  have hs : Real.sqrt 5 ≠ 0 := by positivity
  field_simp

/-- Summary: the first half of the conjecture holds for all `n ≥ 1`; `b 6 = 3142014330/691`, so
`a 6 = 0` and the conjecture is false; the five listed terms and the five values of `s` quoted in
the entry follow from the definitions. -/
theorem summary :
    (∀ n : ℕ, 0 < n → ∃ q : ℚ, s n * Real.sqrt 5 / π ^ (2 * n) = q) ∧
    b 6 = ((3142014330 / 691 : ℚ) : ℂ) ∧ a 6 = 0 ∧ ¬ Conjecture ∧
    (a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 1407 ∧ a 4 = 1444 ∧ a 5 = 4540261) ∧
    (s 1 = 4 * π ^ 2 / (25 * Real.sqrt 5) ∧ s 2 = 8 * π ^ 4 / (375 * Real.sqrt 5) ∧
      s 3 = 536 * π ^ 6 / (234375 * Real.sqrt 5) ∧
      s 4 = 5776 * π ^ 8 / (24609375 * Real.sqrt 5) ∧
      s 5 = 3302008 * π ^ 10 / (138427734375 * Real.sqrt 5)) := by
  refine ⟨rational_part, b6, a6, not_conjecture,
    ⟨by exact_mod_cast a_of_eq_int (z := 1) (by exact_mod_cast b1),
     by exact_mod_cast a_of_eq_int (z := 2) (by exact_mod_cast b2),
     by exact_mod_cast a_of_eq_int (z := 1407) (by exact_mod_cast b3),
     by exact_mod_cast a_of_eq_int (z := 1444) (by exact_mod_cast b4),
     by exact_mod_cast a_of_eq_int (z := 4540261) (by exact_mod_cast b5)⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s_val (by norm_num) (by norm_num [D1] : _ = (4 / 25 : ℝ))]; ring
  · rw [s_val (by norm_num) (by norm_num [D2] : _ = (8 / 375 : ℝ))]; ring
  · rw [s_val (by norm_num) (by norm_num [D3] : _ = (536 / 234375 : ℝ))]; ring
  · rw [s_val (by norm_num) (by norm_num [D4] : _ = (5776 / 24609375 : ℝ))]; ring
  · rw [s_val (by norm_num) (by norm_num [D5] : _ = (3302008 / 138427734375 : ℝ))]; ring

end OMA.S_oeis_a294089

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a294089.main) :=
  OMA.S_oeis_a294089.not_conjecture
