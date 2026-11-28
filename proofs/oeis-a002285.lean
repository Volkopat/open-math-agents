import OMAStatements.S_oeis_a002285
import Mathlib

namespace OMA.A002285

open Finset

/-- `q` is `p`-integral: it can be written `a / b` with `p ∤ b`. -/
def PInt (p : ℕ) (q : ℚ) : Prop := ∃ a : ℤ, ∃ b : ℕ, ¬ p ∣ b ∧ q = a / b

lemma pint_add {p : ℕ} (hp : p.Prime) {q r : ℚ} (hq : PInt p q) (hr : PInt p r) :
    PInt p (q + r) := by
  obtain ⟨a, b, hb, rfl⟩ := hq
  obtain ⟨c, d, hd, rfl⟩ := hr
  have hb0 : (b : ℚ) ≠ 0 := by
    have : b ≠ 0 := by rintro rfl; exact hb (dvd_zero p)
    exact_mod_cast this
  have hd0 : (d : ℚ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; exact hd (dvd_zero p)
    exact_mod_cast this
  refine ⟨a * d + c * b, b * d, fun h => ?_, ?_⟩
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    exacts [hb h, hd h]
  · push_cast
    field_simp

lemma pint_sum {p : ℕ} (hp : p.Prime) (s : Finset ℕ) (f : ℕ → ℚ)
    (h : ∀ i ∈ s, PInt p (f i)) : PInt p (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, hp.one_lt.ne' ∘ Nat.dvd_one.1, by simp⟩
  | insert i s hi ih =>
    rw [sum_insert hi]
    exact pint_add hp (h i (mem_insert_self _ _)) (ih fun j hj => h j (mem_insert_of_mem hj))

/-- The multiples of `p` in `[1, m]` when `p ≤ m < 3p`. -/
lemma filter_dvd_eq {p m : ℕ} (hp : 0 < p) (hpm : p ≤ m) (hm : m < 3 * p) :
    (Icc 1 m).filter (fun i => p ∣ i) = if 2 * p ≤ m then {p, 2 * p} else {p} := by
  ext i
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, j, rfl⟩
    have hj : j < 3 := by
      by_contra hj
      push Not at hj
      nlinarith
    have hj1 : 1 ≤ j := by
      rcases j with _ | j
      · simp at h1
      · omega
    interval_cases j
    · split_ifs <;> simp
    · rw [if_pos (by linarith)]; simp [mul_comm]
  · split_ifs with h
    · simp only [mem_insert, mem_singleton]
      rintro (rfl | rfl)
      · exact ⟨⟨hp, hpm⟩, dvd_refl _⟩
      · exact ⟨⟨by omega, h⟩, dvd_mul_left _ _⟩
    · simp only [mem_singleton]
      rintro rfl
      exact ⟨⟨hp, hpm⟩, dvd_refl _⟩

/-- For a prime `p > 3` with `p ≤ m < 3p`, `p` divides the denominator of `H(m)`: the terms of
`H(m)` with `p` in the denominator add up to `1/p` or `3/(2p)`, all other terms are `p`-integral. -/
lemma dvd_den {p m : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpm : p ≤ m) (hm : m < 3 * p) :
    p ∣ (S_oeis_a002285.H m).den := by
  have hp0 : 0 < p := hp.pos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  -- split the sum
  have hsplit : S_oeis_a002285.H m =
      (∑ i ∈ (Icc 1 m).filter (fun i => p ∣ i), (1 : ℚ) / i) +
        ∑ i ∈ (Icc 1 m).filter (fun i => ¬ p ∣ i), (1 : ℚ) / i := by
    rw [S_oeis_a002285.H, sum_filter_add_sum_filter_not]
  obtain ⟨e, he, hfirst⟩ : ∃ e : ℕ, (e = 2 ∨ e = 3) ∧
      ∑ i ∈ (Icc 1 m).filter (fun i => p ∣ i), (1 : ℚ) / i = e / (2 * p) := by
    rw [filter_dvd_eq hp0 hpm hm]
    split_ifs with h
    · refine ⟨3, Or.inr rfl, ?_⟩
      rw [sum_pair (by omega)]
      push_cast
      field_simp
      ring
    · refine ⟨2, Or.inl rfl, ?_⟩
      simp only [sum_singleton]
      push_cast
      field_simp
  obtain ⟨a, b, hb, hR⟩ := pint_sum hp ((Icc 1 m).filter (fun i => ¬ p ∣ i)) (fun i => (1 : ℚ) / i)
    (fun i hi => ⟨1, i, (mem_filter.1 hi).2, by simp⟩)
  by_contra hD
  set q := S_oeis_a002285.H m with hq
  have hb0 : (b : ℚ) ≠ 0 := by
    have : b ≠ 0 := by rintro rfl; exact hb (dvd_zero p)
    exact_mod_cast this
  have hD0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have key : (q.num : ℚ) / q.den = e / (2 * p) + a / b := by
    rw [Rat.num_div_den, hsplit, hfirst, hR]
  have key2 : ((e * q.den * b : ℕ) : ℤ) = 2 * p * (q.num * b - a * q.den) := by
    have : ((e * q.den * b : ℕ) : ℚ) = 2 * p * (q.num * b - a * q.den) := by
      field_simp at key
      push_cast
      linear_combination (-1 : ℚ) * key
    exact_mod_cast this
  have hdvd : (p : ℤ) ∣ ((e * q.den * b : ℕ) : ℤ) := by
    rw [key2]; exact ⟨2 * (q.num * b - a * q.den), by ring⟩
  rw [Int.natCast_dvd_natCast] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases he with rfl | rfl <;> have := Nat.le_of_dvd (by norm_num) h <;> omega
    · exact hD h
  · exact hb h

end OMA.A002285

namespace OMA.A002285

open Finset Real Filter Topology Chebyshev

/-- `θ(m) - θ(⌊m/3⌋) ≤ log (den H(m))` for `m ≥ 9`: every prime in `(m/3, m]` divides the
denominator. -/
lemma theta_sub_le_log_den (m : ℕ) (hm : 9 ≤ m) :
    θ (m : ℝ) - θ ((m / 3 : ℕ) : ℝ) ≤ Real.log (S_oeis_a002285.H m).den := by
  set s := Nat.primesLE m \ Nat.primesLE (m / 3) with hs
  have hsub : Nat.primesLE (m / 3) ⊆ Nat.primesLE m := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (Nat.div_le_self _ _), hp.2⟩
  have hmem : ∀ p ∈ s, p.Prime ∧ 3 < p ∧ p ≤ m ∧ m < 3 * p := by
    intro p hp
    rw [hs, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    have h4 : m / 3 < p := by
      by_contra h
      exact h3 ⟨by omega, h2⟩
    exact ⟨h2, by omega, h1, by omega⟩
  have hθ : θ (m : ℝ) - θ ((m / 3 : ℕ) : ℝ) = ∑ p ∈ s, Real.log p := by
    rw [theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log, hs, ← sum_sdiff hsub]
    ring
  have hprod : (∏ p ∈ s, p) ∣ (S_oeis_a002285.H m).den :=
    Finset.prod_primes_dvd _ (fun p hp => (hmem p hp).1.prime)
      (fun p hp => dvd_den (hmem p hp).1 (hmem p hp).2.1 (hmem p hp).2.2.1 (hmem p hp).2.2.2)
  have hle : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ (S_oeis_a002285.H m).den := by
    exact_mod_cast Nat.le_of_dvd (S_oeis_a002285.H m).den_pos hprod
  rw [hθ, ← Real.log_prod]
  · apply Real.log_le_log
    · apply prod_pos
      intro p hp
      exact_mod_cast (hmem p hp).1.pos
    · simpa using hle
  · intro p hp
    exact_mod_cast (hmem p hp).1.ne_zero

/-- `log x / log 10 ≤` number of decimal digits of `x`. -/
lemma log_div_le_digits (D : ℕ) (hD : D ≠ 0) :
    Real.log D / Real.log 10 ≤ ((Nat.digits 10 D).length : ℝ) := by
  rw [Nat.length_digits 10 D (by norm_num) hD, div_le_iff₀ (Real.log_pos (by norm_num))]
  have h1 : D < 10 ^ (Nat.log 10 D + 1) := Nat.lt_pow_succ_log_self (by norm_num) D
  have h2 : (D : ℝ) < (10 : ℝ) ^ (Nat.log 10 D + 1) := by exact_mod_cast h1
  have h3 := Real.log_lt_log (by exact_mod_cast Nat.pos_of_ne_zero hD) h2
  rw [Real.log_pow] at h3
  push_cast at h3 ⊢
  linarith

/-- Eventually `log (x + 1) + 2 √x log x ≤ x / 20`. -/
lemma eventually_err : ∀ᶠ x : ℝ in atTop,
    Real.log (x + 1) + 2 * √x * Real.log x ≤ x / 20 := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound
    (show (0 : ℝ) < 1 / 80 by norm_num)
  filter_upwards [h, eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hx0 : 0 ≤ x := by linarith
  have hsq : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm
  rw [hsq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
    abs_of_nonneg (Real.log_nonneg (by linarith))] at hx
  have hs1 : 1 ≤ √x := by rw [Real.one_le_sqrt]; linarith
  have hss : √x * √x = x := Real.mul_self_sqrt hx0
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlx1 : Real.log (x + 1) ≤ 2 * Real.log x := by
    rw [← Real.log_rpow (by linarith)]
    apply Real.log_le_log (by linarith)
    rw [show x ^ (2 : ℝ) = x * x by rw [Real.rpow_two]; ring]
    nlinarith
  have : √x * Real.log x ≤ x / 80 := by nlinarith
  nlinarith

/-- Eventually the ratio is at least `1/2`. -/
lemma eventually_half : ∀ᶠ n : ℕ in atTop,
    (1 / 2 : ℝ) ≤ ((Nat.digits 10 (S_oeis_a002285.H (10 ^ n)).den).length : ℝ) /
      10 ^ ((n : ℝ) - 1) := by
  have hT : Tendsto (fun n : ℕ => (10 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hT.eventually eventually_err, eventually_ge_atTop 1] with n hn hn1
  set m : ℕ := 10 ^ n with hm
  have hmR : (m : ℝ) = (10 : ℝ) ^ n := by rw [hm]; push_cast; ring
  rw [← hmR] at hn
  have hm9 : 9 ≤ m := by
    have : 10 ^ 1 ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
    omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpow : (10 : ℝ) ^ ((n : ℝ) - 1) = m / 10 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_one, hmR]
  rw [hpow, le_div_iff₀ (by positivity)]
  have hD := log_div_le_digits (S_oeis_a002285.H m).den (S_oeis_a002285.H m).den_nz
  have hA := theta_sub_le_log_den m hm9
  have hge := theta_ge m
  have hk : θ ((m / 3 : ℕ) : ℝ) ≤ Real.log 4 * ((m / 3 : ℕ) : ℝ) :=
    theta_le_log4_mul_x (by positivity)
  have hk3 : ((m / 3 : ℕ) : ℝ) * 3 ≤ m := by exact_mod_cast Nat.div_mul_le_self m 3
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl10 : Real.log 10 < 4 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl10pos : 0 < Real.log 10 := Real.log_pos (by norm_num)
  -- `θ m - θ(m/3) ≥ m log 2 / 3 - m / 20 ≥ m log 10 / 20`
  have hmain : (m : ℝ) * Real.log 10 / 20 ≤ Real.log (S_oeis_a002285.H m).den := by
    nlinarith
  rw [div_le_iff₀ hl10pos] at hD
  nlinarith

/-- `log₁₀ e < 1/2`. -/
lemma logb_lt_half : Real.logb 10 (Real.exp 1) < 1 / 2 := by
  rw [Real.logb, Real.log_exp, div_lt_iff₀ (Real.log_pos (by norm_num))]
  have : (2 : ℝ) < Real.log 10 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith [Real.exp_pos 1]
  linarith

end OMA.A002285

/-- The second limit fails: the number of digits of the denominator of `H(10ⁿ)` is at least
`10ⁿ⁻¹ / 2` for large `n`, because every prime `p ∈ (10ⁿ/3, 10ⁿ]` divides it and
`θ(x) - θ(x/3) ≥ (log 2 / 3 - o(1)) x`; hence the ratio cannot tend to `log₁₀ e < 1/2`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002285.main) := by
  intro h
  have h2 := h.2.1
  have := ge_of_tendsto h2 OMA.A002285.eventually_half
  linarith [OMA.A002285.logb_lt_half]
