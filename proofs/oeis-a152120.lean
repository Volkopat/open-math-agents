import OMAStatements.S_oeis_a152120
import Mathlib

/-!
# A152120: Barker's recurrence and generating function

Put `u = √5 + √2` and `v = √5 - √2`, so `u v = 3` and `u² + v² = 14`. With `ω = exp(2πi/N)`,
the product of `u + ω^k v` over `k < N` is `u^N - (-v)^N`. Pairing `k` with `N - k` gives
`u² + v² + 2uv cos(2πk/N) = 4 (2 + 3 cos²(πk/N))`; the unpaired factors are `u + v`
and, for even `N`, `u - v`. Hence `a(2m+1) = 2 (u^(2m+1) + v^(2m+1)) / (u + v)` and
`a(2m+2) = 4 (u^(2m+2) - v^(2m+2)) / ((u + v)(u - v))`. Both `u²` and `v²` are roots of
`t² - 14 t + 9`, which gives the recurrence, and the generating function follows from the
recurrence and the first five values. (Proof outline as in the note of @Iraeeee.)
-/

open Finset

namespace OMA.A152120Proof

open OMA.S_oeis_a152120

theorem prod_roots (N : ℕ) (hN : 0 < N) (x y : ℂ) :
    ∏ k ∈ range N, (x + Complex.exp (2 * Real.pi * Complex.I / N) ^ k * y) = x ^ N - (-y) ^ N := by
  set ω := Complex.exp (2 * Real.pi * Complex.I / N) with hω
  have hprim : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N (by omega)
  classical
  rw [hprim.pow_sub_pow_eq_prod_sub_mul x (-y) hN]
  have himg : (range N).image (fun k => ω ^ k) = Polynomial.nthRootsFinset N (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
      rw [Polynomial.mem_nthRootsFinset hN, ← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    · rw [hprim.card_nthRootsFinset, Finset.card_image_of_injOn, card_range]
      intro a ha b hb hab
      exact hprim.pow_inj (by simpa using ha) (by simpa using hb) hab
  rw [← himg, Finset.prod_image]
  · refine Finset.prod_congr rfl fun k _ => by ring
  · intro a ha b hb hab
    exact hprim.pow_inj (by simpa using ha) (by simpa using hb) hab

theorem pair_odd {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∏ k ∈ range (2 * m + 1), f k = f 0 * ∏ j ∈ range m, (f (j + 1) * f (2 * m - j)) := by
  rw [prod_range_succ', mul_comm, prod_mul_distrib]
  congr 1
  rw [show 2 * m = m + m by ring, prod_range_add]
  congr 1
  rw [← prod_range_reflect]
  refine prod_congr rfl fun j hj => ?_
  have := mem_range.mp hj
  congr 1
  omega

theorem pair_even {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∏ k ∈ range (2 * m + 2), f k =
      f 0 * f (m + 1) * ∏ j ∈ range m, (f (j + 1) * f (2 * m + 1 - j)) := by
  rw [prod_range_succ', prod_mul_distrib]
  rw [show 2 * m + 1 = m + 1 + m by ring, prod_range_add, prod_range_succ]
  rw [← prod_range_reflect (fun j => f (m + 1 + j + 1)) m]
  have : ∏ j ∈ range m, f (m + 1 + (m - 1 - j) + 1) = ∏ j ∈ range m, f (m + 1 + m - j) := by
    refine prod_congr rfl fun j hj => ?_
    have := mem_range.mp hj
    congr 1
    omega
  rw [this]
  ac_rfl

theorem cos_pair (N a : ℕ) (hN : 0 < N) (ha : a ≤ N) (u v : ℝ) :
    ((u : ℂ) + Complex.exp (2 * Real.pi * Complex.I / N) ^ a * v) *
      ((u : ℂ) + Complex.exp (2 * Real.pi * Complex.I / N) ^ (N - a) * v) =
      ((u ^ 2 + v ^ 2 + 2 * u * v * Real.cos (2 * (a * Real.pi / N)) : ℝ) : ℂ) := by
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have e1 : Complex.exp (2 * Real.pi * Complex.I / N) ^ a =
      Complex.exp (((2 * (a * Real.pi / N) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
  have e2 : Complex.exp (2 * Real.pi * Complex.I / N) ^ (N - a) =
      Complex.exp (-(((2 * (a * Real.pi / N) : ℝ) : ℂ)) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    rw [show -(((2 * (a * Real.pi / N) : ℝ) : ℂ)) * Complex.I =
      ((N - a : ℕ) : ℂ) * (2 * Real.pi * Complex.I / N) + ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by
        push_cast [Nat.cast_sub ha]; field_simp; ring]
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [e1, e2]
  set θ : ℝ := 2 * (a * Real.pi / N)
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  linear_combination (v : ℂ) ^ 2 * Complex.cos_sq_add_sin_sq (θ : ℂ)

noncomputable def u : ℝ := Real.sqrt 5 + Real.sqrt 2
noncomputable def v : ℝ := Real.sqrt 5 - Real.sqrt 2

theorem h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
theorem h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem uv : u * v = 3 := by
  unfold u v; linear_combination h5 - h2

theorem u2v2 : u ^ 2 + v ^ 2 = 14 := by
  unfold u v; linear_combination 2 * h5 + 2 * h2

theorem upv : u + v ≠ 0 := by
  unfold u v
  have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  intro h; linarith

theorem umv : u - v ≠ 0 := by
  unfold u v
  have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  intro h; linarith

theorem u4 : u ^ 4 = 14 * u ^ 2 - 9 := by
  have e : u ^ 2 = 7 + 2 * (Real.sqrt 5 * Real.sqrt 2) := by
    unfold u; linear_combination h5 + h2
  rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, e]
  linear_combination (4 * Real.sqrt 2 ^ 2) * h5 + 20 * h2

theorem v4 : v ^ 4 = 14 * v ^ 2 - 9 := by
  have e : v ^ 2 = 7 - 2 * (Real.sqrt 5 * Real.sqrt 2) := by
    unfold v; linear_combination h5 + h2
  rw [show v ^ 4 = (v ^ 2) ^ 2 by ring, e]
  linear_combination (4 * Real.sqrt 2 ^ 2) * h5 + 20 * h2

/-- The paired factor. -/
theorem pair_factor (N j : ℕ) (hN : 0 < N) (hj : j + 1 ≤ N) :
    ((u : ℂ) + Complex.exp (2 * Real.pi * Complex.I / N) ^ (j + 1) * v) *
      ((u : ℂ) + Complex.exp (2 * Real.pi * Complex.I / N) ^ (N - (j + 1)) * v) =
      ((4 * factor N (j + 1) : ℝ) : ℂ) := by
  rw [cos_pair N (j + 1) hN hj u v]
  congr 1
  unfold factor
  rw [show (2 * u * v) = 2 * (u * v) by ring, uv, u2v2, Real.cos_two_mul]
  push_cast
  ring

theorem key_odd (m : ℕ) :
    u ^ (2 * m + 1) + v ^ (2 * m + 1) =
      (u + v) * (4 ^ m * ∏ j ∈ range m, factor (2 * m + 1) (j + 1)) := by
  have hN : 0 < 2 * m + 1 := by omega
  have h := prod_roots (2 * m + 1) hN u v
  rw [pair_odd, Odd.neg_pow (by exact ⟨m, rfl⟩), sub_neg_eq_add] at h
  have h' : ∀ j ∈ range m,
      ((u : ℂ) + Complex.exp (2 * Real.pi * Complex.I / ((2 * m + 1 : ℕ) : ℂ)) ^ (j + 1) * v) *
      ((u : ℂ) + Complex.exp (2 * Real.pi * Complex.I / ((2 * m + 1 : ℕ) : ℂ)) ^ (2 * m - j) * v) =
      ((4 * factor (2 * m + 1) (j + 1) : ℝ) : ℂ) := by
    intro j hj
    have := mem_range.mp hj
    rw [show 2 * m - j = 2 * m + 1 - (j + 1) by omega]
    exact pair_factor _ _ hN (by omega)
  rw [prod_congr rfl h', pow_zero, one_mul] at h
  have h'' : ((u ^ (2 * m + 1) + v ^ (2 * m + 1) : ℝ) : ℂ) =
      (((u + v) * ∏ j ∈ range m, (4 * factor (2 * m + 1) (j + 1)) : ℝ) : ℂ) := by
    push_cast at h ⊢; exact h.symm
  have := Complex.ofReal_injective h''
  rw [this, prod_mul_distrib, prod_const, card_range]

theorem key_even (m : ℕ) :
    u ^ (2 * m + 2) - v ^ (2 * m + 2) =
      (u + v) * (u - v) * (4 ^ m * ∏ j ∈ range m, factor (2 * m + 2) (j + 1)) := by
  have hN : 0 < 2 * m + 2 := by omega
  have h := prod_roots (2 * m + 2) hN u v
  rw [pair_even, Even.neg_pow (by exact ⟨m + 1, by ring⟩)] at h
  have h' : ∀ j ∈ range m,
      ((u : ℂ) + Complex.exp (2 * Real.pi * Complex.I / ((2 * m + 2 : ℕ) : ℂ)) ^ (j + 1) * v) *
      ((u : ℂ) + Complex.exp (2 * Real.pi * Complex.I / ((2 * m + 2 : ℕ) : ℂ)) ^ (2 * m + 1 - j) * v) =
      ((4 * factor (2 * m + 2) (j + 1) : ℝ) : ℂ) := by
    intro j hj
    have := mem_range.mp hj
    rw [show 2 * m + 1 - j = 2 * m + 2 - (j + 1) by omega]
    exact pair_factor _ _ hN (by omega)
  have hmid : Complex.exp (2 * Real.pi * Complex.I / ((2 * m + 2 : ℕ) : ℂ)) ^ (m + 1) = -1 := by
    rw [← Complex.exp_nat_mul]
    rw [show ((m + 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / ((2 * m + 2 : ℕ) : ℂ)) =
      Real.pi * Complex.I by push_cast; field_simp]
    exact Complex.exp_pi_mul_I
  rw [prod_congr rfl h', pow_zero, one_mul, hmid] at h
  have h'' : ((u ^ (2 * m + 2) - v ^ (2 * m + 2) : ℝ) : ℂ) =
      (((u + v) * (u - v) * ∏ j ∈ range m, (4 * factor (2 * m + 2) (j + 1)) : ℝ) : ℂ) := by
    push_cast at h ⊢; rw [← h]; ring
  have := Complex.ofReal_injective h''
  rw [this, prod_mul_distrib, prod_const, card_range]

theorem a_odd (m : ℕ) : a (2 * m + 1) = 2 * (u ^ (2 * m + 1) + v ^ (2 * m + 1)) / (u + v) := by
  rw [key_odd, a, show (2 * m + 1 - 1) / 2 = m by omega]
  field_simp [upv]
  rw [pow_succ, pow_mul]
  norm_num
  ring

theorem a_even (m : ℕ) :
    a (2 * m + 2) = 4 * (u ^ (2 * m + 2) - v ^ (2 * m + 2)) / ((u + v) * (u - v)) := by
  rw [key_even, a, show (2 * m + 2 - 1) / 2 = m by omega]
  field_simp [upv, umv]
  rw [pow_succ, pow_succ, pow_mul]
  norm_num
  ring

theorem recurrence : ∀ n : ℕ, 4 < n → a n = 14 * a (n - 2) - 9 * a (n - 4) := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
    subst hm
    rw [show k + 3 + (k + 3) = 2 * (k + 2) + 2 by ring,
      show 2 * (k + 2) + 2 - 2 = 2 * (k + 1) + 2 by omega,
      show 2 * (k + 2) + 2 - 4 = 2 * k + 2 by omega, a_even, a_even, a_even]
    have e : u ^ (2 * (k + 2) + 2) - v ^ (2 * (k + 2) + 2) =
        14 * (u ^ (2 * (k + 1) + 2) - v ^ (2 * (k + 1) + 2)) -
          9 * (u ^ (2 * k + 2) - v ^ (2 * k + 2)) := by
      linear_combination u ^ (2 * k + 2) * u4 - v ^ (2 * k + 2) * v4
    rw [e]; ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    subst hm
    rw [show 2 * (k + 2) + 1 - 2 = 2 * (k + 1) + 1 by omega,
      show 2 * (k + 2) + 1 - 4 = 2 * k + 1 by omega, a_odd, a_odd, a_odd]
    have e : u ^ (2 * (k + 2) + 1) + v ^ (2 * (k + 2) + 1) =
        14 * (u ^ (2 * (k + 1) + 1) + v ^ (2 * (k + 1) + 1)) -
          9 * (u ^ (2 * k + 1) + v ^ (2 * k + 1)) := by
      linear_combination u ^ (2 * k + 1) * u4 + v ^ (2 * k + 1) * v4
    rw [e]; ring

theorem a0 : a 0 = 1 := by simp [a]
theorem a1 : a 1 = 2 := by simp [a]
theorem a2 : a 2 = 4 := by simp [a]; norm_num
theorem a3 : a 3 = 22 := by
  simp [a, factor, Real.cos_pi_div_three]; norm_num
theorem a4 : a 4 = 56 := by
  simp [a, factor, Real.cos_pi_div_four]
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem gen : generating a := by
  show PowerSeries.mk a * (1 - PowerSeries.C 14 * PowerSeries.X ^ 2 +
      PowerSeries.C 9 * PowerSeries.X ^ 4) = _
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub]
  rw [show PowerSeries.mk a * (PowerSeries.C 14 * PowerSeries.X ^ 2) =
      PowerSeries.C 14 * (PowerSeries.mk a * PowerSeries.X ^ 2) by ring,
    show PowerSeries.mk a * (PowerSeries.C 9 * PowerSeries.X ^ 4) =
      PowerSeries.C 9 * (PowerSeries.mk a * PowerSeries.X ^ 4) by ring]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_X, PowerSeries.coeff_one]
  rcases n with _ | _ | _ | _ | _ | n
  · simp [a0]
  · simp [a1]
  · simp [a2, a0]; norm_num
  · simp [a3, a1]; norm_num
  · simp [a4, a2, a0]; norm_num
  · have := recurrence (n + 5) (by omega)
    simp only [show n + 5 - 2 = n + 3 by omega, show n + 5 - 4 = n + 1 by omega] at this
    rw [show n + 1 + 1 + 1 + 1 + 1 = n + 5 from rfl]
    simp only [show n + 5 - 2 = n + 3 by omega, show n + 5 - 4 = n + 1 by omega,
      show n + 5 - 3 = n + 2 by omega, PowerSeries.coeff_C, if_pos (show 2 ≤ n + 5 by omega),
      if_pos (show 3 ≤ n + 5 by omega), if_pos (show 4 ≤ n + 5 by omega),
      if_neg (show n + 5 ≠ 0 by omega), if_neg (show n + 5 ≠ 1 by omega),
      if_neg (show n + 3 ≠ 0 by omega), if_neg (show n + 2 ≠ 0 by omega),
      if_neg (show n + 1 ≠ 0 by omega)]
    rw [this]; ring

end OMA.A152120Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a152120.main :=
  ⟨OMA.A152120Proof.recurrence, OMA.A152120Proof.gen⟩
