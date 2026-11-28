import OMAStatements.S_oeis_a025249
import Mathlib

/-!
Credit: @ivillar
Proof: with B = sum_{n >= 1} s(n) x^n, the convolution recursion (together with s(1) = 1,
s(2) = 0, s(3) = 2) says B^2 - (1 + x) B + x + 2x^3 = 0, since for n >= 4 the full convolution
[x^n] B^2 equals s(n) + s(n - 1). Then S = 1 + x - 2B satisfies S^2 = R with
R = 1 - 2x + x^2 - 8x^3. Differentiating and multiplying by S gives R (2 S') = R' S, whose
coefficients give a first-order recurrence for c(k) = [x^k] S. Since c(k + 3) = -4 a(k), the
conjectured recurrence at n is minus one eighth of that relation at n - 1, rewritten in a.
-/

namespace OMAA025249Helpers
open OMA.S_oeis_a025249 PowerSeries

noncomputable def B (s : ℕ → ℤ) : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then 0 else (s n : ℚ))

noncomputable def S (s : ℕ → ℤ) : ℚ⟦X⟧ := 1 + X - C 2 * B s

theorem cB (s : ℕ → ℤ) (n : ℕ) : coeff n (B s) = if n = 0 then 0 else (s n : ℚ) := by
  simp [B]

theorem cB0 (s : ℕ → ℤ) : coeff 0 (B s) = 0 := by
  simp [B]

theorem cBs (s : ℕ → ℤ) (n : ℕ) (h : n ≠ 0) : coeff n (B s) = (s n : ℚ) := by
  simp [B, h]

theorem convB (s : ℕ → ℤ) (h1 : s 1 = 1) (h2 : s 2 = 0)
    (hr : ∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) (q : ℕ) :
    coeff (q + 4) (B s * B s) = (s (q + 4) : ℚ) + s (q + 3) := by
  have hI : ∑ k ∈ Finset.Icc 1 (q + 1), (s k : ℚ) * s (q + 4 - k) =
      ∑ k ∈ Finset.range (q + 1), (s (k + 1) : ℚ) * s (q + 4 - (k + 1)) := by
    apply Finset.sum_nbij' (fun k => k - 1) (fun k => k + 1)
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      show k - 1 + 1 = k
      omega
    · intro k _
      show k + 1 - 1 = k
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      show (s k : ℚ) * s (q + 4 - k) = s (k - 1 + 1) * s (q + 4 - (k - 1 + 1))
      rw [Nat.sub_add_cancel hk.1]
  have hq := hr (q + 4) (by omega)
  rw [show q + 4 - 3 = q + 1 by omega] at hq
  have hq' : (s (q + 4) : ℚ) = ∑ k ∈ Finset.Icc 1 (q + 1), (s k : ℚ) * s (q + 4 - k) := by
    rw [hq]
    push_cast
    rfl
  have hmid : ∑ k ∈ Finset.range (q + 1), coeff (k + 1) (B s) * coeff (q + 4 - (k + 1)) (B s) =
      ∑ k ∈ Finset.range (q + 1), (s (k + 1) : ℚ) * s (q + 4 - (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [cBs s (k + 1) (by omega), cBs s (q + 4 - (k + 1)) (by omega)]
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ', hmid, hq', hI,
    show q + 4 - (q + 2) = 2 by omega, show q + 4 - (q + 3) = 1 by omega,
    show q + 4 - (q + 4) = 0 by omega]
  simp only [cB0, cBs s 1 one_ne_zero, cBs s 2 two_ne_zero, cBs s (q + 2) (by omega),
    cBs s (q + 3) (by omega), h1, h2, zero_mul, mul_zero]
  push_cast
  ring

theorem quad (s : ℕ → ℤ) (h1 : s 1 = 1) (h2 : s 2 = 0) (h3 : s 3 = 2)
    (hr : ∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) :
    B s * B s - B s - X ^ 1 * B s + X + C 2 * X ^ 3 = 0 := by
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X, coeff_X_pow, map_zero]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;>
      simp [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
        cB, h1, h2, h3]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 4 := ⟨n - 4, by omega⟩
    rw [convB s h1 h2 hr q, if_pos (by omega), if_neg (by omega), if_neg (by omega),
      show q + 4 - 1 = q + 3 by omega, cBs s (q + 4) (by omega), cBs s (q + 3) (by omega)]
    ring

theorem hS (s : ℕ → ℤ) (h1 : s 1 = 1) (h2 : s 2 = 0) (h3 : s 3 = 2)
    (hr : ∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) :
    S s ^ 2 = 1 - C 2 * X + X ^ 2 - C 8 * X ^ 3 := by
  have q := quad s h1 h2 h3 hr
  rw [map_ofNat C 2] at q
  unfold S
  rw [map_ofNat C 2, map_ofNat C 8]
  linear_combination 4 * q

theorem h1d (s : ℕ → ℤ) : d⁄dX ℚ (S s ^ 2) = 2 * S s * d⁄dX ℚ (S s) := by
  rw [derivative_pow]; norm_num

theorem h2d : d⁄dX ℚ (1 - C 2 * X + X ^ 2 - C 8 * X ^ 3 : ℚ⟦X⟧) =
    -(C 2) + C 2 * X - C 24 * X ^ 2 := by
  ext k
  rw [coeff_derivative]
  rcases k with _ | _ | _ | k <;> simp [coeff_X_pow, coeff_one, coeff_C] <;> norm_num

theorem T (s : ℕ → ℤ) (hsq : S s ^ 2 = 1 - C 2 * X + X ^ 2 - C 8 * X ^ 3)
    (j i1 i2 i3 i4 : ℕ) (h1 : i1 = j + 1) (h2 : i2 = j + 1 + 1)
    (h3 : i3 = j + 1 + 1 + 1) (h4 : i4 = j + 1 + 1 + 1 + 1) :
    2 * ((j : ℚ) + 4) * coeff i4 (S s) - 4 * ((j : ℚ) + 3) * coeff i3 (S s)
      + 2 * ((j : ℚ) + 2) * coeff i2 (S s) - 16 * ((j : ℚ) + 1) * coeff i1 (S s)
      = -2 * coeff i3 (S s) + 2 * coeff i2 (S s) - 24 * coeff i1 (S s) := by
  subst h1 h2 h3 h4
  have E0 : (1 - C 2 * X + X ^ 2 - C 8 * X ^ 3) * (C 2 * d⁄dX ℚ (S s)) =
      (-(C 2) + C 2 * X - C 24 * X ^ 2) * S s := by
    rw [← h2d, ← hsq, h1d, map_ofNat C 2]
    ring
  have h := congrArg (coeff (j + 1 + 1 + 1)) E0
  have eL : (1 - C 2 * X + X ^ 2 - C 8 * X ^ 3) * (C 2 * d⁄dX ℚ (S s)) =
      C 2 * d⁄dX ℚ (S s) - C 2 * (C 2 * (X * d⁄dX ℚ (S s)))
        + C 2 * (X * (X * d⁄dX ℚ (S s)))
        - C 8 * (C 2 * (X * (X * (X * d⁄dX ℚ (S s))))) := by ring
  have eR : (-(C 2) + C 2 * X - C 24 * X ^ 2) * S s =
      -(C 2 * S s) + C 2 * (X * S s) - C 24 * (X * (X * S s)) := by ring
  rw [eL, eR] at h
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at h
  push_cast at h
  linear_combination h

theorem hs (s : ℕ → ℤ) (k i : ℕ) (hi : i = k + 3) : coeff i (S s) = -4 * a s k := by
  subst hi
  unfold S
  rw [map_sub, map_add, coeff_one, coeff_X, coeff_C_mul, cBs s (k + 3) (by omega),
    if_neg (by omega), if_neg (by omega), show a s k = (s (k + 3) : ℚ) / 2 from rfl]
  ring

end OMAA025249Helpers

open OMAA025249Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a025249.main := by
  intro s h1 h2 h3 hr n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  push_cast
  have t := T s (hS s h1 h2 h3 hr) (m + 3) (m + 4) (m + 5) (m + 6) (m + 7) (by omega)
    (by omega) (by omega) (by omega)
  have g7 := hs s (m + 4) (m + 7) (by omega)
  have g6 := hs s (m + 3) (m + 6) (by omega)
  have g5 := hs s (m + 2) (m + 5) (by omega)
  have g4 := hs s (m + 1) (m + 4) (by omega)
  push_cast at t
  linear_combination (-1 / 8 : ℚ) * t + (((m : ℚ) + 7) / 4) * g7
    - ((2 * (m : ℚ) + 11) / 4) * g6 + (((m : ℚ) + 4) / 4) * g5 - (2 * (m : ℚ) + 5) * g4
