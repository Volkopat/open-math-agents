import OMAStatements.S_oeis_a192069
import Mathlib

-- Problem: A192069 = A192249/5, the g.f. x^2(1-2x+4x^2-3x^3+x^4)/((x-1)(x^2+x-1)^5) for the coefficient
-- of x in the reduction of p(n-1,x) = Sum_{k<n} binomial(k+4,4) x^k by x^2 -> x + 1.
-- Upstream: formal-conjectures statements/oeis-a192069.lean (declaration OMA.S_oeis_a192069.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated g.f. holds).
-- Proof: x^k = F(k) x + F(k-1) modulo x^2 - x - 1, so A192249(n+1) = V(n) = Sum_{k<=n} binomial(k+4,4) F(k);
-- the combination of V given by (x-1)(x^2+x-1)^5 reduces to a polynomial identity in n, F(n), F(n+1).

namespace OMA.P_oeis_a192069

open OMA.S_oeis_a192069 Polynomial

/-- (F(k-1), F(k)), with F(-1) = 1. -/
def uv : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | k + 1 => ((uv k).2, (uv k).1 + (uv k).2)

theorem xrem (k : ℕ) :
    ∃ h : ℤ[X], (X : ℤ[X]) ^ k = C (uv k).2 * X + C (uv k).1 + (X ^ 2 - X - 1) * h := by
  induction k with
  | zero => exact ⟨0, by simp [uv]⟩
  | succ k ih =>
    obtain ⟨h, e⟩ := ih
    refine ⟨X * h + C (uv k).2, ?_⟩
    have hu : uv (k + 1) = ((uv k).2, (uv k).1 + (uv k).2) := rfl
    rw [hu, pow_succ]
    simp only [map_add]
    linear_combination X * e

def c (k : ℕ) : ℤ := (((k + 4).choose 4 : ℕ) : ℤ)

def V (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), c k * (uv k).2

def U (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), c k * (uv k).1

theorem V_succ (m : ℕ) : V (m + 1) = V m + c (m + 1) * (uv (m + 1)).2 := by
  unfold V
  rw [Finset.sum_range_succ]

theorem U_succ (m : ℕ) : U (m + 1) = U m + c (m + 1) * (uv (m + 1)).1 := by
  unfold U
  rw [Finset.sum_range_succ]

theorem prem (m : ℕ) : ∃ h : ℤ[X], p m = C (V m) * X + C (U m) + (X ^ 2 - X - 1) * h := by
  induction m with
  | zero =>
    refine ⟨0, ?_⟩
    simp [p, V, U, c, uv]
  | succ m ih =>
    obtain ⟨h, e⟩ := ih
    obtain ⟨h', e'⟩ := xrem (m + 1)
    refine ⟨h + C (c (m + 1)) * h', ?_⟩
    have hp : p (m + 1) = p m + C (c (m + 1)) * X ^ (m + 1) := by
      unfold p c
      rw [Finset.sum_range_succ]
    rw [V_succ, U_succ]
    simp only [map_add, map_mul]
    linear_combination hp + e + C (c (m + 1)) * e'

theorem monic_g : (X ^ 2 - X - 1 : ℤ[X]).Monic := by
  have : (X ^ 2 - X - 1 : ℤ[X]) = X ^ 2 - (X + 1) := by ring
  rw [this]
  apply monic_X_pow_sub
  compute_degree!

theorem deg_g : (X ^ 2 - X - 1 : ℤ[X]).degree = 2 := by
  compute_degree!

theorem A_eq (i : ℕ) : A192249 (i + 1) = V i := by
  obtain ⟨h, e⟩ := prem i
  have hm := (div_modByMonic_unique (f := p i) h (C (V i) * X + C (U i)) monic_g
    ⟨e.symm, by rw [deg_g]; exact degree_linear_lt⟩).2
  simp only [A192249, reduce, Nat.add_sub_cancel, hm, coeff_add, coeff_C_mul_X, coeff_C]
  simp

theorem a_eq (i : ℕ) : a (i + 1) = (V i : ℚ) / 5 := by
  rw [a, A_eq]

theorem v_rec (k : ℕ) : (uv (k + 2)).2 = (uv (k + 1)).2 + (uv k).2 := by
  have h1 : (uv (k + 2)).2 = (uv (k + 1)).1 + (uv (k + 1)).2 := rfl
  have h2 : (uv (k + 1)).1 = (uv k).2 := rfl
  rw [h1, h2]
  ring

theorem ch (k : ℕ) : (c k : ℚ) = ((k : ℚ) + 4) * ((k : ℚ) + 3) * ((k : ℚ) + 2) * ((k : ℚ) + 1) / 24 := by
  unfold c
  push_cast
  rw [Nat.cast_choose ℚ (by omega : 4 ≤ k + 4), show k + 4 - 4 = k by omega]
  simp only [Nat.factorial]
  push_cast
  field_simp
  ring

theorem S_zero (m : ℕ) : (1 : ℚ) * (V (m + 11) : ℚ) + (-6 : ℚ) * (V (m + 10) : ℚ) + (10 : ℚ) * (V (m + 9) : ℚ) + (5 : ℚ) * (V (m + 8) : ℚ) + (-25 : ℚ) * (V (m + 7) : ℚ) + (4 : ℚ) * (V (m + 6) : ℚ) + (26 : ℚ) * (V (m + 5) : ℚ) + (-5 : ℚ) * (V (m + 4) : ℚ) + (-15 : ℚ) * (V (m + 3) : ℚ) + (4 : ℚ) * (V (m + 1) : ℚ) + (1 : ℚ) * (V (m) : ℚ) = 0 := by
  have hV1 : V (m + 1) = V (m) + c (m + 1) * (uv (m + 1)).2 := V_succ (m)
  have hV2 : V (m + 2) = V (m + 1) + c (m + 2) * (uv (m + 2)).2 := V_succ (m + 1)
  have hV3 : V (m + 3) = V (m + 2) + c (m + 3) * (uv (m + 3)).2 := V_succ (m + 2)
  have hV4 : V (m + 4) = V (m + 3) + c (m + 4) * (uv (m + 4)).2 := V_succ (m + 3)
  have hV5 : V (m + 5) = V (m + 4) + c (m + 5) * (uv (m + 5)).2 := V_succ (m + 4)
  have hV6 : V (m + 6) = V (m + 5) + c (m + 6) * (uv (m + 6)).2 := V_succ (m + 5)
  have hV7 : V (m + 7) = V (m + 6) + c (m + 7) * (uv (m + 7)).2 := V_succ (m + 6)
  have hV8 : V (m + 8) = V (m + 7) + c (m + 8) * (uv (m + 8)).2 := V_succ (m + 7)
  have hV9 : V (m + 9) = V (m + 8) + c (m + 9) * (uv (m + 9)).2 := V_succ (m + 8)
  have hV10 : V (m + 10) = V (m + 9) + c (m + 10) * (uv (m + 10)).2 := V_succ (m + 9)
  have hV11 : V (m + 11) = V (m + 10) + c (m + 11) * (uv (m + 11)).2 := V_succ (m + 10)
  have hv2 : (uv (m + 2)).2 = (uv (m + 1)).2 + (uv (m)).2 := v_rec (m)
  have hv3 : (uv (m + 3)).2 = (uv (m + 2)).2 + (uv (m + 1)).2 := v_rec (m + 1)
  have hv4 : (uv (m + 4)).2 = (uv (m + 3)).2 + (uv (m + 2)).2 := v_rec (m + 2)
  have hv5 : (uv (m + 5)).2 = (uv (m + 4)).2 + (uv (m + 3)).2 := v_rec (m + 3)
  have hv6 : (uv (m + 6)).2 = (uv (m + 5)).2 + (uv (m + 4)).2 := v_rec (m + 4)
  have hv7 : (uv (m + 7)).2 = (uv (m + 6)).2 + (uv (m + 5)).2 := v_rec (m + 5)
  have hv8 : (uv (m + 8)).2 = (uv (m + 7)).2 + (uv (m + 6)).2 := v_rec (m + 6)
  have hv9 : (uv (m + 9)).2 = (uv (m + 8)).2 + (uv (m + 7)).2 := v_rec (m + 7)
  have hv10 : (uv (m + 10)).2 = (uv (m + 9)).2 + (uv (m + 8)).2 := v_rec (m + 8)
  have hv11 : (uv (m + 11)).2 = (uv (m + 10)).2 + (uv (m + 9)).2 := v_rec (m + 9)
  rw [hV11, hV10, hV9, hV8, hV7, hV6, hV5, hV4, hV3, hV2, hV1]
  push_cast
  simp only [ch]
  rw [hv11, hv10, hv9, hv8, hv7, hv6, hv5, hv4, hv3, hv2]
  push_cast
  ring

theorem a1 : a 1 = 0 := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, a_eq, show V 0 = 0 by decide]
  norm_num

theorem a2 : a 2 = 1 := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, a_eq, show V 1 = 5 by decide]
  norm_num

theorem a3 : a 3 = 4 := by
  rw [show (3 : ℕ) = 2 + 1 by rfl, a_eq, show V 2 = 20 by decide]
  norm_num

theorem a4 : a 4 = 18 := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, a_eq, show V 3 = 90 by decide]
  norm_num

theorem a5 : a 5 = 60 := by
  rw [show (5 : ℕ) = 4 + 1 by rfl, a_eq, show V 4 = 300 by decide]
  norm_num

theorem a6 : a 6 = 186 := by
  rw [show (6 : ℕ) = 5 + 1 by rfl, a_eq, show V 5 = 930 by decide]
  norm_num

theorem a7 : a 7 = 522 := by
  rw [show (7 : ℕ) = 6 + 1 by rfl, a_eq, show V 6 = 2610 by decide]
  norm_num

theorem a8 : a 8 = 1380 := by
  rw [show (8 : ℕ) = 7 + 1 by rfl, a_eq, show V 7 = 6900 by decide]
  norm_num

theorem a9 : a 9 = 3459 := by
  rw [show (9 : ℕ) = 8 + 1 by rfl, a_eq, show V 8 = 17295 by decide]
  norm_num

theorem a10 : a 10 = 8321 := by
  rw [show (10 : ℕ) = 9 + 1 by rfl, a_eq, show V 9 = 41605 by decide]
  norm_num

theorem a11 : a 11 = 19332 := by
  rw [show (11 : ℕ) = 10 + 1 by rfl, a_eq, show V 10 = 96660 by decide]
  norm_num

theorem key (f : PowerSeries ℚ) :
    f * ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1) ^ 5) =
      PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 0 * f) + PowerSeries.C (-6 : ℚ) * (PowerSeries.X ^ 1 * f) + PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 2 * f) + PowerSeries.C (5 : ℚ) * (PowerSeries.X ^ 3 * f) + PowerSeries.C (-25 : ℚ) * (PowerSeries.X ^ 4 * f) + PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 5 * f) + PowerSeries.C (26 : ℚ) * (PowerSeries.X ^ 6 * f) + PowerSeries.C (-5 : ℚ) * (PowerSeries.X ^ 7 * f) + PowerSeries.C (-15 : ℚ) * (PowerSeries.X ^ 8 * f) + PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 10 * f) + PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 11 * f) := by
  simp only [map_one, map_neg, map_ofNat]
  ring

theorem rhs :
    (PowerSeries.X ^ 2 * (1 - 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 4) : PowerSeries ℚ) = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-2 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-3 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 6 := by
  simp only [map_one, map_neg, map_ofNat]
  ring

theorem main' :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) *
        ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1) ^ 5) =
      PowerSeries.X ^ 2 *
        (1 - 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 +
          PowerSeries.X ^ 4) := by
  rw [key, rhs]
  ext n
  simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  rcases lt_or_ge n 12 with h | h
  · interval_cases n <;> simp [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 12 := ⟨n - 12, by omega⟩
    simp only [show 0 ≤ m + 12 by omega,
        show m + 12 - 0 = m + 12 by omega,
        show 1 ≤ m + 12 by omega,
        show m + 12 - 1 = m + 11 by omega,
        show 2 ≤ m + 12 by omega,
        show m + 12 - 2 = m + 10 by omega,
        show 3 ≤ m + 12 by omega,
        show m + 12 - 3 = m + 9 by omega,
        show 4 ≤ m + 12 by omega,
        show m + 12 - 4 = m + 8 by omega,
        show 5 ≤ m + 12 by omega,
        show m + 12 - 5 = m + 7 by omega,
        show 6 ≤ m + 12 by omega,
        show m + 12 - 6 = m + 6 by omega,
        show 7 ≤ m + 12 by omega,
        show m + 12 - 7 = m + 5 by omega,
        show 8 ≤ m + 12 by omega,
        show m + 12 - 8 = m + 4 by omega,
        show 10 ≤ m + 12 by omega,
        show m + 12 - 10 = m + 2 by omega,
        show 11 ≤ m + 12 by omega,
        show m + 12 - 11 = m + 1 by omega,
        show m + 1 ≠ 0 by omega,
        show m + 2 ≠ 0 by omega,
        show m + 3 ≠ 0 by omega,
        show m + 4 ≠ 0 by omega,
        show m + 5 ≠ 0 by omega,
        show m + 6 ≠ 0 by omega,
        show m + 7 ≠ 0 by omega,
        show m + 8 ≠ 0 by omega,
        show m + 9 ≠ 0 by omega,
        show m + 10 ≠ 0 by omega,
        show m + 11 ≠ 0 by omega,
        show m + 12 ≠ 0 by omega,
        show m + 12 ≠ 2 by omega,
        show m + 12 ≠ 3 by omega,
        show m + 12 ≠ 4 by omega,
        show m + 12 ≠ 5 by omega,
        show m + 12 ≠ 6 by omega,
        if_true, if_false]
    have ha1 : a (m + 1) = (V m : ℚ) / 5 := a_eq m
    have ha2 : a (m + 2) = (V (m + 1) : ℚ) / 5 := a_eq (m + 1)
    have ha3 : a (m + 3) = (V (m + 2) : ℚ) / 5 := a_eq (m + 2)
    have ha4 : a (m + 4) = (V (m + 3) : ℚ) / 5 := a_eq (m + 3)
    have ha5 : a (m + 5) = (V (m + 4) : ℚ) / 5 := a_eq (m + 4)
    have ha6 : a (m + 6) = (V (m + 5) : ℚ) / 5 := a_eq (m + 5)
    have ha7 : a (m + 7) = (V (m + 6) : ℚ) / 5 := a_eq (m + 6)
    have ha8 : a (m + 8) = (V (m + 7) : ℚ) / 5 := a_eq (m + 7)
    have ha9 : a (m + 9) = (V (m + 8) : ℚ) / 5 := a_eq (m + 8)
    have ha10 : a (m + 10) = (V (m + 9) : ℚ) / 5 := a_eq (m + 9)
    have ha11 : a (m + 11) = (V (m + 10) : ℚ) / 5 := a_eq (m + 10)
    have ha12 : a (m + 12) = (V (m + 11) : ℚ) / 5 := a_eq (m + 11)
    simp only [ha12, ha11, ha10, ha9, ha8, ha7, ha6, ha5, ha4, ha3, ha2, ha1]
    linear_combination (1 / 5 : ℚ) * S_zero m

end OMA.P_oeis_a192069

theorem OMA.solution : type_of% @OMA.S_oeis_a192069.main := OMA.P_oeis_a192069.main'
