import OMAStatements.S_oeis_a131607
import Mathlib

/-!
Credit: @ivillar
Proof: write P = A001333 and r(n) = P(n) mod 10, so P(n) = 10 a(n) + r(n). The denominator of
the g.f. is the reversal of Q(x) = x^9 - 3x^8 + x^7 + x^6 + x^3 - 3x^2 + x + 1
= (x^2 - 2x - 1)(x^7 - x^6 + x - 1), so the operator Q(E) kills P. Also
P(n+12) = 13860 P(n+1) + 5741 P(n), so r has period 12, and Q(E) r = 0 is checked on one
period. Hence Q(E) a = 0, which is the recurrence (for every n >= 9), and with the first nine
terms it gives the g.f.
-/

namespace OMAA131607Helpers
open PowerSeries OMA.S_oeis_a131607

theorem P_rec (k : ℕ) : (P (k + 2) : ℤ) = 2 * P (k + 1) + P k := by
  show ((2 * P (k + 1) + P k : ℕ) : ℤ) = _
  push_cast
  ring

theorem shift (n : ℕ) : P (n + 12) = 13860 * P (n + 1) + 5741 * P n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · decide
    · decide
    · have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have e1 : P (n + 1 + 1 + 12) = 2 * P (n + 1 + 12) + P (n + 12) := rfl
      have e2 : P (n + 1 + 1 + 1) = 2 * P (n + 1 + 1) + P (n + 1) := rfl
      have e3 : P (n + 1 + 1) = 2 * P (n + 1) + P n := rfl
      rw [e1, h1, h0, e2, e3]
      ring

theorem rper (n : ℕ) : P (n + 12) % 10 = P n % 10 := by
  rw [shift]
  omega

/-- The operator Q(E) applied to r(n) = P(n) mod 10. -/
def Lr (m : ℕ) : ℤ :=
  ((P (m + 9) % 10 : ℕ) : ℤ) - 3 * ((P (m + 8) % 10 : ℕ) : ℤ) + ((P (m + 7) % 10 : ℕ) : ℤ) +
    ((P (m + 6) % 10 : ℕ) : ℤ) + ((P (m + 3) % 10 : ℕ) : ℤ) - 3 * ((P (m + 2) % 10 : ℕ) : ℤ) +
    ((P (m + 1) % 10 : ℕ) : ℤ) + ((P m % 10 : ℕ) : ℤ)

theorem Lr_per (m : ℕ) : Lr (m + 12) = Lr m := by
  have hj : ∀ j, P (m + 12 + j) % 10 = P (m + j) % 10 := by
    intro j
    rw [show m + 12 + j = (m + j) + 12 by ring]
    exact rper (m + j)
  unfold Lr
  rw [hj 9, hj 8, hj 7, hj 6, hj 3, hj 2, hj 1, rper m]

theorem Lr_zero (m : ℕ) : Lr m = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 12 with h | h
    · interval_cases m <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 12 := ⟨m - 12, by omega⟩
      rw [Lr_per]
      exact ih k (by omega)

theorem La (m : ℕ) :
    (a (m + 9) : ℤ) - 3 * a (m + 8) + a (m + 7) + a (m + 6) + a (m + 3) - 3 * a (m + 2) +
      a (m + 1) + a m = 0 := by
  have h7 : (P (m + 9) : ℤ) = 2 * P (m + 8) + P (m + 7) := P_rec (m + 7)
  have h6 : (P (m + 8) : ℤ) = 2 * P (m + 7) + P (m + 6) := P_rec (m + 6)
  have h1 : (P (m + 3) : ℤ) = 2 * P (m + 2) + P (m + 1) := P_rec (m + 1)
  have h0 : (P (m + 2) : ℤ) = 2 * P (m + 1) + P m := P_rec m
  have hP : (P (m + 9) : ℤ) - 3 * P (m + 8) + P (m + 7) + P (m + 6) + P (m + 3) -
      3 * P (m + 2) + P (m + 1) + P m = 0 := by
    linear_combination h7 - h6 + h1 - h0
  have hr := Lr_zero m
  unfold Lr at hr
  unfold a
  omega

theorem coeff_mk_mul_X_pow (f : ℕ → ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℤ) (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (f : ℕ → ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (f : ℕ → ℤ) (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * f j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at f n k j h]

end OMAA131607Helpers

open PowerSeries OMAA131607Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a131607.main := by
  have hrec : ∀ n : ℕ, 12 < n → (OMA.S_oeis_a131607.a n : ℤ) =
      3 * OMA.S_oeis_a131607.a (n - 1) - OMA.S_oeis_a131607.a (n - 2) -
        OMA.S_oeis_a131607.a (n - 3) - OMA.S_oeis_a131607.a (n - 6) +
          3 * OMA.S_oeis_a131607.a (n - 7) - OMA.S_oeis_a131607.a (n - 8) -
            OMA.S_oeis_a131607.a (n - 9) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega,
      show m + 9 - 3 = m + 6 by omega, show m + 9 - 6 = m + 3 by omega,
      show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega,
      show m + 9 - 9 = m by omega]
    linarith [La m]
  refine ⟨?_, hrec⟩
  set f : ℕ → ℤ := fun n => (OMA.S_oeis_a131607.a n : ℤ) with hfdef
  ext n
  have hD : ((1 - X) * (1 + X ^ 2) * (1 - 2 * X - X ^ 2) * (1 - X ^ 2 + X ^ 4) : PowerSeries ℤ) =
      X ^ 0 - C 3 * X ^ 1 + X ^ 2 + X ^ 3 + X ^ 6 - C 3 * X ^ 7 + X ^ 8 + X ^ 9 := by
    rw [map_ofNat C 3]; ring
  have hN : (X ^ 4 * (1 + X - 2 * X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℤ) =
      X ^ 4 + X ^ 5 - C 2 * X ^ 6 + X ^ 7 + X ^ 8 := by
    rw [map_ofNat C 2]; ring
  rw [hD, hN]
  have v0 : f 0 = 0 := by simp only [hfdef]; decide
  have v1 : f 1 = 0 := by simp only [hfdef]; decide
  have v2 : f 2 = 0 := by simp only [hfdef]; decide
  have v3 : f 3 = 0 := by simp only [hfdef]; decide
  have v4 : f 4 = 1 := by simp only [hfdef]; decide
  have v5 : f 5 = 4 := by simp only [hfdef]; decide
  have v6 : f 6 = 9 := by simp only [hfdef]; decide
  have v7 : f 7 = 23 := by simp only [hfdef]; decide
  have v8 : f 8 = 57 := by simp only [hfdef]; decide
  rcases Nat.lt_or_ge n 9 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_C_mul, coeff_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v0, v1, v2]
    · norm_num [v0, v1, v2, v3]
    · norm_num [v1, v2, v3, v4]
    · norm_num [v2, v3, v4, v5]
    · norm_num [v0, v3, v4, v5, v6]
    · norm_num [v0, v1, v4, v5, v6, v7]
    · norm_num [v0, v1, v2, v5, v6, v7, v8]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at f (m + 9) 0 (m + 9) (by omega), coeff_at_C f 3 (m + 9) 1 (m + 8) (by omega),
      coeff_at f (m + 9) 2 (m + 7) (by omega), coeff_at f (m + 9) 3 (m + 6) (by omega),
      coeff_at f (m + 9) 6 (m + 3) (by omega), coeff_at_C f 3 (m + 9) 7 (m + 2) (by omega),
      coeff_at f (m + 9) 8 (m + 1) (by omega), coeff_at f (m + 9) 9 m (by omega),
      coeff_C_mul, coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow,
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    have hr := La m
    simp only [hfdef]
    linear_combination hr
