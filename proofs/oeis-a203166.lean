import OMAStatements.S_oeis_a203166
import Mathlib

/-!
# A203166: Mathar's recurrence and generating function

The digits repeat with period L, so any L consecutive digits have the same product P and the same
(L−1)-st elementary symmetric function c. Hence (p, e) = products n satisfies p(n+L) = P·p(n) and
e(n+L) = P·e(n) + c·p(n), and eliminating p gives e(n+2L) = 2P·e(n+L) − P²·e(n). Multiplying the
series by (1 − Px^L)² kills every coefficient from x^(2L) on; the first 2L are computed directly.
-/

namespace PA203166
open OMA.S_oeis_a203166

theorem step (n : ℕ) :
    products (n + 1) = ((products n).1 * digit n, (products n).2 * digit n + (products n).1) := by
  rw [products]

theorem window (n : ℕ) :
    digit n * digit (n + 1) * digit (n + 2) * digit (n + 3) * digit (n + 4) = 120 ∧
    digit (n + 1) * digit (n + 2) * digit (n + 3) * digit (n + 4) +
      digit n * digit (n + 2) * digit (n + 3) * digit (n + 4) +
      digit n * digit (n + 1) * digit (n + 3) * digit (n + 4) +
      digit n * digit (n + 1) * digit (n + 2) * digit (n + 4) +
      digit n * digit (n + 1) * digit (n + 2) * digit (n + 3) = 274 := by
  have h := Nat.mod_lt n (show 5 > 0 by norm_num)
  have e1 : (n + 1) % 5 = (n % 5 + 1) % 5 := by omega
  have e2 : (n + 2) % 5 = (n % 5 + 2) % 5 := by omega
  have e3 : (n + 3) % 5 = (n % 5 + 3) % 5 := by omega
  have e4 : (n + 4) % 5 = (n % 5 + 4) % 5 := by omega
  unfold digit
  rw [e1, e2, e3, e4]
  interval_cases (n % 5) <;> norm_num

theorem period (n : ℕ) :
    (products (n + 5)).1 = 120 * (products n).1 ∧
    (products (n + 5)).2 = 120 * (products n).2 + 274 * (products n).1 := by
  obtain ⟨h1, h2⟩ := window n
  simp only [step]
  constructor
  · linear_combination (products n).1 * h1
  · linear_combination (products n).2 * h1 + (products n).1 * h2

theorem rec (m : ℕ) : a (m + 10) = 240 * a (m + 5) - 14400 * a m := by
  obtain ⟨p1, e1⟩ := period m
  obtain ⟨p2, e2⟩ := period (m + 5)
  unfold a
  rw [show m + 10 = m + 5 + 5 by ring, e2, e1, p1]
  ring

end PA203166

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a203166.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    rw [PA203166.rec m, show m + 10 - 5 = m + 5 by omega, show m + 10 - 10 = m by omega]
  · ext n
    have hexp : ((1 - C 120 * X ^ 5 : ℤ⟦X⟧)) ^ 2 * mk OMA.S_oeis_a203166.a =
        mk OMA.S_oeis_a203166.a - C 240 * (X ^ 5 * mk OMA.S_oeis_a203166.a) +
          C 14400 * (X ^ 10 * mk OMA.S_oeis_a203166.a) := by
      have hA : (C 240 : ℤ⟦X⟧) = 2 * C 120 := by
        rw [show (240 : ℤ) = 2 * 120 by norm_num, map_mul]; rfl
      have hB : (C 14400 : ℤ⟦X⟧) = C 120 * C 120 := by rw [← map_mul]; norm_num
      rw [hA, hB]
      ring
    rw [hexp]
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge n 10 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      rw [if_pos (by omega), if_pos (by omega), show m + 10 - 5 = m + 5 by omega,
        show m + 10 - 10 = m by omega, PA203166.rec m]
      simp
