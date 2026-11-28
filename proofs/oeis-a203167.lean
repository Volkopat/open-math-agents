import OMAStatements.S_oeis_a203167
import Mathlib

/-!
# A203167: Mathar's recurrence and generating function

The digits repeat with period L, so any L consecutive digits have the same product P and the same
(L−1)-st elementary symmetric function c. Hence (p, e) = products n satisfies p(n+L) = P·p(n) and
e(n+L) = P·e(n) + c·p(n), and eliminating p gives e(n+2L) = 2P·e(n+L) − P²·e(n). Multiplying the
series by (1 − Px^L)² kills every coefficient from x^(2L) on; the first 2L are computed directly.
-/

namespace PA203167
open OMA.S_oeis_a203167

theorem step (n : ℕ) :
    products (n + 1) = ((products n).1 * digit n, (products n).2 * digit n + (products n).1) := by
  rw [products]

theorem window (n : ℕ) :
    digit n * digit (n + 1) * digit (n + 2) = 4 ∧
    digit (n + 1) * digit (n + 2) +
      digit n * digit (n + 2) +
      digit n * digit (n + 1) = 8 := by
  have h := Nat.mod_lt n (show 3 > 0 by norm_num)
  have e1 : (n + 1) % 3 = (n % 3 + 1) % 3 := by omega
  have e2 : (n + 2) % 3 = (n % 3 + 2) % 3 := by omega
  unfold digit
  rw [e1, e2]
  interval_cases (n % 3) <;> norm_num

theorem period (n : ℕ) :
    (products (n + 3)).1 = 4 * (products n).1 ∧
    (products (n + 3)).2 = 4 * (products n).2 + 8 * (products n).1 := by
  obtain ⟨h1, h2⟩ := window n
  simp only [step]
  constructor
  · linear_combination (products n).1 * h1
  · linear_combination (products n).2 * h1 + (products n).1 * h2

theorem rec (m : ℕ) : a (m + 6) = 8 * a (m + 3) - 16 * a m := by
  obtain ⟨p1, e1⟩ := period m
  obtain ⟨p2, e2⟩ := period (m + 3)
  unfold a
  rw [show m + 6 = m + 3 + 3 by ring, e2, e1, p1]
  ring

end PA203167

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a203167.main := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [PA203167.rec m, show m + 6 - 3 = m + 3 by omega, show m + 6 - 6 = m by omega]
  · ext n
    have hexp : ((1 - C 4 * X ^ 3 : ℤ⟦X⟧)) ^ 2 * mk OMA.S_oeis_a203167.a =
        mk OMA.S_oeis_a203167.a - C 8 * (X ^ 3 * mk OMA.S_oeis_a203167.a) +
          C 16 * (X ^ 6 * mk OMA.S_oeis_a203167.a) := by
      have hA : (C 8 : ℤ⟦X⟧) = 2 * C 4 := by
        rw [show (8 : ℤ) = 2 * 4 by norm_num, map_mul]; rfl
      have hB : (C 16 : ℤ⟦X⟧) = C 4 * C 4 := by rw [← map_mul]; norm_num
      rw [hA, hB]
      ring
    rw [hexp]
    simp only [map_sub, map_add, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
    rcases Nat.lt_or_ge n 6 with hn | hn
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
      rw [if_pos (by omega), if_pos (by omega), show m + 6 - 3 = m + 3 by omega,
        show m + 6 - 6 = m by omega, PA203167.rec m]
      simp
