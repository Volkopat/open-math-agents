import OMAStatements.S_oeis_a263326
import Mathlib

-- Counterexample of T. Adamczewski (OEIS Open, arXiv:2608.11941, Appendix A; recorded in OEIS A263326):
-- for k = 31, s = 1 the sums at n = 5 and n = 1829 = 31 * 59 coincide:
-- 1/32 + 1/36 = 17/288 = 1/32 + 1/62 + 1/90 + 1/1860, so the fractional parts are not distinct.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a263326.main) := by
  intro h
  have hinj := (h 31 1 (by norm_num) (by norm_num)).1
  have d5 : Nat.divisors 5 = {1, 5} := by decide
  have d1829 : Nat.divisors 1829 = {1, 31, 59, 1829} := by decide +kernel
  have e5 : OMA.S_oeis_a263326.shiftedDivisorSum 31 1 5 = 17 / 288 := by
    rw [OMA.S_oeis_a263326.shiftedDivisorSum, d5]
    norm_num
  have e1829 : OMA.S_oeis_a263326.shiftedDivisorSum 31 1 1829 = 17 / 288 := by
    rw [OMA.S_oeis_a263326.shiftedDivisorSum, d1829]
    norm_num
  have heq : (fun n : ℕ => Int.fract (OMA.S_oeis_a263326.shiftedDivisorSum 31 1 n)) 5 =
      (fun n : ℕ => Int.fract (OMA.S_oeis_a263326.shiftedDivisorSum 31 1 n)) 1829 := by
    simp only [e5, e1829]
  have := hinj (show (5 : ℕ) ∈ Set.Ioi 0 by norm_num) (show (1829 : ℕ) ∈ Set.Ioi 0 by norm_num) heq
  norm_num at this
