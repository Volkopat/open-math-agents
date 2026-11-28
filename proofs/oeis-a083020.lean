import OMAStatements.S_oeis_a083020
import Mathlib.Data.ZMod.Basic

/-!
OEIS A083020, https://oeis.org/A083020, conjectures that
`3 ^ (3 ^ n) + 2` is squarefree for every natural number `n`.
At `n = 73` the term is divisible by `29 ^ 2`.
-/

namespace OEIS.A083020

theorem repeatedPrimeFactor : 29 * 29 ∣ (3 : ℕ) ^ (3 ^ 73) + 2 := by
  have remainder : (3 : ℕ) ^ 73 % 812 = 31 := by decide
  have exponent : (3 : ℕ) ^ 73 = 812 * (3 ^ 73 / 812) + 31 := by
    calc
      _ = (3 : ℕ) ^ 73 % 812 + 812 * (3 ^ 73 / 812) := (Nat.mod_add_div _ _).symm
      _ = _ := by rw [remainder, Nat.add_comm]
  have period : (3 : ZMod 841) ^ 812 = 1 := by
    rw [show (812 : ℕ) = 29 * 28 by decide, pow_mul,
      show (3 : ZMod 841) ^ 29 = 467 by decide]
    decide
  change 841 ∣ _
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  rw [exponent, pow_add, pow_mul, period, one_pow, one_mul]
  decide

end OEIS.A083020

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a083020.main) := by
  intro h
  exact Nat.squarefree_iff_prime_squarefree.mp (h 73) 29 (by decide)
    OEIS.A083020.repeatedPrimeFactor
