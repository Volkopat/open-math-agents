import Mathlib

/-!
# OEIS A243847, conjecture (i)

Source: https://oeis.org/A243847
For each `n > 2`, some prime with index `k` between `1` and `n - 1` is a
primitive root both modulo the `n`-th prime and modulo the `(2 * n)`-th prime.
-/

namespace OMA.S_oeis_a243847

-- OEIS counts the first prime at index one.
noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

noncomputable def countCommonPrimitiveRoots (n : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico 1 n).filter fun k =>
    IsPrimitiveRoot (primeAt k : ZMod (primeAt n)) (primeAt n - 1) ∧
    IsPrimitiveRoot (primeAt k : ZMod (primeAt (2 * n))) (primeAt (2 * n) - 1)).card

theorem main : ∀ n : ℕ, 2 < n → 0 < countCommonPrimitiveRoots n := by
  sorry

end OMA.S_oeis_a243847
