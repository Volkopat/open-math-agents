import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a078251

/-- The number whose decimal expansion consists of `k` repetitions of the decimal expansion of `n`,
i.e., `n * ∑_{j=0}^{k-1} (10^d)^j` where `d = (Nat.digits 10 n).length`. -/
def repConcat (n k : ℕ) : ℕ :=
  n * ∑ j ∈ Finset.range k, (10 ^ (Nat.digits 10 n).length) ^ j

/-- `a(n)` (OEIS A078251): the smallest positive multiple of the `n`-th prime (`1`-indexed,
so `Nat.nth Nat.Prime (n - 1)`) whose decimal expansion is `nnn...n`, or `0` if none exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  letI := Classical.propDecidable
  let p := Nat.nth Nat.Prime (n - 1)
  if _h : ∃ k : ℕ, 0 < k ∧ p ∣ repConcat n k then
    repConcat n (sInf {k : ℕ | 0 < k ∧ p ∣ repConcat n k})
  else 0

/-- Conjecture (OEIS A078251): no entry `a(n)` is zero for `n > 3`. -/
theorem main : ∀ n : ℕ, 3 < n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a078251
