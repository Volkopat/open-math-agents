import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a092028

/-- `a(n)` (OEIS A092028): the smallest integer `m > 1` such that `m ∣ n ^ m - 1`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1}

/-- Conjectures 1 and 2 (OEIS A092028): for every `n ≥ 3`, `a(n)` is prime and equals
the least prime factor of `n - 1` (A020639(n - 1)). -/
theorem main : ∀ n : ℕ, 3 ≤ n → (a n).Prime ∧ a n = (n - 1).minFac := by
  sorry

end OMA.S_oeis_a092028
