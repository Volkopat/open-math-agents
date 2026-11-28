import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Order.Interval.Finset.Nat

/-! Source: https://mathoverflow.net/questions/496220
Sequence: https://oeis.org/A381299 -/

open scoped BigOperators

namespace OMA.S_mo_496220

/-- The weight sum for weakly increasing choices from the given interval. -/
noncomputable def block : ℕ → ℕ → ℕ → Polynomial ℤ
  | 0, _, _ => 1
  | m + 1, lo, hi => ∑ j ∈ Finset.Icc lo hi, Polynomial.X ^ j * block m j hi

/-- For the first block of size m, let s_i be its increasing zero-based indices.
The shifts s_i - i count the smaller elements in later blocks. The values of
these shifts are weakly increasing and at most n - m. Relabel the remaining
elements in increasing order to enumerate the rest of the ordered partition. -/
noncomputable def ordered : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => ∑ i ∈ Finset.range (n + 1), block (i + 1) 0 (n - i) * ordered (n - i)
termination_by n => n

noncomputable def R : ℕ → ℕ → Polynomial ℤ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, k => if k = n + 1 then 1 else if n + 1 < k then 0 else
      Polynomial.X ^ k * (2 * (∑ j ∈ Finset.range (n + 1), R n j) - 1 -
        ∑ j ∈ Finset.range k, R n j)

theorem main : ∀ n : ℕ, 0 < n → R (n + 1) 0 + 1 = 4 * ordered n := by
  sorry

end OMA.S_mo_496220
