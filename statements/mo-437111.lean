import Mathlib

/-!
# Greatest common divisor of a diagonal of binomial coefficients

Fabius Wiesner asks whether every row indexed by n ≥ 2 has a nontrivial
common divisor. The row index k ranges from 0 through n−1.
Source: https://mathoverflow.net/questions/437111
-/

namespace OMA.S_mo_437111

theorem main : ∀ n : ℕ, 2 ≤ n →
    1 < (Finset.range n).gcd (fun k =>
      (n*(n-1)/2+3+k).choose ((n-1)/2+1+k)) := by
  sorry

end OMA.S_mo_437111
