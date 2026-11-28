import Mathlib

/-!
# A390107: least m with m*(n-1) + 1 coprime to C(m*n^2, m*n)

Source: https://oeis.org/A390107

A390107 (offset 1): `a(n)` is the least positive integer `m` such that `m*(n-1) + 1` is
relatively prime to `C(m*n^2, m*n)`, where `C(k, j)` denotes the binomial coefficient:
1, 2, 2, 2, 2, 2, 2, 4, 2, 2, …  For example `a(3) = 2` with `2*(3-1) + 1 = 5` relatively prime
to `C(2*3^2, 2*3) = 18564`.

Conjecture (Zhi-Wei Sun, Oct 25 2025): `a(n) ≤ sqrt(3*n + 4)` for all `n > 0`. The entry notes
that this has been verified for `n ≤ 30000`.

Since `a(n)` is the least positive `m` with `m*(n-1) + 1` coprime to `C(m*n^2, m*n)`, the bound
`a(n) ≤ sqrt(3n + 4)` holds exactly when some such `m` satisfies `m^2 ≤ 3n + 4`, and the
conjecture is stated in that form.

Conventions: everything is in `ℕ`; `n - 1` is an exact subtraction for `n > 0`, and the real
inequality `m ≤ sqrt(3n+4)` is written as `m^2 ≤ 3*n + 4`.
-/

namespace OMA.S_oeis_a390107

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ m : ℕ, 0 < m ∧ m ^ 2 ≤ 3 * n + 4 ∧
        Nat.Coprime (m * (n - 1) + 1) ((m * n ^ 2).choose (m * n)) := by
  sorry

end OMA.S_oeis_a390107
