import Mathlib

/-!
# A262955: x^4 + triangular number + pentagonal or twice pentagonal number

Source: https://oeis.org/A262955 (Zhi-Wei Sun, 2015)
Credit: @xor2k
Sibling of OEIS A262999 (same conjecture wording); statement modelled on the accepted one for that entry.

A262955(n) is the number of ordered pairs (x, y) with x >= 0 and y > 0 such that
n - x^4 - y*(y+1)/2 is a pentagonal number (A000326) or twice a pentagonal number (offset 1).

Conjecture (as worded in the entry): a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 1, 10, 35, 75, 134, 415, 515, 1465, 2365, 3515, 4140.

Conventions.
- Pentagonal numbers (A000326) are k*(3*k-1)/2 for k >= 0, including 0 = p_5(0), which the
  entry's own example a(1) uses. In Lean `3 * k - 1` truncates only at k = 0, where the product
  is 0 anyway, and the division by 2 is exact.
- The quantity n - x^4 - y*(y+1)/2 must be a (nonnegative) pentagonal number or twice one, so
  we require x^4 + y*(y+1)/2 <= n; under that hypothesis natural subtraction is exact.
- a(n) is the cardinality of the set of such pairs; the set is finite (x^4 <= n and y <= n),
  so `Set.ncard` is the number of pairs.
- As in the template, the second clause is the one-directional reading of a(n) = 1 only for n in
  the list: a(n) = 1 implies that n is in the printed list. The list is taken exactly as printed.
-/

namespace OMA.S_oeis_a262955

/-- `z` is a pentagonal number (A000326): `z = k*(3*k-1)/2` for some `k >= 0`. -/
def IsPentagonal (z : ℕ) : Prop := ∃ k : ℕ, z = k * (3 * k - 1) / 2

/-- The ordered pairs `(x, y)`, `x >= 0`, `y > 0`, such that `n - x^4 - y*(y+1)/2` is a
pentagonal number or twice a pentagonal number. -/
def reps (n : ℕ) : Set (ℕ × ℕ) :=
  {p | 0 < p.2 ∧ p.1 ^ 4 + p.2 * (p.2 + 1) / 2 ≤ n ∧
    (IsPentagonal (n - p.1 ^ 4 - p.2 * (p.2 + 1) / 2) ∨
      ∃ w : ℕ, IsPentagonal w ∧ n - p.1 ^ 4 - p.2 * (p.2 + 1) / 2 = 2 * w)}

/-- A262955(n). -/
noncomputable def a (n : ℕ) : ℕ := (reps n).ncard

/-- Sun's conjecture on A262955, with the exceptional list as printed. -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      ∀ n : ℕ, a n = 1 →
        n ∈ ({1, 10, 35, 75, 134, 415, 515, 1465, 2365, 3515, 4140} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a262955
