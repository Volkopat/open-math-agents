import Mathlib

/-!
# A142248: Odd numbers in A138123.

Source: https://oeis.org/A142248 (and https://oeis.org/A138123)
Credit: @bnb9001

A138123 (offset 1): antidiagonal sums of the sparse triangle T(p,p) = A000204(p) (Lucas numbers),
T(p,2p) = (-1)^(p+1), T(p,m) = 0 otherwise, i.e. a(n) = Sum_{m=1..n} T(1+n-m, m), as in the PARI
program of A142248: 1, 1, 3, 0, 3, 0, 7, 1, 11, 0, 17, ... A142248 (offset 1) lists the odd numbers
occurring in A138123 in increasing order (the PARI program collects the positive odd sums into a
set): 1, 3, 7, 11, 17, 29, 47, 75, 123, ...

Conjecture (Chai Wah Wu, Apr 15 2024): a(n) = a(n-1) + a(n-2) + a(n-3) - a(n-4) - a(n-5) for n > 6.
(The conjectured g.f. in the entry is equivalent to this recurrence together with the initial terms.)
-/

namespace OMA.S_oeis_a142248

/-- The Lucas numbers `L(n) = F(n+1) + F(n-1)` (A000204), as in the PARI program of the entry. -/
def L (n : ℕ) : ℕ := Nat.fib (n + 1) + Nat.fib (n - 1)

/-- The sparse triangle of A138123: `T(p,p) = L(p)`, `T(p,2p) = (-1)^(p+1)`, and `T(p,m) = 0`
otherwise. -/
def T (p m : ℕ) : ℤ :=
  if m = p then (L p : ℤ) else if m = 2 * p then (-1) ^ (p + 1) else 0

/-- A138123 (offset 1): antidiagonal sums `a(n) = Sum_{m=1..n} T(1+n-m, m)`. -/
def A138123 (n : ℕ) : ℤ := ∑ m ∈ Finset.Icc 1 n, T (n + 1 - m) m

/-- The odd numbers occurring in A138123. -/
def IsTerm (v : ℕ) : Prop := Odd v ∧ ∃ n, 1 ≤ n ∧ A138123 n = v

/-- A142248 (offset 1): the odd numbers in A138123, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

theorem main : ∀ n : ℕ, 6 < n →
    (a n : ℤ) = a (n - 1) + a (n - 2) + a (n - 3) - a (n - 4) - a (n - 5) := by
  sorry

end OMA.S_oeis_a142248
