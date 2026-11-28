import Mathlib

/-!
# A280258: a(n) = Sum_{d|n} pxi(d), where pxi(m) is the product of totatives of m

Source: https://oeis.org/A280258 (conjecture in the comments of the entry)

Conjecture: a(n) is odd for numbers in A183300; a(n) is even for numbers in A001105 (2*n^2).

Conventions:
* `pxi m` (A001783) is the product of the totatives of m, i.e. of the k with 1 <= k <= m and
  gcd(k, m) = 1 (so pxi(1) = 1).
* `a n` (offset 1) is the sum of pxi(d) over the divisors d of n.
* A183300 is the sequence of positive integers not of the form 2k^2, and A001105 lists the
  numbers 2k^2; for n >= 1 the statement says: if n is not of the form 2k^2 then a(n) is odd,
  and if n = 2k^2 then a(n) is even.
-/

namespace OMA.S_oeis_a280258

/-- A001783: the product of the totatives of m. -/
def pxi (m : ℕ) : ℕ := ∏ k ∈ (Finset.Icc 1 m).filter (fun k => Nat.Coprime k m), k

/-- A280258(n) = Sum_{d|n} pxi(d). -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, pxi d

theorem main : ∀ n : ℕ, 1 ≤ n →
    ((¬ ∃ k : ℕ, n = 2 * k ^ 2) → Odd (a n)) ∧ ((∃ k : ℕ, n = 2 * k ^ 2) → Even (a n)) := by
  sorry

end OMA.S_oeis_a280258
