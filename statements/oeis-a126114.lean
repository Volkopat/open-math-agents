import Mathlib

/-!
# A126114: Ultimate fixed-point under the mapping n->f(n), where f(n)=n if n is square else f(n)=n-Floor(Sqrt(n)).

Source: https://oeis.org/A126114
Credit: @agchua

Formula line of A126114 (unsigned; the entry is by John W. Layman, Mar 05 2007):
  Conjecture. Let t(k) be the largest triangular number t(k)=k(k+1)/2 such that 2t(k) is
  smaller than n and denote n-2t(k) by X. Then a(n)=X^2 if X<=k+1, else a(n)=(X-k-1)^2.
  (This has been verified for n=1,2,3,...,1000.)
The sequence has offset 1, so the claim is stated for n ≥ 1. Since t is strictly increasing
and 2t(0) = 0 < n, the largest k with 2t(k) < n is the unique k with 2t(k) < n ≤ 2t(k+1);
the statement quantifies over that k. Then X = n - 2t(k) ≥ 1, and in the second case
X > k+1, so the natural-number subtractions are exact. The ultimate fixed point of n is the
value v at which the orbit n, f(n), f(f(n)), ... becomes constant: f^[i] n = v for all large i
(such a v is a fixed point of f, and it is unique when it exists).
-/

namespace OMA.S_oeis_a126114

/-- The map of A126114: f(n) = n if n is a square, else n - floor(sqrt(n)). -/
def f (n : ℕ) : ℕ := if IsSquare n then n else n - Nat.sqrt n

/-- The triangular number t(k) = k(k+1)/2. -/
def t (k : ℕ) : ℕ := k * (k + 1) / 2

/-- The conjecture: for n ≥ 1 and the largest k with 2t(k) < n, the orbit of n under f
becomes constant at X^2 if X ≤ k+1 and at (X-k-1)^2 otherwise, where X = n - 2t(k). -/
theorem main : ∀ n k : ℕ, 1 ≤ n → 2 * t k < n → n ≤ 2 * t (k + 1) →
    ∃ j : ℕ, ∀ i : ℕ, j ≤ i → f^[i] n =
      if n - 2 * t k ≤ k + 1 then (n - 2 * t k) ^ 2 else (n - 2 * t k - k - 1) ^ 2 := by
  sorry

end OMA.S_oeis_a126114
