import Mathlib

/-!
# A134558: Array read by antidiagonals, a(n,k) = gamma(n+1,k)*e^k, where gamma(n,k) is the upper incomplete gamma function and e is the exponential constant 2.71828...

Source: https://oeis.org/A134558
Credit: @agchua

Formula line of A134558 (unsigned; the entry is by Ross La Haye, Jan 22 2008), verbatim:
  Conjecture: a(n,k) is the permanent of the n X n matrix with k+1 on the main diagonal and 1
  elsewhere.
Offset 0: rows n >= 0 and columns k >= 0 (a(0,k) = 1, a(1,k) = k + 1, a(n,0) = n!).
The first formula line of the entry gives the array in closed form,
  a(n,k) = gamma(n+1,k)*e^k = Sum_{m=0..n} m!*binomial(n,m)*k^(n-m),
and that finite sum is the definition used here (the upper incomplete gamma function is not in
Mathlib; for natural n, gamma(n+1,k) = n! e^(-k) Sum_{j=0..n} k^j/j!, which gives the same values).
The matrix is indexed by Fin n; for n = 0 the permanent of the empty matrix is 1 = a(0,k).
-/

namespace OMA.S_oeis_a134558

/-- A134558 as an array: a(n,k) = Sum_{m=0..n} m! * binomial(n,m) * k^(n-m). -/
def a (n k : ℕ) : ℕ := ∑ m ∈ Finset.range (n + 1), m.factorial * n.choose m * k ^ (n - m)

/-- The n X n matrix with k+1 on the main diagonal and 1 elsewhere. -/
def M (n k : ℕ) : Matrix (Fin n) (Fin n) ℕ := Matrix.of fun i j => if i = j then k + 1 else 1

/-- For all n, k >= 0, a(n,k) is the permanent of the n X n matrix M(n,k). -/
theorem main : ∀ n k : ℕ, (M n k).permanent = a n k := by
  sorry

end OMA.S_oeis_a134558