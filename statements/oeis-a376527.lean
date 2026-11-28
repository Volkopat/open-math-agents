import Mathlib

/-!
# A376527: a(n) = Sum_{k=0..n*(n-1)/2} A227543(n,k)^2 for n >= 0.

Source: https://oeis.org/A376527
Credit: @agchua

Comment of A376527 (unsigned; the entry is by Paul D. Hanna, Oct 11 2024):
  Conjecture: a(n) is odd iff n = 2^k - 1 for some k >= 0.
The sequence has offset 0, so the claim is stated for all n ≥ 0 (k = 0 gives n = 0).
A227543 is the triangle defined by the g.f. A(x,q) = 1 + x*A(q*x,q)*A(x,q), read by terms
k = 0..n*(n-1)/2 in rows n ≥ 0. Comparing the coefficients of x^(n+1) on both sides gives the row
polynomials R(0) = 1 and R(n+1) = Sum_{i=0..n} q^i*R(i)*R(n-i) (this recurrence is also listed in
A227543, from Peter Bala); R n is the row polynomial in q, and A227543(n,k) is its coefficient of q^k.
-/

namespace OMA.S_oeis_a376527

/-- Row polynomials of A227543: R 0 = 1 and R (n+1) = Sum_{i=0..n} q^i * R i * R (n-i). -/
noncomputable def R : ℕ → Polynomial ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin n.succ, Polynomial.X ^ (i : ℕ) * R i * R (n - i)

/-- A227543(n, k): the coefficient of q^k in the row polynomial R n. -/
noncomputable def T (n k : ℕ) : ℕ := (R n).coeff k

/-- A376527(n) = Sum_{k=0..n*(n-1)/2} A227543(n,k)^2. -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n * (n - 1) / 2 + 1), T n k ^ 2

/-- The comment's conjecture: a(n) is odd iff n = 2^k - 1 for some k ≥ 0. -/
theorem main : ∀ n : ℕ, Odd (a n) ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  sorry

end OMA.S_oeis_a376527
