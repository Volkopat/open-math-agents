import Mathlib

/-!
# A188648: Binomial sums a(n) = Sum_{k=0..n} (binomial(2n-k,k))^2.

Source: https://oeis.org/A188648
Credit: @agchua

Formula line of A188648, by Velin Yanev, Oct 31 2019:
  Conjecture: a(n) = hypergeom([-n,-n,n+1,n+1], [1/2,1/2,1], 1/16).
A188648 has offset 0, and the claim is stated for every n >= 0.
hypergeom([a1,a2,a3,a4], [b1,b2,b3], z) is the generalized hypergeometric series
Sum_{k>=0} (a1)_k (a2)_k (a3)_k (a4)_k / ((b1)_k (b2)_k (b3)_k) * z^k / k!, where (x)_k is the
rising factorial x (x+1) ... (x+k-1), Mathlib's `ascPochhammer` evaluated at x. `term n k` is
its k-th term for a1 = a2 = -n, a3 = a4 = n+1, b1 = b2 = 1/2, b3 = 1 and z = 1/16; no
denominator vanishes. Since (-n)_k = 0 for k > n the series terminates, and the claim is that
it sums to a(n).
-/

namespace OMA.S_oeis_a188648

/-- A188648(n) = Sum_{k=0..n} binomial(2n-k, k)^2. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n - k) k) ^ 2

/-- The k-th term of the series hypergeom([-n,-n,n+1,n+1], [1/2,1/2,1], 1/16). -/
noncomputable def term (n k : ℕ) : ℚ :=
  (ascPochhammer ℚ k).eval (-(n : ℚ)) * (ascPochhammer ℚ k).eval (-(n : ℚ)) *
      (ascPochhammer ℚ k).eval ((n : ℚ) + 1) * (ascPochhammer ℚ k).eval ((n : ℚ) + 1) /
    ((ascPochhammer ℚ k).eval (1 / 2) * (ascPochhammer ℚ k).eval (1 / 2) *
      (ascPochhammer ℚ k).eval 1) * (1 / 16) ^ k / (k.factorial : ℚ)

/-- The conjecture: the series hypergeom([-n,-n,n+1,n+1], [1/2,1/2,1], 1/16) sums to a(n),
for every n >= 0. -/
theorem main : ∀ n : ℕ, HasSum (fun k : ℕ => term n k) (a n : ℚ) := by
  sorry

end OMA.S_oeis_a188648
