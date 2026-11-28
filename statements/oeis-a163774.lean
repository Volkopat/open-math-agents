import Mathlib

/-!
# A163774: Row sums of the central coefficients triangle (A163771).

Source: https://oeis.org/A163774
Credit: @jagong-cmu

Definition in the entry: a(n) = Sum_{k=0..n} Sum_{i=k..n} (-1)^(n-i)*binomial(n-k,n-i)*(2i)$,
where i$ denotes the swinging factorial of i (A056040). The inner sum is the entry T(n,k) of
the triangle A163771, so a(n) is the n-th row sum of A163771.

The entry gives (Werner Schulte, Nov 17 2015):
Conjecture: a(n) = Sum_{k=0..n} (-1)^(n-k)*binomial(n+1,k)*binomial(2*k,k).

Conventions:
* Offset 0, as in the entry (data: 1, 3, 13, 51, 201, 783, ...).
* The swinging factorial is n$ = n! / floor(n/2)!^2 (A056040), as in the Mathematica program
  of the entry. The division on `ℕ` is exact.
* In both sums the index `i` (or `k`) is at most `n`, so the exponents `n - i` and `n - k` and
  the arguments `n - k`, `n - i` are the usual differences.
* The sums are computed in `ℤ`. The claim is stated for every `n ≥ 0`.
-/

namespace OMA.S_oeis_a163774

/-- The swinging factorial `n$ = n! / floor(n/2)!^2` (A056040). -/
def swing (n : ℕ) : ℕ := n.factorial / (n / 2).factorial ^ 2

/-- The triangle A163771: `T(n,k) = Sum_{i=k..n} (-1)^(n-i)*binomial(n-k,n-i)*(2i)$`. -/
def T (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc k n, (-1) ^ (n - i) * ((n - k).choose (n - i) : ℤ) * (swing (2 * i) : ℤ)

/-- A163774: the row sums of A163771. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k

/-- `a(n) = Sum_{k=0..n} (-1)^(n-k)*binomial(n+1,k)*binomial(2*k,k)` for every `n ≥ 0`. -/
theorem main :
    ∀ n : ℕ, a n = ∑ k ∈ Finset.range (n + 1),
      (-1) ^ (n - k) * ((n + 1).choose k : ℤ) * ((2 * k).choose k : ℤ) := by
  sorry

end OMA.S_oeis_a163774
