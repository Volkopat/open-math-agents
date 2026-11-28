import Mathlib

/-!
# A105752: Expansion of e.g.f. cos(i*log(1 + x)), i = sqrt(-1).

Source: https://oeis.org/A105752
Credit: @xor2k

Formalizes the OEIS A105752 conjecture (Benedict W. J. Irwin, Oct 19 2016):
a(n) = Sum_{k=0..n} Stirling1(n, 2*k), with Stirling1 the signed Stirling numbers of the first kind.

Conventions:
* A105752 has offset 0, so the claim is stated for all n : ℕ;
* the e.g.f. is cos(i*log(1+x)) = cosh(log(1+x)) = ((1+x) + 1/(1+x))/2 (as in the entry),
  whose x^n coefficient is ([n = 0] + [n = 1] + (-1)^n)/2, so a(n) = n! * ([n ≤ 1] + (-1)^n)/2;
  this is the definition of a below, valued in ℤ;
* Stirling1(n, k) (signed, A048994, offset 0) is (-1)^(n-k) * Nat.stirlingFirst n k, where
  Nat.stirlingFirst is Mathlib's unsigned Stirling number of the first kind (A132393);
* the natural subtraction n - 2*k truncates only when 2*k > n, where Nat.stirlingFirst n (2*k) = 0,
  so the term is 0 either way; / is Int division, and it is exact here since the numerator is even.
-/

namespace OMA.S_oeis_a105752

/-- A105752: n! times the x^n coefficient of ((1+x) + 1/(1+x))/2 = cos(i*log(1+x)). -/
def a (n : ℕ) : ℤ :=
  (n.factorial : ℤ) * ((if n ≤ 1 then 1 else 0) + (-1) ^ n) / 2

/-- The signed Stirling number of the first kind s(n, k). -/
def stirling1 (n k : ℕ) : ℤ :=
  (-1) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

/-- a(n) is the sum of the signed Stirling numbers s(n, 2*k) for k = 0..n. -/
theorem main :
    ∀ n : ℕ, a n = ∑ k ∈ Finset.range (n + 1), stirling1 n (2 * k) := by
  sorry

end OMA.S_oeis_a105752
