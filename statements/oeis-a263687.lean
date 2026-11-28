import Mathlib

/-!
# A263687: b(n) in (sqrt(2))_n = b(n) + c(n)*sqrt(2)

Source: https://oeis.org/A263687 (conjecture by Benedict W. J. Irwin, Oct 14 2016)

Conjecture: a(n) = (-1)^n * Sum_{k=0..n/2} Stirling1(n,2*k)*2^k.

Conventions:
* The Pochhammer symbol (sqrt(2))_n = sqrt(2)*(1 + sqrt(2))*...*(n - 1 + sqrt(2)) is computed
  in the ring `ℤ√2` of numbers b + c*sqrt(2) with b, c integers (`Zsqrtd 2`, where
  `Zsqrtd.sqrtd` is sqrt(2)); since sqrt(2) is irrational, the integers b(n), c(n) are its
  components, and a(n) = b(n) is the real part `re` (offset 0; the empty product is 1).
* `Stirling1 n k` is the signed Stirling number of the first kind (as in the entry, e.g.
  Mathematica's StirlingS1), namely `(-1)^(n-k)` times the unsigned Stirling number
  `Nat.stirlingFirst n k` (the number of permutations of n elements with k cycles).
* The sum over k = 0..n/2 uses floor division, i.e. `Finset.range (n / 2 + 1)`.
* The statement is the identity for every n >= 0, in the integers.
-/

namespace OMA.S_oeis_a263687

/-- The Pochhammer symbol (sqrt(2))_n in `ℤ√2`. -/
def poch (n : ℕ) : ℤ√2 := ∏ i ∈ Finset.range n, (Zsqrtd.sqrtd + (i : ℤ√2))

/-- A263687(n): the rational part b(n) of (sqrt(2))_n = b(n) + c(n)*sqrt(2). -/
def a (n : ℕ) : ℤ := (poch n).re

/-- The signed Stirling number of the first kind. -/
def Stirling1 (n k : ℕ) : ℤ := (-1) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)

theorem main : ∀ n : ℕ,
    a n = (-1) ^ n * ∑ k ∈ Finset.range (n / 2 + 1), Stirling1 n (2 * k) * 2 ^ k := by
  sorry

end OMA.S_oeis_a263687
