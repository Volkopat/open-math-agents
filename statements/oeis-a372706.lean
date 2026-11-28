import Mathlib

/-!
# A372706: a(n) = Sum_{k=1..n} mu(n*k), where mu is the Moebius function A008683.

Source: https://oeis.org/A372706
Credit: @JeremyDevs

Formalizes the identity recorded as a conjecture in OEIS A372706 (Jamie Morken, Sep 15 2026):
a(n) = A008683(n) * A112399(n).
The entry notes (Peter Bala, Sep 22 2026) that the conjecture is correct, so this is a known
result; the statement below is its Lean form.

Conventions (both sequences have offset 1 and integer terms):
* A372706: a(n) = Sum_{k=1..n} mu(n*k).
* A008683 is the Moebius function mu, Mathlib's `ArithmeticFunction.moebius`.
* A112399(n) = Sum_{k=1..n, gcd(k,n)=1} mu(k). It is the function `c` below.
* The identity is asserted for every `n ≥ 1`, the range of the offset-1 sequences.
-/

namespace OMA.S_oeis_a372706

open ArithmeticFunction

/-- A372706: a(n) = Sum_{k=1..n} mu(n*k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, moebius (n * k)

/-- A112399: c(n) = Sum_{k=1..n, gcd(k,n)=1} mu(k). -/
def c (n : ℕ) : ℤ := ∑ k ∈ (Finset.Icc 1 n).filter (fun k => Nat.gcd k n = 1), moebius k

/-- For every `n ≥ 1`, A372706(n) = mu(n) * A112399(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = moebius n * c n := by
  sorry

end OMA.S_oeis_a372706
