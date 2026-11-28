import Mathlib

/-!
# A390818: Number of ways to write n as 3*((p-1)/2)^4 + (q-1)^2/2 + (r-1)^2/4 + s^2, where each of p,q,r is either 1 or an odd prime, and s is half of a practical number

Source: https://oeis.org/A390818
Credit: @gblacher2

Conjectures of Zhi-Wei Sun (Nov 20 2025), in the comments of A390818; both have been verified
for n <= 2*10^5:
* Conjecture 1: a(n) > 0 for all n > 0, i.e. every positive integer n can be written as
  3*((p-1)/2)^4 + (q-1)^2/2 + (r-1)^2/4 + s^2, where each of p, q, r is either 1 or an odd prime,
  and s is half of a practical number.
* Conjecture 2 ("the following similar conjecture"): each natural number n can be written as
  3*u^4 + v^2 + (p-1)^2/2 + (q-1)^2/4, where each of u and v is either zero or half of an even
  practical number, and each of p and q is either 1 or an odd prime.
`main` states both conjectures, as a conjunction.

Conventions:
* A practical number is a positive integer n such that every m with m <= n is a sum of distinct
  divisors of n (Srinivasan's definition, A005153: 1, 2, 4, 6, 8, 12, ...).
* In Conjecture 1, s is a natural number with 2*s practical (so s >= 1), as in the Mathematica
  program of A390818 (`qq[n] = IntegerQ[n] && pr[2n]`). The halves of the practical number 1 are
  not integers, so they do not matter here.
* "Half of an even practical number" is likewise a natural number u >= 1 with 2*u practical.
* For p = 1 or p an odd prime, the divisions (p-1)/2, (p-1)^2/2 and (p-1)^2/4 are exact.
* "Natural number" in Conjecture 2 includes 0.
-/

namespace OMA.S_oeis_a390818

/-- `n` is a practical number: `n > 0` and every `m <= n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- `p` is either 1 or an odd prime. -/
def IsOneOrOddPrime (p : ℕ) : Prop :=
  p = 1 ∨ (p.Prime ∧ Odd p)

/-- Sun's Conjectures 1 and 2 on A390818. -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ p q r s : ℕ, IsOneOrOddPrime p ∧ IsOneOrOddPrime q ∧
      IsOneOrOddPrime r ∧ IsPractical (2 * s) ∧
      n = 3 * ((p - 1) / 2) ^ 4 + (q - 1) ^ 2 / 2 + (r - 1) ^ 2 / 4 + s ^ 2) ∧
    (∀ n : ℕ, ∃ u v p q : ℕ, (u = 0 ∨ IsPractical (2 * u)) ∧ (v = 0 ∨ IsPractical (2 * v)) ∧
      IsOneOrOddPrime p ∧ IsOneOrOddPrime q ∧
      n = 3 * u ^ 4 + v ^ 2 + (p - 1) ^ 2 / 2 + (q - 1) ^ 2 / 4) := by
  sorry

end OMA.S_oeis_a390818
