import Mathlib

/-!
# A390762: Number of ways to write n as (p-1)^2 + (q-1)^2 + (r-1)^2/2 + (s-1)^2/4 with p <= q, where each of p,q,r,s is either 1 or an odd prime

Source: https://oeis.org/A390762
Credit: @gblacher2

Conjecture (Zhi-Wei Sun, in the comments of A390762): let S = {(p-1)/2 : p is 1 or an odd prime}.
Then each nonnegative integer n can be written as w^2 + b*x^2 + c*y^2 + d*z^2 with w, x, y, z in S,
provided that (b,c,d) is among the following 25 triples:
(1,2,3), (1,2,4), (1,2,5), (1,2,6), (1,2,7), (1,2,12), (1,3,5), (1,3,6), (2,2,3), (2,2,5),
(2,3,3), (2,3,4), (2,3,5), (2,3,7), (2,3,9), (2,3,10), (2,4,4), (2,4,5), (2,4,9), (2,4,10),
(2,4,11), (2,4,12), (2,5,7), (2,5,8), (2,5,9).

The source notes that the case (b,c,d) = (2,4,4) holds if and only if a(n) > 0 for all n >= 0,
verified for n <= 10^6.

Formalization notes:
* The statement below is the full conjecture of the source, for all 25 triples; it is not
  restricted to the case (2,4,4).
* For p = 1 or p an odd prime, (p - 1) / 2 is an exact division in `ℕ`; S contains 0 (from p = 1).
* "Nonnegative integer" is `n : ℕ`, including n = 0.
* Check of the reading: counting (p,q,r,s) with p <= q, each 1 or an odd prime, and
  n = (p-1)^2 + (q-1)^2 + (r-1)^2/2 + (s-1)^2/4, reproduces the b-file of A390762 for
  n = 0..10000. Every n <= 20000 has a representation for each of the 25 triples.
-/

namespace OMA.S_oeis_a390762

/-- `p` is 1 or an odd prime. -/
def OneOrOddPrime (p : ℕ) : Prop :=
  p = 1 ∨ (p.Prime ∧ Odd p)

/-- The set `S = {(p-1)/2 : p is 1 or an odd prime}` of A390762. -/
def InS (w : ℕ) : Prop :=
  ∃ p : ℕ, OneOrOddPrime p ∧ w = (p - 1) / 2

/-- The 25 triples `(b, c, d)` listed in the conjecture of A390762. -/
def triples : List (ℕ × ℕ × ℕ) :=
  [(1, 2, 3), (1, 2, 4), (1, 2, 5), (1, 2, 6), (1, 2, 7), (1, 2, 12), (1, 3, 5), (1, 3, 6),
    (2, 2, 3), (2, 2, 5), (2, 3, 3), (2, 3, 4), (2, 3, 5), (2, 3, 7), (2, 3, 9), (2, 3, 10),
    (2, 4, 4), (2, 4, 5), (2, 4, 9), (2, 4, 10), (2, 4, 11), (2, 4, 12), (2, 5, 7), (2, 5, 8),
    (2, 5, 9)]

/-- Sun's conjecture on A390762: for each of the 25 listed triples `(b, c, d)`, every
nonnegative integer `n` is `w^2 + b*x^2 + c*y^2 + d*z^2` with `w, x, y, z ∈ S`. -/
theorem main : ∀ b c d : ℕ, (b, c, d) ∈ triples → ∀ n : ℕ, ∃ w x y z : ℕ,
    InS w ∧ InS x ∧ InS y ∧ InS z ∧ n = w ^ 2 + b * x ^ 2 + c * y ^ 2 + d * z ^ 2 := by
  sorry

end OMA.S_oeis_a390762
