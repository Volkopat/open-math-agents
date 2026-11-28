import Mathlib

/-!
# A223174: Smallest prime p such that 2n+1 = p + 8*q for some odd prime q, or 0 if no such prime exists.

Source: https://oeis.org/A223174
Credit: @prasledi

Conjecture (in the COMMENTS of A223174): except m = 25 and 49, all odd numbers > 17 are of the
form m = p + 8*q where p and q are prime numbers.

Formalization notes:
* The conjecture is stated exactly as written in the comment: p and q are arbitrary primes.
  The sequence name says odd prime q, but the comments list the corresponding q values and
  they include q = 2 (for example 2*9 + 1 = 19 = 3 + 8*2), and the conjecture itself only
  says that p and q are prime numbers.
* m = 25 and m = 49 are the two exceptions above 17 in the data (a(12) = a(24) = 0). A
  brute-force search confirms that every other odd m with 17 < m < 40000 has such a
  representation.
-/

namespace OMA.S_oeis_a223174

/-- The conjecture of A223174: every odd `m > 17` other than `25` and `49` is `p + 8q` with
`p`, `q` prime. -/
theorem main :
    ∀ m : ℕ, Odd m → 17 < m → m ≠ 25 → m ≠ 49 →
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p + 8 * q := by
  sorry

end OMA.S_oeis_a223174
