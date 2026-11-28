import Mathlib

/-!
# A151819: First component x of pairs (x,y) where x!+y! is a square, sorted on x.

Source: https://oeis.org/A151819
Credit: @prasledi

Conjecture (in the COMMENTS of A151819): the only solutions for x!+y!=n^2 are
x=0,0,0,1,1,1,2,4,4,4 and y=4,5,7,4,5,7,2,0,1,5 respectively.

Formalization notes:
* x, y, n are natural numbers (0! = 1, as in the listed solutions with x = 0).
* The listed pairs are not closed under swapping: (4,0) and (4,1) are listed together with
  (0,4) and (1,4), but (5,0), (5,1), (7,0), (7,1) and (5,4) are not listed although they are
  solutions too (for example 5! + 0! = 121 = 11^2 and 5! + 4! = 144 = 12^2). Since
  x! + y! is symmetric in x and y, the content of the conjecture is about unordered pairs,
  so it is stated for x <= y. The pairs of the list with x <= y are exactly
  (0,4), (0,5), (0,7), (1,4), (1,5), (1,7), (2,2), (4,5); the remaining listed pairs (4,0)
  and (4,1) are swaps of (0,4) and (1,4).
* A brute-force search confirms that these are all solutions with x <= y < 40.
-/

namespace OMA.S_oeis_a151819

/-- The conjecture of A151819: if `x ≤ y` and `x! + y!` is a perfect square, then `(x, y)` is
one of the eight listed pairs. -/
theorem main :
    ∀ x y n : ℕ, x ≤ y → Nat.factorial x + Nat.factorial y = n ^ 2 →
      (x, y) ∈ ({(0, 4), (0, 5), (0, 7), (1, 4), (1, 5), (1, 7), (2, 2), (4, 5)} :
        Finset (ℕ × ℕ)) := by
  sorry

end OMA.S_oeis_a151819
