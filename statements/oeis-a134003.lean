import Mathlib

/-!
# A134003: Positive integers n for which n^2+(n+5)^2 is prime.

Source: https://oeis.org/A134003
Credit: @luciusacarr

The entry records the claim: Conjecture. If n is in this sequence then n(n+5)=a(a+5)+b(b+5) is
not solvable in integers. (This has been verified up to n=500.) See A134002 for the complement of
this sequence (in the positive integers).

Reading of the source:
* The terms are the positive integers `n` such that `n^2 + (n+5)^2` is prime.
* "Solvable in integers" is read as in the companion sequence A134002 ("Positive integers n such
  that n(n+5)=a(a+5)+b(b+5) is solvable in positive integers"), which the comment names as the
  complement of this sequence: the unknowns `a`, `b` are positive integers. (With `b = 0` the
  equation always has the trivial solution `a = n`, so the claim is only meaningful for positive
  `a`, `b`.)
* The claim: for every positive integer `n` with `n^2 + (n+5)^2` prime, there are no positive
  integers `a`, `b` with `n(n+5) = a(a+5) + b(b+5)`.
-/

namespace OMA.S_oeis_a134003

theorem main :
    ∀ n : ℕ, 0 < n → (n ^ 2 + (n + 5) ^ 2).Prime →
      ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ n * (n + 5) = a * (a + 5) + b * (b + 5) := by
  sorry

end OMA.S_oeis_a134003
