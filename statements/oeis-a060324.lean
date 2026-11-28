import Mathlib

/-!
# A060324: a(n) is the minimal prime q such that n*(q+1)-1 is prime.

Source: https://oeis.org/A060324
Credit: @gblacher2

The OEIS name is: "a(n) is the minimal prime q such that n*(q+1)-1 is prime, that is, the
smallest prime q so that n = (p+1)/(q+1) with p prime; or a(n) = -1 if no such q exists."

Open problem (comment in A060324): "A conjecture of Schinzel, if true, would imply that such a
q always exists." We state the open claim itself: for every `n` in the range of the sequence,
a prime `q` with `n * (q + 1) - 1` prime exists, so the value `-1` never occurs.

Conventions:
* the offset of A060324 is 1, so `n` ranges over the positive integers;
* for `n ≥ 1` and a prime `q ≥ 2` we have `n * (q + 1) ≥ 3`, so the subtraction
  `n * (q + 1) - 1` in `ℕ` is the integer subtraction of the source.
-/

namespace OMA.S_oeis_a060324

/-- The defining property of `a(n)`: `q` is a prime and `n * (q + 1) - 1` is prime. -/
def Good (n q : ℕ) : Prop :=
  q.Prime ∧ (n * (q + 1) - 1).Prime

/-- The conjecture: for every positive integer `n` there is a prime `q` such that
`n * (q + 1) - 1` is prime, so `a(n)` is always a prime and never `-1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ q : ℕ, Good n q := by
  sorry

end OMA.S_oeis_a060324
