import Mathlib

/-!
# OEIS A329203: Numbers k such that A329308(k) = 0

Source: https://oeis.org/A329203
Credit: @unserus

OEIS: "Numbers k such that there is no m < sqrt(k) for which k mod (m^2) is
prime." and "No more terms up to 2*10^7. I conjecture that these are all the
terms."

A329308(n) is the number of `m` with `1 < m < sqrt(n)` (written `m * m < n`)
such that `n mod m^2` is prime, so the terms are the `n ≥ 1` for which no such
`m` exists (`m = 1` never counts, since `n mod 1 = 0`). The sequence starts at
`n = 1`; `n = 0` satisfies the condition vacuously and is excluded. The
conjecture is that the 23 listed terms are all of them.
-/

namespace OMA.S_oeis_a329203

/-- The terms of A329203. -/
def a329203Set : Set ℕ :=
  {n | 1 ≤ n ∧ ∀ m : ℕ, 1 < m → m * m < n → ¬ (n % (m ^ 2)).Prime}

/-- A329203 consists of exactly the 23 listed terms. -/
theorem main :
    a329203Set = {1, 2, 3, 4, 5, 8, 9, 13, 17, 24, 33, 40, 64, 76, 108, 116, 208, 220,
      324, 496, 504, 564, 1176} := by
  sorry

end OMA.S_oeis_a329203
