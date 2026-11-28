import Mathlib

/-!
# A230148: Numbers whose abundancy, sigma(n)/n, is 1024/513.

Source: https://oeis.org/A230148
Credit: @keiichisince1986-bot

A230148 lists the numbers `n` with `σ(n)/n = 1024/513`, where `σ(n)` is the sum of the divisors
of `n`:
`397575, 3145425129, 7096702977, 53164445037705, 130468907286855, 1229923663366167,`
`2774951736355071`.
The entry states: This list of 7 numbers is conjectured to be complete.

Conventions:
- `σ(n)` is `∑ d ∈ n.divisors, d`, and the abundancy `σ(n)/n` is computed in `ℚ`. We restrict to
  positive `n`, for which the abundancy is defined.
- Complete means that the data list every term, so the conjecture says that the set of positive
  `n` with abundancy `1024/513` is exactly the set of these 7 numbers.
-/

namespace OMA.S_oeis_a230148

theorem main :
    {n : ℕ | 0 < n ∧ ((∑ d ∈ n.divisors, d : ℕ) : ℚ) / n = 1024 / 513} =
      {397575, 3145425129, 7096702977, 53164445037705, 130468907286855, 1229923663366167,
        2774951736355071} := by
  sorry

end OMA.S_oeis_a230148
