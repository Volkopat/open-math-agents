import Mathlib

/-!
# Second differences of a greedy prime sequence: every positive even integer?

Source: https://mathoverflow.net/questions/206581
Credit: @jagraj28

Let `p(1)` and `p(2)` be primes and, for `n > 2`, let `p(n)` be the least prime `p` with
`p - 2 p(n-1) + p(n-2) > 0`. The question asks whether the second differences
`s(n) = p(n) - 2 p(n-1) + p(n-2)` range through all even positive integers, and states as the main
question (point (3)) the case `p(1) = 2`, `p(2) = 3`:
`(p(n)) = (2, 3, 5, 11, 19, 29, 41, 59, 79, 101, …)`, `(s(n)) = (1, 4, 2, 2, 2, 6, 2, 2, 4, …)`.
Point (2) of the question allows the odd value `s(3) = 1`. The asker reports that every even
positive integer up to `120` occurs among the first `30000` terms of `s`. A comment relates the
question to Polignac's conjecture; there is no answer.

`main` states a positive answer for `p(1) = 2`, `p(2) = 3`: every even positive integer is a
value of `s`.

Conventions.
* Indices start at `0`: `p 0 = 2`, `p 1 = 3`, and `p (n + 2)` is the least prime `q` with
  `q + p n > 2 * p (n + 1)` (the same condition as `q - 2 p(n+1) + p(n) > 0`, written without
  subtraction). It is defined as `sInf` of the set of such primes, which is nonempty since there are
  infinitely many primes.
* `s n = p (n + 2) + p n - 2 * p (n + 1)` in `ℤ`; it is positive by construction.
* The computation of the first `30000` terms with this definition reproduces the terms above and
  finds every even number up to `126`.
-/

namespace OMA.S_mo_206581

/-- The greedy prime sequence with positive second differences, starting `2, 3`. -/
noncomputable def p : ℕ → ℕ
  | 0 => 2
  | 1 => 3
  | n + 2 => sInf {q : ℕ | q.Prime ∧ 2 * p (n + 1) < q + p n}

/-- The second differences `s n = p (n + 2) - 2 p (n + 1) + p n`. -/
noncomputable def s (n : ℕ) : ℤ := (p (n + 2) : ℤ) - 2 * p (n + 1) + p n

/-- Every even positive integer is a second difference of the sequence. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, s n = 2 * k := by
  sorry

end OMA.S_mo_206581
