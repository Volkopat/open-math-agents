import Mathlib

/-!
# A140357: a(1)=1; a(n)=floor(4*a(n-1)*(n-a(n-1)) / n) for n > 1.

Source: https://oeis.org/A140357
Credit: @eltociear

`a(1) = 1` and `a(n) = ⌊4 a(n-1) (n - a(n-1)) / n⌋` for `n > 1` (`1, 2, 2, 4, 3, 6, ...`). The
entry conjectures:

  starting with any given n and any 1 <= a(n) <= n and applying the rule for the sequence produces
  a sequence which eventually joins this one. For example, starting with a(9)=5, the sequence
  continues 10,3,9,11,9, at which point it has joined.

`orbit n x j` is the value at index `n + j` of the sequence started with value `x` at index `n`
and continued by the rule; A140357 itself is `orbit 1 1`, whose value at index `n + j` is
`orbit 1 1 (n - 1 + j)`. `main` states that for every `n ≥ 1` and `1 ≤ x ≤ n` the two sequences
agree at some index `≥ n` (after which they agree forever, since each term determines the next).
`m - x` is natural subtraction; along these sequences the value at index `m` never exceeds `m`.
-/

namespace OMA.S_oeis_a140357

/-- The rule: the term at index `m` from the term `x` at index `m - 1`. -/
def rule (m x : ℕ) : ℕ := 4 * x * (m - x) / m

/-- The sequence started with value `x` at index `n`: `orbit n x j` is its term at index `n + j`. -/
def orbit (n x : ℕ) : ℕ → ℕ
  | 0 => x
  | j + 1 => rule (n + j + 1) (orbit n x j)

/-- The conjecture in OEIS A140357: every such sequence eventually joins A140357. -/
theorem main : ∀ n x : ℕ, 1 ≤ n → 1 ≤ x → x ≤ n → ∃ j : ℕ, orbit n x j = orbit 1 1 (n - 1 + j) := by
  sorry

end OMA.S_oeis_a140357
