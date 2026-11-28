import Mathlib

/-!
# A210380: Erdős's lower bound for square-sum-free tuples

Source: https://oeis.org/A210380
Credit: @jagraj28

A210380: consider all `n`-tuples of distinct positive integers for which no two different
elements add up to a square; `a(n)` is the smallest maximal integer in such tuples
(1, 2, 4, 6, 9, 10, 11, 15, ...). The entry gives `a(n) ≤ (32/11) n - 2` and records that Erdős
conjectured `a(n) ≥ (32/11) n - k` for some fixed `k`.

`main` states Erdős's conjecture: there is a constant `k` such that
`a(n) ≥ (32/11) n - k` for every `n ≥ 1`.

Conventions:
* A tuple of distinct positive integers is a finite set `S` of positive integers with
  `|S| = n`; the condition applies to two different elements only (`x ≠ y`), so `x + x` may be a
  square, as in the source (this is what separates it from Erdős Problem 438).
* `a(n)` is the least `m` such that such a set exists inside `{1, ..., m}`, which is the smallest
  possible maximum. These definitions give 1, 2, 4, 6, 9, 10, 11, 15, 18, 20, 21, as listed.
* `k` is a real constant (an integer constant gives the same statement).
-/

namespace OMA.S_oeis_a210380

/-- No two different elements of `S` add up to a square. -/
def SquareSumFree (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ IsSquare (x + y)

/-- `a n`, OEIS A210380: the least `m` such that some `n` distinct integers in `{1, ..., m}`
have no two different elements adding up to a square. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset ℕ, S.card = n ∧ (∀ x ∈ S, 1 ≤ x ∧ x ≤ m) ∧ SquareSumFree S}

/-- Erdős's conjecture recorded in OEIS A210380. -/
theorem main : ∃ k : ℝ, ∀ n : ℕ, 1 ≤ n → (32 / 11 : ℝ) * n - k ≤ a n := by
  sorry

end OMA.S_oeis_a210380
