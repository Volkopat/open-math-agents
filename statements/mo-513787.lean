import Mathlib

/-!
# Arithmetic progressions of sums of two squares

Source: https://mathoverflow.net/questions/513787 (CC BY-SA 4.0).

Let `S = (s_n)` be the increasing sequence of the numbers of the form `x² + y²`, `x, y` integers.
Questions:
a) is it true that for every `l` there is an arithmetic progression of the form
   `s_{n+1}, s_{n+2}, …, s_{n+l}` (that is, `l` consecutive terms of `S`)?
b) for every `l`, is there a `k` such that the first `l` terms of the arithmetic progression
   `1, 1 + k, 1 + 2k, …` belong to `S`?
Both are consequences of Dickson's conjecture, as the asker notes. We state the affirmative
answers to both.

Formalization notes:
* `S` is `{m : ℕ | ∃ x y : ℤ, m = x² + y²}` (it contains `0` and `1`) and `s = Nat.nth (· ∈ S)`
  enumerates it increasingly (`s 0 = 0`); the starting index in a) is existential, so the offset
  of the indexing does not matter.
* In b) the common difference is required to be positive (`k = 0` would make the question
  trivial).
* Checked numerically: a) has examples for `l ≤ 5` (e.g. `2989, 2993, 2997, 3001, 3005`), and b)
  holds for `l ≤ 8` (`k = 12` works for `l = 8`).
-/

namespace OMA.S_mo_513787

/-- The natural numbers that are a sum of two squares of integers. -/
def S : Set ℕ := {m : ℕ | ∃ x y : ℤ, (m : ℤ) = x ^ 2 + y ^ 2}

/-- The increasing enumeration of `S`. -/
noncomputable def s (n : ℕ) : ℕ := Nat.nth (· ∈ S) n

/-- a) arbitrarily long runs of consecutive terms of `S` in arithmetic progression, and
b) arbitrarily long arithmetic progressions `1, 1 + k, …` with `k ≥ 1` inside `S`. -/
theorem main :
    (∀ l : ℕ, ∃ n d : ℕ, ∀ i < l, s (n + i) = s n + i * d) ∧
    (∀ l : ℕ, ∃ k : ℕ, 1 ≤ k ∧ ∀ j < l, 1 + j * k ∈ S) := by
  sorry

end OMA.S_mo_513787
