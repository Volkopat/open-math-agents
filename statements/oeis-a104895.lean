import Mathlib

/-!
# A104895: positions of values

Source: https://oeis.org/A104895
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A104895): the positions where `0, 1, 2, 3, …` appear are given by A048724,
and the positions where `-1, -2, -3, …` appear are given by A065621.

Conventions:
* The sequence is defined by the entry's formula `a(0) = 0` and, for `0 ≤ j < 2^k`,
  `a(2^k + j) = a(j) + 2^k` if `a(j) < 0` and `a(j) - 2^k` otherwise. This reproduces the listed
  terms `0, -1, -2, 1, -4, 3, 2, -3, …`. (The entry's name gives the recursion
  `a(2n) = -2 a(n)`, `a(2n+1) = 2 a(n) - 1`, which does not reproduce the listed data, e.g. it
  gives `a(2) = 2` instead of `-2`; we follow the data.)
* A048724(k) = `k XOR 2k` (offset 0); A065621(k) = `k XOR 2(k - lowbit(k))` (offset 1), with
  `lowbit(k) = 2^{v₂(k)}` (formulas from those entries).
* "The positions where `k` appears are given by" A048724: `a(n) = k` iff `n = A048724(k)`; and
  `a(n) = -k` iff `n = A065621(k)` for `k ≥ 1`.
-/

namespace OMA.S_oeis_a104895

/-- A104895. -/
def a (n : ℕ) : ℤ :=
  if h : n = 0 then 0
  else
    have : n - 2 ^ Nat.log 2 n < n := Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.two_pow_pos _)
    if a (n - 2 ^ Nat.log 2 n) < 0 then a (n - 2 ^ Nat.log 2 n) + 2 ^ Nat.log 2 n
    else a (n - 2 ^ Nat.log 2 n) - 2 ^ Nat.log 2 n

/-- A048724. -/
def b (k : ℕ) : ℕ := k ^^^ (2 * k)

/-- A065621. -/
def c (k : ℕ) : ℕ := k ^^^ (2 * (k - 2 ^ padicValNat 2 k))

theorem main :
    (∀ (n k : ℕ), a n = k ↔ n = b k) ∧ (∀ (n k : ℕ), 1 ≤ k → (a n = -(k : ℤ) ↔ n = c k)) := by
  sorry

end OMA.S_oeis_a104895
