import Mathlib

/-!
# OEIS A057032: limit of forward-cyclic block permutations

Source: https://oeis.org/A057032
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`P(n)` leaves `s(1), …, s(n-1)` fixed and forward-cyclically permutes every block of `n`
consecutive terms thereafter (`(x₁, …, xₙ) ↦ (xₙ, x₁, …, xₙ₋₁)`, as in the entry's examples).
`PS(2) = P(2)(1, 2, 3, …)`, `PS(m+1) = P(m+1)(PS(m))`, and `a(n) = lim PS(m)(n) = PS(n+1)(n)`
(positions `≥ n+1` are the only ones moved later). A057064 is the same construction with
`s(1), …, s(n)` fixed. Conjectures (Mikhail Kurkov, in the entry), for `n ≥ 1`:
* `a(n) - 1` is prime iff `a(n) = n + 1`;
* `a(n) = A057064(n+1) - 1`.
Sequences are 1-indexed functions `ℕ → ℕ` (value at `0` unused).
-/

namespace OMA.S_oeis_a057032

/-- `P` with fixed prefix length `f` and block length `n`: positions `i ≥ f + 1` are grouped into
blocks of `n` consecutive positions starting at `f + 1`, each rotated forward. -/
def rot (f n : ℕ) (s : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ f then s i
  else if (i - (f + 1)) % n = 0 then s (i + n - 1) else s (i - 1)

/-- `PS(m)` for A057032 (prefix `m - 1` fixed at step `m`); `PS(1)` is the identity sequence. -/
def PS : ℕ → ℕ → ℕ
  | 0 => id
  | 1 => id
  | m + 2 => rot (m + 1) (m + 2) (PS (m + 1))

/-- `PS(m)` for A057064 (prefix `m` fixed at step `m`). -/
def PS' : ℕ → ℕ → ℕ
  | 0 => id
  | 1 => id
  | m + 2 => rot (m + 2) (m + 2) (PS' (m + 1))

/-- A057032. -/
def a (n : ℕ) : ℕ := PS (n + 1) n

/-- A057064 (its limit value at `n` is reached at step `n`). -/
def b (n : ℕ) : ℕ := PS' n n

/-- Kurkov's two conjectures. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ((a n - 1).Prime ↔ a n = n + 1) ∧ a n = b (n + 1) - 1 := by
  sorry

end OMA.S_oeis_a057032
