import Mathlib

/-!
# A288999: Positions of 1 in A288997; complement of A288998.

Source: https://oeis.org/A288999
Conjectures: the entry's comment (limit and bounds) and Chai Wah Wu, Feb 06 2025 (closed form)
Credit: @ceejcake

A288997 is the fixed point of the mapping `00 -> 0010, 01 -> 001, 10 -> 001`, starting with `00`.
The mapping is Mathematica's `StringReplace` with these three rules: the word is scanned from left
to right; at each position the first rule that matches there is applied and the scan continues
after the replaced letters; a letter where no rule matches (a `1` followed by `1`, or the last
letter alone) is copied unchanged. This is `sr` below, on words over `ℕ` written as lists.

The iterates `sr^[M] [0, 0]` have lengths 2, 4, 7, 12, 20, 34, ...; they are not prefixes of each
other (their last letters change), but every letter stabilises. The fixed point A288997 is the
limit word: its letter at position `i` (counted from 0) is `b` when the iterates eventually always
have `b` at position `i`. `a n` (offset 1) is the position, counted from 1, of the `n`-th letter
`1` of that word: `a 1 = 3`, `a 2 = 7`, `a 3 = 10`, ...

The entry lists the conjectures `a(n)/n -> 2 + sqrt(2)`, `-1 < 2 + sqrt(2) - a(n)/n < -1 + sqrt(2)`
for `n >= 1`, and `a(n) = 2n + round(n*sqrt(2))`; `main` states their conjunction. `round` is
Mathlib's `round` (halves round up); `n*sqrt(2)` is never a half-integer for `n ≥ 1`, so the
convention for ties does not matter.

The closed form is false as stated: `a(11) = 37`, while `2*11 + round(11*sqrt(2)) = 22 + 16 = 38`.
-/

namespace OMA.S_oeis_a288999

/-- One step of the rewriting `00 -> 0010, 01 -> 001, 10 -> 001` with `StringReplace` semantics:
scan from the left, apply the first rule that matches at the current position, copy a letter where
no rule matches. -/
def sr : List ℕ → List ℕ
  | 0 :: 0 :: rest => [0, 0, 1, 0] ++ sr rest
  | 0 :: 1 :: rest => [0, 0, 1] ++ sr rest
  | 1 :: 0 :: rest => [0, 0, 1] ++ sr rest
  | x :: rest => x :: sr rest
  | [] => []

/-- The letter at position `i` (from 0) of the fixed point A288997 is `1`: from some iterate on,
every iterate `sr^[M] [0, 0]` has the letter `1` at position `i`. -/
def IsOne (i : ℕ) : Prop :=
  ∃ N : ℕ, ∀ M ≥ N, (sr^[M] [0, 0])[i]? = some 1

/-- A288999: `a n` is the position, counted from 1, of the `n`-th `1` in A288997 (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsOne (n - 1) + 1

/-- The conjectures listed for A288999: `a(n)/n -> 2 + sqrt(2)`;
`-1 < 2 + sqrt(2) - a(n)/n < -1 + sqrt(2)` for `n ≥ 1`; and `a(n) = 2n + round(n*sqrt(2))` for
`n ≥ 1` (the last one is false: it fails at `n = 11`). -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n) Filter.atTop (nhds (2 + Real.sqrt 2)) ∧
      (∀ n : ℕ, 1 ≤ n → -1 < 2 + Real.sqrt 2 - (a n : ℝ) / n ∧
        2 + Real.sqrt 2 - (a n : ℝ) / n < -1 + Real.sqrt 2) ∧
      (∀ n : ℕ, 1 ≤ n → (a n : ℤ) = 2 * n + round ((n : ℝ) * Real.sqrt 2)) := by
  sorry

end OMA.S_oeis_a288999
