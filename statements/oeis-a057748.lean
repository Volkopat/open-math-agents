import Mathlib

/-!
# A057748: Number of decompositions of 2n-1 into sum of a twin lucky number and a twin even-lucky-number (from A045955, A045956).

Source: https://oeis.org/A057748
Credit: @velo1203 (agent: Claude Code, model claude-opus-5-5)

OEIS comment (offset 1): Conjecture: this sequence is always positive (with n>1).

## Encoding

* Lucky numbers (A000959) via Ulam's sieve, starting from the odd numbers: `luckyStage 0 i = 2i + 1`;
  at stage `k` the survivor `L = luckyStage k (k + 1)` (that is `3, 7, 9, ...`) is used and every
  `L`-th remaining number is removed, so the `i`-th survivor (0-indexed) is
  `luckyStage k (i + i / (L - 1))`. Positions `<= k` no longer change after stage `k`, so the
  `n`-th lucky number is `luckyStage n n`. This is the encoding of `statements/oeis-a000959.lean`.
* Even-lucky numbers (A045954): the same sieve started from the even numbers,
  `evenLuckyStage 0 i = 2i + 2`; the first term `> 2` is `4`, so every 4th number is removed,
  then every 6th, and so on (A045954: `2, 4, 6, 10, 12, 18, 20, 22, 26, ...`).
* A twin lucky number (A057701) is a lucky number `m` such that `m + 2` or `m - 2` is lucky
  (`1, 3, 7, 9, 13, 15, 31, 33, ...`). A twin even-lucky number is an even-lucky number `m` such
  that `m + 2` or `m - 2` is even-lucky, that is a term of A045955 (lower members) or of
  A045956 (upper members): `2, 4, 6, 10, 12, 18, 20, 22, 34, ...`.
* `a n` counts the decompositions `2n - 1 = p + q` with `p` a twin lucky number and `q` a twin
  even-lucky number, as ordered pairs `(p, q)` (the OEIS example: `5 = 3 + 2 = 1 + 4`, so
  `a 3 = 2`). With this reading the definitions reproduce all 5000 terms of the b-file
  (b057748.txt, Jinyuan Wang).
-/

namespace OMA.S_oeis_a057748

/-- Stages of the lucky-number sieve, started from the odd numbers. -/
def luckyStage : ℕ → ℕ → ℕ
  | 0, i => 2 * i + 1
  | k + 1, i => luckyStage k (i + i / (luckyStage k (k + 1) - 1))

/-- Stages of the even-lucky-number sieve, started from the even numbers. -/
def evenLuckyStage : ℕ → ℕ → ℕ
  | 0, i => 2 * i + 2
  | k + 1, i => evenLuckyStage k (i + i / (evenLuckyStage k (k + 1) - 1))

/-- `m` is a lucky number (A000959). -/
def IsLucky (m : ℕ) : Prop := ∃ n : ℕ, luckyStage n n = m

/-- `m` is an even-lucky number (A045954). -/
def IsEvenLucky (m : ℕ) : Prop := ∃ n : ℕ, evenLuckyStage n n = m

/-- `m` is a twin lucky number (A057701): `m` and `m + 2`, or `m - 2` and `m`, are both lucky. -/
def IsTwinLucky (m : ℕ) : Prop := IsLucky m ∧ (IsLucky (m + 2) ∨ (2 ≤ m ∧ IsLucky (m - 2)))

/-- `m` is a twin even-lucky number (a term of A045955 or A045956). -/
def IsTwinEvenLucky (m : ℕ) : Prop :=
  IsEvenLucky m ∧ (IsEvenLucky (m + 2) ∨ (2 ≤ m ∧ IsEvenLucky (m - 2)))

/-- A057748: the number of ways to write `2n - 1 = p + q` with `p` a twin lucky number and `q`
a twin even-lucky number. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {pq : ℕ × ℕ | pq.1 + pq.2 = 2 * n - 1 ∧ IsTwinLucky pq.1 ∧ IsTwinEvenLucky pq.2}

/-- The conjecture: `a n > 0` for every `n > 1`. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a057748
