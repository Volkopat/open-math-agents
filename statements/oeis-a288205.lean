import Mathlib

/-!
# A288205: Positions of 1 in A288203; complement of A288204.

Source: https://oeis.org/A288205
Conjecture: Jon Maiga, Nov 25 2018
Credit: @ceejcake

A288203 is the fixed point of the mapping `00 -> 0010, 1 -> 010`, starting with `00`. The mapping
is Mathematica's `StringReplace` with the rules `00 -> 0010` and `1 -> 010`: the word is scanned
from left to right; at each position the first rule that matches there is applied and the scan
continues after the replaced letters; a letter where no rule matches (a `0` not followed by `0`)
is copied unchanged. This is `sr` below, on words over `ℕ` written as lists.

The iterates `sr^[M] [0, 0]` have lengths 2, 4, 8, 18, 38, ...; they are not prefixes of each
other (their last letters change), but every letter stabilises. The fixed point A288203 is the
limit word: its letter at position `i` (counted from 0) is `b` when the iterates eventually always
have `b` at position `i`. `a n` (offset 1) is the position, counted from 1, of the `n`-th letter
`1` of that word: `a 1 = 3`, `a 2 = 6`, `a 3 = 10`, ...

A036987 is the Fredholm-Rueppel sequence (offset 0): `A036987(k) = 1` if `k + 1` is a power of 2,
else `0`. The conjecture `a(n) = Sum_{k=1..n} 4 - A036987(k)` is read as
`a(n) = ∑_{k=1}^{n} (4 - A036987(k))` (reading it as `4*n - ∑ A036987(k)` gives the same value).

As stated it is false: `a(2) = 6`, while the sum is `(4 - 1) + (4 - 0) = 7`. (The data agree with
the shifted formula `∑_{k=1}^{n} (4 - A036987(k - 1))`, which is not what the entry states.)
-/

namespace OMA.S_oeis_a288205

/-- One step of the rewriting `00 -> 0010, 1 -> 010` with `StringReplace` semantics: scan from
the left, apply the first rule that matches at the current position, copy a letter where no rule
matches. -/
def sr : List ℕ → List ℕ
  | 0 :: 0 :: rest => [0, 0, 1, 0] ++ sr rest
  | 1 :: rest => [0, 1, 0] ++ sr rest
  | x :: rest => x :: sr rest
  | [] => []

/-- The letter at position `i` (from 0) of the fixed point A288203 is `1`: from some iterate on,
every iterate `sr^[M] [0, 0]` has the letter `1` at position `i`. -/
def IsOne (i : ℕ) : Prop :=
  ∃ N : ℕ, ∀ M ≥ N, (sr^[M] [0, 0])[i]? = some 1

/-- A288205: `a n` is the position, counted from 1, of the `n`-th `1` in A288203 (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsOne (n - 1) + 1

/-- A036987, the Fredholm-Rueppel sequence: `1` if `k + 1` is a power of 2, else `0`. -/
def A036987 (k : ℕ) : ℕ := if ∃ m < k + 1, k + 1 = 2 ^ m then 1 else 0

/-- The conjecture `a(n) = Sum_{k=1..n} 4 - A036987(k)` for all `n ≥ 1` (false: it fails at
`n = 2`). -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n : ℤ) = ∑ k ∈ Finset.Icc 1 n, (4 - (A036987 k : ℤ)) := by
  sorry

end OMA.S_oeis_a288205
