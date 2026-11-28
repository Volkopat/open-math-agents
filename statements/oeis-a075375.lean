import Mathlib

/-!
# A075375: Rearrangement of natural numbers so that every term is relatively prime to the sum of its neighbors.

Source: https://oeis.org/A075375
Credit: @ceejcake

Formalizes the dislocation conjecture of OEIS A075375 (offset 1):
If `a(n) = k`, define the dislocation of `k` to be `|k - n|`.
Conjecture: The maximum value of dislocation is `< 5`, i.e., `|(a n : ℤ) - (n : ℤ)| < 5` for all
`n ≥ 1`.

Note on truth value:
As already noted in the OEIS comments (David Wasserman, Jan 17 2005), this conjecture is false
as written: it first fails at `n = 169`, where `a(169) = 164` and `|164 - 169| = 5`.

Conventions:
* The sequence is defined greedily starting from `a(1) = 1`, `a(2) = 2`; for `n ≥ 3`, `a(n)` is
  the least positive integer `m` not among `a(1), ..., a(n - 1)` such that
  `Nat.gcd (a (n - 1)) (a (n - 2) + m) = 1`.
* `findNext` searches `m = 1, 2, ...` with fuel `(M + prev + 2) * (cur + 1)`, where `M` is the
  maximum of `used`. Since `m₀ = (M + prev + 1) * cur + 1 - prev` satisfies `m₀ > M` (so
  `m₀ ∉ used`), `prev + m₀ = (M + prev + 1) * cur + 1` (coprime to `cur ≥ 1`), and
  `m₀ < (M + prev + 2) * (cur + 1)`, this fuel is always strictly sufficient.
* All 72 OEIS A075375 DATA terms match (`1, 2, 4, 3, 6, 8, 5, 9, 11, 7, ...`), and `a 169 = 164`.
-/

namespace OMA.S_oeis_a075375

/-- First `m` in `[start, start + fuel)` not in `used` with `Nat.gcd cur (prev + m) = 1`. -/
def findNext (used : List ℕ) (prev cur : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | m, fuel + 1 =>
    if !(used.contains m) && Nat.gcd cur (prev + m) == 1 then m
    else findNext used prev cur (m + 1) fuel

/-- Reversed prefix `[a(n), a(n - 1), ..., a(1)]` of OEIS A075375. -/
def prefixRev : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [2, 1]
  | k + 3 =>
    let rev := prefixRev (k + 2)
    match rev with
    | cur :: prev :: _ =>
      let fuel := (rev.foldl max 0 + prev + 2) * (cur + 1)
      findNext rev prev cur 1 fuel :: rev
    | _ => rev

/-- OEIS A075375 (offset 1): greedy rearrangement where each term is coprime to the sum of its
neighbors. -/
def a (n : ℕ) : ℕ :=
  (prefixRev n).headD 0

/-- Conjecture (OEIS A075375): for every `n ≥ 1`, the dislocation `|a(n) - n|` is `< 5`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → |(a n : ℤ) - (n : ℤ)| < 5 := by
  sorry

end OMA.S_oeis_a075375
