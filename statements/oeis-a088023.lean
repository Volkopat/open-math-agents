import Mathlib

/-!
# A088023: Reverse-and-add sequence

Source: https://oeis.org/A088023
Credit: @ceejcake

Formalizes the conjecture of OEIS A088023 (offset 1):
Set `a(1) = 1`. Repeatedly take the list of defined initial terms, reverse their order,
add `1, 2, 3, ...` to the reversed list in succession, and append this new list to the right
of the previously defined terms.
Conjecture: `a(n + 1) ≥ a(n)` for all `n ≥ 1`.

Conventions:
* `step L` performs one expansion step: `L ++ (L.reverse.zipIdx 1).map (fun p => p.1 + p.2)`.
* `block k` is the prefix of length `2^k` obtained after `k` steps starting from `[1]`.
* For `n ≥ 1`, `n ≤ 2 ^ (Nat.log2 n + 1)`, so `a n` is the `(n - 1)`-th entry (0-indexed)
  of `block (Nat.log2 n + 1)`. Since `block k` is a prefix of `block (k + 1)`, this gives the
  exact `n`-th term of the infinite sequence (offset 1).
* Initial values match all 70 OEIS A088023 DATA terms:
  `1, 2, 3, 3, 4, 5, 5, 5, 6, 7, 8, 8, 8, 9, 9, 9, 10, 11, 12, 12, ...`.
-/

namespace OMA.S_oeis_a088023

/-- One expansion step of OEIS A088023: reverse `L`, add `1, 2, ...` to the reversed list
in succession, and append the result to `L`. -/
def step (L : List ℕ) : List ℕ :=
  L ++ (L.reverse.zipIdx 1).map (fun p => p.1 + p.2)

/-- The initial prefix of length `2^k` after `k` expansion steps starting from `[1]`. -/
def block : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => step (block k)

/-- OEIS A088023 (offset 1): the `n`-th term of the sequence (for `n ≥ 1`). -/
def a (n : ℕ) : ℕ :=
  if 1 ≤ n then (block (Nat.log2 n + 1)).getD (n - 1) 0 else 0

/-- Conjecture (OEIS A088023): `a(n + 1) ≥ a(n)` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1) := by
  sorry

end OMA.S_oeis_a088023
