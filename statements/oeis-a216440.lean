import Mathlib

/-!
# A216440: a(n) = smallest m such that 2n-1 | 2^m+1, or 0 if no such m exists.

Source: https://oeis.org/A216440
Credit: @bnb9001

Offset 1: 1, 1, 2, 0, 3, 5, 6, 0, 4, ... (m ranges over positive integers, so a(1) = 1).

Conjecture (Kristjan Kiolein, Mar 25 2023): a(n) is the number of riffle shuffles of 2(n-1) cards
required to reverse the order of the deck, or 0 if no such number of shuffles exists, for the
in-shuffle variant of the riffle shuffle, e.g., [1, 2, 3, 4] -> [3, 1, 4, 2] -> [4, 3, 2, 1].

The in-shuffle of 2k cards cuts the deck into halves and interleaves them starting with the
second half; below, `src k j` is the old position of the card that lands at position `j`
(0-indexed), and `deck k m` is the deck 0, 1, ..., 2k-1 after m in-shuffles.
-/

namespace OMA.S_oeis_a216440

open Classical in
/-- A216440: the smallest `m ≥ 1` with `2n-1 ∣ 2^m + 1`, or 0 if there is none. -/
noncomputable def a (n : ℕ) : ℕ :=
  if h : ∃ m, 1 ≤ m ∧ (2 * n - 1) ∣ 2 ^ m + 1 then Nat.find h else 0

/-- Card positions after an in-shuffle of `2k` cards (0-indexed): the new position `j` holds the
card from old position `k + j/2` if `j` is even and `j/2` if `j` is odd. On `[1, 2, 3, 4]` this
gives `[3, 1, 4, 2]`. -/
def src (k j : ℕ) : ℕ := if j % 2 = 0 then k + j / 2 else j / 2

/-- After `m` in-shuffles of the deck `0, 1, ..., 2k-1`, the card at position `j`. -/
def deck (k : ℕ) : ℕ → ℕ → ℕ
  | 0, j => j
  | m + 1, j => deck k m (src k j)

/-- `m` in-shuffles reverse the deck of `2k` cards. -/
def Reverses (k m : ℕ) : Prop := ∀ j < 2 * k, deck k m j = 2 * k - 1 - j

open Classical in
/-- The number of in-shuffles of `2(n-1)` cards required to reverse the deck, or 0. -/
noncomputable def shuffles (n : ℕ) : ℕ :=
  if h : ∃ m, 1 ≤ m ∧ Reverses (n - 1) m then Nat.find h else 0

/-- Kiolein's conjecture: for `n >= 1`, the number of in-shuffles reversing `2(n-1)` cards is `a(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → shuffles n = a n := by
  sorry

end OMA.S_oeis_a216440
