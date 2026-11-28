import Mathlib

/-!
# A323712: the two-pile shuffle restores a deck of `n` cards within `n` shuffles

Source: https://oeis.org/A323712
Credit: @avivorly

A323712: Number of the following described shuffles required to return a deck of n cards to its original state.
Create two piles by alternating a card from the top of the deck left-right-left-right until the deck is exhausted.
Then, placing the left pile on top of the right pile constitutes one shuffle.

The entry's comments begin: The card shuffling procedure is the same for even n and odd n. Here are a few
conjectures. The first two of them, the only ones stated here (parts (C1) and (C2) of that list of conjectures),
read:

  (C1) a(n) <= n for all n.

  (C2) a(p)=a(p-1) and a(p)|p-1 when p is a prime >= 5.

The entry's further conjectures in the same comment (on the pseudoprimes 341 and 22369621, on the `n` with
`a(n) = n`, on Catalan numbers and on `a(2n+1)` versus `a(2n)`) are not part of this statement.

For even `n` the bound (C1) is known: Van Cott and Wang (arXiv:2302.03579, Prop. 2.2) show that the order of this
shuffle on a deck of even size `n` is the multiplicative order of `-2` modulo `n + 1`, which is at most `n`. The
statement below covers all `n ≥ 1`, odd and even.

Examples (from the entry): for n = 4 one shuffle turns {a1,a2,a3,a4} into {a3,a1,a4,a2}, and four shuffles restore
the deck, so a(4) = 4; for n = 5 one shuffle turns {a1,a2,a3,a4,a5} into {a5,a3,a1,a4,a2}, and a(5) = 4.

Conventions:
- Positions in the deck are `0, 1, ..., n - 1` (as `Fin n`), position `0` being the top card. `shuf n` sends the
  position of a card before one shuffle to its position after that shuffle.
- Dealing from the top, the cards at positions `0, 2, 4, ...` go to the left pile and the cards at positions
  `1, 3, 5, ...` to the right pile, each new card on top of its pile; the left pile receives `(n + 1) / 2` cards and
  the right pile `n / 2` cards (division rounded down). The card at an even position `i` is card number `i / 2 + 1`
  dealt to the left pile, so `(n + 1) / 2 - 1 - i / 2` cards end above it; the card at an odd position `i` is card
  number `i / 2 + 1` dealt to the right pile, so `n / 2 - 1 - i / 2` cards of the right pile end above it, and the
  whole left pile (`(n + 1) / 2` cards) is placed on top of the right pile. This is `newPos`. `oldPos` gives, for a
  position after the shuffle, the position before it of the card that lands there; it is the inverse of `newPos`,
  so `shuf n` is a permutation of `Fin n`.
- This formula reproduces the examples of the entry (n = 4: a3, a1, a4, a2; n = 5: a5, a3, a1, a4, a2) and agrees
  with the Maple program `pileShuf` and the PARI program `perm` of the entry.
- After `k` shuffles the card that started at position `i` lies at position `(shuf n ^ k) i`, so the deck is in its
  original state exactly when `shuf n ^ k = 1`. Hence `a n`, the least `k ≥ 1` for which the deck is back in its
  original state, is `orderOf (shuf n)`; this order is `≥ 1` because `Equiv.Perm (Fin n)` is a finite group (so the
  value `0` that `orderOf` takes on elements of infinite order never occurs). Evaluating the least `k ≥ 1` with
  `shuf n ^ k = 1` from this definition reproduces the data of the entry for n = 1..40, and iterating `newPos`
  reproduces it for n = 1..72.
- The offset of the entry is 1, so (C1) is stated for `n ≥ 1`. In (C2), `p - 1` is subtraction in `ℕ`, exact
  here since `p ≥ 5`, and `a(p)|p-1` is divisibility.
-/

namespace OMA.S_oeis_a323712

/-- The position (`0`-based, top = `0`) after one shuffle of the card at position `i` of a deck of `n` cards. -/
def newPos (n i : ℕ) : ℕ :=
  if i % 2 = 0 then (n + 1) / 2 - 1 - i / 2 else (n + 1) / 2 + (n / 2 - 1 - i / 2)

/-- The position before one shuffle of the card that is at position `j` after it (the inverse of `newPos n`). -/
def oldPos (n j : ℕ) : ℕ :=
  if j < (n + 1) / 2 then 2 * ((n + 1) / 2 - 1 - j) else 2 * (n / 2 - 1 - (j - (n + 1) / 2)) + 1

/-- One shuffle of a deck of `n` cards, as the permutation of positions: old position to new position. -/
def shuf (n : ℕ) : Equiv.Perm (Fin n) where
  toFun i := ⟨newPos n i, by have := i.isLt; unfold newPos; split_ifs <;> omega⟩
  invFun j := ⟨oldPos n j, by have := j.isLt; unfold oldPos; split_ifs <;> omega⟩
  left_inv i := by
    apply Fin.ext
    show oldPos n (newPos n i.val) = i.val
    have := i.isLt
    unfold oldPos newPos
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    show newPos n (oldPos n j.val) = j.val
    have := j.isLt
    unfold oldPos newPos
    split_ifs <;> omega

/-- `a n`: the number of shuffles needed to return a deck of `n` cards to its original state, the order of the
permutation `shuf n`. -/
noncomputable def a (n : ℕ) : ℕ := orderOf (shuf n)

theorem main :
    (∀ n : ℕ, 1 ≤ n → a n ≤ n) ∧
      (∀ p : ℕ, p.Prime → 5 ≤ p → a p = a (p - 1) ∧ a p ∣ p - 1) := by
  sorry

end OMA.S_oeis_a323712
