import Mathlib

/-!
# A221564: The number of FO4C3 moves required to restore a packet of n playing cards to its original state (order and orientation), where each move Flips Over the top four (4) as a unit and then Cuts three (3) cards from the top to bottom.

Source: https://oeis.org/A221564
Credit: @rickmanelius

Conjecture: a(3k+1) = 2k.

(Andrew Howroyd, Apr 27 2020, in a comment and a formula of the entry: the top card stays on top
and is flipped over by each move, and the other cards split into three cycles; a(3n+1) = 2n.)

Formalization notes:
* A packet is a list of cards, top card first. A card is a pair (label, face). The label is the
  original position 0, ..., n-1 of the card from the top, and face = true means turned over.
  The starting packet `deck n` has card i at position i, every card face down (face = false).
* One FO4C3 move, `move`: the top four cards are turned over as one block, so their order is
  reversed and each of them changes face; then three cards are cut from the top to the bottom,
  that is the top three cards move, in order, under the other cards (`List.rotate 3`).
* a(n) is the number of moves that restore the packet, order and orientation: the least m >= 1
  with move^m (deck n) = deck n, which is `Function.minimalPeriod move (deck n)`.
* The offset is 4, so the conjecture is about n = 3k + 1 >= 4, that is every k >= 1.
* Checked by computation: this model gives the first 23 terms 2, 4, 4, 4, 12, 12, 6, 24, 24, ...
  of the data (n = 4, ..., 26), and a(3k+1) = 2k for k = 1, ..., 60.
-/

namespace OMA.S_oeis_a221564

/-- One FO4C3 move on a packet (top card first; a card is a pair (label, turned over)). The top
four cards are turned over as a block, then the top three cards are cut to the bottom. -/
def move (l : List (ℕ × Bool)) : List (ℕ × Bool) :=
  ((l.take 4).reverse.map (fun c => (c.1, !c.2)) ++ l.drop 4).rotate 3

/-- The starting packet of n cards: card i at position i (from the top), face down. -/
def deck (n : ℕ) : List (ℕ × Bool) := (List.range n).map (fun i => (i, false))

/-- A221564(n): the number of FO4C3 moves needed to restore a packet of n cards. -/
noncomputable def a (n : ℕ) : ℕ := Function.minimalPeriod move (deck n)

/-- The conjecture of the entry: a(3k+1) = 2k (for every k >= 1, by the offset 4). -/
theorem main : ∀ k : ℕ, 1 ≤ k → a (3 * k + 1) = 2 * k := by
  sorry

end OMA.S_oeis_a221564
