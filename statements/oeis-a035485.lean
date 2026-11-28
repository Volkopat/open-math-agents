import Mathlib

/-!
# A035485: Guy's shuffling problem — every card eventually comes to the top

Source: https://oeis.org/A035485
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

OEIS A035485 (N. J. A. Sloane and Clark Kimberling; R. K. Guy's shuffling problem, see D. Gale,
"Careful Card-Shuffling and Cutting Can Create Chaos", Math. Intelligencer 14(1), 1992) is the
card on top of the deck at the n-th stage. The deck starts as 1, 2, 3, 4, … (stage 0), and
"at n-th step, pick up top n cards and interlace them with the next n": if the top n cards are
f₀, …, f_{n-1} and the next n are g₀, …, g_{n-1}, the new top 2n cards are
g₀, f₀, g₁, f₁, …, g_{n-1}, f_{n-1}, and the rest of the deck is unchanged (this matches the deck
states shown in the entry, the companion array A035491, and the Python program in the entry).
The entry states the open problem

  "It is conjectured that eventually every number appears on top of the deck."

Modelling choices:
* The deck is infinite, as in the entry; it is modelled as a function `ℕ → ℕ` sending a
  position (0 = top) to the card there. Stage `n` only moves the top `2n` cards.
* "Eventually every number appears on top" is read as: every card `c ≥ 1` is the top card
  after some stage `n` (stage 0, with card 1 on top, included).
-/

namespace OMA.S_oeis_a035485

/-- The deck after stage `n`: `deck n i` is the card at position `i` (position `0` is the top).
Stage `n + 1` takes the top `n + 1` cards `f` and the next `n + 1` cards `g` and puts
`g₀, f₀, g₁, f₁, …` on top; positions `≥ 2 (n + 1)` are untouched. -/
def deck : ℕ → ℕ → ℕ
  | 0, i => i + 1
  | n + 1, i =>
    if i < 2 * (n + 1) then
      if i % 2 = 0 then deck n (n + 1 + i / 2) else deck n (i / 2)
    else deck n i

/-- A035485: the card on top of the deck after stage `n`. -/
def top (n : ℕ) : ℕ := deck n 0

/-- **Guy's shuffling conjecture (A035485).** Every card eventually appears on top of the
deck. -/
theorem main : ∀ c : ℕ, 1 ≤ c → ∃ n : ℕ, top n = c := by
  sorry

end OMA.S_oeis_a035485
