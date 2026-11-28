import Mathlib

/-!
# Erdős Problem 778

Source: https://www.erdosproblems.com/778
Credit: @shc261392

The source: Alice and Bob play a game on the edges of `Kₙ`, alternately colouring edges red
(Alice) and blue (Bob). Alice goes first, and wins if at the end the largest red clique is larger
than any of the blue cliques. Does Bob have a winning strategy for `n ≥ 3`? (Erdős believed the
answer is yes.) The source then asks two further questions about variants of the game (Bob
colouring two edges per turn; maximum degrees instead of cliques).

This file states the first question, in its affirmative form (the answer Erdős expected): a proof
of `main` answers it yes, a proof of `¬ main` answers it no. The two variant games are not stated.

Reading used here:
* The vertices of `Kₙ` are `Fin n`; the edges are the non-diagonal elements of `Sym2 (Fin n)`.
* Each move colours one edge that has no colour yet; the game ends when every edge is coloured.
  Alice moves when both players have coloured the same number of edges (she goes first).
* A red (blue) clique is a set of vertices all of whose pairs are red (blue) edges; the size of
  the largest one is `cliqueSize`. Alice wins when `cliqueSize red > cliqueSize blue` at the end;
  otherwise (ties included) Bob wins. The game is finite with perfect information and no draws,
  so "Bob has a winning strategy" is "Alice has no winning strategy".
* `AliceForces m R B` says that from the position with red edges `R` and blue edges `B`, with `m`
  uncoloured edges left, Alice can force a win; it is defined by recursion on `m`.
-/

namespace OMA.S_erdos_778

/-- The edges of the complete graph on `Fin n`. -/
def edges (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ¬ e.IsDiag

/-- The size of the largest set of vertices all of whose pairs lie in `S`. -/
def cliqueSize {n : ℕ} (S : Finset (Sym2 (Fin n))) : ℕ :=
  ((Finset.univ : Finset (Fin n)).powerset.filter
    (fun s => ∀ x ∈ s, ∀ y ∈ s, x ≠ y → s(x, y) ∈ S)).sup Finset.card

/-- Alice can force a win from red edges `R` and blue edges `B`, with `m` edges still uncoloured. -/
def AliceForces {n : ℕ} : ℕ → Finset (Sym2 (Fin n)) → Finset (Sym2 (Fin n)) → Prop
  | 0, R, B => cliqueSize B < cliqueSize R
  | m + 1, R, B =>
    if R.card = B.card then
      ∃ e ∈ edges n \ (R ∪ B), AliceForces m (insert e R) B
    else
      ∀ e ∈ edges n \ (R ∪ B), AliceForces m R (insert e B)

theorem main :
    ∀ n : ℕ, 3 ≤ n → ¬ AliceForces (edges n).card (∅ : Finset (Sym2 (Fin n))) ∅ := by
  sorry

end OMA.S_erdos_778
