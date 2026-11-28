import Mathlib

/-!
# Tie-breaking in self interest cumulative subtraction games

Source: https://arxiv.org/abs/2510.24280 (A. Bhagat, T. Kulkarni, U. Larsson, D. Murali), Conjecture 4.
Credit: @tatashbar

Conjecture 4 of the source, verbatim: "Consider any subtraction set S, suppose both players act friendly in
case of indifference. Then each player's PSPE utility is never worse than if both players have
antagonistic tie-breaking rules." The paper proves this for `|S| = 2` (Theorem 3, the main result) and
says in the abstract: "For larger subtraction sets, we conjecture that the main result continues to hold,
while tie-breaking monotonicity may fail". `main` below is Conjecture 4. (The other half of that sentence
is settled in the paper itself by the example `S = {4, 5, 9}`, heap `61`.)

The game (Section 1 and Definition 2 of the source). A heap of `h ≥ 0` pebbles and a subtraction set `S` of
positive integers. Two players alternate; a move removes `s ∈ S` pebbles, `s ≤ h`, and the mover keeps
them. The game ends when the player to move has no move. Each player maximises his own total (his
"cumulation"). In case of indifference, that is, when several moves give the mover the same best total, a
friendly player takes a move that maximises the other player's total and an antagonistic player one that
minimises it. With `X` the pair of conventions (mover's, other's) and `d(X)` the swapped pair, the outcome
`o_X(h) = (o¹_X(h), o²_X(h))` = (mover's total, other's total) is defined by `o¹_X(h) = o²_X(h) = 0` if
`h < min S`, and otherwise
  `o¹_X(h) = max { o²_{d(X)}(h - s) + s | s ∈ S, s ≤ h }`,  `o²_X(h) = o¹_{d(X)}(h - s*)`,
where `s*` ranges over the indifferent (tied best) moves and makes `o¹_{d(X)}(h - s*)` largest for a
friendly mover and smallest for an antagonistic mover. "Each player's utility is never worse" is the
componentwise order on these pairs, as the paper says after the conjecture; in its notation the
discrepancies `δⁱ(h) = oⁱ_AvA(h) - oⁱ_FvF(h)`, `i = 1, 2`, are never positive.

Conventions of this translation:
* a convention is a `Bool`: `true` is friendly, `false` is antagonistic;
* `outcome S c₁ c₂ h` is `o_X(h)` for `X = (c₁, c₂)`: the pair (total of the player to move, total of the
  other player) at heap `h`; the recursive call swaps the two conventions, which is the dual `d(X)`;
* `step` is one application of the recurrence. The legal moves are the `s ∈ S` with `s ≤ h` (all elements
  of `S` are positive by hypothesis). With no legal move the result is `(0, 0)`: the supremum of the empty
  set is `0` and the tied set is empty;
* the guard `k < h` in `outcome` only makes the recursion well founded: for `s` positive and `s ≤ h` the
  heap `h - s` is smaller than `h`, so the guard never changes a value that is used;
* `S` is a non-empty `Finset` of positive integers and the heap `h` is arbitrary. The source writes
  `S ⊂ ℕ = {1, 2, …}` and uses `min S`. Only the elements of `S` that are at most `h` matter at heap `h`, so
  nothing is lost by taking `S` finite;
* the conclusion is stated for both players: first the player who starts, then the other one.
-/

namespace OMA.S_arxiv_2510_24280

/-- One application of the recurrence of Definition 2 at heap `h`, for a mover who is friendly
(`friendly = true`) or antagonistic, where `prev k` is the outcome at the smaller heap `k`, seen from the
player who moves there. The result is (mover's total, other player's total). -/
def step (S : Finset ℕ) (friendly : Bool) (h : ℕ) (prev : ℕ → ℕ × ℕ) : ℕ × ℕ :=
  let moves := S.filter (fun s => s ≤ h)
  let mine : ℕ → ℕ := fun s => s + (prev (h - s)).2
  let theirs : ℕ → ℕ := fun s => (prev (h - s)).1
  let best := moves.sup mine
  let ties := moves.filter (fun s => mine s = best)
  (best,
    if friendly then ties.sup theirs
    else if hne : ties.Nonempty then ties.inf' hne theirs else 0)

/-- The outcome `o_X(h)` of the source: (total of the player to move, total of the other player) at heap
`h`, the player to move following convention `c₁` and the other player `c₂`. -/
def outcome (S : Finset ℕ) (c₁ c₂ : Bool) (h : ℕ) : ℕ × ℕ :=
  step S c₁ h (fun k => if _ : k < h then outcome S c₂ c₁ k else (0, 0))
termination_by h

/-- Conjecture 4 of the source: for every subtraction set, at every heap, each player's total when both
players are friendly is at least his total when both are antagonistic. -/
theorem main :
    ∀ S : Finset ℕ, S.Nonempty → (∀ s ∈ S, 0 < s) → ∀ h : ℕ,
      (outcome S false false h).1 ≤ (outcome S true true h).1 ∧
        (outcome S false false h).2 ≤ (outcome S true true h).2 := by
  sorry

end OMA.S_arxiv_2510_24280
