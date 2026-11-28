import Mathlib

/-!
# GoldGrabbing

Determine optimal play when two players take turns removing a leaf of a finite tree
and taking its nonnegative integer gold. The payoff is the difference in gold collected.
The remaining singleton counts as a legal move. The assertion gives both players
an optimal strategy from every remaining position, in particular from the full tree.

Source: https://www.openproblemgarden.org/op/a_gold_grabbing_game
-/

namespace OMA.S_opg_a_gold_grabbing_game

open Finset

/-- A leaf can be removed, including the last remaining vertex. -/
def leafMoves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Finset (Fin n)) : Finset (Fin n) :=
  s.filter fun v => (s.filter (G.Adj v)).card ≤ 1

abbrev Policy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :=
  ∀ (s : Finset (Fin n)), (leafMoves G s).Nonempty → {v // v ∈ leafMoves G s}

/-- Score of the player to move minus the score of the other player. -/
def playScore {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (gold : Fin n → ℕ)
    (s : Finset (Fin n)) (p q : Policy G) : ℤ :=
  if h : (leafMoves G s).Nonempty then
    let v := p s h
    (gold v.val : ℤ) - playScore G gold (s.erase v.val) q p
  else 0
termination_by s.card
decreasing_by
  exact card_erase_lt_of_mem (mem_filter.mp (p s h).property).1

def OptimalStrategies : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], G.IsTree →
    ∀ gold : Fin n → ℕ, ∃ p : Policy G,
      ∀ (q : Policy G) (s : Finset (Fin n)),
        (s.Nonempty → (leafMoves G s).Nonempty) ∧
        playScore G gold s q p ≤ playScore G gold s p p ∧
          playScore G gold s p p ≤ playScore G gold s p q

theorem main : OptimalStrategies := by
  sorry

end OMA.S_opg_a_gold_grabbing_game
