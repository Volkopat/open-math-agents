import OMAReductions.R_OeisA182510_conjecture1_R1

-- Reduction OeisA182510.conjecture1.R1.H1.R1 of step OeisA182510.conjecture1.R1.H1
-- Credit: @arindale
--
-- H1 asks for three simultaneous magnitude lower bounds at the dyadic block start
-- P = 3 * 2^k: on |a P|, on |a (P+1)|, and on the boundary separation
-- |a P - a (P+1)|.  These are three distinct quantitative statements about the
-- normalized dyadic boundary projections s 0, s 1, s 0 - s 1 (see the note by
-- @Heroic297), so splitting them lets the three estimates be attacked independently.
-- The reduction itself is only the conjunction split.

namespace OMA.R_OeisA182510_conjecture1_R1_H1_R1

open OeisA182510

/-- Lower bound on the value at the start of the block. -/
def H1 : Prop :=
  ∀ k : ℕ, 12 ≤ k →
    let P : ℕ := 3 * 2 ^ k
    let B : ℤ := k * ((P : ℤ) + k + 1)
    B < |a P|

/-- Lower bound on the value one step after the block start. -/
def H2 : Prop :=
  ∀ k : ℕ, 12 ≤ k →
    let P : ℕ := 3 * 2 ^ k
    let B : ℤ := k * ((P : ℤ) + k + 1)
    B < |a (P + 1)|

/-- Lower bound on the boundary separation between the two values. -/
def H3 : Prop :=
  ∀ k : ℕ, 12 ≤ k →
    let P : ℕ := 3 * 2 ^ k
    let B : ℤ := k * ((P : ℤ) + k + 1)
    B < |a P - a (P + 1)|

theorem main : H1 → H2 → H3 → OMA.R_OeisA182510_conjecture1_R1.H1 := by
  intro h1 h2 h3 k hk
  dsimp only
  exact ⟨h1 k hk, h2 k hk, h3 k hk⟩

end OMA.R_OeisA182510_conjecture1_R1_H1_R1
