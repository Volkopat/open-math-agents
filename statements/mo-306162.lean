import Mathlib

/-!
# Generalization of Penney's game (Penney's paradox)

Source: https://mathoverflow.net/questions/306162
Credit: @D3DataScience

The source asks about a two-level Penney game.  A word is a finite binary
sequence.  A player completes a two-word choice when both of its words have
occurred in the infinite toss sequence, in either order and with arbitrary
overlap or separation.  The winner is the player whose completion time is
smaller.  The probability measure is required to be the fair independent
Bernoulli measure, expressed by its finite-coordinate cylinder probabilities.
-/

namespace OMA.S_mo_306162

open MeasureTheory
open scoped ENNReal

abbrev Ω := ℕ → Bool
abbrev Word (k : ℕ) := Fin k → Bool

def occurs {k : ℕ} (w : Word k) (ω : Ω) (start : ℕ) : Prop :=
  ∀ i : Fin k, ω (start + (i : ℕ)) = w i

def occurredBy {k : ℕ} (w : Word k) (ω : Ω) (time : ℕ) : Prop :=
  ∃ start ≤ time, occurs w ω start

def Choice (k : ℕ) := {s : Finset (Word k) // s.card = 2}

def disjointChoices {k : ℕ} (A B : Choice k) : Prop :=
  A.1 ∩ B.1 = ∅

def choiceOccurredBy {k : ℕ} (A : Choice k) (ω : Ω) (time : ℕ) : Prop :=
  ∀ w ∈ A.1, occurredBy w ω time

def firstCompletion {k : ℕ} (A : Choice k) (ω : Ω) (time : ℕ) : Prop :=
  choiceOccurredBy A ω time ∧ ∀ earlier < time, ¬ choiceOccurredBy A ω earlier

def BWins {k : ℕ} (A B : Choice k) (ω : Ω) : Prop :=
  ∃ bTime aTime, firstCompletion B ω bTime ∧
    firstCompletion A ω aTime ∧ bTime < aTime

def cylinderCondition (μ : Measure Ω) : Prop :=
  ∀ (s : Finset ℕ) (x : ℕ → Bool),
    μ {ω : Ω | ∀ i ∈ s, ω i = x i} = (2 : ℝ≥0∞)⁻¹ ^ s.card

def fairCoin (μ : Measure Ω) : Prop := cylinderCondition μ

def BWinProbability {k : ℕ} (μ : Measure Ω) (A B : Choice k) : ℝ≥0∞ :=
  μ {ω : Ω | BWins A B ω}

theorem main :
    ∀ (k : ℕ), 2 < k → ∀ (μ : Measure Ω), fairCoin μ →
      ∀ A : Choice k, ∃ B : Choice k,
        disjointChoices A B ∧ BWinProbability μ A B > (2 : ℝ≥0∞)⁻¹ := by
  sorry

end OMA.S_mo_306162
