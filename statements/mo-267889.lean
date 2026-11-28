import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Rat.BigOperators

/-!
# Expected value for difference of two dependent random subset
Source: Sam, MathOverflow question 267889 (2017-04-22).
https://mathoverflow.net/questions/267889/expected-value-for-difference-of-two-dependent-random-subset
Credit: @LDJAI

The first sample consists of m independent uniform draws from Fin n (a
relabeling of 1,...,n). The second sample has exactly as many draws as
there were distinct values in the first sample. Conditional on the first
sample, these draws are independent and uniform, with replacement.
The source asks for both expectations and whether the proposed identity
holds; the main declaration states the proposed identity. The accompanying
proof supplies both expectation formulas and refutes the identity.
-/

open Finset BigOperators
namespace OMA.S_mo_267889

/-- Distinct values seen in k independent uniform samples from an alphabet of n elements. -/
def sample {n k : ℕ} (f : Fin k → Fin n) : Finset (Fin n) :=
  Finset.univ.image f

/-- Exact mean of a rational-valued statistic of a uniformly chosen word. -/
def mean {n k : ℕ} (g : (Fin k → Fin n) → ℚ) : ℚ :=
  (∑ f : Fin k → Fin n, g f) / (n : ℚ) ^ k

/-- Expected size of the first sample. -/
def expectA (n m : ℕ) : ℚ := mean fun f : Fin m → Fin n => (sample f).card

/-- Expected size of the second sample, conditional on the first sample's distinct count. -/
def expectB (n m : ℕ) : ℚ :=
  mean fun f : Fin m → Fin n =>
    mean fun g : Fin (sample f).card → Fin n => (sample g).card

/-- Expected number of new distinct values in the second sample. -/
def expectDiff (n m : ℕ) : ℚ :=
  mean fun f : Fin m → Fin n =>
    mean fun g : Fin (sample f).card → Fin n => ((sample g) \ (sample f)).card

/-- The exact proposed identity in Sam's question (MathOverflow 267889). -/
def claim : Prop :=
  ∀ (n m : ℕ), 0 < n → expectDiff n m = expectB n m * (1 - expectA n m / n)

theorem main : claim := by
  sorry

end OMA.S_mo_267889
