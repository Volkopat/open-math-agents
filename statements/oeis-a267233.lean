import Mathlib

/-!
# A267233: four-letter arrays constrained after their first repeated letter
Source: https://oeis.org/A267233
Credit: @etaubman

R. H. Hardin introduced the sequence. Colin Barker conjectured its ordinary
generating function and recurrence. A repeated letter is an adjacent repeat.
If the first pair repeats, both later letters must be smaller. If the middle
pair is the first repeat, only the final letter is constrained. A final-pair
repeat imposes no further condition.
-/

namespace OMA.S_oeis_a267233

def allowed (a b c d : ℕ) : Prop :=
  if a=b then c<a ∧ d<a else if b=c then d<b else True

instance (a b c d : ℕ) : Decidable (allowed a b c d) := by
  unfold allowed
  split <;> first | infer_instance | split <;> infer_instance

def count (n : ℕ) : ℚ :=
  ∑ b ∈ Finset.range (n+1), ∑ a ∈ Finset.range (n+1),
    ∑ c ∈ Finset.range (n+1), ∑ d ∈ Finset.range (n+1),
      if allowed a b c d then 1 else 0

def terms : ℕ → ℚ
  | 0 => 0
  | n+1 => count (n+1)

open PowerSeries

theorem main :
    (∀ n : ℕ, count n = (n:ℚ)^4 + 17/6*n^3 + 2*n^2 + 1/6*n) ∧
    (∀ n : ℕ, terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
      10*terms (n+3) - 5*terms (n+2) + terms (n+1)) ∧
    (1-X)^5 * mk terms = (X * (6 + 17*X + X^2) : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a267233
