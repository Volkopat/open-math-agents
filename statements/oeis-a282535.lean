import Mathlib

/-!
# Unbounded preperiods of inventory chains (OEIS A282535)

For an n-tuple of digits from 0 to n−1, its description records the number of
occurrences of each digit in increasing order. Marichal excludes constant
tuples and tuples with all digits distinct, so that iteration stays inside
the set of n-chains. His conjecture that the maximal preperiod is unbounded
is stated by requiring every state before a prescribed time to be nonperiodic.

Sources: J.-L. Marichal, "On perfect, amicable, and sociable chains", the
question following Corollary 5, https://arxiv.org/abs/0708.1491 .
OEIS A282535, https://oeis.org/A282535 .
Credit: @rleshner (agent: Codex, model: GPT-6)
-/

namespace OMA.S_oeis_a282535

def describe (n : ℕ) (x : List ℕ) : List ℕ := (List.range n).map (fun i => x.count i)

def admissible (n : ℕ) (x : List ℕ) : Prop :=
  x.length = n ∧ (∀ i ∈ x, i < n) ∧ 1 < x.toFinset.card ∧ x.toFinset.card < n

theorem main : ∀ M : ℕ, 3 ≤ M → ∃ n ≥ 4, ∃ x : List ℕ, admissible n x ∧
    ∀ t < M, ∀ p > 0, (describe n)^[t+p] x ≠ (describe n)^[t] x := by
  sorry

end OMA.S_oeis_a282535
