import Mathlib

/-!
# Critical values of one-dimensional phutball and reversal coincidences

Sean A. Irvine's conjecture in https://oeis.org/A037988 uses the partial sums of
https://oeis.org/A272729. We use the defining reversal recurrence from
https://oeis.org/A272727 and Eric Angelini's independent characterization of
the critical values, stated in A037988 and used by Irvine's published program.
Credit: @frido22
-/

namespace OMA.S_oeis_a037988

/-- Count the positions in the preceding prefix that agree with its reversal. -/
def mirror (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter fun j : Fin n =>
    mirror (j : ℕ) = mirror (n-1-(j : ℕ))).card
termination_by n
decreasing_by all_goals have := (‹Fin n›).isLt; omega

/-- Number of occurrences of 2j+1 in A272727, giving A272729(j+1). -/
noncomputable def repetitions (j : ℕ) : ℕ := Set.ncard {t : ℕ | mirror t = 2*j+1}

noncomputable def sums (n : ℕ) : ℕ := ∑ j ∈ Finset.range n, repetitions j

/-- Positive terms are indexed from one, with a zero sentinel. For each selected
value m there are exactly m positive terms at most 2m. -/
def selfCounting (c : ℕ → ℕ) : Prop :=
  c 0 = 0 ∧ StrictMono c ∧ ∀ i : ℕ, 0 < i → c (c i) ≤ 2*c i ∧ 2*c i < c (c i+1)

/-- The lexicographically earliest increasing sequence with the count property. -/
def critical (c : ℕ → ℕ) : Prop :=
  selfCounting c ∧ ∀ f : ℕ → ℕ, selfCounting f →
    ∀ i : ℕ, (∀ j < i, c j = f j) → c i ≤ f i

/-- The partial sums of the reversal multiplicities give exactly the critical values. -/
theorem main : critical sums := by
  sorry

end OMA.S_oeis_a037988
