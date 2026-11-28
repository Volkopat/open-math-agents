import FormalConjectures.ErdosProblems.«787»

/-!
Reduction of Erdős Problem 787 (Sanders' lower bound) into two cited inputs.

`Erdos787.erdos_787.variants.sanders` asks for `c > 0` with `(log n)^(1+c) ≤ g ℝ n` eventually.
Sanders [Sa21] proves this bound for sets of integers, and Choi [Ch71] observed that one may assume
`A ⊆ ℤ` without loss of generality (see also `Erdos787.erdos_787.variants.integers`, i.e.
`g ℤ n = g ℝ n`).

The splitting used here is exactly that of the literature: the analytic content is the bound for
integer sets (`H2`), and the remaining input is the transfer from `ℤ` back to `ℝ` (`H1`), which is
the non-trivial direction of Choi's observation. `main` assembles them.
-/

open Filter

namespace OMA.R_Erdos787_erdos_787_variants_sanders_R1

/-- Choi's transfer, in the direction needed for a lower bound: a bound valid for all sets of
`n` integers is also valid for all sets of `n` reals, because a finite set of reals can be replaced
by a Freiman-isomorphic set of integers without changing which subsets are sum-avoiding.
Implied by `g ℤ n = g ℝ n`. -/
def H1 : Prop := ∀ n : ℕ, Erdos787.g ℤ n ≤ Erdos787.g ℝ n

/-- Sanders [Sa21], *The Erdős-Moser sum-free set problem*: the lower bound
`(log n)^(1+c) ≤ g n`, stated for sets of integers. -/
def H2 : Prop := ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Real.log n ^ (1 + c) ≤ (Erdos787.g ℤ n : ℝ)

theorem main : H1 → H2 → type_of% @Erdos787.erdos_787.variants.sanders := by
  intro h1 h2
  obtain ⟨c, hcpos, hc⟩ := h2
  exact ⟨c, hcpos, hc.mono fun n hn => hn.trans (Nat.cast_le.mpr (h1 n))⟩

end OMA.R_Erdos787_erdos_787_variants_sanders_R1
