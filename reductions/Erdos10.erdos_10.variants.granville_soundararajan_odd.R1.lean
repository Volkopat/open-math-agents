import FormalConjectures.ErdosProblems.«10»

-- Reduction Erdos10.erdos_10.variants.granville_soundararajan_odd.R1 of Erdős Problem 10
-- (Granville–Soundararajan, odd numbers with three powers of two).
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is the conjunction of two covering statements: odd `n > 1` are a prime plus at most
-- three powers of two, and nonzero even `n` are a prime plus at most four powers of two. The two
-- parity classes are handled by completely different arguments, so they are separate steps.

namespace OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1

/-- Every odd `n > 1` is a prime plus a sum of at most three powers of two. -/
def H1 : Prop := {n : ℕ | Odd n ∧ 1 < n} ⊆ Erdos10.sumPrimeAndTwoPows 3

/-- Every nonzero even `n` is a prime plus a sum of at most four powers of two. -/
def H2 : Prop := {n : ℕ | Even n ∧ n ≠ 0} ⊆ Erdos10.sumPrimeAndTwoPows 4

theorem main : H1 → H2 →
    type_of% @Erdos10.erdos_10.variants.granville_soundararajan_odd := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_Erdos10_erdos_10_variants_granville_soundararajan_odd_R1
