import Mathlib

/-!
# Distinct roots of a polynomial formed from prime factors

Source: user6671, https://mathoverflow.net/questions/261687 (CC BY-SA 3.0).
Credit: @connoranderson.

For at least three distinct prime factors the Mason–Stothers bound is
strict, settling the fourth case asked about in the source. The list
length counts prime factors with multiplicity, and the cardinality of
the finite root set counts distinct complex roots.
-/

namespace OMA.S_mo_261687

open Polynomial

/-- Repetitions in the prime factor list encode prime-power multiplicities. -/
noncomputable def primePoly (K : Type) [Field K] (n : ℕ) : K[X] :=
  (((n.primeFactorsList : Multiset ℕ).map (fun p : ℕ => (p : K))).map (fun z => X-C z)).prod

theorem main :
    ∀ n : ℕ, 3 ≤ n.primeFactors.card →
      n.primeFactorsList.length - n.primeFactors.card + 1 <
        ((primePoly ℂ n)+1).roots.toFinset.card := by
  sorry

end OMA.S_mo_261687
