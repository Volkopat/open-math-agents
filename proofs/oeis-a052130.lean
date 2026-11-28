import OMAStatements.S_oeis_a052130
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a052130.main) := by
  intro h
  have e := (h 2 2 (by decide) (by decide)).2 (by decide) 3 (by decide)
  simp only [OMA.S_oeis_a052130.N, ArithmeticFunction.cardFactors_apply] at e
  exact (by decide +kernel :
    ((Finset.Icc 1 (2 ^ 3)).filter fun k : ℕ => k.primeFactorsList.length = 3 - 2).card ≠
      ((Finset.Icc 1 (2 ^ 2)).filter fun k : ℕ => k.primeFactorsList.length = 2 - 2).card) e