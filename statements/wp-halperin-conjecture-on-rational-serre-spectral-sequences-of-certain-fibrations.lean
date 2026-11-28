import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Regular.RegularSequence

namespace OMA.S_wp_halperin_conjecture_on_rational_serre_spectral_sequences_of_certain_fibrations

/-- Halperin's conjecture in Meier's equivalent algebraic formulation. A positively
elliptic rational algebra has no nonzero derivation of negative degree. -/
theorem main :
    ∀ (n : ℕ) (weights : Fin n → ℕ)
      (relations : Fin n → MvPolynomial (Fin n) ℚ),
      (∀ i, 0 < weights i ∧ Even (weights i)) →
      (∀ i, ∃ d : ℕ, 0 < d ∧ (relations i).IsWeightedHomogeneous weights d) →
      let relationList := List.ofFn relations
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) ℚ) relationList →
      let I := Ideal.ofList relationList
      let A := MvPolynomial (Fin n) ℚ ⧸ I
      let project := Ideal.Quotient.mk I
      ∀ (drop : ℕ), 0 < drop →
      ∀ D : Derivation ℚ A A,
        (∀ (degree : ℕ) (p : MvPolynomial (Fin n) ℚ),
          p.IsWeightedHomogeneous weights degree →
          (degree < drop → D (project p) = 0) ∧
          (drop ≤ degree → ∃ q : MvPolynomial (Fin n) ℚ,
            q.IsWeightedHomogeneous weights (degree - drop) ∧
            D (project p) = project q)) →
        D = 0 := by
  sorry

end OMA.S_wp_halperin_conjecture_on_rational_serre_spectral_sequences_of_certain_fibrations
