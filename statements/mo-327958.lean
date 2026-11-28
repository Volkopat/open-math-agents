import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.GCD.Basic

/-!
# Rational formulas for sums of minima and maxima

Source: https://mathoverflow.net/questions/327958/on-sums-of-minima-and-maxima
Credit: @MMexicann
-/

open scoped BigOperators

namespace OMA.S_mo_327958

/-- Sum the minimum of the fractions over all choices of numerators. -/
noncomputable def sumMin {n : ℕ} (h : Fin (n + 1) → ℕ) : ℚ :=
  ∑ r : (i : Fin (n + 1)) → Fin (h i),
    Finset.univ.inf' Finset.univ_nonempty (fun i => ((r i).val : ℚ) / h i)

/-- Sum the maximum of the fractions over the same choices. -/
noncomputable def sumMax {n : ℕ} (h : Fin (n + 1) → ℕ) : ℚ :=
  ∑ r : (i : Fin (n + 1)) → Fin (h i),
    Finset.univ.sup' Finset.univ_nonempty (fun i => ((r i).val : ℚ) / h i)

theorem main :
    ∀ n : ℕ, ∃ pMin qMin pMax qMax : MvPolynomial (Fin (n + 1)) ℚ,
      ∀ h : Fin (n + 1) → ℕ, (∀ i, 0 < h i) → Pairwise (fun i j => (h i).Coprime (h j)) →
        let v : Fin (n + 1) → ℚ := fun i => h i
        MvPolynomial.eval v qMin ≠ 0 ∧ MvPolynomial.eval v qMax ≠ 0 ∧
          sumMin h = MvPolynomial.eval v pMin / MvPolynomial.eval v qMin ∧
          sumMax h = MvPolynomial.eval v pMax / MvPolynomial.eval v qMax := by
  sorry

end OMA.S_mo_327958
