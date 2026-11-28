import Mathlib

/-!
# Maximal minors of the coefficient matrix of a generic gradient

The generic homogeneous polynomial has degree m+2, so m ranges over all
degrees at least two after this shift. Its coefficient c_μ is the variable
indexed by μ. The coefficient of x^α in its i-th derivative is
(αᵢ+1)c_(α+eᵢ). An embedding of Fin n selects n distinct columns.

Source: https://mathoverflow.net/questions/301954
Credit: @connoranderson
-/

namespace OMA.S_mo_301954

abbrev MultiIndex (n d : ℕ) := {a : Fin n → ℕ // ∑ i, a i = d}

def raiseIndex {n d : ℕ} (a : MultiIndex n d) (i : Fin n) : MultiIndex n (d+1) :=
  ⟨fun j => a.val j + (if j=i then 1 else 0), by simp [Finset.sum_add_distrib, a.property]⟩

noncomputable def minor {n m : ℕ} (col : Fin n ↪ MultiIndex n (m+1)) :
    Matrix (Fin n) (Fin n) (MvPolynomial (MultiIndex n (m+2)) ℤ) := fun i j =>
  (((col j).val i + 1 : ℕ) : MvPolynomial _ ℤ) * MvPolynomial.X (raiseIndex (col j) i)

theorem main : ∀ (m n : ℕ), 0 < n → ∀ col : Fin n ↪ MultiIndex n (m+1),
    (minor col).det ≠ 0 ∧ ∃ c : MultiIndex n (m+2) → ℤ,
      MvPolynomial.eval c (minor col).det ≠ 0 := by
  sorry

end OMA.S_mo_301954
