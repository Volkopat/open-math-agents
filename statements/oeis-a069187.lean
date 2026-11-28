import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Sqrt

/-! OEIS A069187. For positive n, the squarefree part is the unique
squarefree d with n = m²*d. The conjectured polynomial description is
stated as printed. Its exceptional first term is relevant to the verdict.
Source: https://oeis.org/A069187
Credit: @DomTheDeveloper -/

namespace OMA.S_oeis_a069187

theorem main : ∀ n : ℕ, 0 < n →
    ((∃ m d : ℕ, Squarefree d ∧ n = m^2*d ∧ d = (n-1).sqrt+1) ↔
      ∃ m : ℕ, 0 < m ∧ Squarefree (m^2+1) ∧ n = m^2*(m^2+1)) := by
  sorry

end OMA.S_oeis_a069187
