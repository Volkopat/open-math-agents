import Mathlib

/-!
# Derivatives of the geometric sum at modular roots of unity

Source: https://mathoverflow.net/questions/315652 . Glasby states the exact
vanishing criterion for the k-th ordinary derivative, evaluated at an integer
whose n-th power is 1 modulo n. The third alternative takes p = k+1.

Credit: @connoranderson
-/

namespace OMA.S_mo_315652
open Polynomial

noncomputable def geometric (n : ℕ) : ℤ[X] := ∑ i ∈ Finset.range n, X^i

theorem main : ∀ n k : ℕ, 1≤n → k≤n → ∀ a : ℤ, a^n ≡ 1 [ZMOD (n:ℤ)] →
    (((n:ℤ) ∣ (derivative^[k] (geometric n)).eval a) ↔
      (k+1 ≠ 4 ∧ ¬(k+1).Prime) ∨ (k+1 = 4 ∧ ¬4 ∣ n) ∨
        ((k+1).Prime ∧ (¬(k+1) ∣ n ∨ ¬a ≡ 1 [ZMOD ((k+1:ℕ):ℤ)]))) := by
  sorry

end OMA.S_mo_315652
