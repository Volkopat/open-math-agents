import Mathlib

/-!
# Zhi-Wei Sun's four derangement identities at roots of unity

Source: https://mathoverflow.net/questions/403025 (Zhi-Wei Sun, CC BY-SA 4.0).
Credit: @connoranderson

Indices begin at zero in Lean. Simultaneously shifting all row and column indices
by one preserves the integer differences in the powers of the primitive root.
-/

namespace OMA.S_mo_403025

noncomputable def derangementSum (m : ℕ) (ζ : ℂ) (signed : Bool) : ℂ := by
  classical
  exact ∑ τ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => ∀ j, τ j ≠ j),
    (if signed then (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) else 1) *
      ∏ j, (1 - ζ ^ ((j.val : ℤ) - ((τ j).val : ℤ)))⁻¹

theorem main : ∀ (n : ℕ) (ζ : ℂ), 1 < n → IsPrimitiveRoot ζ n →
    (Even n →
      derangementSum n ζ false = (Nat.doubleFactorial (n-1) : ℂ)^2 / 2^n ∧
      derangementSum n ζ true = (-1 : ℂ)^(n/2) * (Nat.doubleFactorial (n-1) : ℂ)^2 / 2^n) ∧
    (Odd n →
      derangementSum (n-1) ζ false = (Nat.factorial ((n-1)/2) : ℂ)^2 / n ∧
      derangementSum (n-1) ζ true =
        (-1 : ℂ)^((n-1)/2) * (Nat.factorial ((n-1)/2) : ℂ)^2 / n) := by
  sorry

end OMA.S_mo_403025
