import Mathlib

/-!
# Irreducibility of a family of palindromic integer polynomials

Source: https://mathoverflow.net/questions/371405, CC BY-SA 4.0.
Credit: @connoranderson

The squared geometric sum gives the triangular coefficients. Adding twice the
middle monomial raises its coefficient from n+1 to n+3. This is the equivalent
form noted by Max Alekseyev in the source discussion.
-/

namespace OMA.S_mo_371405
open Polynomial

noncomputable def geometric (n : ℕ) : ℤ[X] := ∑ k ∈ Finset.range (n+1), X^k

noncomputable def palindromic (n : ℕ) : ℤ[X] := (geometric n)^2 + C 2 * X^n

theorem main : ∀ n : ℕ, 0 < n → Irreducible (palindromic n) := by
  sorry

end OMA.S_mo_371405
