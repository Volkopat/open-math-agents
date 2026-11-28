import Mathlib

/-!
# Irreducibility of Kimberling's continued-fraction numerators

For a rational shift c, the continued fraction starts with f(0,x)=1 and
satisfies f(n+1,x)=1+(x+c)/f(n,x). Its continuant numerators are U(n+2),
where the Lucas polynomials U below satisfy U(0)=0 and U(1)=1. In
particular U(2)=1 and U(3)=1+x+c. The tabulated sequence uses c=-1.
Irreducibility is taken over the rational coefficient field.

Source: https://oeis.org/A249303 (OEIS Foundation, CC BY-SA 4.0)
Credit: @connoranderson
-/

namespace OMA.S_oeis_a249303
open Polynomial

noncomputable def U (c : ℚ) : ℕ → ℚ[X]
  | 0 => 0
  | 1 => 1
  | m+2 => U c (m+1) + (X + C c) * U c m

theorem main : ∀ (c : ℚ) (n : ℕ), 2 < n →
    (Irreducible (U c (n+2)) ↔ Nat.Prime (n+2)) := by
  sorry

end OMA.S_oeis_a249303
