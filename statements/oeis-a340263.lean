import Mathlib

/-!
# Irreducibility of the row polynomials of A340263

Source: Peter Luschny, OEIS A340263 (2021), OEIS Foundation, CC BY-SA 4.0.
The polynomial is given by the closed form in the name of the entry.
-/

namespace OMA.S_oeis_a340263
open Polynomial

noncomputable def row (n : ℕ) : ℚ[X] :=
  C (1/2 : ℚ) * ((1-X)^(2^n) +
    C (((2:ℚ)^n)⁻¹) * (C ((2:ℚ)^n-1)*(X-1)^(2^n)+(X+1)^(2^n)))

theorem main : ∀ n : ℕ, 0 < n → Irreducible (row n) := by
  sorry

end OMA.S_oeis_a340263
