import Mathlib

/-!
# Positive universal sum of fourth powers with coefficients

Source: https://mathoverflow.net/questions/74932
Credit: @JeremyDevs

Formalizes the conjecture of Will Jagy (MathOverflow 74932, 2011): the 16-variable polynomial
`w₁⁴ + w₂⁴ + w₃⁴ + w₄⁴ + 5 (x₁⁴ + x₂⁴ + x₃⁴ + x₄⁴) + 25 (y₁⁴ + y₂⁴ + y₃⁴ + y₄⁴)
  + 125 (z₁⁴ + z₂⁴ + z₃⁴ + z₄⁴)`
"integrally represents all positive integers".

Conventions:
* "Integrally represents `n`" means that `n` is a value of the polynomial at integer arguments;
  the four blocks of variables are functions `Fin 4 → ℤ`.
* "All positive integers" is `n : ℕ` with `0 < n`, compared in `ℤ`. (`0` is represented
  trivially, so it is left out exactly as in the source.)
-/

namespace OMA.S_mo_74932

/-- Every positive integer is represented over `ℤ` by
`Σ wᵢ⁴ + 5 Σ xᵢ⁴ + 25 Σ yᵢ⁴ + 125 Σ zᵢ⁴` (four variables in each block). -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ w x y z : Fin 4 → ℤ,
      (n : ℤ) = ∑ i, w i ^ 4 + 5 * ∑ i, x i ^ 4 + 25 * ∑ i, y i ^ 4 + 125 * ∑ i, z i ^ 4 := by
  sorry

end OMA.S_mo_74932
