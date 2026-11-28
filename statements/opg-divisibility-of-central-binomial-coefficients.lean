import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Set.Finite.Basic

/-!
# Divisibility of central binomial coefficients

Source: https://www.openproblemgarden.org/op/divisibility_of_central_binomial_coefficients
Credit: @yakataN

The source states two problems, both included here with its positive-integer convention.
Nat.centralBinom n is the binomial coefficient (2*n choose n).
The first problem is also recorded upstream as Erdos376.erdos_376; the second
asks for finiteness after adding the prime 11, rather than infinitude.
The stronger exact list mentioned in the source's discussion is not asserted here.
-/

namespace OMA.S_opg_divisibility_of_central_binomial_coefficients

/-- The two displayed problems of Graham, in their order on the source page. -/
theorem main :
    {n : ℕ | 0 < n ∧ n.centralBinom.Coprime (3 * 5 * 7)}.Infinite ∧
      {n : ℕ | 0 < n ∧ n.centralBinom.Coprime (3 * 5 * 7 * 11)}.Finite := by
  sorry

end OMA.S_opg_divisibility_of_central_binomial_coefficients
