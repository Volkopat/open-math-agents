import Mathlib

/-!
# Eventual periodicity of greedy irreducible polynomial extensions

Source: Wolfgang, https://mathoverflow.net/questions/149560
Credit: @wtho704

Index zero in the sequence of added coefficients corresponds to degree
one greater than the seed's degree. Positive coefficients are required
so that each extension has the intended degree.
-/

open Polynomial

namespace OMA.S_mo_149560

/-- Append the first `j` coefficients to the seed and view the result over the rationals. -/
noncomputable def partialPolynomial (P : ℤ[X]) (a : ℕ → ℕ) (j : ℕ) : ℚ[X] :=
  P.map (Int.castRingHom ℚ) +
    ∑ i ∈ Finset.range j, C (a i : ℚ) * X ^ (P.natDegree + i + 1)

theorem main : ∀ P : ℤ[X], P.coeff 0 ≠ 0 →
    ∃ a : ℕ → ℕ,
      (∀ j, 0 < a j ∧ Irreducible (partialPolynomial P a (j + 1)) ∧
        ∀ b : ℕ, 0 < b → b < a j →
          ¬ Irreducible (partialPolynomial P a j + C (b : ℚ) * X ^ (P.natDegree + j + 1))) ∧
      ∃ N p : ℕ, 0 < p ∧ ∀ j ≥ N, a (j + p) = a j := by
  sorry

end OMA.S_mo_149560
