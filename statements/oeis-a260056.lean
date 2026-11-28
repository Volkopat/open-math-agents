import Mathlib.Algebra.Polynomial.Coeff

/-!
# Two conjectures on the polynomial triangle OEIS A260056

Sources: https://oeis.org/A260056 and https://oeis.org/A004524.
Werner Schulte's row polynomial determines every entry, including zeros
past the end of each row. In the alternating antidiagonal the column-zero
entry has positive sign. A004524 at index j is j/4 + (j+1)/4 with each
division rounded down.
-/

namespace OMA.S_oeis_a260056

open Polynomial

noncomputable def row (n : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range (n + 1), (1 + Polynomial.X + Polynomial.X ^ 2) ^ j

noncomputable def T (n k : ℕ) : ℤ := (row n).coeff k

theorem main :
    (∀ n : ℕ, (∑ k ∈ Finset.range (n + 1), (-1 : ℤ)^k * T (n-k) k) =
      (((n+3)/4 + (n+4)/4 : ℕ) : ℤ)) ∧
    (∀ n k : ℕ, (∑ m ∈ Finset.range (k + 3),
      (-1 : ℤ)^m * T (n+m) k * ((k+2).choose m : ℤ)) = 0) := by
  sorry

end OMA.S_oeis_a260056
