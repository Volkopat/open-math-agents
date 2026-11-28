import Mathlib.LinearAlgebra.Matrix.Circulant
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# A052182: a circulant determinant as a polynomial resultant

Irwin's identity holds in positive dimensions, the range of the original
sequence when the identity was proposed in 2016. OEIS prepended the value
at dimension zero in 2026. The matrix below starts with the row `1, …, n`
and shifts it one position to the right at each subsequent row.

OEIS entry: https://oeis.org/A052182
Proof by Sela Fried: https://oeis.org/A052182/a052182.pdf
-/

namespace OMA.S_oeis_a052182

open Finset Polynomial

def circulantMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  (Matrix.circulant (fun i : Fin n => (i.val : ℤ) + 1)).transpose

noncomputable def weightedSum (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Icc 1 n, C (k : ℤ) * X ^ k

theorem main : ∀ n : ℕ, 0 < n →
    (circulantMatrix n).det = -Polynomial.resultant (weightedSum n) (X ^ n - 1) := by
  sorry

end OMA.S_oeis_a052182
