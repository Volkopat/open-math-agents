import Mathlib

/-!
# A spectral lower bound for a Hermitian sum with a complex coefficient

Source: Bullmoose, https://mathoverflow.net/questions/231133 (CC BY-SA 3.0).
Credit: @connoranderson.

For real b the problem is the distance between A and D = -b(B+B*).
Mirsky's trace-norm inequality gives a sharp lower bound in terms of their
ordered eigenvalues. Equality can be attained by aligning their eigenbases.
For nonreal b and fixed H = B+B*, varying the skew-Hermitian part of B reaches
every Hermitian target. Requiring B to be non-Hermitian excludes precisely
the target A + Re(b) H. These conclusions include traceless A and H.
-/

namespace OMA.S_mo_231133
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexConjugate

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

noncomputable def nuclear {n : ℕ} (C : Mat n) : ℝ := (CFC.abs C).trace.re

noncomputable def lower {n : ℕ} {A D : Mat n} (hA : A.IsHermitian) (hD : D.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues₀ i - hD.eigenvalues₀ i|

def mix {n : ℕ} (A : Mat n) (b : ℂ) (B : Mat n) : Mat n := A + b • B + (star b) • Bᴴ

theorem main : ∀ {n : ℕ} (A : Mat n) (hA : A.IsHermitian),
    (∀ (D : Mat n) (hD : D.IsHermitian), lower hA hD ≤ nuclear (A-D) ∧
      ∃ U : Matrix.unitaryGroup (Fin n) ℂ,
        nuclear (A - (U : Mat n)*D*(U : Mat n)ᴴ) = lower hA hD) ∧
    (∀ (s : ℝ) (B : Mat n), mix A (s:ℂ) B = A - (-(s • (B+Bᴴ)))) ∧
    (∀ (b : ℂ), b.im≠0 → ∀ (H T : Mat n), H.IsHermitian → T.IsHermitian →
      ((∃ B : Mat n, B+Bᴴ = H ∧ mix A b B = T ∧ ¬ B.IsHermitian) ↔ T ≠ A+b.re • H)) := by
  sorry

end OMA.S_mo_231133
