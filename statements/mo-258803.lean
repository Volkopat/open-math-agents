import Mathlib

/-!
# Sharp trace-norm bounds from a finite net on the Euclidean unit sphere

Source: user58955, https://mathoverflow.net/questions/258803 (CC BY-SA 3.0).
Anthony Quas's comment gives the qualitative rank-one cap construction.
Sharp constants and the constrained optimum by @connoranderson.

For a net of chordal radius ε, the corresponding angular radius has cosine
1−ε²/2. The theorem gives the infimum of the nuclear norm in every positive
dimension. If √n exceeds the reciprocal sine of that angular radius, the
least possible nuclear norm under the extra Frobenius constraint is √n.

The roots of the characteristic polynomial of TᵀT are its nonnegative real
eigenvalues with multiplicity. Their square roots give the singular values.
-/

namespace OMA.S_mo_258803
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)
def net {n : ℕ} (N : Finset (E n)) (ε : ℝ) : Prop :=
  (∀ y ∈ N, ‖y‖=1) ∧ ∀ x : E n, ‖x‖=1 → ∃ y∈N, dist x y ≤ ε
noncomputable def sineRadius (ε : ℝ) : ℝ := Real.sqrt (1-(1-ε^2/2)^2)
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def nuclear {n : ℕ} (T : Mat n) : ℝ :=
  (((T.conjTranspose*T).charpoly.roots).map Real.sqrt).sum
noncomputable def frobeniusSq {n : ℕ} (T : Mat n) : ℝ := (T.conjTranspose*T).trace
def matrixPass {n : ℕ} (ε : ℝ) (T : Mat n) : Prop :=
  ∃ N : Finset (E n), net N ε ∧ ∀ y ∈ N, 1 ≤ ‖T.toEuclideanLin y‖
noncomputable def matrixValues (n : ℕ) (ε : ℝ) : Set ℝ :=
  {S | ∃ T : Mat n, matrixPass ε T ∧ nuclear T=S}
theorem main : ∀ {n : ℕ}, 0<n → ∀ {ε : ℝ}, 0<ε → ε<1 →
    IsGLB (matrixValues n ε) (min (n:ℝ) (1/sineRadius ε)) ∧
    (1/sineRadius ε < Real.sqrt n →
      IsLeast {S : ℝ | ∃ T : Mat n, matrixPass ε T ∧ (n:ℝ) ≤ frobeniusSq T ∧ nuclear T=S} (Real.sqrt n)) := by
  sorry
end OMA.S_mo_258803
