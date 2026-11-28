import Mathlib

/-!
# Exact maximum simplex volume in a spherical cap

Source: https://mathoverflow.net/questions/198405 (Roy Han, CC BY-SA 3.0).
Credit: @connoranderson

Use the regular-simplex barycentric model of Euclidean n-space: the affine
hyperplane sum xᵢ=1 in ℝ^(n+1), centered at the uniform vector, with lengths
multiplied by √((n+1)/n). The coordinate vertices then lie on the unit sphere.
Write a row as (1-u, u/n+v₁,…,u/n+vₙ) with sum v=0. Its physical depth
below the north pole is (n+1)u/n. The unit ball inequality is exactly
sum vᵢ² ≤ 2u−(1+1/n)u². The determinant of the matrix of barycentric rows
is its signed volume relative to the coordinate simplex. That simplex has
unscaled edge Gram matrix I+J, of determinant n+1, giving the volume
normalization below. All n+1 rows vary independently, including degenerate
simplices. The lower-dimensional case n=1 is the interval of length ε.

The extremizer in a small cap has a regular base on the rim and the north
pole as apex, as suggested by Moritz Firsching in the source answer.
An enclosing ellipsoid proves optimality. For ε≥1+1/n a full-ball maximizing
regular simplex already fits. The clipped depth q in the formula covers
both regimes.
-/

namespace OMA.S_mo_198405
open Matrix Finset
noncomputable section

abbrev Idx (n : ℕ) := Unit ⊕ Fin n

def shape (n : ℕ) (u : ℝ) : ℝ := 2*u-(1+1/(n:ℝ))*u^2

def admissible (n : ℕ) (ε : ℝ) (u : Idx n → ℝ) (v : Idx n → Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ u i ∧ (n+1 : ℝ)*u i ≤ n*ε ∧ ∑ j, v i j = 0 ∧ ∑ j, (v i j)^2 ≤ shape n (u i)

def bary {n : ℕ} (u : Idx n → ℝ) (v : Idx n → Fin n → ℝ) : Matrix (Idx n) (Idx n) ℝ :=
  Matrix.of fun i j => Sum.elim (fun _ => 1-u i) (fun l => u i/n+v i l) j

def regularVolume (n : ℕ) : ℝ :=
  Real.sqrt (n+1) * (Real.sqrt (((n:ℝ)+1)/n))^n / n.factorial

def volume {n : ℕ} (u : Idx n → ℝ) (v : Idx n → Fin n → ℝ) : ℝ :=
  regularVolume n * |(bary u v).det|

def q (n : ℕ) (ε : ℝ) : ℝ := min 1 ((n:ℝ)*ε/(n+1))

def stretch (n : ℕ) (q : ℝ) : ℝ := Real.sqrt (q*(2*n-(n+1)*q)/(n-1:ℝ))

def optimalVolume (n : ℕ) (ε : ℝ) : ℝ :=
  regularVolume n * (q n ε * (stretch n (q n ε))^(n-1))

theorem main :
    (∀ ε : ℝ, 0 ≤ ε → ε ≤ 2 → Metric.diam (Set.Icc (1-ε) (1:ℝ)) = ε) ∧
    ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 2 →
      IsGreatest {V : ℝ | ∃ (u : Idx n → ℝ) (v : Idx n → Fin n → ℝ),
        admissible n ε u v ∧ volume u v = V} (optimalVolume n ε) := by
  sorry

end
end OMA.S_mo_198405
