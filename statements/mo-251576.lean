import Mathlib

/-!
# Fixed-size sums of independent uniform permutation matrices

Source: https://mathoverflow.net/questions/251576 (Minkov, CC BY-SA 3.0).
Credit: @connoranderson

Write k=d+1. In an explicit orthonormal frame for the zero-sum subspace,
the compression of the sum, multiplied by sqrt(d/m), converges weakly to
a d by d matrix of independent standard real Gaussians (real Ginibre).
For the sum centered by m times the mean, its characteristic polynomial
has one additional zero root. Literal subtraction of the mean just once
instead leaves the deterministic row sum m-1. In either centering the
action on the zero-sum subspace is identical. We also prove joint weak
convergence of all coefficients of the normalized complementary characteristic
polynomial, which specifies the law of its unordered complex roots.
-/

namespace OMA.S_mo_251576
open Finset Matrix MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators Topology RealInnerProductSpace
noncomputable section

abbrev I (d : ℕ) := Option (Fin d)
abbrev Perm (d : ℕ) := Equiv.Perm (I d)
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)
def permMat {d : ℕ} (π : Perm d) : Matrix (I d) (I d) ℝ :=
  fun i j => if π i = j then 1 else 0
def meanMat (d : ℕ) : Matrix (I d) (I d) ℝ := fun _ _ => ((d:ℝ)+1)⁻¹
def frame (d : ℕ) : Matrix (I d) (Fin d) ℝ := fun i a =>
  let s := (Real.sqrt ((d:ℝ)+1))⁻¹
  match i with
  | none => -s
  | some j => (if j=a then 1 else 0) - (1-s)/d
def entry {d : ℕ} (π : Perm d) (a b : Fin d) : ℝ :=
  ∑ i, frame d i a * frame d (π i) b
def compressed {d m : ℕ} (p : Fin m → Perm d) : Matrix (Fin d) (Fin d) ℝ :=
  fun a b => ∑ j, entry (p j) a b
def observed {d m : ℕ} (p : Fin m → Perm d) : E d :=
  WithLp.toLp 2 fun ab => (Real.sqrt m)⁻¹ * (Real.sqrt d * compressed p ab.1 ab.2)
def law (d m : ℕ) : ProbabilityMeasure (E d) :=
  ⟨((PMF.uniformOfFintype (Fin m → Perm d)).map observed).toMeasure, inferInstance⟩
def coefficients (d : ℕ) (x : E d) (k : Fin (d+1)) : ℝ :=
  (Matrix.charpoly (Matrix.of fun i j : Fin d => x (i,j))).coeff (d-k.val)

theorem main : ∀ d : ℕ, 0 < d →
    (frame d).transpose * frame d = 1 ∧
    (∀ m (p : Fin m → Perm d),
      ((∑ j, permMat (p j)) - (m:ℝ) • meanMat d).charpoly =
        X * (compressed p).charpoly ∧
      ((∑ j, permMat (p j)) - meanMat d).charpoly =
        (X-C ((m:ℝ)-1)) * (compressed p).charpoly ∧
      (∀ i, ∑ j, ((∑ t, permMat (p t)) - meanMat d) i j = (m:ℝ)-1)) ∧
    let G : ProbabilityMeasure (E d) := ⟨stdGaussian (E d), inferInstance⟩
    Tendsto (law d) atTop (𝓝 G) ∧
    ∃ h : Continuous (coefficients d),
      Tendsto (fun m => (law d m).map h.measurable.aemeasurable) atTop
        (𝓝 (G.map h.measurable.aemeasurable)) := by
  sorry
end
end OMA.S_mo_251576
