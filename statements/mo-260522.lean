import Mathlib

/-!
# A singular M-matrix without a positive-stable orthogonal polar factor

Source: Astor, https://mathoverflow.net/questions/260522 (CC BY-SA 3.0).
Credit: @connoranderson.

We use column diagonal dominance, as in the source's example and column-sum
condition. The five-cycle Laplacian has successive rates 65536, 4096, 256, 16,
and 1. Every real orthogonal polar factor has a strictly negative quadratic
form on the same vector (2,3,1,−3,−3). Consequently it has an eigenvalue
with strictly negative real part. This applies to every choice of left and
right singular vectors. Optimality of an orthogonal polar factor is compared
to exact rational certificates for one rank-one perturbation.
-/
namespace OMA.S_mo_260522
open Matrix Finset
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def complexify {n : ℕ} (Q : Mat n) := Q.map (algebraMap ℝ ℂ)
def cycleQ : Matrix (Fin 5) (Fin 5) ℚ :=
  !![65536,0,0,0,-1; -65536,4096,0,0,0; 0,-4096,256,0,0;
     0,0,-256,16,0; 0,0,0,-16,1]
noncomputable def cycleExample : Mat 5 := cycleQ.map (Rat.castHom ℝ)
def direction : Fin 5 → ℝ := ![2,3,1,-3,-3]
theorem main :
    (∀ j, 0 < cycleExample j j) ∧
    (∀ i j, i≠j → cycleExample i j ≤ 0) ∧
    (∀ j, (∑ i,cycleExample i j)=0 ∧
      (∑ i ∈ univ.erase j, |cycleExample i j|)=cycleExample j j) ∧
    cycleExample.det=0 ∧ cycleExampleᵀ≠cycleExample ∧
    (∀ Q H : Mat 5, Qᵀ*Q=1 → H.PosSemidef → cycleExample=Q*H →
      direction ⬝ᵥ (Q*ᵥdirection) < 0 ∧ ∃ z∈spectrum ℂ (complexify Q),z.re < 0) ∧
    (∀ (W V : Mat 5) (d : Fin 5 → ℝ), Wᵀ*W=1 → Vᵀ*V=1 → (∀ i, 0≤d i) →
      cycleExample=W*diagonal d*Vᵀ → ∃ z∈spectrum ℂ (complexify (W*Vᵀ)),z.re < 0) := by
  sorry
end OMA.S_mo_260522
