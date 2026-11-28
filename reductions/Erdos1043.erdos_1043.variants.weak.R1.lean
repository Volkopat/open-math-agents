import FormalConjectures.ErdosProblems.«1043»

/-! The pairwise-distance product on a monic polynomial lemniscate has
subexponential growth on the n² scale. This is the upper bound on its
logarithmic capacity, obtained directly from Vandermonde determinants. -/
noncomputable section
namespace OMA.Capacity1043
open Polynomial Finset Filter

theorem compact (f : ℂ[X]) (hd : 1 ≤ f.degree) : IsCompact (Erdos1043.levelSet f) := by
  have h := (f.isProperMap_eval (lt_of_lt_of_le (by simp) hd)).isCompact_preimage
    (isCompact_closedBall (0:ℂ) 1)
  simpa [Erdos1043.levelSet,Metric.closedBall,Set.preimage,dist_zero_right] using h

private theorem determinant {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {B : ℝ}
    (hB : 0 ≤ B) (entries : ∀ i j, ‖M i j‖ ≤ B) : ‖M.det‖ ≤ ((n:ℝ)*B)^n := by
  rw [Matrix.det_apply]
  refine (norm_sum_le ..).trans ?_
  calc ∑ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖
      ≤ ∑ _σ : Equiv.Perm (Fin n), B^n := by
        apply sum_le_sum; intro σ _
        rw [norm_units_zsmul,Complex.norm_prod]
        simpa using (prod_le_prod (s:=univ) (f:=fun i => ‖M (σ i) i‖)
          (g:=fun _ => B) (fun _ _ => norm_nonneg _) (fun i _ => entries (σ i) i))
    _ = (n.factorial : ℝ)*B^n := by simp [Fintype.card_perm]
    _ ≤ ((n:ℝ)*B)^n := by
      rw [mul_pow]
      gcongr
      exact_mod_cast Nat.factorial_le_pow n

theorem cap (f : ℂ[X]) (mon : f.Monic) (hd : 1 ≤ f.degree) :
    ∀ c : ℝ, 1 < c → ∀ᶠ n : ℕ in atTop,
    ∀ z : Fin n → ℂ, (∀ i, z i ∈ Erdos1043.levelSet f) →
      (∏ i, ∏ j ∈ Ioi i, ‖z j-z i‖) ≤ c^(n^2) := by
  let d := f.natDegree
  have dp : 0 < d := (natDegree_pos_iff_degree_pos).mpr (lt_of_lt_of_le (by simp) hd)
  obtain ⟨R,hR⟩ := (compact f hd).isBounded.exists_norm_le
  let A := max 1 R
  have age : 1 ≤ A := le_max_left ..
  let B := A^d
  have bp : 0 < B := pow_pos (by linarith) _
  intro c hc
  filter_upwards [(isLittleO_coe_const_pow_of_one_lt (R:=ℝ) hc).def (one_div_pos.mpr bp)] with n bound
  have cp : 0 ≤ c := by linarith
  have sc : (n:ℝ)*B ≤ c^n := by
    simpa [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) n),
      abs_of_nonneg cp, one_div, ←div_eq_inv_mul,le_div_iff₀ bp] using bound
  intro z hz
  let P (j : Fin n) : ℂ[X] := X^(j.val%d)*f^(j.val/d)
  have mono (j : Fin n) : (P j).Monic := (monic_X_pow _).mul (mon.pow _)
  have deg (j : Fin n) : (P j).natDegree=j.val := by
    dsimp only [P]
    rw [natDegree_X_pow_mul _ (pow_ne_zero _ mon.ne_zero),natDegree_pow]
    simpa [d,mul_comm,add_comm] using Nat.mod_add_div j.val d
  have entries (i j : Fin n) : ‖(P j).eval (z i)‖ ≤ B := by
    have fbound : ‖f.eval (z i)‖ ≤ 1 := hz i
    have zbound := (hR _ (hz i)).trans (le_max_right 1 R)
    have pw : ‖f.eval (z i)‖^(j.val/d) ≤ 1 := pow_le_one₀ (norm_nonneg _) fbound
    simp only [P,eval_mul,eval_pow,eval_X,norm_mul,norm_pow]
    calc ‖z i‖^(j.val%d)*‖f.eval (z i)‖^(j.val/d)
        ≤ A^(j.val%d)*1 := mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) zbound _) pw
          (by positivity) (by positivity)
      _ ≤ B := by rw [mul_one]; exact pow_le_pow_right₀ age (Nat.mod_lt _ dp).le
  have eq := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde z P deg mono
  have major := determinant (Matrix.of fun i j => (P j).eval (z i)) bp.le entries
  rw [←eq,Matrix.det_vandermonde] at major
  simp only [Complex.norm_prod] at major
  refine major.trans ?_
  simpa only [←pow_mul,sq] using pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) bp.le) sc n

end OMA.Capacity1043
end

/- Following Ch. Pommerenke, *On metric properties of complex polynomials*
(1961), Theorem 7. The geometric input is the finite-cover theorem of his
*Einige Sätze über die Kapazität ebener Mengen* (1960), Satz 2.
The perimeter threshold 10.361 leaves room to polygonalize the convex curves
of total length <10.36. -/
namespace OMA.R_Erdos1043_erdos_1043_variants_weak_R1
open Finset Filter OMA.Capacity1043 MeasureTheory
open scoped NNReal ENNReal

/-- Finite enclosure theorem for compact sets of logarithmic capacity at most one. -/
def H1 : Prop := ∀ K : Set ℂ, IsCompact K → (∀ c : ℝ, 1 < c → ∀ᶠ n : ℕ in atTop,
    ∀ z : Fin n → ℂ, (∀ i, z i ∈ K) →
      (∏ i, ∏ j ∈ Ioi i, ‖z j-z i‖) ≤ c^(n^2)) →
    ∃ (m : ℕ) (n : Fin m → ℕ) (v : Fin m → ℕ → ℂ),
      (∀ i, v i (n i) = v i 0) ∧ K ⊆ ⋃ i, convexHull ℝ (v i '' Set.Iic (n i)) ∧
        (∑ i, ∑ j ∈ range (n i), ‖v i (j+1)-v i j‖) ≤ (10.361 : ℝ)

/-- Projection inequality for an arbitrary polygonal enclosure. -/
def H2 : Prop := ∀ (K : Set ℂ) (m : ℕ) (n : Fin m → ℕ) (v : Fin m → ℕ → ℂ)
    (C : ℝ), (∀ i, v i (n i) = v i 0) →
    K ⊆ ⋃ i, convexHull ℝ (v i '' Set.Iic (n i)) →
    (∑ i, ∑ j ∈ range (n i), ‖v i (j+1)-v i j‖) < Real.pi*C →
    ∃ u : ℂ, ‖u‖ = 1 ∧ volume ((ℝ ∙ u).orthogonalProjectionOnto '' K) ≤ ENNReal.ofReal C

theorem main : H1 → H2 → type_of% @Erdos1043.erdos_1043.variants.weak := by
  intro enclose project f mon degree
  obtain ⟨m,n,v,closed,covers,cost⟩ := enclose _ (compact f degree) (cap f mon degree)
  obtain ⟨u,unit,bound⟩ := project _ m n v 3.3 closed covers (cost.trans_lt (by linarith [Real.pi_gt_d4]))
  refine ⟨u,unit,bound.trans (le_of_eq ?_)⟩
  change ((Real.toNNReal 3.3 : ℝ≥0) : ℝ≥0∞) = ((3.3 : ℝ≥0) : ℝ≥0∞)
  apply congrArg ENNReal.ofNNReal
  apply NNReal.eq
  change max (3.3 : ℝ) 0 = ((3.3 : ℝ≥0) : ℝ)
  norm_num

end OMA.R_Erdos1043_erdos_1043_variants_weak_R1
