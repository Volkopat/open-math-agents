import OMAStatements.S_mo_451483

/-!
Faithful credited port of @connoranderson's complete proof:
https://github.com/connoranderson/open-math-agents/blob/b6e41b777237598b495ef1f0c641788d2038684d/proofs/mo-451483.lean
Linked from merged statement PR #25688 and task-desk DONE #117794.
The mathematical source below is unchanged. This registers prior proof work.
Source: Haimeng Zhao, https://mathoverflow.net/questions/451483 (CC BY-SA 4.0).
Credit Terry Tao and fedja for the endpoint obstruction in the source discussion.
-/

namespace OMA.S_mo_451483
open Complex

noncomputable def unitPoint (x : ℝ) : ℂ := Complex.exp (I*x)

lemma chord (x y : ℝ) : ‖unitPoint x-unitPoint y‖ = 2*|Real.sin ((x-y)/2)| := by
  have h : unitPoint x-unitPoint y = unitPoint y*(unitPoint (x-y)-1) := by
    unfold unitPoint
    rw [mul_sub,mul_one,← Complex.exp_add]
    push_cast
    ring_nf
  rw [h,norm_mul,show ‖unitPoint y‖=1 from Complex.norm_exp_I_mul_ofReal _,one_mul]
  unfold unitPoint
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]

lemma chord_bounds {r : ℝ} (hr : 0<r) (hrπ : r≤Real.pi) {x y : ℝ}
    (hx : |x|≤r) (hy : |y|≤r) :
    Real.sin r/r * |x-y| ≤ ‖unitPoint x-unitPoint y‖ ∧ ‖unitPoint x-unitPoint y‖ ≤ |x-y| := by
  let t := |x-y|/2
  have ht : 0≤t := by dsimp [t]; positivity
  have htr : t≤r := by
    have := abs_sub_le x 0 y
    simp only [sub_zero,zero_sub,abs_neg] at this
    dsimp [t]; linarith
  have hp : |(x-y)/2|=t := by simp [t,abs_div]
  have hsin := strictConcaveOn_sin_Icc.concaveOn.2 (show (0:ℝ)∈Set.Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
    (show r∈Set.Icc 0 Real.pi from ⟨hr.le,hrπ⟩)
    (show 0≤1-t/r by have := (div_le_one hr).mpr htr; linarith)
    (div_nonneg ht hr.le) (show 1-t/r+t/r=1 by ring)
  simp only [smul_eq_mul,Real.sin_zero,mul_zero,zero_add,div_mul_cancel₀ _ hr.ne'] at hsin
  rw [chord]
  constructor
  · rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (hp ▸ htr.trans hrπ),hp]
    have he : |x-y|=2*t := by dsimp [t]; ring
    rw [he]
    calc _ = 2*(t/r*Real.sin r) := by ring
      _ ≤ _ := by linarith
  · have hu := Real.abs_sin_le_abs (x:=(x-y)/2)
    rw [hp] at hu
    dsimp [t] at hu
    linarith

end OMA.S_mo_451483

namespace OMA.S_mo_451483
open Matrix Finset
open scoped Matrix.Norms.L2Operator

private lemma fro_trace {n : ℕ} (A : Mat n) : froSq A = (A * star A).trace.re := by
  simp only [froSq,Matrix.trace,Matrix.diag,Matrix.mul_apply,star_eq_conjTranspose,
    conjTranspose_apply,Complex.star_def,Complex.mul_conj',Complex.re_sum,←Complex.ofReal_pow,Complex.ofReal_re]

private lemma fro_unitaries {n : ℕ} (U V : unitaryGroup (Fin n) ℂ) (T : Mat n) :
    froSq (star (U:Mat n)*T*(V:Mat n)) = froSq T := by
  have hU : (U:Mat n)*star (U:Mat n) = 1 := Unitary.coe_mul_star_self U
  have hV : (V:Mat n)*star (V:Mat n) = 1 := Unitary.coe_mul_star_self V
  rw [fro_trace,fro_trace,star_mul,star_mul,star_star]
  have h : (star (U:Mat n)*T*V)*(star (V:Mat n)*(star T*U)) =
        star (U:Mat n)*(T*star T)*U := by
    calc _ = star (U:Mat n)*T*((V:Mat n)*star (V:Mat n))*star T*U := by simp only [mul_assoc]
      _ = _ := by rw [hV,mul_one];simp only [mul_assoc]
  rw [h,trace_mul_cycle,hU,one_mul]

lemma mixed_fro {n : ℕ} (U V : Matrix.unitaryGroup (Fin n) ℂ) (f g : Fin n → ℂ) :
    froSq (Unitary.conjStarAlgAut ℂ (Mat n) U (Matrix.diagonal f) -
      Unitary.conjStarAlgAut ℂ (Mat n) V (Matrix.diagonal g)) =
      ∑ i, ∑ j, ‖f i-g j‖^2 * ‖((star (U:Mat n)) * (V:Mat n)) i j‖^2 := by
  let W : Mat n := star (U:Mat n)*V
  have hU : star (U:Mat n)*(U:Mat n) = 1 := Unitary.coe_star_mul_self U
  have hV : star (V:Mat n)*(V:Mat n) = 1 := Unitary.coe_star_mul_self V
  rw [←fro_unitaries U V]
  simp only [Unitary.conjStarAlgAut_apply,mul_sub,sub_mul]
  have hf : star (U:Mat n)*((U:Mat n)*diagonal f*star (U:Mat n))*V = diagonal f*W := by
    calc _ = (star (U:Mat n)*U)*diagonal f*W := by simp only [W,mul_assoc]
      _ = _ := by rw [hU,one_mul]
  have hg : star (U:Mat n)*((V:Mat n)*diagonal g*star (V:Mat n))*V = W*diagonal g := by
    calc _ = W*diagonal g*(star (V:Mat n)*V) := by simp only [W,mul_assoc]
      _ = _ := by rw [hV,mul_one]
  rw [hf,hg]
  unfold froSq
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  change ‖(diagonal f*W-W*diagonal g) i j‖^2 = ‖f i-g j‖^2 * ‖W i j‖^2
  rw [Matrix.sub_apply,diagonal_mul,mul_diagonal,mul_comm (W i j) (g j),←sub_mul,norm_mul,mul_pow]

end OMA.S_mo_451483

namespace OMA.S_mo_451483
open Matrix Complex Unitary
open scoped Matrix.Norms.L2Operator

lemma phase_diag {n : ℕ} (v : Fin n → ℝ) :
    phase (diagonal (fun i => (v i:ℂ))) = diagonal (fun i => unitPoint (v i)) := by
  unfold phase
  rw [←diagonal_smul,Matrix.exp_diagonal]
  congr 1
  funext i
  simp [unitPoint,Complex.exp_eq_exp_ℂ,smul_eq_mul]

lemma phase_spectral {n : ℕ} (A : Mat n) (hA : A.IsHermitian) :
    phase A = conjStarAlgAut ℂ (Mat n) hA.eigenvectorUnitary (diagonal (fun i => unitPoint (hA.eigenvalues i))) := by
  let U := hA.eigenvectorUnitary
  let D : Mat n := diagonal (fun i => (hA.eigenvalues i:ℂ))
  have h : A = conjStarAlgAut ℂ (Mat n) U D := hA.spectral_theorem
  change phase A = conjStarAlgAut ℂ (Mat n) U _
  rw [←phase_diag]
  change NormedSpace.exp (I • A) = conjStarAlgAut ℂ (Mat n) U (NormedSpace.exp (I • D))
  rw [h,←map_smul]
  exact Matrix.exp_units_conj (Unitary.toUnits U) (I • D)

lemma scalar_sharp (r : ℝ) (hr : 0<r) (hp : r≤Real.pi) :
    0 < froSq (scalar r - scalar (-r)) ∧
      froSq (phase (scalar r) - phase (scalar (-r))) =
        (Real.sin r/r)^2 * froSq (scalar r - scalar (-r)) := by
  have h1 : froSq (scalar r - scalar (-r)) = (2*r)^2 := by
    simp only [froSq,scalar,Fin.sum_univ_one,Matrix.sub_apply,diagonal_apply_eq,Complex.ofReal_neg,sub_neg_eq_add]
    rw [←Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  rw [h1]
  refine ⟨by positivity,?_⟩
  unfold scalar
  rw [phase_diag,phase_diag]
  simp only [froSq,Fin.sum_univ_one,Matrix.sub_apply,diagonal_apply_eq,chord,sub_neg_eq_add,add_self_div_two,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hr.le hp)]
  field_simp

end OMA.S_mo_451483

namespace OMA.S_mo_451483
open Matrix Finset Unitary
open scoped Matrix.Norms.L2Operator

lemma matrix_bounds (r : ℝ) (hr : 0<r) (hp : r≤Real.pi) (n : ℕ) (A B : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (ha : ∀ i, |hA.eigenvalues i|≤r)
    (hb : ∀ j, |hB.eigenvalues j|≤r) :
    (Real.sin r/r)^2 * froSq (A-B) ≤ froSq (phase A-phase B) ∧
    froSq (phase A-phase B) ≤ froSq (A-B) := by
  let W := star (hA.eigenvectorUnitary : Mat n) * (hB.eigenvectorUnitary : Mat n)
  have hbase : froSq (A-B) = ∑ i,∑ j, |hA.eigenvalues i-hB.eigenvalues j|^2 * ‖W i j‖^2 := by
    calc _ = _ := congrArg₂ (fun P Q : Mat n => froSq (P-Q)) hA.spectral_theorem hB.spectral_theorem
      _ = _ := by
        simpa only [Function.comp_apply,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_sub,
          Complex.norm_real,Real.norm_eq_abs] using mixed_fro hA.eigenvectorUnitary hB.eigenvectorUnitary
          (RCLike.ofReal ∘ hA.eigenvalues) (RCLike.ofReal ∘ hB.eigenvalues)
  have hphase : froSq (phase A-phase B) = ∑ i,∑ j,
      ‖unitPoint (hA.eigenvalues i)-unitPoint (hB.eigenvalues j)‖^2 * ‖W i j‖^2 := by
    rw [phase_spectral A hA,phase_spectral B hB,mixed_fro]
  rw [hbase,hphase]
  have hsin : 0 ≤ Real.sin r/r := div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hr.le hp) hr.le
  constructor
  · simp_rw [mul_sum]
    apply sum_le_sum; intro i _
    apply sum_le_sum; intro j _
    have h := chord_bounds hr hp (ha i) (hb j)
    rw [←mul_assoc,←mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hsin (abs_nonneg _)) h.1 2) (sq_nonneg _)
  · apply sum_le_sum; intro i _
    apply sum_le_sum; intro j _
    have h := chord_bounds hr hp (ha i) (hb j)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h.2 2) (sq_nonneg _)

end OMA.S_mo_451483

theorem OMA.solution : type_of% @OMA.S_mo_451483.main :=
  ⟨OMA.S_mo_451483.matrix_bounds,OMA.S_mo_451483.scalar_sharp⟩
