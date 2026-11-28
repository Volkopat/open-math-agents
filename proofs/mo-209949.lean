import OMAStatements.S_mo_209949

/-!
Credited port of @connoranderson's complete public proof, linked from merged statement
PR #21291, pinned at:
https://github.com/connoranderson/open-math-agents/blob/bc13fddc9f1ad8880eef559c20b33cd94762a192/proofs/mo-209949.lean
All mathematical code is retained unchanged. This integrates prior proof work,
not a claim of a new mathematical discovery. The final derivative implication
has no differentiable unequal-slope case: differentiability at the midpoint
forces equal slopes, contradicting its c != d hypothesis.
-/

/-!
The two endpoint jets determine the Bernstein coefficients exactly. In a unit
coordinate, each coefficient takes its value from the left or right tangent
according to whether its index is below or above half the degree. Subtracting
the jump from the right tangent leaves a continuous piecewise affine function,
so its Bernstein polynomials converge uniformly. The remaining step function
is controlled off center by the binomial variance, and at the midpoint by
symmetry and a bound for the central binomial mass. This also determines when
the limit is continuous and when it can be differentiable at the midpoint.

Michael Renardy observed the discontinuous step limit when the given slopes
are zero in https://mathoverflow.net/a/209992 .
-/

namespace OMA.S_mo_209949
open Polynomial
/-- The endpoint conditions used in the convergence statement always admit a polynomial. -/
lemma endpoint_conditions_exist (n : ℕ) (a b A B c d : ℝ) (hab : a < b) :
    ∃ p : ℝ[X], EndpointConditions n a b A B c d p := by
  let l : ℝ[X] := (X-C a)^(n/2+1)
  let r : ℝ[X] := (X-C b)^(n-n/2)
  let L := tangentLine a A c
  let R := tangentLine b B d
  have cop : IsCoprime l r := (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab.ne).isUnit).pow
  obtain ⟨u,v,huv⟩ := cop
  let y := L+u*l*(R-L)
  have ml : l.Monic := (monic_X_sub_C a).pow _
  have mr : r.Monic := (monic_X_sub_C b).pow _
  have deg : (l*r).natDegree = n+1 := by
    rw [natDegree_mul ml.ne_zero mr.ne_zero]
    simp only [l,r,natDegree_pow,natDegree_X_sub_C,mul_one]
    omega
  have ne : l*r ≠ 1 := by intro h; simp [h] at deg
  refine ⟨y %ₘ (l*r), ?_, ?_, ?_⟩
  · have hh := natDegree_modByMonic_lt y (ml.mul mr) ne
    omega
  · refine ⟨u*(R-L) - r*(y /ₘ (l*r)),?_⟩
    rw [modByMonic_eq_sub_mul_div]
    change (L+u*l*(R-L))-l*r*(y /ₘ (l*r))-L = _
    ring
  · refine ⟨-v*(R-L)-l*(y /ₘ (l*r)),?_⟩
    rw [modByMonic_eq_sub_mul_div]
    change (L+u*l*(R-L))-l*r*(y /ₘ (l*r))-R = _
    linear_combination (R-L)*huv
end OMA.S_mo_209949

namespace OMA.S_mo_209949
open Polynomial Finset

noncomputable def sample (n : ℕ) (v : Fin (n+1) → ℝ) : ℝ[X] :=
  ∑ k, C (v k) * bernsteinPolynomial ℝ n k

noncomputable def grid (n : ℕ) (k : Fin (n+1)) : ℝ := k.val/n

noncomputable def candidate (n : ℕ) (L M : ℝ → ℝ) : ℝ[X] :=
  sample n (fun k => if 2*k.val ≤ n then L (grid n k) else M (grid n k))

lemma sample_affine {n : ℕ} (hn : 0 < n) (a b : ℝ) :
    sample n (fun k => a+b*grid n k) = C a + C b*X := by
  have hsum : (∑ k : Fin (n+1), bernsteinPolynomial ℝ n k) = 1 := by
    simpa only [← Finset.sum_range] using bernsteinPolynomial.sum ℝ n
  have hmoment : (∑ k : Fin (n+1), k.val • bernsteinPolynomial ℝ n k) = n • (X:ℝ[X]) := by
    simpa only [Finset.sum_range] using bernsteinPolynomial.sum_smul ℝ n
  have hh : (∑ k : Fin (n+1), C (grid n k)*bernsteinPolynomial ℝ n k) = X := by
    calc
      _ = C (n:ℝ)⁻¹ * ∑ k : Fin (n+1), k.val • bernsteinPolynomial ℝ n k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
        simp [grid,div_eq_mul_inv,nsmul_eq_mul]; ring
      _ = _ := by rw [hmoment]; simp [nsmul_eq_mul,← mul_assoc]
                  change C (n:ℝ)⁻¹ * C (n:ℝ) = 1
                  rw [← map_mul,inv_mul_cancel₀ (by exact_mod_cast hn.ne'),map_one]
  unfold sample; simp only [map_add,map_mul,add_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum,hsum,hh,mul_one]

lemma sample_sub (n : ℕ) (v w : Fin (n+1) → ℝ) : sample n v - sample n w = sample n (fun k => v k-w k) := by
  simp [sample,map_sub,sub_mul,Finset.sum_sub_distrib]

lemma sample_degree (n : ℕ) (v : Fin (n+1) → ℝ) : (sample n v).natDegree ≤ n := by
  apply natDegree_sum_le_of_forall_le
  intro k _
  unfold bernsteinPolynomial
  have hk := k.is_le
  compute_degree; omega

lemma candidate_identified (n : ℕ) (hn : 0 < n) (a b c d : ℝ) (P : ℝ[X]) (hP : P.natDegree ≤ n)
    (hl : X^(n/2+1) ∣ P-(C a+C b*X)) (hr : (1-X)^(n-n/2) ∣ P-(C c+C d*X)) :
    P = candidate n (fun t => a+b*t) (fun t => c+d*t) := by
  classical
  let L (t : ℝ) := a+b*t
  let R (t : ℝ) := c+d*t
  let Q := candidate n L R
  have ql : X^(n/2+1) ∣ Q-(C a+C b*X) := by
    rw [← sample_affine hn]; change _ ∣ sample n _ - sample n _; rw [sample_sub]
    apply Finset.dvd_sum
    intro k _
    by_cases hk : 2*k.val ≤ n
    · simp [hk,L]
    · simp only [hk,ite_false]; unfold bernsteinPolynomial
      exact (pow_dvd_pow (X : ℝ[X]) (show n/2+1 ≤ k.val by omega)).trans (by apply dvd_mul_of_dvd_right; apply dvd_mul_of_dvd_left; exact dvd_mul_left _ _)
  have qr : (1-X)^(n-n/2) ∣ Q-(C c+C d*X) := by
    rw [← sample_affine hn]; change _ ∣ sample n _ - sample n _; rw [sample_sub]
    apply Finset.dvd_sum
    intro k _
    by_cases hk : 2*k.val ≤ n
    · simp only [hk,ite_true]; unfold bernsteinPolynomial
      exact (pow_dvd_pow (1-X : ℝ[X]) (show n-n/2 ≤ n-k.val by omega)).trans (by apply dvd_mul_of_dvd_right; exact dvd_mul_left _ _)
    · simp [hk,R]
  have cop : IsCoprime (X:ℝ[X]) (1-X) := ⟨1,1,by ring⟩
  have dvd1 : X^(n/2+1) ∣ P-Q := by simpa using dvd_sub hl ql
  have dvd2 : (1-X)^(n-n/2) ∣ P-Q := by simpa using dvd_sub hr qr
  have dvd := cop.pow.mul_dvd dvd1 dvd2
  change P = Q
  by_contra hz
  have deg := natDegree_le_of_dvd dvd (sub_ne_zero.mpr hz)
  have dX : (1-X : ℝ[X]).natDegree = 1 := by compute_degree; norm_num
  have nX : (1-X : ℝ[X]) ≠ 0 := by intro h; simp [h] at dX
  rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ nX),natDegree_pow,natDegree_pow,natDegree_X,dX,mul_one,mul_one] at deg
  have qu : Q.natDegree ≤ n := sample_degree _ _
  have dp := natDegree_sub_le P Q
  omega

lemma normalized_identified {n : ℕ} {a b A B c d : ℝ} {P : ℝ[X]} (hn : 3 ≤ n)
    (h : EndpointConditions n a b A B c d P) :
    P.comp (C a + C (b-a)*X) = candidate n (fun t => A+(c*(b-a))*t)
      (fun t => (B-d*(b-a))+(d*(b-a))*t) := by
  let T : ℝ[X] := C a + C (b-a)*X
  apply candidate_identified n (by omega)
  · have hT : T.natDegree ≤ 1 := by dsimp [T]; compute_degree
    change (P.comp T).natDegree ≤ n
    exact natDegree_comp_le.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul h.1 hT)
  · obtain ⟨Q,hQ⟩ := h.2.1
    refine ⟨C (b-a)^(n/2+1)*Q.comp T, ?_⟩
    have hh := congrArg (fun p : ℝ[X] => p.comp T) hQ
    simp only [sub_comp,mul_comp,pow_comp,C_comp,X_comp,tangentLine,add_comp] at hh
    dsimp [T] at hh ⊢
    simp only [add_sub_cancel_left,mul_pow,map_mul] at hh ⊢
    linear_combination hh
  · obtain ⟨Q,hQ⟩ := h.2.2
    refine ⟨C (a-b)^(n-n/2)*Q.comp T, ?_⟩
    have hh := congrArg (fun p : ℝ[X] => p.comp T) hQ
    simp only [sub_comp,mul_comp,pow_comp,C_comp,X_comp,tangentLine,add_comp] at hh
    have eqn : T-C b = C (a-b)*(1-X) := by dsimp [T]; simp [map_sub]; ring
    rw [eqn,mul_pow] at hh
    dsimp [T] at hh ⊢
    simp only [map_sub,map_mul] at hh ⊢
    linear_combination hh

end OMA.S_mo_209949

namespace OMA.S_mo_209949
open Filter Set Finset
open scoped unitInterval Topology

/-- Bernstein approximation to the indicator of the upper half-interval. -/
noncomputable def step (n : ℕ) (x : I) : ℝ :=
  ∑ k : Fin (n+1), if n < 2*k.val then bernstein n k x else 0
noncomputable def lower (n : ℕ) (x : I) : ℝ :=
  ∑ k : Fin (n+1), if 2*k.val ≤ n then bernstein n k x else 0

theorem step_add_lower (n : ℕ) (x : I) : step n x + lower n x = 1 := by
  rw [step,lower,← Finset.sum_add_distrib,← bernstein.probability n x]
  apply Finset.sum_congr rfl
  intro k _; by_cases hk : n < 2*k.val <;> simp [hk,Nat.le_of_not_gt,not_le_of_gt]

theorem step_nonneg (n : ℕ) (x : I) : 0 ≤ step n x := Finset.sum_nonneg (fun k _ => by split <;> positivity)
theorem lower_nonneg (n : ℕ) (x : I) : 0 ≤ lower n x := Finset.sum_nonneg (fun k _ => by split <;> positivity)

private theorem tail_tendsto (x : I) (d : ℝ) (hd : 0 < d) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n ≠ 0, d^2*a n ≤ (x:ℝ)*(1-x)/n) :
    Tendsto a atTop (𝓝 0) := by
  have hup : Tendsto (fun n : ℕ => ((x:ℝ)*(1-x)/n)/d^2) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat ((x:ℝ)*(1-x))).div_const (d^2)
  apply squeeze_zero' (Eventually.of_forall ha) _ hup
  filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
  exact (le_div_iff₀ (sq_pos_of_pos hd)).mpr (by simpa [mul_comm] using hb n hn)

theorem step_left (x : I) (hx : (x:ℝ) < 1/2) : Tendsto (fun n => step n x) atTop (𝓝 0) := by
  apply tail_tendsto x (1/2-x) (sub_pos.mpr hx) _ (fun n => step_nonneg n x)
  intro n hn
  rw [step,Finset.mul_sum,← bernstein.variance hn x]
  apply Finset.sum_le_sum
  intro k _
  split_ifs with hk
  · apply mul_le_mul_of_nonneg_right _ bernstein_nonneg
    have zhi : (1/2 : ℝ) ≤ bernstein.z k := by
      change (1/2 : ℝ) ≤ (k.val:ℝ)/n
      rw [le_div_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)]; linarith [show (n:ℝ) < 2*k.val by exact_mod_cast hk]
    nlinarith [mul_nonneg (sub_nonneg.mpr zhi) (show 0 ≤ ((bernstein.z k:ℝ)-x)+(1/2-x) by linarith)]
  · simp only [mul_zero]; positivity

theorem step_right (x : I) (hx : (1/2 : ℝ) < x) : Tendsto (fun n => step n x) atTop (𝓝 1) := by
  have hl : Tendsto (fun n => lower n x) atTop (𝓝 0) := by
    apply tail_tendsto x (x-1/2) (sub_pos.mpr hx) _ (fun n => lower_nonneg n x)
    intro n hn
    rw [lower,Finset.mul_sum,← bernstein.variance hn x]
    apply Finset.sum_le_sum
    intro k _
    split_ifs with hk
    · apply mul_le_mul_of_nonneg_right _ bernstein_nonneg
      have zlo : (bernstein.z k:ℝ) ≤ 1/2 := by
        change (k.val:ℝ)/n ≤ 1/2
        rw [div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hn)]; linarith [show 2*(k.val:ℝ) ≤ n by exact_mod_cast hk]
      nlinarith [mul_nonneg (sub_nonneg.mpr zlo) (show 0 ≤ ((x:ℝ)-bernstein.z k)+(x-1/2) by linarith)]
    · simp only [mul_zero]; positivity
  have h (n : ℕ) : step n x = 1-lower n x := by linarith [step_add_lower n x]
  simpa [h] using (tendsto_const_nhds (x:=(1:ℝ))).sub hl

end OMA.S_mo_209949

namespace OMA.S_mo_209949
open Filter Set Finset
open scoped unitInterval Topology

noncomputable def center (n : ℕ) : ℝ := (n.centralBinom:ℝ)/4^n
noncomputable def half : I := ⟨1/2,by constructor <;> norm_num⟩

lemma center_nonneg (n : ℕ) : 0 ≤ center n := by unfold center; positivity
lemma center_sq (n : ℕ) : (n+1:ℝ)*(center n)^2 ≤ 1 := by
  induction n with
  | zero => norm_num [center,Nat.centralBinom]
  | succ n ih =>
    have hc : ((n:ℝ)+1)*n.succ.centralBinom = 2*(2*n+1)*(n.centralBinom:ℝ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have recurrence : center (n+1) = center n*((2*n+1)/(2*((n:ℝ)+1))) := by
      dsimp [center]; rw [pow_succ]; field_simp; linear_combination 2*hc
    rw [recurrence,Nat.cast_succ]
    have pos : 0 < 2*((n:ℝ)+1) := by positivity
    rw [mul_pow,div_pow,← mul_div_assoc,← mul_div_assoc,div_le_one (sq_pos_of_pos pos)]
    calc
      _ ≤ (((n:ℝ)+1)*(center n)^2) * (2*((n:ℝ)+1))^2 := by
        have heg : ((n:ℝ)+1+1)*(2*n+1)^2 ≤ ((n:ℝ)+1)*(2*(n+1))^2 := by nlinarith [show 0 ≤ (n:ℝ) by positivity]
        nlinarith [mul_nonneg (sq_nonneg (center n)) (sub_nonneg.mpr heg)]
      _ ≤ _ := by exact le_trans (mul_le_mul_of_nonneg_right ih (sq_nonneg _)) (by simp)

lemma center_limit : Tendsto center atTop (𝓝 0) := by
  have hu : Tendsto (fun n : ℕ => 1 / ((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_add_atTop_nat 1)
  have hs : Tendsto (fun n => (center n)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ hu
    intro n; exact (le_div_iff₀ (by positivity)).mpr (by simpa [mul_comm] using center_sq n)
  simpa [Real.sqrt_sq (center_nonneg _)] using hs.sqrt

lemma half_value (m : ℕ) : bernstein (2*m) m half = center m := by
  rw [bernstein_apply]; change _*(1/2:ℝ)^m*(1-1/2)^(2*m-m) = _
  unfold center; rw [Nat.centralBinom_eq_two_mul_choose]
  rw [show 2*m-m=m by omega,show (1-1/2:ℝ)=1/2 by norm_num,mul_assoc,← mul_pow]
  norm_num
  simp [div_eq_mul_inv,inv_pow]

lemma half_symm {n : ℕ} (i : Fin (n+1)) : bernstein n i.rev half = bernstein n i half := by
  have hv : i.rev.val = n-i.val := by change n+1-(i.val+1) = n-i.val; omega
  have hi := i.is_le
  rw [bernstein_apply,bernstein_apply,hv,Nat.choose_symm hi, Nat.sub_sub_self hi]
  change _ * (1/2:ℝ)^_*(1-1/2)^_ = _ * (1/2)^_*(1-1/2)^_
  rw [show (1-1/2:ℝ)=1/2 by norm_num]; ring

lemma half_mass (n : ℕ) : |2*step n half-1| ≤ center (n/2) := by
  let m := n/2
  let middle (i : Fin (n+1)) : ℝ := if 2*i.val=n then bernstein n i half else 0
  let low (i : Fin (n+1)) : ℝ := if 2*i.val<n then bernstein n i half else 0
  have reflected : (∑ i, low i) = step n half := by
    rw [← Equiv.sum_comp (Fin.revPerm (n:=n+1)) low]
    unfold step; apply Finset.sum_congr rfl; intro i _
    have hrev : (Fin.revPerm i).val = n-i.val := by change n+1-(i.val+1) = n-i.val; omega
    have hb : bernstein n (Fin.revPerm i).val half = bernstein n i half := half_symm i
    rw [hrev] at hb
    dsimp only [low]; rw [hrev,hb]
    have hi := i.is_le
    simp only [show 2*(n-i.val)<n ↔ n<2*i.val by omega]
  have total : (∑ i, middle i) + (∑ i, low i) + step n half = 1 := by
    rw [step,← Finset.sum_add_distrib,← Finset.sum_add_distrib,← bernstein.probability n half]
    apply Finset.sum_congr rfl; intro i _
    dsimp [low,middle]; split_ifs <;> simp_all <;> omega
  rw [reflected] at total
  have eq : 2*step n half-1 = -(∑ i, middle i) := by linarith
  have nonneg : 0 ≤ ∑ i, middle i := sum_nonneg (fun i _ => by dsimp [middle]; split <;> positivity)
  rw [eq,abs_neg,abs_of_nonneg nonneg]
  let j : Fin (n+1) := ⟨m,by dsimp [m]; omega⟩
  rw [Finset.sum_eq_single j]
  · dsimp only [middle]
    split_ifs with he
    · change 2*m=n at he
      change bernstein n m half ≤ center m
      rw [← he,half_value]
    · exact center_nonneg _
  · intro i _ hne
    have h : 2*i.val ≠ n := by intro he; apply hne; apply Fin.ext; change i.val = n/2; omega
    simp [middle,h]
  · simp

lemma step_half : Tendsto (fun n => step n half) atTop (𝓝 (1/2)) := by
  have hm : Tendsto (fun n : ℕ => n/2) atTop atTop := by
    apply tendsto_atTop.2; intro k; filter_upwards [eventually_ge_atTop (2*k)] with n hn; omega
  have hc := center_limit.comp hm
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hc (2*ε) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have h := hN n hn; have b := half_mass n
  simp only [Function.comp_apply,Real.dist_eq,sub_zero,abs_of_nonneg (center_nonneg _)] at h
  rw [Real.dist_eq,abs_lt]; have hh := abs_le.mp b; constructor <;> linarith

end OMA.S_mo_209949

namespace OMA.S_mo_209949
open Filter Set Polynomial Finset
open scoped unitInterval Topology

noncomputable def jump (a b c d : ℝ) := (c+d*(1/2))-(a+b*(1/2))
noncomputable def joined (a b c d : ℝ) : C(I,ℝ) :=
  ⟨fun t => if (t:ℝ) ≤ 1/2 then a+b*t else c+d*t-jump a b c d, by
    apply continuous_if_le continuous_subtype_val continuous_const
    · fun_prop
    · fun_prop
    · intro t ht; change (t:ℝ) = 1/2 at ht; rw [ht]; unfold jump; ring⟩

lemma candidate_eval {n : ℕ} (hn : 0 < n) (a b c d : ℝ) (t : I) :
    (candidate n (fun y => a+b*y) (fun y => c+d*y)).eval (t:ℝ) =
      bernsteinApproximation n (joined a b c d) t + jump a b c d * step n t := by
  simp only [candidate,sample,eval_finsetSum,eval_mul,eval_C,bernsteinApproximation.apply,step,
    Finset.mul_sum,← Finset.sum_add_distrib,smul_eq_mul]
  apply Finset.sum_congr rfl; intro k _
  have he : (bernsteinPolynomial ℝ n k).eval (t:ℝ) = bernstein n k t := rfl
  have hz : ((bernstein.z k):ℝ) = grid n k := rfl
  have hlt : (grid n k ≤ 1/2) ↔ 2*k.val ≤ n := by
    dsimp [grid]; rw [div_le_iff₀ (by exact_mod_cast hn)]
    constructor
    · intro h; exact_mod_cast (show 2*(k.val:ℝ) ≤ n by linarith)
    · intro h; have h' : 2*(k.val:ℝ) ≤ n := by exact_mod_cast h
      linarith
  rw [he]; dsimp only [joined,ContinuousMap.coe_mk]; simp only [hz,hlt]
  by_cases hk : 2*k.val ≤ n <;> simp [hk,not_lt_of_ge,Nat.lt_of_not_ge] <;> ring

noncomputable def pointStep (t : ℝ) : ℝ := if t < 1/2 then 0 else if 1/2 < t then 1 else 1/2

lemma bernstein_joined_uniform (a b c d : ℝ) :
    TendstoUniformly (fun n t => bernsteinApproximation n (joined a b c d) t)
      (joined a b c d) atTop :=
  ContinuousMap.tendsto_iff_tendstoUniformly.mp (bernsteinApproximation_uniform _)

lemma candidate_pointwise (center_limit : Tendsto (fun n => step n (⟨1/2,by constructor <;> norm_num⟩ : I)) atTop (𝓝 (1/2)))
    (a b c d : ℝ) (t : I) :
    Tendsto (fun n => (candidate n (fun y => a+b*y) (fun y => c+d*y)).eval (t:ℝ)) atTop
      (𝓝 (joined a b c d t + jump a b c d * pointStep t)) := by
  have hstep : Tendsto (fun n => step n t) atTop (𝓝 (pointStep t)) := by
    rcases lt_trichotomy (t:ℝ) (1/2) with h|h|h
    · simpa only [pointStep,if_pos h] using step_left t h
    · have ht : t = (⟨1/2,by constructor <;> norm_num⟩ : I) := Subtype.ext h
      subst t; simpa [pointStep] using center_limit
    · simpa only [pointStep,if_neg (not_lt_of_gt h),if_pos h] using step_right t h
  have base := ((bernstein_joined_uniform a b c d).tendsto_at t).add (hstep.const_mul (jump a b c d))
  apply base.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact (candidate_eval hn a b c d t).symm

end OMA.S_mo_209949

namespace OMA.S_mo_209949
open Filter Set
open scoped Topology

lemma matching_of_continuous (a b A B c d : ℝ)
    (hf : ContinuousAt (endpointLimit a b A B c d) ((a+b)/2)) :
    A+c*((a+b)/2-a) = B+d*((a+b)/2-b) := by
  let m := (a+b)/2
  let F := endpointLimit a b A B c d
  have left : Tendsto F (𝓝[<] m) (𝓝 (A+c*(m-a))) := by
    have h : ContinuousAt (fun x : ℝ => A+c*(x-a)) m := by fun_prop
    apply (h.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (if_pos (show x < m from hx)).symm
  have right : Tendsto F (𝓝[>] m) (𝓝 (B+d*(m-b))) := by
    have h : ContinuousAt (fun x : ℝ => B+d*(x-b)) m := by fun_prop
    apply (h.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hmx : m < x := hx
    change _ = (if x < m then _ else if m < x then _ else _)
    rw [if_neg (not_lt_of_gt hmx),if_pos hmx]
  have hl := tendsto_nhds_unique left (hf.tendsto.mono_left nhdsWithin_le_nhds)
  have hr := tendsto_nhds_unique right (hf.tendsto.mono_left nhdsWithin_le_nhds)
  exact hl.trans hr.symm

lemma slopes_of_differentiable (a b A B c d : ℝ) (hab : a < b)
    (hh : DifferentiableOn ℝ (endpointLimit a b A B c d) (Ioo a b)) : c = d := by
  let m := (a+b)/2
  let F := endpointLimit a b A B c d
  have hm : m ∈ Ioo a b := by dsimp [m]; constructor <;> linarith
  have hf : DifferentiableAt ℝ F m := (hh m hm).differentiableAt (isOpen_Ioo.mem_nhds hm)
  have matchv := matching_of_continuous a b A B c d hf.continuousAt
  change A+c*(m-a) = B+d*(m-b) at matchv
  have centerV : F m = A+c*(m-a) := by
    change (if m < m then _ else if m < m then _ else _) = _
    simp only [lt_irrefl,ite_false]; linarith
  have affine (v w y : ℝ) : HasDerivAt (fun x : ℝ => v+w*(x-y)) w m := by
    simpa using (((hasDerivAt_id m).sub_const y).const_mul w).const_add v
  have left : HasDerivWithinAt F c (Iic m) m := by
    apply (affine A c a).hasDerivWithinAt.congr_of_mem _ (by simp)
    intro x hx
    rcases lt_or_eq_of_le (show x ≤ m from hx) with h|rfl
    · exact if_pos h
    · exact centerV
  have right : HasDerivWithinAt F d (Ici m) m := by
    apply (affine B d b).hasDerivWithinAt.congr_of_mem _ (by simp)
    intro x hx
    rcases lt_or_eq_of_le (show m ≤ x from hx) with h|rfl
    · change (if x < m then _ else if m < x then _ else _) = _
      simp [h,not_lt_of_gt h]
    · exact centerV.trans matchv
  have hleft := hf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic m)
  have hright := hf.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici m)
  exact (left.derivWithin (uniqueDiffWithinAt_Iic m)).symm.trans
    (hleft.trans (hright.symm.trans (right.derivWithin (uniqueDiffWithinAt_Ici m))))

end OMA.S_mo_209949

namespace OMA.S_mo_209949
open Polynomial Set Filter
open scoped Topology unitInterval

lemma coordinates {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    ∃ t : I, x = a+(b-a)*t := by
  have hp := sub_pos.mpr hab
  refine ⟨⟨(x-a)/(b-a),div_nonneg (sub_nonneg.mpr hx.1) hp.le, (div_le_one hp).mpr (by linarith [hx.2])⟩,?_⟩
  change x=a+(b-a)*((x-a)/(b-a)); field_simp; ring

lemma physical_value (a b A B c d : ℝ) (hab : a < b) (t : I) :
    endpointLimit a b A B c d (a+(b-a)*t) =
      joined A (c*(b-a)) (B-d*(b-a)) (d*(b-a)) t + jump A (c*(b-a)) (B-d*(b-a)) (d*(b-a)) * pointStep t := by
  rcases lt_trichotomy (t:ℝ) (1/2) with ht|ht|ht
  · have hx : a+(b-a)*t < (a+b)/2 := by nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht)]
    simp only [endpointLimit,if_pos hx,joined,ContinuousMap.coe_mk,if_pos ht.le,pointStep,if_pos ht,mul_zero,add_zero]
    ring
  · simp only [endpointLimit,joined,ContinuousMap.coe_mk,pointStep,jump,ht]
    have hm : a+(b-a)*(1/2) = (a+b)/2 := by ring
    simp only [hm,lt_irrefl,ite_false,le_refl,ite_true]; ring
  · have hx : (a+b)/2 < a+(b-a)*t := by nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht)]
    simp only [endpointLimit,if_neg (not_lt_of_gt hx),if_pos hx,joined,ContinuousMap.coe_mk,
      if_neg (not_le_of_gt ht),pointStep,if_neg (not_lt_of_gt ht),if_pos ht,mul_one]
    ring

lemma eval_equation {a b A B c d : ℝ} {P : ℕ → ℝ[X]}
    (h : ∀ n ≥ 3, EndpointConditions n a b A B c d (P n)) (n : ℕ) (hn : 3 ≤ n) (t : I) :
    (P n).eval (a+(b-a)*t) = (candidate n (fun y => A+c*(b-a)*y)
      (fun y => (B-d*(b-a))+d*(b-a)*y)).eval (t:ℝ) := by
  simpa only [eval_comp,eval_add,eval_mul,eval_C,eval_X] using
    congrArg (fun p : ℝ[X] => p.eval (t:ℝ)) (normalized_identified hn (h n hn))

end OMA.S_mo_209949
open Filter Set OMA.S_mo_209949
open scoped Topology unitInterval

theorem OMA.solution : type_of% @OMA.S_mo_209949.main := by
  intro a b A B c d hab P hP
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · intro x hx
    obtain ⟨t,rfl⟩ := coordinates hab hx
    rw [physical_value _ _ _ _ _ _ hab]
    apply (candidate_pointwise step_half _ _ _ _ t).congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact (eval_equation hP n hn t).symm
  · intro hu
    have hm : (a+b)/2 ∈ Ioo a b := by constructor <;> linarith
    have hc := hu.continuousOn (Frequently.of_forall (fun n => (P n).continuous.continuousOn))
    exact matching_of_continuous _ _ _ _ _ _ (hc.continuousAt (Icc_mem_nhds hm.1 hm.2))
  · intro he
    have hj : jump A (c*(b-a)) (B-d*(b-a)) (d*(b-a))=0 := by unfold jump; linarith
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have h := Metric.tendstoUniformly_iff.mp (bernstein_joined_uniform A (c*(b-a)) (B-d*(b-a)) (d*(b-a))) ε hε
    filter_upwards [h,eventually_ge_atTop 3] with n hn h3 x hx
    obtain ⟨t,rfl⟩ := coordinates hab hx
    rw [physical_value _ _ _ _ _ _ hab,eval_equation hP n h3 t,candidate_eval (by omega),hj,zero_mul,zero_mul,add_zero,add_zero]
    exact hn t
  · intro hcd _ hdiff
    exact (hcd (slopes_of_differentiable _ _ _ _ _ _ hab hdiff)).elim
