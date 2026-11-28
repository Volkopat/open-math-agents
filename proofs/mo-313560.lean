import OMAStatements.S_mo_313560

/-!

Complete formal proof by @connoranderson, linked from merged statement PR #22962
and task-desk DONE #105360, pinned at:
https://github.com/connoranderson/open-math-agents/blob/45fbefdc7b6df719b07ca1648f551c768292d002/proofs/mo-313560.lean
This port preserves the mathematical source and adds attribution.
Proof of the conjectures of G. Milovanović, A. Cvetković, and M. Stanić following
Sergiu Alexandru Bîsceanu, https://mathoverflow.net/a/515313 (CC BY-SA 4.0).
The oscillatory antiderivative is obtained by inverting the polynomial operator
q ↦ q″ + π²q. Its endpoint functional is linear. Moving a half-integer root
to the right reduces the root index sum while preserving the induction on degree.
-/
namespace OMA.S_mo_313560

open Polynomial Real

private noncomputable def osc : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  derivative.comp derivative + (π^2) • LinearMap.id

private lemma osc_apply (p : ℝ[X]) : osc p = p.derivative.derivative + C (π^2)*p := by
  simp [osc,smul_eq_C_mul]

private lemma osc_inj : Function.Injective osc := by
  apply (LinearMap.ker_eq_bot.mp ?_)
  apply LinearMap.ker_eq_bot'.mpr
  intro p hp
  by_contra hn
  rw [osc_apply,add_eq_zero_iff_eq_neg] at hp
  have hlt : p.derivative.derivative.degree < p.degree :=
    degree_derivative_le.trans_lt (degree_derivative_lt hn)
  have hd := congrArg degree hp
  rw [degree_neg,degree_C_mul (pow_ne_zero _ Real.pi_ne_zero)] at hd
  exact hlt.ne hd

private lemma osc_surj (p : ℝ[X]) : ∃ q, osc q = p := by
  by_cases hp : p=0
  · exact ⟨0,by simp [hp]⟩
  obtain ⟨q,hq⟩ := osc_surj p.derivative.derivative
  refine ⟨(π^2)⁻¹ • (p-q),?_⟩
  rw [map_smul,map_sub,hq,osc_apply,add_sub_cancel_left,smul_eq_C_mul,← mul_assoc,← C_mul,
    inv_mul_cancel₀ (pow_ne_zero _ Real.pi_ne_zero),map_one,one_mul]
termination_by p.degree
decreasing_by exact degree_derivative_le.trans_lt (degree_derivative_lt hp)

private noncomputable def invOsc := (LinearEquiv.ofBijective osc ⟨osc_inj,osc_surj⟩).symm

private lemma osc_inv (p : ℝ[X]) : osc (invOsc p) = p :=
  (LinearEquiv.ofBijective osc ⟨osc_inj,osc_surj⟩).apply_symm_apply p

private noncomputable def endpoint (p : ℝ[X]) : ℝ := (invOsc p).derivative.eval 0

private lemma endpoint_add (p q : ℝ[X]) : endpoint (p+q) = endpoint p+endpoint q := by
  simp [endpoint]

private lemma endpoint_C_mul (c : ℝ) (p : ℝ[X]) : endpoint (C c*p) = c*endpoint p := by
  simp [endpoint,← smul_eq_C_mul]

private lemma integral_osc (p : ℝ[X]) (a b : ℝ) :
    (∫ x in a..b, p.eval x * cos (π*x)) =
    ((invOsc p).derivative.eval b*cos (π*b)+π*(invOsc p).eval b*sin (π*b)) -
    ((invOsc p).derivative.eval a*cos (π*a)+π*(invOsc p).eval a*sin (π*a)) := by
  let q := invOsc p
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x _
    have hθ : HasDerivAt (fun t : ℝ => π*t) π x := by
      simpa using (hasDerivAt_id x).const_mul π
    have hd := ((q.derivative.hasDerivAt x).mul hθ.cos).add
      (((q.hasDerivAt x).const_mul π).mul hθ.sin)
    convert hd using 1 <;> try rfl
    have h := congrArg (Polynomial.eval x) (osc_inv p)
    rw [osc_apply,eval_add,eval_mul,eval_C] at h
    change q.derivative.derivative.eval x+π^2*q.eval x=p.eval x at h
    rw [← h]
    ring
  · exact (p.continuous.mul (by fun_prop)).intervalIntegrable ..

private lemma integral_sym (p : ℝ[X]) (d : ℕ)
    (hp : p.comp (C (-(d:ℝ))-X) = C ((-1:ℝ)^d)*p) :
    (∫ x in (-(d:ℝ))..0, p.eval x*cos (π*x)) = 2*endpoint p := by
  let q := invOsc p
  let T : ℝ[X] := C (-(d:ℝ))-X
  let e : ℝ := (-1)^d
  have hT : T.derivative = -1 := by simp [T]
  have hflip (f : ℝ[X]) : (f.comp T).derivative = -(f.derivative.comp T) := by
    rw [derivative_comp,hT,neg_one_mul]
  have hq : q.comp T = C e*q := by
    apply osc_inj
    rw [osc_apply,hflip,derivative_neg,hflip,neg_neg]
    rw [← smul_eq_C_mul (a := e),map_smul,show osc q=p from osc_inv p,smul_eq_C_mul,← hp]
    change _ = p.comp T
    conv_rhs => rw [← osc_inv p,osc_apply,add_comp,mul_comp,C_comp]
  have hder := congrArg (fun f : ℝ[X] => f.derivative.eval 0) hq
  simp only [hflip,eval_neg,eval_comp,T,eval_sub,eval_C,eval_X,sub_zero,
    derivative_C_mul,eval_mul] at hder
  have hcos : cos (π * -(d:ℝ))=e := by simpa [e,mul_comm] using Real.cos_nat_mul_pi d
  have hsin : sin (π * -(d:ℝ))=0 := by rw [mul_neg,Real.sin_neg,mul_comm,Real.sin_nat_mul_pi,neg_zero]
  have hsq : e*e=1 := by simp [e,← mul_pow]
  rw [integral_osc,hcos,hsin]
  simp only [mul_zero,Real.cos_zero,Real.sin_zero,mul_one,add_zero]
  change q.derivative.eval 0-q.derivative.eval (-↑d)*e=2*q.derivative.eval 0
  linear_combination e * hder + q.derivative.eval 0 * hsq

end OMA.S_mo_313560
namespace OMA.S_mo_313560

open Polynomial Real Finset

private noncomputable def halfProd (S : Finset ℕ) : ℝ[X] :=
  ∏ j ∈ S, (X+C ((j:ℝ)+1/2))

private noncomputable def base (d : ℕ) := halfProd (range d)

private lemma base_succ (d : ℕ) (x : ℝ) :
    (base (d+1)).eval x = (base d).eval x * (x+d+1/2) := by
  simp [base,halfProd,prod_range_succ,add_assoc]

private lemma base_shift (d : ℕ) (x : ℝ) :
    (base (d+1)).eval x = (x+1/2)*(base d).eval (x+1) := by
  simp only [base,halfProd,eval_prod,eval_add,eval_X,eval_C]
  rw [prod_range_succ']
  simp only [Nat.cast_zero,zero_add,Nat.cast_succ]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro j _
  ring

private lemma base_sym (d : ℕ) (x : ℝ) :
    (base d).eval (-(d:ℝ)-x) = (-1:ℝ)^d*(base d).eval x := by
  induction d generalizing x with
  | zero => simp [base,halfProd]
  | succ d ih =>
    rw [base_shift,base_succ,Nat.cast_succ,show -((d:ℝ)+1)-x+1= -d-x by ring,ih,pow_succ]
    ring

private lemma base_sign (d : ℕ) (x : ℝ) (hl : -(d:ℝ)-1/2 ≤ x) (hu : x ≤ 1/2) :
    0 ≤ (base d).eval x*cos (π*x) := by
  induction d generalizing x with
  | zero =>
    simp only [Nat.cast_zero,neg_zero,zero_sub] at hl
    simp only [base,halfProd,range_zero,prod_empty,eval_one,one_mul]
    exact cos_nonneg_of_mem_Icc ⟨by nlinarith [mul_le_mul_of_nonneg_left hl pi_pos.le],
      by nlinarith [mul_le_mul_of_nonneg_left hu pi_pos.le]⟩
  | succ d ih =>
    rw [Nat.cast_succ] at hl
    by_cases hx : -(d:ℝ)-1/2 ≤ x
    · rw [base_succ,mul_right_comm]
      exact mul_nonneg (ih x hx hu) (by linarith)
    · rw [base_shift]
      have h := ih (x+1) (by linarith) (by have := (d.cast_nonneg : (0:ℝ) ≤ d); linarith)
      rw [mul_add,mul_one,cos_add_pi] at h
      nlinarith [mul_nonneg (show 0 ≤ -(x+1/2) by have := d.cast_nonneg (α := ℝ); linarith) h]

private lemma base_positive (d : ℕ) (hd : 0 < d) : 0 < endpoint (base d) := by
  have hs : (base d).comp (C (-(d:ℝ))-X) = C ((-1:ℝ)^d)*base d := by
    apply Polynomial.funext
    intro x
    simpa using base_sym d x
  let f := fun x : ℝ => (base d).eval x*cos (π*x)
  have hc : Continuous f := (base d).continuous.mul (by fun_prop)
  have hp (x : ℝ) (hx : x ∈ Set.Ioo (-(1/4:ℝ)) 0) : 0 < f x := by
    apply mul_pos
    · simp only [base,halfProd,eval_prod,eval_add,eval_X,eval_C]
      apply prod_pos
      intro j _
      linarith [hx.1, Nat.cast_nonneg (α := ℝ) j]
    · exact cos_pos_of_mem_Ioo ⟨by nlinarith [mul_lt_mul_of_pos_left hx.1 pi_pos,pi_pos],
        by nlinarith [mul_lt_mul_of_pos_left hx.2 pi_pos,pi_pos]⟩
  have hreal : (1:ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 ≤ ∫ x in (-(d:ℝ))..(-(1/4:ℝ)), f x :=
    intervalIntegral.integral_nonneg (by linarith) (fun x hx => base_sign d x (by linarith [hx.1]) (by linarith [hx.2]))
  have h2 := intervalIntegral.intervalIntegral_pos_of_pos_on
    (hc.intervalIntegrable (-(1/4:ℝ)) 0) hp (by norm_num)
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := MeasureTheory.volume) (-(d:ℝ)) (-(1/4:ℝ))) (hc.intervalIntegrable (-(1/4:ℝ)) 0)
  change _ = ∫ x in (-(d:ℝ))..0, (base d).eval x*cos (π*x) at hsum
  rw [integral_sym (base d) d hs] at hsum
  linarith

end OMA.S_mo_313560
namespace OMA.S_mo_313560

open Polynomial Real Finset

private lemma endpoint_empty : endpoint (halfProd ∅)=0 := by
  have h := integral_sym (1:ℝ[X]) 0 (by simp)
  simp [halfProd] at *
  linarith

private lemma endpoint_all (S : Finset ℕ) : 0 ≤ endpoint (halfProd S) := by
  classical
  by_cases h0 : S.card=0
  · simpa [Finset.card_eq_zero.mp h0] using endpoint_empty.ge
  by_cases he : S=range S.card
  · exact (congrArg (fun T => endpoint (halfProd T)) he).symm ▸ (base_positive _ (Nat.pos_of_ne_zero h0)).le
  have hex₁ : ¬range S.card ⊆ S := by
    intro h
    exact he (eq_of_subset_of_card_le h (by simp)).symm
  have hex₂ : ¬S ⊆ range S.card := by
    intro h
    exact he (eq_of_subset_of_card_le h (by simp))
  obtain ⟨i,hi,hi'⟩ := Finset.not_subset.mp hex₁
  obtain ⟨j,hj,hj'⟩ := Finset.not_subset.mp hex₂
  have hlt : i < j := (mem_range.mp hi).trans_le (by simpa using hj')
  let D := S.erase j
  let T := insert i D
  have hjD : j ∉ D := by simp [D]
  have hiD : i ∉ D := fun h => hi' (mem_of_mem_erase h)
  have hD := Finset.card_erase_of_mem hj
  have hT : T.card=S.card := by simp [T,D,hiD,hD]; omega
  have hs : ∑ x ∈ T, x < ∑ x ∈ S, x := by
    change ∑ x ∈ insert i D, x < _
    rw [Finset.sum_insert hiD,← Finset.sum_erase_add S (fun t => t) hj]
    change i + ∑ x ∈ D, x < (∑ x ∈ D, x)+j
    omega
  have hd : 0 ≤ endpoint (halfProd D) := endpoint_all D
  have ht : 0 ≤ endpoint (halfProd T) := endpoint_all T
  have hp : halfProd S = halfProd T + C ((j:ℝ)-i)*halfProd D := by
    have eqs : S = insert j D := (insert_erase hj).symm
    conv_lhs => rw [eqs,halfProd,prod_insert hjD]
    change _ = (∏ k ∈ insert i D, (X+C ((k:ℝ)+1/2))) + C ((j:ℝ)-i)*(∏ k ∈ D, (X+C ((k:ℝ)+1/2)))
    rw [prod_insert hiD]
    rw [map_add,map_add,map_sub]
    ring
  rw [hp,endpoint_add,endpoint_C_mul]
  exact add_nonneg ht (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hlt.le)) hd)
termination_by (S.card,∑ x ∈ S, x)
decreasing_by
  · apply Prod.Lex.left
    rw [hD]; omega
  · rw [hT]
    exact Prod.Lex.right _ hs

end OMA.S_mo_313560
namespace OMA.S_mo_313560

open Real Polynomial Finset

private lemma extended (S : Finset ℕ) (d : ℕ) (s : ℝ) (hs : 0 < s) (hs' : s ≤ 1/2)
    (hsym : ∀ x, (halfProd S).eval (-(d:ℝ)-x) = (-1:ℝ)^d*(halfProd S).eval x) :
    0 < ∫ x in (-(d:ℝ)-s)..s, (halfProd S).eval x*cos (π*x) := by
  let f := fun x : ℝ => (halfProd S).eval x*cos (π*x)
  have hc : Continuous f := (halfProd S).continuous.mul (by fun_prop)
  have hp : (halfProd S).comp (C (-(d:ℝ))-X) = C ((-1:ℝ)^d)*(halfProd S) := by
    apply Polynomial.funext
    intro x
    simpa using hsym x
  have eqs (x : ℝ) : f (-(d:ℝ)-x)=f x := by
    have harg : π*(-(d:ℝ)-x) = -(π*x+d*π) := by ring
    dsimp only [f]
    rw [hsym,harg,cos_neg,cos_add_nat_mul_pi]
    have h : (-1:ℝ)^d * (-1:ℝ)^d = 1 := by simp [← mul_pow]
    linear_combination (halfProd S).eval x * cos (π*x) * h
  have htail : 0 < ∫ x in 0..s, f x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable ..) _ hs
    intro x hx
    apply mul_pos
    · simp only [halfProd,eval_prod,eval_add,eval_X,eval_C]
      apply prod_pos
      intro i _
      linarith [Nat.cast_nonneg (α := ℝ) i,hx.1]
    · apply cos_pos_of_mem_Ioo
      constructor
      · nlinarith [mul_pos pi_pos hx.1,pi_pos]
      · nlinarith [mul_lt_mul_of_pos_left (hx.2.trans_le hs') pi_pos]
  have hleft : (∫ x in (-(d:ℝ)-s)..(-(d:ℝ)), f x) = ∫ x in 0..s, f x := by
    calc
      _ = ∫ x in (0:ℝ)..s, f (-(d:ℝ)-x) := by
        rw [intervalIntegral.integral_comp_sub_left,sub_zero]
      _ = _ := by simp only [eqs]
  have hmid : 0 ≤ ∫ x in (-(d:ℝ))..0, f x := by
    change 0 ≤ ∫ x in (-(d:ℝ))..0, (halfProd S).eval x*cos (π*x)
    rw [integral_sym _ _ hp]
    positivity [endpoint_all S]
  change 0 < ∫ x in (-(d:ℝ)-s)..s, f x
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-(d:ℝ)-s) (-(d:ℝ))) (hc.intervalIntegrable (-(d:ℝ)) s)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-(d:ℝ)) 0) (hc.intervalIntegrable 0 s),hleft]
  linarith

end OMA.S_mo_313560
namespace OMA.S_mo_313560

open Polynomial Real Finset

private def paired (d n : ℕ) := range n ∪ (range n).image (fun j => d-1-j)

private lemma paired_eval (d n : ℕ) (h : 2*n ≤ d) (x : ℝ) :
    (halfProd (paired d n)).eval x =
    ∏ j ∈ range n, (x+j+1/2)*(x+d-j-1/2) := by
  classical
  have dis : Disjoint (range n) ((range n).image (fun j => d-1-j)) := by
    refine disjoint_left.mpr ?_
    intro t ht ht'
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ht'
    have := mem_range.mp hj
    have := mem_range.mp ht
    omega
  simp only [halfProd,eval_mul,eval_prod,eval_add,eval_X,eval_C,paired,prod_union dis,prod_mul_distrib]
  congr 1
  · apply prod_congr rfl
    intro j _
    ring
  · rw [prod_image]
    · apply prod_congr rfl
      intro j hj
      have hj := mem_range.mp hj
      rw [Nat.cast_sub (by omega : j ≤ d-1),Nat.cast_sub (by omega : 1 ≤ d)]
      push_cast; ring
    · intro i hi j hj hij
      change d-1-i=d-1-j at hij
      have := mem_range.mp hi
      have := mem_range.mp hj
      omega

private lemma middle_free (N n : ℕ) (hn : n ≤ N) : N ∉ paired (2*N+1) n := by
  intro h
  rcases mem_union.mp h with h | h
  · have := mem_range.mp h
    omega
  · obtain ⟨j,hj,he⟩ := mem_image.mp h
    have := mem_range.mp hj
    omega

private noncomputable def evenP (N n : ℕ) (y : ℝ) :=
  ∏ j ∈ range n, (y^2-((N:ℝ)-j-1/2)^2)

private noncomputable def oddP (N n : ℕ) (y : ℝ) :=
  y*∏ j ∈ range n, (y^2-((N:ℝ)-j)^2)

private lemma evenP_neg (N n : ℕ) (y : ℝ) : evenP N n (-y)=evenP N n y := by
  simp [evenP]

private lemma oddP_neg (N n : ℕ) (y : ℝ) : oddP N n (-y)= -oddP N n y := by
  simp [oddP]

private lemma even_shape (N n : ℕ) (hn : n ≤ N) (x : ℝ) :
    (halfProd (paired (2*N) n)).eval x=evenP N n (x+N) := by
  rw [paired_eval _ _ (by omega)]
  apply prod_congr rfl
  intro j _
  push_cast
  ring

private lemma odd_shape (N n : ℕ) (hn : n ≤ N) (x : ℝ) :
    (halfProd (insert N (paired (2*N+1) n))).eval x=oddP N n (x+((N:ℝ)+1/2)) := by
  rw [halfProd,prod_insert (middle_free N n hn),eval_mul,eval_add,eval_X,eval_C]
  change _*(halfProd (paired (2*N+1) n)).eval x = _
  rw [paired_eval _ _ (by omega)]
  apply congrArg ((x+((N:ℝ)+1/2))*·)
  apply prod_congr rfl
  intro j _
  push_cast
  ring

end OMA.S_mo_313560
namespace OMA.S_mo_313560

open Real Finset

private lemma phase {ξ X : ℝ} {N : ℕ} (hξ : ξ=π*X) (hlo : (N:ℝ) ≤ X)
    (hhi : X < N+1) (hz : sin (2*ξ) ≠ 0) :
    Real.sign (sin ξ)=(-1:ℝ)^N ∧
      (0 < sin (2*ξ) → 0 < X-N ∧ X-N < 1/2) ∧
      (sin (2*ξ) < 0 → 1/2 < X-N ∧ X-N < 1) := by
  let t := X-(N:ℝ)
  have ht0 : 0 ≤ t := sub_nonneg.mpr hlo
  have ht1 : t < 1 := by dsimp [t]; linarith
  have e : ξ = π*t+N*π := by rw [hξ]; dsimp [t]; ring
  have hs : sin ξ = (-1:ℝ)^N*sin (π*t) := by rw [e,sin_add_nat_mul_pi]
  have hc : cos ξ = (-1:ℝ)^N*cos (π*t) := by rw [e,cos_add_nat_mul_pi]
  have he : (-1:ℝ)^N * (-1:ℝ)^N = 1 := by simp [← mul_pow]
  have h2 : sin (2*ξ) = 2*sin (π*t)*cos (π*t) := by
    rw [sin_two_mul,hs,hc]
    linear_combination 2*sin (π*t)*cos (π*t)*he
  have ht : 0 < t := lt_of_le_of_ne ht0 (by
    intro h
    apply hz
    simp [h.symm,h2])
  have hsin : 0 < sin (π*t) := sin_pos_of_pos_of_lt_pi (mul_pos pi_pos ht)
    (by nlinarith [mul_lt_mul_of_pos_left ht1 pi_pos])
  refine ⟨?_,?_,?_⟩
  · rw [hs]
    rcases neg_one_pow_eq_or ℝ N with h | h
    · rw [h,one_mul,sign_of_pos hsin]
    · rw [h,neg_one_mul,sign_of_neg (neg_lt_zero.mpr hsin)]
  · intro h
    refine ⟨ht,?_⟩
    change t < 1/2
    by_contra! H
    have hcos := cos_nonpos_of_pi_div_two_le_of_le (x := π*t)
      (by nlinarith [mul_le_mul_of_nonneg_left H pi_pos.le])
      (by nlinarith [mul_lt_mul_of_pos_left ht1 pi_pos,pi_pos])
    exact (not_lt.mpr (h2 ▸ mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos)) h
  · intro h
    refine ⟨?_,ht1⟩
    change 1/2 < t
    by_contra! H
    have hcos := cos_nonneg_of_mem_Icc (x := π*t) ⟨by nlinarith [mul_nonneg pi_pos.le ht0,pi_pos],
      by nlinarith [mul_le_mul_of_nonneg_left H pi_pos.le]⟩
    exact (not_lt.mpr (h2 ▸ mul_nonneg (by positivity) hcos)) h

private lemma dilate (n : ℕ) (a : ℕ → ℝ) (X t : ℝ) (hX : X ≠ 0) :
    (∏ j ∈ range n, ((X*t)^2-(a j)^2)) =
    (X^2)^n * ∏ j ∈ range n, (t^2-(a j/X)^2) := by
  calc
    _ = ∏ j ∈ range n, (X^2*(t^2-(a j/X)^2)) := by
      apply prod_congr rfl
      intro i _
      field_simp
    _ = _ := by simp [prod_mul_distrib]

private lemma transformed (S : Finset ℕ) (d : ℕ) (X C : ℝ)
    (hsym : ∀ x, (halfProd S).eval (-(d:ℝ)-x) = (-1:ℝ)^d*(halfProd S).eval x)
    (hd : (d:ℝ)=2*C) (hX : 0 < X) (hl : 0 < X-C) (hu : X-C ≤ 1/2) :
    0 < ∫ t in (-1:ℝ)..1, (halfProd S).eval (X*t-C)*cos (π*(X*t-C)) := by
  let f := fun x => (halfProd S).eval x*cos (π*x)
  change 0 < ∫ t in (-1:ℝ)..1, f (X*t-C)
  rw [intervalIntegral.integral_comp_mul_sub f hX.ne',smul_eq_mul,mul_one,mul_neg_one]
  have h := extended S d (X-C) hl hu hsym
  rw [show -(d:ℝ)-(X-C)= -X-C by linarith] at h
  exact mul_pos (inv_pos.mpr hX) h

end OMA.S_mo_313560
namespace OMA.S_mo_313560

open Polynomial Real Finset

private lemma even_case {ξ X : ℝ} {N n : ℕ} (hξ : ξ=π*X) (hX : 0 < X) (hn : n ≤ N)
    (hsig : Real.sign (sin ξ)=(-1:ℝ)^N) (hl : 0 < X-N) (hu : X-N ≤ 1/2) :
    0 < Real.sign (sin ξ)*cosineIntegral ξ N n := by
  have hsym (x : ℝ) : (halfProd (paired (2*N) n)).eval (-((2*N:ℕ):ℝ)-x) =
      (-1:ℝ)^(2*N)*(halfProd (paired (2*N) n)).eval x := by
    rw [even_shape N n hn,even_shape N n hn,pow_mul]
    norm_num
    rw [show -(2*(N:ℝ))-x+N = -(x+N) by ring,evenP_neg]
  have h := transformed (paired (2*N) n) (2*N) X N hsym (by push_cast; ring) hX hl hu
  let f := fun t : ℝ => (∏ j ∈ range n, (t^2-(((N:ℝ)-j-1/2)*π/ξ)^2))*cos (ξ*t)
  have eqf (t : ℝ) : (halfProd (paired (2*N) n)).eval (X*t-N)*cos (π*(X*t-N)) =
      ((X^2)^n * Real.sign (sin ξ))*f t := by
    rw [even_shape N n hn,sub_add_cancel,evenP,dilate _ _ _ _ hX.ne']
    have ep (j : ℕ) : ((N:ℝ)-j-1/2)/X = ((N:ℝ)-j-1/2)*π/ξ := by
      rw [hξ]; field_simp [Real.pi_ne_zero]
    simp_rw [ep]
    rw [show π*(X*t-N)=ξ*t-N*π by rw [hξ]; ring,cos_sub_nat_mul_pi,hsig]
    dsimp [f]; ring
  simp_rw [eqf] at h
  rw [intervalIntegral.integral_const_mul,mul_assoc] at h
  exact pos_of_mul_pos_right h (by positivity : 0 ≤ (X^2)^n)

private lemma odd_case {ξ X : ℝ} {N n : ℕ} (hξ : ξ=π*X) (hX : 0 < X) (hn : n ≤ N)
    (hsig : Real.sign (sin ξ)=(-1:ℝ)^N) (hl : 1/2 < X-N) (hu : X-N ≤ 1) :
    0 < Real.sign (sin ξ)*sineIntegral ξ N n := by
  let C := (N:ℝ)+1/2
  let S := insert N (paired (2*N+1) n)
  have hsym (x : ℝ) : (halfProd S).eval (-((2*N+1:ℕ):ℝ)-x) =
      (-1:ℝ)^(2*N+1)*(halfProd S).eval x := by
    dsimp only [S]
    rw [odd_shape N n hn,odd_shape N n hn,pow_succ,pow_mul]
    norm_num
    rw [show -1+ -(2*(N:ℝ))-x+(N+1/2) = -(x+(N+1/2)) by ring,oddP_neg]
  have h := transformed S (2*N+1) X C hsym (by dsimp [C]; push_cast; ring) hX
    (by dsimp [C]; linarith) (by dsimp [C]; linarith)
  let f := fun t : ℝ => (t*∏ j ∈ range n, (t^2-(((N:ℝ)-j)*π/ξ)^2))*sin (ξ*t)
  have eqf (t : ℝ) : (halfProd S).eval (X*t-C)*cos (π*(X*t-C)) =
      (X*(X^2)^n * Real.sign (sin ξ))*f t := by
    dsimp only [S,C]
    rw [odd_shape N n hn,sub_add_cancel,oddP,dilate _ _ _ _ hX.ne']
    have ep (j : ℕ) : ((N:ℝ)-j)/X = ((N:ℝ)-j)*π/ξ := by
      rw [hξ]; field_simp [Real.pi_ne_zero]
    simp_rw [ep]
    rw [show π*(X*t-(N+1/2))=(ξ*t-π/2)-N*π by rw [hξ]; ring,cos_sub_nat_mul_pi,
      cos_sub_pi_div_two,hsig]
    dsimp [f]; ring
  simp_rw [eqf] at h
  rw [intervalIntegral.integral_const_mul,mul_assoc] at h
  exact pos_of_mul_pos_right h (by positivity : 0 ≤ X*(X^2)^n)

end OMA.S_mo_313560

open OMA.S_mo_313560 Real in
theorem OMA.solution : type_of% @OMA.S_mo_313560.main := by
  intro ξ hξ n _ hn
  let X := ξ/π
  let N := ⌊X⌋₊
  have he : ξ=π*X := by dsimp [X]; field_simp
  have hx : 0 < X := div_pos hξ pi_pos
  have h0 : (N:ℝ) ≤ X := Nat.floor_le hx.le
  have h1 : X < N+1 := Nat.lt_floor_add_one X
  constructor
  · intro h
    obtain ⟨hsig,_,hph⟩ := phase he h0 h1 h.ne
    exact odd_case he hx hn hsig (hph h).1 (hph h).2.le
  · intro h
    obtain ⟨hsig,hph,_⟩ := phase he h0 h1 h.ne'
    exact even_case he hx hn hsig (hph h).1 (hph h).2.le

