import OMAStatements.S_mo_504555

/-! The normalized Bernoulli antiderivative of a square is monotone on
every unit-step progression. An intermediate level separating its value
at m from its value in [0,1] would yield more roots than its degree allows. -/

namespace OMA.S_mo_504555

open Polynomial

private lemma step_raw (k : ℕ) (x : ℝ) :
    ((Polynomial.bernoulli (k+1)).map (algebraMap ℚ ℝ)).eval (x+1) =
    ((Polynomial.bernoulli (k+1)).map (algebraMap ℚ ℝ)).eval x + (k+1:ℝ)*x^k := by
  have h := congrArg (fun P : ℚ[X] => (P.map (algebraMap ℚ ℝ)).eval x)
    (Polynomial.bernoulli_comp_one_add_X (k+1))
  simpa [Polynomial.map_comp, add_comm x 1, nsmul_eq_mul] using h

lemma moment_step (k : ℕ) (x : ℝ) :
    (momentPoly k).eval (x+1) - (momentPoly k).eval x = x^k := by
  simp only [momentPoly, eval_mul, eval_C, step_raw]
  field_simp
  ring

lemma moment_integral (k : ℕ) : ∫ x in (0:ℝ)..1, (momentPoly k).eval x = 0 := by
  let P := (Polynomial.bernoulli ((k+1)+1)).map (algebraMap ℚ ℝ)
  have hd : P.derivative = C ((k:ℝ)+2) * (Polynomial.bernoulli (k+1)).map (algebraMap ℚ ℝ) := by
    dsimp only [P]
    rw [derivative_map, derivative_bernoulli_add_one]
    rw [Polynomial.map_mul]
    congr 1
    simp only [Polynomial.map_add,Polynomial.map_one,Polynomial.map_natCast,Nat.cast_add,Nat.cast_one,map_add,map_ofNat,map_natCast]
    ring
  have hi : (∫ x in (0:ℝ)..1, P.derivative.eval x) = P.eval 1 - P.eval 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => P.hasDerivAt x)
      (P.derivative.continuous.intervalIntegrable ..)
  have he : P.eval 1 - P.eval 0 = 0 := by
    apply sub_eq_zero.mpr
    simpa [P] using step_raw (k+1) 0
  rw [he, hd] at hi
  simp only [eval_mul,eval_C,intervalIntegral.integral_const_mul] at hi
  have h := (mul_eq_zero.mp hi).resolve_left (by positivity)
  simp only [momentPoly,eval_mul,eval_C,intervalIntegral.integral_const_mul,h,mul_zero]

lemma moment_degree (k : ℕ) : (momentPoly k).natDegree ≤ k+1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  simp [momentPoly,Polynomial.coeff_map,Polynomial.coeff_bernoulli,not_le.mpr hj]

end OMA.S_mo_504555

namespace OMA.S_mo_504555
open Polynomial Finset
open scoped Matrix

noncomputable def antidiff {d : ℕ} (a : Fin (d+1) → ℝ) : ℝ[X] :=
  ∑ i, ∑ j, C (a i*a j)*momentPoly (i.val+j.val)

private lemma form_eval {d : ℕ} (a : Fin (d+1) → ℝ) (t : ℝ) :
    (antidiff a).eval t = ∑ i, ∑ j, (a i*a j)*(momentPoly (i.val+j.val)).eval t := by
  simp [antidiff,eval_finsetSum,eval_mul]

lemma form_step {d : ℕ} (a : Fin (d+1) → ℝ) (t : ℝ) :
    (antidiff a).eval (t+1) - (antidiff a).eval t = (∑ i, a i*t^i.val)^2 := by
  simp only [form_eval,←Finset.sum_sub_distrib,←mul_sub,moment_step,pow_add,pow_two,Finset.sum_mul]
  apply sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply sum_congr rfl; intro j _
  ring

lemma form_mean {d : ℕ} (a : Fin (d+1) → ℝ) :
    (∫ t in (0:ℝ)..1, (antidiff a).eval t)=0 := by
  let f (i j : Fin (d+1)) (t : ℝ) := (a i*a j)*(momentPoly (i.val+j.val)).eval t
  have hc (i j : Fin (d+1)) : Continuous (f i j) :=
    continuous_const.mul (momentPoly _).continuous
  simp_rw [form_eval]
  change (∫ t in (0:ℝ)..1, ∑ i, ∑ j, f i j t)=0
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum Finset.univ (fun j _ => hc i j)).intervalIntegrable 0 1)]
  apply sum_eq_zero; intro i _
  rw [intervalIntegral.integral_finsetSum (fun j _ => (hc i j).intervalIntegrable 0 1)]
  apply sum_eq_zero; intro j _
  simp [f,intervalIntegral.integral_const_mul,moment_integral]

lemma form_degree {d : ℕ} (a : Fin (d+1) → ℝ) : (antidiff a).natDegree ≤ 2*d+1 := by
  unfold antidiff
  apply natDegree_sum_le_of_forall_le; intro i _
  apply natDegree_sum_le_of_forall_le; intro j _
  exact (natDegree_C_mul_le _ _).trans ((moment_degree _).trans (by have := i.isLt;have := j.isLt;omega))

lemma form_value {d : ℕ} (a : Fin (d+1) → ℝ) (m : ℕ) :
    (antidiff a).eval (m:ℝ) = star a ⬝ᵥ hankel d m *ᵥ a := by
  simp only [form_eval,dotProduct,Matrix.mulVec,hankel,Pi.star_apply,star_trivial,Finset.mul_sum]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  ring

lemma form_nonconstant {d : ℕ} (a : Fin (d+1) → ℝ) (ha : a ≠ 0) (m : ℝ) :
    antidiff a ≠ C ((antidiff a).eval m) := by
  intro he
  have hz(t : ℝ) : (∑ i, a i*t^i.val)=0 := by
    have h := form_step a t
    rw [he,eval_C,eval_C,sub_self] at h
    exact sq_eq_zero_iff.mp h.symm
  have hpoly : ofFn (d+1) a=0 := by
    apply Polynomial.funext
    intro t
    simpa only [ofFn_eq_sum_monomial,eval_finsetSum,eval_monomial,eval_zero] using hz t
  apply ha
  apply (injective_ofFn (R:=ℝ) (d+1))
  simpa using hpoly

end OMA.S_mo_504555

namespace OMA.S_mo_504555

open Polynomial

private lemma same_interval {m : ℕ} (i j : Fin m) (z : ℝ)
    (hi : (i.val:ℝ) < z ∧ z < i.val+1) (hj : (j.val:ℝ) < z ∧ z < j.val+1) : i=j := by
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with hl | hl
  · have hle : (i.val:ℝ)+1 ≤ j.val := by exact_mod_cast hl
    linarith [hi.2,hj.1]
  · have hle : (j.val:ℝ)+1 ≤ i.val := by exact_mod_cast hl
    linarith [hj.2,hi.1]

private lemma count_crossings (P : ℝ[X]) (m : ℕ) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1)
    (hP : P ≠ 0) (L R : Fin m → ℝ)
    (hl : ∀ i, (i.val:ℝ) < L i ∧ L i < i.val+t ∧ P.IsRoot (L i))
    (hr : ∀ i, (i.val:ℝ)+t < R i ∧ R i < i.val+1 ∧ P.IsRoot (R i)) :
    2*m ≤ P.natDegree := by
  classical
  let Z : Fin m ⊕ Fin m → ℝ := Sum.elim L R
  let I : Fin m ⊕ Fin m → Fin m := Sum.elim id id
  have hi (a) : ((I a).val:ℝ) < Z a ∧ Z a < (I a).val+1 := by
    cases a with
    | inl i =>
      change (i.val:ℝ) < L i ∧ L i < i.val+1
      exact ⟨(hl i).1,by linarith [(hl i).2.1,ht.2]⟩
    | inr i =>
      change (i.val:ℝ) < R i ∧ R i < i.val+1
      exact ⟨by linarith [(hr i).1,ht.1],(hr i).2.1⟩
  have hinj : Function.Injective Z := by
    intro a b he
    have hh := same_interval (I a) (I b) (Z b) (he ▸ hi a) (hi b)
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl hh
      | inr j =>
        change i=j at hh
        subst j
        change L i=R i at he
        linarith [(hl i).2.1,(hr i).1]
    | inr i =>
      cases b with
      | inl j =>
        change i=j at hh
        subst j
        change R i=L i at he
        linarith [(hl i).2.1,(hr i).1]
      | inr j => exact congrArg Sum.inr hh
  have hv (a) : Z a ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset,mem_roots hP]
    cases a with
    | inl i => exact (hl i).2.2
    | inr i => exact (hr i).2.2
  let F (a : Fin m ⊕ Fin m) : ↥P.roots.toFinset := ⟨Z a,hv a⟩
  have hc := Fintype.card_le_of_injective F (fun _ _ he => hinj (congrArg Subtype.val he))
  have hc' : 2*m ≤ P.roots.toFinset.card := by simpa [two_mul] using hc
  exact hc'.trans (P.roots.toFinset_card_le.trans P.card_roots')

lemma crossing_max (Q : ℝ[X]) (m : ℕ) (hdeg : Q.natDegree < 2*m)
    (hstep : ∀ x : ℝ, Q.eval x ≤ Q.eval (x+1)) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, Q.eval t ≤ Q.eval (m:ℝ) := by
  have hmono (x : ℝ) : Monotone (fun i : ℕ => Q.eval (x+i)) := by
    apply monotone_nat_of_le_succ
    intro i
    simpa [Nat.cast_succ,add_assoc] using hstep (x+i)
  intro t ht
  by_contra! h
  let y := (Q.eval (m:ℝ)+Q.eval t)/2
  have hy : Q.eval (m:ℝ) < y ∧ y < Q.eval t := by dsimp [y]; constructor <;> linarith
  let P := Q-C y
  have hP : P ≠ 0 := by
    intro he
    have := congrArg (Polynomial.eval (m:ℝ)) he
    dsimp [P] at this
    simp only [eval_sub,eval_C,eval_zero] at this
    linarith [hy.1]
  have low (i : ℕ) (hi : i ≤ m) : Q.eval (i:ℝ) < y := by
    have hle : Q.eval (i:ℝ) ≤ Q.eval (m:ℝ) := by simpa using hmono 0 hi
    exact hle.trans_lt hy.1
  have high (i : ℕ) : y < Q.eval ((i:ℝ)+t) := by
    apply hy.2.trans_le
    simpa [add_comm t] using hmono t (Nat.zero_le i)
  have hL (i : Fin m) : ∃ z : ℝ, (i.val:ℝ) < z ∧ z < i.val+t ∧ P.IsRoot z := by
    obtain ⟨z,hz,he⟩ := intermediate_value_Ioo (show (i.val:ℝ) ≤ i.val+t by linarith [ht.1])
      Q.continuous.continuousOn ⟨low i i.isLt.le, high i⟩
    exact ⟨z,hz.1,hz.2,by simpa [P,IsRoot,sub_eq_zero] using he⟩
  have hR (i : Fin m) : ∃ z : ℝ, (i.val:ℝ)+t < z ∧ z < i.val+1 ∧ P.IsRoot z := by
    have hl : Q.eval ((i.val:ℝ)+1) < y := by exact_mod_cast low (i.val+1) i.isLt
    obtain ⟨z,hz,he⟩ := intermediate_value_Ioo' (show (i.val:ℝ)+t ≤ i.val+1 by linarith [ht.2])
      Q.continuous.continuousOn ⟨hl,high i⟩
    exact ⟨z,hz.1,hz.2,by simpa [P,IsRoot,sub_eq_zero] using he⟩
  choose L hL using hL
  choose R hR using hR
  have hc := count_crossings P m t ht hP L R hL hR
  change 2*m ≤ (Q-C y).natDegree at hc
  rw [natDegree_sub_C] at hc
  omega

end OMA.S_mo_504555

namespace OMA.S_mo_504555
open Polynomial

lemma positive_of_mean (Q : ℝ[X]) (m : ℕ)
    (hmax : ∀ t ∈ Set.Icc (0:ℝ) 1, Q.eval t ≤ Q.eval (m:ℝ))
    (hnc : Q ≠ C (Q.eval (m:ℝ))) (hmean : ∫ t in (0:ℝ)..1, Q.eval t = 0) :
    0 < Q.eval (m:ℝ) := by
  have hlt : ∃ t ∈ Set.Icc (0:ℝ) 1, Q.eval t < Q.eval (m:ℝ) := by
    by_contra! h
    apply hnc
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Icc_infinite (zero_lt_one : (0:ℝ)<1)).mono
    intro t ht
    simpa using (hmax t ht).antisymm (h t ht)
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (zero_lt_one : (0:ℝ)<1) Q.continuous.continuousOn
    (continuousOn_const (c := Q.eval (m:ℝ)))
    (fun t ht => hmax t (Set.Ioc_subset_Icc_self ht)) hlt
  simpa [hmean] using h

end OMA.S_mo_504555

theorem OMA.solution : type_of% @OMA.S_mo_504555.main := by
  intro d m hm
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simp [Matrix.conjTranspose_apply,OMA.S_mo_504555.hankel,add_comm]
  intro a ha
  rw [← OMA.S_mo_504555.form_value]
  apply OMA.S_mo_504555.positive_of_mean
  · apply OMA.S_mo_504555.crossing_max
    · have := OMA.S_mo_504555.form_degree a
      omega
    · intro t
      have h := OMA.S_mo_504555.form_step a t
      linarith [sq_nonneg (∑ i, a i*t^i.val)]
  · exact OMA.S_mo_504555.form_nonconstant a ha _
  · exact OMA.S_mo_504555.form_mean a
