import OMAStatements.S_mo_486714

/-! The two polynomial sequences differ by a monomial. Roots of unity
index quadratic factors, and the imaginary parts of their root sums give
a uniform separation of angular averages. -/

namespace OMA.S_mo_486714
open Polynomial

lemma roots_factor (m : ℕ) (hm : 0 < m) :
    (((X-C (3:ℂ))^(2*m) - X^m).roots) =
      (((X:ℂ[X])^m-1).roots.bind (fun w : ℂ => ((X-C 3)^2-C w*X).roots)) := by
  let p := (X:ℂ[X])^m-1
  let q (w : ℂ) := ((X-C 3)^2-C w*X : ℂ[X])
  have hmon : p.Monic := by simpa [p] using monic_X_pow_sub_C (1:ℂ) hm.ne'
  have hc : p.roots.card=m := by
    rw [←(IsAlgClosed.splits p).natDegree_eq_card_roots]
    simpa [p] using (natDegree_X_pow_sub_C (R:=ℂ) (r:=1) (n:=m))
  have hom (s : Multiset ℂ) (a x : ℂ) (hx : x ≠ 0) :
      (s.map (fun w => a-w*x)).prod = x^s.card * (s.map (fun w => a/x-w)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons w t ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons,ih,pow_succ]
      have h : x*(a/x-w)=a-w*x := by field_simp
      rw [←h];ring
  have he : (X-C 3)^(2*m)-X^m = (p.roots.map q).prod := by
    apply Polynomial.funext
    intro x
    simp only [eval_sub,eval_pow,eval_X,eval_C,eval_multiset_prod,Multiset.map_map,Function.comp_def,q,eval_mul]
    by_cases hx : x=0
    · subst x
      simp [hc,hm.ne',pow_mul]
    · rw [hom _ _ _ hx,←(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmon,hc]
      simp only [p,eval_sub,eval_pow,eval_X,eval_one,div_pow,pow_mul]
      field_simp
  have hq : (0:ℂ[X]) ∉ p.roots.map q := by
    intro h
    obtain ⟨w,_,hw⟩ := Multiset.mem_map.mp h
    have hz := congrArg (Polynomial.eval 0) hw
    norm_num [q] at hz
  rw [he,roots_multiset_prod _ hq,Multiset.bind_map]

end OMA.S_mo_486714

namespace OMA.S_mo_486714
open Polynomial

private lemma sum_im_bound (s : Multiset ℂ) (h : ∀ z∈s, |z.im| ≤ 6*angular z) :
    |s.sum.im| ≤ 6*(s.map angular).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    have ha := h z (Multiset.mem_cons_self ..)
    have hb := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    simpa only [Multiset.sum_cons, Complex.add_im, Multiset.map_cons, mul_add] using
      (abs_add_le z.im s.sum.im).trans (add_le_add ha hb)

lemma quad_angle (w : ℂ) (hw : ‖w‖=1) :
    |w.im| ≤ 6 * ((((X-C (3:ℂ))^2 - C w*X).roots).map angular).sum := by
  let f : ℂ[X] := (X-C (3:ℂ))^2-C w*X
  have hform : f = X^2+C (-(6+w))*X+C 9 := by
    dsimp [f]
    simp only [map_neg, map_add, map_ofNat]
    ring
  have hm : f.Monic := by rw [hform]; monicity <;> decide
  have hd : f.natDegree=2 := by rw [hform]; compute_degree!
  have hc : f.nextCoeff = -(6+w) := by
    rw [nextCoeff,hd]
    norm_num [hform, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X]
  have hv := (IsAlgClosed.splits f).nextCoeff_eq_neg_sum_roots_of_monic hm
  rw [hc, neg_inj] at hv
  have him : f.roots.sum.im = w.im := by rw [← hv]; simp
  rw [← him]
  apply sum_im_bound
  intro z hz
  have he : f.eval z=0 := isRoot_of_mem_roots hz
  have hpow : (z-3)^2 = w*z := by simpa [f, sub_eq_zero] using he
  have heq := congrArg norm hpow
  rw [norm_pow, norm_mul, hw, one_mul] at heq
  have htri := norm_add_le (z-3) (3:ℂ)
  simp only [sub_add_cancel] at htri
  norm_num at htri
  have hbound : ‖z‖ ≤ 6 := by nlinarith [sq_nonneg (‖z-3‖-2)]
  by_cases h0 : z=0
  · simp [h0,angular]
  · have hzpos := norm_pos_iff.mpr h0
    calc |z.im| = angular z * ‖z‖ := by rw [angular, div_mul_cancel₀ _ hzpos.ne']
         _ ≤ angular z * 6 := mul_le_mul_of_nonneg_left hbound (by unfold angular; positivity)
         _ = _ := mul_comm _ _

end OMA.S_mo_486714


namespace OMA.S_mo_486714
open Polynomial Finset

lemma unity_im (m : ℕ) (hm : 2 < m) : (m:ℝ)/2 ≤
    ((((X:ℂ[X])^m-1).roots).map (fun w : ℂ => |w.im|)).sum := by
  let ζ := Complex.exp (2*Real.pi*Complex.I/m)
  have hm0 : m≠0 := by omega
  have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm0
  have hnorm (j : ℕ) : ‖ζ^j‖=1 := by rw [norm_pow,hζ.norm'_eq_one hm0,one_pow]
  have hsq : ζ^2≠1 := hζ.pow_ne_one_of_pos_of_lt (by decide) hm
  have htotal : ∑ j ∈ range m, (ζ^j)^2 = 0 := by
    have hh : (ζ^2)^m=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul,hζ.pow_eq_one,one_pow]
    have hg := geom_sum_mul (ζ^2) m
    rw [hh,sub_self] at hg
    have hzero := (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hsq)
    simpa only [← pow_mul,Nat.mul_comm] using hzero
  have hre : ∑ j ∈ range m, ((ζ^j)^2).re=0 := by
    simpa only [Complex.re_sum,Complex.zero_re] using congrArg Complex.re htotal
  have hit (j : ℕ) : 2*((ζ^j).im)^2 = 1-((ζ^j)^2).re := by
    have hh := Complex.sq_norm_sub_sq_im (ζ^j)
    rw [hnorm] at hh
    rw [pow_two (ζ^j),Complex.mul_re]
    nlinarith
  have him : (m:ℝ)/2 = ∑ j ∈ range m, (ζ^j).im^2 := by
    have h := Finset.sum_congr (s₁:=range m) rfl (fun j _ => hit j)
    rw [← Finset.mul_sum,Finset.sum_sub_distrib,hre,sub_zero] at h
    simp only [sum_const,card_range,nsmul_eq_mul,mul_one] at h
    linarith
  have hrts : ((X:ℂ[X])^m-1).roots = (Multiset.range m).map (fun j => ζ^j) := by
    simpa only [nthRoots,C_1,mul_one] using hζ.nthRoots_eq (one_pow m : (1:ℂ)^m=1)
  rw [hrts,Multiset.map_map,him]
  change _ ≤ ∑ j ∈ range m, |(ζ^j).im|
  apply sum_le_sum
  intro j _
  have hab := Complex.abs_im_le_norm (ζ^j)
  rw [hnorm] at hab
  nlinarith [sq_abs ((ζ^j).im),mul_nonneg (abs_nonneg ((ζ^j).im)) (sub_nonneg.mpr hab)]

end OMA.S_mo_486714

namespace OMA.S_mo_486714

open Polynomial Filter

private noncomputable def f (n : ℕ) : ℂ[X] := (X-C 3)^n
private noncomputable def g (n : ℕ) : ℂ[X] :=
  if 0<n ∧ Even n then f n - X^(n/2) else f n

private lemma data_fg (n : ℕ) :
    (f n).Monic ∧ (g n).Monic ∧ (f n).natDegree=n ∧ (g n).natDegree=n := by
  have hm : (f n).Monic := (monic_X_sub_C (3:ℂ)).pow n
  have hd : (f n).natDegree=n := by simp [f,natDegree_pow]
  unfold g
  split_ifs with h
  · have hlt : ((X:ℂ[X])^(n/2)).natDegree < (f n).natDegree := by
      rw [hd,natDegree_X_pow]
      omega
    exact ⟨hm,hm.sub_of_left (degree_lt_degree hlt),hd,(natDegree_sub_eq_left_of_natDegree_lt hlt).trans hd⟩
  · exact ⟨hm,hm,hd,hd⟩

private lemma exterior (n : ℕ) (z : ℂ) (h : (f n).IsRoot z ∨ (g n).IsRoot z) : 1 ≤ ‖z‖ := by
  by_contra! hz
  have hdist : 1 < ‖z-3‖ := by
    have htri := norm_add_le (3-z) z
    rw [sub_add_cancel,norm_sub_rev] at htri
    norm_num at htri
    linarith
  have hf : ¬ (f n).IsRoot z := by
    simpa [f,IsRoot] using pow_ne_zero n (show z-3 ≠ 0 by intro he; rw [he,norm_zero] at hdist; linarith)
  rcases h with h | h
  · exact hf h
  unfold g at h
  split_ifs at h with hn
  · have he : (z-3)^n = z^(n/2) := by simpa [f,IsRoot,sub_eq_zero] using h
    have he' := congrArg norm he
    simp only [norm_pow] at he'
    have := one_lt_pow₀ hdist hn.1.ne'
    have hle : ‖z‖^(n/2) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz.le
    linarith
  · exact hf h

private lemma uniform_gap (r : ℝ) (hr : 0<r) (hr' : r<1) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ z : ℂ, ‖z‖≤r → ‖(f n).eval z-(g n).eval z‖<ε := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr').comp
    (Nat.tendsto_div_const_atTop (n:=2) (by decide))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hε))
  refine ⟨N,fun n hn z hz => ?_⟩
  unfold g
  split_ifs
  · simp only [eval_sub,eval_pow,eval_X,sub_sub_cancel,norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg z) hz _).trans_lt (hN n hn)
  · simpa using hε

private lemma sum_quad (s : Multiset ℂ) (hs : ∀ w ∈ s, ‖w‖=1) :
    (s.map (fun w : ℂ => |w.im|)).sum ≤
      6 * (((s.bind (fun w : ℂ => ((X-C 3)^2-C w*X).roots)).map angular).sum) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons w s ih =>
    have hq := quad_angle w (hs w (Multiset.mem_cons_self ..))
    have hi := ih (fun z hz => hs z (Multiset.mem_cons_of_mem hz))
    simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.cons_bind,Multiset.map_add,
      Multiset.sum_add,mul_add]
    exact add_le_add hq hi

private lemma gap_even (m : ℕ) (hm : 2 < m) :
    (1:ℝ)/24 ≤ |angularMean (f (2*m))-angularMean (g (2*m))| := by
  have hf : angularMean (f (2*m))=0 := by
    simp [angularMean,f,roots_pow,Multiset.nsmul_singleton,angular]
  have he : g (2*m) = (X-C (3:ℂ))^(2*m)-X^m := by
    simp [g,f,show 0<2*m by omega]
  let s := ((X:ℂ[X])^m-1).roots
  have hs (w : ℂ) (hw : w ∈ s) : ‖w‖=1 := by
    have h := Polynomial.isRoot_of_mem_roots hw
    change ((X:ℂ[X])^m-1).eval w=0 at h
    exact Complex.norm_eq_one_of_pow_eq_one (n:=m) (by simpa [sub_eq_zero] using h) (by omega)
  have hsum := (unity_im m hm).trans (sum_quad s hs)
  have hh : (m:ℝ)/2 ≤ 6 * (((g (2*m)).roots.map angular).sum) := by
    rw [he,roots_factor m (by omega)]
    exact hsum
  rw [hf,zero_sub,abs_neg]
  apply le_trans _ (le_abs_self _)
  unfold angularMean
  rw [(data_fg (2*m)).2.2.2]
  apply (le_div_iff₀ (by positivity : (0:ℝ) < (2*m:ℕ))).mpr
  push_cast
  linarith

private theorem result : type_of% @main := by
  refine ⟨f,g,data_fg,exterior,uniform_gap,1/24,by norm_num,?_⟩
  intro N
  exact ⟨2*(N+3),by omega,gap_even (N+3) (by omega)⟩

end OMA.S_mo_486714

theorem OMA.solution : type_of% @OMA.S_mo_486714.main := OMA.S_mo_486714.result
