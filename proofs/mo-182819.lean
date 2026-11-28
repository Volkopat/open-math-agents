import OMAStatements.S_mo_182819

/-! Robert Israel proposed the trinomial family in a comment on Igor Rivin’s question.
The constant term of a proper factor of the auxiliary binomial would have
two positive conjugates, with an integral trace strictly between two and three. -/


namespace OMA.S_mo_182819
open Polynomial

noncomputable def basePoly : ℚ[X] := X^2 + 3*X + 1

lemma basePoly_natDegree : basePoly.natDegree=2 := by
  dsimp [basePoly]
  compute_degree!

lemma basePoly_irreducible : Irreducible basePoly := by
  apply (irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [basePoly_natDegree])
    (by rw [basePoly_natDegree]; decide)).mpr
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro r hr
  have he := isRoot_of_mem_roots hr
  change eval r basePoly=0 at he
  simp [basePoly] at he
  have hr' : (r:ℝ)^2+3*r+1=0 := by exact_mod_cast he
  have hsq : (Real.sqrt 5)^2 = (((2*r+3 : ℚ):ℝ))^2 := by
    push_cast
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
  have irr : Irrational (Real.sqrt 5) := by norm_num
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact irr ⟨2*r+3,h.symm⟩
  · exact irr ⟨-(2*r+3),by push_cast at *; exact h.symm⟩

instance basePoly_irredFact : Fact (Irreducible basePoly) := ⟨basePoly_irreducible⟩
abbrev K := AdjoinRoot basePoly
noncomputable def α : K := AdjoinRoot.root basePoly

noncomputable def e₁ : K →ₐ[ℚ] ℝ :=
  AdjoinRoot.liftAlgHom basePoly (Algebra.ofId ℚ ℝ) ((-3-Real.sqrt 5)/2) (by
    simp [basePoly]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)])

noncomputable def e₂ : K →ₐ[ℚ] ℝ :=
  AdjoinRoot.liftAlgHom basePoly (Algebra.ofId ℚ ℝ) ((-3+Real.sqrt 5)/2) (by
    simp [basePoly]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)])

lemma e₁_α : e₁ α = (-3-Real.sqrt 5)/2 := AdjoinRoot.liftAlgHom_root _ _ _ _
lemma e₂_α : e₂ α = (-3+Real.sqrt 5)/2 := AdjoinRoot.liftAlgHom_root _ _ _ _

private lemma exists_linear_rep (u : K) : ∃ a b : ℚ,
    u = algebraMap ℚ K a * α + algebraMap ℚ K b := by
  let pb := AdjoinRoot.powerBasis basePoly_irreducible.ne_zero
  obtain ⟨f,hdeg,hu⟩ := pb.exists_eq_aeval u
  have h2 : pb.dim=2 := basePoly_natDegree
  obtain ⟨a,b,hf⟩ := exists_eq_X_add_C_of_natDegree_le_one
    (show f.natDegree ≤ 1 by omega)
  refine ⟨a,b,?_⟩
  rw [hu,hf]
  simp [pb,α]

lemma trace_int {u : K} (hu : IsIntegral ℤ u) : ∃ z : ℤ, e₁ u + e₂ u = z := by
  obtain ⟨a,b,hab⟩ := exists_linear_rep u
  let q : ℚ := -3*a+2*b
  have he : e₁ u+e₂ u = (q:ℝ) := by
    rw [hab]
    simp only [map_add,map_mul,AlgHom.commutes,e₁_α,e₂_α]
    change ((a:ℝ)*((-3-Real.sqrt 5)/2)+b)+((a:ℝ)*((-3+Real.sqrt 5)/2)+b) = (q:ℝ)
    dsimp [q]
    push_cast
    ring
  have hi : IsIntegral ℤ ((q:ℚ):ℝ) := he ▸ (hu.map (e₁.restrictScalars ℤ)).add
    (hu.map (e₂.restrictScalars ℤ))
  have hq : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ ℝ).injective).mp hi
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
  exact ⟨z,he.trans (by rw [← hz]; norm_cast)⟩

end OMA.S_mo_182819

namespace OMA.S_mo_182819

open Polynomial Filter

private lemma prod_modulus (l : Multiset ℂ) (a : ℝ) (n : ℕ)
    (h : ∀ z ∈ l, ‖z‖^n = a) : ‖l.prod‖^n = a^l.card := by
  induction l using Multiset.induction_on with
  | empty => simp
  | cons z l ih =>
    simp only [Multiset.prod_cons,Multiset.card_cons,norm_mul,mul_pow,pow_succ]
    rw [h z (Multiset.mem_cons_self ..),ih (fun w hw => h w (Multiset.mem_cons_of_mem hw))]
    ring

lemma constant_factor (n : ℕ) (a : ℝ) (ha : 0<a) (g : ℝ[X]) (hg : g.Monic)
    (hd : 0<g.natDegree) (hdiv : g ∣ X^n+C a) :
    0 < g.coeff 0 ∧ (g.coeff 0)^n = a^g.natDegree := by
  classical
  have hnr (x : ℝ) (hx : 0 ≤ x) : g.eval x ≠ 0 := by
    intro he
    have h := Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdiv he
    simp only [eval_add,eval_pow,eval_X,eval_C] at h
    exact (add_pos_of_nonneg_of_pos (pow_nonneg hx _) ha).ne' h
  have hp : 0 < g.coeff 0 := by
    rw [coeff_zero_eq_eval_zero]
    by_contra! h
    have htop := g.tendsto_atTop_of_leadingCoeff_nonneg (natDegree_pos_iff_degree_pos.mp hd) (by simp [hg])
    obtain ⟨t, ht, hgt⟩ := ((eventually_ge_atTop (0:ℝ)).and (htop.eventually (eventually_ge_atTop (0:ℝ)))).exists
    obtain ⟨x,hx,hgx⟩ := intermediate_value_Icc ht g.continuous.continuousOn ⟨h,hgt⟩
    exact hnr x hx.1 hgx
  let G := g.map Complex.ofRealHom
  have hm : G.Monic := hg.map _
  have hs : G.Splits := IsAlgClosed.splits _
  have hdvd : G ∣ (X^n + C (a:ℂ)) := by
    simpa [G] using Polynomial.map_dvd Complex.ofRealHom hdiv
  have hr (z : ℂ) (hz : z ∈ G.roots) : ‖z‖^n = a := by
    have he := (Polynomial.mem_roots hm.ne_zero).mp hz
    have hw := he.dvd hdvd
    change (X^n+C (a:ℂ)).eval z = 0 at hw
    simp only [eval_add,eval_pow,eval_X,eval_C] at hw
    have hh : z^n = -(a:ℂ) := eq_neg_of_add_eq_zero_left hw
    have e := congrArg (fun u : ℂ => ‖u‖) hh
    simpa [norm_pow,Real.norm_eq_abs,abs_of_pos ha] using e
  refine ⟨hp,?_⟩
  have hc : ‖G.coeff 0‖ = g.coeff 0 := by
    simp [G,Real.norm_eq_abs,abs_of_pos hp]
  rw [← hc,hs.coeff_zero_eq_prod_roots_of_monic hm]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
  rw [prod_modulus _ _ _ hr,← hs.natDegree_eq_card_roots]
  simp [G]

end OMA.S_mo_182819

namespace OMA.S_mo_182819

open Polynomial

private lemma trace_bounds {a b u v : ℝ} {n d : ℕ}
    (ha : 1 < a) (hab : a*b = 1) (hu : 0 < u) (hv : 0 < v)
    (hd : 0 < d) (hdn : d < n) (h₁ : u^n = a^d) (h₂ : v^n = b^d) :
    2 < u+v ∧ u+v < a+b := by
  have hn : n ≠ 0 := by omega
  have au := lt_trans zero_lt_one ha
  have hprod : u*v=1 := by
    apply (pow_left_inj₀ (mul_pos hu hv).le zero_le_one hn).mp
    rw [mul_pow,h₁,h₂,← mul_pow,hab,one_pow,one_pow]
  have hu₁ : 1 < u := (one_lt_pow_iff_of_nonneg hu.le hn).mp (h₁ ▸ one_lt_pow₀ ha hd.ne')
  have hua : u < a := (pow_lt_pow_iff_left₀ hu.le au.le hn).mp (h₁ ▸ pow_lt_pow_right₀ ha hdn)
  constructor
  · apply (mul_lt_mul_iff_right₀ hu).mp
    nlinarith [sq_pos_of_pos (sub_pos.mpr hu₁)]
  · apply (mul_lt_mul_iff_right₀ (mul_pos au hu)).mp
    have h₃ := congrArg (fun x : ℝ => a*x) hprod
    have h₄ := congrArg (fun x : ℝ => u*x) hab
    nlinarith [mul_pos (sub_pos.mpr hua) (sub_pos.mpr (one_lt_mul_of_lt_of_le ha hu₁.le))]

private lemma factor_integral (n : ℕ) (hn : 0<n) (g : K[X]) (hg : g.Monic)
    (hd : g ∣ X^n - C α) : IsIntegral ℤ (g.coeff 0) := by
  let T : ℤ[X] := X^(2*n) + 3*X^n + 1
  have hm : T.Monic := by
    dsimp [T]
    rw [add_assoc]
    apply monic_X_pow_add
    apply lt_of_le_of_lt (degree_le_natDegree)
    exact_mod_cast (show (3*(X:ℤ[X])^n+1).natDegree < 2*n by
      have h : (3*(X:ℤ[X])^n+1).natDegree ≤ n := by compute_degree
      omega)
  have hα : α*(α+3) = -1 := by
    apply e₁.injective
    simp only [map_mul,map_add,map_ofNat,map_neg,map_one]
    change e₁ α * (e₁ α + 3) = -1
    rw [e₁_α]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤5)]
  have hC := congrArg (C : K → K[X]) hα
  simp only [map_mul,map_add,map_ofNat,map_neg,map_one] at hC
  apply isIntegral_coeff_of_dvd T g hm hg (hd.trans ?_) 0
  refine ⟨X^n + C α + 3, ?_⟩
  simp only [T,Polynomial.map_add,Polynomial.map_pow,map_X,Polynomial.map_mul,
    Polynomial.map_ofNat,Polynomial.map_one]
  rw [show 2*n = n+n by omega,pow_add]
  linear_combination hC

private lemma transport_real (e : K →ₐ[ℚ] ℝ) (n : ℕ) (g : K[X]) (hg : g.Monic)
    (hd : 0<g.natDegree) (h : g ∣ X^n - C α) (ha : 0 < -e α) :
    0 < e (g.coeff 0) ∧ (e (g.coeff 0))^n = (-e α)^g.natDegree := by
  have hv : g.map e.toRingHom ∣ X^n+C (-e α) := by
    simpa [sub_eq_add_neg] using Polynomial.map_dvd e.toRingHom h
  simpa using constant_factor n (-e α) ha (g.map e.toRingHom) (hg.map _) (by simpa using hd) hv

lemma binomial_irreducible (n : ℕ) (hn : 0<n) :
    Irreducible ((X:K[X])^n - C α) := by
  have hm := monic_X_pow_sub_C α hn.ne'
  have hne : (X:K[X])^n-C α ≠ 1 := by
    intro h
    have := congrArg natDegree h
    simp only [natDegree_X_pow_sub_C,natDegree_one] at this
    omega
  apply (hm.irreducible_iff_lt_natDegree_lt hne).mpr
  intro g hg hd hdiv
  rw [Finset.mem_Ioc,natDegree_X_pow_sub_C] at hd
  obtain ⟨hd, hd'⟩ := hd
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  have hpos := Real.sqrt_nonneg 5
  have ha : 1 < -e₁ α := by rw [e₁_α]; linarith
  have hb : 0 < -e₂ α := by rw [e₂_α]; nlinarith
  have hab : (-e₁ α)*(-e₂ α)=1 := by rw [e₁_α,e₂_α]; nlinarith
  have hsum : -e₁ α + -e₂ α=3 := by rw [e₁_α,e₂_α]; ring
  obtain ⟨hu,h₁⟩ := transport_real e₁ n g hg hd hdiv (lt_trans zero_lt_one ha)
  obtain ⟨hv,h₂⟩ := transport_real e₂ n g hg hd hdiv hb
  obtain ⟨hl,hr⟩ := trace_bounds ha hab hu hv hd (show g.natDegree<n by omega) h₁ h₂
  obtain ⟨z,hz⟩ := trace_int (factor_integral n hn g hg hdiv)
  rw [hz] at hl
  rw [hz,hsum] at hr
  have hl' : 2 < z := by exact_mod_cast hl
  have hr' : z < 3 := by exact_mod_cast hr
  omega

end OMA.S_mo_182819

namespace OMA.S_mo_182819
open Polynomial IntermediateField

lemma trinomial_irreducible (n : ℕ) (hn : 0<n) :
    Irreducible ((X:ℚ[X])^(2*n)+3*X^n+1) := by
  have hm : basePoly.Monic := by unfold basePoly; monicity <;> decide
  have h : Irreducible (basePoly.comp (X^n)) := by
    apply Polynomial.irreducible_comp hm (monic_X_pow n) basePoly_irreducible
    intro E _ _ x hx
    have hi : IsIntegral ℚ x := minpoly.ne_zero_iff.mp (hx ▸ basePoly_irreducible.ne_zero)
    let _ : Algebra ℚ ℚ⟮x⟯ := (ℚ⟮x⟯).algebra'
    let e₁ := AdjoinRoot.algEquivOfEq ℚ basePoly (minpoly ℚ x) hx.symm
    let e₂ := IntermediateField.adjoinRootEquivAdjoin ℚ hi
    let e := e₁.toRingEquiv.trans e₂.toRingEquiv
    have hα : e α = AdjoinSimple.gen ℚ x := by
      change e₂ (e₁ (AdjoinRoot.root basePoly)) = _
      rw [show e₁ (AdjoinRoot.root basePoly) = _ from AdjoinRoot.algEquivOfEq_root (R:=ℚ) _ _ hx.symm]
      exact IntermediateField.adjoinRootEquivAdjoin_apply_root ℚ hi
    have hmap : Irreducible (mapEquiv e ((X:K[X])^n-C α)) := by
      rw [MulEquiv.irreducible_iff]
      exact binomial_irreducible n hn
    simpa [mapEquiv_apply, hα] using hmap
  rw [show (X:ℚ[X])^(2*n)=(X^n)^2 by rw [← pow_mul, mul_comm]]
  simpa [basePoly, add_comp, mul_comp, pow_comp] using h

end OMA.S_mo_182819


namespace OMA.S_mo_182819
open Polynomial

lemma family_shape (n : ℕ) (hn : 0<n) :
    (family ℤ n).natDegree=2*n ∧ (family ℤ n).coeff n=3 ∧
    (∀ j ≤ 2*n, (family ℤ n).coeff j=(family ℤ n).coeff (2*n-j)) ∧
    (∀ j, |(family ℤ n).coeff j| ≤ 3) ∧ (∀ z : ℂ, ‖z‖=1 → (family ℂ n).eval z ≠0) := by
  have hc (j : ℕ) : (family ℤ n).coeff j =
      (if j=2*n then 1 else 0)+(if j=n then 3 else 0)+(if j=0 then 1 else 0) := by
    change (X^(2*n) + C (3:ℤ)*X^n+1).coeff j=_
    simp [coeff_X_pow,coeff_one,eq_comm]
  have top : (family ℤ n).coeff (2*n)=1 := by rw [hc]; split_ifs <;> omega
  refine ⟨natDegree_eq_of_le_of_coeff_ne_zero ?_ (top ▸ one_ne_zero),?_,?_,?_,?_⟩
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [hc]; split_ifs <;> omega
  · rw [hc]; split_ifs <;> omega
  · intro j hj
    rw [hc,hc]; split_ifs <;> omega
  · intro j
    rw [hc]; split_ifs <;> norm_num <;> omega
  · intro z hz h
    have he : z^(2*n)+3*z^n+1=0 := by simpa [family] using h
    have he' : 3*z^n = -(z^(2*n)+1) := by linear_combination he
    have hnrm := congrArg norm he'
    rw [norm_mul,norm_neg] at hnrm
    have ht := norm_add_le (z^(2*n)) 1
    rw [← hnrm] at ht
    norm_num [norm_pow,hz] at ht

end OMA.S_mo_182819

theorem OMA.solution : type_of% @OMA.S_mo_182819.main := by
  intro n hn
  obtain ⟨hd,hc,hs,hh,hu⟩ := OMA.S_mo_182819.family_shape n hn
  exact ⟨hd,hc,hs,hh,OMA.S_mo_182819.trinomial_irreducible n hn,hu⟩
