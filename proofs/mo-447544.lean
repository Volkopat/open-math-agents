import OMAStatements.S_mo_447544

/-!
# Five-term polynomials have simple roots

For 0 < p < q < r < n, all complex roots of 1+X^p+X^q+X^r−X^n are simple.
Question by ABB, https://mathoverflow.net/questions/447544 (CC BY-SA 4.0).
Credit: @connoranderson.

A repeated monic integral factor G is reciprocal. Indeed, write F=G²H
and compare F with (G*)²H, where G* reverses the coefficients. Both have
coefficient-square sum 5, value 3 at 1, and leading coefficient −1. Every
other coefficient lies in {0,1}. After normalizing G* to be monic, the first
coefficient where the two products could differ would have to be even.

Divide the exponents by their gcd. For any conjugate z of a repeated factor,
both z and its inverse are double roots. The five signed powers u_i satisfy
sum u_i = sum e_i*u_i = 0 and the same equations with u_i inverted. With
D(T) the product of the five linear factors T−e_i, the values u_i*D'(e_i)
interpolate a quadratic. The counterpart for inverse powers gives a second
quadratic, and their product is fixed by its values at the five exponents.
Normalization at zero and degree-two reflection leave at most six choices
even when the interpolating degree drops. The signed powers determine z.
This bounds the degree of G by 6, independently of all four exponents.

Landau's inequality gives M(G)^4 ≤ 5. Exact integer coefficient bounds,
Graeffe root squaring, and finite enumeration give either a real root or
a cyclotomic divisor. Descartes' rule forces four sign variations for two
distinct positive double roots after a possible change of sign of X. The
alternating five-term polynomial is positive on (0,1). The cyclotomic
cases are excluded by evaluating at 1, −1, or the Gaussian integer i.
-/

namespace FiveSparse
open Polynomial
open scoped Polynomial

noncomputable def F (p q r n : ℕ) : ℤ[X] := 1+X^p+X^q+X^r-X^n

private lemma coeff_F (p q r n k : ℕ) : (F p q r n).coeff k =
    (if k=0 then 1 else 0)+(if k=p then 1 else 0)+(if k=q then 1 else 0)+
      (if k=r then 1 else 0)-(if k=n then 1 else 0) := by
  simp [F,coeff_X_pow,coeff_one,eq_comm]

private lemma moments_F {p q r n : ℕ} (hp : 0<p) (hq : p<q) (hr : q<r) (hn : r<n) :
    (F p q r n).sum (fun _ a => a^2) = 5 ∧ (F p q r n).eval 1 = 3 ∧
    (F p q r n).natDegree=n ∧ (F p q r n).leadingCoeff = -1 ∧ (F p q r n).coeff 0=1 := by
  classical
  have hc : ∀ k, k ∉ ({0,p,q,r,n}:Finset ℕ) → (F p q r n).coeff k=0 := by
    intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
    simp [coeff_F,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2]
  have eqs : (F p q r n).support ⊆ ({0,p,q,r,n}:Finset ℕ) := by
    intro k hk
    exact Classical.byContradiction fun h => (mem_support_iff.mp hk) (hc k h)
  have hcoeff : (F p q r n).coeff n = -1 := by
    simp [coeff_F,show n≠0 by omega,show n≠p by omega,show n≠q by omega,hn.ne']
  have hd : (F p q r n).natDegree=n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · apply natDegree_le_iff_coeff_eq_zero.mpr
      intro k hk
      apply hc
      simp
      omega
    · rw [hcoeff]; decide
  refine ⟨?_,by norm_num [F],hd,by simpa [leadingCoeff,hd] using hcoeff,?_⟩
  · rw [sum_eq_of_subset _ (by simp) eqs]
    have h0q : 0<q := by omega
    have h0r : 0<r := by omega
    have h0n : 0<n := by omega
    have hpr := hq.trans hr
    have hpn := hpr.trans hn
    have hqn := hr.trans hn
    norm_num [coeff_F,hp.ne,hp.ne',h0q.ne,h0q.ne',h0r.ne,h0r.ne',h0n.ne,h0n.ne',
      hq.ne,hq.ne',hr.ne,hr.ne',hn.ne,hn.ne',hpr.ne,hpr.ne',hpn.ne,hpn.ne',hqn.ne,hqn.ne']
  · simp [coeff_F, hp.ne, show 0≠q by omega,show 0≠r by omega,show 0≠n by omega]

private lemma binary_coeffs (A : ℤ[X]) (h2 : A.sum (fun _ a => a^2)=5)
    (h1 : A.eval 1=3) (ht : A.leadingCoeff = -1) {k : ℕ} (hk : k≠A.natDegree) :
    A.coeff k=0 ∨ A.coeff k=1 := by
  classical
  rw [eval_eq_sum, sum_def] at h1
  simp only [one_pow,mul_one] at h1
  rw [sum_def] at h2
  let f (j : ℕ) := (A.coeff j)^2 - A.coeff j
  have hnon (j) : 0 ≤ f j := by
    dsimp [f]
    rcases le_or_gt (A.coeff j) 0 with h | h
    · nlinarith [sq_nonneg (A.coeff j)]
    · have : 0≤(A.coeff j)*(A.coeff j-1) := mul_nonneg (by omega) (by omega)
      nlinarith
  have tot : (∑ j ∈ A.support, f j) = 2 := by simp [f,Finset.sum_sub_distrib,h1,h2]
  have tf : f A.natDegree=2 := by change A.leadingCoeff^2-A.leadingCoeff=2; norm_num [ht]
  have mem : A.natDegree ∈ A.support := mem_support_iff.mpr (by change A.leadingCoeff ≠ 0; omega)
  by_cases memk : k∈A.support
  · have kle := Finset.single_le_sum (s:= A.support.erase A.natDegree) (f:=f)
        (fun j _ => hnon j) (Finset.mem_erase.mpr ⟨hk,memk⟩)
    have all := Finset.sum_erase_add _ f mem
    rw [tot,tf] at all
    have fk : f k=0 := by have := hnon k; omega
    have hk' : A.coeff k * (A.coeff k-1)=0 := by dsimp [f] at fk; nlinarith
    rcases mul_eq_zero.mp hk' with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · exact Or.inl (notMem_support_iff.mp memk)

private lemma sq_sum_swap (G H : ℤ[X]) :
    (G.mirror^2*H).sum (fun _ a => a^2) = (G^2*H).sum (fun _ a => a^2) := by
  let a := G.mirror^2*H
  let b := G^2*H
  have eqn : a*a.mirror=b*b.mirror := by
    simp only [a,b,pow_two,mirror_mul_of_domain,mirror_mirror]
    ring
  have hd : a.natDegree = b.natDegree := by
    have e := congrArg natDegree eqn
    simp only [natDegree_mul_mirror] at e
    omega
  have ht : a.natTrailingDegree = b.natTrailingDegree := by
    have e := congrArg natTrailingDegree eqn
    simp only [natTrailingDegree_mul_mirror] at e
    omega
  change a.sum _=b.sum _
  rw [← coeff_mul_mirror,← coeff_mul_mirror,eqn,hd,ht]

end FiveSparse

namespace FiveSparse
open Polynomial
open scoped Polynomial

theorem repeated_factor_reciprocal {p q r n : ℕ} (hp : 0<p) (hq : p<q) (hr : q<r)
    (hn : r<n) {G : ℤ[X]} (hm : G.Monic) (hdvd : G^2 ∣ F p q r n) :
    G.mirror = G ∨ G.mirror = -G := by
  classical
  obtain ⟨H,hH⟩ := hdvd
  obtain ⟨h2,h1,hdeg,hlead,hzero⟩ := moments_F hp hq hr hn
  have hc := congrArg (fun A : ℤ[X] => A.coeff 0) hH
  rw [hzero,coeff_zero_eq_eval_zero,eval_mul,eval_pow,← coeff_zero_eq_eval_zero,
    ← coeff_zero_eq_eval_zero] at hc
  have hunit : IsUnit (G.coeff 0) := by
    have hU : IsUnit ((G.coeff 0)^2 * H.coeff 0) := by rw [← hc]; exact isUnit_one
    exact isUnit_of_mul_isUnit_left (by simpa [pow_two,mul_assoc] using hU)
  have hs : G.coeff 0=1 ∨ G.coeff 0 = -1 := Int.isUnit_iff.mp hunit
  have ht : G.trailingCoeff=G.coeff 0 := by
    rw [trailingCoeff, natTrailingDegree_eq_zero.mpr (Or.inr hunit.ne_zero)]
  have hleadH : H.leadingCoeff = -1 := by simpa [hH,hm.leadingCoeff] using hlead
  let B := G.mirror^2*H
  have h2b : B.sum (fun _ a => a^2)=5 := (sq_sum_swap G H).trans (hH ▸ h2)
  have h1b : B.eval 1=3 := by simpa [B,hH,mirror_eval_one] using h1
  have hLb : B.leadingCoeff = -1 := by
    rcases hs with e | e <;> simp [B,ht,e,hleadH]
  have hNZ : H≠0 := by intro e; simp [e] at hleadH
  have hDb : B.natDegree=(F p q r n).natDegree := by
    simp [B,hH,natDegree_mul (pow_ne_zero 2 (mt mirror_eq_zero.mp hm.ne_zero)) hNZ,
      natDegree_mul (pow_ne_zero 2 hm.ne_zero) hNZ,mirror_natDegree]
  let T := if G.coeff 0=1 then G.mirror else -G.mirror
  have hmt : T.Monic := by
    rcases hs with e | e <;> simp [Monic,T,e,ht]
  have dt : T.natDegree=G.natDegree := by dsimp [T]; split <;> simp [mirror_natDegree]
  have sqt : T^2=G.mirror^2 := by dsimp [T]; split <;> ring
  suffices eq : G=T by
    by_cases hc1 : G.coeff 0=1
    · exact Or.inl (by simpa [T,hc1] using eq.symm)
    · exact Or.inr (by simpa [T,hc1,neg_eq_iff_eq_neg] using eq.symm)
  by_contra hne
  have hs2 : (G+T).leadingCoeff=2 := by
    rw [leadingCoeff_add_of_degree_eq (by rw [degree_eq_natDegree hm.ne_zero, degree_eq_natDegree hmt.ne_zero,dt])
        (by simp [hm.leadingCoeff,hmt.leadingCoeff]),hm.leadingCoeff,hmt.leadingCoeff]
    norm_num
  have he : F p q r n-B=(G-T)*(G+T)*H := by
    dsimp [B]
    rw [hH,← sqt]
    ring
  let k := (F p q r n-B).natDegree
  have hk : (F p q r n-B).coeff k = -2*(G-T).leadingCoeff := by
    change (F p q r n-B).leadingCoeff=_
    rw [he,leadingCoeff_mul,leadingCoeff_mul,hs2,hleadH]
    ring
  have hdiff : (G-T).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (sub_ne_zero.mpr hne)
  rw [coeff_sub] at hk
  by_cases top : k=(F p q r n).natDegree
  · have btop : k=B.natDegree := top.trans hDb.symm
    rw [show (F p q r n).coeff k = -1 from top ▸ hlead,
      show B.coeff k = -1 from btop ▸ hLb] at hk
    omega
  · have af := binary_coeffs _ h2 h1 hlead top
    have bf := binary_coeffs B h2b h1b hLb (fun e => top (e.trans hDb))
    omega

end FiveSparse

namespace FiveSparse
open Polynomial
open scoped Polynomial

theorem integral_double_factor {p q r n : ℕ} (hp : 0<p) (hq : p<q) (hr : q<r) (hn : r<n)
    {z : ℂ} (hz : aeval z (F p q r n)=0) (hd : aeval z (F p q r n).derivative=0) :
    IsIntegral ℤ z ∧ (minpoly ℤ z)^2 ∣ F p q r n := by
  obtain ⟨_,_,_,hL,_⟩ := moments_F hp hq hr hn
  have hm : (-(F p q r n)).Monic := by rw [Monic,leadingCoeff_neg,hL]; norm_num
  have hi : IsIntegral ℤ z := by
    refine ⟨_,hm,?_⟩
    change aeval z (-(F p q r n))=0
    rw [map_neg,hz,neg_zero]
  refine ⟨hi,?_⟩
  let g := minpoly ℤ z
  obtain ⟨H,hH⟩ := minpoly.isIntegrallyClosed_dvd hi hz
  have hg : aeval z g=0 := minpoly.aeval ..
  have hdg : aeval z g.derivative ≠ 0 := by
    intro eg
    have hdiv : g ∣ g.derivative := minpoly.isIntegrallyClosed_dvd hi eg
    have pos := minpoly.natDegree_pos hi
    have le := natDegree_le_of_dvd hdiv (derivative_ne_zero.mpr pos.ne')
    exact (natDegree_derivative_lt pos.ne').not_ge le
  rw [hH,derivative_mul,map_add,map_mul,map_mul] at hd
  change aeval z g.derivative * aeval z H + aeval z g * aeval z H.derivative=0 at hd
  rw [hg,zero_mul,add_zero] at hd
  obtain ⟨B,hB⟩ := minpoly.isIntegrallyClosed_dvd hi ((mul_eq_zero.mp hd).resolve_left hdg)
  exact ⟨B,by rw [hH,hB,pow_two,mul_assoc]⟩

theorem mahler_bound {p q r n : ℕ} (hp : 0<p) (hq : p<q) (hr : q<r) (hn : r<n)
    {G : ℤ[X]} (hdiv : G^2 ∣ F p q r n) : ((G.map (Int.castRingHom ℂ)).mahlerMeasure)^4 ≤ 5 := by
  classical
  obtain ⟨H,hH⟩ := hdiv
  obtain ⟨h2,_,_,hL,_⟩ := moments_F hp hq hr hn
  have hHnz : H≠0 := by intro h; simp [hH,h] at hL
  let φ := Int.castRingHom ℂ
  let f := F p q r n
  have ht : (∑ i ∈ (f.map φ).support, ‖(f.map φ).coeff i‖^2) = 5 := by
    rw [support_map_of_injective f (Int.castRingHom ℂ).injective_int]
    simp only [coeff_map,φ,Int.coe_castRingHom,Complex.norm_intCast,sq_abs]
    exact_mod_cast h2
  have M := (f.map φ).mahlerMeasure_le_sqrt_sum_sq_norm_coeff
  rw [ht] at M
  have bound : (G.map φ).mahlerMeasure^2*(H.map φ).mahlerMeasure ≤ Real.sqrt 5 := by
    simpa [f,hH,pow_two,mahlerMeasure_mul] using M
  have low : 1 ≤ (H.map φ).mahlerMeasure := one_le_mahlerMeasure_of_ne_zero hHnz
  have mid : (G.map φ).mahlerMeasure^2 ≤ Real.sqrt 5 :=
    (le_mul_of_one_le_right (sq_nonneg _) low).trans bound
  have sqb := mul_self_le_mul_self (sq_nonneg _) mid
  rw [← sq, ← pow_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ)≤5)] at sqb
  exact sqb

theorem root_of_inverse {K : Type*} [Field K] [CharZero K] {g : ℤ[X]} {x : K} (hx : x≠0)
    (hr : g.reverse = g) (he : aeval x g=0) : aeval x⁻¹ g=0 := by
  let _ := invertibleOfNonzero hx
  have h := (eval₂_reverse_eq_zero_iff (algebraMap ℤ K) x g).mpr he
  simpa only [invOf_eq_inv,hr,aeval_def] using h

theorem root_and_derivative_of_sq_dvd {K : Type*} [Field K] [CharZero K] {g f : ℤ[X]} {x : K}
    (hd : g^2 ∣ f) (h : aeval x g=0) : aeval x f=0 ∧ aeval x f.derivative=0 := by
  obtain ⟨q,rfl⟩ := hd
  simp [pow_two,derivative_mul,h]

end FiveSparse

namespace FiveSparse
open Polynomial
open scoped Polynomial

private lemma const_eval {K : Type*} [Field K] [CharZero K] {p q r n : ℕ}
    (hp : 0<p) (hq : p<q) (hr : q<r) (hn : r<n) :
    aeval (0:K) (F p q r n)=1 := by
  simp [F,hp.ne',show q≠0 by omega,show r≠0 by omega,show n≠0 by omega]

private theorem reverse_eq_self {p q r n : ℕ} (hp : 0<p) (hq : p<q) (hr : q<r) (hn : r<n)
    {g : ℤ[X]} (hm : g.Monic) (hd : g^2 ∣ F p q r n) : g.reverse=g := by
  have dv : g ∣ F p q r n := (dvd_pow_self g two_ne_zero).trans hd
  have c0 : g.coeff 0 ≠ 0 := by
    intro h
    have dvd := Polynomial.eval_dvd (x:=0) dv
    rw [← coeff_zero_eq_eval_zero,h] at dvd
    have hc := (moments_F hp hq hr hn).2.2.2.2
    rw [← coeff_zero_eq_eval_zero,hc] at dvd
    simp at dvd
  have hmrev : g.mirror=g.reverse := by
    simp [mirror,natTrailingDegree_eq_zero.mpr (Or.inr c0)]
  rcases repeated_factor_reciprocal hp hq hr hn hm hd with eq|eq
  · rwa [hmrev] at eq
  · have ev := g.mirror_eval_one
    rw [eq,eval_neg] at ev
    have gz : g.eval 1=0 := by omega
    have dv1 := Polynomial.eval_dvd (x:=1) dv
    rw [gz,(moments_F hp hq hr hn).2.1] at dv1
    norm_num at dv1

private theorem degree_bound {p q r n : ℕ} (hp : 0<p) (hq : p<q) (hr : q<r) (hn : r<n)
    {z : ℂ} (hi : IsIntegral ℤ z) (hd : (minpoly ℤ z)^2 ∣ F p q r n)
    (hrev : (minpoly ℤ z).reverse=minpoly ℤ z)
    (cb : ∀ S : Finset ℂ, (∀ x ∈ S, x≠0) →
      (∀ x ∈ S, aeval x (F p q r n)=0 ∧ aeval x (F p q r n).derivative=0 ∧
        aeval x⁻¹ (F p q r n)=0 ∧ aeval x⁻¹ (F p q r n).derivative=0) → S.card≤6) :
    (minpoly ℤ z).natDegree≤6 := by
  classical
  let g := minpoly ℤ z
  let G := g.map (algebraMap ℤ ℂ)
  let S := G.roots.toFinset
  have eqQ : minpoly ℚ z=g.map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi
  have splitG := IsAlgClosed.splits G
  have monG : G.Monic := (minpoly.monic hi).map _
  have eqG : G=(minpoly ℚ z).map (algebraMap ℚ ℂ) := by
    rw [eqQ,map_map,← IsScalarTower.algebraMap_eq]
  have sepG : G.Separable := by
    rw [eqG]
    exact (minpoly.irreducible (hi.tower_top (A:=ℚ))).separable.map
  have degS : S.card=g.natDegree := by
    rw [show S=G.roots.toFinset from rfl,Multiset.toFinset_card_of_nodup (nodup_roots sepG),
      ← splitG.natDegree_eq_card_roots]
    exact natDegree_map_eq_of_injective (algebraMap ℤ ℂ).injective_int g
  have memS (x : ℂ) (hx : x∈S) : aeval x g=0 := by
    have e := (mem_roots monG.ne_zero).mp (Multiset.mem_toFinset.mp hx)
    simpa only [IsRoot,G,eval_map_algebraMap] using e
  have nz (x : ℂ) (hx : x∈S) : x≠0 := by
    rintro rfl
    have e := (root_and_derivative_of_sq_dvd hd (memS 0 hx)).1
    rw [const_eval hp hq hr hn] at e
    exact one_ne_zero e
  rw [← show S.card=(minpoly ℤ z).natDegree from degS]
  apply cb S nz
  intro x hx
  have e := memS x hx
  have i := root_of_inverse (nz x hx) hrev e
  obtain ⟨a,b⟩ := root_and_derivative_of_sq_dvd hd e
  exact ⟨a,b,root_and_derivative_of_sq_dvd hd i⟩

end FiveSparse

namespace FiveSparse
open Polynomial
open scoped Polynomial

private lemma step_sign (P : ℝ[X]) {k : ℕ} (c : ℝ) (h : P.natDegree<k) (hc : c≠0) :
    (P+monomial k c).natDegree=k ∧ (P+monomial k c).leadingCoeff=c ∧
    (P+monomial k c).signVariations=P.signVariations+
      (if SignType.sign c = -SignType.sign P.leadingCoeff then 1 else 0) := by
  classical
  have deg : (monomial k c).natDegree=k := by simp [natDegree_monomial,hc]
  have hd : P.natDegree < (monomial k c).natDegree := by rwa [deg]
  have hl : (P+monomial k c).leadingCoeff=c := by
    rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hd),leadingCoeff_monomial]
  have he : (P+monomial k c).eraseLead=P := by rw [eraseLead_add_of_natDegree_lt_right hd]; simp
  refine ⟨(natDegree_add_eq_right_of_natDegree_lt hd).trans deg,hl,?_⟩
  have hnz : P+monomial k c≠0 := leadingCoeff_ne_zero.mp (by rwa [hl])
  rw [signVariations_eq_eraseLead_add_ite hnz,hl,he]

private lemma count_two_doubles (P : ℝ[X]) (hP : P≠0) {x y : ℝ} (hx : 0<x) (hy : 0<y)
    (hne : x≠y) (hx' : P.IsRoot x ∧ P.derivative.IsRoot x)
    (hy' : P.IsRoot y ∧ P.derivative.IsRoot y) : 4≤P.signVariations := by
  classical
  have cx : 2≤P.roots.count x := by rw [count_roots]; exact (one_lt_rootMultiplicity_iff_isRoot hP).mpr hx'
  have cy : 2≤P.roots.count y := by rw [count_roots]; exact (one_lt_rootMultiplicity_iff_isRoot hP).mpr hy'
  have hsub : ({x,x,y,y}:Multiset ℝ) ≤ P.roots := by
    apply Multiset.le_iff_count.mpr
    intro a
    by_cases ex : a=x
    · subst a; simpa [hne,hne.symm] using cx
    by_cases ey : a=y
    · subst a; simpa [hne,hne.symm] using cy
    · simp [ex,ey]
  have h := Multiset.countP_le_of_le (p := fun t : ℝ => 0<t) hsub
  have lower : 4 ≤ P.roots.countP (0<·) := by
    simpa [hx,hy,Multiset.countP_eq_card_filter,Multiset.filter_singleton] using h
  exact lower.trans P.roots_countP_pos_le_signVariations

private noncomputable def signedF (p q r n : ℕ) (a b c d : ℝ) : ℝ[X] :=
  1+monomial p a+monomial q b+monomial r c+monomial n d

private lemma alternating_of_four {p q r n : ℕ} (hp : 0<p) (hq : p<q) (hr : q<r) (hn : r<n)
    {a b c d : ℝ} (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) (hc : c=1 ∨ c= -1) (hd : d=1 ∨ d= -1)
    (h : 4 ≤ (signedF p q r n a b c d).signVariations) :
    a= -1 ∧ b=1 ∧ c= -1 ∧ d=1 := by
  let P : ℝ[X] := 1+monomial p a
  let Q := P+monomial q b
  let R := Q+monomial r c
  have s0 := step_sign (1:ℝ[X]) a (by simpa using hp) (by rcases ha with h|h <;> norm_num [h])
  have s1 := step_sign P b (s0.1.trans_lt hq) (by rcases hb with h|h <;> norm_num [h])
  have s2 := step_sign Q c (s1.1.trans_lt hr) (by rcases hc with h|h <;> norm_num [h])
  have s3 := step_sign R d (s2.1.trans_lt hn) (by rcases hd with h|h <;> norm_num [h])
  change 4 ≤ (R+monomial n d).signVariations at h
  rw [s3.2.2,s2.2.2,s1.2.2,s0.2.2,s0.2.1,s1.2.1,s2.2.1] at h
  have lone : (1 : ℝ[X]).signVariations=0 := by
    simpa only [monomial_zero_left,C_1] using signVariations_monomial (R:=ℝ) 0 1
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> rcases hc with rfl|rfl <;>
    rcases hd with rfl|rfl <;> norm_num [lone,Left.sign_neg] at h
  all_goals norm_num

theorem signed_real_exclusion {p q r n : ℕ} (hp : 0<p) (hq : p<q) (hr : q<r) (hn : r<n)
    {a b c d : ℝ} (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) (hc : c=1 ∨ c= -1) (hd : d=1 ∨ d= -1)
    {t u : ℝ} (ht : 0<t) (ht' : t<1) (hu : 0<u) (hne : t≠u)
    (h1 : (signedF p q r n a b c d).IsRoot t ∧ (signedF p q r n a b c d).derivative.IsRoot t)
    (h2 : (signedF p q r n a b c d).IsRoot u ∧ (signedF p q r n a b c d).derivative.IsRoot u) : False := by
  let P := signedF p q r n a b c d
  have hc0 : P.coeff 0=1 := by
    simp [P,signedF,coeff_monomial,hp.ne',show q≠0 by omega,show r≠0 by omega,show n≠0 by omega]
  have hP : P≠0 := by intro e; simp [e] at hc0
  obtain ⟨rfl,rfl,rfl,rfl⟩ := alternating_of_four hp hq hr hn ha hb hc hd
    (count_two_doubles P hP ht hu hne h1 h2)
  have h0 := h1.1
  simp [Polynomial.IsRoot,signedF,eval_monomial] at h0
  have htp : t^p<1 := pow_lt_one₀ ht.le ht' hp.ne'
  have hqr : t^r≤t^q := pow_le_pow_of_le_one ht.le ht'.le hr.le
  linarith [pow_pos ht n]

end FiveSparse

namespace FiveSparse
open Polynomial
open scoped Polynomial

private lemma signed_double {p q r n : ℕ} {s t : ℝ}
    (hz : aeval (s*t) (F p q r n)=0) (hd : aeval (s*t) (F p q r n).derivative=0) :
    (signedF p q r n (s^p) (s^q) (s^r) (-(s^n))).IsRoot t ∧
    (signedF p q r n (s^p) (s^q) (s^r) (-(s^n))).derivative.IsRoot t := by
  let f := (F p q r n).map (algebraMap ℤ ℝ)
  have e : signedF p q r n (s^p) (s^q) (s^r) (-(s^n))=f.comp (C s*X) := by
    simp [signedF,f,F,← C_mul_X_pow_eq_monomial,mul_pow,sub_eq_add_neg]
  have h0 : f.eval (s*t)=0 := (eval_map_algebraMap _ _).trans hz
  have h1 : f.derivative.eval (s*t)=0 := by
    rw [show f=(F p q r n).map (algebraMap ℤ ℝ) from rfl,derivative_map,eval_map_algebraMap,hd]
  rw [e]
  constructor
  · simp [IsRoot,eval_comp,h0]
  · simp [IsRoot,derivative_comp,eval_comp,h1]

private lemma real_exclusion {p q r n : ℕ} (hp : 0<p) (hq : p<q) (hr : q<r) (hn : r<n)
    {x : ℝ} (hx : x≠0)
    (h : aeval x (F p q r n)=0 ∧ aeval x (F p q r n).derivative=0)
    (hi : aeval x⁻¹ (F p q r n)=0 ∧ aeval x⁻¹ (F p q r n).derivative=0) : False := by
  have x1 : x≠1 := by rintro rfl; have e:=h.1; norm_num [F] at e
  have xm : x≠ -1 := by
    rintro rfl
    have e := h.1
    simp only [F,map_sub,map_add,map_one,map_pow,aeval_X] at e
    rcases neg_one_pow_eq_or ℝ p with ep|ep <;> rcases neg_one_pow_eq_or ℝ q with eq|eq <;>
      rcases neg_one_pow_eq_or ℝ r with er|er <;> rcases neg_one_pow_eq_or ℝ n with en|en <;>
      linarith only [e,ep,eq,er,en]
  let s : ℝ := if 0<x then 1 else -1
  let t := |x|
  have hs : s=1 ∨ s= -1 := by dsimp [s]; split <;> simp
  have hst : s*t=x := by
    by_cases pos : 0<x
    · simp [s,t,pos,abs_of_pos pos]
    · simp [s,t,pos,abs_of_nonpos (by linarith : x≤0)]
  have hsi : s*t⁻¹=x⁻¹ := by rw [← hst, mul_inv_rev]; rcases hs with h|h <;> simp [h]
  have signPow (k : ℕ) : s^k=1 ∨ s^k= -1 := by
    rcases hs with en|en
    · simp [en]
    · simpa [en] using neg_one_pow_eq_or ℝ k
  have signN : -(s^n)=1 ∨ -(s^n)= -1 := by
    rcases signPow n with h|h <;> simp [h]
  have ht : 0<t := abs_pos.mpr hx
  have ht1 : t≠1 := by
    intro e
    rw [e,mul_one] at hst
    exact hs.elim (fun h => x1 (hst.symm.trans h)) (fun h => xm (hst.symm.trans h))
  have H := signed_double (s:=s) (t:=t) (hst ▸ h.1) (hst ▸ h.2)
  have I := signed_double (s:=s) (t:=t⁻¹) (hsi ▸ hi.1) (hsi ▸ hi.2)
  have posi : 0<t⁻¹ := inv_pos.mpr ht
  rcases lt_or_gt_of_ne ht1 with lt|gt
  · exact signed_real_exclusion hp hq hr hn (signPow _) (signPow _) (signPow _) signN
      ht lt posi (lt.trans (one_lt_inv₀ ht |>.mpr lt)).ne H I
  · exact signed_real_exclusion hp hq hr hn (signPow _) (signPow _) (signPow _) signN
      posi (inv_lt_one_of_one_lt₀ gt) ht ((inv_lt_one_of_one_lt₀ gt).trans gt).ne I H

end FiveSparse

namespace OMA.S_mo_447544
namespace Interpolation
open Polynomial Finset

noncomputable def numerator (e u : Fin 5 → ℂ) : ℂ[X] :=
    C (u 2 * e 2 * (e 2-e 1)) * (X-C (e 3)) * (X-C (e 4))
  + C (u 3 * e 3 * (e 3-e 1)) * (X-C (e 2)) * (X-C (e 4))
  + C (u 4 * e 4 * (e 4-e 1)) * (X-C (e 2)) * (X-C (e 3))

noncomputable def weight (e : Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![(e 0-e 1)*(e 0-e 2)*(e 0-e 3)*(e 0-e 4),
    (e 1-e 0)*(e 1-e 2)*(e 1-e 3)*(e 1-e 4),
    (e 2-e 0)*(e 2-e 1)*(e 2-e 3)*(e 2-e 4),
    (e 3-e 0)*(e 3-e 1)*(e 3-e 2)*(e 3-e 4),
    (e 4-e 0)*(e 4-e 1)*(e 4-e 2)*(e 4-e 3)]

lemma weight_ne (e : Fin 5 → ℂ) (he : Function.Injective e) (i : Fin 5) : weight e i ≠ 0 := by
  fin_cases i <;> simp [weight,he.eq_iff,sub_ne_zero]

lemma numerator_degree (e u : Fin 5 → ℂ) : (numerator e u).natDegree ≤ 2 := by
  unfold numerator
  compute_degree

lemma numerator_eval (e u : Fin 5 → ℂ) (h0 : e 0 = 0)
    (hu : ∑ i, u i = 0) (heu : ∑ i, e i*u i = 0) (i : Fin 5) :
    (numerator e u).eval (e i) = u i * weight e i := by
  simp only [Fin.sum_univ_five,h0,zero_mul,zero_add] at hu heu
  fin_cases i
  · change (numerator e u).eval (e 0) = u 0 * weight e 0
    simp [numerator,weight,h0]
    linear_combination (e 2*e 3*e 4)*heu - (e 1*e 2*e 3*e 4)*hu
  · change (numerator e u).eval (e 1) = u 1 * weight e 1
    simp [numerator,weight,h0]
    linear_combination -((e 1-e 2)*(e 1-e 3)*(e 1-e 4))*heu
  · change (numerator e u).eval (e 2) = u 2 * weight e 2
    simp [numerator,weight,h0]
    ring
  · change (numerator e u).eval (e 3) = u 3 * weight e 3
    simp [numerator,weight,h0]
    ring
  · change (numerator e u).eval (e 4) = u 4 * weight e 4
    simp [numerator,weight,h0]
    ring

end Interpolation
end OMA.S_mo_447544

namespace OMA.S_mo_447544
open Polynomial Finset
open Interpolation

/-- Four moment equations bound the number of distinct reciprocal profiles at five
nodes by the number of pairs of roots of a fixed quartic. -/
theorem reciprocal_profile_bound (S : Finset ℂ) (e : Fin 5 → ℂ) (he : Function.Injective e)
    (he0 : e 0 = 0) (u : ℂ → Fin 5 → ℂ) (hi : Set.InjOn u (↑S : Set ℂ))
    (h0 : ∀ z ∈ S, u z 0 = 1) (hne : ∀ z ∈ S, ∀ i, u z i ≠ 0)
    (h : ∀ z ∈ S, (∑ i, u z i) = 0 ∧ (∑ i, e i * u z i) = 0 ∧
      (∑ i, (u z i)⁻¹) = 0 ∧ (∑ i, e i * (u z i)⁻¹) = 0) : S.card ≤ 6 := by
  classical
  obtain hs | ⟨z₀,hz₀⟩ := S.eq_empty_or_nonempty
  · simp [hs]
  let A (z : ℂ) := numerator e (u z)
  let B (z : ℂ) := numerator e (fun i => (u z i)⁻¹)
  have ha (z : ℂ) (hz : z ∈ S) (i : Fin 5) : (A z).eval (e i) = u z i * weight e i :=
    numerator_eval e _ he0 (h z hz).1 (h z hz).2.1 i
  have hb (z : ℂ) (hz : z ∈ S) (i : Fin 5) : (B z).eval (e i) = (u z i)⁻¹ * weight e i :=
    numerator_eval e _ he0 (h z hz).2.2.1 (h z hz).2.2.2 i
  have ha₂ (z) : (A z).natDegree ≤ 2 := numerator_degree e _
  have hb₂ (z) : (B z).natDegree ≤ 2 := numerator_degree e _
  have hab (z) : (A z*B z).natDegree ≤ 4 := (natDegree_mul_le).trans (Nat.add_le_add (ha₂ _) (hb₂ _))
  have eqn (z : ℂ) (hz : z ∈ S) : A z * B z = A z₀ * B z₀ := by
    apply eq_of_natDegree_lt_card_of_eval_eq _ _ he
    · intro i
      simp only [eval_mul,ha z hz,hb z hz,ha z₀ hz₀,hb z₀ hz₀]
      field_simp [hne z hz i,hne z₀ hz₀ i]
    · simpa using (show max (A z*B z).natDegree (A z₀*B z₀).natDegree < 5 from
        lt_of_le_of_lt (max_le (hab _) (hab _)) (by decide))
  let f (z : ℂ) := (A z).reflect 2
  let U := (A z₀ * B z₀).reflect 4
  have coeff (z : ℂ) (hz : z ∈ S) : (f z).coeff 2 = weight e 0 := by
    simpa [f,revAt_le,coeff_zero_eq_eval_zero,he0,h0 z hz] using ha z hz 0
  have deg (z : ℂ) (hz : z ∈ S) : (f z).natDegree = 2 :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_reflect_le.trans (max_le (by rfl) (ha₂ z)))
      ((coeff z hz).trans_ne (weight_ne e he 0))
  have hU (z : ℂ) (hz : z ∈ S) : U = f z * (B z).reflect 2 := by
    dsimp [U,f]; rw [← eqn z hz]; exact reflect_mul _ _ (ha₂ z) (hb₂ z)
  have Unz : U ≠ 0 := by
    dsimp [U]; rw [reflect_eq_zero_iff,mul_eq_zero,not_or]
    constructor
    · intro hh
      have heval := ha z₀ hz₀ 0
      simp [hh,h0 z₀ hz₀] at heval
      exact weight_ne e he 0 heval.symm
    · intro hh
      have heval := hb z₀ hz₀ 0
      simp [hh,h0 z₀ hz₀] at heval
      exact weight_ne e he 0 heval.symm
  let P := U.roots.powersetCard 2
  have maps : Set.MapsTo (fun z => (f z).roots) (↑S : Set ℂ) (↑P.toFinset : Set (Multiset ℂ)) := by
    intro z hz
    apply Multiset.mem_toFinset.mpr
    apply Multiset.mem_powersetCard.mpr
    exact ⟨Polynomial.roots.le_of_dvd Unz ⟨_,hU z hz⟩, IsAlgClosed.card_roots_eq_natDegree.trans (deg z hz)⟩
  have inj : Set.InjOn (fun z => (f z).roots) (↑S : Set ℂ) := by
    intro z hz w hw eqroots
    change (f z).roots = (f w).roots at eqroots
    have matchLead : (f z).leadingCoeff = (f w).leadingCoeff := by
      simp only [leadingCoeff,deg z hz,deg w hw,coeff z hz,coeff w hw]
    have eqf : f z = f w := by
      rw [(IsAlgClosed.splits (f z)).eq_prod_roots,(IsAlgClosed.splits (f w)).eq_prod_roots,eqroots,matchLead]
    have ea : A z = A w := by simpa [f] using congrArg (Polynomial.reflect 2) eqf
    apply hi hz hw; funext i
    have ee := congrArg (fun p : ℂ[X] => p.eval (e i)) ea
    simpa [ha z hz i,ha w hw i,weight_ne e he i] using ee
  have hdegU : U.natDegree ≤ 4 := natDegree_reflect_le.trans (max_le (by rfl) (hab z₀))
  calc
    _ ≤ P.toFinset.card := Finset.card_le_card_of_injOn _ maps inj
    _ ≤ P.card := Multiset.toFinset_card_le _
    _ = U.natDegree.choose 2 := by simp [P,Multiset.card_powersetCard,IsAlgClosed.card_roots_eq_natDegree]
    _ ≤ Nat.choose 4 2 := Nat.choose_le_choose 2 hdegU
    _ = 6 := by decide

end OMA.S_mo_447544

namespace OMA.S_mo_447544

/-- Nonzero complex numbers are determined by their powers at relatively prime exponents. -/
theorem eq_of_four_powers {p q r n : ℕ} (hg : p.gcd (q.gcd (r.gcd n)) = 1)
    {z w : ℂ} (hw : w ≠ 0) (hp : z^p = w^p) (hq : z^q = w^q)
    (hr : z^r = w^r) (hn : z^n = w^n) : z = w := by
  have aux (k : ℕ) (hk : z^k = w^k) : orderOf (z/w) ∣ k :=
    orderOf_dvd_of_pow_eq_one (by rw [div_pow,hk,div_self (pow_ne_zero _ hw)])
  have hd := Nat.dvd_gcd (aux p hp) (Nat.dvd_gcd (aux q hq) (Nat.dvd_gcd (aux r hr) (aux n hn)))
  rw [hg,Nat.dvd_one,orderOf_eq_one_iff] at hd
  exact (div_eq_one_iff_eq hw).mp hd

end OMA.S_mo_447544

namespace OMA.S_mo_447544
open Polynomial Finset
namespace Interpolation

noncomputable def exponents (p q r n : ℕ) : Fin 5 → ℂ := ![0,(p:ℂ),(q:ℂ),(r:ℂ),(n:ℂ)]
noncomputable def powers (p q r n : ℕ) (z : ℂ) : Fin 5 → ℂ := ![1,z^p,z^q,z^r,-z^n]
noncomputable def five (p q r n : ℕ) : ℂ[X] := 1 + X^p + X^q + X^r - X^n

lemma euler_xpow (z : ℂ) {k : ℕ} (hk : 0 < k) :
    z * (Polynomial.derivative (X^k : ℂ[X])).eval z = (k:ℂ)*z^k := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Polynomial.derivative_X_pow]
  simp only [Nat.succ_sub_one,eval_mul,eval_C,eval_pow,eval_X,pow_succ]
  ring

lemma moments_of_double {p q r n : ℕ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hn : 0 < n)
    (z : ℂ) (h : (five p q r n).IsRoot z) (dh : (five p q r n).derivative.IsRoot z) :
    (∑ i, powers p q r n z i) = 0 ∧
      (∑ i, exponents p q r n i*powers p q r n z i) = 0 := by
  constructor
  · simpa [five,Polynomial.IsRoot,powers,Fin.sum_univ_five,sub_eq_add_neg,add_assoc] using h
  · have hh := congrArg (z * ·) dh
    change z * (five p q r n).derivative.eval z = z * 0 at hh
    simp only [five,derivative_sub,derivative_add,derivative_one,zero_add,eval_sub,eval_add,
      mul_sub,mul_add,euler_xpow z hp,euler_xpow z hq,euler_xpow z hr,euler_xpow z hn,mul_zero] at hh
    simpa [exponents,powers,Fin.sum_univ_five,sub_eq_add_neg,add_assoc] using hh

end Interpolation
open Interpolation

/-- At most six nonzero numbers can be double roots together with their reciprocals. -/
theorem reciprocal_double_roots_card (S : Finset ℂ) {p q r n : ℕ} (hp : 0 < p) (hpq : p < q)
    (hqr : q < r) (hrn : r < n) (hg : p.gcd (q.gcd (r.gcd n)) = 1)
    (hne : ∀ z ∈ S, z ≠ 0) (hh : ∀ z ∈ S, (five p q r n).IsRoot z ∧
      (five p q r n).derivative.IsRoot z ∧ (five p q r n).IsRoot z⁻¹ ∧
      (five p q r n).derivative.IsRoot z⁻¹) : S.card ≤ 6 := by
  let v := exponents p q r n
  let u := powers p q r n
  have h₁ : Function.Injective v := by
    have hm : StrictMono (![0,p,q,r,n] : Fin 5 → ℕ) := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i; fin_cases i <;> simp_all
    intro i j ee; apply hm.injective
    have hcv (a : Fin 5) : v a = ((![0,p,q,r,n] a : ℕ) : ℂ) := by fin_cases a <;> simp [v,exponents]
    rw [hcv i,hcv j] at ee; exact_mod_cast ee
  apply reciprocal_profile_bound S v h₁ rfl u
  · intro z hz w hw eqp
    apply eq_of_four_powers hg (hne w hw)
    · exact congrFun eqp 1
    · exact congrFun eqp 2
    · exact congrFun eqp 3
    · simpa [u,powers] using congrFun eqp 4
  · intro z _; rfl
  · intro z hz i; fin_cases i <;> simp [u,powers,hne z hz]
  · intro z hz
    have hq := hp.trans hpq
    have hr := hq.trans hqr
    obtain ⟨ha,hb,hc,hd⟩ := hh z hz
    obtain ⟨a,b⟩ := moments_of_double hp hq hr (hr.trans hrn) z ha hb
    obtain ⟨c,d⟩ := moments_of_double hp hq hr (hr.trans hrn) z⁻¹ hc hd
    have inv (i : Fin 5) : (u z i)⁻¹ = u z⁻¹ i := by fin_cases i <;> simp [u,powers,inv_pow]
    exact ⟨a,b,by simpa only [inv] using c,by simpa only [inv] using d⟩

/-- In particular the degree of a separable rational factor is at most six if each
complex conjugate and its reciprocal are double roots. -/
theorem reciprocal_separable_degree (f : ℚ[X]) (hf : f.Separable) {p q r n : ℕ}
    (hp : 0 < p) (hpq : p < q) (hqr : q < r) (hrn : r < n)
    (hg : p.gcd (q.gcd (r.gcd n)) = 1)
    (hh : ∀ z : ℂ, (f.map (algebraMap ℚ ℂ)).IsRoot z → z ≠ 0 ∧
      (five p q r n).IsRoot z ∧ (five p q r n).derivative.IsRoot z ∧
      (five p q r n).IsRoot z⁻¹ ∧ (five p q r n).derivative.IsRoot z⁻¹) : f.natDegree ≤ 6 := by
  classical
  let s := (f.map (algebraMap ℚ ℂ)).roots.toFinset
  have hz (z : ℂ) (h : z ∈ s) := hh z (Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp h))
  have hc := reciprocal_double_roots_card s hp hpq hqr hrn hg (fun z h => (hz z h).1) (fun z h => (hz z h).2)
  simpa [s,Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hf.map), IsAlgClosed.card_roots_eq_natDegree] using hc

end OMA.S_mo_447544

namespace OMA.S_mo_447544
open Polynomial Interpolation

/-- Removing the common divisor of the exponents is legitimate for multiple roots:
composition with a power has nonzero derivative at every nonzero complex number. -/
theorem main_of_coprime (h : ∀ p q r n : ℕ, 0 < p → p < q → q < r → r < n →
    p.gcd (q.gcd (r.gcd n)) = 1 → ∀ z : ℂ, (five p q r n).IsRoot z →
    ¬ (five p q r n).derivative.IsRoot z) :
    ∀ p q r n : ℕ, 0 < p → p < q → q < r → r < n → ∀ z : ℂ,
      (five p q r n).IsRoot z → ¬ (five p q r n).derivative.IsRoot z := by
  intro p q r n hp hpq hqr hrn z hz hd
  let d := p.gcd (q.gcd (r.gcd n))
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ hp
  have hdiv := Nat.gcd_dvd_right p (q.gcd (r.gcd n))
  have hdiv' := hdiv.trans (Nat.gcd_dvd_right q (r.gcd n))
  obtain ⟨a,ha⟩ : d ∣ p := Nat.gcd_dvd_left ..
  obtain ⟨b,hb⟩ : d ∣ q := hdiv.trans (Nat.gcd_dvd_left ..)
  obtain ⟨c,hc⟩ : d ∣ r := hdiv'.trans (Nat.gcd_dvd_left ..)
  obtain ⟨k,hk⟩ : d ∣ n := hdiv'.trans (Nat.gcd_dvd_right ..)
  have hg : a.gcd (b.gcd (c.gcd k)) = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hdpos
    calc
      d * a.gcd (b.gcd (c.gcd k)) = (d*a).gcd ((d*b).gcd ((d*c).gcd (d*k))) := by simp only [Nat.gcd_mul_left]
      _ = d*1 := by rw [← ha,← hb,← hc,← hk,Nat.mul_one]
  have hapos : 0 < a := by
    have hda : 0 < d*a := by simpa only [← ha] using hp
    exact (Nat.mul_pos_iff_of_pos_left hdpos).mp hda
  have hab : a < b := by apply Nat.lt_of_mul_lt_mul_left (a := d); simpa only [← ha,← hb] using hpq
  have hbc : b < c := by apply Nat.lt_of_mul_lt_mul_left (a := d); simpa only [← hb,← hc] using hqr
  have hck : c < k := by apply Nat.lt_of_mul_lt_mul_left (a := d); simpa only [← hc,← hk] using hrn
  have zne : z ≠ 0 := by
    intro he
    have hq := hp.trans hpq
    have hr := hq.trans hqr
    simp [he,five,Polynomial.IsRoot,zero_pow hp.ne',zero_pow hq.ne',zero_pow hr.ne',zero_pow (hr.trans hrn).ne'] at hz
  have heq : five p q r n = (five a b c k).comp (X^d) := by
    rw [ha,hb,hc,hk]; simp [five,pow_mul]
  rw [Polynomial.IsRoot,heq,eval_comp,eval_pow,eval_X] at hz
  rw [Polynomial.IsRoot,heq,derivative_comp,eval_mul,eval_comp,eval_pow,eval_X] at hd
  have hnz : (Polynomial.derivative (X^d : ℂ[X])).eval z ≠ 0 := by
    intro he
    have hh := euler_xpow z hdpos
    rw [he,mul_zero] at hh
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hdpos.ne') (pow_ne_zero _ zne) hh.symm
  exact h a b c k hapos hab hbc hck hg (z^d) hz ((mul_eq_zero.mp hd).resolve_left hnz)

end OMA.S_mo_447544

namespace OMA.S_mo_447544
open Polynomial
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2500000 in
private lemma small_order {k : ℕ} (hk : 0 < k) (hd : k.totient ≤ 6) : k ≤ 18 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h1 : k = 1
    · omega
    let l := k.minFac
    have hl : l.Prime := Nat.minFac_prime h1
    have hld : l ∣ k := Nat.minFac_dvd _
    have hφ := Nat.le_of_dvd (Nat.totient_pos.mpr hk) (Nat.totient_dvd_of_dvd hld)
    rw [Nat.totient_prime hl] at hφ
    have hl7 : l ≤ 7 := by omega
    obtain ⟨m, hm⟩ := hld
    have hm0 : 0 < m := by
      by_contra! hz
      have hz0 : m=0 := by omega
      simp [hz0] at hm
      omega
    have hmk : m < k := by
      rw [hm]
      nlinarith [hl.two_le]
    have hmt : m.totient ≤ 6 := le_trans (Nat.le_of_dvd (Nat.totient_pos.mpr hk)
      (Nat.totient_dvd_of_dvd (show m ∣ k from ⟨l,by rw [hm, Nat.mul_comm]⟩))) hd
    have hm18 := ih m hmk hm0 hmt
    have h126 : k ≤ 126 := by rw [hm]; exact Nat.mul_le_mul hl7 hm18
    have hc : ∀ j : Fin 127, j.val.totient ≤ 6 → j.val ≤ 18 := by decide
    exact hc ⟨k,by omega⟩ hd

private theorem neg_prime (l : ℕ) (hl : l.Prime) (hodd : ¬ 2 ∣ l)
    (hval : (cyclotomic l ℤ).eval (-1) = 1) : (cyclotomic (l*2) ℤ).eval (-1)=l := by
  have : Fact l.Prime := ⟨hl⟩
  have h := congrArg (Polynomial.eval (-1 : ℤ))
    (cyclotomic_expand_eq_cyclotomic_mul Nat.prime_two hodd (n := l) ℤ)
  simpa [expand_eval,eval_mul,hval] using h.symm

private theorem minus_values (k : ℕ) (h : k = 6 ∨ k = 10 ∨ k = 14 ∨ k = 18) :
    (cyclotomic k ℤ).eval (-1) = 3 ∨ (cyclotomic k ℤ).eval (-1) = 5 ∨
      (cyclotomic k ℤ).eval (-1) = 7 := by
  rcases h with rfl|rfl|rfl|rfl
  · left; simp
  · right; left
    exact neg_prime 5 (by decide) (by decide) (by
      have : Fact (Nat.Prime 5) := ⟨by decide⟩
      norm_num [cyclotomic_prime,Finset.sum_range_succ])
  · right; right
    exact neg_prime 7 (by decide) (by decide) (by
      have : Fact (Nat.Prime 7) := ⟨by decide⟩
      norm_num [cyclotomic_prime,Finset.sum_range_succ])
  · left
    rw [show 18 = 6*3 by rfl,← cyclotomic_expand_eq_cyclotomic Nat.prime_three (by decide),expand_eval]
    norm_num

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2500000 in
private lemma fourth_exclusion (p q r n : ℕ) :
    ¬(cyclotomic 12 ℤ)^2 ∣ (1+X^p+X^q+X^r-X^n : ℤ[X]) := by
  let u : GaussianInt := ⟨0, 1⟩
  have hu : u^4=1 := by decide
  have hu_repr (a : ℕ) : -1 ≤ (u^a).re ∧ (u^a).re ≤ 1 ∧
      -1 ≤ (u^a).im ∧ (u^a).im ≤ 1 ∧ ((u^a).re + (u^a).im)%2=1 := by
    have hred : u^a = u^(a%4) := by
      conv_lhs => rw [← Nat.mod_add_div a 4, pow_add, pow_mul,hu,one_pow,mul_one]
    rw [hred]
    have hfour : ∀ j : Fin 4, -1 ≤ (u^j.val).re ∧ (u^j.val).re ≤ 1 ∧
      -1 ≤ (u^j.val).im ∧ (u^j.val).im ≤ 1 ∧ ((u^j.val).re + (u^j.val).im)%2=1 := by decide
    exact hfour ⟨_,Nat.mod_lt _ (by decide)⟩
  have hv : Polynomial.aeval u (cyclotomic 12 ℤ) = 3 := by
    rw [show 12=6*2 by rfl,← cyclotomic_expand_eq_cyclotomic Nat.prime_two (by decide),
      expand_aeval,cyclotomic_six]
    simp only [map_add,map_sub,map_pow,aeval_X,map_one]
    decide
  rintro ⟨s, hs⟩
  let w := Polynomial.aeval u s
  have he := congrArg (Polynomial.aeval u) hs
  simp only [map_add,map_sub,map_pow,aeval_X,map_one,map_mul,hv] at he
  change 1 + u^p + u^q + u^r - u^n = 3^2*w at he
  have hR := congrArg Zsqrtd.re he
  have hI := congrArg Zsqrtd.im he
  have h9 : (3^2 : GaussianInt) = ⟨9,0⟩ := by decide
  simp only [Zsqrtd.re_sub,Zsqrtd.im_sub,Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_one,
    Zsqrtd.im_one,h9,Zsqrtd.re_mul,Zsqrtd.im_mul,mul_zero,zero_mul,zero_add,add_zero] at hR hI
  obtain ⟨_,_,_,_,_⟩ := hu_repr p
  obtain ⟨_,_,_,_,_⟩ := hu_repr q
  obtain ⟨_,_,_,_,_⟩ := hu_repr r
  obtain ⟨_,_,_,_,_⟩ := hu_repr n
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2500000 in
/-- No cyclotomic polynomial of degree at most six occurs twice in the five-term polynomial. -/
theorem cyclotomic_sq_not_dvd {k : ℕ} (hk : 0 < k) (hd : k.totient ≤ 6)
    (p q r n : ℕ) : ¬ (cyclotomic k ℤ)^2 ∣ (1+X^p+X^q+X^r-X^n : ℤ[X]) := by
  intro h
  have h18 := small_order hk hd
  by_cases h12 : k=12
  · exact fourth_exclusion p q r n (h12 ▸ h)
  by_cases hminus : k=6 ∨ k=10 ∨ k=14 ∨ k=18
  · have H := map_dvd (evalRingHom (-1 : ℤ)) h
    change eval (-1) _ ∣ eval (-1) _ at H
    simp only [eval_sub,eval_add,eval_pow,eval_one,eval_X] at H
    have hpar (m : ℕ) : (-1:ℤ)^m=1 ∨ (-1:ℤ)^m= -1 := neg_one_pow_eq_or ℤ _
    rcases minus_values k hminus with he|he|he <;> rw [he] at H <;> norm_num at H <;>
      rcases hpar p with hp|hp <;> rcases hpar q with hq|hq <;> rcases hpar r with hr|hr <;>
      rcases hpar n with hn|hn <;> rw [hp,hq,hr,hn] at H <;> norm_num at H
  · have H := map_dvd (evalRingHom (1 : ℤ)) h
    change eval 1 _ ∣ eval 1 _ at H
    simp only [eval_sub,eval_add,eval_pow,eval_one,eval_X,one_pow] at H
    have he : ((cyclotomic k ℤ).eval 1)^2 ∣ (3:ℤ) := by
      norm_num only [Int.reduceSub,Int.reduceAdd] at H
      exact H
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have : Fact (Nat.Prime 7) := ⟨by decide⟩
    have Hlist : ∀ j : Fin 19, j.val.totient ≤ 6 → 0 < j.val → j.val ≠ 12 →
        ¬(j.val=6 ∨ j.val=10 ∨ j.val=14 ∨ j.val=18) →
        j.val=1 ∨ j.val=2 ∨ j.val=3 ∨ j.val=4 ∨ j.val=5 ∨ j.val=7 ∨ j.val=8 ∨ j.val=9 := by decide
    have hl := Hlist ⟨k,by omega⟩ hd hk h12 hminus
    change k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=7 ∨ k=8 ∨ k=9 at hl
    rcases hl with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · norm_num at he
    · rw [eval_one_cyclotomic_prime] at he; norm_num at he
    · rw [eval_one_cyclotomic_prime] at he; norm_num at he
    · rw [show 4=2^(1+1) by rfl,eval_one_cyclotomic_prime_pow] at he; norm_num at he
    · rw [eval_one_cyclotomic_prime] at he; norm_num at he
    · rw [eval_one_cyclotomic_prime] at he; norm_num at he
    · rw [show 8=2^(2+1) by rfl,eval_one_cyclotomic_prime_pow] at he; norm_num at he
    · rw [show 9=3^(1+1) by rfl,eval_one_cyclotomic_prime_pow] at he; norm_num at he

end OMA.S_mo_447544

namespace FiveSparse
open Polynomial OMA.S_mo_447544
open scoped Polynomial

private lemma eval_five {p q r n : ℕ} (x : ℂ) :
    (Interpolation.five p q r n).eval x=aeval x (F p q r n) ∧
    (Interpolation.five p q r n).derivative.eval x=aeval x (F p q r n).derivative := by
  have hmap : (F p q r n).map (algebraMap ℤ ℂ)=Interpolation.five p q r n := by
    simp [F,Interpolation.five]
  rw [← hmap,derivative_map,eval_map_algebraMap,eval_map_algebraMap]
  exact ⟨rfl,rfl⟩

private theorem simple_of_classification
    (classify : ∀ g : ℤ[X], g.Monic → g.reverse=g → 0<g.natDegree → g.natDegree≤6 →
      ((g.map (Int.castRingHom ℂ)).mahlerMeasure)^4≤5 →
      (∃ x : ℝ, aeval x g=0) ∨ ∃ k : ℕ, 0<k ∧ cyclotomic k ℤ ∣ g) :
    ∀ p q r n : ℕ, 0<p → p<q → q<r → r<n → ∀ z : ℂ,
      (Interpolation.five p q r n).IsRoot z → ¬ (Interpolation.five p q r n).derivative.IsRoot z := by
  apply main_of_coprime
  intro p q r n hp hq hr hn gcd1 z hz hdz
  obtain ⟨e,d⟩ := eval_five (p:=p) (q:=q) (r:=r) (n:=n) z
  obtain ⟨intg,hdiv⟩ := integral_double_factor hp hq hr hn (e.symm.trans hz) (d.symm.trans hdz)
  let g := minpoly ℤ z
  have mon : g.Monic := minpoly.monic intg
  have rev := reverse_eq_self hp hq hr hn mon hdiv
  have deg : g.natDegree ≤ 6 := by
    apply degree_bound hp hq hr hn intg hdiv rev
    intro S nz hh
    apply reciprocal_double_roots_card S hp hq hr hn gcd1 nz
    intro x hx
    obtain ⟨u,v,w,y⟩ := hh x hx
    obtain ⟨ex,dx⟩ := eval_five (p:=p) (q:=q) (r:=r) (n:=n) x
    obtain ⟨ei,di⟩ := eval_five (p:=p) (q:=q) (r:=r) (n:=n) x⁻¹
    exact ⟨ex.trans u,dx.trans v,ei.trans w,di.trans y⟩
  rcases classify g mon rev (minpoly.natDegree_pos intg) deg (mahler_bound hp hq hr hn hdiv)
      with ⟨x,hx⟩ | ⟨k,hk,hkg⟩
  · have dbl := root_and_derivative_of_sq_dvd hdiv hx
    have nx : x≠0 := by
      rintro rfl
      exact one_ne_zero ((const_eval hp hq hr hn).symm.trans dbl.1)
    exact real_exclusion hp hq hr hn nx dbl
      (root_and_derivative_of_sq_dvd hdiv (root_of_inverse nx rev hx))
  · have bound : k.totient ≤ 6 := by
      rw [← natDegree_cyclotomic k ℤ]
      exact (natDegree_le_of_dvd hkg mon.ne_zero).trans deg
    exact cyclotomic_sq_not_dvd hk bound p q r n ((pow_dvd_pow_of_dvd hkg 2).trans hdiv)

end FiveSparse

namespace OMA.S_mo_447544.Classification
/-! Bounded exact integer calculations after root squaring. -/
abbrev Triple := ℤ × ℤ × ℤ
abbrev Pair := ℤ × ℤ

def grSix : Triple → Triple
  | (a,b,c) => (2*b-a*a, b*b+2*b-2*a*c, 2+2*b*b-2*a*a-c*c)
def grFour : Pair → Pair
  | (a,b) => (2*b-a*a,b*b+2-2*a*a)

def within (den num : ℤ) (w : Triple) : Bool :=
  den*w.1.natAbs ≤ num*6 && den*w.2.1.natAbs ≤ num*15 && den*w.2.2.natAbs ≤ num*20
def withinFour (den num : ℤ) (w : Pair) : Bool :=
  den*w.1.natAbs ≤ num*4 && den*w.2.natAbs ≤ num*6

def allowed6 (w : Triple) : Bool :=
  let (a,b,c) := w
  0 < 2+2*b+(2*a+c) && 0 < 2+2*b-(2*a+c) &&
  within 2 3 w && within 4 9 (grSix w) && within 1 5 (grSix (grSix w)) &&
  within 1 25 (grSix (grSix (grSix w))) &&
  within 1 625 (grSix (grSix (grSix (grSix w))))
def allowed4 (w : Pair) : Bool :=
  let (a,b) := w
  0 < 2+2*a+b && 0 < 2-2*a+b &&
  withinFour 2 3 w && withinFour 4 9 (grFour w) && withinFour 1 5 (grFour (grFour w))

def cases4 : List Pair :=
  [(-2, 3),
   (-1, 1),
   (-1, 2),
   (0, -1),
   (0, 0),
   (0, 1),
   (0, 2),
   (1, 1),
   (1, 2),
   (2, 3)]

def cases6 : List Triple :=
  [(-3, 6, -7),
   (-2, 3, -3),
   (-2, 4, -4),
   (-1, 0, 1),
   (-1, 1, -1),
   (-1, 1, 0),
   (-1, 2, -2),
   (-1, 2, -1),
   (-1, 3, -2),
   (0, 0, -1),
   (0, 0, 0),
   (0, 0, 1),
   (0, 1, -1),
   (0, 1, 0),
   (0, 1, 1),
   (0, 2, 0),
   (0, 3, 0),
   (1, 0, -1),
   (1, 1, 0),
   (1, 1, 1),
   (1, 2, 1),
   (1, 2, 2),
   (1, 3, 2),
   (2, 3, 3),
   (2, 4, 4),
   (3, 6, 7)]


end OMA.S_mo_447544.Classification

namespace OMA.S_mo_447544.Classification
open Polynomial

noncomputable def polyTwo (a : ℤ) : ℤ[X] := X^2+C a*X+1
noncomputable def polyFour (a b : ℤ) : ℤ[X] := X^4+C a*X^3+C b*X^2+C a*X+1
noncomputable def polySix (a b c : ℤ) : ℤ[X] := X^6+C a*X^5+C b*X^4+C c*X^3+C b*X^2+C a*X+1

end OMA.S_mo_447544.Classification

namespace OMA.S_mo_447544.Classification
noncomputable section
open Polynomial

private def fromRoots (s : Multiset ℂ) : ℂ[X] := (s.map fun z => X-C z).prod

private def squareRoots (s : Multiset ℂ) : ℂ[X] := (s.map fun z => X-C (z^2)).prod

private theorem square_comp (s : Multiset ℂ) : (squareRoots s).comp (X^2) =
    (-1:ℂ[X])^s.card * fromRoots s * (fromRoots s).comp (-X) := by
  induction s using Multiset.induction with
  | empty => simp [squareRoots,fromRoots]
  | cons z s ih =>
    have f : fromRoots (z::ₘs) = (X-C z)*fromRoots s := by simp [fromRoots]
    have g : squareRoots (z::ₘs) = (X-C (z^2))*squareRoots s := by simp [squareRoots]
    rw [f,g,mul_comp,mul_comp,sub_comp,sub_comp,X_comp,X_comp,C_comp,C_comp,ih,
      Multiset.card_cons,pow_succ, map_pow]
    ring

private theorem square_measure (s : Multiset ℂ) :
    (squareRoots s).mahlerMeasure = (fromRoots s).mahlerMeasure^2 := by
  induction s using Multiset.induction with
  | empty => simp [squareRoots,fromRoots]
  | cons z s ih =>
    have f : fromRoots (z::ₘs) = (X-C z)*fromRoots s := by simp [fromRoots]
    have g : squareRoots (z::ₘs) = (X-C (z^2))*squareRoots s := by simp [squareRoots]
    rw [f,g,mahlerMeasure_mul,mahlerMeasure_mul,mahlerMeasure_X_sub_C,mahlerMeasure_X_sub_C,
      norm_pow,ih,mul_pow]
    by_cases hz : ‖z‖≤1
    · rw [max_eq_left hz,max_eq_left (by nlinarith [norm_nonneg z])]
      simp
    · rw [max_eq_right (le_of_not_ge hz),max_eq_right (by nlinarith [norm_nonneg z])]

theorem mahler_of_root_square {p q : ℂ[X]} (hp : p.Monic) (he : Even p.natDegree)
    (hq : q.comp (X^2) = p*p.comp (-X)) : q.mahlerMeasure=p.mahlerMeasure^2 := by
  have hc : p.roots.card = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hroot : fromRoots p.roots = p := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hc
  have sq := square_comp p.roots
  rw [hc,he.neg_one_pow,one_mul,hroot,← hq] at sq
  have eq : squareRoots p.roots = q :=
    Polynomial.expand_injective (R:=ℂ) (by decide : 0<2) sq
  rw [← eq,square_measure,hroot]

end
end OMA.S_mo_447544.Classification

namespace OMA.S_mo_447544.Classification

private def check6 (i : Fin 19) : Bool :=
  (List.range 45).all fun j => (List.range 61).all fun k =>
    let w : Triple := ((i.val:ℤ)-9, (j:ℤ)-22, (k:ℤ)-30)
    !allowed6 w || cases6.contains w

private def check4 (i : Fin 13) : Bool :=
  (List.range 19).all fun j =>
    let w : Pair := ((i.val:ℤ)-6,(j:ℤ)-9)
    !allowed4 w || cases4.contains w

set_option maxRecDepth 50000 in
set_option maxHeartbeats 3000000 in
private theorem check6_ok (i : Fin 19) : check6 i := by
  fin_cases i <;> decide +kernel

private theorem check4_ok (i : Fin 13) : check4 i := by
  fin_cases i <;> decide +kernel

theorem finite_six (a b c : ℤ) (ha : -9≤a ∧ a≤9) (hb : -22≤b ∧ b≤22)
    (hc : -30≤c ∧ c≤30) (hw : allowed6 (a,b,c)) : (a,b,c) ∈ cases6 := by
  let i : Fin 19 := ⟨(a+9).toNat, by omega⟩
  have h := check6_ok i
  unfold check6 at h
  have hj := List.all_eq_true.mp h (b+22).toNat (List.mem_range.mpr (by omega))
  have hk := List.all_eq_true.mp hj (c+30).toNat (List.mem_range.mpr (by omega))
  dsimp only at hk
  have hi : (i.val:ℤ)-9=a := by dsimp [i]; omega
  rw [hi,show (((b+22).toNat:ℕ):ℤ)-22=b by omega,
    show (((c+30).toNat:ℕ):ℤ)-30=c by omega, hw] at hk
  simpa using hk

theorem finite_four (a b : ℤ) (ha : -6≤a ∧ a≤6) (hb : -9≤b ∧ b≤9)
    (hw : allowed4 (a,b)) : (a,b) ∈ cases4 := by
  let i : Fin 13 := ⟨(a+6).toNat, by omega⟩
  have h := check4_ok i
  unfold check4 at h
  have hj := List.all_eq_true.mp h (b+9).toNat (List.mem_range.mpr (by omega))
  dsimp only at hj
  have hi : (i.val:ℤ)-6=a := by dsimp [i]; omega
  rw [hi,show (((b+9).toNat:ℕ):ℤ)-9=b by omega,hw] at hj
  simpa using hj

end OMA.S_mo_447544.Classification

namespace OMA.S_mo_447544.Classification
open Polynomial
noncomputable section

private lemma formula3 : cyclotomic 3 ℤ = 1 + X + X^2 := by
  simp; ring

private lemma formula4 : cyclotomic 4 ℤ = 1 + X^2 := by
  rw [show 4=2^(1+1) by rfl,cyclotomic_prime_pow_eq_geom_sum (by decide : Nat.Prime 2)]
  simp [Finset.sum_range_succ]

private lemma formula5 : cyclotomic 5 ℤ = 1 + X + X^2 + X^3 + X^4 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  simp [cyclotomic_prime, Finset.sum_range_succ]

private lemma formula6 : cyclotomic 6 ℤ = 1 - X + X^2 := by
  simp; ring

private lemma formula7 : cyclotomic 7 ℤ = 1 + X + X^2 + X^3 + X^4 + X^5 + X^6 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  simp [cyclotomic_prime, Finset.sum_range_succ]

private lemma formula8 : cyclotomic 8 ℤ = 1 + X^4 := by
  rw [show 8=2^(2+1) by rfl,cyclotomic_prime_pow_eq_geom_sum (by decide : Nat.Prime 2)]
  simp [Finset.sum_range_succ]

private lemma formula9 : cyclotomic 9 ℤ = 1 + X^3 + X^6 := by
  rw [show 9=3^(1+1) by rfl,cyclotomic_prime_pow_eq_geom_sum (by decide : Nat.Prime 3)]
  simp [Finset.sum_range_succ]; ring

private lemma formula10 : cyclotomic 10 ℤ = 1 - X + X^2 - X^3 + X^4 := by
  apply mul_right_cancel₀ (cyclotomic_ne_zero 2 ℤ)
  rw [show 10=2*5 by rfl,← cyclotomic_expand_eq_cyclotomic_mul (by decide : Nat.Prime 5) (by decide)]
  simp; ring

private lemma formula12 : cyclotomic 12 ℤ = 1 - X^2 + X^4 := by
  rw [show 12=6*2 by rfl,← cyclotomic_expand_eq_cyclotomic (by decide : Nat.Prime 2) (by decide),cyclotomic_six]
  simp; ring

private lemma formula14 : cyclotomic 14 ℤ = 1 - X + X^2 - X^3 + X^4 - X^5 + X^6 := by
  apply mul_right_cancel₀ (cyclotomic_ne_zero 2 ℤ)
  rw [show 14=2*7 by rfl,← cyclotomic_expand_eq_cyclotomic_mul (by decide : Nat.Prime 7) (by decide)]
  simp; ring

private lemma formula18 : cyclotomic 18 ℤ = 1 - X^3 + X^6 := by
  rw [show 18=6*3 by rfl,← cyclotomic_expand_eq_cyclotomic (by decide : Nat.Prime 3) (by decide),cyclotomic_six]
  simp; ring

theorem survivors_two (a : ℤ) (h : (a = -1 ∨ a = 0 ∨ a = 1)) :
    ∃ k ∈ ([3,4,5,6,7,8,9,10,12,14,18] : List ℕ), cyclotomic k ℤ ∣ polyTwo a := by
  rcases h with rfl|rfl|rfl
  · refine ⟨6,by decide, 1, ?_⟩
    rw [formula6]
    norm_num [polyTwo]; ring
  · refine ⟨4,by decide, 1, ?_⟩
    rw [formula4]
    norm_num [polyTwo]; ring
  · refine ⟨3,by decide, 1, ?_⟩
    rw [formula3]
    norm_num [polyTwo]; ring

theorem survivors_four (a b : ℤ) (h : (a,b) ∈ cases4) :
    ∃ k ∈ ([3,4,5,6,7,8,9,10,12,14,18] : List ℕ), cyclotomic k ℤ ∣ polyFour a b := by
  simp only [cases4,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · refine ⟨6,by decide, 1 - X + X^2, ?_⟩
    rw [formula6]
    norm_num [polyFour]; ring
  · refine ⟨10,by decide, 1, ?_⟩
    rw [formula10]
    norm_num [polyFour]; ring
  · refine ⟨4,by decide, 1 - X + X^2, ?_⟩
    rw [formula4]
    norm_num [polyFour]; ring
  · refine ⟨12,by decide, 1, ?_⟩
    rw [formula12]
    norm_num [polyFour]; ring
  · refine ⟨8,by decide, 1, ?_⟩
    rw [formula8]
    norm_num [polyFour]; ring
  · refine ⟨3,by decide, 1 - X + X^2, ?_⟩
    rw [formula3]
    norm_num [polyFour]; ring
  · refine ⟨4,by decide, 1 + X^2, ?_⟩
    rw [formula4]
    norm_num [polyFour]; ring
  · refine ⟨5,by decide, 1, ?_⟩
    rw [formula5]
    norm_num [polyFour]; ring
  · refine ⟨3,by decide, 1 + X^2, ?_⟩
    rw [formula3]
    norm_num [polyFour]; ring
  · refine ⟨3,by decide, 1 + X + X^2, ?_⟩
    rw [formula3]
    norm_num [polyFour]; ring

theorem survivors_six (a b c : ℤ) (h : (a,b,c) ∈ cases6) :
    ∃ k ∈ ([3,4,5,6,7,8,9,10,12,14,18] : List ℕ), cyclotomic k ℤ ∣ polySix a b c := by
  simp only [cases6,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · refine ⟨6,by decide, 1 - 2*X + 3*X^2 - 2*X^3 + X^4, ?_⟩
    rw [formula6]
    norm_num [polySix]; ring
  · refine ⟨6,by decide, 1 - X + X^2 - X^3 + X^4, ?_⟩
    rw [formula6]
    norm_num [polySix]; ring
  · refine ⟨4,by decide, 1 - 2*X + 3*X^2 - 2*X^3 + X^4, ?_⟩
    rw [formula4]
    norm_num [polySix]; ring
  · refine ⟨6,by decide, 1 - X^2 + X^4, ?_⟩
    rw [formula6]
    norm_num [polySix]; ring
  · refine ⟨14,by decide, 1, ?_⟩
    rw [formula14]
    norm_num [polySix]; ring
  · refine ⟨6,by decide, 1 + X^4, ?_⟩
    rw [formula6]
    norm_num [polySix]; ring
  · refine ⟨4,by decide, 1 - X + X^2 - X^3 + X^4, ?_⟩
    rw [formula4]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 - 2*X + 3*X^2 - 2*X^3 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring
  · refine ⟨4,by decide, 1 - X + 2*X^2 - X^3 + X^4, ?_⟩
    rw [formula4]
    norm_num [polySix]; ring
  · refine ⟨18,by decide, 1, ?_⟩
    rw [formula18]
    norm_num [polySix]; ring
  · refine ⟨4,by decide, 1 - X^2 + X^4, ?_⟩
    rw [formula4]
    norm_num [polySix]; ring
  · refine ⟨9,by decide, 1, ?_⟩
    rw [formula9]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 - X + X^2 - X^3 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring
  · refine ⟨4,by decide, 1 + X^4, ?_⟩
    rw [formula4]
    norm_num [polySix]; ring
  · refine ⟨6,by decide, 1 + X + X^2 + X^3 + X^4, ?_⟩
    rw [formula6]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 - X + 2*X^2 - X^3 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring
  · refine ⟨4,by decide, 1 + 2*X^2 + X^4, ?_⟩
    rw [formula4]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 - X^2 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring
  · refine ⟨7,by decide, 1, ?_⟩
    rw [formula7]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 + X^2 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring
  · refine ⟨4,by decide, 1 + X + X^2 + X^3 + X^4, ?_⟩
    rw [formula4]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 + 2*X^2 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 + X + X^2 + X^3 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 + X + 2*X^2 + X^3 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring
  · refine ⟨3,by decide, 1 + 2*X + 3*X^2 + 2*X^3 + X^4, ?_⟩
    rw [formula3]
    norm_num [polySix]; ring

end
end OMA.S_mo_447544.Classification

namespace OMA.S_mo_447544.Classification
noncomputable section
open Polynomial

def M (p : ℤ[X]) : ℝ := (p.map (Int.castRingHom ℂ)).mahlerMeasure
abbrev p6 (w : Triple) := polySix w.1 w.2.1 w.2.2
abbrev p4 (w : Pair) := polyFour w.1 w.2

theorem degree_two (a : ℤ) : (polyTwo a).IsMonicOfDegree 2 := by
  apply (isMonicOfDegree_iff _ _).2
  constructor
  · unfold polyTwo
    compute_degree
  · simp only [polyTwo, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]; norm_num

theorem degree_four (w : Pair) : (p4 w).IsMonicOfDegree 4 := by
  apply (isMonicOfDegree_iff _ _).2
  constructor
  · unfold p4 polyFour
    compute_degree
  · simp only [p4, polyFour, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]; norm_num

theorem degree_six (w : Triple) : (p6 w).IsMonicOfDegree 6 := by
  apply (isMonicOfDegree_iff _ _).2
  constructor
  · unfold p6 polySix
    compute_degree
  · simp only [p6, polySix, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]; norm_num

private theorem M_four (w : Pair) : M (p4 (grFour w)) = M (p4 w)^2 := by
  obtain ⟨a,b⟩ := w
  apply mahler_of_root_square ((degree_four _).monic.map _)
  · rw [((degree_four _).monic.natDegree_map _),(degree_four _).natDegree_eq]
    decide
  · simp [grFour,p4,polyFour,add_comp,mul_comp,pow_comp,sub_comp]
    ring

private theorem M_six (w : Triple) : M (p6 (grSix w)) = M (p6 w)^2 := by
  obtain ⟨a,b,c⟩ := w
  apply mahler_of_root_square ((degree_six _).monic.map _)
  · rw [((degree_six _).monic.natDegree_map _),(degree_six _).natDegree_eq]
    decide
  · simp [grSix,p6,polySix,add_comp,mul_comp,pow_comp,sub_comp]
    ring

private theorem coeff_bound (p : ℤ[X]) {d : ℕ} (hdeg : p.IsMonicOfDegree d)
    (j : ℕ) {a : ℤ} (hc : p.coeff j=a) (den num : ℤ) (hd : 0≤den)
    (hM : (den : ℝ)*M p ≤ num) :
    den * (a.natAbs : ℤ) ≤ num * d.choose j := by
  have hm := norm_coeff_le_choose_mul_mahlerMeasure j (p.map (Int.castRingHom ℂ))
  rw [hdeg.monic.natDegree_map,hdeg.natDegree_eq, coeff_map,hc] at hm
  have habs : ‖(Int.castRingHom ℂ) a‖ = (a.natAbs : ℝ) := by
    simp
  rw [habs] at hm
  change (a.natAbs:ℝ) ≤ (d.choose j : ℝ)*M p at hm
  have hc' : (den:ℝ)*(a.natAbs:ℝ)≤(num:ℝ)*(d.choose j:ℝ) := by
    calc
      _ ≤ (den:ℝ)*((d.choose j:ℝ)*M p) := mul_le_mul_of_nonneg_left hm (by exact_mod_cast hd)
      _ = ((den:ℝ)*M p)*(d.choose j:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hM (by positivity)
  apply (Int.cast_le (R:=ℝ)).mp
  rw [Int.cast_mul,Int.cast_mul,Int.cast_natCast,Int.cast_natCast]
  exact hc'

theorem within4_of (w : Pair) (den num : ℤ) (hd : 0≤den)
    (hM : (den:ℝ)*M (p4 w)≤num) : withinFour den num w := by
  obtain ⟨a,b⟩ := w
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    exact (coeff_bound (p4 (a,b)) (degree_four _) 1 (a:=a) (by simp only [p4, polyFour, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]; norm_num) den num hd hM)
  · apply decide_eq_true
    exact (coeff_bound (p4 (a,b)) (degree_four _) 2 (a:=b) (by simp only [p4, polyFour, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]; norm_num) den num hd hM)

theorem within6_of (w : Triple) (den num : ℤ) (hd : 0≤den)
    (hM : (den:ℝ)*M (p6 w)≤num) : within den num w := by
  obtain ⟨a,b,c⟩ := w
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply Bool.and_eq_true_iff.mpr
    constructor
    · apply decide_eq_true
      exact (coeff_bound (p6 (a,b,c)) (degree_six _) 1 (a:=a) (by simp only [p6, polySix, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]; norm_num) den num hd hM)
    · apply decide_eq_true
      exact (coeff_bound (p6 (a,b,c)) (degree_six _) 2 (a:=b) (by simp only [p6, polySix, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]; norm_num) den num hd hM)
  · apply decide_eq_true
    exact (coeff_bound (p6 (a,b,c)) (degree_six _) 3 (a:=c) (by simp only [p6, polySix, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]; norm_num) den num hd hM)

private theorem margins (x : ℝ) (hx : 0≤x) (h : x^4≤5) :
    2*x≤3 ∧ 4*x^2≤9 ∧ x^4≤5 ∧ x^8≤25 ∧ x^16≤625 := by
  have ha : x≤3/2 := by
    by_contra! h'
    have hh := pow_lt_pow_left₀ h' (by norm_num : (0:ℝ)≤3/2) (by decide : 4≠0)
    norm_num at hh
    linarith
  have hb : x^2 ≤ (3/2:ℝ)^2 := by gcongr
  have h8 : (x^4)^2≤(5:ℝ)^2 := by gcongr
  have h16 : ((x^4)^2)^2≤(25:ℝ)^2 := by gcongr; norm_num at h8; exact h8
  exact ⟨by linarith,by linarith,h,by nlinarith,by nlinarith⟩

theorem allowed_four (a b : ℤ) (hpos : 0<2+2*a+b ∧ 0<2-2*a+b)
    (hM : M (polyFour a b)^4≤5) :
    allowed4 (a,b) ∧ (-6≤a ∧ a≤6) ∧ (-9≤b ∧ b≤9) := by
  let w : Pair := (a,b)
  obtain ⟨h₀,h₁,h₂,_,_⟩ := margins (M (p4 w)) (mahlerMeasure_nonneg _) hM
  have f₀ := within4_of w 2 3 (by decide) h₀
  have f₁ := within4_of (grFour w) 4 9 (by decide) (by rw [M_four]; exact h₁)
  have f₂ := within4_of (grFour (grFour w)) 1 5 (by decide) (by
    simp only [M_four,Int.cast_one,one_mul,←pow_mul]; exact h₂)
  have bounds : 2*(a.natAbs:ℤ)≤3*4 ∧ 2*(b.natAbs:ℤ)≤3*6 := by
    simpa [withinFour,w] using f₀
  exact ⟨by simp only [allowed4, Bool.and_eq_true,decide_eq_true_eq]; exact ⟨⟨⟨⟨hpos.1,hpos.2⟩,f₀⟩,f₁⟩,f₂⟩,
    by omega, by omega⟩

theorem allowed_six (a b c : ℤ) (hpos : 0<2+2*b+(2*a+c) ∧ 0<2+2*b-(2*a+c))
    (hM : M (polySix a b c)^4≤5) :
    allowed6 (a,b,c) ∧ (-9≤a ∧ a≤9) ∧ (-22≤b ∧ b≤22) ∧ (-30≤c ∧ c≤30) := by
  let w : Triple := (a,b,c)
  obtain ⟨h₀,h₁,h₂,h₃,h₄⟩ := margins (M (p6 w)) (mahlerMeasure_nonneg _) hM
  have f₀ := within6_of w 2 3 (by decide) h₀
  have f₁ := within6_of (grSix w) 4 9 (by decide) (by rw [M_six]; exact h₁)
  have f₂ := within6_of (grSix (grSix w)) 1 5 (by decide) (by
    simp only [M_six,Int.cast_one,one_mul,←pow_mul];exact h₂)
  have f₃ := within6_of (grSix (grSix (grSix w))) 1 25 (by decide) (by
    simp only [M_six,Int.cast_one,one_mul,←pow_mul];exact h₃)
  have f₄ := within6_of (grSix (grSix (grSix (grSix w)))) 1 625 (by decide) (by
    simp only [M_six,Int.cast_one,one_mul,←pow_mul];exact h₄)
  have bounds : (2*(a.natAbs:ℤ)≤3*6 ∧ 2*(b.natAbs:ℤ)≤3*15) ∧ 2*(c.natAbs:ℤ)≤3*20 := by
    simpa [within,w] using f₀
  exact ⟨by simp only [allowed6, Bool.and_eq_true,decide_eq_true_eq]; exact ⟨⟨⟨⟨⟨⟨hpos.1,hpos.2⟩,f₀⟩,f₁⟩,f₂⟩,f₃⟩,f₄⟩,
    by omega, by omega, by omega⟩

end
end OMA.S_mo_447544.Classification

namespace OMA.S_mo_447544.Classification
open Polynomial Set
noncomputable section

private theorem eval_pos (p : ℤ[X]) (h0 : aeval (0:ℝ) p=1)
    (h : ¬ ∃ x : ℝ, aeval x p=0) (x : ℝ) : 0 < aeval x p := by
  by_contra! h'
  have hmem : (0:ℝ) ∈ uIcc (aeval x p) (aeval (0:ℝ) p) :=
    Set.mem_uIcc_of_le h' (by rw [h0]; norm_num)
  obtain ⟨t,_,ht⟩ := intermediate_value_uIcc
    (a:=x) (b:=0) (f:=fun s : ℝ => aeval s p) p.continuous_aeval.continuousOn hmem
  exact h ⟨t,ht⟩

theorem endpoints_two (a : ℤ) (h : ¬ ∃ x : ℝ, aeval x (polyTwo a)=0) :
    a = -1 ∨ a=0 ∨ a=1 := by
  have hp := eval_pos (polyTwo a) (by simp [polyTwo]) h (1:ℝ)
  have hm := eval_pos (polyTwo a) (by simp [polyTwo]) h (-1:ℝ)
  norm_num [polyTwo] at hp hm
  have ha : (-2:ℤ)<a := by exact_mod_cast (show (-2:ℝ)<a by linarith)
  have hb : a<(2:ℤ) := by exact_mod_cast (show (a:ℝ)<2 by linarith)
  omega

theorem endpoints_four (a b : ℤ) (h : ¬ ∃ x : ℝ, aeval x (polyFour a b)=0) :
    0<2+2*a+b ∧ 0<2-2*a+b := by
  have hp := eval_pos (polyFour a b) (by simp [polyFour]) h (1:ℝ)
  have hm := eval_pos (polyFour a b) (by simp [polyFour]) h (-1:ℝ)
  norm_num [polyFour] at hp hm
  constructor
  · exact_mod_cast (show (0:ℝ)<2+2*(a:ℝ)+(b:ℝ) by linarith)
  · exact_mod_cast (show (0:ℝ)<2-2*(a:ℝ)+(b:ℝ) by linarith)

theorem endpoints_six (a b c : ℤ) (h : ¬ ∃ x : ℝ, aeval x (polySix a b c)=0) :
    0<2+2*b+(2*a+c) ∧ 0<2+2*b-(2*a+c) := by
  have hp := eval_pos (polySix a b c) (by simp [polySix]) h (1:ℝ)
  have hm := eval_pos (polySix a b c) (by simp [polySix]) h (-1:ℝ)
  norm_num [polySix] at hp hm
  constructor
  · exact_mod_cast (show (0:ℝ)<2+2*(b:ℝ)+(2*(a:ℝ)+(c:ℝ)) by linarith)
  · exact_mod_cast (show (0:ℝ)<2+2*(b:ℝ)-(2*(a:ℝ)+(c:ℝ)) by linarith)
end
end OMA.S_mo_447544.Classification

namespace OMA.S_mo_447544.Classification
open Polynomial
open scoped Polynomial

theorem shape_cases (g : ℤ[X]) (hm : g.Monic) (hrev : g.reverse=g)
    (hpos : 0<g.natDegree) (hdeg : g.natDegree≤6) :
    (∃ x : ℝ, aeval x g=0) ∨ (∃ a, g=polyTwo a) ∨ (∃ a b, g=polyFour a b) ∨
      (∃ a b c, g=polySix a b c) := by
  by_cases ho : Odd g.natDegree
  · left
    refine ⟨-1,?_⟩
    let _ := invertibleOfNonzero (show (-1:ℝ)≠0 by norm_num)
    have ev := eval₂_reverse_mul_pow (algebraMap ℤ ℝ) (-1:ℝ) g
    rw [hrev,ho.neg_one_pow,invOf_eq_inv] at ev
    simp only [inv_neg,inv_one,mul_neg_one] at ev
    change -(aeval (-1:ℝ) g) = aeval (-1:ℝ) g at ev
    linarith
  have ds : g.natDegree=2 ∨ g.natDegree=4 ∨ g.natDegree=6 := by
    rw [Nat.odd_iff] at ho
    omega
  have mirror (i : ℕ) (hi : i ≤ g.natDegree) : g.coeff i = g.coeff (g.natDegree-i) := by
    nth_rw 1 [← hrev]
    rw [coeff_reverse,revAt_le hi]
  have c0 : g.coeff 0=1 := by
    simpa only [Nat.sub_zero, hm.coeff_natDegree] using mirror 0 (Nat.zero_le _)
  rcases ds with d|d|d
  · right; left; refine ⟨g.coeff 1,?_⟩
    have en : g.coeff 2=1 := d ▸ hm.coeff_natDegree
    calc
      g = _ := g.as_sum_range_C_mul_X_pow
      _ = _ := by rw [d]; simp [Finset.sum_range_succ,polyTwo,en,c0]; ring
  · right; right; left; refine ⟨g.coeff 1,g.coeff 2,?_⟩
    have en : g.coeff 4=1 := d ▸ hm.coeff_natDegree
    have e3 : g.coeff 3=g.coeff 1 := by simpa [d] using mirror 3 (by omega)
    calc
      g = _ := g.as_sum_range_C_mul_X_pow
      _ = _ := by rw [d]; simp [Finset.sum_range_succ,polyFour,en,e3,c0]; ring
  · right; right; right; refine ⟨g.coeff 1,g.coeff 2,g.coeff 3,?_⟩
    have en : g.coeff 6=1 := d ▸ hm.coeff_natDegree
    have e4 : g.coeff 4=g.coeff 2 := by simpa [d] using mirror 4 (by omega)
    have e5 : g.coeff 5=g.coeff 1 := by simpa [d] using mirror 5 (by omega)
    calc
      g = _ := g.as_sum_range_C_mul_X_pow
      _ = _ := by rw [d]; simp [Finset.sum_range_succ,polySix,en,e4,e5,c0]; ring

end OMA.S_mo_447544.Classification

namespace OMA.S_mo_447544.Classification
open Polynomial
noncomputable section

theorem classify_shapes (g : ℤ[X]) (hM : M g^4 ≤ 5)
    (hs : (∃ x : ℝ, aeval x g = 0) ∨ (∃ a, g = polyTwo a) ∨
      (∃ a b, g = polyFour a b) ∨ (∃ a b c, g = polySix a b c)) :
    (∃ x : ℝ, aeval x g = 0) ∨
    ∃ k ∈ ([3,4,5,6,7,8,9,10,12,14,18] : List ℕ), cyclotomic k ℤ ∣ g := by
  by_cases hreal : ∃ x : ℝ, aeval x g = 0
  · exact Or.inl hreal
  right
  rcases hs with hr | ⟨a,rfl⟩ | ⟨a,b,rfl⟩ | ⟨a,b,c,rfl⟩
  · exact (hreal hr).elim
  · exact survivors_two a (endpoints_two a hreal)
  · obtain ⟨hw,ha,hb⟩ := allowed_four a b (endpoints_four a b hreal) hM
    exact survivors_four a b (finite_four a b ha hb hw)
  · obtain ⟨hw,ha,hb,hc⟩ := allowed_six a b c (endpoints_six a b c hreal) hM
    exact survivors_six a b c (finite_six a b c ha hb hc hw)
end
end OMA.S_mo_447544.Classification

namespace OMA.S_mo_447544.Classification
open Polynomial
theorem classify (g : ℤ[X]) (hm : g.Monic) (hrev : g.reverse=g)
    (hpos : 0<g.natDegree) (hdeg : g.natDegree≤6)
    (hM : (g.map (Int.castRingHom ℂ)).mahlerMeasure ^ 4 ≤ 5) :
    (∃ x : ℝ, aeval x g = 0) ∨
    ∃ k ∈ ([3,4,5,6,7,8,9,10,12,14,18] : List ℕ), cyclotomic k ℤ ∣ g :=
  classify_shapes g hM (shape_cases g hm hrev hpos hdeg)
end OMA.S_mo_447544.Classification

theorem OMA.solution : type_of% @OMA.S_mo_447544.main := by
  intro p q r n hp hq hr hn
  apply FiveSparse.simple_of_classification _ p q r n (by omega) hq hr hn
  intro g hm hrev hpos hdeg hM
  rcases OMA.S_mo_447544.Classification.classify g hm hrev hpos hdeg hM with hx | ⟨k,hk,hdiv⟩
  · exact Or.inl hx
  · right
    refine ⟨k,?_,hdiv⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    omega
