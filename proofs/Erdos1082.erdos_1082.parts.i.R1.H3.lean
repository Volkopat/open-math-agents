import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! A repeated chord length forces the point onto a symmetry axis. After this normalization, the radius is a quotient of cyclotomic integers. Its reductions modulo small primes give the incidence bounds for each of the thirteen polygon orders. -/

open OMA.R_Erdos1082_erdos_1082_parts_i_R1

namespace Erdos1082Trace

lemma folded_chord (g z : ℂ) (n : ℕ) (hn : 0<n) (hg : IsPrimitiveRoot g n)
    (hr : z^n=1) (hne : z≠1) :
    ∃ i ∈ Finset.Icc 1 (n/2), z + z⁻¹ = g^i+(g^i)⁻¹ := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨j,hj,rfl⟩ := hg.eq_pow_of_pow_eq_one hr
  have hjpos : 0 < j := by
    by_contra! h
    obtain rfl : j = 0 := by omega
    exact hne (pow_zero g)
  by_cases h : j ≤ n/2
  · exact ⟨j,Finset.mem_Icc.mpr ⟨hjpos,h⟩,rfl⟩
  · have hmul : g^j * g^(n-j) = 1 := by rw [←pow_add]; convert hg.pow_eq_one using 2 <;> omega
    have hi : g^(n-j) = (g^j)⁻¹ := by
      apply (mul_left_cancel₀ (pow_ne_zero j (hg.ne_zero (by omega))))
      rwa [mul_inv_cancel₀ (pow_ne_zero _ (hg.ne_zero (by omega)))]
    exact ⟨n-j,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by rw [hi,inv_inv,add_comm]⟩

lemma trace_axis (q z y : ℂ) (hz : z≠0) (hy : y≠0) (hne : z ≠ y)
    (h : starRingEnd ℂ q * z+q/z=starRingEnd ℂ q * y+q/y) :
    q = starRingEnd ℂ q * (z*y) := by
  field_simp [hz,hy] at h
  apply (mul_left_inj' (sub_ne_zero.mpr hne)).mp
  linear_combination -h

lemma axis_coordinates (q z e : ℂ) (hq : q = starRingEnd ℂ q * e^2) (he : e≠0) (hz : z≠0) :
    starRingEnd ℂ q*z+q/z+(1-(Complex.normSq q : ℂ)) =
      (q/e) * (z/e+(z/e)⁻¹) + (1-(q/e)^2) := by
  rw [Complex.normSq_eq_conj_mul_self]
  field_simp [he,hz]
  linear_combination (q*z-z^2)*hq

lemma matched_axis (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle) = T)
    (q : ℂ) (hq : q ≠ 0) (hnorm : ‖q‖ ≠ 1) (S : Finset Circle) (hST : S ⊆ T)
    (hmatch : ∀ z ∈ S, dist q (z : ℂ) ∈ distanceSet T) (hsize : T.card/2 < S.card)
    (hn : 0 < T.card) :
    ∃ (eta e r : ℂ) (A : Finset ℂ), IsPrimitiveRoot eta (2*T.card) ∧ (e^T.card = 1 ∨ e^T.card = -1) ∧
      r ≠ 0 ∧ r^2 ≠ 1 ∧ A.card=S.card ∧ ∀ x ∈ A, x^T.card=e^T.card ∧
      ∃ i ∈ Finset.Icc 1 (T.card/2), r^2-r*(x+x⁻¹)+((eta^2)^i+((eta^2)^i)⁻¹)-1=0 := by
  classical
  let n := T.card
  have hn0 : n≠0 := by dsimp [n]; omega
  let eta := Complex.exp (2*Real.pi*Complex.I/(2*n : ℕ))
  have heta : IsPrimitiveRoot eta (2*n) := Complex.isPrimitiveRoot_exp _ (by omega)
  let g := eta^2
  have hg : IsPrimitiveRoot g n := heta.pow (by omega) rfl
  have hfold (z : Circle) (hz : z ∈ S) : ∃ i ∈ Finset.Icc 1 (n/2),
      g^i + (g^i)⁻¹ = starRingEnd ℂ q*(z : ℂ) + q/(z : ℂ) + (1 - (Complex.normSq q : ℂ)) := by
    obtain ⟨w,hw,he⟩ := chord_ratio q T H hT z (hmatch z hz)
    have hwne : (w : ℂ) ≠ 1 := by
      intro hw1
      rw [hw1] at he
      have hd : ‖q-(z:ℂ)‖^2 = 0 := by
        rw [Complex.sq_norm]
        apply Complex.ofReal_injective
        rw [Complex.normSq_eq_conj_mul_self,map_sub,←Circle.coe_inv_eq_conj,Circle.coe_inv]
        rw [Complex.normSq_eq_conj_mul_self] at he
        simp only [inv_one] at he
        field_simp [Circle.coe_ne_zero z] at he ⊢
        simp only [Complex.ofReal_zero,mul_zero] at *
        linear_combination he
      have hzq : q=(z:ℂ) := sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (q-(z:ℂ))]))
      exact hnorm (hzq ▸ Circle.norm_coe _)
    obtain ⟨i,hi,hle⟩ := folded_chord g (w : ℂ) n hn hg (finite_subgroup_root _ _ hT w hw) hwne
    exact ⟨i,hi,hle.symm.trans he⟩
  let idx (z : Circle) := if h : z∈S then (hfold z h).choose else 0
  have hidx (z : Circle) (hz : z ∈ S) : idx z ∈ Finset.Icc 1 (n/2) ∧
      g^(idx z)+(g^(idx z))⁻¹ = starRingEnd ℂ q*(z : ℂ)+q/(z : ℂ)+(1-(Complex.normSq q : ℂ)) := by
    simpa [idx,hz] using (hfold z hz).choose_spec
  obtain ⟨u,hu,v,hv,huv,heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (show (Finset.Icc 1 (n/2)).card<S.card by simpa [n] using hsize)
    (fun z hz => (hidx z hz).1)
  have hfu := (hidx u hu).2
  rw [heq,(hidx v hv).2] at hfu
  have hax := trace_axis q (u : ℂ) (v : ℂ) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_injective.ne huv)
    (by linear_combination -hfu)
  have huvpow : ((u : ℂ)*(v : ℂ))^n = 1 := by
    rw [mul_pow,finite_subgroup_root _ _ hT u (hST hu),finite_subgroup_root _ _ hT v (hST hv),mul_one]
  have : NeZero n := ⟨hn0⟩
  obtain ⟨d,hd,hpow⟩ := hg.eq_pow_of_pow_eq_one huvpow
  let e := eta^d
  have he : e≠0 := pow_ne_zero _ (heta.ne_zero (by omega))
  have he2 : e^2 = (u : ℂ)*(v : ℂ) := by rw [←hpow]; dsimp [g,e]; rw [←pow_mul,←pow_mul,Nat.mul_comm]
  have he2n : (e^n)^2=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul,he2,huvpow]
  have hnorme : ‖e‖=1 := by
    have h := congrArg norm heta.pow_eq_one
    have hη : ‖eta‖=1 := by
      rw [norm_pow,norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega : 2*n≠0)).mp h
    simp [e,norm_pow,hη]
  let r := q/e
  have hr : r ≠ 0 := div_ne_zero hq he
  have hr2 : r^2 ≠ 1 := by
    intro hr2
    have h := sq_eq_one_iff.mp hr2
    have hh : ‖r‖=1 := by rcases h with h|h <;> simp [h]
    exact hnorm (by simpa [r,norm_div,hnorme] using hh)
  let f (z : Circle) := (z : ℂ)/e
  have hfinj : Function.Injective f := fun _ _ h => Circle.coe_injective ((div_left_inj' he).mp h)
  refine ⟨eta,e,r,S.image f,heta,sq_eq_one_iff.mp he2n,hr,hr2,Finset.card_image_of_injective _ hfinj,?_⟩
  intro x hx
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
  have hzn := finite_subgroup_root _ _ hT z (hST hz)
  refine ⟨?_,idx z,(hidx z hz).1,?_⟩
  · change ((z:ℂ)/e)^n=e^n
    rw [div_pow,hzn]; rcases sq_eq_one_iff.mp he2n with h|h <;> simp [h]
  · have ha := axis_coordinates q (z : ℂ) e (he2 ▸ hax) he (Circle.coe_ne_zero _)
    have hh := (hidx z hz).2
    rw [ha] at hh
    dsimp [r,f]
    linear_combination hh

end Erdos1082Trace
namespace Erdos1082Finite

def modTrace {p : ℕ} (e : ZMod p) (n j : ℕ) := e^j+e^(2*n-j)

def modCertificate (n p : ℕ) (e : ZMod p) [NeZero p] : Prop :=
  ∀ s : Fin 2, ∀ R : ZMod p, R≠0 → R≠1 → R≠ -1 →
    2*((Finset.range n).filter (fun j =>
      1+R*modTrace e n (2*j+s.val)-R^2 ∈
        (Finset.Icc 1 (n/2)).image (fun i => modTrace e n (2*i)))).card ≤ n

lemma root_of_checks (p n : ℕ) (e : ZMod p) (hn : 0<n) (hpow : e^n=1)
    (hcheck : ∀ i : Fin n, 0 < i.val → e^i.val ≠ 1) : IsPrimitiveRoot e n := by
  apply IsPrimitiveRoot.mk_of_lt e hn hpow
  intro i hpos hlt
  exact hcheck ⟨i,hlt⟩ hpos


set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_7 : IsPrimitiveRoot (4 : ZMod 29) (2*7) ∧ modCertificate 7 29 4 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_8 : IsPrimitiveRoot (3 : ZMod 17) (2*8) ∧ modCertificate 8 17 3 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_10 : IsPrimitiveRoot (36 : ZMod 41) (2*10) ∧ modCertificate 10 41 36 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_12 : IsPrimitiveRoot (52 : ZMod 73) (2*12) ∧ modCertificate 12 73 52 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_14 : IsPrimitiveRoot (81 : ZMod 113) (2*14) ∧ modCertificate 14 113 81 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_16 : IsPrimitiveRoot (28 : ZMod 97) (2*16) ∧ modCertificate 16 97 28 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_18 : IsPrimitiveRoot (2 : ZMod 37) (2*18) ∧ modCertificate 18 37 2 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_20 : IsPrimitiveRoot (6 : ZMod 41) (2*20) ∧ modCertificate 20 41 6 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_22 : IsPrimitiveRoot (9 : ZMod 89) (2*22) ∧ modCertificate 22 89 9 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_24 : IsPrimitiveRoot (25 : ZMod 97) (2*24) ∧ modCertificate 24 97 25 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_26 : IsPrimitiveRoot (2 : ZMod 53) (2*26) ∧ modCertificate 26 53 2 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_28 : IsPrimitiveRoot (9 : ZMod 113) (2*28) ∧ modCertificate 28 113 9 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma cert_30 : IsPrimitiveRoot (2 : ZMod 61) (2*30) ∧ modCertificate 30 61 2 := by
  constructor
  · apply root_of_checks <;> decide +kernel
  · unfold modCertificate
    decide +kernel

end Erdos1082Finite


open Polynomial
open scoped Polynomial

namespace Erdos1082Modular

lemma recognize_zero {n : ℕ} (hn : 0 < n) {x : ℂ} (hx : IsPrimitiveRoot x n)
    {k : Type} [Field k] [NeZero (n : k)] {y : k} (hy : IsPrimitiveRoot y n) (f : ℤ[X]) :
    aeval x f = 0 → aeval y f = 0 := by
  intro h
  have hdvd : cyclotomic n ℤ ∣ f := by
    rw [cyclotomic_eq_minpoly hx hn]
    exact minpoly.isIntegrallyClosed_dvd (hx.isIntegral hn) h
  obtain ⟨g,rfl⟩ := hdvd
  have hcyc : aeval y (cyclotomic n ℤ) = 0 := by
    simpa [aeval_def,eval₂_eq_eval_map,IsRoot.def] using hy.isRoot_cyclotomic hn
  rw [map_mul,hcyc,zero_mul]

noncomputable def tracePoly (n j : ℕ) : ℤ[X] := X^j+X^(n-j)

lemma eval_tracePoly {k : Type} [Field k] (n j : ℕ) (x : k) (h : x^n=1) (hx : x ≠ 0)
    (hj : j ≤ n) : aeval x (tracePoly n j) = x^j+(x^j)⁻¹ := by
  simp only [tracePoly,map_add,map_pow,aeval_X]
  congr 1
  apply mul_left_cancel₀ (pow_ne_zero j hx)
  rw [mul_inv_cancel₀ (pow_ne_zero _ hx),←pow_add,Nat.add_sub_of_le hj,h]

lemma sign_exponents (n : ℕ) (hn : 0<n) (eta e : ℂ) (heta : IsPrimitiveRoot eta (2*n))
    (he : e^n=1 ∨ e^n = -1) :
    ∃ s : ℕ, s ≤ 1 ∧ ∀ x : ℂ, x^n=e^n → ∃ i < n, x = eta^(2*i+s) := by
  have : NeZero n := ⟨by omega⟩
  let g := eta^2
  have hg : IsPrimitiveRoot g n := heta.pow (by omega) rfl
  obtain h|h := he
  · refine ⟨0,by omega,?_⟩
    intro x hx
    obtain ⟨i,hi,hr⟩ := hg.eq_pow_of_pow_eq_one (hx.trans h)
    exact ⟨i,hi,by simpa [g,pow_mul] using hr.symm⟩
  · have hneta : eta^n = -1 := by
      apply (sq_eq_one_iff.mp (show (eta^n)^2=1 by rw [←pow_mul,Nat.mul_comm,heta.pow_eq_one])).resolve_left
      exact heta.pow_ne_one_of_pos_of_lt (by omega) (by omega)
    refine ⟨1,by omega,?_⟩
    intro x hx
    have hef : (x/eta)^n=1 := by rw [div_pow,hx,h,hneta]; norm_num
    obtain ⟨i,hi,hr⟩ := hg.eq_pow_of_pow_eq_one hef
    refine ⟨i,hi,?_⟩
    rw [pow_succ,pow_mul]
    exact (div_eq_iff (heta.ne_zero (by omega))).mp hr.symm


def tr {k : Type} [Field k] (x : k) (i : ℕ) := x^i + (x^i)⁻¹

lemma trace_pair {k : Type} [Field k] (a b : k) (ha : a≠0) (hb : b≠0) :
    a+a⁻¹=b+b⁻¹ ↔ a=b ∨ a*b=1 := by
  constructor
  · intro he
    have hzero : (a-b)*(a*b-1)=0 := by field_simp [ha,hb] at he; linear_combination he
    simpa only [mul_eq_zero,sub_eq_zero] using hzero
  · rintro (rfl|h)
    · rfl
    · field_simp [ha,hb]; linear_combination (a-b)*h

lemma recognize_trace {n i j : ℕ} (hn : 0<n) {k L : Type} [Field k] [Field L]
    {x : k} {y : L} (hx : IsPrimitiveRoot x n) (hy : IsPrimitiveRoot y n) :
    tr x i=tr x j → tr y i=tr y j := by
  intro h
  have hx0 := hx.ne_zero (by omega)
  have hy0 := hy.ne_zero (by omega)
  obtain h|h := (trace_pair _ _ (pow_ne_zero _ hx0) (pow_ne_zero _ hx0)).mp h
  · have hm (a : k) (ha : IsPrimitiveRoot a n) (l : ℕ) : a^(l%n)=a^l := by
      rw [ha.eq_orderOf]; exact pow_mod_orderOf _ _
    have hy' (l : ℕ) : y^(l%n)=y^l := by rw [hy.eq_orderOf]; exact pow_mod_orderOf _ _
    have ho : i%n=j%n := hx.pow_inj (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (by
      rw [hm x hx,hm x hx,h])
    apply (trace_pair _ _ (pow_ne_zero _ hy0) (pow_ne_zero _ hy0)).mpr
    exact Or.inl (by rw [←hy' i,←hy' j,ho])
  · apply (trace_pair _ _ (pow_ne_zero _ hy0) (pow_ne_zero _ hy0)).mpr
    rw [←pow_add] at h ⊢
    exact Or.inr ((hy.pow_eq_one_iff_dvd _).mpr ((hx.pow_eq_one_iff_dvd _).mp h))

lemma trace_half {n : ℕ} (hn : 0<n) {k : Type} [Field k] {e : k}
    (he : IsPrimitiveRoot e (2*n)) (i : ℕ) : tr e (i+n) = -tr e i := by
  have hneg : e^n = -1 := by
    apply (sq_eq_one_iff.mp (show (e^n)^2=1 by rw [←pow_mul,Nat.mul_comm,he.pow_eq_one])).resolve_left
    exact he.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  simp [tr,pow_add,hneg,add_comm]


lemma distinct_projections (n s : ℕ) (hn : 0<n) (hs : s≤1) (eta : ℂ)
    (he : IsPrimitiveRoot eta (2*n)) (I : Finset ℕ) (hI : ∀ i ∈ I, i < n) (hbig : 2 < I.card) :
    ∃ a ∈ I, ∃ b ∈ I, tr eta (2*a+s) ≠ tr eta (2*b+s) := by
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hbig
  have inj (i j : ℕ) (hi : i∈I) (hj : j∈I) (h : eta^(2*i+s)=eta^(2*j+s)) : i=j := by
    have h₁ := hI i hi
    have h₂ := hI j hj
    have := he.pow_inj (by omega) (by omega) h
    omega
  have h0 (i : ℕ) : eta^(2*i+s)≠0 := pow_ne_zero _ (he.ne_zero (by omega))
  by_cases hx : tr eta (2*a+s) = tr eta (2*b+s)
  · refine ⟨a,ha,c,hc,?_⟩
    intro hy
    have hu := ((trace_pair _ _ (h0 _) (h0 _)).mp hx).resolve_left (fun h => hab (inj _ _ ha hb h))
    have hv := ((trace_pair _ _ (h0 _) (h0 _)).mp hy).resolve_left (fun h => hac (inj _ _ ha hc h))
    exact hbc (inj _ _ hb hc (mul_left_cancel₀ (h0 _) (hu.trans hv.symm)))
  · exact ⟨a,ha,b,hb,hx⟩

lemma special_radius {k : Type} [Field k] (n s : ℕ) (hn : 0<n) {eta : ℂ} {e : k}
    (hη : IsPrimitiveRoot eta (2*n)) (he : IsPrimitiveRoot e (2*n))
    (r : ℂ) (hr : r^2 ≠ 1) (I : Finset ℕ) (idx : ℕ → ℕ)
    (horig : ∀ j ∈ I, r^2-r*tr eta (2*j+s)+tr eta (2*idx j)-1 = 0)
    (a b : ℕ) (ha : a∈I) (hb : b∈I) (hne : tr eta (2*a+s)≠tr eta (2*b+s))
    (R : k) (hmod : ∀ j ∈ I, R^2-R*tr e (2*j+s)+tr e (2*idx j)-1 = 0) :
    R≠1 ∧ R≠ -1 := by
  constructor
  · rintro rfl
    have lift (j : ℕ) (hj : j∈I) : tr eta (2*j+s)=r+1 := by
      have htr : tr e (2*idx j) = tr e (2*j+s) := by linear_combination hmod j hj
      have hh := recognize_trace (by omega) he hη htr
      have hp : (r-1)*(r+1-tr eta (2*j+s))=0 := by
        have h := horig j hj
        rw [hh] at h
        linear_combination h
      have hr1 : r-1 ≠ 0 := by intro h; apply hr; rw [sub_eq_zero.mp h]; norm_num
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hr1)).symm
    exact hne ((lift _ ha).trans (lift _ hb).symm)
  · rintro rfl
    have lift (j : ℕ) (hj : j∈I) : tr eta (2*j+s)=r-1 := by
      have htr : tr e (2*idx j) = tr e ((2*j+s)+n) := by
        rw [trace_half hn he]
        linear_combination hmod j hj
      have hh := recognize_trace (by omega) he hη htr
      rw [trace_half hn hη] at hh
      have hp : (r+1)*(r-1-tr eta (2*j+s))=0 := by
        have h := horig j hj
        rw [hh] at h
        linear_combination h
      have hr1 : r+1 ≠ 0 := by intro h; apply hr; rw [show r= -1 by linear_combination h]; norm_num
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hr1)).symm
    exact hne ((lift _ ha).trans (lift _ hb).symm)


lemma reduce_radius {k : Type} [Field k] (n s : ℕ) (hn : 0<n) (hs : s≤1) [NeZero ((2*n : ℕ) : k)]
    {eta : ℂ} {e : k} (hη : IsPrimitiveRoot eta (2*n)) (he : IsPrimitiveRoot e (2*n))
    (r : ℂ) (hr0 : r≠0) (hr2 : r^2 ≠ 1) (I : Finset ℕ) (hI : ∀ i ∈ I, i<n) (hbig : 2<I.card)
    (idx : ℕ → ℕ) (hidx : ∀ i ∈ I, idx i ≤ n/2)
    (horig : ∀ j ∈ I, r^2-r*tr eta (2*j+s)+tr eta (2*idx j)-1 = 0) :
    ∃ R : k, R≠0 ∧ R≠1 ∧ R≠ -1 ∧ ∀ j ∈ I, R^2-R*tr e (2*j+s)+tr e (2*idx j)-1 = 0 := by
  obtain ⟨a,ha,b,hb,hab⟩ := distinct_projections n s hn hs eta hη I hI hbig
  let J (i : ℕ) := tracePoly (2*n) (2*i+s)
  let Cc (i : ℕ) := tracePoly (2*n) (2*idx i)
  let D := J a - J b
  let N := Cc a - Cc b
  have valJ {L : Type} [Field L] (v : L) (hv : IsPrimitiveRoot v (2*n)) (j : ℕ) (hj : j∈I) :
      aeval v (J j) = tr v (2*j+s) := by
    have h := hI j hj
    apply eval_tracePoly _ _ _ hv.pow_eq_one (hv.ne_zero (by omega)) (by omega)
  have valC {L : Type} [Field L] (v : L) (hv : IsPrimitiveRoot v (2*n)) (j : ℕ) (hj : j∈I) :
      aeval v (Cc j) = tr v (2*idx j) := by
    have h := hidx j hj
    apply eval_tracePoly _ _ _ hv.pow_eq_one (hv.ne_zero (by omega)) (by omega)
  have hND : aeval eta N = r * aeval eta D := by
    simp only [N,D,map_sub,valC eta hη a ha,valC eta hη b hb,valJ eta hη a ha,valJ eta hη b hb]
    linear_combination horig a ha - horig b hb
  have hDeta : aeval eta D ≠ 0 := by
    simpa only [D,map_sub,valJ eta hη a ha,valJ eta hη b hb,sub_ne_zero] using hab
  have hDe : aeval e D ≠ 0 := by
    simp only [D,map_sub,valJ e he a ha,valJ e he b hb,sub_ne_zero]
    exact fun hh => hab (recognize_trace (by omega) he hη hh)
  have hNe : aeval e N ≠ 0 := by
    intro hh
    simp only [N,map_sub,valC e he a ha,valC e he b hb,sub_eq_zero] at hh
    have hη' := recognize_trace (by omega) he hη hh
    have hNeta : aeval eta N=0 := by
      simpa only [N,map_sub,valC eta hη a ha,valC eta hη b hb,sub_eq_zero] using hη'
    exact (mul_ne_zero hr0 hDeta) (hND ▸ hNeta)
  let R := aeval e N / aeval e D
  have hres (j : ℕ) (hj : j∈I) : R^2-R*tr e (2*j+s)+tr e (2*idx j)-1=0 := by
    let F := N^2-N*J j*D+(Cc j-1)*D^2
    have hC : aeval eta F=0 := by
      simp only [F,map_add,map_sub,map_pow,map_mul,map_one,hND,valJ eta hη j hj,valC eta hη j hj]
      linear_combination (aeval eta D)^2 * horig j hj
    have hM := recognize_zero (by omega) hη he F hC
    simp only [F,map_add,map_sub,map_pow,map_mul,map_one,valJ e he j hj,valC e he j hj] at hM
    dsimp [R]
    field_simp [hDe]
    linear_combination hM
  obtain ⟨hR1,hRn⟩ := special_radius n s hn hη he r hr2 I idx horig a b ha hb hab R hres
  exact ⟨R,div_ne_zero hNe hDe,hR1,hRn,hres⟩

lemma bound_of_certificate (n p : ℕ) (hn : 7 ≤ n) [Fact p.Prime] [NeZero p] [NeZero ((2*n : ℕ) : ZMod p)]
    (e : ZMod p) (he : IsPrimitiveRoot e (2*n)) (hcert : Erdos1082Finite.modCertificate n p e)
    (T : Finset Circle) (H : Subgroup Circle) (hT : (H : Set Circle)=T) (hcard : T.card=n)
    (q : ℂ) (hq : q≠0) (hnorm : ‖q‖≠1) :
    2 * (T.filter (fun z : Circle => dist q (z : ℂ) ∈ distanceSet T)).card ≤ T.card := by
  classical
  let S := T.filter (fun z : Circle => dist q (z : ℂ) ∈ distanceSet T)
  by_contra! h
  change T.card<2*S.card at h
  obtain ⟨eta,u,r,A,hη,hu,hr0,hr2,hA,horig⟩ := Erdos1082Trace.matched_axis T H hT q hq hnorm S
    (Finset.filter_subset _ _) (fun _ hz => (Finset.mem_filter.mp hz).2) (by omega) (by omega)
  rw [hcard] at hη hu horig
  obtain ⟨s,hs,hidx⟩ := sign_exponents n (by omega) eta u hη hu
  let fin (x : A) := (hidx x.1 (horig x.1 x.2).1).choose
  have hfin (x : A) : fin x<n ∧ x.1=eta^(2*fin x+s) := (hidx x.1 (horig x.1 x.2).1).choose_spec
  have hinj : Function.Injective fin := fun a b h => Subtype.ext ((hfin a).2.trans (h ▸ (hfin b).2.symm))
  let I := A.attach.image fin
  have hI : I.card=A.card := by dsimp [I]; rw [Finset.card_image_of_injective _ hinj,Finset.card_attach]
  have hJ (i : ℕ) (hi : i∈I) : i<n ∧ ∃ m ∈ Finset.Icc 1 (n/2),
      r^2-r*tr eta (2*i+s)+tr eta (2*m)-1=0 := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨_,m,hm,hc⟩ := horig x.1 x.2
    refine ⟨(hfin x).1,m,hm,?_⟩
    rw [(hfin x).2] at hc
    simpa [tr,pow_mul] using hc
  let idx (i : ℕ) := if hi : i∈I then ((hJ i hi).2).choose else 0
  have hidx' (i : ℕ) (hi : i∈I) : idx i ∈ Finset.Icc 1 (n/2) ∧
      r^2-r*tr eta (2*i+s)+tr eta (2*idx i)-1=0 := by simpa [idx,hi] using ((hJ i hi).2).choose_spec
  obtain ⟨R,hR0,hR1,hRm,hres⟩ := reduce_radius n s (by omega) hs hη he r hr0 hr2 I
    (fun i hi => (hJ i hi).1) (by omega) idx
    (fun i hi => (Finset.mem_Icc.mp (hidx' i hi).1).2) (fun i hi => (hidx' i hi).2)
  let B := (Finset.range n).filter (fun j => 1+R*Erdos1082Finite.modTrace e n (2*j+s)-R^2 ∈
    (Finset.Icc 1 (n/2)).image (fun i => Erdos1082Finite.modTrace e n (2*i)))
  have hbound : 2*B.card≤n := hcert ⟨s,by omega⟩ R hR0 hR1 hRm
  have htr (j : ℕ) (hj : j≤2*n) : Erdos1082Finite.modTrace e n j = tr e j := by
    unfold Erdos1082Finite.modTrace tr
    have hpos : e ≠ 0 := he.ne_zero (by omega)
    congr 1
    apply mul_left_cancel₀ (pow_ne_zero _ hpos)
    rw [mul_inv_cancel₀ (pow_ne_zero _ hpos),←pow_add,Nat.add_sub_of_le hj,he.pow_eq_one]
  have hsub : I ⊆ B := by
    intro i hi
    have hin := (hJ i hi).1
    have hch := (hidx' i hi).1
    have hch' := (Finset.mem_Icc.mp hch).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin,Finset.mem_image.mpr ⟨idx i,hch,?_⟩⟩
    rw [htr _ (by omega),htr _ (by omega)]
    linear_combination hres i hi
  have hh := Finset.card_le_card hsub
  omega

end Erdos1082Modular

open Erdos1082Finite Erdos1082Modular

theorem OMA.solution : OMA.R_Erdos1082_erdos_1082_parts_i_R1.H3 := by
  intro T H hT hlo hhi hpar q hq hnorm
  have hcases : T.card=7 ∨ T.card=8 ∨ T.card=10 ∨ T.card=12 ∨ T.card=14 ∨ T.card=16 ∨ T.card=18 ∨ T.card=20 ∨ T.card=22 ∨ T.card=24 ∨ T.card=26 ∨ T.card=28 ∨ T.card=30 := by
    rcases hpar with ⟨j,hj⟩|hh <;> omega
  rcases hcases with h|h|h|h|h|h|h|h|h|h|h|h|h
  · letI : Fact (Nat.Prime 29) := ⟨by decide⟩
    letI : NeZero ((2*7 : ℕ) : ZMod 29) := ⟨by decide⟩
    exact bound_of_certificate 7 29 (by omega) 4 cert_7.1 cert_7.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 17) := ⟨by decide⟩
    letI : NeZero ((2*8 : ℕ) : ZMod 17) := ⟨by decide⟩
    exact bound_of_certificate 8 17 (by omega) 3 cert_8.1 cert_8.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 41) := ⟨by decide⟩
    letI : NeZero ((2*10 : ℕ) : ZMod 41) := ⟨by decide⟩
    exact bound_of_certificate 10 41 (by omega) 36 cert_10.1 cert_10.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 73) := ⟨by decide⟩
    letI : NeZero ((2*12 : ℕ) : ZMod 73) := ⟨by decide⟩
    exact bound_of_certificate 12 73 (by omega) 52 cert_12.1 cert_12.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 113) := ⟨by decide⟩
    letI : NeZero ((2*14 : ℕ) : ZMod 113) := ⟨by decide⟩
    exact bound_of_certificate 14 113 (by omega) 81 cert_14.1 cert_14.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 97) := ⟨by decide⟩
    letI : NeZero ((2*16 : ℕ) : ZMod 97) := ⟨by decide⟩
    exact bound_of_certificate 16 97 (by omega) 28 cert_16.1 cert_16.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 37) := ⟨by decide⟩
    letI : NeZero ((2*18 : ℕ) : ZMod 37) := ⟨by decide⟩
    exact bound_of_certificate 18 37 (by omega) 2 cert_18.1 cert_18.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 41) := ⟨by decide⟩
    letI : NeZero ((2*20 : ℕ) : ZMod 41) := ⟨by decide⟩
    exact bound_of_certificate 20 41 (by omega) 6 cert_20.1 cert_20.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 89) := ⟨by decide⟩
    letI : NeZero ((2*22 : ℕ) : ZMod 89) := ⟨by decide⟩
    exact bound_of_certificate 22 89 (by omega) 9 cert_22.1 cert_22.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 97) := ⟨by decide⟩
    letI : NeZero ((2*24 : ℕ) : ZMod 97) := ⟨by decide⟩
    exact bound_of_certificate 24 97 (by omega) 25 cert_24.1 cert_24.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 53) := ⟨by decide⟩
    letI : NeZero ((2*26 : ℕ) : ZMod 53) := ⟨by decide⟩
    exact bound_of_certificate 26 53 (by omega) 2 cert_26.1 cert_26.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 113) := ⟨by decide⟩
    letI : NeZero ((2*28 : ℕ) : ZMod 113) := ⟨by decide⟩
    exact bound_of_certificate 28 113 (by omega) 9 cert_28.1 cert_28.2 T H hT h q hq hnorm
  · letI : Fact (Nat.Prime 61) := ⟨by decide⟩
    letI : NeZero ((2*30 : ℕ) : ZMod 61) := ⟨by decide⟩
    exact bound_of_certificate 30 61 (by omega) 2 cert_30.1 cert_30.2 T H hT h q hq hnorm
