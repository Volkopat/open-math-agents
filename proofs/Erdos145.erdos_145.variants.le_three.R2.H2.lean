import OMAReductions.R_Erdos145_erdos_145_variants_le_three_R2
import Mathlib

/-!
The order-7/2 bound for squarefree gaps and its restriction to completed gaps.

The interval count is mattdorman's kernel-accepted proof from PR 29977 at
b43b24a0b3b2. The packing theorem and passage from interval counts to moments
come from PRs 4368 and 4255. The three source proofs retain their arguments.
The final specialization uses 7/2 < 11/3, identifies the weight g³√g, and
restricts a nonnegative sum to the completed gaps of the parent reduction.
-/
-- Credit: @Pasx71

namespace SquarefreeIntervalMoment
open Filter Finset Erdos145
open scoped Topology

def BoundedMoments : Prop := ∀ q : ℝ, 0 < q → q < 11/3 → ∃ B : ℝ, ∀ᶠ x : ℝ in atTop,
  (1/x) * (∑ n ∈ A x, ((s (n+1) - s n : ℕ) : ℝ)^q) ≤ B

def IntervalPacking : Prop :=
  let bad (x : ℝ) (k : ℕ) := (range (2 * ⌊x⌋₊ + 5)).filter fun v =>
    ∀ j ∈ Ioo 0 (2^k/2 : ℕ), ¬ Squarefree (v+j)
  ∀ x : ℝ, 1 ≤ x → ∀ k : ℕ,
    2^k * ((A x).filter (fun n => Nat.log 2 (s (n+1)-s n) = k)).card ≤ 4 * (bad x k).card

def IntervalCount : Prop :=
  let bad (x : ℝ) (k : ℕ) := (range (2 * ⌊x⌋₊ + 5)).filter fun v =>
    ∀ j ∈ Ioo 0 (2^k/2 : ℕ), ¬ Squarefree (v+j)
  ∀ r : ℝ, 0 < r → r < 8/3 → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ k : ℕ,
    ((2:ℝ)^r)^k * ((bad x k).card : ℝ) ≤ C*x

theorem bounded_moments : IntervalPacking → IntervalCount → BoundedMoments := by
  classical
  intro packing estimate q hq hlim
  let r := (max 0 (q-1) + 8/3)/2
  have r0 : 0 < r := by dsimp [r]; linarith [le_max_left (0:ℝ) (q-1)]
  have rt : r < 8/3 := by dsimp [r]; rw [max_def]; split <;> linarith
  have qr : q < 1+r := by dsimp [r]; linarith [le_max_right (0:ℝ) (q-1)]
  obtain ⟨C,hC,hb⟩ := estimate r r0 rt
  let d := (2:ℝ)^q / (2*2^r)
  have d0 : 0 ≤ d := by dsimp [d]; positivity
  have d1 : d < 1 := by
    dsimp [d]
    rw [div_lt_one (by positivity)]
    simpa [Real.rpow_add (by norm_num : (0:ℝ)<2)] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) qr
  refine ⟨4*C*2^q*(1-d)⁻¹,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with x hx xpos
  have xp : 0<x := by linarith
  let g (n : ℕ) := s (n+1) - s n
  let bin (n : ℕ) := Nat.log 2 (g n)
  let T := (A x).image bin
  let bad (x : ℝ) (k : ℕ) := (range (2 * ⌊x⌋₊ + 5)).filter fun v =>
    ∀ j ∈ Ioo 0 (2^k/2 : ℕ), ¬ Squarefree (v+j)
  have block (k : ℕ) :
      (∑ n ∈ (A x).filter (fun n => bin n=k), (g n:ℝ)^q) ≤ (4*C*x*2^q)*d^k := by
    let S := (A x).filter (fun n => bin n=k)
    have pack : (2:ℝ)^k * S.card ≤ 4*(bad x k).card := by exact_mod_cast packing x xpos k
    have cnt : ((2:ℝ)^r)^k*((bad x k).card:ℝ) ≤ C*x := hx k
    have scaled : (2*(2:ℝ)^r)^k * S.card ≤ 4*C*x := by
      rw [mul_pow]
      have tmp := mul_le_mul_of_nonneg_left pack (show 0 ≤ ((2:ℝ)^r)^k by positivity)
      linarith only [show ((2:ℝ)^r)^k*((2:ℝ)^k * S.card) ≤ ((2:ℝ)^r)^k*(4*(bad x k).card) from tmp,cnt]
    have bound : ∀ n ∈ S, (g n:ℝ)^q ≤ 2^q*((2:ℝ)^q)^k := by
      intro n hn
      have e : Nat.log 2 (g n)=k := (mem_filter.mp hn).2
      have upper := Nat.lt_pow_succ_log_self (by decide : 1<2) (g n)
      rw [e,pow_succ] at upper
      have hu : (g n:ℝ) ≤ (2:ℝ)^k*2 := by exact_mod_cast upper.le
      apply (Real.rpow_le_rpow (by positivity) hu hq.le).trans_eq
      rw [Real.mul_rpow (by positivity) (by norm_num),← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (k:ℝ) q,Real.rpow_mul_natCast (by norm_num)]
      ring
    calc
      _ ≤ ∑ _n ∈ S, 2^q*((2:ℝ)^q)^k := sum_le_sum bound
      _ = S.card * (2^q*((2:ℝ)^q)^k) := by simp
      _ ≤ _ := by
        dsimp [d]
        rw [div_pow]
        rw [← mul_div_assoc,le_div_iff₀ (by positivity)]
        convert mul_le_mul_of_nonneg_right scaled (show 0 ≤ 2^q*((2:ℝ)^q)^k by positivity) using 1 <;> ring
  have total := sum_le_sum (s := T) (fun k _ => block k)
  rw [sum_fiberwise_of_maps_to (fun n hn => mem_image_of_mem bin hn),← mul_sum] at total
  have geom := (summable_geometric_of_lt_one d0 d1).sum_le_tsum T (fun i _ => pow_nonneg d0 i)
  rw [tsum_geometric_of_lt_one d0 d1] at geom
  change 1/x * (∑ n ∈ A x,(g n:ℝ)^q) ≤ _
  calc
    _ ≤ 1/x*((4*C*x*2^q)*(1-d)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact total.trans (mul_le_mul_of_nonneg_left geom (by positivity))
    _ = _ := by field_simp <;> ring
end SquarefreeIntervalMoment

namespace SquarefreeIntervalMoment
open Erdos145 Finset

private lemma next_le_of_squarefree {n z : ℕ} (h : s n < z) (hs : Squarefree z) :
    s (n+1) ≤ z := by
  obtain ⟨i,hi⟩ := (Nat.subset_range_nth (p := Squarefree)) (show z ∈ Set.ofPred Squarefree from hs)
  change s i = z at hi
  have mono : StrictMono s := Nat.nth_strictMono Nat.squarefree_infinite
  rw [← hi] at h ⊢
  exact mono.monotone (show n+1 ≤ i from mono.lt_iff_lt.mp h)

private lemma next_le_double (n : ℕ) : s (n+1) ≤ 2*s n := by
  have h : Squarefree (s n) := Nat.nth_mem_of_infinite Nat.squarefree_infinite n
  obtain ⟨p,hp,hn,hu⟩ := Nat.exists_prime_lt_and_le_two_mul (s n) h.ne_zero
  exact (next_le_of_squarefree hn hp.squarefree).trans hu

theorem packing : IntervalPacking := by
  classical
  intro x hx k
  let W := 2^k
  let m := (W+1)/2
  let G := (A x).filter fun n => Nat.log 2 (s (n+1)-s n) = k
  let B := (range (2*⌊x⌋₊+5)).filter fun v => ∀ j ∈ Ioo 0 (W/2), ¬ Squarefree (v+j)
  change W*G.card ≤ 4*B.card
  have mono : StrictMono s := Nat.nth_strictMono Nat.squarefree_infinite
  have gap {n} (hn : n ∈ G) : W ≤ s (n+1)-s n := by
    have he := (mem_filter.mp hn).2
    have hp := Nat.sub_pos_of_lt (mono (Nat.lt_succ_self n))
    simpa only [he] using Nat.pow_log_le_self 2 hp.ne'
  have bound {n} (hn : n ∈ G) : s n ≤ ⌊x⌋₊ :=
    (mem_Icc.mp (mem_preimage.mp (mem_filter.mp hn).1)).2
  have endpos {n i} (hn : n ∈ G) (hi : i < m) : s n + i < s (n+1) := by
    have := gap hn
    have : 0 < W := pow_pos (by decide) _
    dsimp [m] at hi
    omega
  let f (u : ℕ × ℕ) := s u.1 + u.2
  have maps : Set.MapsTo f (G ×ˢ range m : Finset _) B := by
    rintro ⟨n,i⟩ hu
    obtain ⟨hn,hi⟩ := mem_product.mp hu
    change n ∈ G at hn
    change i ∈ range m at hi
    have hi' := mem_range.mp hi
    have e := endpos hn hi'
    have ub := bound hn
    have dub := next_le_double n
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by dsimp [f]; omega), ?_⟩
    intro j hj sq
    obtain ⟨hj1,hj2⟩ := mem_Ioo.mp hj
    change Squarefree (s n+i+j) at sq
    have := next_le_of_squarefree (n:=n) (z:=s n+i+j) (by omega) sq
    have := gap hn
    change i < (W+1)/2 at hi'
    omega
  have inj : Set.InjOn f (G ×ˢ range m : Finset _) := by
    rintro ⟨n,i⟩ hn ⟨t,j⟩ ht he
    obtain ⟨hn,hi⟩ := mem_product.mp hn
    obtain ⟨ht,hj⟩ := mem_product.mp ht
    change n ∈ G at hn
    change t ∈ G at ht
    change i ∈ range m at hi
    change j ∈ range m at hj
    dsimp [f] at he
    have ei := endpos hn (mem_range.mp hi)
    have ej := endpos ht (mem_range.mp hj)
    have nt : n = t := by
      rcases lt_trichotomy n t with h|h|h
      · have := mono.monotone (show n+1 ≤ t from h)
        omega
      · exact h
      · have := mono.monotone (show t+1 ≤ n from h)
        omega
    subst t
    exact Prod.ext rfl (by omega)
  have hc := card_le_card_of_injOn f maps inj
  simp only [card_product, card_range] at hc
  have hw : W ≤ 4*m := by dsimp [m]; omega
  calc
    W*G.card ≤ (4*m)*G.card := Nat.mul_le_mul_right _ hw
    _ = 4*(G.card*m) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hc

end SquarefreeIntervalMoment

namespace Erdos145H2Proof
open Finset Filter Set
open scoped Topology
open Real (rpow_add rpow_mul rpow_natCast rpow_neg rpow_one one_le_rpow rpow_le_rpow rpow_le_rpow_of_exponent_le rpow_pos_of_pos rpow_nonneg mul_rpow div_rpow log_le_log log_pow log_rpow log_le_sub_one_of_pos log_two_gt_d9)
private abbrev E := ℝ
lemma poly_contDiff (P:Polynomial E) (n:ℕ):ContDiff E n (fun t=>P.eval t):=by
 induction P using Polynomial.induction_on' with
 | add p q hp hq =>
  simpa [Polynomial.eval_add] using hp.add hq
 | monomial m a =>
  simpa [Polynomial.eval_monomial] using contDiff_const.mul (contDiff_id.pow m)
lemma exists_iteratedDeriv_eq_zero_of_zeros :
  ∀ (k:ℕ) (xs:Fin (k+1)->E) (f:E->E),StrictMono xs → ContDiffOn E k f (Icc (xs 0) (xs (Fin.last k))) → (∀ i,f (xs i)=0) → ∃ ξ∈Icc (xs 0) (xs (Fin.last k)),(1<=k->ξ∈Ioo (xs 0) (xs (Fin.last k)))/\iteratedDeriv k f ξ=0:=by
 intro k
 induction k with
 | zero =>
  intro xs f _ _ h0;refine ⟨xs 0,⟨le_rfl,le_rfl⟩,fun h=>by omega,?_⟩;simpa [iteratedDeriv_zero] using h0 0
 | succ k ih =>
  intro xs f hmono hcd h0
  have hstep:∀ i:Fin (k+1),∃ y∈Ioo (xs i.castSucc) (xs i.succ),deriv f y=0:=by
   intro i;have hlt:xs i.castSucc < xs i.succ:=hmono Fin.castSucc_lt_succ
   have hsub:Icc (xs i.castSucc) (xs i.succ)⊆Icc (xs 0) (xs (Fin.last (k+1))):=by
    intro t ht;exact ⟨(hmono.monotone (Fin.zero_le _)).trans ht.1,ht.2.trans (hmono.monotone (Fin.le_last _))⟩
   have hcont:ContinuousOn f (Icc (xs i.castSucc) (xs i.succ)) :=(hcd.continuousOn).mono hsub;have heq:f (xs i.castSucc)=f (xs i.succ):=by rw [h0,h0]
   exact exists_deriv_eq_zero hlt hcont heq
  choose ys hys_mem hys_eq using hstep
  have hys_mono:StrictMono ys:=by
   intro i j hij;have h1:ys i < xs i.succ:=(hys_mem i).2;have h2:xs j.castSucc < ys j:=(hys_mem j).1
   have hle:i.succ<=j.castSucc:=by
    show (i:ℕ)+1<=(j:ℕ)
    exact hij
   exact lt_trans h1 (lt_of_le_of_lt (hmono.monotone hle) h2)
  have hsub_y:Icc (ys 0) (ys (Fin.last k))⊆Ioo (xs 0) (xs (Fin.last (k+1))):=by
   intro t ht;have hlo:xs 0 < ys 0:=(hys_mem 0).1;have hhi:ys (Fin.last k) < xs (Fin.last (k+1)):=by simpa [Fin.succ_last] using (hys_mem (Fin.last k)).2
   exact ⟨lt_of_lt_of_le hlo ht.1,lt_of_le_of_lt ht.2 hhi⟩
  have hcd_deriv:ContDiffOn E k (deriv f) (Icc (ys 0) (ys (Fin.last k))):=by
   have hcd_open:ContDiffOn E ((k+1:ℕ):WithTop ℕ∞) f (Ioo (xs 0) (xs (Fin.last (k+1)))) :=hcd.mono Ioo_subset_Icc_self;have hderiv_open:ContDiffOn E k (deriv f) (Ioo (xs 0) (xs (Fin.last (k+1)))) :=hcd_open.deriv_of_isOpen isOpen_Ioo (by norm_cast)
   exact hderiv_open.mono hsub_y
  obtain ⟨ξ,hξ_mem,_,hξ_eq⟩:=ih ys (deriv f) hys_mono hcd_deriv hys_eq;have hξ_ioo:ξ∈Ioo (xs 0) (xs (Fin.last (k+1))):=hsub_y hξ_mem;refine ⟨ξ,Ioo_subset_Icc_self hξ_ioo,fun _=>hξ_ioo,?_⟩;rw [iteratedDeriv_succ'];exact hξ_eq
noncomputable def dividedDiff {k:ℕ} (xs ys:Fin (k+1)->E):E :=∑ j:Fin (k+1),ys j/∏ i∈Finset.univ.erase j,(xs j-xs i)
noncomputable def lagrangePoly {k:ℕ} (xs ys:Fin (k+1)->E):Polynomial E := ∑ j:Fin (k+1),Polynomial.C (ys j/∏ i∈Finset.univ.erase j,(xs j-xs i)) * ∏ i∈Finset.univ.erase j,(Polynomial.X-Polynomial.C (xs i))
lemma lagrangePoly_eval {k:ℕ} (xs ys:Fin (k+1)->E)
  (hinj:Function.Injective xs) (m:Fin (k+1)) :
  (lagrangePoly xs ys).eval (xs m)=ys m:=by
 unfold lagrangePoly;rw [Polynomial.eval_finsetSum];rw [Finset.sum_eq_single m]
 ·
  rw [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_prod]
  have hne:(∏ i∈Finset.univ.erase m,(xs m-xs i))≠0:=by
   apply Finset.prod_ne_zero_iff.mpr;intro i hi;exact sub_ne_zero.mpr (fun h=>(Finset.ne_of_mem_erase hi) (hinj h).symm)
  have hprod:(∏ i∈Finset.univ.erase m,(Polynomial.X-Polynomial.C (xs i)).eval (xs m)) = ∏ i∈Finset.univ.erase m,(xs m-xs i):=by
   apply prod_congr rfl;intro i _;simp
  rw [hprod,div_mul_cancel₀ _ hne]
 ·
  intro j _ hjm;rw [Polynomial.eval_mul,Polynomial.eval_prod];have hm_mem:m∈Finset.univ.erase j:=mem_erase.mpr ⟨hjm.symm,Finset.mem_univ _⟩
  have hzero:(∏ i∈Finset.univ.erase j,(Polynomial.X-Polynomial.C (xs i)).eval (xs m))=0:=by
   apply Finset.prod_eq_zero hm_mem;simp
  rw [hzero,mul_zero]
 · intro hm;exact (hm (Finset.mem_univ m)).elim
lemma lagrangePoly_natDegree_le {k:ℕ} (xs ys:Fin (k+1)->E) :
  (lagrangePoly xs ys).natDegree<=k:=by
 unfold lagrangePoly;apply (Polynomial.natDegree_sum_le _ _).trans;rw [Finset.fold_max_le];refine ⟨Nat.zero_le k,?_⟩;intro j _;apply (Polynomial.natDegree_mul_le).trans;rw [Polynomial.natDegree_C,zero_add];apply (Polynomial.natDegree_prod_le _ _).trans
 calc
  ∑ i∈Finset.univ.erase j,(Polynomial.X-Polynomial.C (xs i)).natDegree
    ≤ ∑ _i∈Finset.univ.erase j,1:=by
   apply sum_le_sum;intro i _;rw [Polynomial.natDegree_X_sub_C]
  _ = (Finset.univ.erase j).card:=by simp
  _ = k:=by simp
lemma lagrangePoly_coeff_top {k:ℕ} (xs ys:Fin (k+1)->E) :
  (lagrangePoly xs ys).coeff k=dividedDiff xs ys:=by
 unfold lagrangePoly dividedDiff;rw [Polynomial.finsetSum_coeff];apply sum_congr rfl;intro j _;rw [Polynomial.coeff_C_mul];let Pj:=∏ i∈Finset.univ.erase j,(Polynomial.X-Polynomial.C (xs i))
 have hmonic:Pj.Monic :=Polynomial.monic_prod_of_monic _ _ (fun i _=>Polynomial.monic_X_sub_C _)
 have hdeg:Pj.natDegree=k:=by
  dsimp [Pj];rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _=>Polynomial.monic_X_sub_C _)];simp
 have hcoeff:Pj.coeff k=1:=by
  have hlead:Pj.coeff Pj.natDegree=1:=hmonic.leadingCoeff;rwa [hdeg] at hlead
 change (ys j/∏ i∈Finset.univ.erase j,(xs j-xs i))*Pj.coeff k=_;rw [hcoeff,mul_one]
lemma eq_lagrangePoly_of_eval {k:ℕ} (xs ys:Fin (k+1)->E)
  (hinj:Function.Injective xs) (P:Polynomial E)
  (hdeg:P.natDegree<=k) (heval:∀ i,P.eval (xs i)=ys i) :
  P=lagrangePoly xs ys:=by
 let Q:=P-lagrangePoly xs ys
 by_contra hne
 have hQne:Q≠0:=sub_ne_zero.mpr hne;have hQdeg:Q.natDegree<=k :=(Polynomial.natDegree_sub_le _ _).trans (max_le hdeg (lagrangePoly_natDegree_le xs ys))
 have hroots:(Finset.univ.image xs)⊆Q.roots.toFinset:=by
  intro x hx;rcases Finset.mem_image.mp hx with ⟨i,_,rfl⟩;rw [Multiset.mem_toFinset,Polynomial.mem_roots hQne,Polynomial.IsRoot];simp [Q,heval i,lagrangePoly_eval xs ys hinj i]
 have hcard1:(Finset.univ.image xs).card=k+1:=by rw [Finset.card_image_of_injective _ hinj,Finset.card_fin]
 have hcard2:Q.roots.toFinset.card<=Q.natDegree :=(Multiset.toFinset_card_le _).trans (Polynomial.card_roots' Q);have hle:=(Finset.card_le_card hroots).trans hcard2;omega
lemma iteratedDeriv_poly_eval_eq (P:Polynomial E) (k:ℕ) (hdeg:P.natDegree<=k) (x:E) :
  iteratedDeriv k (fun t=>P.eval t) x=(k.factorial:E)*P.coeff k:=by
 induction k generalizing P x with
 | zero =>
  rw [iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,one_mul];rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hdeg)];simp
 | succ k ih =>
  rw [iteratedDeriv_succ']
  have hderiv_eq:deriv (fun t=>P.eval t)=fun t=>(Polynomial.derivative P).eval t:=by
   ext t;exact (P.hasDerivAt t).deriv
  rw [hderiv_eq]
  have hdeg':(Polynomial.derivative P).natDegree<=k:=by
   have:=Polynomial.natDegree_derivative_le P
   omega
  rw [ih (Polynomial.derivative P) hdeg' x,Polynomial.coeff_derivative];rw [Nat.factorial_succ];push_cast;ring
lemma contDiffAt_deriv_of_succ {k:ℕ} {f:E->E} {ξ:E}
  (hf:ContDiffAt E ((k+1:ℕ):WithTop ℕ∞) f ξ) :
  ContDiffAt E k (deriv f) ξ:=by
 obtain ⟨u,hu_mem,hcd_u⟩:=hf.contDiffOn (m:=k+1) le_rfl (by simp);obtain ⟨v,hv_sub,hv_open,hξ_v⟩:=mem_nhds_iff.mp hu_mem;have hcd_v:ContDiffOn E ((k+1:ℕ):WithTop ℕ∞) f v:=hcd_u.mono hv_sub
 have hd_v:ContDiffOn E k (deriv f) v:=hcd_v.deriv_of_isOpen hv_open (by norm_cast);exact hd_v.contDiffAt (hv_open.mem_nhds hξ_v)
lemma iteratedDeriv_sub_smooth {k:ℕ} {f g:E->E} {ξ:E}
  (hf:ContDiffAt E k f ξ) (hg:ContDiffAt E k g ξ) :
  iteratedDeriv k (fun t=>f t-g t) ξ=iteratedDeriv k f ξ-iteratedDeriv k g ξ:=by
 induction k generalizing f g ξ with
 | zero=>simp [iteratedDeriv_zero]
 | succ k ih =>
  rw [iteratedDeriv_succ',iteratedDeriv_succ',iteratedDeriv_succ']
  have hnhds:∀ᶠ t in 𝓝 ξ,deriv (fun s=>f s-g s) t=deriv f t-deriv g t:=by
   filter_upwards [hf.eventually (by simp),hg.eventually (by simp)] with t hft hgt
   have hfd:DifferentiableAt E f t:=hft.differentiableAt (by simp);have hgd:DifferentiableAt E g t:=hgt.differentiableAt (by simp);exact deriv_sub hfd hgd
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hnhds];exact ih (contDiffAt_deriv_of_succ hf) (contDiffAt_deriv_of_succ hg)
theorem exists_dividedDiff_eq_iteratedDeriv {k:ℕ} (hk:1<=k) (xs:Fin (k+1)->E) (f:E->E)
  (hmono:StrictMono xs)
  (hcd:ContDiffOn E k f (Icc (xs 0) (xs (Fin.last k)))) :
  ∃ ξ∈Ioo (xs 0) (xs (Fin.last k)),dividedDiff xs (f ∘ xs)=iteratedDeriv k f ξ/(k.factorial:E):=by
 let P:=lagrangePoly xs (f ∘ xs);let F:=fun t=>f t-P.eval t;have hcdP:ContDiffOn E k (fun t=>P.eval t) (Icc (xs 0) (xs (Fin.last k))) :=(poly_contDiff P k).contDiffOn;have hcdF:ContDiffOn E k F (Icc (xs 0) (xs (Fin.last k))):=hcd.sub hcdP
 have hzeros:∀ i,F (xs i)=0:=by
  intro i;dsimp [F,P];rw [lagrangePoly_eval xs (f ∘ xs) hmono.injective i];simp
 obtain ⟨ξ,_,hξ_ioo_fn,hξ_eq⟩:=exists_iteratedDeriv_eq_zero_of_zeros k xs F hmono hcdF hzeros;have hξ_ioo:ξ∈Ioo (xs 0) (xs (Fin.last k)):=hξ_ioo_fn hk;have hf_at:ContDiffAt E k f ξ :=hcd.contDiffAt (Icc_mem_nhds hξ_ioo.1 hξ_ioo.2)
 have hP_at:ContDiffAt E k (fun t=>P.eval t) ξ :=(poly_contDiff P k).contDiffAt;have hsub:=iteratedDeriv_sub_smooth hf_at hP_at;rw [hsub] at hξ_eq;have hP_der:=iteratedDeriv_poly_eval_eq P k (lagrangePoly_natDegree_le xs (f ∘ xs)) ξ
 rw [lagrangePoly_coeff_top] at hP_der;rw [hP_der] at hξ_eq;refine ⟨ξ,hξ_ioo,?_⟩;have hfac:(k.factorial:E)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k);field_simp [hfac];linarith
def vandermondeInt {k:ℕ} (xs:Fin (k+1)->ℤ):ℤ :=∏ i:Fin (k+1),∏ j∈Finset.univ.filter (fun j=>i < j),(xs j-xs i)
def vandermondeErase {k:ℕ} (xs:Fin (k+1)->ℤ) (j:Fin (k+1)):ℤ := ∏ a∈Finset.univ.erase j,∏ b∈(Finset.univ.erase j).filter (fun b=>a < b),(xs b-xs a)
lemma vandermondeInt_pos {k:ℕ} (xs:Fin (k+1)->ℤ) (hmono:StrictMono xs) :
  0 < vandermondeInt xs:=by
 unfold vandermondeInt;apply prod_pos;intro i _;apply prod_pos;intro j hj;exact sub_pos.mpr (hmono (mem_filter.mp hj).2)
lemma vandermondeErase_pos {k:ℕ} (xs:Fin (k+1)->ℤ) (hmono:StrictMono xs)
  (j:Fin (k+1)) :
  0 < vandermondeErase xs j:=by
 unfold vandermondeErase;apply prod_pos;intro a _;apply prod_pos;intro b hb;exact sub_pos.mpr (hmono (mem_filter.mp hb).2)
lemma vandermondeInt_eq_mul_erase {k:ℕ} (xs:Fin (k+1)->ℤ) (j:Fin (k+1)) :
  ∃ s:ℤ,(s=1\/s=-1) ∧ vandermondeInt xs = s*(∏ i∈Finset.univ.erase j,(xs j-xs i))*vandermondeErase xs j:=by
 let pairs:=(Finset.univ:Finset (Fin (k+1) × Fin (k+1))).filter (fun p=>p.1 < p.2)
 have hvand:vandermondeInt xs=∏ p∈pairs,(xs p.2-xs p.1):=by
  unfold vandermondeInt;rw [Finset.prod_sigma'];refine Finset.prod_bij (fun p _=>(p.1,p.2)) ?_ ?_ ?_ ?_
  ·
   intro p hp;simp only [Finset.mem_sigma,Finset.mem_univ,mem_filter,true_and] at hp;exact mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
  ·
   intro p₁ _ p₂ _ h;cases p₁;cases p₂;cases h;rfl
  ·
   intro p hp;refine ⟨⟨p.1,p.2⟩,?_,rfl⟩;simp only [Finset.mem_sigma,Finset.mem_univ,mem_filter,true_and];exact (mem_filter.mp hp).2
  · intro p _;rfl
 have herase:vandermondeErase xs j = ∏ p∈pairs.filter (fun p=>p.1≠j/\p.2≠j),(xs p.2-xs p.1):=by
  unfold vandermondeErase;rw [Finset.prod_sigma'];refine Finset.prod_bij (fun p _=>(p.1,p.2)) ?_ ?_ ?_ ?_
  ·
   intro p hp;simp only [Finset.mem_sigma,mem_erase,mem_filter,Finset.mem_univ,and_true] at hp;exact mem_filter.mpr ⟨mem_filter.mpr ⟨Finset.mem_univ _,hp.2.2⟩,hp.1,hp.2.1⟩
  ·
   intro p₁ _ p₂ _ h;cases p₁;cases p₂;cases h;rfl
  ·
   intro p hp;have hp1:=mem_filter.mp hp;have hp2:=mem_filter.mp hp1.1;refine ⟨⟨p.1,p.2⟩,?_,rfl⟩;simp only [Finset.mem_sigma,mem_erase,mem_filter,Finset.mem_univ,and_true];exact ⟨hp1.2.1,hp1.2.2,hp2.2⟩
  · intro p _;rfl
 have hsplit:pairs = (pairs.filter (fun p=>p.1≠j/\p.2≠j)) ∪
   (pairs.filter (fun p=>p.1=j\/p.2=j)):=by
  ext p;simp only [Finset.mem_union,mem_filter];tauto
 have hdisj:Disjoint (pairs.filter (fun p=>p.1≠j/\p.2≠j))
   (pairs.filter (fun p=>p.1=j\/p.2=j)):=by
  rw [disjoint_filter];intro p _ h1 h2;tauto
 let P1:=pairs.filter (fun p=>p.2=j);let P2:=pairs.filter (fun p=>p.1=j)
 have hP12_eq:pairs.filter (fun p=>p.1=j\/p.2=j)=P1∪P2:=by
  ext p;simp only [P1,P2,Finset.mem_union,mem_filter];tauto
 have hP12_disj:Disjoint P1 P2:=by
  rw [disjoint_filter];intro p hp h2 h1;have hlt:=(mem_filter.mp hp).2;rw [h1,h2] at hlt;exact lt_irrefl _ hlt
 have hP1_prod:(∏ p∈P1,(xs p.2-xs p.1)) = ∏ i∈(Finset.univ.erase j).filter (fun i=>i < j),(xs j-xs i):=by
  refine Finset.prod_bij (fun p _=>p.1) ?_ ?_ ?_ ?_
  ·
   intro p hp;have hp':=mem_filter.mp hp;have hlt:=(mem_filter.mp hp'.1).2;rw [hp'.2] at hlt;exact mem_filter.mpr ⟨mem_erase.mpr ⟨ne_of_lt hlt,Finset.mem_univ _⟩,hlt⟩
  ·
   intro p₁ hp₁ p₂ hp₂ h;exact Prod.ext h ((mem_filter.mp hp₁).2.trans (mem_filter.mp hp₂).2.symm)
  ·
   intro i hi;have hi':=mem_filter.mp hi;refine ⟨(i,j),mem_filter.mpr ⟨mem_filter.mpr ⟨Finset.mem_univ _,hi'.2⟩,rfl⟩,rfl⟩
  ·
   intro p hp;rw [(mem_filter.mp hp).2]
 have hP2_prod:(∏ p∈P2,(xs p.2-xs p.1)) = (-1:ℤ)^((Finset.univ.erase j).filter (fun i=>j < i)).card * ∏ i∈(Finset.univ.erase j).filter (fun i=>j < i),(xs j-xs i):=by
  have hbij:(∏ p∈P2,(xs p.2-xs p.1)) = ∏ i∈(Finset.univ.erase j).filter (fun i=>j < i),(xs i-xs j):=by
   refine Finset.prod_bij (fun p _=>p.2) ?_ ?_ ?_ ?_
   ·
    intro p hp;have hp':=mem_filter.mp hp;have hlt:=(mem_filter.mp hp'.1).2;rw [hp'.2] at hlt;exact mem_filter.mpr ⟨mem_erase.mpr ⟨ne_of_gt hlt,Finset.mem_univ _⟩,hlt⟩
   ·
    intro p₁ hp₁ p₂ hp₂ h;exact Prod.ext ((mem_filter.mp hp₁).2.trans (mem_filter.mp hp₂).2.symm) h
   ·
    intro i hi;have hi':=mem_filter.mp hi;refine ⟨(j,i),mem_filter.mpr ⟨mem_filter.mpr ⟨Finset.mem_univ _,hi'.2⟩,rfl⟩,rfl⟩
   ·
    intro p hp;rw [(mem_filter.mp hp).2]
  rw [hbij];have hneg:∀ i,xs i-xs j=(-1:ℤ)*(xs j-xs i):=fun i=>by ring
  simp_rw [hneg,Finset.prod_mul_distrib,Finset.prod_const]
 have herase_split:(∏ i∈Finset.univ.erase j,(xs j-xs i)) = (∏ i∈(Finset.univ.erase j).filter (fun i=>i < j),(xs j-xs i)) * (∏ i∈(Finset.univ.erase j).filter (fun i=>j < i),(xs j-xs i)):=by
  rw [← Finset.prod_union]
  ·
   congr 1;ext i;simp only [Finset.mem_union,mem_filter,mem_erase,Finset.mem_univ,and_true];constructor
   ·
    intro hne;rcases lt_or_gt_of_ne hne with h | h
    · left;exact ⟨hne,h⟩
    · right;exact ⟨hne,h⟩
   · rintro (⟨hne,_⟩ | ⟨hne,_⟩) <;> exact hne
  ·
   rw [disjoint_filter];intro i _ h1 h2;exact lt_asymm h1 h2
 refine ⟨(-1:ℤ)^((Finset.univ.erase j).filter (fun i=>j < i)).card,neg_one_pow_eq_or _ _,?_⟩;rw [hvand,hsplit,Finset.prod_union hdisj,← herase,hP12_eq,Finset.prod_union hP12_disj,hP1_prod,hP2_prod,herase_split];ring
private lemma card_lt_pairs (k:ℕ) :
  ((Finset.univ:Finset (Fin (k+1) × Fin (k+1))).filter (fun p=>p.1 < p.2)).card = k*(k+1)/2:=by
 let pairs:=(Finset.univ:Finset (Fin (k+1) × Fin (k+1))).filter (fun p=>p.1 < p.2)
 have h1:pairs.card=∑ j:Fin (k+1),(j:ℕ):=by
  have:pairs=Finset.univ.biUnion (fun j:Fin (k+1) =>
    (Finset.univ.filter (fun i:Fin (k+1)=>i < j)).image (fun i=>(i,j))):=by
   ext ⟨a,b⟩;simp only [pairs,mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,Finset.mem_image];constructor
   · intro h;exact ⟨b,a,h,rfl⟩
   · rintro ⟨_,a',h,heq⟩;cases heq;exact h
  rw [this,card_biUnion]
  ·
   apply sum_congr rfl;intro j _;rw [Finset.card_image_of_injective _ (fun a b h=>(Prod.mk.inj h).1)]
   trans (Finset.range (j:ℕ)).card
   ·
    refine Finset.card_bij (fun i _=>(i:ℕ)) ?_ ?_ ?_
    · intro i hi;exact Finset.mem_range.mpr (mem_filter.mp hi).2
    · intro i₁ _ i₂ _ h;exact Fin.ext h
    ·
     intro m hm;have hm':=Finset.mem_range.mp hm;refine ⟨⟨m,lt_trans hm' j.isLt⟩,mem_filter.mpr ⟨Finset.mem_univ _,hm'⟩,rfl⟩
   · exact card_range _
  ·
   intro j₁ _ j₂ _ hne;change Disjoint _ _;rw [Finset.disjoint_left];intro p hp1 hp2;rcases Finset.mem_image.mp hp1 with ⟨_,_,rfl⟩;rcases Finset.mem_image.mp hp2 with ⟨_,_,heq⟩;exact hne (Prod.mk.inj heq).2.symm
 rw [h1,Fin.sum_univ_eq_sum_range (fun n=>n) (k+1),Finset.sum_range_id];simp [Nat.mul_comm]
lemma vandermondeInt_le_pow {k:ℕ} (xs:Fin (k+1)->ℤ) (hmono:StrictMono xs) :
  vandermondeInt xs<=(xs (Fin.last k)-xs 0)^(k*(k+1)/2):=by
 let pairs:=(Finset.univ:Finset (Fin (k+1) × Fin (k+1))).filter (fun p=>p.1 < p.2)
 have hvand:vandermondeInt xs=∏ p∈pairs,(xs p.2-xs p.1):=by
  unfold vandermondeInt;rw [Finset.prod_sigma'];refine Finset.prod_bij (fun p _=>(p.1,p.2)) ?_ ?_ ?_ ?_
  ·
   intro p hp;simp only [Finset.mem_sigma,Finset.mem_univ,mem_filter,true_and] at hp;exact mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
  ·
   intro p₁ _ p₂ _ h;cases p₁;cases p₂;cases h;rfl
  ·
   intro p hp;refine ⟨⟨p.1,p.2⟩,?_,rfl⟩;simp only [Finset.mem_sigma,Finset.mem_univ,mem_filter,true_and];exact (mem_filter.mp hp).2
  · intro p _;rfl
 have hcard:pairs.card=k*(k+1)/2:=card_lt_pairs k;rw [hvand,← hcard,← Finset.prod_const];apply Finset.prod_le_prod
 ·
  intro p hp;exact le_of_lt (sub_pos.mpr (hmono (mem_filter.mp hp).2))
 ·
  intro p _;have h1:xs 0<=xs p.1:=hmono.monotone (Fin.zero_le _);have h2:xs p.2<=xs (Fin.last k):=hmono.monotone (Fin.le_last _);omega
lemma vandermondeErase_le_pow {k:ℕ} (xs:Fin (k+1)->ℤ) (hmono:StrictMono xs)
  (j:Fin (k+1)) :
  vandermondeErase xs j<=(xs (Fin.last k)-xs 0)^(k*(k-1)/2):=by
 let allp:=(Finset.univ:Finset (Fin (k+1) × Fin (k+1))).filter (fun p=>p.1 < p.2);let pairs:=allp.filter (fun p=>p.1≠j/\p.2≠j)
 have herase:vandermondeErase xs j=∏ p∈pairs,(xs p.2-xs p.1):=by
  unfold vandermondeErase;rw [Finset.prod_sigma'];refine Finset.prod_bij (fun p _=>(p.1,p.2)) ?_ ?_ ?_ ?_
  ·
   intro p hp;simp only [Finset.mem_sigma,mem_erase,mem_filter,Finset.mem_univ,and_true] at hp;exact mem_filter.mpr ⟨mem_filter.mpr ⟨Finset.mem_univ _,hp.2.2⟩,hp.1,hp.2.1⟩
  ·
   intro p₁ _ p₂ _ h;cases p₁;cases p₂;cases h;rfl
  ·
   intro p hp;have hp1:=mem_filter.mp hp;have hp2:=mem_filter.mp hp1.1;refine ⟨⟨p.1,p.2⟩,?_,rfl⟩;simp only [Finset.mem_sigma,mem_erase,mem_filter,Finset.mem_univ,and_true];exact ⟨hp1.2.1,hp1.2.2,hp2.2⟩
  · intro p _;rfl
 have hcard:pairs.card=k*(k-1)/2:=by
  have hsplit:allp.card=pairs.card+(allp.filter (fun p=>p.1=j\/p.2=j)).card:=by
   rw [← Finset.card_union_of_disjoint]
   ·
    congr 1;ext p;simp only [pairs,Finset.mem_union,mem_filter];tauto
   · rw [disjoint_filter];intro p _ h1 h2;tauto
  have htouch:(allp.filter (fun p=>p.1=j\/p.2=j)).card=k:=by
   trans (Finset.univ.erase j).card
   ·
    refine Finset.card_bij (fun p _=>if p.1=j then p.2 else p.1) ?_ ?_ ?_
    ·
     intro p hp;have hp1:=mem_filter.mp hp;have hlt:=(mem_filter.mp hp1.1).2;split_ifs with h
     · rw [h] at hlt;exact mem_erase.mpr ⟨ne_of_gt hlt,Finset.mem_univ _⟩
     ·
      rcases hp1.2 with h1 | h2
      · exact (h h1).elim
      · rw [h2] at hlt;exact mem_erase.mpr ⟨ne_of_lt hlt,Finset.mem_univ _⟩
    ·
     intro p₁ hp₁ p₂ hp₂ heq;have hlt1:=(mem_filter.mp (mem_filter.mp hp₁).1).2;have hlt2:=(mem_filter.mp (mem_filter.mp hp₂).1).2;have hor1:=(mem_filter.mp hp₁).2;have hor2:=(mem_filter.mp hp₂).2;split_ifs at heq with h1 h2 h2
     · exact Prod.ext (h1.trans h2.symm) heq
     ·
      rcases hor2 with h2' | h2'
      · exact (h2 h2').elim
      · rw [h1] at hlt1;rw [h2'] at hlt2;rw [heq] at hlt1;exact (lt_asymm hlt1 hlt2).elim
     ·
      rcases hor1 with h1' | h1'
      · exact (h1 h1').elim
      · rw [h1'] at hlt1;rw [h2] at hlt2;rw [← heq] at hlt2;exact (lt_asymm hlt1 hlt2).elim
     ·
      rcases hor1 with h1' | h1'
      · exact (h1 h1').elim
      ·
       rcases hor2 with h2' | h2'
       · exact (h2 h2').elim
       · exact Prod.ext heq (h1'.trans h2'.symm)
    ·
     intro i hi;have hne:=Finset.ne_of_mem_erase hi;rcases lt_or_gt_of_ne hne with hlt | hgt
     ·
      refine ⟨(i,j),mem_filter.mpr ⟨mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩,Or.inr rfl⟩,?_⟩;simp [hne]
     ·
      refine ⟨(j,i),mem_filter.mpr ⟨mem_filter.mpr ⟨Finset.mem_univ _,hgt⟩,Or.inl rfl⟩,?_⟩;simp
   · simp
  have hall:allp.card=k*(k+1)/2:=card_lt_pairs k
  cases k with
  | zero=>omega
  | succ k' =>
   have harith:(k'+1)*(k'+1+1)/2=(k'+1)*k'/2+(k'+1):=by
    have hmul:(k'+1)*(k'+1+1)=(k'+1)*k'+2*(k'+1):=by ring
    rw [hmul,Nat.add_mul_div_left _ _ (by decide:0 < 2)]
   simp only [Nat.add_sub_cancel];omega
 rw [herase,← hcard,← Finset.prod_const];apply Finset.prod_le_prod
 ·
  intro p hp;exact le_of_lt (sub_pos.mpr (hmono (mem_filter.mp (mem_filter.mp hp).1).2))
 ·
  intro p _;have h1:xs 0<=xs p.1:=hmono.monotone (Fin.zero_le _);have h2:xs p.2<=xs (Fin.last k):=hmono.monotone (Fin.le_last _);omega
lemma vandermondeInt_mul_dividedDiff_int {k:ℕ} (xs ms:Fin (k+1)->ℤ)
  (hmono:StrictMono xs) :
  ∃ A:ℤ,(A:E)=(vandermondeInt xs:E) * dividedDiff (fun i=>(xs i:E)) (fun i=>(ms i:E)):=by
 have hterm:∀ j:Fin (k+1),∃ t:ℤ,(t:E)=(vandermondeInt xs:E) * ((ms j:E)/∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E))):=by
  intro j;obtain ⟨s,_,hs⟩:=vandermondeInt_eq_mul_erase xs j;refine ⟨s*ms j*vandermondeErase xs j,?_⟩
  have hne:(∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E)))≠0:=by
   apply Finset.prod_ne_zero_iff.mpr;intro i hi;have hne_i:xs j≠xs i:=fun h=>(Finset.ne_of_mem_erase hi) (hmono.injective h).symm;exact sub_ne_zero.mpr (by exact_mod_cast hne_i)
  have hcast:(vandermondeInt xs:E) = (s:E)*(∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E))) * (vandermondeErase xs j:E):=by rw [hs];push_cast;rfl
  rw [hcast];field_simp [hne];push_cast;ring
 choose t ht using hterm
 refine ⟨∑ j,t j,?_⟩;unfold dividedDiff;rw [Finset.mul_sum];push_cast;exact sum_congr rfl (fun j _=>ht j)
lemma vandermondeInt_mul_lagrangePoly_int {k:ℕ} (xs ms:Fin (k+1)->ℤ)
  (hmono:StrictMono xs) :
  ∃ Q:Polynomial ℤ,Polynomial.C (vandermondeInt xs:E) * lagrangePoly (fun i=>(xs i:E)) (fun i=>(ms i:E)) = Q.map (Int.castRingHom E):=by
 have hterm:∀ j:Fin (k+1),∃ Qj:Polynomial ℤ,Polynomial.C (vandermondeInt xs:E) * (Polynomial.C ((ms j:E)/∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E))) * ∏ i∈Finset.univ.erase j,(Polynomial.X-Polynomial.C (xs i:E))) = Qj.map (Int.castRingHom E):=by
  intro j;obtain ⟨s,_,hs⟩:=vandermondeInt_eq_mul_erase xs j;refine ⟨Polynomial.C (s*ms j*vandermondeErase xs j) * ∏ i∈Finset.univ.erase j,(Polynomial.X-Polynomial.C (xs i)),?_⟩
  have hne:(∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E)))≠0:=by
   apply Finset.prod_ne_zero_iff.mpr;intro i hi;have hne_i:xs j≠xs i:=fun h=>(Finset.ne_of_mem_erase hi) (hmono.injective h).symm;exact sub_ne_zero.mpr (by exact_mod_cast hne_i)
  have hcast:(vandermondeInt xs:E) * ((ms j:E)/∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E))) = ((s*ms j*vandermondeErase xs j:ℤ):E):=by
   have hc:(vandermondeInt xs:E) = (s:E)*(∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E))) * (vandermondeErase xs j:E):=by rw [hs];push_cast;rfl
   rw [hc];field_simp [hne];push_cast;ring
  rw [← mul_assoc,← Polynomial.C_mul,hcast];simp [Polynomial.map_mul,Polynomial.map_prod,Polynomial.map_sub]
 choose Qj hQj using hterm
 refine ⟨∑ j,Qj j,?_⟩;unfold lagrangePoly;rw [Finset.mul_sum,Polynomial.map_sum];exact sum_congr rfl (fun j _=>hQj j)
lemma iteratedDeriv_comp_neg (g:E->E) :
  ∀ (m:ℕ) (x:E),iteratedDeriv m (fun t=>g (-t)) x=(-1:E)^m*iteratedDeriv m g (-x):=by
 intro m
 induction m with
 | zero=>intro x;simp [iteratedDeriv_zero]
 | succ m ih =>
  intro x;rw [iteratedDeriv_succ,iteratedDeriv_succ];have hfun:iteratedDeriv m (fun t=>g (-t))=fun t=>(-1:E)^m*iteratedDeriv m g (-t):=by ext t;exact ih t
  rw [hfun,deriv_const_mul_field];rw [deriv_comp_neg (iteratedDeriv m g) x];ring
lemma taylor_order_four_bound_lt {g:E->E} {a b M₄:E}
  (hcd:∀ t∈Icc a b,ContDiffAt E 4 g t)
  (hM4:∀ t∈Icc a b,|iteratedDeriv 4 g t| ≤ M₄)
  {x y:E} (hx:x∈Icc a b) (hy:y∈Icc a b) (hxy:x < y) :
  |g y-(g x+(y-x)*deriv g x+(y-x)^2/2*iteratedDeriv 2 g x + (y-x)^3/6*iteratedDeriv 3 g x)| ≤ M₄*(y-x)^4/24:=by
 have hsub:Icc x y⊆Icc a b:=fun t ht=>⟨hx.1.trans ht.1,ht.2.trans hy.2⟩
 let φ:E->E:=fun t =>
  g y-(g t+(y-t)*deriv g t+(y-t)^2/2*iteratedDeriv 2 g t + (y-t)^3/6*iteratedDeriv 3 g t)
 let C:E:=φ x/(y-x)^4;let ψ:E->E:=fun t=>φ t-C*(y-t)^4
 have hder_ψ:∀ t∈Icc x y,HasDerivAt ψ (-(y-t)^3/6*iteratedDeriv 4 g t+4*C*(y-t)^3) t:=by
  intro t ht;have h4:ContDiffAt E 4 g t:=hcd t (hsub ht);have h3:ContDiffAt E 3 (deriv g) t:=contDiffAt_deriv_of_succ h4
  have h2:ContDiffAt E 2 (iteratedDeriv 2 g) t:=by
   have:=contDiffAt_deriv_of_succ h3
   rwa [show deriv (deriv g)=iteratedDeriv 2 g by rw [← iteratedDeriv_one (f:=g)];exact (iteratedDeriv_succ (n:=1)).symm] at this
  have h1:ContDiffAt E 1 (iteratedDeriv 3 g) t:=by
   have:=contDiffAt_deriv_of_succ h2
   rwa [show deriv (iteratedDeriv 2 g)=iteratedDeriv 3 g from
    (iteratedDeriv_succ (n:=2)).symm] at this
  have hd0:HasDerivAt g (deriv g t) t :=(h4.differentiableAt (by simp)).hasDerivAt
  have hd1:HasDerivAt (deriv g) (iteratedDeriv 2 g t) t:=by
   have:=(h3.differentiableAt (by simp)).hasDerivAt
   rwa [show deriv (deriv g) t=iteratedDeriv 2 g t by rw [← iteratedDeriv_one (f:=g)];exact congrFun (iteratedDeriv_succ (n:=1)).symm t] at this
  have hd2:HasDerivAt (iteratedDeriv 2 g) (iteratedDeriv 3 g t) t:=by
   have:=(h2.differentiableAt (by simp)).hasDerivAt
   rwa [show deriv (iteratedDeriv 2 g) t=iteratedDeriv 3 g t from
    congrFun (iteratedDeriv_succ (n:=2)).symm t] at this
  have hd3:HasDerivAt (iteratedDeriv 3 g) (iteratedDeriv 4 g t) t:=by
   have:=(h1.differentiableAt (by simp)).hasDerivAt
   rwa [show deriv (iteratedDeriv 3 g) t=iteratedDeriv 4 g t from
    congrFun (iteratedDeriv_succ (n:=3)).symm t] at this
  have hlin:HasDerivAt (fun s=>y-s) (-1) t:=by
   have h:=(hasDerivAt_id t).neg.const_add y;have hfn:(fun x=>y+(-id) x)=(fun s=>y-s):=by ext s;simp [sub_eq_add_neg]
   rwa [hfn] at h
  have hp2:HasDerivAt (fun s=>(y-s)^2/2) (-(y-t)) t:=by
   have h:=(hlin.pow 2).div_const 2;have hv:(↑(2:ℕ):E)*(y-t)^(2-1)*(-1)/2=-(y-t):=by push_cast;ring
   rwa [hv] at h
  have hp3:HasDerivAt (fun s=>(y-s)^3/6) (-(y-t)^2/2) t:=by
   have h:=(hlin.pow 3).div_const 6;have hv:(↑(3:ℕ):E)*(y-t)^(3-1)*(-1)/6=-(y-t)^2/2:=by push_cast;ring
   rwa [hv] at h
  have hp4:HasDerivAt (fun s=>C*(y-s)^4) (-4*C*(y-t)^3) t:=by
   have h:=(hlin.pow 4).const_mul C;have hv:C*((↑(4:ℕ):E)*(y-t)^(4-1)*(-1))=-4*C*(y-t)^3:=by push_cast;ring
   rwa [hv] at h
  have hφ:HasDerivAt φ (-(y-t)^3/6*iteratedDeriv 4 g t) t:=by
   have hsum:=((hd0.add (hlin.mul hd1)).add (hp2.mul hd2)).add (hp3.mul hd3);have hfull:=hsum.neg.const_add (g y)
   have hfull':HasDerivAt φ
     (-(deriv g t+(-1*deriv g t+(y-t)*iteratedDeriv 2 g t) + (-(y-t)*iteratedDeriv 2 g t+(y-t)^2/2*iteratedDeriv 3 g t) + (-(y-t)^2/2*iteratedDeriv 3 g t+(y-t)^3/6*iteratedDeriv 4 g t))) t :=
    hfull.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s=>by simp only [φ,Pi.neg_apply,Pi.add_apply,Pi.mul_apply];ring)
   have hv:-(deriv g t+(-1*deriv g t+(y-t)*iteratedDeriv 2 g t) + (-(y-t)*iteratedDeriv 2 g t+(y-t)^2/2*iteratedDeriv 3 g t) + (-(y-t)^2/2*iteratedDeriv 3 g t+(y-t)^3/6*iteratedDeriv 4 g t)) = -(y-t)^3/6*iteratedDeriv 4 g t:=by ring
   rwa [hv] at hfull'
  have hfull:=hφ.sub hp4;have hfull':HasDerivAt ψ (-(y-t)^3/6*iteratedDeriv 4 g t - -4*C*(y-t)^3) t := hfull.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s=>by simp only [ψ,Pi.sub_apply])
  have hv:-(y-t)^3/6*iteratedDeriv 4 g t - -4*C*(y-t)^3 = -(y-t)^3/6*iteratedDeriv 4 g t+4*C*(y-t)^3:=by ring
  rwa [hv] at hfull'
 have hcont:ContinuousOn ψ (Icc x y):=fun t ht=>(hder_ψ t ht).continuousAt.continuousWithinAt
 have hψ_x:ψ x=0:=by
  dsimp [ψ,C];have hne:(y-x)^4≠0:=pow_ne_zero 4 (sub_ne_zero.mpr hxy.ne');rw [div_mul_cancel₀ _ hne,sub_self]
 have hψ_y:ψ y=0:=by simp [ψ,φ]
 obtain ⟨ξ,hξ_ioo,hξ_eq⟩:=exists_deriv_eq_zero hxy hcont (hψ_x.trans hψ_y.symm);have hξ_icc:ξ∈Icc x y:=Ioo_subset_Icc_self hξ_ioo;have hderiv_at:deriv ψ ξ=-(y-ξ)^3/6*iteratedDeriv 4 g ξ+4*C*(y-ξ)^3 :=(hder_ψ ξ hξ_icc).deriv;rw [hderiv_at] at hξ_eq
 have hpos3:0 < (y-ξ)^3:=pow_pos (sub_pos.mpr hξ_ioo.2) 3
 have hC_eq:C=iteratedDeriv 4 g ξ/24:=by
  have hmul:(y-ξ)^3*(4*C-iteratedDeriv 4 g ξ/6)=0:=by linarith
  have hzero:=(mul_eq_zero.mp hmul).resolve_left hpos3.ne';linarith
 have hφ_eq:φ x=iteratedDeriv 4 g ξ*(y-x)^4/24:=by
  have hne:(y-x)^4≠0:=pow_ne_zero 4 (sub_ne_zero.mpr hxy.ne');have h1:φ x=C*(y-x)^4:=by dsimp [C];rw [div_mul_cancel₀ _ hne]
  rw [h1,hC_eq];ring
 change |φ x| ≤ M₄*(y-x)^4/24;rw [hφ_eq,abs_div,abs_mul,abs_of_nonneg (pow_nonneg (sub_pos.mpr hxy).le 4),abs_of_pos (by norm_num:(0:E) < 24)];have hM:=hM4 ξ (hsub hξ_icc);gcongr
lemma taylor_order_four_bound {g:E->E} {a b M₄:E}
  (hcd:∀ t∈Icc a b,ContDiffAt E 4 g t)
  (hM4:∀ t∈Icc a b,|iteratedDeriv 4 g t| ≤ M₄)
  (_hM4_nonneg:0<=M₄)
  {x y:E} (hx:x∈Icc a b) (hy:y∈Icc a b) :
  |g y-(g x+(y-x)*deriv g x+(y-x)^2/2*iteratedDeriv 2 g x + (y-x)^3/6*iteratedDeriv 3 g x)| ≤ M₄ * |y-x| ^ 4/24:=by
 rcases lt_trichotomy x y with hlt | rfl | hgt
 ·
  have h:=taylor_order_four_bound_lt hcd hM4 hx hy hlt;rwa [abs_of_pos (sub_pos.mpr hlt)]
 · simp
 ·
  let g':E->E:=fun t=>g (-t)
  have hcd':∀ t∈Icc (-b) (-a),ContDiffAt E 4 g' t:=by
   intro t ht;have hnt:-t∈Icc a b:=⟨by linarith [ht.2],by linarith [ht.1]⟩;exact (hcd (-t) hnt).comp t contDiffAt_id.neg
  have hM4':∀ t∈Icc (-b) (-a),|iteratedDeriv 4 g' t| ≤ M₄:=by
   intro t ht;have hnt:-t∈Icc a b:=⟨by linarith [ht.2],by linarith [ht.1]⟩;have heq:=iteratedDeriv_comp_neg g 4 t;change |iteratedDeriv 4 (fun s=>g (-s)) t| ≤ M₄;rw [heq];simpa using hM4 (-t) hnt
  have hx':-x∈Icc (-b) (-a):=⟨by linarith [hx.2],by linarith [hx.1]⟩;have hy':-y∈Icc (-b) (-a):=⟨by linarith [hy.2],by linarith [hy.1]⟩;have hlt':-x < -y:=neg_lt_neg hgt;have h:=taylor_order_four_bound_lt hcd' hM4' hx' hy' hlt'
  have hd1:deriv g' (-x)=-deriv g x:=by
   have:=iteratedDeriv_comp_neg g 1 (-x)
   simpa [g',iteratedDeriv_one] using this
  have hd2:iteratedDeriv 2 g' (-x)=iteratedDeriv 2 g x:=by
   have:=iteratedDeriv_comp_neg g 2 (-x)
   simpa [g'] using this
  have hd3:iteratedDeriv 3 g' (-x)=-iteratedDeriv 3 g x:=by
   have:=iteratedDeriv_comp_neg g 3 (-x)
   have hpow:(-1:E)^3=-1:=by norm_num
   simp only [neg_neg,hpow,neg_one_mul] at this;exact this
  have hg_x:g' (-x)=g x:=by simp [g']
  have hg_y:g' (-y)=g y:=by simp [g']
  rw [hg_y,hg_x,hd1,hd2,hd3] at h;have habs:|y-x| = -y - -x:=by rw [abs_of_neg (sub_neg.mpr hgt)];ring
  rw [habs];convert h using 2;ring
theorem neder_order_four {g:E->E} {a L M₀ M₄:E}
  (hL:0 < L)
  (hcd:∀ t∈Icc a (a+L),ContDiffAt E 4 g t)
  (hM0:∀ t∈Icc a (a+L),|g t| ≤ M₀)
  (hM4:∀ t∈Icc a (a+L),|iteratedDeriv 4 g t| ≤ M₄)
  (hM0_nn:0<=M₀) (hM4_nn:0<=M₄)
  {x:E} (hx:x∈Icc a (a+L)) :
  |deriv g x| ≤ 100*(M₀/L+L^3*M₄) ∧
  |iteratedDeriv 2 g x| ≤ 1000*(M₀/L^2+L^2*M₄) ∧
  |iteratedDeriv 3 g x| ≤ 10000*(M₀/L^3+L*M₄):=by
 have hstep:∃ h:E,|h| = L/6 ∧ x+h∈Icc a (a+L)/\x+2*h∈Icc a (a+L)/\x+3*h∈Icc a (a+L):=by
  by_cases hmid:x<=a+L/2
  ·
    refine ⟨L/6,abs_of_pos (by positivity),?_,?_,?_⟩ <;> exact ⟨by linarith [hx.1],by linarith⟩
  ·
    refine ⟨-(L/6),by rw [abs_neg,abs_of_pos (by positivity)],?_,?_,?_⟩ <;> exact ⟨by linarith,by linarith [hx.2]⟩
 obtain ⟨h,habs_h,hx1,hx2,hx3⟩:=hstep;have hh_ne:h≠0:=by intro he;rw [he,abs_zero] at habs_h;linarith
 let d1:=h*deriv g x;let d2:=h^2*iteratedDeriv 2 g x;let d3:=h^3*iteratedDeriv 3 g x;let Δ1:=g (x+h)-g x;let Δ2:=g (x+2*h)-g x;let Δ3:=g (x+3*h)-g x;let R1:=Δ1-(d1+d2/2+d3/6);let R2:=Δ2-(2*d1+2*d2+4/3*d3);let R3:=Δ3-(3*d1+9/2*d2+9/2*d3)
 have hR1:|R1| ≤ M₄ * |h| ^ 4/24:=by
  have:=taylor_order_four_bound hcd hM4 hM4_nn hx hx1
  have hsub:x+h-x=h:=by ring
  rw [hsub] at this;convert this using 2;dsimp [R1,Δ1,d1,d2,d3];ring
 have hR2:|R2| ≤ 16*(M₄ * |h| ^ 4)/24:=by
  have:=taylor_order_four_bound hcd hM4 hM4_nn hx hx2
  have hsub:x+2*h-x=2*h:=by ring
  rw [hsub,abs_mul,abs_of_pos (by norm_num:(0:E) < 2)] at this;have hpow2:(2 * |h|)^4=16 * |h| ^ 4:=by ring
  rw [hpow2] at this
  calc
   |R2| ≤ M₄*(16 * |h| ^ 4)/24:=by convert this using 2;dsimp [R2,Δ2,d1,d2,d3];ring
   _ = 16*(M₄ * |h| ^ 4)/24:=by ring
 have hR3:|R3| ≤ 81*(M₄ * |h| ^ 4)/24:=by
  have:=taylor_order_four_bound hcd hM4 hM4_nn hx hx3
  have hsub:x+3*h-x=3*h:=by ring
  rw [hsub,abs_mul,abs_of_pos (by norm_num:(0:E) < 3)] at this;have hpow3:(3 * |h|)^4=81 * |h| ^ 4:=by ring
  rw [hpow3] at this
  calc
   |R3| ≤ M₄*(81 * |h| ^ 4)/24:=by convert this using 2;dsimp [R3,Δ3,d1,d2,d3];ring
   _ = 81*(M₄ * |h| ^ 4)/24:=by ring
 have hΔ1:|Δ1| ≤ 2*M₀:=by dsimp [Δ1];linarith [abs_sub (g (x+h)) (g x),hM0 (x+h) hx1,hM0 x hx]
 have hΔ2:|Δ2| ≤ 2*M₀:=by dsimp [Δ2];linarith [abs_sub (g (x+2*h)) (g x),hM0 (x+2*h) hx2,hM0 x hx]
 have hΔ3:|Δ3| ≤ 2*M₀:=by dsimp [Δ3];linarith [abs_sub (g (x+3*h)) (g x),hM0 (x+3*h) hx3,hM0 x hx]
 have hid1:d1=3*Δ1-3/2*Δ2+1/3*Δ3-(3*R1-3/2*R2+1/3*R3):=by dsimp [R1,R2,R3];ring
 have hid2:d2=-5*Δ1+4*Δ2-Δ3-(-5*R1+4*R2-R3):=by dsimp [R1,R2,R3];ring
 have hid3:d3=3*Δ1-3*Δ2+Δ3-(3*R1-3*R2+R3):=by dsimp [R1,R2,R3];ring
 have hM4h_nn:0<=M₄ * |h| ^ 4:=mul_nonneg hM4_nn (pow_nonneg (abs_nonneg h) 4)
 have hbd1:|d1| ≤ 10*M₀+3*(M₄ * |h| ^ 4):=by
  rw [hid1]
  have htri:|3*Δ1-3/2*Δ2+1/3*Δ3-(3*R1-3/2*R2+1/3*R3)| ≤ 3 * |Δ1| + 3/2 * |Δ2| + 1/3 * |Δ3| + 3 * |R1| + 3/2 * |R2| + 1/3 * |R3|:=by
   have e1:=abs_sub (3*Δ1-3/2*Δ2+1/3*Δ3) (3*R1-3/2*R2+1/3*R3);have e2:=abs_add_le (3*Δ1-3/2*Δ2) (1/3*Δ3);have e3:=abs_sub (3*Δ1) (3/2*Δ2);have e4:=abs_add_le (3*R1-3/2*R2) (1/3*R3);have e5:=abs_sub (3*R1) (3/2*R2)
   simp only [abs_mul,abs_of_pos (by norm_num:(0:E) < 3),abs_of_pos (by norm_num:(0:E) < 3/2),abs_of_pos (by norm_num:(0:E) < 1/3)] at e2 e3 e4 e5;linarith
  linarith
 have hbd2:|d2| ≤ 20*M₀+7*(M₄ * |h| ^ 4):=by
  rw [hid2]
  have htri:|-5*Δ1+4*Δ2-Δ3-(-5*R1+4*R2-R3)| ≤ 5 * |Δ1| + 4 * |Δ2| + |Δ3| + 5 * |R1| + 4 * |R2| + |R3|:=by
   have e1:=abs_sub (-5*Δ1+4*Δ2-Δ3) (-5*R1+4*R2-R3);have e2:=abs_sub (-5*Δ1+4*Δ2) Δ3;have e3:=abs_add_le (-5*Δ1) (4*Δ2);have e4:=abs_sub (-5*R1+4*R2) R3;have e5:=abs_add_le (-5*R1) (4*R2)
   simp only [abs_mul,abs_neg,abs_of_pos (by norm_num:(0:E) < 5),abs_of_pos (by norm_num:(0:E) < 4)] at e3 e5;linarith
  linarith
 have hbd3:|d3| ≤ 14*M₀+6*(M₄ * |h| ^ 4):=by
  rw [hid3]
  have htri:|3*Δ1-3*Δ2+Δ3-(3*R1-3*R2+R3)| ≤ 3 * |Δ1| + 3 * |Δ2| + |Δ3| + 3 * |R1| + 3 * |R2| + |R3|:=by
   have e1:=abs_sub (3*Δ1-3*Δ2+Δ3) (3*R1-3*R2+R3);have e2:=abs_add_le (3*Δ1-3*Δ2) Δ3;have e3:=abs_sub (3*Δ1) (3*Δ2);have e4:=abs_add_le (3*R1-3*R2) R3;have e5:=abs_sub (3*R1) (3*R2);simp only [abs_mul,abs_of_pos (by norm_num:(0:E) < 3)] at e3 e5;linarith
  linarith
 have hpos_h:0 < |h|:=abs_pos.mpr hh_ne;refine ⟨?_,?_,?_⟩
 ·
  have h1:|h| * |deriv g x| ≤ 10*M₀+3*(M₄ * |h| ^ 4):=by simpa [d1,abs_mul] using hbd1
  rw [← le_div_iff₀' hpos_h] at h1
  calc
   |deriv g x| ≤ (10*M₀+3*(M₄ * |h| ^ 4)) / |h|:=h1
   _ = 10*(M₀ / |h|)+3*M₄ * |h| ^ 3:=by field_simp
   _ = 60*(M₀/L)+3/216*(L^3*M₄):=by rw [habs_h];ring
   _ <= 100*(M₀/L+L^3*M₄):=by
    have:0<=M₀/L:=div_nonneg hM0_nn hL.le
    have:0<=L^3*M₄:=by positivity
    linarith
 ·
  have h2:|h| ^ 2 * |iteratedDeriv 2 g x| ≤ 20*M₀+7*(M₄ * |h| ^ 4):=by simpa [d2,abs_mul,abs_pow] using hbd2
  rw [← le_div_iff₀' (pow_pos hpos_h 2)] at h2
  calc
   |iteratedDeriv 2 g x| ≤ (20*M₀+7*(M₄ * |h| ^ 4)) / |h| ^ 2:=h2
   _ = 20*(M₀ / |h| ^ 2)+7*M₄ * |h| ^ 2:=by field_simp
   _ = 720*(M₀/L^2)+7/36*(L^2*M₄):=by rw [habs_h];ring
   _ <= 1000*(M₀/L^2+L^2*M₄):=by
    have:0<=M₀/L^2:=div_nonneg hM0_nn (sq_nonneg L)
    have:0<=L^2*M₄:=by positivity
    linarith
 ·
  have h3:|h| ^ 3 * |iteratedDeriv 3 g x| ≤ 14*M₀+6*(M₄ * |h| ^ 4):=by simpa [d3,abs_mul,abs_pow] using hbd3
  rw [← le_div_iff₀' (pow_pos hpos_h 3)] at h3
  calc
   |iteratedDeriv 3 g x| ≤ (14*M₀+6*(M₄ * |h| ^ 4)) / |h| ^ 3:=h3
   _ = 14*(M₀ / |h| ^ 3)+6*M₄ * |h|:=by field_simp
   _ = 3024*(M₀/L^3)+L*M₄:=by rw [habs_h];ring
   _ <= 10000*(M₀/L^3+L*M₄):=by
    have:0<=M₀/L^3:=div_nonneg hM0_nn (pow_nonneg hL.le 3)
    have:0<=L*M₄:=by positivity
    linarith
lemma hasDerivAt_c_div_pow (c:E) (n:ℕ) {u:E} (hu:u≠0) :
  HasDerivAt (fun t:E=>c/t^n) (-(n:E)*c/u^(n+1)) u:=by
 have h1:HasDerivAt (fun t:E=>t^n) ((n:E)*u^(n-1)) u:=hasDerivAt_pow n u
 have h2:HasDerivAt (fun t:E=>c/t^n)
   ((0*u^n-c*((n:E)*u^(n-1)))/(u^n)^2) u :=
  (hasDerivAt_const u c).div h1 (pow_ne_zero n hu)
 convert h2 using 1
 cases n with
 | zero=>simp
 | succ k =>
  simp only [Nat.add_sub_cancel];have hpow:u^(k+1)≠0:=pow_ne_zero _ hu;have hpow2:(u^(k+1))^2≠0:=pow_ne_zero _ hpow;field_simp [hu,hpow,hpow2];ring
lemma contDiffAt_c_div_pow (c:E) (n:ℕ) (m:ℕ) {u:E} (hu:u≠0) :
  ContDiffAt E m (fun t:E=>c/t^n) u :=
 contDiffAt_const.div (contDiffAt_id.pow n) (pow_ne_zero n hu)
lemma iteratedDeriv_inv_sq_1 (c:E) {u:E} (hu:0 < u) :
  deriv (fun t:E=>c/t^2) u=-2*c/u^3:=by
 simpa using (hasDerivAt_c_div_pow c 2 hu.ne').deriv
lemma iteratedDeriv_inv_sq_2 (c:E) {u:E} (hu:0 < u) :
  iteratedDeriv 2 (fun t:E=>c/t^2) u=6*c/u^4:=by
 rw [iteratedDeriv_succ,iteratedDeriv_one]
 have heq:(fun t=>deriv (fun s:E=>c/s^2) t) =ᶠ[𝓝 u] (fun t=>(-2*c)/t^3):=by
  filter_upwards [Ioi_mem_nhds hu] with t ht
  exact iteratedDeriv_inv_sq_1 c ht
 rw [Filter.EventuallyEq.deriv_eq heq];have hd:=(hasDerivAt_c_div_pow (-2*c) 3 hu.ne').deriv;convert hd using 1;ring
lemma iteratedDeriv_inv_sq_3 (c:E) {u:E} (hu:0 < u) :
  iteratedDeriv 3 (fun t:E=>c/t^2) u=-24*c/u^5:=by
 rw [iteratedDeriv_succ]
 have heq:(fun t=>iteratedDeriv 2 (fun s:E=>c/s^2) t) =ᶠ[𝓝 u]
   (fun t=>(6*c)/t^4):=by
  filter_upwards [Ioi_mem_nhds hu] with t ht
  exact iteratedDeriv_inv_sq_2 c ht
 rw [Filter.EventuallyEq.deriv_eq heq];have hd:=(hasDerivAt_c_div_pow (6*c) 4 hu.ne').deriv;convert hd using 1;ring
lemma iteratedDeriv_inv_sq_4 (c:E) {u:E} (hu:0 < u) :
  iteratedDeriv 4 (fun t:E=>c/t^2) u=120*c/u^6:=by
 rw [iteratedDeriv_succ]
 have heq:(fun t=>iteratedDeriv 3 (fun s:E=>c/s^2) t) =ᶠ[𝓝 u]
   (fun t=>(-24*c)/t^5):=by
  filter_upwards [Ioi_mem_nhds hu] with t ht
  exact iteratedDeriv_inv_sq_3 c ht
 rw [Filter.EventuallyEq.deriv_eq heq];have hd:=(hasDerivAt_c_div_pow (-24*c) 5 hu.ne').deriv;convert hd using 1;ring
section
open Classical
noncomputable def nearCurveSet (f:E->E) (M:ℕ) (δ:E):Finset ℤ := (Finset.Icc (M:ℤ) (2*(M:ℤ))).filter
  (fun n=>|f (n:E)-(round (f (n:E)):E)| < δ)
lemma round_eq_of_abs_sub_lt_half {x:E} {m:ℤ} (h:|x-(m:E)| < 1/2) :
  round x=m:=by
 have h1:=abs_sub_round x
 have hdiff:|(round x:E)-(m:E)| < 1:=by
  calc
   |(round x:E)-(m:E)| = |(round x:E)-x+(x-(m:E))|:=by ring_nf
   _ <= |(round x:E)-x| + |x-(m:E)|:=abs_add_le _ _
   _ = |x-(round x:E)| + |x-(m:E)|:=by rw [abs_sub_comm]
   _ < 1/2+1/2:=by linarith
   _ = 1:=by norm_num
 have hint:|(round x-m:ℤ)| < 1:=by exact_mod_cast hdiff
 have:=abs_lt.mp hint
 omega
def HasIntDenom (P:Polynomial E):Prop :=∃ q:ℕ,0 < q/\∃ Q:Polynomial ℤ,Polynomial.C (q:E)*P=Q.map (Int.castRingHom E)
noncomputable def polyDenom (P:Polynomial E):ℕ:=by
 classical
 exact if h:HasIntDenom P then Nat.find h else 0
lemma polyDenom_pos {P:Polynomial E} (h:HasIntDenom P):0 < polyDenom P:=by
 classical
 rw [polyDenom,dif_pos h];exact (Nat.find_spec h).1
lemma polyDenom_spec {P:Polynomial E} (h:HasIntDenom P) :
  ∃ Q:Polynomial ℤ,Polynomial.C (polyDenom P:E)*P=Q.map (Int.castRingHom E):=by
 classical
 rw [polyDenom,dif_pos h];exact (Nat.find_spec h).2
lemma polyDenom_le {P:Polynomial E} {q:ℕ} (hq:0 < q)
  (hQ:∃ Q:Polynomial ℤ,Polynomial.C (q:E)*P=Q.map (Int.castRingHom E)) :
  polyDenom P<=q:=by
 classical
 have h:HasIntDenom P:=⟨q,hq,hQ⟩;rw [polyDenom,dif_pos h];exact Nat.find_min' h ⟨hq,hQ⟩
lemma abs_eval_sub_int_ge_inv_polyDenom {P:Polynomial E} (h:HasIntDenom P)
  (n m:ℤ) (hne:P.eval (n:E)≠(m:E)) :
  1/(polyDenom P:E) ≤ |P.eval (n:E)-(m:E)|:=by
 obtain ⟨Q,hQ⟩:=polyDenom_spec h;have hq_pos:(0:E) < (polyDenom P:E):=by exact_mod_cast polyDenom_pos h
 have heval:(polyDenom P:E)*P.eval (n:E)=((Q.eval n:ℤ):E):=by
  have h1:=congrArg (Polynomial.eval (Int.castRingHom E n)) hQ;rw [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map_apply] at h1;simpa using h1
 have hdiff_int:(polyDenom P:E)*(P.eval (n:E)-(m:E)) = ((Q.eval n-(polyDenom P:ℤ)*m:ℤ):E):=by push_cast;linarith
 have hint_ne:Q.eval n-(polyDenom P:ℤ)*m≠0:=by
  intro h0;apply hne;have hmul:(polyDenom P:E)*(P.eval (n:E)-(m:E))=0:=by rw [hdiff_int,h0,Int.cast_zero]
  have hsub:=(mul_eq_zero.mp hmul).resolve_left hq_pos.ne';linarith
 have habs_ge1:(1:E) ≤ |(polyDenom P:E)*(P.eval (n:E)-(m:E))|:=by
  rw [hdiff_int]
  have:(1:ℤ) ≤ |Q.eval n-(polyDenom P:ℤ)*m|:=Int.one_le_abs hint_ne
  exact_mod_cast this
 rw [abs_mul,abs_of_pos hq_pos] at habs_ge1;rw [div_le_iff₀ hq_pos];linarith
lemma hasIntDenom_and_le_of_interp4 {P:Polynomial E} (hdeg:P.natDegree<=3)
  (xs ms:Fin 4->ℤ) (hmono:StrictMono xs)
  (heval:∀ i,P.eval (xs i:E)=(ms i:E)) :
  HasIntDenom P/\(polyDenom P:E)<=((xs 3-xs 0:ℤ):E)^6:=by
 have hinj:Function.Injective (fun i=>(xs i:E)):=by
  intro i j h;exact hmono.injective (Int.cast_injective h)
 have hP:P=lagrangePoly (fun i=>(xs i:E)) (fun i=>(ms i:E)) :=eq_lagrangePoly_of_eval _ _ hinj P hdeg heval;obtain ⟨Q,hQ⟩:=vandermondeInt_mul_lagrangePoly_int xs ms hmono;have hv_pos:0 < vandermondeInt xs:=vandermondeInt_pos xs hmono
 let q:ℕ:=(vandermondeInt xs).toNat;have hq_eq:(q:ℤ)=vandermondeInt xs:=Int.toNat_of_nonneg hv_pos.le;have hq_pos:0 < q:=by omega
 have hqR:(q:E)=(vandermondeInt xs:E):=by exact_mod_cast hq_eq
 have hQ':Polynomial.C (q:E)*P=Q.map (Int.castRingHom E):=by rw [hqR,hP];exact hQ
 have hhas:HasIntDenom P:=⟨q,hq_pos,Q,hQ'⟩;have hle:polyDenom P<=q:=polyDenom_le hq_pos ⟨Q,hQ'⟩;have hv_le:vandermondeInt xs<=(xs 3-xs 0)^6:=by simpa using vandermondeInt_le_pow xs hmono
 refine ⟨hhas,?_⟩;have h1:(polyDenom P:E)<=(q:E):=by exact_mod_cast hle
 have h2:(q:E)<=((xs 3-xs 0:ℤ):E)^6:=by rw [hqR];exact_mod_cast hv_le
 exact h1.trans h2
lemma minor_arc_sep_4 {f:E->E} {M:ℕ} {δ lam c:E}
  (hδ:0 < δ) (hlam:0 < lam) (hc:1<=c)
  (hcd:∀ t∈Icc (M:E) (2*(M:E)),ContDiffAt E 4 f t)
  (hder:∀ t∈Icc (M:E) (2*(M:E)),|iteratedDeriv 4 f t| ≤ c*lam)
  (xs:Fin 5->ℤ) (hmono:StrictMono xs)
  (hmem:∀ i,xs i∈nearCurveSet f M δ)
  (hnotcubic:dividedDiff (fun i=>(xs i:E)) (fun i=>(round (f (xs i:E)):E))≠0) :
  min ((c*lam)^(-(1/10:E))) (δ^(-(1/6:E))/2)<=((xs 4-xs 0:ℤ):E):=by
 let ms:Fin 5->ℤ:=fun i=>round (f (xs i:E));let D:ℤ:=vandermondeInt xs;have hD_pos:0 < D:=vandermondeInt_pos xs hmono;have hDR_pos:(0:E) < (D:E):=by exact_mod_cast hD_pos
 obtain ⟨A,hA⟩:=vandermondeInt_mul_dividedDiff_int xs ms hmono
 have hA_ne:A≠0:=by
  intro h0;rw [h0,Int.cast_zero] at hA;exact hnotcubic ((mul_eq_zero.mp hA.symm).resolve_left hDR_pos.ne')
 have hA_ge1:(1:E) ≤ |(A:E)|:=by
  have:(1:ℤ) ≤ |A|:=Int.one_le_abs hA_ne
  exact_mod_cast this
 have hmonoR:StrictMono (fun i=>(xs i:E)):=fun i j h=>Int.cast_lt.mpr (hmono h)
 have hsub_M:Icc (xs 0:E) (xs 4:E)⊆Icc (M:E) (2*(M:E)):=by
  intro t ht;have h0:=Finset.mem_Icc.mp (mem_filter.mp (hmem 0)).1;have h4:=Finset.mem_Icc.mp (mem_filter.mp (hmem 4)).1;exact ⟨le_trans (by exact_mod_cast h0.1) ht.1,le_trans ht.2 (by exact_mod_cast h4.2)⟩
 have hcd_xs:ContDiffOn E 4 f (Icc (xs 0:E) (xs 4:E)) := fun t ht=>(hcd t (hsub_M ht)).contDiffWithinAt;obtain ⟨ξ,hξ_ioo,hξ_eq⟩ :=exists_dividedDiff_eq_iteratedDeriv (by decide:1<=4) (fun i=>(xs i:E)) f hmonoR hcd_xs
 have hξ_M:ξ∈Icc (M:E) (2*(M:E)):=hsub_M (Ioo_subset_Icc_self hξ_ioo);let err:Fin 5->E:=fun i=>f (xs i:E)-(ms i:E);have herr_lt:∀ i,|err i| < δ:=fun i=>(mem_filter.mp (hmem i)).2
 have hdd_split:dividedDiff (fun i=>(xs i:E)) (fun i=>(ms i:E)) = dividedDiff (fun i=>(xs i:E)) (f ∘ (fun i=>(xs i:E))) -
   dividedDiff (fun i=>(xs i:E)) err:=by
  unfold dividedDiff;rw [← Finset.sum_sub_distrib];apply sum_congr rfl;intro j _;dsimp [err];ring
 have h24A:24*(A:E)=(D:E)*iteratedDeriv 4 f ξ -
   24*((D:E)*dividedDiff (fun i=>(xs i:E)) err):=by
  rw [hA,hdd_split,hξ_eq];have hfac:((4:ℕ).factorial:E)=24:=by norm_num [Nat.factorial]
  rw [hfac];ring
 let L:E:=((xs 4-xs 0:ℤ):E)
 have hL_pos:0 < L:=by
  have:xs 0 < xs 4:=hmono (by decide:(0:Fin 5) < 4)
  dsimp [L];exact_mod_cast sub_pos.mpr this
 have hD_le:(D:E)<=L^10:=by
  have:=vandermondeInt_le_pow xs hmono
  dsimp [D,L];exact_mod_cast this
 have herr_sum:|(D:E)*dividedDiff (fun i=>(xs i:E)) err| ≤ 5*δ*L^6:=by
  unfold dividedDiff;rw [Finset.mul_sum]
  calc
   |∑ j:Fin 5,(D:E)*(err j/∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E)))|
     ≤ ∑ j:Fin 5,|(D:E)*(err j/∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E)))| :=
    Finset.abs_sum_le_sum_abs _ _
   _ <= ∑ _j:Fin 5,(δ*L^6):=by
    apply sum_le_sum;intro j _;obtain ⟨s,hs_or,hs_eq⟩:=vandermondeInt_eq_mul_erase xs j
    have hne:(∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E)))≠0:=by
     apply Finset.prod_ne_zero_iff.mpr;intro i hi
     have:xs j≠xs i:=fun h=>(Finset.ne_of_mem_erase hi) (hmono.injective h).symm
     exact sub_ne_zero.mpr (by exact_mod_cast this)
    have hcast:(D:E)=(s:E)*(∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E))) * (vandermondeErase xs j:E):=by dsimp [D];rw [hs_eq];push_cast;rfl
    have hterm_eq:(D:E)*(err j/∏ i∈Finset.univ.erase j,((xs j:E)-(xs i:E))) = (s:E)*err j*(vandermondeErase xs j:E):=by rw [hcast];field_simp [hne]
    rw [hterm_eq,abs_mul,abs_mul];have hs1:|(s:E)| = 1:=by rcases hs_or with rfl | rfl <;> norm_num
    have he_pos:(0:E)<=(vandermondeErase xs j:E):=by exact_mod_cast (vandermondeErase_pos xs hmono j).le
    have he_le:(vandermondeErase xs j:E)<=L^6:=by
     have:=vandermondeErase_le_pow xs hmono j
     dsimp [L];exact_mod_cast this
    rw [hs1,one_mul,abs_of_nonneg he_pos];exact mul_le_mul (herr_lt j).le he_le he_pos hδ.le
   _ = 5*δ*L^6:=by simp;ring
 have h24_le:(24:E)<=c*lam*L^10+120*δ*L^6:=by
  have h1:(24:E) ≤ |24*(A:E)|:=by rw [abs_mul,abs_of_pos (by norm_num:(0:E) < 24)];linarith
  have h2:|24*(A:E)| ≤ |(D:E)*iteratedDeriv 4 f ξ| + 24 * |(D:E)*dividedDiff (fun i=>(xs i:E)) err|:=by
   rw [h24A]
   have:=abs_sub ((D:E)*iteratedDeriv 4 f ξ)
    (24*((D:E)*dividedDiff (fun i=>(xs i:E)) err))
   rw [abs_mul (24:E),abs_of_pos (by norm_num:(0:E) < 24)] at this;exact this
  have h3:|(D:E)*iteratedDeriv 4 f ξ| ≤ c*lam*L^10:=by
   rw [abs_mul,abs_of_pos hDR_pos]
   calc
    (D:E) * |iteratedDeriv 4 f ξ| ≤ L^10*(c*lam) :=mul_le_mul hD_le (hder ξ hξ_M) (abs_nonneg _) (pow_nonneg hL_pos.le 10)
    _ = c*lam*L^10:=by ring
  linarith
 have hcl_pos:0 < c*lam:=by positivity
 by_cases hcase:(12:E)<=c*lam*L^10
 ·
  apply le_trans (min_le_left _ _);have hpow:(c*lam)⁻¹<=L^10:=by rw [inv_le_iff_one_le_mul₀' hcl_pos];linarith
  have hrp:=rpow_le_rpow (by positivity) hpow (by norm_num:(0:E)<=1/10);rw [Real.inv_rpow hcl_pos.le,← rpow_neg hcl_pos.le] at hrp;rw [← rpow_natCast L 10,← rpow_mul hL_pos.le] at hrp;norm_num at hrp;exact hrp
 ·
  push Not at hcase
  apply le_trans (min_le_right _ _);have h12:(12:E)<=120*δ*L^6:=by linarith
  have hpow:(64*δ)⁻¹<=L^6:=by rw [inv_le_iff_one_le_mul₀' (by positivity)];linarith
  have hrp:=rpow_le_rpow (by positivity) hpow (by norm_num:(0:E)<=1/6)
  have h64:((64*δ)⁻¹)^(1/6:E)=δ^(-(1/6:E))/2:=by
   rw [Real.inv_rpow (by positivity),mul_rpow (by norm_num) hδ.le,mul_inv,← rpow_neg hδ.le]
   have h26:(64:E)^(1/6:E)=2:=by
    have h64_eq:(64:E)=(2:E)^(6:E):=by norm_num
    rw [h64_eq,← rpow_mul (by norm_num:(0:E)<=2)];norm_num
   rw [h26];ring
  rw [h64,← rpow_natCast L 6,← rpow_mul hL_pos.le] at hrp;norm_num at hrp;exact hrp
lemma cubic_breaks_card_le_three {f:E->E} {M:ℕ} {δ lam:E}
  (hlam:0 < lam)
  (hcd:∀ t∈Icc (M:E) (2*(M:E)),ContDiffAt E 4 f t)
  (hder_lo:∀ t∈Icc (M:E) (2*(M:E)),lam ≤ |iteratedDeriv 4 f t|)
  {P:Polynomial E} (hdeg:P.natDegree<=3)
  {r:ℕ} (b:Fin r->ℤ) (hb_mono:StrictMono b)
  (hb_mem:∀ i,b i∈nearCurveSet f M δ)
  (hb_P:∀ i,P.eval (b i:E)=(round (f (b i:E)):E)) :
  ((Finset.univ:Finset (Fin (r-1))).filter (fun (i:Fin (r-1)) =>
   ∃ x∈Ioo (b ⟨i.1,by omega⟩:E) (b ⟨i.1+1,by omega⟩:E),δ < |f x-P.eval x|)).card<=3:=by
 classical
 let B:=(Finset.univ:Finset (Fin (r-1))).filter (fun (i:Fin (r-1)) =>
  ∃ x∈Ioo (b ⟨i.1,by omega⟩:E) (b ⟨i.1+1,by omega⟩:E),δ < |f x-P.eval x|)
 change B.card<=3
 by_contra hgt
 have hge4:4<=B.card:=by omega
 let emb:=B.orderEmbOfFin rfl;let idx:Fin 4->Fin (r-1):=fun m=>emb ⟨m.1,lt_of_lt_of_le m.2 hge4⟩;have hidx_mono:StrictMono idx:=fun i j hij=>emb.strictMono (by exact hij);have hidx_mem:∀ m:Fin 4,idx m∈B:=fun m=>Finset.orderEmbOfFin_mem B rfl _
 let g:E->E:=fun x=>f x-P.eval x
 have hcd_g:∀ t∈Icc (M:E) (2*(M:E)),ContDiffAt E 4 g t:=fun t ht =>
  (hcd t ht).sub (poly_contDiff P 4).contDiffAt
 have hex_stat:∀ m:Fin 4,∃ y∈Ioo (b ⟨(idx m).1,by omega⟩:E) (b ⟨(idx m).1+1,by omega⟩:E),deriv g y=0:=by
  intro m;let i0:Fin r:=⟨(idx m).1,by omega⟩;let i1:Fin r:=⟨(idx m).1+1,by omega⟩;have hlt:(b i0:E) < (b i1:E):=by exact_mod_cast hb_mono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self (idx m).1))
  have hsub:Icc (b i0:E) (b i1:E)⊆Icc (M:E) (2*(M:E)):=by
   intro t ht;have h0:=Finset.mem_Icc.mp (mem_filter.mp (hb_mem i0)).1;have h1:=Finset.mem_Icc.mp (mem_filter.mp (hb_mem i1)).1;exact ⟨le_trans (by exact_mod_cast h0.1) ht.1,le_trans ht.2 (by exact_mod_cast h1.2)⟩
  have hcont:ContinuousOn g (Icc (b i0:E) (b i1:E)) := fun t ht=>(hcd_g t (hsub ht)).continuousAt.continuousWithinAt;have hg0:|g (b i0:E)| < δ:=by dsimp [g];rw [hb_P i0];exact (mem_filter.mp (hb_mem i0)).2
  have hg1:|g (b i1:E)| < δ:=by dsimp [g];rw [hb_P i1];exact (mem_filter.mp (hb_mem i1)).2
  obtain ⟨x0,hx0_ioo,hx0_gt⟩:=(mem_filter.mp (hidx_mem m)).2;rcases lt_or_ge (g x0) 0 with hneg | hnn
  ·
   obtain ⟨y,hy_icc,hy_min⟩:=isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hlt.le) hcont
   have hy_lt:g y < -δ:=by
    have hle:g y<=g x0:=hy_min (Ioo_subset_Icc_self hx0_ioo);have hgx:-g x0 > δ:=by rwa [abs_of_neg hneg] at hx0_gt
    linarith
   have hy_ne0:y≠(b i0:E):=by intro he;rw [he] at hy_lt;linarith [(abs_lt.mp hg0).1]
   have hy_ne1:y≠(b i1:E):=by intro he;rw [he] at hy_lt;linarith [(abs_lt.mp hg1).1]
   have hy_ioo:y∈Ioo (b i0:E) (b i1:E) :=⟨lt_of_le_of_ne hy_icc.1 hy_ne0.symm,lt_of_le_of_ne hy_icc.2 hy_ne1⟩;have hloc:IsLocalMin g y:=hy_min.isLocalMin (Icc_mem_nhds hy_ioo.1 hy_ioo.2);exact ⟨y,hy_ioo,hloc.deriv_eq_zero⟩
  ·
   obtain ⟨y,hy_icc,hy_max⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hlt.le) hcont
   have hy_gt:δ < g y:=by
    have hle:g x0<=g y:=hy_max (Ioo_subset_Icc_self hx0_ioo);have hgx:g x0 > δ:=by rwa [abs_of_nonneg hnn] at hx0_gt
    linarith
   have hy_ne0:y≠(b i0:E):=by intro he;rw [he] at hy_gt;linarith [(abs_lt.mp hg0).2]
   have hy_ne1:y≠(b i1:E):=by intro he;rw [he] at hy_gt;linarith [(abs_lt.mp hg1).2]
   have hy_ioo:y∈Ioo (b i0:E) (b i1:E) :=⟨lt_of_le_of_ne hy_icc.1 hy_ne0.symm,lt_of_le_of_ne hy_icc.2 hy_ne1⟩;have hloc:IsLocalMax g y:=hy_max.isLocalMax (Icc_mem_nhds hy_ioo.1 hy_ioo.2);exact ⟨y,hy_ioo,hloc.deriv_eq_zero⟩
 choose ys hys_ioo hys_eq using hex_stat
 have hys_mono:StrictMono ys:=by
  intro m1 m2 hlt;have hidx_lt:(idx m1).1 < (idx m2).1:=hidx_mono hlt;have h1:ys m1 < (b ⟨(idx m1).1+1,by omega⟩:E):=(hys_ioo m1).2;have h2:(b ⟨(idx m2).1,by omega⟩:E) < ys m2:=(hys_ioo m2).1
  have hle:(b ⟨(idx m1).1+1,by omega⟩:E)<=(b ⟨(idx m2).1,by omega⟩:E):=by
   have hf:(⟨(idx m1).1+1,by omega⟩:Fin r)<=⟨(idx m2).1,by omega⟩:=by show (idx m1).1+1<=(idx m2).1;omega
   exact_mod_cast hb_mono.monotone hf
  linarith
 have hsub_y:Icc (ys 0) (ys 3)⊆Icc (M:E) (2*(M:E)):=by
  intro t ht;have hlo1:(M:E)<=(b ⟨(idx 0).1,by omega⟩:E):=by exact_mod_cast (Finset.mem_Icc.mp (mem_filter.mp (hb_mem _)).1).1
  have hhi1:(b ⟨(idx 3).1+1,by omega⟩:E)<=2*(M:E):=by exact_mod_cast (Finset.mem_Icc.mp (mem_filter.mp (hb_mem _)).1).2
  exact ⟨le_trans (hlo1.trans (hys_ioo 0).1.le) ht.1,le_trans ht.2 ((hys_ioo 3).2.le.trans hhi1)⟩
 have hcd_dg:ContDiffOn E 3 (deriv g) (Icc (ys 0) (ys 3)):=by
  intro t ht;have h4:ContDiffAt E 4 g t:=hcd_g t (hsub_y ht);exact (contDiffAt_deriv_of_succ h4).contDiffWithinAt
 obtain ⟨ξ,hξ_mem,_,hξ_eq⟩ :=exists_iteratedDeriv_eq_zero_of_zeros 3 ys (deriv g) hys_mono hcd_dg hys_eq;have hξ_M:ξ∈Icc (M:E) (2*(M:E)):=hsub_y hξ_mem;have h4_eq:iteratedDeriv 4 g ξ=0:=by rw [iteratedDeriv_succ'];exact hξ_eq
 have hsub_4:=iteratedDeriv_sub_smooth (hcd ξ hξ_M) (poly_contDiff P 4).contDiffAt
 have hP4:iteratedDeriv 4 (fun t=>P.eval t) ξ=0:=by
  rw [iteratedDeriv_poly_eval_eq P 4 (by omega) ξ];have hc4:P.coeff 4=0:=Polynomial.coeff_eq_zero_of_natDegree_lt (by omega);rw [hc4,mul_zero]
 have hf4_zero:iteratedDeriv 4 f ξ=0:=by
  change iteratedDeriv 4 (fun t=>f t-P.eval t) ξ=0 at h4_eq;rw [hsub_4,hP4,sub_zero] at h4_eq;exact h4_eq
 have hlo:=hder_lo ξ hξ_M;rw [hf4_zero,abs_zero] at hlo;linarith
structure ProperArc (f:E->E) (M:ℕ) (δ:E) where
 pts:Finset ℤ
 poly:Polynomial E
 hsub:pts⊆nearCurveSet f M δ
 hdeg:poly.natDegree<=3
 hcard:5<=pts.card
 heval:∀ n∈pts,poly.eval (n:E)=(round (f (n:E)):E)
 hclose:∀ x∈Icc ((pts.min' (Finset.card_pos.mp (by omega)):ℤ):E)
   ((pts.max' (Finset.card_pos.mp (by omega)):ℤ):E),
  |f x-poly.eval x| ≤ δ
lemma ProperArc.nonempty {f M δ} (A:ProperArc f M δ):A.pts.Nonempty :=Finset.card_pos.mp (by have:=A.hcard;omega)
noncomputable def ProperArc.lo {f M δ} (A:ProperArc f M δ):ℤ :=A.pts.min' A.nonempty
noncomputable def ProperArc.hi {f M δ} (A:ProperArc f M δ):ℤ :=A.pts.max' A.nonempty
noncomputable def ProperArc.len {f M δ} (A:ProperArc f M δ):E :=((A.hi-A.lo:ℤ):E)
lemma ProperArc.len_ge_four {f M δ} (A:ProperArc f M δ):(4:E)<=A.len:=by
 have hsub:A.pts⊆Finset.Icc A.lo A.hi:=fun n hn =>
  Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hn,Finset.le_max' _ _ hn⟩
 have hc:=Finset.card_le_card hsub;rw [Int.card_Icc] at hc;have h5:=A.hcard;dsimp [ProperArc.len]
 have:(4:ℤ)<=A.hi-A.lo:=by omega
 exact_mod_cast this
lemma ProperArc.hasIntDenom {f M δ} (A:ProperArc f M δ):HasIntDenom A.poly:=by
 let emb:=A.pts.orderEmbOfFin rfl;let xs:Fin 4->ℤ:=fun i=>emb ⟨i.1,lt_of_lt_of_le i.2 (by have:=A.hcard;omega)⟩;have hmono:StrictMono xs:=fun i j h=>emb.strictMono h;let ms:Fin 4->ℤ:=fun i=>round (f (xs i:E))
 have hev:∀ i,A.poly.eval (xs i:E)=(ms i:E):=fun i =>
  A.heval (xs i) (Finset.orderEmbOfFin_mem A.pts rfl _)
 exact (hasIntDenom_and_le_of_interp4 A.hdeg xs ms hmono hev).1
noncomputable def ProperArc.denom {f M δ} (A:ProperArc f M δ):ℕ :=polyDenom A.poly
lemma ProperArc.denom_pos {f M δ} (A:ProperArc f M δ):0 < A.denom :=polyDenom_pos A.hasIntDenom
lemma ProperArc.len_le {f:E->E} {M:ℕ} {δ lam:E}
  (hδ:0 < δ) (hlam:0 < lam)
  (hcd:∀ t∈Icc (M:E) (2*(M:E)),ContDiffAt E 4 f t)
  (hder_lo:∀ t∈Icc (M:E) (2*(M:E)),lam ≤ |iteratedDeriv 4 f t|)
  (A:ProperArc f M δ) :
  A.len<=8*(δ/lam)^(1/4:E):=by
 have hL_pos:0 < A.len:=lt_of_lt_of_le (by norm_num) A.len_ge_four;let α:Fin 5->E:=fun j=>(A.lo:E)+(j:E)*(A.len/4)
 have hα_mono:StrictMono α:=by
  intro i j hij;dsimp [α];have hijR:(i:E) < (j:E):=by exact_mod_cast hij
  nlinarith
 have hα_0:α 0=(A.lo:E):=by simp [α]
 have hα_4:α 4=(A.hi:E):=by dsimp [α,ProperArc.len];push_cast;ring
 have hα_mem:∀ j:Fin 5,α j∈Icc (A.lo:E) (A.hi:E):=by
  intro j;rw [← hα_0,← hα_4];exact ⟨hα_mono.monotone (Fin.zero_le j),hα_mono.monotone (Fin.le_last j)⟩
 have hsub_M:Icc (α 0) (α 4)⊆Icc (M:E) (2*(M:E)):=by
  rw [hα_0,hα_4];intro t ht;have hlo_m:=Finset.mem_Icc.mp (mem_filter.mp (A.hsub (Finset.min'_mem A.pts A.nonempty))).1;have hhi_m:=Finset.mem_Icc.mp (mem_filter.mp (A.hsub (Finset.max'_mem A.pts A.nonempty))).1
  exact ⟨le_trans (by exact_mod_cast hlo_m.1) ht.1,le_trans ht.2 (by exact_mod_cast hhi_m.2)⟩
 let g:E->E:=fun t=>f t-A.poly.eval t
 have hcd_g:ContDiffOn E 4 g (Icc (α 0) (α 4)):=fun t ht =>
  ((hcd t (hsub_M ht)).sub (poly_contDiff A.poly 4).contDiffAt).contDiffWithinAt
 obtain ⟨ξ,hξ_ioo,hξ_eq⟩ :=exists_dividedDiff_eq_iteratedDeriv (by decide:1<=4) α g hα_mono hcd_g;have hξ_M:ξ∈Icc (M:E) (2*(M:E)):=hsub_M (Ioo_subset_Icc_self hξ_ioo)
 have hder4_g:iteratedDeriv 4 g ξ=iteratedDeriv 4 f ξ:=by
  have hsub:=iteratedDeriv_sub_smooth (hcd ξ hξ_M) (poly_contDiff A.poly 4).contDiffAt
  have hP4:iteratedDeriv 4 (fun t=>A.poly.eval t) ξ=0:=by
   rw [iteratedDeriv_poly_eval_eq A.poly 4 (by have:=A.hdeg;omega) ξ];have hc4:A.poly.coeff 4=0:=Polynomial.coeff_eq_zero_of_natDegree_lt (by have:=A.hdeg;omega);rw [hc4,mul_zero]
  change iteratedDeriv 4 (fun t=>f t-A.poly.eval t) ξ=iteratedDeriv 4 f ξ;rw [hsub,hP4,sub_zero]
 have hlo_dd:lam/24 ≤ |dividedDiff α (g ∘ α)|:=by
  rw [hξ_eq,hder4_g];have hfac:((4:ℕ).factorial:E)=24:=by norm_num [Nat.factorial]
  rw [hfac,abs_div,abs_of_pos (by norm_num:(0:E) < 24)];exact div_le_div_of_nonneg_right (hder_lo ξ hξ_M) (by norm_num)
 have hup_dd:|dividedDiff α (g ∘ α)| ≤ (8/A.len)^4*δ/24:=by
  unfold dividedDiff
  have hprod_eq:∀ j:Fin 5,
    |∏ i∈Finset.univ.erase j,(α j-α i)| = (A.len/4)^4*((j.1.factorial*(4-j.1).factorial:ℕ):E):=by
   intro j
   fin_cases j
   ·
    change |∏ i∈(Finset.univ:Finset (Fin 5)).erase 0,(α 0-α i)| = _;have he:(Finset.univ:Finset (Fin 5)).erase 0=({1,2,3,4}:Finset (Fin 5)):=by decide
    rw [he];simp only [Finset.prod_insert,Finset.prod_singleton,Finset.mem_insert,Finset.mem_singleton,Fin.reduceEq,or_self,not_false_eq_true,α,Nat.factorial]
    have:|((A.lo:E)+↑(0:Fin 5)*(A.len/4)-((A.lo:E)+↑(1:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(0:Fin 5)*(A.len/4)-((A.lo:E)+↑(2:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(0:Fin 5)*(A.len/4)-((A.lo:E)+↑(3:Fin 5)*(A.len/4))) * ((A.lo:E)+↑(0:Fin 5)*(A.len/4)-((A.lo:E)+↑(4:Fin 5)*(A.len/4)))))| =
      |24*(A.len/4)^4|:=by congr 1;norm_num;ring
    rw [this,abs_of_pos (by positivity)];push_cast;ring
   ·
    change |∏ i∈(Finset.univ:Finset (Fin 5)).erase 1,(α 1-α i)| = _;have he:(Finset.univ:Finset (Fin 5)).erase 1=({0,2,3,4}:Finset (Fin 5)):=by decide
    rw [he];simp only [Finset.prod_insert,Finset.prod_singleton,Finset.mem_insert,Finset.mem_singleton,Fin.reduceEq,or_self,not_false_eq_true,α,Nat.factorial]
    have:|((A.lo:E)+↑(1:Fin 5)*(A.len/4)-((A.lo:E)+↑(0:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(1:Fin 5)*(A.len/4)-((A.lo:E)+↑(2:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(1:Fin 5)*(A.len/4)-((A.lo:E)+↑(3:Fin 5)*(A.len/4))) * ((A.lo:E)+↑(1:Fin 5)*(A.len/4)-((A.lo:E)+↑(4:Fin 5)*(A.len/4)))))| =
      |-(6*(A.len/4)^4)|:=by congr 1;norm_num;ring
    rw [this,abs_neg,abs_of_pos (by positivity)];push_cast;ring
   ·
    change |∏ i∈(Finset.univ:Finset (Fin 5)).erase 2,(α 2-α i)| = _;have he:(Finset.univ:Finset (Fin 5)).erase 2=({0,1,3,4}:Finset (Fin 5)):=by decide
    rw [he];simp only [Finset.prod_insert,Finset.prod_singleton,Finset.mem_insert,Finset.mem_singleton,Fin.reduceEq,or_self,not_false_eq_true,α,Nat.factorial]
    have:|((A.lo:E)+↑(2:Fin 5)*(A.len/4)-((A.lo:E)+↑(0:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(2:Fin 5)*(A.len/4)-((A.lo:E)+↑(1:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(2:Fin 5)*(A.len/4)-((A.lo:E)+↑(3:Fin 5)*(A.len/4))) * ((A.lo:E)+↑(2:Fin 5)*(A.len/4)-((A.lo:E)+↑(4:Fin 5)*(A.len/4)))))| =
      |4*(A.len/4)^4|:=by congr 1;norm_num;ring
    rw [this,abs_of_pos (by positivity)];push_cast;ring
   ·
    change |∏ i∈(Finset.univ:Finset (Fin 5)).erase 3,(α 3-α i)| = _;have he:(Finset.univ:Finset (Fin 5)).erase 3=({0,1,2,4}:Finset (Fin 5)):=by decide
    rw [he];simp only [Finset.prod_insert,Finset.prod_singleton,Finset.mem_insert,Finset.mem_singleton,Fin.reduceEq,or_self,not_false_eq_true,α,Nat.factorial]
    have:|((A.lo:E)+↑(3:Fin 5)*(A.len/4)-((A.lo:E)+↑(0:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(3:Fin 5)*(A.len/4)-((A.lo:E)+↑(1:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(3:Fin 5)*(A.len/4)-((A.lo:E)+↑(2:Fin 5)*(A.len/4))) * ((A.lo:E)+↑(3:Fin 5)*(A.len/4)-((A.lo:E)+↑(4:Fin 5)*(A.len/4)))))| =
      |-(6*(A.len/4)^4)|:=by congr 1;norm_num;ring
    rw [this,abs_neg,abs_of_pos (by positivity)];push_cast;ring
   ·
    change |∏ i∈(Finset.univ:Finset (Fin 5)).erase 4,(α 4-α i)| = _;have he:(Finset.univ:Finset (Fin 5)).erase 4=({0,1,2,3}:Finset (Fin 5)):=by decide
    rw [he];simp only [Finset.prod_insert,Finset.prod_singleton,Finset.mem_insert,Finset.mem_singleton,Fin.reduceEq,or_self,not_false_eq_true,α,Nat.factorial]
    have:|((A.lo:E)+↑(4:Fin 5)*(A.len/4)-((A.lo:E)+↑(0:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(4:Fin 5)*(A.len/4)-((A.lo:E)+↑(1:Fin 5)*(A.len/4))) * (((A.lo:E)+↑(4:Fin 5)*(A.len/4)-((A.lo:E)+↑(2:Fin 5)*(A.len/4))) * ((A.lo:E)+↑(4:Fin 5)*(A.len/4)-((A.lo:E)+↑(3:Fin 5)*(A.len/4)))))| =
      |24*(A.len/4)^4|:=by congr 1;norm_num;ring
    rw [this,abs_of_pos (by positivity)];push_cast;ring
  calc
   |∑ j:Fin 5,g (α j)/∏ i∈Finset.univ.erase j,(α j-α i)|
     ≤ ∑ j:Fin 5,|g (α j)/∏ i∈Finset.univ.erase j,(α j-α i)| :=
    Finset.abs_sum_le_sum_abs _ _
   _ <= ∑ j:Fin 5,δ/((A.len/4)^4*((j.1.factorial*(4-j.1).factorial:ℕ):E)):=by
    apply sum_le_sum;intro j _;rw [abs_div,hprod_eq j];have hg_le:|g (α j)| ≤ δ:=A.hclose (α j) (hα_mem j);exact div_le_div_of_nonneg_right hg_le (by positivity)
   _ = (8/A.len)^4*δ/24:=by
    simp [Fin.sum_univ_five,Nat.factorial];field_simp [hL_pos.ne'];ring
 have hpow4:A.len^4<=8^4*(δ/lam):=by
  have h1:lam/24<=(8/A.len)^4*δ/24:=hlo_dd.trans hup_dd
  have h2:lam<=8^4*δ/A.len^4:=by
   have:(8/A.len)^4*δ=8^4*δ/A.len^4:=by ring
   linarith
  rw [le_div_iff₀ (pow_pos hL_pos 4)] at h2;rw [← mul_div_assoc,le_div_iff₀ hlam];linarith
 have hrp:=rpow_le_rpow (pow_nonneg hL_pos.le 4) hpow4 (by norm_num:(0:E)<=1/4);rw [← rpow_natCast A.len 4,← rpow_mul hL_pos.le] at hrp;rw [mul_rpow (by positivity) (by positivity)] at hrp
 have h8:((8:E)^4)^(1/4:E)=8:=by
  rw [← rpow_natCast (8:E) 4,← rpow_mul (by norm_num:(0:E)<=8)];norm_num
 rw [h8] at hrp;norm_num at hrp;exact hrp
lemma ProperArc.card_le {f:E->E} {M:ℕ} {δ:E} (A:ProperArc f M δ) :
  (A.pts.card:E)<=8*A.len*(A.denom:E)^(-(1/6:E)):=by
 let emb:=A.pts.orderEmbOfFin rfl;let k:=A.pts.card;have hq_pos:(0:E) < (A.denom:E):=by exact_mod_cast A.denom_pos
 have hstep:∀ i:ℕ,(hi:i+3 < k) → (A.denom:E)^(1/6:E)<=((emb ⟨i+3,hi⟩-emb ⟨i,by omega⟩:ℤ):E):=by
  intro i hi;let xs:Fin 4->ℤ:=fun j=>emb ⟨i+j.1,by omega⟩;have hmono:StrictMono xs:=fun a b hab=>emb.strictMono (by show i+a.1 < i+b.1;omega);let ms:Fin 4->ℤ:=fun j=>round (f (xs j:E))
  have hev:∀ j,A.poly.eval (xs j:E)=(ms j:E):=fun j =>
   A.heval (xs j) (Finset.orderEmbOfFin_mem A.pts rfl _)
  have hle:=(hasIntDenom_and_le_of_interp4 A.hdeg xs ms hmono hev).2
  have hpos_d:(0:E)<=((xs 3-xs 0:ℤ):E):=by
   have:xs 0 < xs 3:=hmono (by decide:(0:Fin 4) < 3)
   exact_mod_cast (sub_pos.mpr this).le
  have hrp:=rpow_le_rpow hq_pos.le hle (by norm_num:(0:E)<=1/6);rw [← rpow_natCast _ 6,← rpow_mul hpos_d] at hrp;norm_num at hrp;simpa [xs,ProperArc.denom] using hrp
 let m:ℕ:=(k-1)/3;have hm_pos:1<=m:=by have:=A.hcard;dsimp [m,k];omega
 have hsum_le:(m:E)*(A.denom:E)^(1/6:E)<=A.len:=by
  let term:ℕ->E:=fun j =>
   if hj:3*(j+1) < k then
    ((emb ⟨3*(j+1),hj⟩-emb ⟨3*j,by omega⟩:ℤ):E)
   else 0
  have htele:∀ n:ℕ,(hn:n<=m) → ∑ j∈Finset.range n,term j = ((emb ⟨3*n,by dsimp [m,k] at *;omega⟩-emb ⟨0,by have:=A.hcard;omega⟩:ℤ):E):=by
   intro n hn
   induction n with
   | zero=>simp
   | succ n ih =>
    rw [sum_range_succ,ih (by omega)];have hlt:3*(n+1) < k:=by dsimp [m,k] at *;omega
    simp only [term,hlt,↓reduceDIte];push_cast;ring
  have hsum_ge:(m:E)*(A.denom:E)^(1/6:E)<=∑ j∈Finset.range m,term j:=by
   calc
    (m:E)*(A.denom:E)^(1/6:E)=∑ _j∈Finset.range m,(A.denom:E)^(1/6:E):=by simp
    _ <= ∑ j∈Finset.range m,term j:=by
     apply sum_le_sum;intro j hj;have hj':=Finset.mem_range.mp hj;have hlt:3*(j+1) < k:=by dsimp [m,k] at *;omega
     simp only [term,hlt,↓reduceDIte];have h:=hstep (3*j) (by omega);simpa [Nat.mul_add,Nat.add_assoc] using h
  have hle_len:((emb ⟨3*m,by dsimp [m,k];omega⟩ -
    emb ⟨0,by have:=A.hcard;omega⟩:ℤ):E)<=A.len:=by
   have h1:A.lo<=emb ⟨0,by have:=A.hcard;omega⟩ :=Finset.min'_le _ _ (Finset.orderEmbOfFin_mem A.pts rfl _);have h2:emb ⟨3*m,by dsimp [m,k];omega⟩<=A.hi :=Finset.le_max' _ _ (Finset.orderEmbOfFin_mem A.pts rfl _);dsimp [ProperArc.len]
   have:emb ⟨3*m,by dsimp [m,k];omega⟩-emb ⟨0,by have:=A.hcard;omega⟩<=A.hi-A.lo:=by omega
   exact_mod_cast this
  exact hsum_ge.trans ((htele m le_rfl).le.trans hle_len)
 have hk_le:(k:E)<=8*(m:E):=by
  have:k<=8*m:=by dsimp [m,k];omega
  exact_mod_cast this
 have hqp:(0:E) < (A.denom:E)^(1/6:E):=rpow_pos_of_pos hq_pos _;rw [rpow_neg hq_pos.le,← div_eq_mul_inv,le_div_iff₀ hqp]
 calc
  (A.pts.card:E)*(A.denom:E)^(1/6:E)
    ≤ (8*(m:E))*(A.denom:E)^(1/6:E) :=
   mul_le_mul_of_nonneg_right hk_le hqp.le
  _ = 8*((m:E)*(A.denom:E)^(1/6:E)):=by ring
  _ <= 8*A.len:=mul_le_mul_of_nonneg_left hsum_le (by norm_num)
set_option maxHeartbeats 400000 in
lemma ProperArc.dist_gt_of_not_on_poly {f:E->E} {M:ℕ} {δ lam c:E}
  (hδ:0 < δ) (hlam:0 < lam) (hc:1<=c)
  (hcd:∀ t∈Icc (M:E) (2*(M:E)),ContDiffAt E 4 f t)
  (hder_lo:∀ t∈Icc (M:E) (2*(M:E)),lam ≤ |iteratedDeriv 4 f t|)
  (hder_hi:∀ t∈Icc (M:E) (2*(M:E)),|iteratedDeriv 4 f t| ≤ c*lam)
  (A:ProperArc f M δ)
  (hq_small:(10^9*c)*(A.denom:E)*δ<=1)
  {n n0:ℤ} (hn:n∈nearCurveSet f M δ) (hn0:n0∈A.pts)
  (hnot:A.poly.eval (n:E)≠(round (f (n:E)):E)) :
  A.len*((10^9*c)*(A.denom:E)*δ)^(-(1/4:E)) < |(n:E)-(n0:E)|:=by
 have hL_pos:0 < A.len:=lt_of_lt_of_le (by norm_num) A.len_ge_four;have hq_pos:(0:E) < (A.denom:E):=by exact_mod_cast A.denom_pos
 have ha4_pos:(0:E) < 10^9*c:=by positivity
 let g:E->E:=fun t=>f t-A.poly.eval t
 have hcd_g:∀ t∈Icc (M:E) (2*(M:E)),ContDiffAt E 4 g t:=fun t ht =>
  (hcd t ht).sub (poly_contDiff A.poly 4).contDiffAt
 have hder4_g:∀ t∈Icc (M:E) (2*(M:E)),|iteratedDeriv 4 g t| ≤ c*lam:=by
  intro t ht;have hsub:=iteratedDeriv_sub_smooth (hcd t ht) (poly_contDiff A.poly 4).contDiffAt
  have hP4:iteratedDeriv 4 (fun s=>A.poly.eval s) t=0:=by
   rw [iteratedDeriv_poly_eval_eq A.poly 4 (by have:=A.hdeg;omega) t];have hc4:A.poly.coeff 4=0:=Polynomial.coeff_eq_zero_of_natDegree_lt (by have:=A.hdeg;omega);rw [hc4,mul_zero]
  change |iteratedDeriv 4 (fun s=>f s-A.poly.eval s) t| ≤ c*lam;rw [hsub,hP4,sub_zero];exact hder_hi t ht
 have hgn_diff:1/(3*(A.denom:E)) ≤ |g (n:E)-g (n0:E)|:=by
  have h1:=abs_eval_sub_int_ge_inv_polyDenom A.hasIntDenom n (round (f (n:E))) hnot;have h2:|f (n:E)-(round (f (n:E)):E)| < δ:=(mem_filter.mp hn).2;have h3:|g (n0:E)| < δ:=by dsimp [g];rw [A.heval n0 hn0];exact (mem_filter.mp (A.hsub hn0)).2
  have htri1:|A.poly.eval (n:E)-(round (f (n:E)):E)| ≤
    |g (n:E)| + |f (n:E)-(round (f (n:E)):E)|:=by
   have:A.poly.eval (n:E)-(round (f (n:E)):E) = -g (n:E)+(f (n:E)-(round (f (n:E)):E)):=by dsimp [g];ring
   rw [this]
   calc
    |-g (n:E)+(f (n:E)-(round (f (n:E)):E))|
        ≤ |-g (n:E)| + |f (n:E)-(round (f (n:E)):E)|:=abs_add_le _ _
    _ = |g (n:E)| + |f (n:E)-(round (f (n:E)):E)|:=by rw [abs_neg]
  have htri2:|g (n:E)| ≤ |g (n:E)-g (n0:E)| + |g (n0:E)|:=by
   have:g (n:E)=(g (n:E)-g (n0:E))+g (n0:E):=by ring
   conv_lhs=>rw [this]
   exact abs_add_le _ _
  have hq3:2*δ<=2/(3*(A.denom:E)):=by
   rw [le_div_iff₀ (by positivity)];nlinarith
  have hq_split:1/(A.denom:E)=1/(3*(A.denom:E))+2/(3*(A.denom:E)):=by ring
  change 1/(A.denom:E) ≤ |A.poly.eval (n:E)-(round (f (n:E)):E)| at h1;linarith
 have hcl_bd:c*lam<=4096*c*δ/A.len^4:=by
  have hL_le:=A.len_le hδ hlam hcd hder_lo;have hpow4:A.len^4<=(8*(δ/lam)^(1/4:E))^4 :=pow_le_pow_left₀ hL_pos.le hL_le 4
  have h84:(8*(δ/lam)^(1/4:E))^4=4096*(δ/lam):=by
   rw [mul_pow,← rpow_natCast ((δ/lam)^(1/4:E)) 4,← rpow_mul (by positivity)];norm_num
  rw [h84,← mul_div_assoc] at hpow4;rw [le_div_iff₀ (pow_pos hL_pos 4)];have h1:A.len^4*lam<=4096*δ:=(le_div_iff₀ hlam).mp hpow4;nlinarith
 have hhi_eq:(A.lo:E)+A.len=(A.hi:E):=by dsimp [ProperArc.len];push_cast;ring
 have hsub_A:Icc (A.lo:E) ((A.lo:E)+A.len)⊆Icc (M:E) (2*(M:E)):=by
  rw [hhi_eq];intro t ht;have hlo_m:=Finset.mem_Icc.mp (mem_filter.mp (A.hsub (Finset.min'_mem A.pts A.nonempty))).1;have hhi_m:=Finset.mem_Icc.mp (mem_filter.mp (A.hsub (Finset.max'_mem A.pts A.nonempty))).1
  exact ⟨le_trans (by exact_mod_cast hlo_m.1) ht.1,le_trans ht.2 (by exact_mod_cast hhi_m.2)⟩
 have hn0_A:(n0:E)∈Icc (A.lo:E) ((A.lo:E)+A.len):=by
  rw [hhi_eq];exact ⟨by exact_mod_cast Finset.min'_le A.pts n0 hn0,by exact_mod_cast Finset.le_max' A.pts n0 hn0⟩
 have hM0_A:∀ t∈Icc (A.lo:E) ((A.lo:E)+A.len),|g t| ≤ δ:=by
  intro t ht;rw [hhi_eq] at ht;exact A.hclose t ht
 obtain ⟨hd1,hd2,hd3⟩:=neder_order_four hL_pos
  (fun t ht=>hcd_g t (hsub_A ht)) hM0_A (fun t ht=>hder4_g t (hsub_A ht))
  hδ.le (by positivity) hn0_A
 have hn_M:(n:E)∈Icc (M:E) (2*(M:E)):=by
  have h:=Finset.mem_Icc.mp (mem_filter.mp hn).1;exact ⟨by exact_mod_cast h.1,by exact_mod_cast h.2⟩
 have hn0_M:(n0:E)∈Icc (M:E) (2*(M:E)):=hsub_A hn0_A;have htay:=taylor_order_four_bound hcd_g hder4_g (by positivity) hn0_M hn_M;let d:E:=|(n:E)-(n0:E)|;let u:E:=d/A.len;have hu_nn:0<=u:=by positivity
 have hd_eq:d=u*A.len:=by dsimp [u];field_simp [hL_pos.ne']
 have hgn_up:|g (n:E)-g (n0:E)| ≤ 2*10^7*c*δ*(u+u^2+u^3+u^4):=by
  have htri:|g (n:E)-g (n0:E)| ≤ d * |deriv g (n0:E)| + d^2/2 * |iteratedDeriv 2 g (n0:E)| + d^3/6 * |iteratedDeriv 3 g (n0:E)| + c*lam*d^4/24:=by
   have hre:g (n:E)-g (n0:E) = (g (n:E)-(g (n0:E)+((n:E)-(n0:E))*deriv g (n0:E) + ((n:E)-(n0:E))^2/2*iteratedDeriv 2 g (n0:E) + ((n:E)-(n0:E))^3/6*iteratedDeriv 3 g (n0:E))) + (((n:E)-(n0:E))*deriv g (n0:E) + ((n:E)-(n0:E))^2/2*iteratedDeriv 2 g (n0:E) + ((n:E)-(n0:E))^3/6*iteratedDeriv 3 g (n0:E)):=by ring
   rw [hre]
   have e1:=abs_add_le
    (g (n:E)-(g (n0:E)+((n:E)-(n0:E))*deriv g (n0:E) + ((n:E)-(n0:E))^2/2*iteratedDeriv 2 g (n0:E) + ((n:E)-(n0:E))^3/6*iteratedDeriv 3 g (n0:E)))
    (((n:E)-(n0:E))*deriv g (n0:E) + ((n:E)-(n0:E))^2/2*iteratedDeriv 2 g (n0:E) + ((n:E)-(n0:E))^3/6*iteratedDeriv 3 g (n0:E))
   have e2:=abs_add_le
    (((n:E)-(n0:E))*deriv g (n0:E) + ((n:E)-(n0:E))^2/2*iteratedDeriv 2 g (n0:E))
    (((n:E)-(n0:E))^3/6*iteratedDeriv 3 g (n0:E))
   have e3:=abs_add_le
    (((n:E)-(n0:E))*deriv g (n0:E))
    (((n:E)-(n0:E))^2/2*iteratedDeriv 2 g (n0:E))
   simp only [abs_mul,abs_div,abs_pow,abs_of_pos (by norm_num:(0:E) < 2),abs_of_pos (by norm_num:(0:E) < 6)] at e2 e3;dsimp [d] at htay ⊢;linarith
  have hL3cl:A.len^3*(c*lam)<=4096*c*δ/A.len:=by
   calc
    A.len^3*(c*lam)<=A.len^3*(4096*c*δ/A.len^4) :=mul_le_mul_of_nonneg_left hcl_bd (pow_nonneg hL_pos.le 3)
    _ = 4096*c*δ/A.len:=by field_simp [hL_pos.ne']
  have hL2cl:A.len^2*(c*lam)<=4096*c*δ/A.len^2:=by
   calc
    A.len^2*(c*lam)<=A.len^2*(4096*c*δ/A.len^4) :=mul_le_mul_of_nonneg_left hcl_bd (sq_nonneg A.len)
    _ = 4096*c*δ/A.len^2:=by field_simp [hL_pos.ne']
  have hL1cl:A.len*(c*lam)<=4096*c*δ/A.len^3:=by
   calc
    A.len*(c*lam)<=A.len*(4096*c*δ/A.len^4) :=mul_le_mul_of_nonneg_left hcl_bd hL_pos.le
    _ = 4096*c*δ/A.len^3:=by field_simp [hL_pos.ne']
  have ht1:d * |deriv g (n0:E)| ≤ 500000*c*δ*u:=by
   have h1:|deriv g (n0:E)| ≤ 100*(δ/A.len+4096*c*δ/A.len):=by linarith
   have h2:d * |deriv g (n0:E)| ≤ (u*A.len)*(100*(δ/A.len+4096*c*δ/A.len)):=by rw [← hd_eq];exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
   have h3:(u*A.len)*(100*(δ/A.len+4096*c*δ/A.len)) = 100*(1+4096*c)*δ*u:=by field_simp [hL_pos.ne']
   rw [h3] at h2;have h4:100*(1+4096*c)<=500000*c:=by linarith
   have h5:100*(1+4096*c)*(δ*u)<=500000*c*(δ*u) :=mul_le_mul_of_nonneg_right h4 (mul_nonneg hδ.le hu_nn);linarith
  have ht2:d^2/2 * |iteratedDeriv 2 g (n0:E)| ≤ 3*10^6*c*δ*u^2:=by
   have h1:|iteratedDeriv 2 g (n0:E)| ≤ 1000*(δ/A.len^2+4096*c*δ/A.len^2):=by linarith
   have h2:d^2/2 * |iteratedDeriv 2 g (n0:E)| ≤ ((u*A.len)^2/2)*(1000*(δ/A.len^2+4096*c*δ/A.len^2)):=by rw [← hd_eq];exact mul_le_mul_of_nonneg_left h1 (by positivity)
   have h3:((u*A.len)^2/2)*(1000*(δ/A.len^2+4096*c*δ/A.len^2)) = 500*(1+4096*c)*δ*u^2:=by field_simp [hL_pos.ne'];ring
   rw [h3] at h2;have h4:500*(1+4096*c)<=3*10^6*c:=by linarith
   have h5:500*(1+4096*c)*(δ*u^2)<=3*10^6*c*(δ*u^2) :=mul_le_mul_of_nonneg_right h4 (mul_nonneg hδ.le (sq_nonneg u));linarith
  have ht3:d^3/6 * |iteratedDeriv 3 g (n0:E)| ≤ 10^7*c*δ*u^3:=by
   have h1:|iteratedDeriv 3 g (n0:E)| ≤ 10000*(δ/A.len^3+4096*c*δ/A.len^3):=by linarith
   have h2:d^3/6 * |iteratedDeriv 3 g (n0:E)| ≤ ((u*A.len)^3/6)*(10000*(δ/A.len^3+4096*c*δ/A.len^3)):=by rw [← hd_eq];exact mul_le_mul_of_nonneg_left h1 (by positivity)
   have h3:((u*A.len)^3/6)*(10000*(δ/A.len^3+4096*c*δ/A.len^3)) = (10000/6)*(1+4096*c)*δ*u^3:=by field_simp [hL_pos.ne']
   rw [h3] at h2;have h4:(10000/6:E)*(1+4096*c)<=10^7*c:=by linarith
   have h5:(10000/6:E)*(1+4096*c)*(δ*u^3)<=10^7*c*(δ*u^3) :=mul_le_mul_of_nonneg_right h4 (mul_nonneg hδ.le (pow_nonneg hu_nn 3));linarith
  have ht4:c*lam*d^4/24<=10^4*c*δ*u^4:=by
   have h2:c*lam*d^4/24<=(4096*c*δ/A.len^4)*(u*A.len)^4/24:=by rw [← hd_eq];gcongr
   have h3:(4096*c*δ/A.len^4)*(u*A.len)^4/24=(4096/24)*c*δ*u^4:=by field_simp [hL_pos.ne']
   rw [h3] at h2;have h4:(4096/24:E)*(c*δ*u^4)<=10^4*(c*δ*u^4) :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity);linarith
  have hcd_nn:0<=c*δ:=by positivity
  have h1:500000*(c*δ*u)<=2*10^7*(c*δ*u) :=mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hcd_nn hu_nn);have h2:3*10^6*(c*δ*u^2)<=2*10^7*(c*δ*u^2) :=mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hcd_nn (sq_nonneg u))
  have h3:10^7*(c*δ*u^3)<=2*10^7*(c*δ*u^3) :=mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hcd_nn (pow_nonneg hu_nn 3));have h4:10^4*(c*δ*u^4)<=2*10^7*(c*δ*u^4) :=mul_le_mul_of_nonneg_right (by norm_num) (mul_nonneg hcd_nn (pow_nonneg hu_nn 4));linarith
 have hu_comb:1 < (10^9*c)*(A.denom:E)*δ*max u (u^4):=by
  have hsum_le:u+u^2+u^3+u^4<=4*max u (u^4):=by
   by_cases hu1:u<=1
   ·
    have h2:u^2<=u:=by nlinarith
    have h3:u^3<=u:=by nlinarith
    have h4:u^4<=u:=by nlinarith
    linarith [le_max_left u (u^4)]
   ·
    push Not at hu1
    have h12:u<=u^2:=by nlinarith
    have h23:u^2<=u^3:=by nlinarith
    have h34:u^3<=u^4:=by nlinarith
    linarith [le_max_right u (u^4)]
  have hstep1:1/(3*(A.denom:E))<=8*10^7*c*δ*max u (u^4):=by
   have h1:=hgn_diff.trans hgn_up
   have:2*10^7*c*δ*(u+u^2+u^3+u^4) ≤ 2*10^7*c*δ*(4*max u (u^4)) :=mul_le_mul_of_nonneg_left hsum_le (by positivity)
   linarith
  have hstep2:1<=24*10^7*c*(A.denom:E)*δ*max u (u^4):=by
   have hm:=(div_le_iff₀ (by positivity:(0:E) < 3*(A.denom:E))).mp hstep1;linarith
  have hmax_pos:0 < max u (u^4):=by
   by_contra hle
   push Not at hle
   have:24*10^7*c*(A.denom:E)*δ*max u (u^4)<=0 :=mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
   linarith
  have hcqδ:0 < c*(A.denom:E)*δ*max u (u^4):=by positivity
  linarith
 have hmax_gt1:1 < max u (u^4):=by
  have hnn:0<=max u (u^4):=le_trans hu_nn (le_max_left _ _);nlinarith
 have hu_gt1:1 < u:=by
  by_contra hle
  push Not at hle
  have h2:u^2<=1:=by nlinarith
  have h4:u^4<=1:=by nlinarith
  have:max u (u^4)<=1:=max_le hle h4
  linarith
 have hmax_eq:max u (u^4)=u^4:=by
  apply max_eq_right;have h12:u<=u^2:=by nlinarith
  have h24:u^2<=u^4:=by nlinarith
  linarith
 rw [hmax_eq] at hu_comb;have hprod_pos:0 < (10^9*c)*(A.denom:E)*δ:=by positivity
 have hinv_lt:((10^9*c)*(A.denom:E)*δ)⁻¹ < u^4:=by rw [inv_lt_iff_one_lt_mul₀' hprod_pos];exact hu_comb
 have hrp:=Real.rpow_lt_rpow (by positivity) hinv_lt (by norm_num:(0:E) < 1/4);rw [Real.inv_rpow hprod_pos.le,← rpow_neg hprod_pos.le] at hrp;rw [← rpow_natCast u 4,← rpow_mul hu_nn] at hrp;norm_num at hrp;change A.len*((10^9*c)*(A.denom:E)*δ)^(-(1/4:E)) < d
 rw [hd_eq];nlinarith
lemma card_filter_poly_eq_le_three {P Q:Polynomial E} (hP:P.natDegree<=3)
  (hQ:Q.natDegree<=3) (hne:P≠Q) (S:Finset ℤ) :
  (S.filter (fun (n:ℤ)=>P.eval (n:E)=Q.eval (n:E))).card<=3:=by
 let R:=P-Q;have hR_ne:R≠0:=sub_ne_zero.mpr hne;have hR_deg:R.natDegree<=3:=(Polynomial.natDegree_sub_le P Q).trans (max_le hP hQ)
 have hsub:((S.filter (fun (n:ℤ)=>P.eval (n:E)=Q.eval (n:E))).image (fun n:ℤ=>(n:E))).val ⊆
   R.roots:=by
  intro x hx;rw [Finset.mem_val,Finset.mem_image] at hx;rcases hx with ⟨n,hn,rfl⟩;rw [Polynomial.mem_roots hR_ne,Polynomial.IsRoot.def,Polynomial.eval_sub,(mem_filter.mp hn).2,sub_self]
 have hcard_img:((S.filter (fun (n:ℤ)=>P.eval (n:E)=Q.eval (n:E))).image (fun n:ℤ=>(n:E))).card = (S.filter (fun (n:ℤ)=>P.eval (n:E)=Q.eval (n:E))).card :=Finset.card_image_of_injective _ Int.cast_injective
 have hle_roots:((S.filter (fun (n:ℤ)=>P.eval (n:E)=Q.eval (n:E))).image (fun n:ℤ=>(n:E))).card ≤ R.roots.card:=by simpa [Finset.card] using Multiset.card_le_card ((Multiset.le_iff_subset (Finset.nodup _)).mpr hsub)
 have hroots_deg:R.roots.card<=R.natDegree:=Polynomial.card_roots' R;omega
lemma ProperArc.order_and_sep {f:E->E} {M:ℕ} {δ lam c:E}
  (hδ:0 < δ) (hlam:0 < lam) (hc:1<=c)
  (hcd:∀ t∈Icc (M:E) (2*(M:E)),ContDiffAt E 4 f t)
  (hder_lo:∀ t∈Icc (M:E) (2*(M:E)),lam ≤ |iteratedDeriv 4 f t|)
  (hder_hi:∀ t∈Icc (M:E) (2*(M:E)),|iteratedDeriv 4 f t| ≤ c*lam)
  (A B:ProperArc f M δ)
  (hAq:(10^9*c)*(A.denom:E)*δ<=1)
  (hBq:(10^9*c)*(B.denom:E)*δ<=1)
  (hne:A.poly≠B.poly) :
  (A.lo < B.lo/\A.hi < B.hi ∧ A.len*((10^9*c)*(A.denom:E)*δ)^(-(1/4:E)) < ((B.hi-A.hi:ℤ):E)) ∨
  (B.lo < A.lo/\B.hi < A.hi ∧ B.len*((10^9*c)*(B.denom:E)*δ)^(-(1/4:E)) < ((A.hi-B.hi:ℤ):E)):=by
 have hexA:∃ nA∈A.pts,B.poly.eval (nA:E)≠(round (f (nA:E)):E):=by
  by_contra hall
  push Not at hall
  have hle:=card_filter_poly_eq_le_three A.hdeg B.hdeg hne A.pts
  have heq:A.pts.filter (fun (n:ℤ)=>A.poly.eval (n:E)=B.poly.eval (n:E))=A.pts:=by
   ext n;simp only [mem_filter,and_iff_left_iff_imp];intro hn;rw [A.heval n hn,hall n hn]
  rw [heq] at hle
  have:=A.hcard;omega
 have hexB:∃ nB∈B.pts,A.poly.eval (nB:E)≠(round (f (nB:E)):E):=by
  by_contra hall
  push Not at hall
  have hle:=card_filter_poly_eq_le_three B.hdeg A.hdeg hne.symm B.pts
  have heq:B.pts.filter (fun (n:ℤ)=>B.poly.eval (n:E)=A.poly.eval (n:E))=B.pts:=by
   ext n;simp only [mem_filter,and_iff_left_iff_imp];intro hn;rw [B.heval n hn,hall n hn]
  rw [heq] at hle
  have:=B.hcard;omega
 obtain ⟨nA,hnA_mem,hnA_not⟩:=hexA;obtain ⟨nB,hnB_mem,hnB_not⟩:=hexB
 have hprodA_pos:0 < (10^9*c)*(A.denom:E)*δ:=by
  have:(0:E) < (A.denom:E):=by exact_mod_cast A.denom_pos
  positivity
 have hprodB_pos:0 < (10^9*c)*(B.denom:E)*δ:=by
  have:(0:E) < (B.denom:E):=by exact_mod_cast B.denom_pos
  positivity
 have hge1_A:(1:E)<=((10^9*c)*(A.denom:E)*δ)^(-(1/4:E)):=by
  rw [rpow_neg hprodA_pos.le]
  have hle1:((10^9*c)*(A.denom:E)*δ)^(1/4:E)<=1:=by
   calc
    ((10^9*c)*(A.denom:E)*δ)^(1/4:E)<=(1:E)^(1/4:E) :=rpow_le_rpow hprodA_pos.le hAq (by norm_num)
    _ = 1:=Real.one_rpow _
  exact one_le_inv₀ (rpow_pos_of_pos hprodA_pos _) |>.mpr hle1
 have hge1_B:(1:E)<=((10^9*c)*(B.denom:E)*δ)^(-(1/4:E)):=by
  rw [rpow_neg hprodB_pos.le]
  have hle1:((10^9*c)*(B.denom:E)*δ)^(1/4:E)<=1:=by
   calc
    ((10^9*c)*(B.denom:E)*δ)^(1/4:E)<=(1:E)^(1/4:E) :=rpow_le_rpow hprodB_pos.le hBq (by norm_num)
    _ = 1:=Real.one_rpow _
  exact one_le_inv₀ (rpow_pos_of_pos hprodB_pos _) |>.mpr hle1
 have hLA_pos:0 < A.len:=lt_of_lt_of_le (by norm_num) A.len_ge_four;have hLB_pos:0 < B.len:=lt_of_lt_of_le (by norm_num) B.len_ge_four
 have hB_out:nB < A.lo\/A.hi < nB:=by
  by_contra hmid
  push Not at hmid
  have hd:A.len*((10^9*c)*(A.denom:E)*δ)^(-(1/4:E)) < |(nB:E)-(A.lo:E)| := A.dist_gt_of_not_on_poly hδ hlam hc hcd hder_lo hder_hi hAq
    (B.hsub hnB_mem) (Finset.min'_mem A.pts A.nonempty) hnB_not
  have hle_len:|(nB:E)-(A.lo:E)| ≤ A.len:=by
   rw [abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr hmid.1)];dsimp [ProperArc.len];exact_mod_cast (sub_le_sub_right hmid.2 A.lo)
  have:A.len<=A.len*((10^9*c)*(A.denom:E)*δ)^(-(1/4:E)) :=le_mul_of_one_le_right hLA_pos.le hge1_A
  linarith
 have hA_out:nA < B.lo\/B.hi < nA:=by
  by_contra hmid
  push Not at hmid
  have hd:B.len*((10^9*c)*(B.denom:E)*δ)^(-(1/4:E)) < |(nA:E)-(B.lo:E)| := B.dist_gt_of_not_on_poly hδ hlam hc hcd hder_lo hder_hi hBq
    (A.hsub hnA_mem) (Finset.min'_mem B.pts B.nonempty) hnA_not
  have hle_len:|(nA:E)-(B.lo:E)| ≤ B.len:=by
   rw [abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr hmid.1)];dsimp [ProperArc.len];exact_mod_cast (sub_le_sub_right hmid.2 B.lo)
  have:B.len<=B.len*((10^9*c)*(B.denom:E)*δ)^(-(1/4:E)) :=le_mul_of_one_le_right hLB_pos.le hge1_B
  linarith
 have hnA_lo:A.lo<=nA:=Finset.min'_le _ _ hnA_mem;have hnA_hi:nA<=A.hi:=Finset.le_max' _ _ hnA_mem;have hnB_lo:B.lo<=nB:=Finset.min'_le _ _ hnB_mem;have hnB_hi:nB<=B.hi:=Finset.le_max' _ _ hnB_mem;rcases hB_out with hBn_lt | hBn_gt
 ·
  have hBlo_lt:B.lo < A.lo:=lt_of_le_of_lt hnB_lo hBn_lt
  have hAn_gt:B.hi < nA:=by
   rcases hA_out with h | h
   · omega
   · exact h
  have hBhi_lt:B.hi < A.hi:=lt_of_lt_of_le hAn_gt hnA_hi;right;refine ⟨hBlo_lt,hBhi_lt,?_⟩
  have hd:B.len*((10^9*c)*(B.denom:E)*δ)^(-(1/4:E)) < |(nA:E)-(B.hi:E)| := B.dist_gt_of_not_on_poly hδ hlam hc hcd hder_lo hder_hi hBq
    (A.hsub hnA_mem) (Finset.max'_mem B.pts B.nonempty) hnA_not
  have hdiff:|(nA:E)-(B.hi:E)| ≤ ((A.hi-B.hi:ℤ):E):=by
   rw [abs_of_pos (by exact_mod_cast sub_pos.mpr hAn_gt)];exact_mod_cast sub_le_sub_right hnA_hi B.hi
  linarith
 ·
  have hAhi_lt:A.hi < B.hi:=lt_of_lt_of_le hBn_gt hnB_hi
  have hAn_lt:nA < B.lo:=by
   rcases hA_out with h | h
   · exact h
   · omega
  have hAlo_lt:A.lo < B.lo:=lt_of_le_of_lt hnA_lo hAn_lt;left;refine ⟨hAlo_lt,hAhi_lt,?_⟩
  have hd:A.len*((10^9*c)*(A.denom:E)*δ)^(-(1/4:E)) < |(nB:E)-(A.hi:E)| := A.dist_gt_of_not_on_poly hδ hlam hc hcd hder_lo hder_hi hAq
    (B.hsub hnB_mem) (Finset.max'_mem A.pts A.nonempty) hnB_not
  have hdiff:|(nB:E)-(A.hi:E)| ≤ ((B.hi-A.hi:ℤ):E):=by
   rw [abs_of_pos (by exact_mod_cast sub_pos.mpr hBn_gt)];exact_mod_cast sub_le_sub_right hnB_hi A.hi
  linarith
lemma exists_properArc_of_card_ge_17 {f:E->E} {M:ℕ} {δ lam:E}
  (hlam:0 < lam)
  (hcd:∀ t∈Icc (M:E) (2*(M:E)),ContDiffAt E 4 f t)
  (hder_lo:∀ t∈Icc (M:E) (2*(M:E)),lam ≤ |iteratedDeriv 4 f t|)
  {P:Polynomial E} (hdeg:P.natDegree<=3)
  (hcard17:17<=((nearCurveSet f M δ).filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))).card) :
  ∃ A:ProperArc f M δ,A.poly=P ∧ ((nearCurveSet f M δ).filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))).card<=4*A.pts.card:=by
 classical
 let SP:=(nearCurveSet f M δ).filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E));let r:=SP.card;let emb:=SP.orderEmbOfFin rfl
 let B:Finset (Fin (r-1)):=Finset.univ.filter (fun i =>
  ∃ x∈Ioo (emb ⟨i.1,by omega⟩:E) (emb ⟨i.1+1,by omega⟩:E),δ < |f x-P.eval x|)
 have hB_le:B.card<=3:=cubic_breaks_card_le_three hlam hcd hder_lo hdeg emb emb.strictMono
  (fun i=>(mem_filter.mp (Finset.orderEmbOfFin_mem SP rfl i)).1)
  (fun i=>(mem_filter.mp (Finset.orderEmbOfFin_mem SP rfl i)).2)
 let cuts:Finset ℕ:=({0,r}:Finset ℕ)∪B.image (fun i=>i.1+1);have h0_mem:0∈cuts:=Finset.mem_union_left _ (by simp);have hr_mem:r∈cuts:=Finset.mem_union_left _ (by simp)
 have hcuts_le_r:∀ c∈cuts,c<=r:=by
  intro c hc;rcases Finset.mem_union.mp hc with h | h
  ·
   simp only [Finset.mem_insert,Finset.mem_singleton] at h;rcases h with rfl | rfl <;> omega
  ·
   rcases Finset.mem_image.mp h with ⟨i,_,rfl⟩;omega
 have hcuts_card_le:cuts.card<=5:=by
  calc
   cuts.card<=({0,r}:Finset ℕ).card+(B.image (fun i=>i.1+1)).card:=Finset.card_union_le _ _
   _ <= 2+B.card:=Nat.add_le_add Finset.card_le_two card_image_le
   _ <= 5:=by omega
 have hr_ge17:17<=r:=hcard17
 have hcuts_card_ge:2<=cuts.card:=by
  have hsub:({0,r}:Finset ℕ)⊆cuts:=Finset.subset_union_left;have hr_ne:(0:ℕ)≠r:=by omega
  have h2:({0,r}:Finset ℕ).card=2:=Finset.card_pair hr_ne;exact h2 ▸ Finset.card_le_card hsub
 let m:=cuts.card-1;have hm_pos:1<=m:=by omega
 have hm_le:m<=4:=by omega
 let cEmb:=cuts.orderEmbOfFin rfl
 have hc0:cEmb ⟨0,by omega⟩=0:=by
  have h0_in:(0:ℕ)∈Set.range cEmb:=by
   rw [Finset.range_orderEmbOfFin cuts rfl];exact h0_mem
  rcases h0_in with ⟨j,hj⟩;have hle:cEmb ⟨0,by omega⟩<=cEmb j:=cEmb.monotone (Fin.mk_le_mk.mpr (Nat.zero_le j.1));omega
 have hcm:cEmb ⟨m,by omega⟩=r:=by
  have hmem:=Finset.orderEmbOfFin_mem cuts rfl ⟨m,by omega⟩;have hle:cEmb ⟨m,by omega⟩<=r:=hcuts_le_r _ hmem
  have hr_in:r∈Set.range cEmb:=by
   rw [Finset.range_orderEmbOfFin cuts rfl];exact hr_mem
  rcases hr_in with ⟨j,hj⟩
  have hge:cEmb j<=cEmb ⟨m,by omega⟩:=cEmb.monotone (show j<=⟨m,by omega⟩ by
   have:=j.2;exact Fin.mk_le_mk.mpr (by omega))
  omega
 let gap:ℕ->ℕ:=fun j=>if hj:j < m then cEmb ⟨j+1,by omega⟩-cEmb ⟨j,by omega⟩ else 0
 have hsum_gaps:∑ j∈Finset.range m,gap j=r:=by
  have htele:∀ k:ℕ,(hk:k<=m) → ∑ j∈Finset.range k,gap j=cEmb ⟨k,by omega⟩-cEmb ⟨0,by omega⟩:=by
   intro k hk
   induction k with
   | zero=>simp
   | succ k ih =>
    rw [sum_range_succ,ih (by omega)];have hk_lt:k < m:=by omega
    have hgap_eq:gap k=cEmb ⟨k+1,by omega⟩-cEmb ⟨k,by omega⟩:=dif_pos hk_lt;rw [hgap_eq];have h1:cEmb ⟨0,by omega⟩<=cEmb ⟨k,by omega⟩ :=cEmb.monotone (show (⟨0,_⟩:Fin cuts.card)<=⟨k,_⟩ by simp)
    have h2:cEmb ⟨k,by omega⟩<=cEmb ⟨k+1,by omega⟩ :=cEmb.monotone (show (⟨k,_⟩:Fin cuts.card)<=⟨k+1,_⟩ by simp);omega
  rw [htele m le_rfl,hc0,hcm,Nat.sub_zero]
 obtain ⟨j0,hj0_mem,hj0_max⟩:=Finset.exists_max_image (Finset.range m)
  gap (Finset.nonempty_range_iff.mpr (by omega))
 have hj0_lt:j0 < m:=Finset.mem_range.mp hj0_mem;let L:=cEmb ⟨j0+1,by omega⟩-cEmb ⟨j0,by omega⟩;have hL_eq:gap j0=L:=dif_pos hj0_lt
 have hr_le_4L:r<=4*L:=by
  calc
   r=∑ j∈Finset.range m,gap j:=hsum_gaps.symm
   _ <= ∑ _j∈Finset.range m,L:=by
    apply sum_le_sum;intro j hj;have h:=hj0_max j hj;rwa [hL_eq] at h
   _ = m*L:=by simp
   _ <= 4*L:=Nat.mul_le_mul_right L hm_le
 have hL_ge5:5<=L:=by omega
 let loIdx:=cEmb ⟨j0,by omega⟩;let hiIdx:=cEmb ⟨j0+1,by omega⟩;have hlo_lt_hi:loIdx < hiIdx:=cEmb.strictMono (show (⟨j0,_⟩:Fin cuts.card) < ⟨j0+1,_⟩ by simp);have hhi_le_r:hiIdx<=r:=hcuts_le_r _ (Finset.orderEmbOfFin_mem cuts rfl _)
 let idxSet:Finset (Fin r):=Finset.univ.filter (fun i=>loIdx<=i.1/\i.1 < hiIdx);let pts:Finset ℤ:=idxSet.image emb
 have hpts_card:pts.card=L:=by
  rw [Finset.card_image_of_injective _ emb.injective]
  have hbij:idxSet.card=(Finset.Ico loIdx hiIdx).card:=by
   apply Finset.card_bij (fun i _=>i.1)
   ·
    intro i hi;simp only [idxSet,mem_filter,Finset.mem_univ,true_and] at hi;exact Finset.mem_Ico.mpr hi
   · intro i1 _ i2 _ h;exact Fin.ext h
   ·
    intro k hk;rw [Finset.mem_Ico] at hk;exact ⟨⟨k,by omega⟩,by simp [idxSet,hk.1,hk.2],rfl⟩
  rw [hbij,Nat.card_Ico]
 have hpts_sub:pts⊆nearCurveSet f M δ:=by
  intro n hn;rcases Finset.mem_image.mp hn with ⟨i,_,rfl⟩;exact (mem_filter.mp (Finset.orderEmbOfFin_mem SP rfl i)).1
 have hpts_eval:∀ n∈pts,P.eval (n:E)=(round (f (n:E)):E):=by
  intro n hn;rcases Finset.mem_image.mp hn with ⟨i,_,rfl⟩;exact (mem_filter.mp (Finset.orderEmbOfFin_mem SP rfl i)).2
 have hno_break:∀ i:ℕ,(hi1:loIdx<=i)->(hi2:i+1 < hiIdx) → ∀ x∈Ioo (emb ⟨i,by omega⟩:E) (emb ⟨i+1,by omega⟩:E),|f x-P.eval x| ≤ δ:=by
  intro i hi1 hi2 x hx
  by_contra hgt
  push Not at hgt
  have hiB:(⟨i,by omega⟩:Fin (r-1))∈B:=by
   simp only [B,mem_filter,Finset.mem_univ,true_and];exact ⟨x,hx,hgt⟩
  have hcut:i+1∈cuts:=Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨i,by omega⟩,hiB,rfl⟩)
  have hex:∃ t:Fin cuts.card,cEmb t=i+1:=by
   have hmem:i+1∈Set.range cEmb:=by
    rw [Finset.range_orderEmbOfFin cuts rfl];exact hcut
   rcases hmem with ⟨t,ht⟩;exact ⟨t,ht⟩
  obtain ⟨t,ht⟩:=hex
  have ht_gt:(⟨j0,by omega⟩:Fin cuts.card) < t:=by
   by_contra hle;push Not at hle
   have:=cEmb.monotone hle;omega
  have ht_lt:t < (⟨j0+1,by omega⟩:Fin cuts.card):=by
   by_contra hle;push Not at hle
   have:=cEmb.monotone hle;omega
  have h1:j0 < t.1:=ht_gt;have h2:t.1 < j0+1:=ht_lt;omega
 have hpts_ne:pts.Nonempty:=Finset.card_pos.mp (by omega)
 have hmin_eq:pts.min' hpts_ne=emb ⟨loIdx,by omega⟩:=by
  apply le_antisymm
  ·
    exact Finset.min'_le pts _ (Finset.mem_image.mpr ⟨⟨loIdx,by omega⟩,
    by simp [idxSet,hlo_lt_hi],rfl⟩)
  ·
   apply Finset.le_min';intro y hy;rcases Finset.mem_image.mp hy with ⟨i,hi,rfl⟩;simp only [idxSet,mem_filter,Finset.mem_univ,true_and] at hi;exact emb.monotone (show (⟨loIdx,_⟩:Fin r)<=i from hi.1)
 have hmax_eq:pts.max' hpts_ne=emb ⟨hiIdx-1,by omega⟩:=by
  apply le_antisymm
  ·
   apply Finset.max'_le;intro y hy;rcases Finset.mem_image.mp hy with ⟨i,hi,rfl⟩;simp only [idxSet,mem_filter,Finset.mem_univ,true_and] at hi;exact emb.monotone (show i<=(⟨hiIdx-1,_⟩:Fin r) by show i.1<=hiIdx-1;omega)
  ·
    exact Finset.le_max' pts _ (Finset.mem_image.mpr ⟨⟨hiIdx-1,by omega⟩,
    by simp [idxSet];omega,rfl⟩)
 have hclose:∀ x∈Icc ((pts.min' (Finset.card_pos.mp (by omega)):ℤ):E)
      ((pts.max' (Finset.card_pos.mp (by omega)):ℤ):E),
   |f x-P.eval x| ≤ δ:=by
  intro x hx;rw [hmin_eq,hmax_eq] at hx
  by_cases hhit:∃ k:ℕ,∃ hk:k < r,loIdx<=k/\k < hiIdx/\x=(emb ⟨k,hk⟩:E)
  ·
   rcases hhit with ⟨k,hk,h1,h2,rfl⟩;have hmem:=Finset.orderEmbOfFin_mem SP rfl ⟨k,hk⟩;have hfl:=mem_filter.mp hmem;rw [hfl.2];exact (mem_filter.mp hfl.1).2.le
  ·
   let K:=(Finset.Ico loIdx hiIdx).filter (fun k =>
    if hk:k < r then (emb ⟨k,hk⟩:E)<=x else False)
   have hlo_K:loIdx∈K:=by
    simp only [K,mem_filter,Finset.mem_Ico];exact ⟨⟨le_rfl,hlo_lt_hi⟩,by simp [show loIdx < r by omega,hx.1]⟩
   let k0:=K.max' ⟨loIdx,hlo_K⟩;have hk0_K:k0∈K:=Finset.max'_mem K ⟨loIdx,hlo_K⟩;simp only [K,mem_filter,Finset.mem_Ico] at hk0_K;have hk0_r:k0 < r:=by omega
   have hk0_le:(emb ⟨k0,hk0_r⟩:E)<=x:=by simpa [hk0_r] using hk0_K.2
   have hk0_lt:(emb ⟨k0,hk0_r⟩:E) < x :=lt_of_le_of_ne hk0_le (fun he=>hhit ⟨k0,hk0_r,hk0_K.1.1,hk0_K.1.2,he.symm⟩)
   have hk0_lt_last:k0+1 < hiIdx:=by
    by_contra hge
    have hk0_eq:k0=hiIdx-1:=by omega
    have heq_emb:emb ⟨k0,hk0_r⟩=emb ⟨hiIdx-1,by omega⟩:=by congr 1;exact Fin.ext hk0_eq
    rw [heq_emb] at hk0_lt;linarith [hx.2]
   have hx_lt_next:x < (emb ⟨k0+1,by omega⟩:E):=by
    by_contra hle
    push Not at hle
    have hmem_next:k0+1∈K:=by
     simp only [K,mem_filter,Finset.mem_Ico];exact ⟨⟨by omega,hk0_lt_last⟩,by simp [show k0+1 < r by omega,hle]⟩
    have:=Finset.le_max' K (k0+1) hmem_next
    omega
   exact hno_break k0 hk0_K.1.1 hk0_lt_last x ⟨hk0_lt,hx_lt_next⟩
 refine ⟨⟨pts,P,hpts_sub,hdeg,by omega,hpts_eval,hclose⟩,rfl,?_⟩;simpa [SP,hpts_card] using hr_le_4L
set_option maxHeartbeats 800000 in
theorem huxley_sargos_4 {f:E->E} {M:ℕ} {δ lam c:E}
  (_hM:1<=M) (hδ:0 < δ) (_hδ_le:δ<=1/4) (hlam:0 < lam) (hc:1<=c)
  (hcd:∀ t∈Icc (M:E) (2*(M:E)),ContDiffAt E 4 f t)
  (hder_lo:∀ t∈Icc (M:E) (2*(M:E)),lam ≤ |iteratedDeriv 4 f t|)
  (hder_hi:∀ t∈Icc (M:E) (2*(M:E)),|iteratedDeriv 4 f t| ≤ c*lam) :
  ((nearCurveSet f M δ).card:E) ≤ 2000*c * ((M:E)*lam^(1/10:E) + (M:E)*δ^(1/6:E) + (δ/lam)^(1/4:E)+1):=by
 classical
 let S:Finset ℤ:=nearCurveSet f M δ;let a4:E:=10^9*c;have ha4_pos:0 < a4:=by positivity
 let mkPoly:Finset ℤ->Polynomial E:=fun T =>
  if h:T.card=4 then
   let e:=T.orderEmbOfFin h
   lagrangePoly (fun i=>(e i:E)) (fun i=>(round (f (e i:E)):E))
  else 0
 let candPolys:Finset (Polynomial E):=(S.powersetCard 4).image mkPoly
 let goodPolys:Finset (Polynomial E):=candPolys.filter (fun P =>
  P.natDegree<=3 ∧
  17<=(S.filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))).card ∧
  HasIntDenom P/\a4*(polyDenom P:E)*δ<=1)
 have hmem_cand:∀ P:Polynomial E,P.natDegree<=3 → 4<=(S.filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))).card->P∈candPolys:=by
  intro P hdeg h4;let SP:Finset ℤ:=S.filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E));obtain ⟨T,hT_sub,hT_card⟩:=Finset.exists_subset_card_eq h4;have hT_S:T⊆S:=hT_sub.trans (Finset.filter_subset _ _)
  refine Finset.mem_image.mpr ⟨T,Finset.mem_powersetCard.mpr ⟨hT_S,hT_card⟩,?_⟩;simp only [mkPoly,hT_card,↓reduceDIte];let e:=T.orderEmbOfFin hT_card
  have hinj:Function.Injective (fun i:Fin 4=>(e i:E)):=by
   intro i j hij;exact e.injective (Int.cast_injective hij)
  have hev:∀ i:Fin 4,P.eval (e i:E)=(round (f (e i:E)):E):=fun i =>
   (mem_filter.mp (hT_sub (Finset.orderEmbOfFin_mem T hT_card i))).2
  exact (eq_lagrangePoly_of_eval _ _ hinj P hdeg hev).symm
 let S0:Finset ℤ:=S.filter (fun (n:ℤ)=>∃ P∈goodPolys,P.eval (n:E)=(round (f (n:E)):E));let T0:Finset ℤ:=S.filter (fun (n:ℤ)=>¬ ∃ P∈goodPolys,P.eval (n:E)=(round (f (n:E)):E));have hS_split:S.card=S0.card+T0.card:=(Finset.card_filter_add_card_filter_not _).symm
 have ha4_rpow:a4^(1/6:E)<=32*c:=by
  have h1:a4^(1/6:E)=(10^9:E)^(1/6:E)*c^(1/6:E):=by dsimp [a4];exact mul_rpow (by positivity) (by linarith)
  rw [h1]
  have h10:(10^9:E)^(1/6:E)<=32:=by
   have hle:(10^9:E)<=(32:E)^(6:ℕ):=by norm_num
   have hrp:=rpow_le_rpow (by positivity) hle (by norm_num:(0:E)<=1/6);rw [← rpow_natCast (32:E) 6,← rpow_mul (by norm_num)] at hrp;have h6:((6:ℕ):E)*(1/6:E)=1:=by norm_num
   rw [h6,rpow_one] at hrp;exact hrp
  have hc16:c^(1/6:E)<=c:=by
   calc
    c^(1/6:E)<=c^(1:E):=rpow_le_rpow_of_exponent_le hc (by norm_num)
    _ = c:=rpow_one c
  exact mul_le_mul h10 hc16 (rpow_nonneg (by linarith) _) (by norm_num)
 have hcl_rpow:(c*lam)^(1/10:E)<=c*lam^(1/10:E):=by
  rw [mul_rpow (by linarith) hlam.le]
  have hc10:c^(1/10:E)<=c:=by
   calc
    c^(1/10:E)<=c^(1:E):=rpow_le_rpow_of_exponent_le hc (by norm_num)
    _ = c:=rpow_one c
  exact mul_le_mul_of_nonneg_right hc10 (rpow_nonneg hlam.le _)
 have hS0_bound:(S0.card:E)<=32*a4^(1/6:E)*(M:E)*δ^(1/6:E) + 256*(δ/lam)^(1/4:E):=by
  have hex_arc:∀ P:Polynomial E,P∈goodPolys → ∃ A:ProperArc f M δ,A.poly=P ∧ (S.filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))).card<=4*A.pts.card:=by
   intro P hP;have hfl:=(mem_filter.mp hP).2;exact exists_properArc_of_card_ge_17 hlam hcd hder_lo hfl.1 hfl.2.1
  choose arc harc_poly harc_card using hex_arc
  have hS0_sum:(S0.card:E)<=4*∑ P∈goodPolys.attach,((arc P.1 P.2).pts.card:E):=by
   have hsub:S0⊆goodPolys.biUnion (fun P=>S.filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))):=by
    intro n hn;rcases mem_filter.mp hn with ⟨hnS,P,hP,hev⟩;exact Finset.mem_biUnion.mpr ⟨P,hP,mem_filter.mpr ⟨hnS,hev⟩⟩
   have h1:S0.card<=∑ P∈goodPolys,(S.filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))).card :=(Finset.card_le_card hsub).trans Finset.card_biUnion_le
   have h2:∑ P∈goodPolys,(S.filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))).card = ∑ P∈goodPolys.attach,(S.filter (fun (n:ℤ)=>P.1.eval (n:E)=(round (f (n:E)):E))).card :=(Finset.sum_attach goodPolys _).symm
   have h3:∑ P∈goodPolys.attach,(S.filter (fun (n:ℤ)=>P.1.eval (n:E)=(round (f (n:E)):E))).card ≤ ∑ P∈goodPolys.attach,4*(arc P.1 P.2).pts.card :=sum_le_sum (fun P _=>harc_card P.1 P.2);rw [← Finset.mul_sum] at h3
   have hnat:S0.card<=4*∑ P∈goodPolys.attach,(arc P.1 P.2).pts.card:=h1.trans (h2 ▸ h3);exact_mod_cast hnat
  let loMap:{P // P∈goodPolys}->ℤ:=fun P=>(arc P.1 P.2).lo
  have hlo_inj:Function.Injective loMap:=by
   intro P1 P2 heq
   by_contra hne
   have hpoly_ne:(arc P1.1 P1.2).poly≠(arc P2.1 P2.2).poly:=by rw [harc_poly P1.1 P1.2,harc_poly P2.1 P2.2];exact Subtype.coe_ne_coe.mpr hne
   have hq1:a4*((arc P1.1 P1.2).denom:E)*δ<=1:=by dsimp [ProperArc.denom];rw [harc_poly];exact (mem_filter.mp P1.2).2.2.2.2
   have hq2:a4*((arc P2.1 P2.2).denom:E)*δ<=1:=by dsimp [ProperArc.denom];rw [harc_poly];exact (mem_filter.mp P2.2).2.2.2.2
   dsimp [loMap] at heq
   rcases ProperArc.order_and_sep hδ hlam hc hcd hder_lo hder_hi (arc P1.1 P1.2) (arc P2.1 P2.2)
      hq1 hq2 hpoly_ne with ⟨hlt,_,_⟩ | ⟨hlt,_,_⟩ <;> omega
  let loSet:Finset ℤ:=goodPolys.attach.image loMap;let m:=loSet.card
  by_cases hm0:m=0
  ·
   have hempty:goodPolys.attach=∅:=by rw [Finset.card_eq_zero,Finset.image_eq_empty] at hm0;exact hm0
   rw [hempty,Finset.sum_empty,mul_zero] at hS0_sum;exact hS0_sum.trans (by positivity)
  ·
   have hm_pos:0 < m:=Nat.pos_of_ne_zero hm0;let emb:=loSet.orderEmbOfFin rfl
   have hrec:∀ i:Fin m,∃ P:{P // P∈goodPolys},loMap P=emb i:=by
    intro i;have hmem:=Finset.orderEmbOfFin_mem loSet rfl i;rcases Finset.mem_image.mp hmem with ⟨P,_,hP⟩;exact ⟨P,hP⟩
   choose Pseq hPseq using hrec
   have hPseq_inj:Function.Injective Pseq:=by
    intro i j h
    have:emb i=emb j:=by rw [← hPseq i,← hPseq j,h]
    exact emb.injective this
   have hsum_eq:∑ P∈goodPolys.attach,((arc P.1 P.2).pts.card:E) = ∑ i:Fin m,((arc (Pseq i).1 (Pseq i).2).pts.card:E):=by
    symm
    apply Finset.sum_nbij Pseq
    · intro i _;exact Finset.mem_attach _ _
    · intro i _ j _ h;exact hPseq_inj h
    ·
      intro P _;have hmem:loMap P∈(loSet:Set ℤ):=Finset.mem_image.mpr ⟨P,Finset.mem_attach _ _,rfl⟩;rw [← Finset.range_orderEmbOfFin loSet rfl] at hmem;rcases Set.mem_range.mp hmem with ⟨i,hi⟩;exact ⟨i,Finset.mem_univ _,hlo_inj ((hPseq i).trans hi)⟩
    · intro _ _;rfl
   have hstep:∀ i:ℕ,(hi:i+1 < m) → ((arc (Pseq ⟨i,by omega⟩).1 (Pseq ⟨i,by omega⟩).2).pts.card:E) ≤ 8*a4^(1/6:E)*δ^(1/6:E) * (((arc (Pseq ⟨i+1,hi⟩).1 (Pseq ⟨i+1,hi⟩).2).hi -
          (arc (Pseq ⟨i,by omega⟩).1 (Pseq ⟨i,by omega⟩).2).hi:ℤ):E):=by
    intro i hi;set A:=arc (Pseq ⟨i,by omega⟩).1 (Pseq ⟨i,by omega⟩).2;set B:=arc (Pseq ⟨i+1,hi⟩).1 (Pseq ⟨i+1,hi⟩).2
    have hlo_lt:A.lo < B.lo:=by
      change loMap (Pseq ⟨i,by omega⟩) < loMap (Pseq ⟨i+1,hi⟩);rw [hPseq,hPseq];exact emb.strictMono (by show i < i+1;omega)
    have hpoly_ne:A.poly≠B.poly:=by
      intro heq
      have hP_eq:Pseq ⟨i,by omega⟩=Pseq ⟨i+1,hi⟩:=by
       apply Subtype.ext;rw [← harc_poly (Pseq ⟨i,by omega⟩).1 (Pseq ⟨i,by omega⟩).2,← harc_poly (Pseq ⟨i+1,hi⟩).1 (Pseq ⟨i+1,hi⟩).2];exact heq
      have:=hPseq_inj hP_eq
      simp at this
    have hqA:a4*(A.denom:E)*δ<=1:=by dsimp [A,ProperArc.denom];rw [harc_poly];exact (mem_filter.mp (Pseq ⟨i,by omega⟩).2).2.2.2.2
    have hqB:a4*(B.denom:E)*δ<=1:=by dsimp [B,ProperArc.denom];rw [harc_poly];exact (mem_filter.mp (Pseq ⟨i+1,hi⟩).2).2.2.2.2
    have hsep:A.len*(a4*(A.denom:E)*δ)^(-(1/4:E)) < ((B.hi-A.hi:ℤ):E):=by
      rcases ProperArc.order_and_sep hδ hlam hc hcd hder_lo hder_hi A B hqA hqB hpoly_ne with
       ⟨_,_,h⟩ | ⟨hcontra,_,_⟩
      · exact h
      · omega
    have hcardA:=A.card_le;have hqA_pos:(0:E) < (A.denom:E):=by exact_mod_cast A.denom_pos
    have hLA_pos:0 < A.len:=lt_of_lt_of_le (by norm_num) A.len_ge_four
    have hq_exp:(A.denom:E)^(-(1/6:E)) ≤ a4^(1/6:E)*δ^(1/6:E)*(a4*(A.denom:E)*δ)^(-(1/4:E)):=by
      have haδ_pos:0 < a4*δ:=by positivity
      have hq_le_inv:(A.denom:E)<=(a4*δ)⁻¹:=by rw [← one_div,le_div_iff₀ haδ_pos];linarith
      have hq12:(A.denom:E)^(1/12:E)<=(a4*δ)^(-(1/12:E)):=by
       have h:=rpow_le_rpow hqA_pos.le hq_le_inv (by norm_num:(0:E)<=1/12);rwa [Real.inv_rpow haδ_pos.le,← rpow_neg haδ_pos.le] at h
      have hsplit:(A.denom:E)^(-(1/6:E)) = (A.denom:E)^(-(1/4:E))*(A.denom:E)^(1/12:E):=by rw [← rpow_add hqA_pos];norm_num
      have hrhs:a4^(1/6:E)*δ^(1/6:E)*(a4*(A.denom:E)*δ)^(-(1/4:E)) = (A.denom:E)^(-(1/4:E))*(a4*δ)^(-(1/12:E)):=by
       have hmul:a4*(A.denom:E)*δ=(a4*δ)*(A.denom:E):=by ring
       rw [hmul,mul_rpow haδ_pos.le hqA_pos.le,← mul_rpow ha4_pos.le hδ.le]
       calc
         (a4*δ)^(1/6:E)*((a4*δ)^(-(1/4:E))*(A.denom:E)^(-(1/4:E)))
           = (A.denom:E)^(-(1/4:E))*((a4*δ)^(1/6:E)*(a4*δ)^(-(1/4:E))):=by ring
         _ = (A.denom:E)^(-(1/4:E))*(a4*δ)^(-(1/12:E)):=by rw [← rpow_add haδ_pos];norm_num
      rw [hsplit,hrhs];exact mul_le_mul_of_nonneg_left hq12 (rpow_nonneg hqA_pos.le _)
    have hstep1:8*A.len*(A.denom:E)^(-(1/6:E)) ≤ 8*a4^(1/6:E)*δ^(1/6:E)*(A.len*(a4*(A.denom:E)*δ)^(-(1/4:E))):=by
      have:=mul_le_mul_of_nonneg_left hq_exp (mul_nonneg (by norm_num:(0:E)<=8) hLA_pos.le)
      linarith
    have hstep2:8*a4^(1/6:E)*δ^(1/6:E)*(A.len*(a4*(A.denom:E)*δ)^(-(1/4:E))) ≤ 8*a4^(1/6:E)*δ^(1/6:E)*((B.hi-A.hi:ℤ):E) := mul_le_mul_of_nonneg_left hsep.le (mul_nonneg (mul_nonneg (by norm_num) (rpow_nonneg ha4_pos.le _))
       (rpow_nonneg hδ.le _))
    exact hcardA.trans (hstep1.trans hstep2)
   let cardAt:ℕ->E:=fun i =>
    if h:i < m then ((arc (Pseq ⟨i,h⟩).1 (Pseq ⟨i,h⟩).2).pts.card:E) else 0
   let hiAt:ℕ->ℤ:=fun i =>
    if h:i < m then (arc (Pseq ⟨i,h⟩).1 (Pseq ⟨i,h⟩).2).hi else 0
   have hsplit_sum:∑ i:Fin m,((arc (Pseq i).1 (Pseq i).2).pts.card:E) = (∑ i∈Finset.range (m-1),cardAt i)+cardAt (m-1):=by
    have h1:∑ i:Fin m,((arc (Pseq i).1 (Pseq i).2).pts.card:E) = ∑ i∈Finset.range m,cardAt i:=by
      have h1a:∑ i:Fin m,((arc (Pseq i).1 (Pseq i).2).pts.card:E) = ∑ i:Fin m,cardAt i.1:=by
       apply sum_congr rfl;intro i _;dsimp only [cardAt];rw [dif_pos i.2]
      rw [h1a];exact Fin.sum_univ_eq_sum_range cardAt m
    rw [h1];have hm_eq:m=(m-1)+1:=by omega
    conv_lhs=>rw [hm_eq,sum_range_succ]
   have hfirst:(∑ i∈Finset.range (m-1),cardAt i) ≤ 8*a4^(1/6:E)*(M:E)*δ^(1/6:E):=by
    have htele:∑ i∈Finset.range (m-1),((hiAt (i+1)-hiAt i:ℤ):E) = ((hiAt (m-1)-hiAt 0:ℤ):E):=by
      have hgen:∀ k:ℕ,∑ i∈Finset.range k,((hiAt (i+1)-hiAt i:ℤ):E) = ((hiAt k-hiAt 0:ℤ):E):=by
       intro k
       induction k with
       | zero=>simp
       | succ k ih =>
         rw [sum_range_succ,ih];push_cast;ring
      exact hgen (m-1)
    have hspan:((hiAt (m-1)-hiAt 0:ℤ):E)<=(M:E):=by
      have hm1:m-1 < m:=by omega
      have hhi_m:=(Finset.mem_Icc.mp (mem_filter.mp
       ((arc (Pseq ⟨m-1,hm1⟩).1 (Pseq ⟨m-1,hm1⟩).2).hsub
         (Finset.max'_mem _ (arc _ _).nonempty))).1).2
      have hlo_m:=(Finset.mem_Icc.mp (mem_filter.mp
       ((arc (Pseq ⟨0,hm_pos⟩).1 (Pseq ⟨0,hm_pos⟩).2).hsub
         (Finset.max'_mem _ (arc _ _).nonempty))).1).1
      have hhi_eq:hiAt (m-1)=(arc (Pseq ⟨m-1,hm1⟩).1 (Pseq ⟨m-1,hm1⟩).2).hi :=dif_pos hm1;have hlo_eq:hiAt 0=(arc (Pseq ⟨0,hm_pos⟩).1 (Pseq ⟨0,hm_pos⟩).2).hi :=dif_pos hm_pos
      have:hiAt (m-1)-hiAt 0<=(M:ℤ):=by
       rw [hhi_eq,hlo_eq];dsimp [ProperArc.hi];omega
      exact_mod_cast this
    calc
      ∑ i∈Finset.range (m-1),cardAt i
         ≤ ∑ i∈Finset.range (m-1),(8*a4^(1/6:E)*δ^(1/6:E)*((hiAt (i+1)-hiAt i:ℤ):E)):=by
       apply sum_le_sum;intro i hi;have hi_lt:i < m-1:=Finset.mem_range.mp hi;have hi1:i < m:=by omega
       have hi2:i+1 < m:=by omega
       simp only [cardAt,hiAt,hi1,hi2,↓reduceDIte];exact hstep i hi2
      _ = 8*a4^(1/6:E)*δ^(1/6:E) * ∑ i∈Finset.range (m-1),((hiAt (i+1)-hiAt i:ℤ):E):=by rw [← Finset.mul_sum]
      _ = 8*a4^(1/6:E)*δ^(1/6:E)*((hiAt (m-1)-hiAt 0:ℤ):E):=by rw [htele]
      _ <= 8*a4^(1/6:E)*δ^(1/6:E)*(M:E) :=mul_le_mul_of_nonneg_left hspan (by positivity)
      _ = 8*a4^(1/6:E)*(M:E)*δ^(1/6:E):=by ring
   have hlast_arc:∀ (A:ProperArc f M δ),(A.pts.card:E)<=64*(δ/lam)^(1/4:E):=by
    intro A;have hcA:=A.card_le;have hlenA:=A.len_le hδ hlam hcd hder_lo;have hq_ge1:(1:E)<=(A.denom:E):=by exact_mod_cast A.denom_pos
    have hq_le1:(A.denom:E)^(-(1/6:E))<=1:=by
      rw [rpow_neg (by linarith)];exact inv_le_one_of_one_le₀ (one_le_rpow hq_ge1 (by norm_num))
    have hLA_pos:0 < A.len:=lt_of_lt_of_le (by norm_num) A.len_ge_four
    calc
      (A.pts.card:E)<=8*A.len*(A.denom:E)^(-(1/6:E)):=hcA
      _ <= 8*A.len*1:=mul_le_mul_of_nonneg_left hq_le1 (mul_nonneg (by norm_num) hLA_pos.le)
      _ = 8*A.len:=mul_one _
      _ <= 8*(8*(δ/lam)^(1/4:E)):=mul_le_mul_of_nonneg_left hlenA (by norm_num)
      _ = 64*(δ/lam)^(1/4:E):=by ring
   have hlast:cardAt (m-1)<=64*(δ/lam)^(1/4:E):=by
    have hm1:m-1 < m:=by omega
    dsimp only [cardAt];rw [dif_pos hm1];exact hlast_arc (arc (Pseq ⟨m-1,hm1⟩).1 (Pseq ⟨m-1,hm1⟩).2)
   rw [hsum_eq,hsplit_sum] at hS0_sum;linarith
 have hT0_bound:(T0.card:E)<=16*(M:E)*(c*lam)^(1/10:E) + 16*a4^(1/6:E)*(M:E)*δ^(1/6:E)+16:=by
  let t:=T0.card;let emb:=T0.orderEmbOfFin rfl;let sep:E:=min ((c*lam)^(-(1/10:E))) (a4^(-(1/6:E))*δ^(-(1/6:E)))
  have hsep_pos:0 < sep:=lt_min (rpow_pos_of_pos (by positivity) _)
   (mul_pos (rpow_pos_of_pos ha4_pos _) (rpow_pos_of_pos hδ _))
  have hstep16:∀ i:ℕ,(hi:i+16 < t) → sep<=((emb ⟨i+16,hi⟩-emb ⟨i,by omega⟩:ℤ):E):=by
   intro i hi;let xs4:Fin 4->ℤ:=fun j=>emb ⟨i+j.1,by omega⟩;have hmono4:StrictMono xs4:=fun a b hab=>emb.strictMono (by show i+a.1 < i+b.1;omega);let ms4:Fin 4->ℤ:=fun j=>round (f (xs4 j:E));let P:=lagrangePoly (fun j=>(xs4 j:E)) (fun j=>(ms4 j:E))
   have hinj4:Function.Injective (fun j=>(xs4 j:E)):=fun a b h =>
    hmono4.injective (by dsimp only at h;exact_mod_cast h)
   have hP_deg:P.natDegree<=3:=lagrangePoly_natDegree_le _ _
   have hP_eval4:∀ j:Fin 4,P.eval (xs4 j:E)=(ms4 j:E):=fun j =>
    lagrangePoly_eval _ _ hinj4 j
   by_cases hall:∀ j:Fin 17,P.eval (emb ⟨i+j.1,by omega⟩:E) = (round (f (emb ⟨i+j.1,by omega⟩:E)):E)
   ·
    have h17_sub:(Finset.univ.image (fun j:Fin 17=>emb ⟨i+j.1,by omega⟩)) ⊆
       S.filter (fun n=>P.eval (n:E)=(round (f (n:E)):E)):=by
      intro n hn;rcases Finset.mem_image.mp hn with ⟨j,_,rfl⟩
      exact mem_filter.mpr
       ⟨(mem_filter.mp (Finset.orderEmbOfFin_mem T0 rfl ⟨i+j.1,by omega⟩)).1,hall j⟩
    have hcard17:17<=(S.filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))).card:=by
      have hinj17:Function.Injective (fun j:Fin 17=>emb ⟨i+j.1,by omega⟩):=by
       intro a b h;have:=emb.injective h;ext;simp at this;omega
      have h17:(Finset.univ.image (fun j:Fin 17=>emb ⟨i+j.1,by omega⟩)).card=17:=by rw [Finset.card_image_of_injective _ hinj17,Finset.card_fin]
      calc
       17=(Finset.univ.image (fun j:Fin 17=>emb ⟨i+j.1,by omega⟩)).card:=h17.symm
       _ <= (S.filter (fun (n:ℤ)=>P.eval (n:E)=(round (f (n:E)):E))).card :=Finset.card_le_card h17_sub
    obtain ⟨hhas,hq_le⟩:=hasIntDenom_and_le_of_interp4 hP_deg xs4 ms4 hmono4 hP_eval4
    have hnot_good:P ∉ goodPolys:=by
      intro hPin
      have hT0_mem:=(mem_filter.mp (Finset.orderEmbOfFin_mem T0 rfl ⟨i,by omega⟩)).2;exact hT0_mem ⟨P,hPin,by simpa [xs4,ms4] using hP_eval4 0⟩
    have hq_gt:1 < a4*(polyDenom P:E)*δ:=by
      by_contra hle
      push Not at hle
      exact hnot_good (mem_filter.mpr ⟨hmem_cand P hP_deg (by omega),hP_deg,hcard17,hhas,hle⟩)
    have hspan_ge:((xs4 3-xs4 0:ℤ):E)<=((emb ⟨i+16,hi⟩-emb ⟨i,by omega⟩:ℤ):E):=by
      have h1:xs4 3<=emb ⟨i+16,hi⟩:=emb.monotone (by show i+3<=i+16;omega);have h2:xs4 0=emb ⟨i,by omega⟩:=rfl;exact_mod_cast sub_le_sub_right h1 _
    have hpos_d:(0:E)<=((emb ⟨i+16,hi⟩-emb ⟨i,by omega⟩:ℤ):E):=by
      have:emb ⟨i,by omega⟩ < emb ⟨i+16,hi⟩:=emb.strictMono (by show i < i+16;omega)
      exact_mod_cast (sub_pos.mpr this).le
    have hpos_3:(0:E)<=((xs4 3-xs4 0:ℤ):E):=by
      have:xs4 0 < xs4 3:=hmono4 (by decide:(0:Fin 4) < 3)
      exact_mod_cast (sub_pos.mpr this).le
    have hinv_le:(a4*δ)⁻¹<=((emb ⟨i+16,hi⟩-emb ⟨i,by omega⟩:ℤ):E)^6:=by
      have h1:(a4*δ)⁻¹ < (polyDenom P:E):=by rw [inv_lt_iff_one_lt_mul₀' (by positivity)];linarith
      have h2:((xs4 3-xs4 0:ℤ):E)^6<=((emb ⟨i+16,hi⟩-emb ⟨i,by omega⟩:ℤ):E)^6 :=pow_le_pow_left₀ hpos_3 hspan_ge 6;linarith
    have hrp:=rpow_le_rpow (by positivity) hinv_le (by norm_num:(0:E)<=1/6);rw [Real.inv_rpow (by positivity),mul_rpow ha4_pos.le hδ.le,mul_inv,← rpow_neg ha4_pos.le,← rpow_neg hδ.le,← rpow_natCast _ 6,← rpow_mul hpos_d] at hrp;norm_num at hrp;push_cast
    exact (min_le_right _ _).trans hrp
   ·
    push Not at hall
    obtain ⟨j0,hj0_ne⟩:=hall
    have hj0_ge4:4<=j0.1:=by
      by_contra hlt
      have:=hP_eval4 ⟨j0.1,by omega⟩
      exact hj0_ne (by simpa [xs4,ms4] using this)
    let xs5:Fin 5->ℤ:=fun k =>
      if hk:k.1 < 4 then emb ⟨i+k.1,by omega⟩ else emb ⟨i+j0.1,by omega⟩
    have hmono5:StrictMono xs5:=by
      intro a b hab
      by_cases ha:a.1 < 4 <;> by_cases hb:b.1 < 4
      · simp only [xs5,ha,hb,↓reduceDIte];exact emb.strictMono (by show i+a.1 < i+b.1;omega)
      · simp only [xs5,ha,hb,↓reduceDIte];exact emb.strictMono (by show i+a.1 < i+j0.1;omega)
      · omega
      · omega
    have hmem5:∀ k:Fin 5,xs5 k∈nearCurveSet f M δ:=by
      intro k
      by_cases hk:k.1 < 4
      ·
       simp only [xs5,hk,↓reduceDIte];exact (mem_filter.mp (Finset.orderEmbOfFin_mem T0 rfl ⟨i+k.1,by omega⟩)).1
      ·
       simp only [xs5,hk,↓reduceDIte];exact (mem_filter.mp (Finset.orderEmbOfFin_mem T0 rfl ⟨i+j0.1,by omega⟩)).1
    have hnotcubic:dividedDiff (fun k=>(xs5 k:E)) (fun k=>(round (f (xs5 k:E)):E))≠0:=by
      intro hdd0;let Q:=lagrangePoly (fun k=>(xs5 k:E)) (fun k=>(round (f (xs5 k:E)):E))
      have hinj5:Function.Injective (fun k=>(xs5 k:E)):=fun a b h =>
       hmono5.injective (by dsimp only at h;exact_mod_cast h)
      have hQ_deg4:Q.natDegree<=4:=lagrangePoly_natDegree_le _ _;have hQ_c4:Q.coeff 4=0:=by rw [lagrangePoly_coeff_top _ _];exact hdd0
      have hQ_deg3:Q.natDegree<=3:=by
       by_contra hgt
       have h4eq:Q.natDegree=4:=by omega
       have hlc:Q.leadingCoeff=0:=by rw [Polynomial.leadingCoeff,h4eq];exact hQ_c4
       have hQ0:Q=0:=Polynomial.leadingCoeff_eq_zero.mp hlc;rw [hQ0,Polynomial.natDegree_zero] at h4eq;omega
      have hQ_eval4:∀ j:Fin 4,Q.eval (xs4 j:E)=(ms4 j:E):=by
       intro j
       have h:=lagrangePoly_eval (fun k=>(xs5 k:E)) (fun k=>(round (f (xs5 k:E)):E))
         hinj5 ⟨j.1,by omega⟩
       simpa [Q,xs5,xs4,ms4,j.2] using h
      have hQP:Q=P:=eq_lagrangePoly_of_eval _ _ hinj4 Q hQ_deg3 hQ_eval4
      have hQ4:=lagrangePoly_eval (fun k=>(xs5 k:E)) (fun k=>(round (f (xs5 k:E)):E))
       hinj5 ⟨4,by omega⟩
      change Q.eval (xs5 ⟨4,by omega⟩:E)=(round (f (xs5 ⟨4,by omega⟩:E)):E) at hQ4;rw [hQP] at hQ4;exact hj0_ne (by simpa [xs5] using hQ4)
    have hminor:=minor_arc_sep_4 hδ hlam hc hcd hder_hi xs5 hmono5 hmem5 hnotcubic
    have hspan_le:((xs5 4-xs5 0:ℤ):E)<=((emb ⟨i+16,hi⟩-emb ⟨i,by omega⟩:ℤ):E):=by
      have h1:xs5 4<=emb ⟨i+16,hi⟩:=by
       dsimp only [xs5];rw [dif_neg (by norm_num)];exact emb.monotone (by show i+j0.1<=i+16;omega)
      have h2:xs5 0=emb ⟨i,by omega⟩:=by simp [xs5]
      rw [h2];exact_mod_cast sub_le_sub_right h1 _
    have ha4_half:a4^(-(1/6:E))*δ^(-(1/6:E))<=δ^(-(1/6:E))/2:=by
      have ha4_64:(64:E)<=a4:=by dsimp [a4];linarith
      have hrp:=rpow_le_rpow (by norm_num) ha4_64 (by norm_num:(0:E)<=1/6)
      have h64:(64:E)^(1/6:E)=2:=by
       have:(64:E)=(2:E)^(6:E):=by norm_num
       rw [this,← rpow_mul (by norm_num)];norm_num
      rw [h64] at hrp
      have hinv:a4^(-(1/6:E))<=1/2:=by
       rw [rpow_neg ha4_pos.le,one_div];simpa [one_div] using inv_anti₀ (by norm_num) hrp
      have hδp:0<=δ^(-(1/6:E)):=rpow_nonneg hδ.le _;nlinarith
    have hsep_le:sep<=min ((c*lam)^(-(1/10:E))) (δ^(-(1/6:E))/2) :=le_min (min_le_left _ _) ((min_le_right _ _).trans ha4_half);exact hsep_le.trans (hminor.trans hspan_le)
  by_cases ht0:t=0
  · rw [show T0.card=0 from ht0,Nat.cast_zero];positivity
  ·
   let q16:ℕ:=(t-1)/16;let embAt:ℕ->ℤ:=fun j=>if hj:j < t then emb ⟨j,hj⟩ else 0
   have hq16_sep:(q16:E)*sep<=(M:E):=by
    have htele:∑ j∈Finset.range q16,((embAt (16*(j+1))-embAt (16*j):ℤ):E) = ((embAt (16*q16)-embAt 0:ℤ):E):=by
      have hgen:∀ k:ℕ,∑ j∈Finset.range k,((embAt (16*(j+1))-embAt (16*j):ℤ):E) = ((embAt (16*k)-embAt 0:ℤ):E):=by
       intro k
       induction k with
       | zero=>simp
       | succ k ih =>
         rw [sum_range_succ,ih];push_cast;ring
      exact hgen q16
    have hspan:((embAt (16*q16)-embAt 0:ℤ):E)<=(M:E):=by
      have hq_lt:16*q16 < t:=by dsimp [q16,t];omega
      have h0_lt:0 < t:=by omega
      have hhi:=(Finset.mem_Icc.mp (mem_filter.mp
       (mem_filter.mp (Finset.orderEmbOfFin_mem T0 rfl ⟨16*q16,hq_lt⟩)).1).1).2
      have hlo:=(Finset.mem_Icc.mp (mem_filter.mp
       (mem_filter.mp (Finset.orderEmbOfFin_mem T0 rfl ⟨0,h0_lt⟩)).1).1).1
      have h1:embAt (16*q16)=emb ⟨16*q16,hq_lt⟩:=dif_pos hq_lt;have h2:embAt 0=emb ⟨0,h0_lt⟩:=dif_pos h0_lt;have hle:embAt (16*q16)-embAt 0<=(M:ℤ):=by rw [h1,h2];dsimp [emb];omega
      exact_mod_cast hle
    calc
      (q16:E)*sep=∑ _j∈Finset.range q16,sep:=by simp
      _ <= ∑ j∈Finset.range q16,((embAt (16*(j+1))-embAt (16*j):ℤ):E):=by
       apply sum_le_sum;intro j hj;have hj':=Finset.mem_range.mp hj;have h1:16*j+16 < t:=by dsimp [q16,t] at hj' ⊢;omega
       have h2:16*j < t:=by omega
       have h3:16*(j+1)=16*j+16:=by ring
       have hstep:=hstep16 (16*j) h1;have he1:embAt (16*(j+1))=emb ⟨16*j+16,h1⟩:=by rw [h3];exact dif_pos h1
       have he2:embAt (16*j)=emb ⟨16*j,h2⟩:=dif_pos h2;rw [he1,he2];exact hstep
      _ = ((embAt (16*q16)-embAt 0:ℤ):E):=htele
      _ <= (M:E):=hspan
   have hq16_le:(q16:E)<=(M:E)*(c*lam)^(1/10:E) + a4^(1/6:E)*(M:E)*δ^(1/6:E):=by
    have hinv:sep⁻¹<=(c*lam)^(1/10:E)+a4^(1/6:E)*δ^(1/6:E):=by
      rcases min_cases ((c*lam)^(-(1/10:E))) (a4^(-(1/6:E))*δ^(-(1/6:E))) with
       ⟨hmin,_⟩ | ⟨hmin,_⟩
      ·
       rw [show sep=(c*lam)^(-(1/10:E)) from hmin,rpow_neg (by positivity),inv_inv];linarith [mul_nonneg (rpow_nonneg ha4_pos.le (1/6:E)) (rpow_nonneg hδ.le (1/6:E))]
      ·
       rw [show sep=a4^(-(1/6:E))*δ^(-(1/6:E)) from hmin,mul_inv,rpow_neg ha4_pos.le,rpow_neg hδ.le,inv_inv,inv_inv];linarith [rpow_nonneg (by positivity:(0:E)<=c*lam) (1/10:E)]
    have h1:(q16:E)<=(M:E)*sep⁻¹:=by rw [← div_eq_mul_inv,le_div_iff₀ hsep_pos];exact hq16_sep
    have h2:(M:E)*sep⁻¹<=(M:E)*((c*lam)^(1/10:E)+a4^(1/6:E)*δ^(1/6:E)) :=mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg M);linarith
   have ht_le:(T0.card:E)<=16*(q16:E)+16:=by
    have:t<=16*q16+16:=by dsimp [q16,t];omega
    exact_mod_cast this
   linarith
 have hS_cast:(S.card:E)=(S0.card:E)+(T0.card:E):=by exact_mod_cast hS_split
 have hM_nn:(0:E)<=(M:E):=Nat.cast_nonneg M;have hδ16_nn:0<=δ^(1/6:E):=rpow_nonneg hδ.le _;have hlam10_nn:0<=lam^(1/10:E):=rpow_nonneg hlam.le _;have hdl_nn:0<=(δ/lam)^(1/4:E):=rpow_nonneg (by positivity) _
 have ht1:16*(M:E)*(c*lam)^(1/10:E)<=16*c*((M:E)*lam^(1/10:E)):=by
  have:=mul_le_mul_of_nonneg_left hcl_rpow (mul_nonneg (by norm_num:(0:E)<=16) hM_nn)
  linarith
 have ht2:48*a4^(1/6:E)*(M:E)*δ^(1/6:E) ≤ 1536*c*((M:E)*δ^(1/6:E)):=by
  have:=mul_le_mul_of_nonneg_right ha4_rpow (mul_nonneg hM_nn hδ16_nn)
  linarith
 have hS_sum:(S.card:E)<=16*c*((M:E)*lam^(1/10:E)) + 1536*c*((M:E)*δ^(1/6:E))+256*(δ/lam)^(1/4:E)+16:=by linarith
 have hc_pos:0<=c:=by linarith
 nlinarith [mul_nonneg hc_pos (mul_nonneg hM_nn hlam10_nn),mul_nonneg hc_pos (mul_nonneg hM_nn hδ16_nn),mul_nonneg hc_pos hdl_nn]
theorem nearCurve_inv_sq_card_le {v D H:ℕ} (hv:1<=v) (hD:1<=D) (hH:1<=H)
  (hH_le:4*H<=D^2) :
  (((Finset.Icc (D:ℤ) (2*(D:ℤ))).filter (fun (d:ℤ) =>
    ∃ m:ℤ,|((v:E)-(m:E)*(d:E)^2)| < (H:E))).card:E) ≤
   3*10^5 * ((v:E)^(1/10:E)*(D:E)^(2/5:E) + (D:E)^(2/3:E)*(H:E)^(1/6:E) + (H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E)+1):=by
 classical
 let f:E->E:=fun u=>(v:E)/u^2;let δ:E:=(H:E)/(D:E)^2;let lam:E:=120*(v:E)/(2*(D:E))^6;let c:E:=64;have hvR:(0:E) < (v:E):=by exact_mod_cast hv
 have hDR:(0:E) < (D:E):=by exact_mod_cast hD
 have hHR:(0:E) < (H:E):=by exact_mod_cast hH
 have hδ:0 < δ:=by positivity
 have hδ_le:δ<=1/4:=by
  dsimp [δ];rw [div_le_div_iff₀ (sq_pos_of_pos hDR) (by norm_num)]
  have:4*(H:E)<=(D:E)^2:=by exact_mod_cast hH_le
  linarith
 have hlam:0 < lam:=by positivity
 have hcd:∀ t∈Icc (D:E) (2*(D:E)),ContDiffAt E 4 f t:=by
  intro t ht;have ht_ne:t≠0:=by linarith [ht.1]
  exact contDiffAt_c_div_pow (v:E) 2 4 ht_ne
 have hder_lo:∀ t∈Icc (D:E) (2*(D:E)),lam ≤ |iteratedDeriv 4 f t|:=by
  intro t ht;have ht_pos:0 < t:=lt_of_lt_of_le hDR ht.1;rw [iteratedDeriv_inv_sq_4 (v:E) ht_pos,abs_of_pos (by positivity)];dsimp [lam];exact div_le_div_of_nonneg_left (by positivity) (pow_pos ht_pos 6) (pow_le_pow_left₀ ht_pos.le ht.2 6)
 have hder_hi:∀ t∈Icc (D:E) (2*(D:E)),|iteratedDeriv 4 f t| ≤ c*lam:=by
  intro t ht;have ht_pos:0 < t:=lt_of_lt_of_le hDR ht.1;rw [iteratedDeriv_inv_sq_4 (v:E) ht_pos,abs_of_pos (by positivity)];have hcl:c*lam=120*(v:E)/(D:E)^6:=by dsimp [c,lam];field_simp [hDR.ne'];ring
  rw [hcl];exact div_le_div_of_nonneg_left (by positivity) (pow_pos hDR 6) (pow_le_pow_left₀ hDR.le ht.1 6)
 have hsub:(Finset.Icc (D:ℤ) (2*(D:ℤ))).filter (fun (d:ℤ) =>
    ∃ m:ℤ,|((v:E)-(m:E)*(d:E)^2)| < (H:E))⊆nearCurveSet f D δ:=by
  intro d hd;rcases mem_filter.mp hd with ⟨hd_icc,m,hm⟩;refine mem_filter.mpr ⟨hd_icc,?_⟩;have hd_ge:(D:E)<=(d:E):=by exact_mod_cast (Finset.mem_Icc.mp hd_icc).1
  have hd_pos:(0:E) < (d:E):=lt_of_lt_of_le hDR hd_ge
  have hdiff:|f (d:E)-(m:E)| < δ:=by
   have heq:f (d:E)-(m:E)=((v:E)-(m:E)*(d:E)^2)/(d:E)^2:=by dsimp [f];field_simp [hd_pos.ne']
   rw [heq,abs_div,abs_of_pos (sq_pos_of_pos hd_pos)]
   calc
    |((v:E)-(m:E)*(d:E)^2)| / (d:E)^2
       < (H:E)/(d:E)^2:=div_lt_div_of_pos_right hm (sq_pos_of_pos hd_pos)
    _ <= (H:E)/(D:E)^2:=div_le_div_of_nonneg_left hHR.le (sq_pos_of_pos hDR)
       (pow_le_pow_left₀ hDR.le hd_ge 2)
  have hrm:round (f (d:E))=m:=round_eq_of_abs_sub_lt_half (lt_of_lt_of_le hdiff (by linarith));rwa [hrm]
 have hcard_le:(((Finset.Icc (D:ℤ) (2*(D:ℤ))).filter (fun (d:ℤ) =>
    ∃ m:ℤ,|((v:E)-(m:E)*(d:E)^2)| < (H:E))).card:E) ≤
   ((nearCurveSet f D δ).card:E):=by exact_mod_cast Finset.card_le_card hsub
 have hHS:=huxley_sargos_4 hD hδ hδ_le hlam (by norm_num:(1:E)<=c) hcd hder_lo hder_hi
 have ht1:(D:E)*lam^(1/10:E)<=2*(v:E)^(1/10:E)*(D:E)^(2/5:E):=by
  have hlam_eq:lam=(120/64:E)*((v:E)/(D:E)^6):=by dsimp [lam];ring
  rw [hlam_eq,mul_rpow (by positivity) (by positivity),div_rpow hvR.le (by positivity),← rpow_natCast (D:E) 6,← rpow_mul hDR.le]
  have hconst:(120/64:E)^(1/10:E)<=2:=by
   calc
    (120/64:E)^(1/10:E)<=(2:E)^(1/10:E) :=rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ <= (2:E)^(1:E):=rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2:=rpow_one 2
  have hDpow:(D:E)*((v:E)^(1/10:E)/(D:E)^((6:E)*(1/10:E))) = (v:E)^(1/10:E)*(D:E)^(2/5:E):=by
   have h1:(D:E)/(D:E)^((6:E)*(1/10:E))=(D:E)^(2/5:E):=by
    rw [div_eq_mul_inv,← rpow_neg hDR.le]
    conv_lhs=>arg 1;rw [← rpow_one (D:E)]
    rw [← rpow_add hDR];norm_num
   calc
    (D:E)*((v:E)^(1/10:E)/(D:E)^((6:E)*(1/10:E)))
       = (v:E)^(1/10:E)*((D:E)/(D:E)^((6:E)*(1/10:E))):=by ring
    _ = (v:E)^(1/10:E)*(D:E)^(2/5:E):=by rw [h1]
  calc
   (D:E)*((120/64:E)^(1/10:E)*((v:E)^(1/10:E)/(D:E)^((6:E)*(1/10:E))))
      = (120/64:E)^(1/10:E)*((D:E)*((v:E)^(1/10:E)/(D:E)^((6:E)*(1/10:E)))):=by ring
   _ = (120/64:E)^(1/10:E)*((v:E)^(1/10:E)*(D:E)^(2/5:E)):=by rw [hDpow]
   _ <= 2*((v:E)^(1/10:E)*(D:E)^(2/5:E)) :=mul_le_mul_of_nonneg_right hconst (by positivity)
   _ = 2*(v:E)^(1/10:E)*(D:E)^(2/5:E):=by ring
 have ht2:(D:E)*δ^(1/6:E)=(D:E)^(2/3:E)*(H:E)^(1/6:E):=by
  dsimp [δ];rw [div_rpow hHR.le (by positivity),← rpow_natCast (D:E) 2,← rpow_mul hDR.le]
  have h1:(D:E)/(D:E)^((2:E)*(1/6:E))=(D:E)^(2/3:E):=by
   rw [div_eq_mul_inv,← rpow_neg hDR.le]
   conv_lhs=>arg 1;rw [← rpow_one (D:E)]
   rw [← rpow_add hDR];norm_num
  calc
   (D:E)*((H:E)^(1/6:E)/(D:E)^((2:E)*(1/6:E)))
      = ((D:E)/(D:E)^((2:E)*(1/6:E)))*(H:E)^(1/6:E):=by ring
   _ = (D:E)^(2/3:E)*(H:E)^(1/6:E):=by rw [h1]
 have ht3:(δ/lam)^(1/4:E)<=(H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E):=by
  have hdl:δ/lam=(64/120:E)*((H:E)*(D:E)^4/(v:E)):=by dsimp [δ,lam];field_simp [hDR.ne',hvR.ne'];ring
  rw [hdl,mul_rpow (by positivity) (by positivity),div_rpow (by positivity) hvR.le,mul_rpow hHR.le (by positivity),← rpow_natCast (D:E) 4,← rpow_mul hDR.le];norm_num
  have hconst:(8/15:E)^(1/4:E)<=1:=by
   calc
    (8/15:E)^(1/4:E)<=(1:E)^(1/4:E) :=rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
    _ = 1:=Real.one_rpow _
  have hterm_nn:0<=(H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E):=by positivity
  calc
   (8/15:E)^(1/4:E)*((H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E))
      ≤ 1*((H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E)) :=
    mul_le_mul_of_nonneg_right hconst hterm_nn
   _ = (H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E):=one_mul _
 have hconst_le:2000*c*((D:E)*lam^(1/10:E)+(D:E)*δ^(1/6:E) + (δ/lam)^(1/4:E)+1) ≤ 3*10^5*((v:E)^(1/10:E)*(D:E)^(2/5:E) + (D:E)^(2/3:E)*(H:E)^(1/6:E) + (H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E)+1):=by
  have hvD_nn:0<=(v:E)^(1/10:E)*(D:E)^(2/5:E):=by positivity
  have hDH_nn:0<=(D:E)^(2/3:E)*(H:E)^(1/6:E):=by positivity
  have hHDv_nn:0<=(H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E):=by positivity
  dsimp [c];linarith
 exact hcard_le.trans (hHS.trans hconst_le)
end
lemma sum_inv_prime_sq_lt_half (S:Finset ℕ) (hS:∀ p∈S,Nat.Prime p) :
  ∑ p∈S,(1:E)/(p:E)^2 < 1/2:=by
 let S_small:=S.filter (fun p=>p<=7);let S_big:=S.filter (fun p=>7 < p)
 have hsplit:∑ p∈S,(1:E)/(p:E)^2 = (∑ p∈S_small,(1:E)/(p:E)^2)+(∑ p∈S_big,(1:E)/(p:E)^2):=by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p=>p<=7)];congr 1;apply sum_congr _ (fun _ _=>rfl);ext p;simp [S_big]
 have hsmall_sub:S_small⊆({2,3,5,7}:Finset ℕ):=by
  intro p hp;have hfl:=mem_filter.mp hp;have hpr:=hS p hfl.1;have hle:=hfl.2
  interval_cases p <;> first | decide | (exfalso;revert hpr;decide)
 have hsmall_le:∑ p∈S_small,(1:E)/(p:E)^2 ≤ 1/4+1/9+1/25+1/49:=by
  calc
   ∑ p∈S_small,(1:E)/(p:E)^2
     ≤ ∑ p∈({2,3,5,7}:Finset ℕ),(1:E)/(p:E)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsmall_sub (fun _ _ _=>by positivity)
   _ = 1/4+1/9+1/25+1/49:=by norm_num
 have hbig_le:∑ p∈S_big,(1:E)/(p:E)^2<=1/14:=by
  by_cases hne:S_big.Nonempty
  ·
   let N:=S_big.max' hne;let odds:Finset ℕ:=(Finset.Icc 4 (N/2)).image (fun k=>2*k+1)
   have hbig_sub:S_big⊆odds:=by
    intro p hp;have hfl:=mem_filter.mp hp;have hpr:=hS p hfl.1
    have hodd:p % 2=1:=by
     rcases hpr.eq_two_or_odd with rfl | h
     · omega
     · exact h
    have hleN:p<=N:=Finset.le_max' S_big p hp;refine Finset.mem_image.mpr ⟨p/2,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
   have hsum1:∑ p∈S_big,(1:E)/(p:E)^2<=∑ p∈odds,(1:E)/(p:E)^2 :=Finset.sum_le_sum_of_subset_of_nonneg hbig_sub (fun _ _ _=>by positivity);have hinj:Function.Injective (fun k:ℕ=>2*k+1):=fun a b h=>by dsimp only at h;omega
   have hsum2:∑ p∈odds,(1:E)/(p:E)^2 = ∑ k∈Finset.Icc 4 (N/2),(1:E)/((2*k+1:ℕ):E)^2 :=Finset.sum_image (fun a _ b _ h=>hinj h)
   have htele_step:∀ k∈Finset.Icc 4 (N/2),(1:E)/((2*k+1:ℕ):E)^2 ≤ (1/2:E)*(1/(2*(k:E)-1)-1/(2*(k:E)+1)):=by
    intro k hk;have hk4:(4:E)<=(k:E):=by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have h1:(0:E) < 2*(k:E)-1:=by linarith
    have h2:(0:E) < 2*(k:E)+1:=by linarith
    have hrhs:(1/2:E)*(1/(2*(k:E)-1)-1/(2*(k:E)+1)) = 1/((2*(k:E)-1)*(2*(k:E)+1)):=by field_simp [h1.ne',h2.ne'];ring
    rw [hrhs];push_cast;exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
   have htele_sum:∀ m:ℕ,4<=m → ∑ k∈Finset.Icc 4 m,(1/2:E)*(1/(2*(k:E)-1)-1/(2*(k:E)+1)) = (1/2:E)*(1/7-1/(2*(m:E)+1)):=by
    intro m hm
    induction m,hm using Nat.le_induction with
    | base=>norm_num
    | succ n hn ih =>
     have hIcc:Finset.Icc 4 (n+1)=insert (n+1) (Finset.Icc 4 n):=by ext x;simp only [Finset.mem_Icc,Finset.mem_insert];omega
     rw [hIcc,Finset.sum_insert (by simp),ih];push_cast;ring
   have hN4:4<=N/2:=by
    rcases hne with ⟨p,hp⟩;have hle:=Finset.le_max' S_big p hp;have hgt:=(mem_filter.mp hp).2;omega
   have hsum3:∑ k∈Finset.Icc 4 (N/2),(1:E)/((2*k+1:ℕ):E)^2 ≤ (1/2:E)*(1/7-1/(2*((N/2:ℕ):E)+1)):=by
    calc
     _ <= ∑ k∈Finset.Icc 4 (N/2),(1/2:E)*(1/(2*(k:E)-1)-1/(2*(k:E)+1)) :=sum_le_sum htele_step
     _ = (1/2:E)*(1/7-1/(2*((N/2:ℕ):E)+1)):=htele_sum (N/2) hN4
   have hpos_last:(0:E)<=1/(2*((N/2:ℕ):E)+1):=by positivity
   linarith
  ·
   rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty];norm_num
 linarith
lemma card_dvd_in_Ioo_le (v H d:ℕ) (hd:0 < d) :
  (((Finset.Ioo 0 H).filter (fun j=>d∣v+j)).card:E)<=(H:E)/(d:E)+1:=by
 let S:=(Finset.Ioo 0 H).filter (fun j=>d∣v+j)
 by_cases hne:S.Nonempty
 ·
  let j0:=S.min' hne;have hj0_mem:j0∈S:=Finset.min'_mem S hne;have hj0_dvd:d∣v+j0:=(mem_filter.mp hj0_mem).2;let f:ℕ->ℕ:=fun j=>(j-j0)/d
  have hf_inj:Set.InjOn f S:=by
   intro a ha b hb heq;have ha_ge:j0<=a:=Finset.min'_le S a ha;have hb_ge:j0<=b:=Finset.min'_le S b hb
   have ha_dvd:d∣a-j0:=by
    have h1:d∣v+a:=(mem_filter.mp ha).2
    have:v+a=(v+j0)+(a-j0):=by omega
    exact (Nat.dvd_add_right hj0_dvd).mp (this ▸ h1)
   have hb_dvd:d∣b-j0:=by
    have h1:d∣v+b:=(mem_filter.mp hb).2
    have:v+b=(v+j0)+(b-j0):=by omega
    exact (Nat.dvd_add_right hj0_dvd).mp (this ▸ h1)
   have h1:d*f a=a-j0:=Nat.mul_div_cancel' ha_dvd;have h2:d*f b=b-j0:=Nat.mul_div_cancel' hb_dvd;rw [heq] at h1;omega
  have hf_sub:S.image f⊆Finset.range (H/d+1):=by
   intro y hy;rcases Finset.mem_image.mp hy with ⟨j,hj,rfl⟩;have hj_lt:j < H:=(Finset.mem_Ioo.mp (mem_filter.mp hj).1).2;rw [Finset.mem_range]
   have:(j-j0)/d<=H/d:=Nat.div_le_div_right (by omega)
   dsimp [f];omega
  have hcard:S.card<=H/d+1:=by
   calc
    S.card=(S.image f).card:=(Finset.card_image_iff.mpr hf_inj).symm
    _ <= (Finset.range (H/d+1)).card:=Finset.card_le_card hf_sub
    _ = H/d+1:=card_range _
  have hdR:(0:E) < (d:E):=by exact_mod_cast hd
  have hdiv:((H/d:ℕ):E)<=(H:E)/(d:E):=by
   rw [le_div_iff₀ hdR];exact_mod_cast Nat.div_mul_le_self H d
  have hcast:(S.card:E)<=((H/d:ℕ):E)+1:=by exact_mod_cast hcard
  linarith
 ·
  change (S.card:E)<=(H:E)/(d:E)+1;rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero];positivity
lemma card_small_prime_sq_lt (v H:ℕ) (hH:16<=H) :
  (((Finset.Ioo 0 H).filter (fun j=>∃ p,p < H/4/\Nat.Prime p/\p^2∣v+j)).card:E) <
   (3/4:E)*(H:E):=by
 let P:=(Finset.range (H/4)).filter Nat.Prime
 have hsub:(Finset.Ioo 0 H).filter (fun j=>∃ p,p < H/4/\Nat.Prime p/\p^2∣v+j) ⊆
   P.biUnion (fun p=>(Finset.Ioo 0 H).filter (fun j=>p^2∣v+j)):=by
  intro j hj;rcases mem_filter.mp hj with ⟨hjIoo,p,hp_lt,hp_pr,hp_dvd⟩;exact Finset.mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨Finset.mem_range.mpr hp_lt,hp_pr⟩,mem_filter.mpr ⟨hjIoo,hp_dvd⟩⟩
 have h1:(((Finset.Ioo 0 H).filter (fun j=>∃ p,p < H/4/\Nat.Prime p/\p^2∣v+j)).card:E) ≤ ∑ p∈P,(((Finset.Ioo 0 H).filter (fun j=>p^2∣v+j)).card:E):=by
  have hnat:=(Finset.card_le_card hsub).trans Finset.card_biUnion_le;exact_mod_cast hnat
 have h2:∑ p∈P,(((Finset.Ioo 0 H).filter (fun j=>p^2∣v+j)).card:E) ≤ ∑ p∈P,((H:E)/(p:E)^2+1):=by
  apply sum_le_sum;intro p hp;have hp_pos:0 < p^2:=pow_pos (mem_filter.mp hp).2.pos 2;have h:=card_dvd_in_Ioo_le v H (p^2) hp_pos;simpa [Nat.cast_pow] using h
 have h3:∑ p∈P,((H:E)/(p:E)^2+1) = (H:E)*(∑ p∈P,(1:E)/(p:E)^2)+(P.card:E):=by
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,Finset.mul_sum];congr 1;apply sum_congr rfl;intro p _;ring
 have hsum_half:∑ p∈P,(1:E)/(p:E)^2 < 1/2 :=sum_inv_prime_sq_lt_half P (fun p hp=>(mem_filter.mp hp).2)
 have hP_card:(P.card:E)<=(H:E)/4:=by
  have hnat:P.card<=H/4:=by
   calc
    P.card<=(Finset.range (H/4)).card:=Finset.card_filter_le _ _
    _ = H/4:=card_range _
  have hdiv:((H/4:ℕ):E)<=(H:E)/4:=by
   rw [le_div_iff₀ (by norm_num:(0:E) < 4)];exact_mod_cast Nat.div_mul_le_self H 4
  exact (by exact_mod_cast hnat:(P.card:E)<=((H/4:ℕ):E)).trans hdiv
 have hH_pos:(0:E) < (H:E):=by exact_mod_cast (show 0 < H by omega)
 have hmul:(H:E)*(∑ p∈P,(1:E)/(p:E)^2) < (H:E)*(1/2) :=mul_lt_mul_of_pos_left hsum_half hH_pos;linarith
lemma exists_squarefree_of_small_v (v H:ℕ) (hH:16<=H) (hvH:v+H<=(H/4)^2) :
  ∃ j∈Finset.Ioo 0 H,Squarefree (v+j):=by
 by_contra hnone
 push Not at hnone
 have hcover:Finset.Ioo 0 H ⊆
   (Finset.Ioo 0 H).filter (fun j=>∃ p,p < H/4/\Nat.Prime p/\p^2∣v+j):=by
  intro j hj;refine mem_filter.mpr ⟨hj,?_⟩;have hj_pos:0 < j:=(Finset.mem_Ioo.mp hj).1;have hj_lt:j < H:=(Finset.mem_Ioo.mp hj).2;have hnsq:=hnone j hj;rw [Nat.squarefree_iff_prime_squarefree] at hnsq
  push Not at hnsq
  obtain ⟨p,hp_pr,hp_dvd⟩:=hnsq;have hp_sq_dvd:p^2∣v+j:=by simpa [sq] using hp_dvd
  have hp_le:p^2<=v+j:=Nat.le_of_dvd (by omega) hp_sq_dvd
  have hp_lt:p < H/4:=by
   by_contra hge
   have:(H/4)^2<=p^2:=Nat.pow_le_pow_left (by omega) 2
   omega
  exact ⟨p,hp_lt,hp_pr,hp_sq_dvd⟩
 have hcard_le:((Finset.Ioo 0 H).card:E) ≤ (((Finset.Ioo 0 H).filter (fun j=>∃ p,p < H/4/\Nat.Prime p/\p^2∣v+j)).card:E):=by exact_mod_cast Finset.card_le_card hcover
 have hIoo_card:((Finset.Ioo 0 H).card:E)=(H:E)-1:=by
  rw [Nat.card_Ioo,Nat.sub_zero]
  have:(1:ℕ)<=H:=by omega
  rw [Nat.cast_sub this,Nat.cast_one]
 have hlt:=card_small_prime_sq_lt v H hH;have hHR:(16:E)<=(H:E):=by exact_mod_cast hH
 linarith
def dyadicPrimeSet (v H D:ℕ):Finset ℕ :=(Finset.Ico D (2*D)).filter (fun p=>Nat.Prime p/\∃ j∈Finset.Ioo 0 H,p^2∣v+j)
lemma card_dyadic_covered_le (v H D:ℕ) (hDH:H<=D^2) :
  ((Finset.Ioo 0 H).filter (fun j=>∃ p∈Finset.Ico D (2*D),Nat.Prime p/\p^2∣v+j)).card ≤ (dyadicPrimeSet v H D).card:=by
 classical
 let J:=(Finset.Ioo 0 H).filter (fun j=>∃ p∈Finset.Ico D (2*D),Nat.Prime p/\p^2∣v+j)
 have hex:∀ j∈J,∃ p∈dyadicPrimeSet v H D,p^2∣v+j:=by
  intro j hj;rcases mem_filter.mp hj with ⟨hjIoo,p,hpIco,hpPr,hpDvd⟩;exact ⟨p,mem_filter.mpr ⟨hpIco,hpPr,j,hjIoo,hpDvd⟩,hpDvd⟩
 let g:ℕ->ℕ:=fun j=>if h:j∈J then Classical.choose (hex j h) else 0
 have hg_mem:∀ j∈J,g j∈dyadicPrimeSet v H D:=by
  intro j hj;simp only [g,hj,↓reduceDIte];exact (Classical.choose_spec (hex j hj)).1
 have hg_dvd:∀ j∈J,(g j)^2∣v+j:=by
  intro j hj;simp only [g,hj,↓reduceDIte];exact (Classical.choose_spec (hex j hj)).2
 have hg_inj:Set.InjOn g J:=by
  intro a ha b hb heq;set p:=g a;have hp_mem:p∈dyadicPrimeSet v H D:=hg_mem a ha;have hp_ge:D<=p:=(Finset.mem_Ico.mp (mem_filter.mp hp_mem).1).1;have hp_sq_ge:H<=p^2:=hDH.trans (Nat.pow_le_pow_left hp_ge 2);have ha_dvd:p^2∣v+a:=hg_dvd a ha
  have hb_dvd:p^2∣v+b:=heq ▸ hg_dvd b hb;have ha_Ioo:=Finset.mem_Ioo.mp (mem_filter.mp ha).1;have hb_Ioo:=Finset.mem_Ioo.mp (mem_filter.mp hb).1;rcases le_total a b with hab | hba
  ·
   have hsub:p^2∣b-a:=by
    have:v+b=(v+a)+(b-a):=by omega
    exact (Nat.dvd_add_right ha_dvd).mp (this ▸ hb_dvd)
   have hlt:b-a < p^2:=by omega
   have h0:b-a=0:=by
    by_contra hne
    exact not_le_of_gt hlt (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hsub)
   omega
  ·
   have hsub:p^2∣a-b:=by
    have:v+a=(v+b)+(a-b):=by omega
    exact (Nat.dvd_add_right hb_dvd).mp (this ▸ ha_dvd)
   have hlt:a-b < p^2:=by omega
   have h0:a-b=0:=by
    by_contra hne
    exact not_le_of_gt hlt (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hsub)
   omega
 calc
  J.card=(J.image g).card:=(Finset.card_image_iff.mpr hg_inj).symm
  _ <= (dyadicPrimeSet v H D).card:=Finset.card_le_card (Finset.image_subset_iff.mpr hg_mem)
lemma dyadicPrimeSet_rangeA_le {v H D:ℕ} (hv:1<=v) (hD:1<=D) (hH:1<=H)
  (hH_le:4*H<=D^2) :
  ((dyadicPrimeSet v H D).card:E) ≤ 3*10^5 * ((v:E)^(1/10:E)*(D:E)^(2/5:E) + (D:E)^(2/3:E)*(H:E)^(1/6:E) + (H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E)+1):=by
 classical
 let target:=(Finset.Icc (D:ℤ) (2*(D:ℤ))).filter (fun (d:ℤ) =>
  ∃ m:ℤ,|((v:E)-(m:E)*(d:E)^2)| < (H:E))
 have hsub:(dyadicPrimeSet v H D).image (fun p:ℕ=>(p:ℤ))⊆target:=by
  intro d hd;rcases Finset.mem_image.mp hd with ⟨p,hp,rfl⟩;rcases mem_filter.mp hp with ⟨hpIco,_,j,hjIoo,m,hm⟩;have hp_bounds:=Finset.mem_Ico.mp hpIco;have hj_bounds:=Finset.mem_Ioo.mp hjIoo
  refine mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,(m:ℤ),?_⟩
  have heq:(v:E)-(m:E)*(p:E)^2=-(j:E):=by
   have:(v:E)+(j:E)=(p:E)^2*(m:E):=by exact_mod_cast hm
   linarith
  push_cast;rw [heq,abs_neg,abs_of_pos (by exact_mod_cast hj_bounds.1)];exact_mod_cast hj_bounds.2
 have hcard:((dyadicPrimeSet v H D).card:E)<=(target.card:E):=by
  have h1:(dyadicPrimeSet v H D).card=((dyadicPrimeSet v H D).image (fun p:ℕ=>(p:ℤ))).card :=(Finset.card_image_of_injective _ Nat.cast_injective).symm;exact_mod_cast h1 ▸ Finset.card_le_card hsub
 exact hcard.trans (nearCurve_inv_sq_card_le hv hD hH hH_le)
lemma inv_sq_cubic_diff_id (p a:E) (hp:p≠0) (hpa:p+a≠0) :
  -(2*p-a)/p^2+(2*p+3*a)/(p+a)^2=a^3/(p^2*(p+a)^2):=by
 field_simp [hp,hpa];ring
lemma dyadicPrimeSet_rangeC_le {v H D:ℕ} (hv:1<=v) (hD:1<=D) (hH:1<=H)
  (hHD:14*H < D) (hvD:8*(v+H) < D^3) :
  ((dyadicPrimeSet v H D).card:E)<=(2*(v:E)/(D:E))^(1/3:E)+1:=by
 let S:=dyadicPrimeSet v H D;let t:=S.card
 by_cases ht:t<=1
 ·
  have:(S.card:E)<=1:=by exact_mod_cast ht
  linarith [rpow_nonneg (by positivity:(0:E)<=2*(v:E)/(D:E)) (1/3:E)]
 ·
  let emb:=S.orderEmbOfFin rfl;have hvR:(0:E) < (v:E):=by exact_mod_cast hv
  have hDR:(0:E) < (D:E):=by exact_mod_cast hD
  have hgap:∀ i:ℕ,(hi:i+1 < t) → ((D:E)^4/(2*(v:E)))^(1/3:E) ≤ ((emb ⟨i+1,hi⟩:E)-(emb ⟨i,by omega⟩:E)):=by
   intro i hi;set p1:ℕ:=emb ⟨i,by omega⟩;set p2:ℕ:=emb ⟨i+1,hi⟩;have hp1_mem:p1∈S:=Finset.orderEmbOfFin_mem S rfl ⟨i,by omega⟩;have hp2_mem:p2∈S:=Finset.orderEmbOfFin_mem S rfl ⟨i+1,hi⟩;have hp1_lt:p1 < p2:=emb.strictMono (by show i < i+1;omega);set a:ℕ:=p2-p1
   have ha_pos:0 < a:=by omega
   have hp2_eq:p2=p1+a:=by omega
   rcases mem_filter.mp hp1_mem with ⟨hp1_ico,hp1_pr,j1,hj1_ioo,m1,hm1⟩;rcases mem_filter.mp hp2_mem with ⟨hp2_ico,_,j2,hj2_ioo,m2,hm2⟩;have hp1_ge:D<=p1:=(Finset.mem_Ico.mp hp1_ico).1;have hp2_lt:p2 < 2*D:=(Finset.mem_Ico.mp hp2_ico).2
   have ha_lt_p1:a < p1:=by omega
   let I:ℤ:=-((2*(p1:ℤ)-(a:ℤ))*(m1:ℤ))+(2*(p1:ℤ)+3*(a:ℤ))*(m2:ℤ)
   have hI_ne:I≠0:=by
    intro hI0
    have hdvd_Z:(p1:ℤ)∣(a:ℤ)*((m1:ℤ)+3*(m2:ℤ)):=by
     refine ⟨2*((m1:ℤ)-(m2:ℤ)),?_⟩;dsimp [I] at hI0;linarith
    have hdvd_N:p1∣a*(m1+3*m2):=by
     have:((p1:ℕ):ℤ)∣((a*(m1+3*m2):ℕ):ℤ):=by push_cast;exact hdvd_Z
     exact Int.ofNat_dvd.mp this
    rcases hp1_pr.dvd_mul.mp hdvd_N with hpa | hpm
    · exact not_le_of_gt ha_lt_p1 (Nat.le_of_dvd ha_pos hpa)
    ·
     have hm1_pos:0 < m1:=by
      by_contra h0;simp only [Nat.not_lt,Nat.le_zero] at h0
      rw [h0,mul_zero] at hm1;have:=(Finset.mem_Ioo.mp hj1_ioo).1;omega
     have hm1_le:m1*D^2<=v+H:=by
      calc
       m1*D^2<=m1*p1^2:=Nat.mul_le_mul_left m1 (Nat.pow_le_pow_left hp1_ge 2)
       _ = p1^2*m1:=mul_comm _ _
       _ = v+j1:=hm1.symm
       _ <= v+H:=by have:=(Finset.mem_Ioo.mp hj1_ioo).2;omega
     have hm2_le:m2*D^2<=v+H:=by
      calc
       m2*D^2<=m2*p2^2:=Nat.mul_le_mul_left m2 (Nat.pow_le_pow_left (by omega) 2)
       _ = p2^2*m2:=mul_comm _ _
       _ = v+j2:=hm2.symm
       _ <= v+H:=by have:=(Finset.mem_Ioo.mp hj2_ioo).2;omega
     have hsum_lt:m1+3*m2 < p1:=by
      have hmul:(m1+3*m2)*D^2<=4*(v+H):=by nlinarith
      have hltD:(m1+3*m2)*D^2 < D*D^2:=by
       calc
        (m1+3*m2)*D^2<=4*(v+H):=hmul
        _ < D^3:=by omega
        _ = D*D^2:=by ring
      have hlt1:m1+3*m2 < D:=Nat.lt_of_mul_lt_mul_right hltD;omega
     exact not_le_of_gt hsum_lt (Nat.le_of_dvd (by omega) hpm)
   have hI_ge1:(1:E) ≤ |(I:E)|:=by
    have:(1:ℤ) ≤ |I|:=Int.one_le_abs hI_ne
    exact_mod_cast this
   have hp1R_pos:(0:E) < (p1:E):=by exact_mod_cast (show 0 < p1 by omega)
   have hp2R_pos:(0:E) < (p2:E):=by exact_mod_cast (show 0 < p2 by omega)
   have hp2R_eq:(p2:E)=(p1:E)+(a:E):=by exact_mod_cast hp2_eq
   have hm1R:(m1:E)=((v:E)+(j1:E))/(p1:E)^2:=by
    have h:(v:E)+(j1:E)=(p1:E)^2*(m1:E):=by exact_mod_cast hm1
    field_simp [hp1R_pos.ne'];linarith
   have hm2R:(m2:E)=((v:E)+(j2:E))/((p1:E)+(a:E))^2:=by
    have h:(v:E)+(j2:E)=((p1:E)+(a:E))^2*(m2:E):=by rw [← hp2R_eq];exact_mod_cast hm2
    field_simp [(hp2R_eq ▸ hp2R_pos).ne'];linarith
   have hI_decomp:(I:E) = (v:E)*(a:E)^3/((p1:E)^2*((p1:E)+(a:E))^2) + (-(2*(p1:E)-(a:E))*(j1:E)/(p1:E)^2 + (2*(p1:E)+3*(a:E))*(j2:E)/((p1:E)+(a:E))^2):=by
    have hcastI:(I:E)=-(2*(p1:E)-(a:E))*(m1:E) + (2*(p1:E)+3*(a:E))*(m2:E):=by dsimp [I];push_cast;ring
    rw [hcastI,hm1R,hm2R];have hid:=inv_sq_cubic_diff_id (p1:E) (a:E) hp1R_pos.ne' (hp2R_eq ▸ hp2R_pos).ne';have hmul:=congrArg (fun z=>(v:E)*z) hid;ring_nf at hmul ⊢;linarith
   have hmain_le:|(v:E)*(a:E)^3/((p1:E)^2*((p1:E)+(a:E))^2)| ≤ (v:E)*(a:E)^3/(D:E)^4:=by
    rw [abs_of_nonneg (by positivity)];have hp1D:(D:E)<=(p1:E):=by exact_mod_cast hp1_ge
    have hp2D:(D:E)<=(p1:E)+(a:E):=by rw [← hp2R_eq];exact_mod_cast (show D<=p2 by omega)
    have hden:(D:E)^4<=(p1:E)^2*((p1:E)+(a:E))^2:=by
     calc
      (D:E)^4=(D:E)^2*(D:E)^2:=by ring
      _ <= (p1:E)^2*((p1:E)+(a:E))^2 :=mul_le_mul (pow_le_pow_left₀ hDR.le hp1D 2) (pow_le_pow_left₀ hDR.le hp2D 2) (by positivity) (by positivity)
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hDR 4) hden
   have herr_lt:|-(2*(p1:E)-(a:E))*(j1:E)/(p1:E)^2 + (2*(p1:E)+3*(a:E))*(j2:E)/((p1:E)+(a:E))^2| < 1/2:=by
    have hp1D:(D:E)<=(p1:E):=by exact_mod_cast hp1_ge
    have ha_le:(a:E)<=(p1:E):=by exact_mod_cast ha_lt_p1.le
    have hj1_le:(j1:E)<=(H:E):=by exact_mod_cast (Finset.mem_Ioo.mp hj1_ioo).2.le
    have hj2_le:(j2:E)<=(H:E):=by exact_mod_cast (Finset.mem_Ioo.mp hj2_ioo).2.le
    have ht1:|-(2*(p1:E)-(a:E))*(j1:E)/(p1:E)^2| ≤ 2*(H:E)/(D:E):=by
     rw [abs_div,abs_mul,abs_neg,abs_of_nonneg (by linarith),abs_of_nonneg (Nat.cast_nonneg j1),abs_of_pos (sq_pos_of_pos hp1R_pos)]
     calc
      (2*(p1:E)-(a:E))*(j1:E)/(p1:E)^2
        ≤ (2*(p1:E))*(H:E)/(p1:E)^2:=by
       apply div_le_div_of_nonneg_right _ (sq_nonneg _);exact mul_le_mul (by linarith [(Nat.cast_nonneg a:(0:E)<=(a:E))]) hj1_le (Nat.cast_nonneg j1) (by positivity)
      _ = 2*(H:E)/(p1:E):=by field_simp [hp1R_pos.ne']
      _ <= 2*(H:E)/(D:E):=div_le_div_of_nonneg_left (by positivity) hDR hp1D
    have ht2:|(2*(p1:E)+3*(a:E))*(j2:E)/((p1:E)+(a:E))^2| ≤ 5*(H:E)/(D:E):=by
     rw [abs_div,abs_mul,abs_of_nonneg (by positivity),abs_of_nonneg (Nat.cast_nonneg j2),abs_of_pos (sq_pos_of_pos (by positivity))]
     calc
      (2*(p1:E)+3*(a:E))*(j2:E)/((p1:E)+(a:E))^2
        ≤ (5*(p1:E))*(H:E)/(p1:E)^2:=by
       have hnum:(2*(p1:E)+3*(a:E))*(j2:E)<=(5*(p1:E))*(H:E) :=mul_le_mul (by linarith) hj2_le (Nat.cast_nonneg j2) (by positivity);have hden:(p1:E)^2<=((p1:E)+(a:E))^2 :=pow_le_pow_left₀ hp1R_pos.le (by linarith [(Nat.cast_nonneg a:(0:E)<=(a:E))]) 2
       calc
        (2*(p1:E)+3*(a:E))*(j2:E)/((p1:E)+(a:E))^2
          ≤ (5*(p1:E))*(H:E)/((p1:E)+(a:E))^2 :=
         div_le_div_of_nonneg_right hnum (by positivity)
        _ <= (5*(p1:E))*(H:E)/(p1:E)^2 :=div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hp1R_pos) hden
      _ = 5*(H:E)/(p1:E):=by field_simp [hp1R_pos.ne']
      _ <= 5*(H:E)/(D:E):=div_le_div_of_nonneg_left (by positivity) hDR hp1D
    have h7HD:7*(H:E)/(D:E) < 1/2:=by
     rw [div_lt_div_iff₀ hDR (by norm_num)]
     have:14*(H:E) < (D:E):=by exact_mod_cast hHD
     linarith
    calc
     _ <= |-(2*(p1:E)-(a:E))*(j1:E)/(p1:E)^2| +
       |(2*(p1:E)+3*(a:E))*(j2:E)/((p1:E)+(a:E))^2|:=abs_add_le _ _
     _ <= 2*(H:E)/(D:E)+5*(H:E)/(D:E):=add_le_add ht1 ht2
     _ = 7*(H:E)/(D:E):=by ring
     _ < 1/2:=h7HD
   have hmain_ge:1/2<=(v:E)*(a:E)^3/(D:E)^4:=by
    have htri:|(I:E)| ≤ |(v:E)*(a:E)^3/((p1:E)^2*((p1:E)+(a:E))^2)| +
      |-(2*(p1:E)-(a:E))*(j1:E)/(p1:E)^2 + (2*(p1:E)+3*(a:E))*(j2:E)/((p1:E)+(a:E))^2|:=by
     rw [hI_decomp];exact abs_add_le _ _
    linarith
   have ha3:(D:E)^4/(2*(v:E))<=(a:E)^3:=by
    rw [div_le_iff₀ (by positivity)];have h1:=(le_div_iff₀ (pow_pos hDR 4)).mp hmain_ge;linarith
   have hrp:=rpow_le_rpow (by positivity) ha3 (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (a:E) 3,← rpow_mul (Nat.cast_nonneg a)] at hrp;norm_num at hrp;have hdiff:(p2:E)-(p1:E)=(a:E):=by rw [hp2R_eq];ring
   rwa [hdiff]
  let eAt:ℕ->E:=fun i=>if hi:i < t then (emb ⟨i,hi⟩:E) else 0
  have htele:∑ i∈Finset.range (t-1),(eAt (i+1)-eAt i)=eAt (t-1)-eAt 0:=by
   have hgen:∀ k:ℕ,∑ i∈Finset.range k,(eAt (i+1)-eAt i)=eAt k-eAt 0:=by
    intro k
    induction k with
    | zero=>simp
    | succ k ih=>rw [sum_range_succ,ih];ring
   exact hgen (t-1)
  have hspan:eAt (t-1)-eAt 0<=(D:E):=by
   have h1:t-1 < t:=by omega
   have h0:0 < t:=by omega
   have hhi:=(Finset.mem_Ico.mp (mem_filter.mp (Finset.orderEmbOfFin_mem S rfl ⟨t-1,h1⟩)).1).2;have hlo:=(Finset.mem_Ico.mp (mem_filter.mp (Finset.orderEmbOfFin_mem S rfl ⟨0,h0⟩)).1).1;have hhiR:(emb ⟨t-1,h1⟩:E)<=2*(D:E):=by exact_mod_cast hhi.le
   have hloR:(D:E)<=(emb ⟨0,h0⟩:E):=by exact_mod_cast hlo
   rw [show eAt (t-1)=(emb ⟨t-1,h1⟩:E) from dif_pos h1,show eAt 0=(emb ⟨0,h0⟩:E) from dif_pos h0];linarith
  have hprod:((t-1:ℕ):E)*((D:E)^4/(2*(v:E)))^(1/3:E)<=(D:E):=by
   calc
    ((t-1:ℕ):E)*((D:E)^4/(2*(v:E)))^(1/3:E)
      = ∑ _i∈Finset.range (t-1),((D:E)^4/(2*(v:E)))^(1/3:E):=by simp
    _ <= ∑ i∈Finset.range (t-1),(eAt (i+1)-eAt i):=by
     apply sum_le_sum;intro i hi;have hi_lt:i+1 < t:=by have:=Finset.mem_range.mp hi;omega
     have hi0:i < t:=by omega
     rw [show eAt (i+1)=(emb ⟨i+1,hi_lt⟩:E) from dif_pos hi_lt,show eAt i=(emb ⟨i,hi0⟩:E) from dif_pos hi0];exact hgap i hi_lt
    _ = eAt (t-1)-eAt 0:=htele
    _ <= (D:E):=hspan
  have hstep_pos:0 < ((D:E)^4/(2*(v:E)))^(1/3:E):=rpow_pos_of_pos (by positivity) _;have ht1_le:((t-1:ℕ):E)<=(D:E)/((D:E)^4/(2*(v:E)))^(1/3:E) :=(le_div_iff₀ hstep_pos).mpr hprod
  have hsimp:(D:E)/((D:E)^4/(2*(v:E)))^(1/3:E) = (2*(v:E)/(D:E))^(1/3:E):=by
   rw [div_rpow (by positivity) (by positivity),div_rpow (by positivity) hDR.le,← rpow_natCast (D:E) 4,← rpow_mul hDR.le]
   have hD_pow:(D:E)^(1/3:E)*(D:E)=(D:E)^(((4:ℕ):E)*(1/3:E)):=by
    conv_lhs=>arg 2;rw [← rpow_one (D:E)]
    rw [← rpow_add hDR];push_cast;norm_num
   field_simp [(rpow_pos_of_pos (by positivity:(0:E) < 2*(v:E)) (1/3:E)).ne',(rpow_pos_of_pos hDR (1/3:E)).ne',(rpow_pos_of_pos hDR (((4:ℕ):E)*(1/3:E))).ne']
   calc
    (D:E)*(D:E)^(1/3:E)=(D:E)^(1/3:E)*(D:E):=mul_comm _ _
    _ = (D:E)^(((4:ℕ):E)*(1/3:E)):=hD_pow
    _ = (D:E)^((4:E)/3):=by push_cast;congr 1;ring
  rw [hsimp] at ht1_le
  have ht_eq:(S.card:E)=((t-1:ℕ):E)+1:=by
   have h1:1<=t:=by omega
   change (t:E)=((t-1:ℕ):E)+1;rw [Nat.cast_sub h1,Nat.cast_one];ring
  linarith
lemma inv_sq_second_diff_id (d a b:E) (hd:d≠0) (hda:d+a≠0) (hdb:d+b≠0) :
  (b-a)/d^2-b/(d+a)^2+a/(d+b)^2 = a*b*(b-a)*(3*d^2+2*d*(a+b)+a*b) / (d^2*(d+a)^2*(d+b)^2):=by
 field_simp [hd,hda,hdb];ring
lemma dividedDiff_four_pair (d0 a b:E) (f:E->E)
  (ha:a≠0) (hb:b≠0) (hba:b-a≠0) (hbpa:b+a≠0) :
  a*b*(b-a)*(b+a) * dividedDiff ![d0,d0+a,d0+b,d0+b+a] (f ∘ ![d0,d0+a,d0+b,d0+b+a]) = -(b-a)*f d0+(b+a)*f (d0+a)-(b+a)*f (d0+b)+(b-a)*f (d0+b+a):=by
 let xs:Fin 4->E:=![d0,d0+a,d0+b,d0+b+a];change a*b*(b-a)*(b+a)*dividedDiff xs (f ∘ xs)=_;unfold dividedDiff;rw [Fin.sum_univ_four];have he0:(Finset.univ.erase (0:Fin 4))={1,2,3}:=by decide
 have he1:(Finset.univ.erase (1:Fin 4))={0,2,3}:=by decide
 have he2:(Finset.univ.erase (2:Fin 4))={0,1,3}:=by decide
 have he3:(Finset.univ.erase (3:Fin 4))={0,1,2}:=by decide
 rw [he0,he1,he2,he3];have hp0:∏ i∈({1,2,3}:Finset (Fin 4)),(xs 0-xs i) = (xs 0-xs 1)*((xs 0-xs 2)*(xs 0-xs 3)):=by rw [Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton]
 have hp1:∏ i∈({0,2,3}:Finset (Fin 4)),(xs 1-xs i) = (xs 1-xs 0)*((xs 1-xs 2)*(xs 1-xs 3)):=by rw [Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton]
 have hp2:∏ i∈({0,1,3}:Finset (Fin 4)),(xs 2-xs i) = (xs 2-xs 0)*((xs 2-xs 1)*(xs 2-xs 3)):=by rw [Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton]
 have hp3:∏ i∈({0,1,2}:Finset (Fin 4)),(xs 3-xs i) = (xs 3-xs 0)*((xs 3-xs 1)*(xs 3-xs 2)):=by rw [Finset.prod_insert (by decide),Finset.prod_insert (by decide),Finset.prod_singleton]
 rw [hp0,hp1,hp2,hp3];have h0:xs 0=d0:=rfl;have h1:xs 1=d0+a:=rfl;have h2:xs 2=d0+b:=rfl;have h3:xs 3=d0+b+a:=rfl;simp only [Function.comp_apply,h0,h1,h2,h3];have hne1:d0-(d0+a)≠0:=by intro h;apply ha;linarith
 have hne2:d0-(d0+b)≠0:=by intro h;apply hb;linarith
 have hne3:d0-(d0+b+a)≠0:=by intro h;apply hbpa;linarith
 have hne4:d0+a-d0≠0:=by intro h;apply ha;linarith
 have hne5:d0+a-(d0+b)≠0:=by intro h;apply hba;linarith
 have hne6:d0+a-(d0+b+a)≠0:=by intro h;apply hb;linarith
 have hne7:d0+b-d0≠0:=by intro h;apply hb;linarith
 have hne8:d0+b-(d0+a)≠0:=by intro h;apply hba;linarith
 have hne9:d0+b-(d0+b+a)≠0:=by intro h;apply ha;linarith
 have hne10:d0+b+a-d0≠0:=by intro h;apply hbpa;linarith
 have hne11:d0+b+a-(d0+a)≠0:=by intro h;apply hb;linarith
 have hne12:d0+b+a-(d0+b)≠0:=by intro h;apply ha;linarith
 field_simp [hne1,hne2,hne3,hne4,hne5,hne6,hne7,hne8,hne9,hne10,hne11,hne12];ring
set_option maxHeartbeats 1200000 in
lemma dyadicPrimeSet_second_diff_gap {v H D:ℕ} (d0 d1 d2:ℕ)
  (hv:1<=v) (hD:1<=D) (hH:1<=H) (hHD2:256*H*D^2 < 3*v)
  (hd0:d0∈dyadicPrimeSet v H D) (hd1:d1∈dyadicPrimeSet v H D)
  (hd2:d2∈dyadicPrimeSet v H D) (h01:d0 < d1) (h12:d1 < d2) :
  ((D:E)^4/(22*(v:E)))^(1/3:E)<=(d2:E)-(d0:E):=by
 have hvR:(0:E) < (v:E):=by exact_mod_cast hv
 have hDR:(0:E) < (D:E):=by exact_mod_cast hD
 have hHR:(0:E) < (H:E):=by exact_mod_cast hH
 rcases (mem_filter.mp hd0).2.2 with ⟨j0,hj0_ioo,m0,hm0⟩;rcases (mem_filter.mp hd1).2.2 with ⟨j1,hj1_ioo,m1,hm1⟩;rcases (mem_filter.mp hd2).2.2 with ⟨j2,hj2_ioo,m2,hm2⟩;set a:ℕ:=d1-d0;set b:ℕ:=d2-d0;have ha_pos:1<=a:=by omega
 have hba_pos:1<=b-a:=by omega
 have hd1_eq:d1=d0+a:=by omega
 have hd2_eq:d2=d0+b:=by omega
 have hd0_lo:D<=d0:=(Finset.mem_Ico.mp (mem_filter.mp hd0).1).1;have hd2_hi:d2 < 2*D:=(Finset.mem_Ico.mp (mem_filter.mp hd2).1).2;let A2:ℤ:=((b-a:ℕ):ℤ)*(m0:ℤ)-(b:ℤ)*(m1:ℤ)+(a:ℤ)*(m2:ℤ);have hd0R:(0:E) < (d0:E):=by exact_mod_cast (show 0 < d0 by omega)
 have hd1R:(0:E) < (d1:E):=by exact_mod_cast (show 0 < d1 by omega)
 have hd2R:(0:E) < (d2:E):=by exact_mod_cast (show 0 < d2 by omega)
 have hm0_eq:(m0:E)=((v:E)+(j0:E))/(d0:E)^2:=by
  have h:(v:E)+(j0:E)=(d0:E)^2*(m0:E):=by exact_mod_cast hm0
  field_simp [hd0R.ne'];linarith
 have hm1_eq:(m1:E)=((v:E)+(j1:E))/(d1:E)^2:=by
  have h:(v:E)+(j1:E)=(d1:E)^2*(m1:E):=by exact_mod_cast hm1
  field_simp [hd1R.ne'];linarith
 have hm2_eq:(m2:E)=((v:E)+(j2:E))/(d2:E)^2:=by
  have h:(v:E)+(j2:E)=(d2:E)^2*(m2:E):=by exact_mod_cast hm2
  field_simp [hd2R.ne'];linarith
 have hd1R_eq:(d1:E)=(d0:E)+(a:E):=by exact_mod_cast hd1_eq
 have hd2R_eq:(d2:E)=(d0:E)+(b:E):=by exact_mod_cast hd2_eq
 have hbaR_eq:((b-a:ℕ):E)=(b:E)-(a:E):=by rw [Nat.cast_sub (by omega)]
 let main2:E:=(v:E)*((a:E)*(b:E)*((b:E)-(a:E)) * (3*(d0:E)^2+2*(d0:E)*((a:E)+(b:E))+(a:E)*(b:E)) / ((d0:E)^2*(d1:E)^2*(d2:E)^2))
 let err2:E:=((b:E)-(a:E))*(j0:E)/(d0:E)^2 -
   (b:E)*(j1:E)/(d1:E)^2+(a:E)*(j2:E)/(d2:E)^2
 have hA2_eq:(A2:E)=main2+err2:=by
  have hcast:(A2:E)=((b:E)-(a:E))*(m0:E)-(b:E)*(m1:E)+(a:E)*(m2:E):=by dsimp [A2];push_cast;rw [hbaR_eq]
  rw [hcast,hm0_eq,hm1_eq,hm2_eq];have hid:=inv_sq_second_diff_id (d0:E) (a:E) (b:E) hd0R.ne' (hd1R_eq ▸ hd1R).ne' (hd2R_eq ▸ hd2R).ne';rw [← hd1R_eq,← hd2R_eq] at hid
  have hsplit:((b:E)-(a:E))*(((v:E)+(j0:E))/(d0:E)^2) -
    (b:E)*(((v:E)+(j1:E))/(d1:E)^2) +
    (a:E)*(((v:E)+(j2:E))/(d2:E)^2) =
    (v:E)*(((b:E)-(a:E))/(d0:E)^2-(b:E)/(d1:E)^2+(a:E)/(d2:E)^2)+err2:=by
   dsimp [err2];ring
  rw [hsplit,hid]
 have hd0_ge:(D:E)<=(d0:E):=by exact_mod_cast hd0_lo
 have hd1_ge:(D:E)<=(d1:E):=by exact_mod_cast (show D<=d1 by omega)
 have hd2_ge:(D:E)<=(d2:E):=by exact_mod_cast (show D<=d2 by omega)
 have hd0_le:(d0:E)<=2*(D:E):=by exact_mod_cast (show d0<=2*D by omega)
 have hd1_le:(d1:E)<=2*(D:E):=by exact_mod_cast (show d1<=2*D by omega)
 have hd2_le:(d2:E)<=2*(D:E):=by exact_mod_cast hd2_hi.le
 have ha_le:(a:E)<=(D:E):=by exact_mod_cast (show a<=D by omega)
 have hb_le:(b:E)<=(D:E):=by exact_mod_cast (show b<=D by omega)
 have ha_ge1:(1:E)<=(a:E):=by exact_mod_cast ha_pos
 have hba_ge1:(1:E)<=(b:E)-(a:E):=by rw [← hbaR_eq];exact_mod_cast hba_pos
 have hba_nn:(0:E)<=(b:E)-(a:E):=by linarith
 have hmain_lo:3*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(64*(D:E)^4)<=main2:=by
  dsimp [main2]
  have hnum:3*(D:E)^2<=3*(d0:E)^2+2*(d0:E)*((a:E)+(b:E))+(a:E)*(b:E):=by
   nlinarith [sq_nonneg ((d0:E)-(D:E)),mul_nonneg hd0R.le (by positivity:(0:E)<=(a:E)+(b:E)),mul_nonneg (Nat.cast_nonneg a:(0:E)<=(a:E)) (Nat.cast_nonneg b:(0:E)<=(b:E))]
  have hden:(d0:E)^2*(d1:E)^2*(d2:E)^2<=64*(D:E)^6:=by
   have h0:(d0:E)^2<=4*(D:E)^2:=by nlinarith
   have h1:(d1:E)^2<=4*(D:E)^2:=by nlinarith
   have h2:(d2:E)^2<=4*(D:E)^2:=by nlinarith
   have h01:(d0:E)^2*(d1:E)^2<=16*(D:E)^4:=by
    calc
     (d0:E)^2*(d1:E)^2<=(4*(D:E)^2)*(4*(D:E)^2) :=mul_le_mul h0 h1 (sq_nonneg _) (by positivity)
     _ = 16*(D:E)^4:=by ring
   calc
    (d0:E)^2*(d1:E)^2*(d2:E)^2<=(16*(D:E)^4)*(4*(D:E)^2) :=mul_le_mul h01 h2 (sq_nonneg _) (by positivity)
    _ = 64*(D:E)^6:=by ring
  have h1:3*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(64*(D:E)^4) = (v:E)*((a:E)*(b:E)*((b:E)-(a:E))*(3*(D:E)^2)/(64*(D:E)^6)):=by field_simp [hDR.ne']
  rw [h1]
  conv_rhs=>rw [← mul_div_assoc]
  rw [le_div_iff₀ (by positivity)];have hfac_nn:0<=(v:E)*((a:E)*(b:E)*((b:E)-(a:E))):=by positivity
  calc
   (v:E)*((a:E)*(b:E)*((b:E)-(a:E))*(3*(D:E)^2)/(64*(D:E)^6)) * ((d0:E)^2*(d1:E)^2*(d2:E)^2)
     ≤ (v:E)*((a:E)*(b:E)*((b:E)-(a:E))*(3*(D:E)^2)/(64*(D:E)^6)) * (64*(D:E)^6):=mul_le_mul_of_nonneg_left hden (by positivity)
   _ = (v:E)*((a:E)*(b:E)*((b:E)-(a:E)))*(3*(D:E)^2):=by field_simp [hDR.ne']
   _ <= (v:E)*((a:E)*(b:E)*((b:E)-(a:E))) * (3*(d0:E)^2+2*(d0:E)*((a:E)+(b:E))+(a:E)*(b:E)) :=mul_le_mul_of_nonneg_left hnum hfac_nn
   _ = (v:E)*((a:E)*(b:E)*((b:E)-(a:E)) * (3*(d0:E)^2+2*(d0:E)*((a:E)+(b:E))+(a:E)*(b:E))):=by ring
 have hmain_hi:main2<=21*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4:=by
  dsimp [main2]
  have hnum:3*(d0:E)^2+2*(d0:E)*((a:E)+(b:E))+(a:E)*(b:E)<=21*(D:E)^2:=by
   have h0:(d0:E)^2<=4*(D:E)^2:=by nlinarith
   have h1:2*(d0:E)*((a:E)+(b:E))<=8*(D:E)^2:=by nlinarith
   have h2:(a:E)*(b:E)<=(D:E)^2:=by nlinarith
   linarith
  have hden:(D:E)^6<=(d0:E)^2*(d1:E)^2*(d2:E)^2:=by
   have h0:(D:E)^2<=(d0:E)^2:=pow_le_pow_left₀ hDR.le hd0_ge 2;have h1:(D:E)^2<=(d1:E)^2:=pow_le_pow_left₀ hDR.le hd1_ge 2;have h2:(D:E)^2<=(d2:E)^2:=pow_le_pow_left₀ hDR.le hd2_ge 2
   have h01:(D:E)^4<=(d0:E)^2*(d1:E)^2:=by
    calc
     (D:E)^4=(D:E)^2*(D:E)^2:=by ring
     _ <= (d0:E)^2*(d1:E)^2:=mul_le_mul h0 h1 (by positivity) (by positivity)
   calc
    (D:E)^6=(D:E)^4*(D:E)^2:=by ring
    _ <= (d0:E)^2*(d1:E)^2*(d2:E)^2:=mul_le_mul h01 h2 (by positivity) (by positivity)
  calc
   (v:E)*((a:E)*(b:E)*((b:E)-(a:E)) * (3*(d0:E)^2+2*(d0:E)*((a:E)+(b:E))+(a:E)*(b:E)) / ((d0:E)^2*(d1:E)^2*(d2:E)^2))
     ≤ (v:E)*((a:E)*(b:E)*((b:E)-(a:E))*(21*(D:E)^2)/(D:E)^6):=by
    have hdiv:(a:E)*(b:E)*((b:E)-(a:E)) * (3*(d0:E)^2+2*(d0:E)*((a:E)+(b:E))+(a:E)*(b:E)) / ((d0:E)^2*(d1:E)^2*(d2:E)^2) ≤ (a:E)*(b:E)*((b:E)-(a:E))*(21*(D:E)^2)/(D:E)^6:=by
     calc
      _ <= (a:E)*(b:E)*((b:E)-(a:E))*(21*(D:E)^2) / ((d0:E)^2*(d1:E)^2*(d2:E)^2):=by
       apply div_le_div_of_nonneg_right _ (by positivity);exact mul_le_mul_of_nonneg_left hnum (by positivity)
      _ <= _:=div_le_div_of_nonneg_left (by positivity) (pow_pos hDR 6) hden
    exact mul_le_mul_of_nonneg_left hdiv hvR.le
   _ = 21*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4:=by field_simp [hDR.ne']
 have herr_le:|err2| ≤ 2*(b:E)*(H:E)/(D:E)^2:=by
  dsimp [err2];have hj0:(j0:E)<=(H:E):=by exact_mod_cast (Finset.mem_Ioo.mp hj0_ioo).2.le
  have hj1:(j1:E)<=(H:E):=by exact_mod_cast (Finset.mem_Ioo.mp hj1_ioo).2.le
  have hj2:(j2:E)<=(H:E):=by exact_mod_cast (Finset.mem_Ioo.mp hj2_ioo).2.le
  have ht0:|((b:E)-(a:E))*(j0:E)/(d0:E)^2| ≤ ((b:E)-(a:E))*(H:E)/(D:E)^2:=by
   rw [abs_of_nonneg (by positivity)]
   exact div_le_div₀ (by positivity)
    (mul_le_mul_of_nonneg_left hj0 hba_nn) (sq_pos_of_pos hDR) (pow_le_pow_left₀ hDR.le hd0_ge 2)
  have ht1:|(b:E)*(j1:E)/(d1:E)^2| ≤ (b:E)*(H:E)/(D:E)^2:=by
   rw [abs_of_nonneg (by positivity)]
   exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hj1 (Nat.cast_nonneg b))
    (sq_pos_of_pos hDR) (pow_le_pow_left₀ hDR.le hd1_ge 2)
  have ht2:|(a:E)*(j2:E)/(d2:E)^2| ≤ (a:E)*(H:E)/(D:E)^2:=by
   rw [abs_of_nonneg (by positivity)]
   exact div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hj2 (Nat.cast_nonneg a))
    (sq_pos_of_pos hDR) (pow_le_pow_left₀ hDR.le hd2_ge 2)
  have htri1:=abs_add_le (((b:E)-(a:E))*(j0:E)/(d0:E)^2 -
    (b:E)*(j1:E)/(d1:E)^2) ((a:E)*(j2:E)/(d2:E)^2)
  have htri2:=abs_sub (((b:E)-(a:E))*(j0:E)/(d0:E)^2)
    ((b:E)*(j1:E)/(d1:E)^2)
  have hsum:((b:E)-(a:E))*(H:E)/(D:E)^2+(b:E)*(H:E)/(D:E)^2 + (a:E)*(H:E)/(D:E)^2=2*(b:E)*(H:E)/(D:E)^2:=by ring
  linarith
 have herr_lt_half:2*(b:E)*(H:E)/(D:E)^2 <
   (1/2:E)*(3*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(64*(D:E)^4)):=by
  have h1:256*(H:E)*(D:E)^2 < 3*(v:E):=by exact_mod_cast hHD2
  have h2:1<=(a:E)*((b:E)-(a:E)):=by nlinarith
  have h3:256*(H:E)*(D:E)^2 < 3*(v:E)*(a:E)*((b:E)-(a:E)):=by nlinarith
  have hb_pos:(0:E) < (b:E):=by exact_mod_cast (show 0 < b by omega)
  rw [div_lt_iff₀ (sq_pos_of_pos hDR)];have hrhs:(1/2:E)*(3*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(64*(D:E)^4))*(D:E)^2 = 3*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(128*(D:E)^2):=by field_simp [hDR.ne'];ring
  rw [hrhs,lt_div_iff₀ (by positivity)];have h4:=mul_lt_mul_of_pos_right h3 hb_pos;linarith
 have hA2_pos:(0:E) < (A2:E):=by
  have:=(abs_le.mp herr_le).1
  have hM_nn:(0:E)<=3*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(64*(D:E)^4):=by positivity
  linarith
 have hA2_ge1:(1:E)<=(A2:E):=by
  have:(0:ℤ) < A2:=by exact_mod_cast hA2_pos
  exact_mod_cast (show (1:ℤ)<=A2 by omega)
 have hA2_up:(A2:E)<=22*(v:E)*(b:E)^3/(D:E)^4:=by
  have herr_le_main:|err2| ≤ (v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4:=by
   have hnn:(0:E)<=(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4:=by positivity
   have hrat:(1/2:E)*(3*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(64*(D:E)^4)) = (3/128:E)*((v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4):=by ring
   linarith
  have hle1:(A2:E)<=22*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4:=by
   have h21:21*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4 = 21*((v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4):=by ring
   have h22:22*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4 = 22*((v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4):=by ring
   have:=(abs_le.mp herr_le_main).2
   linarith
  have hab_le:(a:E)*(b:E)*((b:E)-(a:E))<=(b:E)^3:=by
   have ha_lt_b:(a:E)<=(b:E):=by exact_mod_cast (show a<=b by omega)
   have hba_le_b:(b:E)-(a:E)<=(b:E):=by linarith [(Nat.cast_nonneg a:(0:E)<=(a:E))]
   calc
    (a:E)*(b:E)*((b:E)-(a:E))
      ≤ (b:E)*(b:E)*(b:E):=by
     have h1:(a:E)*(b:E)<=(b:E)*(b:E):=mul_le_mul_of_nonneg_right ha_lt_b (Nat.cast_nonneg b);exact mul_le_mul h1 hba_le_b hba_nn (by positivity)
    _ = (b:E)^3:=by ring
  calc
   (A2:E)<=22*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))/(D:E)^4:=hle1
   _ <= 22*(v:E)*(b:E)^3/(D:E)^4:=by
    apply div_le_div_of_nonneg_right _ (pow_nonneg hDR.le 4);have hmul:=mul_le_mul_of_nonneg_left hab_le (by positivity:(0:E)<=22*(v:E));have hL:22*(v:E)*(a:E)*(b:E)*((b:E)-(a:E)) = 22*(v:E)*((a:E)*(b:E)*((b:E)-(a:E))):=by ring
    linarith
 have hb3:(D:E)^4/(22*(v:E))<=(b:E)^3:=by
  rw [div_le_iff₀ (by positivity)]
  have:=(le_div_iff₀ (pow_pos hDR 4)).mp (hA2_ge1.trans hA2_up)
  linarith
 have hrp:=rpow_le_rpow (by positivity) hb3 (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (b:E) 3,← rpow_mul (Nat.cast_nonneg b)] at hrp;norm_num at hrp;have hdiff:(d2:E)-(d0:E)=(b:E):=by rw [hd2R_eq];ring
 rwa [hdiff]
set_option maxHeartbeats 800000 in
lemma dyadicPrimeSet_third_diff_step {v H D d0 a b:ℕ}
  (hv:1<=v) (hD:1<=D) (hH:1<=H) (hHD:704*H < D)
  (ha_pos:0 < a) (hb_ge2a:2*a<=b)
  (ha_lb:(1/22:E)<=(v:E)*(a:E)^3/(D:E)^4)
  (hd0_S:d0∈dyadicPrimeSet v H D) (hd0a_S:d0+a∈dyadicPrimeSet v H D)
  (hd2_S:d0+b∈dyadicPrimeSet v H D) (hd2a_S:d0+b+a∈dyadicPrimeSet v H D) :
  ((D:E)^5/(9*(v:E)*(a:E)))^(1/3:E)<=(b:E):=by
 have hvR:(0:E) < (v:E):=by exact_mod_cast hv
 have hDR:(0:E) < (D:E):=by exact_mod_cast hD
 have hHR:(0:E) < (H:E):=by exact_mod_cast hH
 have haR_pos:(0:E) < (a:E):=by exact_mod_cast ha_pos
 rcases (mem_filter.mp hd0_S).2.2 with ⟨j0,hj0_ioo,m0,hm0⟩;rcases (mem_filter.mp hd0a_S).2.2 with ⟨j1,hj1_ioo,m1,hm1⟩;rcases (mem_filter.mp hd2_S).2.2 with ⟨j2,hj2_ioo,m2,hm2⟩;rcases (mem_filter.mp hd2a_S).2.2 with ⟨j3,hj3_ioo,m3,hm3⟩
 let xs:Fin 4->E:=![((d0:ℕ):E),((d0+a:ℕ):E),((d0+b:ℕ):E),((d0+b+a:ℕ):E)]
 have hxs_mono:StrictMono xs:=by
  intro u w huw
  fin_cases u <;> fin_cases w <;> simp_all [xs] <;> norm_cast <;> omega
 have hd0_lo:D<=d0:=(Finset.mem_Ico.mp (mem_filter.mp hd0_S).1).1;have hd2a_hi:d0+b+a < 2*D:=(Finset.mem_Ico.mp (mem_filter.mp hd2a_S).1).2;let f:E->E:=fun u=>(v:E)/u^2;have hxs0:xs 0=(d0:E):=rfl;have hxs3:xs (Fin.last 3)=((d0+b+a:ℕ):E):=rfl
 have hcd_f:ContDiffOn E 3 f (Icc (xs 0) (xs 3)):=by
  intro u hu;have hu_pos:0 < u:=lt_of_lt_of_le (by rw [hxs0];exact_mod_cast (show 0 < d0 by omega)) hu.1;exact (contDiffAt_c_div_pow (v:E) 2 3 hu_pos.ne').contDiffWithinAt
 obtain ⟨ξ,hξ_ioo,hξ_eq⟩ :=exists_dividedDiff_eq_iteratedDeriv (by decide:1<=3) xs f hxs_mono hcd_f;have hξ_lo:(D:E)<=ξ:=le_trans (by rw [hxs0];exact_mod_cast hd0_lo) hξ_ioo.1.le
 have hξ_hi:ξ<=2*(D:E):=le_trans hξ_ioo.2.le (by rw [hxs3];exact_mod_cast hd2a_hi.le);have hξ_pos:0 < ξ:=lt_of_lt_of_le hDR hξ_lo;have hder3:iteratedDeriv 3 f ξ=-24*(v:E)/ξ^5 :=iteratedDeriv_inv_sq_3 (v:E) hξ_pos
 have hdd_val:dividedDiff xs (f ∘ xs)=-4*(v:E)/ξ^5:=by
  rw [hξ_eq,hder3];have hfac:((3:ℕ).factorial:E)=6:=by norm_num [Nat.factorial]
  rw [hfac];ring
 have haR_ne:(a:E)≠0:=haR_pos.ne';have hbR_pos:(0:E) < (b:E):=by exact_mod_cast (show 0 < b by omega)
 have hbaR_pos:(0:E) < (b:E)-(a:E):=by
  have:(2:E)*(a:E)<=(b:E):=by exact_mod_cast hb_ge2a
  linarith
 have hbpaR_pos:(0:E) < (b:E)+(a:E):=by positivity
 let A3:ℤ:=-(((b-a:ℕ):ℤ)*(m0:ℤ)) + ((b+a:ℕ):ℤ)*(m1:ℤ) -
   ((b+a:ℕ):ℤ)*(m2:ℤ) +
   ((b-a:ℕ):ℤ)*(m3:ℤ)
 have hm_eq:∀ d j m:ℕ,D<=d->v+j=d^2*m->(m:E)=f (d:E)+(j:E)/(d:E)^2:=by
  intro d j m hd hvm;have hd_pos:(0:E) < (d:E):=by exact_mod_cast (show 0 < d by omega)
  have h:(v:E)+(j:E)=(d:E)^2*(m:E):=by exact_mod_cast hvm
  dsimp [f];field_simp [hd_pos.ne'];linarith
 have hdd_expand:(a:E)*(b:E)*((b:E)-(a:E))*((b:E)+(a:E)) * dividedDiff xs (f ∘ xs) = -((b:E)-(a:E))*f (d0:E)+((b:E)+(a:E))*f ((d0+a:ℕ):E) -
   ((b:E)+(a:E))*f ((d0+b:ℕ):E)+((b:E)-(a:E))*f ((d0+b+a:ℕ):E):=by
  have hxs_eq:xs=![(d0:E),(d0:E)+(a:E),(d0:E)+(b:E),(d0:E)+(b:E)+(a:E)]:=by ext j;fin_cases j <;> simp [xs,Nat.cast_add]
  rw [hxs_eq]
  simpa only [Nat.cast_add] using dividedDiff_four_pair (d0:E) (a:E) (b:E) f
   haR_ne hbR_pos.ne' hbaR_pos.ne' hbpaR_pos.ne'
 let err3:E:=-((b:E)-(a:E))*(j0:E)/(d0:E)^2 + ((b:E)+(a:E))*(j1:E)/((d0+a:ℕ):E)^2 -
   ((b:E)+(a:E))*(j2:E)/((d0+b:ℕ):E)^2 +
   ((b:E)-(a:E))*(j3:E)/((d0+b+a:ℕ):E)^2
 have hA3_eq:(A3:E) = -4*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))*((b:E)+(a:E))/ξ^5+err3:=by
  have hcast:(A3:E)=-((b:E)-(a:E))*(m0:E) + ((b:E)+(a:E))*(m1:E) -
     ((b:E)+(a:E))*(m2:E) +
     ((b:E)-(a:E))*(m3:E):=by
   dsimp [A3];push_cast;rw [Nat.cast_sub (by omega)];ring
  rw [hcast,hm_eq d0 j0 m0 hd0_lo hm0,hm_eq (d0+a) j1 m1 (by omega) hm1,hm_eq (d0+b) j2 m2 (by omega) hm2,hm_eq (d0+b+a) j3 m3 (by omega) hm3];have hmul:=congrArg (fun z=>(a:E)*(b:E)*((b:E)-(a:E))*((b:E)+(a:E))*z) hdd_val;rw [hdd_expand] at hmul
  have h_alg:-((b:E)-(a:E))*(f (d0:E)+(j0:E)/(d0:E)^2) + ((b:E)+(a:E))*(f ((d0+a:ℕ):E)+(j1:E)/((d0+a:ℕ):E)^2) -
     ((b:E)+(a:E))*(f ((d0+b:ℕ):E)+(j2:E)/((d0+b:ℕ):E)^2) +
     ((b:E)-(a:E))*(f ((d0+b+a:ℕ):E)+(j3:E)/((d0+b+a:ℕ):E)^2) =
     (-((b:E)-(a:E))*f (d0:E)+((b:E)+(a:E))*f ((d0+a:ℕ):E) -
      ((b:E)+(a:E))*f ((d0+b:ℕ):E)+((b:E)-(a:E))*f ((d0+b+a:ℕ):E))+err3:=by
   dsimp [err3];ring
  rw [h_alg,hmul];ring
 have herr3_le:|err3| ≤ 4*(b:E)*(H:E)/(D:E)^2:=by
  have hterm:∀ d j:ℕ,D<=d->j∈Finset.Ioo 0 H->(j:E)/(d:E)^2<=(H:E)/(D:E)^2:=by
   intro d j hd hj;have hjR:(j:E)<=(H:E):=by exact_mod_cast (Finset.mem_Ioo.mp hj).2.le
   have hdg:(D:E)<=(d:E):=by exact_mod_cast hd
   exact div_le_div₀ hHR.le hjR (sq_pos_of_pos hDR) (pow_le_pow_left₀ hDR.le hdg 2)
  dsimp [err3]
  have e1:=abs_add_le
   (-((b:E)-(a:E))*(j0:E)/(d0:E)^2 + ((b:E)+(a:E))*(j1:E)/((d0+a:ℕ):E)^2 -
    ((b:E)+(a:E))*(j2:E)/((d0+b:ℕ):E)^2)
   (((b:E)-(a:E))*(j3:E)/((d0+b+a:ℕ):E)^2)
  have e2:=abs_sub
   (-((b:E)-(a:E))*(j0:E)/(d0:E)^2 + ((b:E)+(a:E))*(j1:E)/((d0+a:ℕ):E)^2)
   (((b:E)+(a:E))*(j2:E)/((d0+b:ℕ):E)^2)
  have e3:=abs_add_le
   (-((b:E)-(a:E))*(j0:E)/(d0:E)^2)
   (((b:E)+(a:E))*(j1:E)/((d0+a:ℕ):E)^2)
  have t0:|-((b:E)-(a:E))*(j0:E)/(d0:E)^2| ≤ ((b:E)-(a:E))*((H:E)/(D:E)^2):=by
   rw [show -((b:E)-(a:E))*(j0:E)/(d0:E)^2=-(((b:E)-(a:E))*((j0:E)/(d0:E)^2)) by ring,abs_neg,abs_of_nonneg (by positivity)];exact mul_le_mul_of_nonneg_left (hterm d0 j0 hd0_lo hj0_ioo) hbaR_pos.le
  have t1:|((b:E)+(a:E))*(j1:E)/((d0+a:ℕ):E)^2| ≤ ((b:E)+(a:E))*((H:E)/(D:E)^2):=by
   rw [mul_div_assoc,abs_of_nonneg (by positivity)];exact mul_le_mul_of_nonneg_left (hterm (d0+a) j1 (by omega) hj1_ioo) hbpaR_pos.le
  have t2:|((b:E)+(a:E))*(j2:E)/((d0+b:ℕ):E)^2| ≤ ((b:E)+(a:E))*((H:E)/(D:E)^2):=by
   rw [mul_div_assoc,abs_of_nonneg (by positivity)];exact mul_le_mul_of_nonneg_left (hterm (d0+b) j2 (by omega) hj2_ioo) hbpaR_pos.le
  have t3:|((b:E)-(a:E))*(j3:E)/((d0+b+a:ℕ):E)^2| ≤ ((b:E)-(a:E))*((H:E)/(D:E)^2):=by
   rw [mul_div_assoc,abs_of_nonneg (by positivity)];exact mul_le_mul_of_nonneg_left (hterm (d0+b+a) j3 (by omega) hj3_ioo) hbaR_pos.le
  have hsum:((b:E)-(a:E))*((H:E)/(D:E)^2)+((b:E)+(a:E))*((H:E)/(D:E)^2) + ((b:E)+(a:E))*((H:E)/(D:E)^2)+((b:E)-(a:E))*((H:E)/(D:E)^2) = 4*(b:E)*(H:E)/(D:E)^2:=by ring
  linarith
 let main3:E:=4*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))*((b:E)+(a:E))/ξ^5
 have hmain3_lo:(v:E)*(a:E)*(b:E)^3/(16*(D:E)^5)<=main3:=by
  have hba_half:(b:E)/2<=(b:E)-(a:E):=by
   have:2*(a:E)<=(b:E):=by exact_mod_cast hb_ge2a
   linarith
  have hnum:2*(v:E)*(a:E)*(b:E)^3 ≤ 4*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))*((b:E)+(a:E)):=by
   have h1:(b:E)^2/2<=((b:E)-(a:E))*((b:E)+(a:E)):=by
     calc
       (b:E)^2/2=((b:E)/2)*(b:E):=by ring
       _ <= ((b:E)-(a:E))*((b:E)+(a:E)) :=mul_le_mul hba_half (by linarith) hbR_pos.le hbaR_pos.le
   have h2:=mul_le_mul_of_nonneg_left h1 (by positivity:(0:E)<=4*(v:E)*(a:E)*(b:E));have hL:4*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))*((b:E)+(a:E)) = 4*(v:E)*(a:E)*(b:E)*(((b:E)-(a:E))*((b:E)+(a:E))):=by ring
   have hR:4*(v:E)*(a:E)*(b:E)*((b:E)^2/2)=2*(v:E)*(a:E)*(b:E)^3:=by ring
   linarith
  have hden:ξ^5<=32*(D:E)^5:=by
   calc
     ξ^5<=(2*(D:E))^5:=pow_le_pow_left₀ hξ_pos.le hξ_hi 5
     _ = 32*(D:E)^5:=by ring
  calc
   (v:E)*(a:E)*(b:E)^3/(16*(D:E)^5)
       = 2*(v:E)*(a:E)*(b:E)^3/(32*(D:E)^5):=by ring
   _ <= 4*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))*((b:E)+(a:E))/(32*(D:E)^5) :=div_le_div_of_nonneg_right hnum (by positivity)
   _ <= main3:=div_le_div_of_nonneg_left (by positivity) (pow_pos hξ_pos 5) hden
 have hmain3_hi:main3<=8*(v:E)*(a:E)*(b:E)^3/(D:E)^5:=by
  have hnum:4*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))*((b:E)+(a:E)) ≤ 8*(v:E)*(a:E)*(b:E)^3:=by
   have h1:((b:E)-(a:E))*((b:E)+(a:E))<=2*(b:E)^2:=by
     have:(a:E)<=(b:E):=by exact_mod_cast (show a<=b by omega)
     nlinarith
   have h2:=mul_le_mul_of_nonneg_left h1 (by positivity:(0:E)<=4*(v:E)*(a:E)*(b:E));have hL:4*(v:E)*(a:E)*(b:E)*((b:E)-(a:E))*((b:E)+(a:E)) = 4*(v:E)*(a:E)*(b:E)*(((b:E)-(a:E))*((b:E)+(a:E))):=by ring
   have hR:4*(v:E)*(a:E)*(b:E)*(2*(b:E)^2)=8*(v:E)*(a:E)*(b:E)^3:=by ring
   linarith
  have hden:(D:E)^5<=ξ^5:=pow_le_pow_left₀ hDR.le hξ_lo 5
  calc
   main3<=8*(v:E)*(a:E)*(b:E)^3/ξ^5 :=div_le_div_of_nonneg_right hnum (pow_nonneg hξ_pos.le 5)
   _ <= 8*(v:E)*(a:E)*(b:E)^3/(D:E)^5 :=div_le_div_of_nonneg_left (by positivity) (pow_pos hDR 5) hden
 have herr3_lt_half:4*(b:E)*(H:E)/(D:E)^2 <
   (1/2:E)*((v:E)*(a:E)*(b:E)^3/(16*(D:E)^5)):=by
  have h1:4*(a:E)^3<=(a:E)*(b:E)^2:=by
   have h2a:2*(a:E)<=(b:E):=by exact_mod_cast hb_ge2a
   have hsq:4*(a:E)^2<=(b:E)^2:=by nlinarith
   calc
     4*(a:E)^3=(a:E)*(4*(a:E)^2):=by ring
     _ <= (a:E)*(b:E)^2:=mul_le_mul_of_nonneg_left hsq haR_pos.le
  have h2:(D:E)^4<=22*(v:E)*(a:E)^3:=by
   have:=(div_le_div_iff₀ (by norm_num) (pow_pos hDR 4)).mp ha_lb
   linarith
  have h3:2*(D:E)^4<=11*(v:E)*(a:E)*(b:E)^2:=by nlinarith
  have h4:704*(H:E) < (D:E):=by exact_mod_cast hHD
  have h5:1408*(H:E)*(D:E)^4 < 11*(v:E)*(a:E)*(b:E)^2*(D:E):=by
   have:1408*(H:E)*(D:E)^4 < 2*(D:E)^4*(D:E):=by nlinarith [pow_pos hDR 4]
   nlinarith
  have h6:128*(H:E)*(D:E)^3 < (v:E)*(a:E)*(b:E)^2:=by
   have h5':11*(128*(H:E)*(D:E)^3)*(D:E) < 11*((v:E)*(a:E)*(b:E)^2)*(D:E):=by linarith
   nlinarith
  rw [div_lt_iff₀ (sq_pos_of_pos hDR)];have hrhs:(1/2:E)*((v:E)*(a:E)*(b:E)^3/(16*(D:E)^5))*(D:E)^2 = (v:E)*(a:E)*(b:E)^3/(32*(D:E)^3):=by field_simp [hDR.ne'];ring
  rw [hrhs,lt_div_iff₀ (by positivity)];have h7:=mul_lt_mul_of_pos_right h6 hbR_pos;linarith
 have hA3_neg:(A3:E) < 0:=by
  have h1:(A3:E)=-main3+err3:=by rw [hA3_eq];dsimp [main3];ring
  have h2:=(abs_le.mp herr3_le).2;have hM_nn:(0:E)<=(v:E)*(a:E)*(b:E)^3/(16*(D:E)^5):=by positivity
  linarith
 have hA3_ge1:(1:E) ≤ |(A3:E)|:=by
  have hne:A3≠0:=by
   intro h0;rw [h0,Int.cast_zero] at hA3_neg;linarith
  have:(1:ℤ) ≤ |A3|:=Int.one_le_abs hne
  exact_mod_cast this
 have hA3_up:|(A3:E)| ≤ 9*(v:E)*(a:E)*(b:E)^3/(D:E)^5:=by
  have h1:(A3:E)=-main3+err3:=by rw [hA3_eq];dsimp [main3];ring
  have htri:|(A3:E)| ≤ main3 + |err3|:=by
   rw [h1]
   calc
     |-main3+err3| ≤ |-main3| + |err3|:=abs_add_le _ _
     _ = main3 + |err3|:=by rw [abs_neg,abs_of_nonneg (by dsimp [main3];positivity)]
  have herr_le1:|err3| ≤ (v:E)*(a:E)*(b:E)^3/(D:E)^5:=by
   have hnn:(0:E)<=(v:E)*(a:E)*(b:E)^3/(D:E)^5:=by positivity
   have hrat:(1/2:E)*((v:E)*(a:E)*(b:E)^3/(16*(D:E)^5)) = (1/32:E)*((v:E)*(a:E)*(b:E)^3/(D:E)^5):=by ring
   linarith
  have h8:8*(v:E)*(a:E)*(b:E)^3/(D:E)^5 = 8*((v:E)*(a:E)*(b:E)^3/(D:E)^5):=by ring
  have h9:9*(v:E)*(a:E)*(b:E)^3/(D:E)^5 = 9*((v:E)*(a:E)*(b:E)^3/(D:E)^5):=by ring
  linarith
 have hb3:(D:E)^5/(9*(v:E)*(a:E))<=(b:E)^3:=by
  rw [div_le_iff₀ (by positivity)]
  have:=(le_div_iff₀ (pow_pos hDR 5)).mp (hA3_ge1.trans hA3_up)
  linarith
 have hrp:=rpow_le_rpow (by positivity) hb3 (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (b:E) 3,← rpow_mul (Nat.cast_nonneg b)] at hrp;norm_num at hrp;exact hrp
set_option maxHeartbeats 1200000 in
lemma dyadicPrimeSet_Ga_bound {v H D a:ℕ} {S' Ga:Finset ℕ}
  (hv:1<=v) (hD:1<=D) (hH:1<=H) (hHD:704*H < D) (ha_pos:0 < a)
  (hS'_sub:S'⊆dyadicPrimeSet v H D)
  (hS'_gap:∀ d1 d2:ℕ,d1∈S'->d2∈S'->d1 < d2 → ((D:E)^4/(22*(v:E)))^(1/3:E)<=(d2:E)-(d1:E))
  (hGa_mem:∀ d∈Ga,d∈S'/\d+a∈S'/\∀ d'∈S',d < d'->d+a<=d') :
  (Ga.card:E) ≤ 90*(v:E)*(a:E)^3/(D:E)^4 + 180000*(H:E)*(v:E)^(1/3:E)*(a:E)^(1/3:E)/(D:E)^(5/3:E):=by
 classical
 have hvR:(0:E) < (v:E):=by exact_mod_cast hv
 have hDR:(0:E) < (D:E):=by exact_mod_cast hD
 have hHR:(0:E) < (H:E):=by exact_mod_cast hH
 have haR_pos:(0:E) < (a:E):=by exact_mod_cast ha_pos
 by_cases hGa:Ga.Nonempty
 ·
  let S:=dyadicPrimeSet v H D
  have hex_jm:∀ d∈S,∃ j m:ℕ,j∈Finset.Ioo 0 H/\v+j=d^2*m:=by
   intro d hd;rcases (mem_filter.mp hd).2.2 with ⟨j,hj,m,hm⟩;exact ⟨j,m,hj,hm⟩
  let jOf:ℕ->ℕ:=fun d=>if h:d∈S then Classical.choose (hex_jm d h) else 0;let mOf:ℕ->ℕ:=fun d=>if h:d∈S then Classical.choose (Classical.choose_spec (hex_jm d h)) else 0
  have hjm_spec:∀ d∈S,jOf d∈Finset.Ioo 0 H/\v+jOf d=d^2*mOf d:=by
   intro d hd;simp only [jOf,mOf,hd,↓reduceDIte];exact Classical.choose_spec (Classical.choose_spec (hex_jm d hd))
  have ha_lb:(1/22:E)<=(v:E)*(a:E)^3/(D:E)^4:=by
   rcases hGa with ⟨d0,hd0⟩;have hspec:=hGa_mem d0 hd0;have hg:=hS'_gap d0 (d0+a) hspec.1 hspec.2.1 (by omega);have hdiff:((d0+a:ℕ):E)-(d0:E)=(a:E):=by push_cast;ring
   rw [hdiff] at hg;have hpow:=pow_le_pow_left₀ (by positivity) hg 3;rw [← rpow_natCast _ 3,← rpow_mul (by positivity)] at hpow;norm_num at hpow;rw [div_le_iff₀ (by positivity)] at hpow;rw [div_le_div_iff₀ (by norm_num) (pow_pos hDR 4)];linarith
  let Ia:ℕ->ℤ:=fun d =>
   -((2*(d:ℤ)-(a:ℤ))*(mOf d:ℤ))+(2*(d:ℤ)+3*(a:ℤ))*(mOf (d+a):ℤ)
  have hIa_decomp:∀ d∈Ga,
    |(Ia d:E)-(v:E)*(a:E)^3/((d:E)^2*((d:E)+(a:E))^2)| ≤ 7*(H:E)/(D:E):=by
   intro d hd;have hsp:=hGa_mem d hd;have hdS:d∈S:=hS'_sub hsp.1;have hdaS:d+a∈S:=hS'_sub hsp.2.1;have hd_lo:D<=d:=(Finset.mem_Ico.mp (mem_filter.mp hdS).1).1;have hda_hi:d+a < 2*D:=(Finset.mem_Ico.mp (mem_filter.mp hdaS).1).2
   have hd_pos:(0:E) < (d:E):=by exact_mod_cast (show 0 < d by omega)
   have hda_pos:(0:E) < (d:E)+(a:E):=by positivity
   have hm1:(mOf d:E)=((v:E)+(jOf d:E))/(d:E)^2:=by
    have h:(v:E)+(jOf d:E)=(d:E)^2*(mOf d:E):=by exact_mod_cast (hjm_spec d hdS).2
    field_simp [hd_pos.ne'];linarith
   have hm2:(mOf (d+a):E)=((v:E)+(jOf (d+a):E))/((d:E)+(a:E))^2:=by
    have h:(v:E)+(jOf (d+a):E)=((d:E)+(a:E))^2*(mOf (d+a):E):=by
     have:=(hjm_spec (d+a) hdaS).2
     exact_mod_cast this
    field_simp [hda_pos.ne'];linarith
   have hdiff_eq:(Ia d:E)-(v:E)*(a:E)^3/((d:E)^2*((d:E)+(a:E))^2) = -(2*(d:E)-(a:E))*(jOf d:E)/(d:E)^2 + (2*(d:E)+3*(a:E))*(jOf (d+a):E)/((d:E)+(a:E))^2:=by
    have hcast:(Ia d:E)=-(2*(d:E)-(a:E))*(mOf d:E) + (2*(d:E)+3*(a:E))*(mOf (d+a):E):=by dsimp [Ia];push_cast;ring
    rw [hcast,hm1,hm2];have hid:=inv_sq_cubic_diff_id (d:E) (a:E) hd_pos.ne' hda_pos.ne'
    have hsplit:-(2*(d:E)-(a:E))*(((v:E)+(jOf d:E))/(d:E)^2) + (2*(d:E)+3*(a:E))*(((v:E)+(jOf (d+a):E))/((d:E)+(a:E))^2) = (v:E)*(-(2*(d:E)-(a:E))/(d:E)^2 + (2*(d:E)+3*(a:E))/((d:E)+(a:E))^2) + (-(2*(d:E)-(a:E))*(jOf d:E)/(d:E)^2 + (2*(d:E)+3*(a:E))*(jOf (d+a):E)/((d:E)+(a:E))^2):=by ring
    rw [hsplit,hid];ring
   rw [hdiff_eq];have hdD:(D:E)<=(d:E):=by exact_mod_cast hd_lo
   have ha_le:(a:E)<=(d:E):=by exact_mod_cast (show a<=d by omega)
   have hj1:(jOf d:E)<=(H:E):=by exact_mod_cast (Finset.mem_Ioo.mp (hjm_spec d hdS).1).2.le
   have hj2:(jOf (d+a):E)<=(H:E):=by exact_mod_cast (Finset.mem_Ioo.mp (hjm_spec (d+a) hdaS).1).2.le
   have ht1:|-(2*(d:E)-(a:E))*(jOf d:E)/(d:E)^2| ≤ 2*(H:E)/(D:E):=by
    rw [abs_div,abs_mul,abs_neg,abs_of_nonneg (by linarith),abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos (sq_pos_of_pos hd_pos)]
    calc
     (2*(d:E)-(a:E))*(jOf d:E)/(d:E)^2
        ≤ (2*(d:E))*(H:E)/(d:E)^2:=by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _);exact mul_le_mul (by linarith) hj1 (Nat.cast_nonneg _) (by positivity)
     _ = 2*(H:E)/(d:E):=by field_simp [hd_pos.ne']
     _ <= 2*(H:E)/(D:E):=div_le_div_of_nonneg_left (by positivity) hDR hdD
   have ht2:|(2*(d:E)+3*(a:E))*(jOf (d+a):E)/((d:E)+(a:E))^2| ≤ 5*(H:E)/(D:E):=by
    rw [abs_div,abs_mul,abs_of_nonneg (by positivity),abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos (sq_pos_of_pos hda_pos)]
    calc
     (2*(d:E)+3*(a:E))*(jOf (d+a):E)/((d:E)+(a:E))^2
        ≤ (5*(d:E))*(H:E)/(d:E)^2:=by
      have hnum:(2*(d:E)+3*(a:E))*(jOf (d+a):E)<=(5*(d:E))*(H:E) :=mul_le_mul (by linarith) hj2 (Nat.cast_nonneg _) (by positivity);have hden:(d:E)^2<=((d:E)+(a:E))^2:=pow_le_pow_left₀ hd_pos.le (by linarith) 2
      calc
        _ <= (5*(d:E))*(H:E)/((d:E)+(a:E))^2:=div_le_div_of_nonneg_right hnum (by positivity)
        _ <= _:=div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd_pos) hden
     _ = 5*(H:E)/(d:E):=by field_simp [hd_pos.ne']
     _ <= 5*(H:E)/(D:E):=div_le_div_of_nonneg_left (by positivity) hDR hdD
   calc
    _ <= |-(2*(d:E)-(a:E))*(jOf d:E)/(d:E)^2| +
      |(2*(d:E)+3*(a:E))*(jOf (d+a):E)/((d:E)+(a:E))^2|:=abs_add_le _ _
    _ <= 2*(H:E)/(D:E)+5*(H:E)/(D:E):=add_le_add ht1 ht2
    _ = 7*(H:E)/(D:E):=by ring
  let R_set:Finset ℤ:=Ga.image Ia
  have hR_card:(R_set.card:E)<=45*(v:E)*(a:E)^3/(D:E)^4:=by
   have hsub:R_set⊆Finset.Icc 0 (⌊(v:E)*(a:E)^3/(D:E)^4⌋+1):=by
    intro r hr;rcases Finset.mem_image.mp hr with ⟨d,hd,rfl⟩;have hdec:=hIa_decomp d hd;have h7HD:7*(H:E)/(D:E) < 1:=by rw [div_lt_one hDR];exact_mod_cast (show 7*H < D by omega)
    have hdS:d∈S:=hS'_sub (hGa_mem d hd).1;have hd_lo:(D:E)<=(d:E):=by exact_mod_cast (Finset.mem_Ico.mp (mem_filter.mp hdS).1).1
    have hmain_nn:0<=(v:E)*(a:E)^3/((d:E)^2*((d:E)+(a:E))^2):=by positivity
    have hmain_le:(v:E)*(a:E)^3/((d:E)^2*((d:E)+(a:E))^2) ≤ (v:E)*(a:E)^3/(D:E)^4:=by
     have hden:(D:E)^4<=(d:E)^2*((d:E)+(a:E))^2:=by
      have h1:(D:E)^2<=(d:E)^2:=pow_le_pow_left₀ hDR.le hd_lo 2;have h2:(D:E)^2<=((d:E)+(a:E))^2:=pow_le_pow_left₀ hDR.le (by linarith) 2
      calc
        (D:E)^4=(D:E)^2*(D:E)^2:=by ring
        _ <= (d:E)^2*((d:E)+(a:E))^2:=mul_le_mul h1 h2 (by positivity) (by positivity)
     exact div_le_div_of_nonneg_left (by positivity) (pow_pos hDR 4) hden
    have hlo_R:(-1:E) < (Ia d:E):=by linarith [(abs_le.mp hdec).1]
    have hhi_R:(Ia d:E) < (v:E)*(a:E)^3/(D:E)^4+1:=by linarith [(abs_le.mp hdec).2]
    refine Finset.mem_Icc.mpr ⟨?_,?_⟩
    ·
     have:(-1:ℤ) < Ia d:=by exact_mod_cast hlo_R
     omega
    ·
     have hfl:=Int.lt_floor_add_one ((v:E)*(a:E)^3/(D:E)^4);have hlt:(Ia d:E) < ((⌊(v:E)*(a:E)^3/(D:E)^4⌋+2:ℤ):E):=by push_cast;linarith
     have:Ia d < ⌊(v:E)*(a:E)^3/(D:E)^4⌋+2:=by exact_mod_cast hlt
     omega
   have h1:R_set.card<=(Finset.Icc (0:ℤ) (⌊(v:E)*(a:E)^3/(D:E)^4⌋+1)).card :=Finset.card_le_card hsub;rw [Int.card_Icc] at h1;have hfl_nn:(0:ℤ)<=⌊(v:E)*(a:E)^3/(D:E)^4⌋ :=Int.floor_nonneg.mpr (by positivity)
   have hcast:(R_set.card:E)<=(⌊(v:E)*(a:E)^3/(D:E)^4⌋:E)+2:=by
    have h2:(R_set.card:ℤ)<=⌊(v:E)*(a:E)^3/(D:E)^4⌋+2:=by omega
    exact_mod_cast h2
   have hfl_le:(⌊(v:E)*(a:E)^3/(D:E)^4⌋:E)<=(v:E)*(a:E)^3/(D:E)^4 :=Int.floor_le _;have h45:45*(v:E)*(a:E)^3/(D:E)^4 = 45*((v:E)*(a:E)^3/(D:E)^4):=by ring
   linarith
  have hfib_le:∀ r0∈R_set,((Ga.filter (fun d=>Ia d=r0)).card:E) ≤ 2+4000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E)):=by
   intro r0 _;let F:=Ga.filter (fun d=>Ia d=r0);let k:=F.card
   by_cases hk:k<=2
   ·
    have:(F.card:E)<=2:=by exact_mod_cast hk
    linarith [show (0:E)<=4000*(H:E)*(D:E)^(7/3:E) / ((v:E)^(2/3:E)*(a:E)^(8/3:E)) by positivity]
   ·
    let fEmb:=F.orderEmbOfFin rfl
    have hspan_F:(fEmb ⟨k-1,by omega⟩:E)-(fEmb ⟨0,by omega⟩:E) ≤ 896*(H:E)*(D:E)^4/((v:E)*(a:E)^3):=by
     set d1:=fEmb ⟨0,by omega⟩;set d2:=fEmb ⟨k-1,by omega⟩;have hd1_F:d1∈F:=Finset.orderEmbOfFin_mem F rfl _;have hd2_F:d2∈F:=Finset.orderEmbOfFin_mem F rfl _;have hd1_G:d1∈Ga:=(mem_filter.mp hd1_F).1;have hd2_G:d2∈Ga:=(mem_filter.mp hd2_F).1
     have hI_eq:(Ia d1:E)=(Ia d2:E):=by rw [(mem_filter.mp hd1_F).2,(mem_filter.mp hd2_F).2]
     have hd1_lt:d1 < d2:=fEmb.strictMono (by show 0 < k-1;omega);have hdec1:=hIa_decomp d1 hd1_G;have hdec2:=hIa_decomp d2 hd2_G
     have hdiff_main:(v:E)*(a:E)^3 * (1/((d1:E)^2*((d1:E)+(a:E))^2) -
         1/((d2:E)^2*((d2:E)+(a:E))^2))<=14*(H:E)/(D:E):=by
      have h1:=(abs_le.mp hdec1).1;have h2:=(abs_le.mp hdec2).2
      have hdist:(v:E)*(a:E)^3 * (1/((d1:E)^2*((d1:E)+(a:E))^2) -
           1/((d2:E)^2*((d2:E)+(a:E))^2)) =
          (v:E)*(a:E)^3/((d1:E)^2*((d1:E)+(a:E))^2) -
          (v:E)*(a:E)^3/((d2:E)^2*((d2:E)+(a:E))^2):=by ring
      have h14:14*(H:E)/(D:E)=2*(7*(H:E)/(D:E)):=by ring
      linarith
     have hd1_lo:(D:E)<=(d1:E):=by exact_mod_cast (Finset.mem_Ico.mp (mem_filter.mp (hS'_sub (hGa_mem d1 hd1_G).1)).1).1
     have hd2_lo:(D:E)<=(d2:E):=by exact_mod_cast (Finset.mem_Ico.mp (mem_filter.mp (hS'_sub (hGa_mem d2 hd2_G).1)).1).1
     have hd1_pos:(0:E) < (d1:E):=lt_of_lt_of_le hDR hd1_lo;have hd2_pos:(0:E) < (d2:E):=lt_of_lt_of_le hDR hd2_lo;have hd1a_hi:(d1:E)+(a:E)<=2*(D:E):=by exact_mod_cast (Finset.mem_Ico.mp (mem_filter.mp (hS'_sub (hGa_mem d1 hd1_G).2.1)).1).2.le
     have hd2a_hi:(d2:E)+(a:E)<=2*(D:E):=by exact_mod_cast (Finset.mem_Ico.mp (mem_filter.mp (hS'_sub (hGa_mem d2 hd2_G).2.1)).1).2.le
     have hd1_hi:(d1:E)<=2*(D:E):=by linarith
     have hd2_hi:(d2:E)<=2*(D:E):=by linarith
     have hdiff_pos:0 < (d2:E)-(d1:E):=sub_pos.mpr (by exact_mod_cast hd1_lt)
     have hinv_lb:((d2:E)-(d1:E))/(64*(D:E)^5) ≤ 1/((d1:E)^2*((d1:E)+(a:E))^2) -
        1/((d2:E)^2*((d2:E)+(a:E))^2):=by
      have hrw:1/((d1:E)^2*((d1:E)+(a:E))^2) -
          1/((d2:E)^2*((d2:E)+(a:E))^2) =
          ((d2:E)-(d1:E))*((d2:E)+(d1:E)+(a:E)) *
          ((d2:E)*((d2:E)+(a:E))+(d1:E)*((d1:E)+(a:E))) /
          (((d1:E)^2*((d1:E)+(a:E))^2)*((d2:E)^2*((d2:E)+(a:E))^2)):=by
        field_simp [hd1_pos.ne',hd2_pos.ne',(by positivity:(d1:E)+(a:E)≠0),(by positivity:(d2:E)+(a:E)≠0)];ring
      rw [hrw]
      have hnum_lb:4*(D:E)^3*((d2:E)-(d1:E)) ≤ ((d2:E)-(d1:E))*((d2:E)+(d1:E)+(a:E)) * ((d2:E)*((d2:E)+(a:E))+(d1:E)*((d1:E)+(a:E))):=by
        have h1:2*(D:E)<=(d2:E)+(d1:E)+(a:E):=by linarith
        have h2:2*(D:E)^2<=(d2:E)*((d2:E)+(a:E))+(d1:E)*((d1:E)+(a:E)):=by nlinarith
        have h3:4*(D:E)^3<=((d2:E)+(d1:E)+(a:E)) * ((d2:E)*((d2:E)+(a:E))+(d1:E)*((d1:E)+(a:E))):=by
          calc
            4*(D:E)^3=(2*(D:E))*(2*(D:E)^2):=by ring
            _ <= _:=mul_le_mul h1 h2 (by positivity) (by positivity)
        nlinarith
      have hden_ub:((d1:E)^2*((d1:E)+(a:E))^2) * ((d2:E)^2*((d2:E)+(a:E))^2)<=256*(D:E)^8:=by
        have h1:(d1:E)^2<=4*(D:E)^2:=by nlinarith
        have h2:((d1:E)+(a:E))^2<=4*(D:E)^2:=by nlinarith
        have h3:(d2:E)^2<=4*(D:E)^2:=by nlinarith
        have h4:((d2:E)+(a:E))^2<=4*(D:E)^2:=by nlinarith
        have h12:(d1:E)^2*((d1:E)+(a:E))^2<=16*(D:E)^4:=by
          calc
            _ <= (4*(D:E)^2)*(4*(D:E)^2):=mul_le_mul h1 h2 (by positivity) (by positivity)
            _ = 16*(D:E)^4:=by ring
        have h34:(d2:E)^2*((d2:E)+(a:E))^2<=16*(D:E)^4:=by
          calc
            _ <= (4*(D:E)^2)*(4*(D:E)^2):=mul_le_mul h3 h4 (by positivity) (by positivity)
            _ = 16*(D:E)^4:=by ring
        calc
          _ <= (16*(D:E)^4)*(16*(D:E)^4):=mul_le_mul h12 h34 (by positivity) (by positivity)
          _ = 256*(D:E)^8:=by ring
      calc
        ((d2:E)-(d1:E))/(64*(D:E)^5)
            = 4*(D:E)^3*((d2:E)-(d1:E))/(256*(D:E)^8):=by
          field_simp [hDR.ne'];ring
        _ <= ((d2:E)-(d1:E))*((d2:E)+(d1:E)+(a:E)) * ((d2:E)*((d2:E)+(a:E))+(d1:E)*((d1:E)+(a:E))) / (256*(D:E)^8):=div_le_div_of_nonneg_right hnum_lb (by positivity)
        _ <= _:=div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ub
     have hcomb:(v:E)*(a:E)^3*(((d2:E)-(d1:E))/(64*(D:E)^5)) ≤ 14*(H:E)/(D:E) :=(mul_le_mul_of_nonneg_left hinv_lb (by positivity)).trans hdiff_main
     rw [le_div_iff₀ (by positivity)];have h1:=(le_div_iff₀ hDR).mp hcomb;have h2:(v:E)*(a:E)^3*(((d2:E)-(d1:E))/(64*(D:E)^5))*(D:E) = ((d2:E)-(d1:E))*((v:E)*(a:E)^3)/(64*(D:E)^4):=by field_simp [hDR.ne']
     rw [h2,div_le_iff₀ (by positivity)] at h1;linarith
    have hstep_F:∀ i:ℕ,(hi:i+2 < k) → ((D:E)^5/(9*(v:E)*(a:E)))^(1/3:E) ≤ (fEmb ⟨i+2,hi⟩:E)-(fEmb ⟨i,by omega⟩:E):=by
     intro i hi;set d0:=fEmb ⟨i,by omega⟩;set d_mid:=fEmb ⟨i+1,by omega⟩;set d2:=fEmb ⟨i+2,hi⟩;have hd0_G:d0∈Ga:=(mem_filter.mp (Finset.orderEmbOfFin_mem F rfl ⟨i,by omega⟩)).1
     have hdmid_G:d_mid∈Ga:=(mem_filter.mp (Finset.orderEmbOfFin_mem F rfl ⟨i+1,by omega⟩)).1;have hd2_G:d2∈Ga:=(mem_filter.mp (Finset.orderEmbOfFin_mem F rfl ⟨i+2,hi⟩)).1;have h0m:d0 < d_mid:=fEmb.strictMono (by show i < i+1;omega)
     have hm2:d_mid < d2:=fEmb.strictMono (by show i+1 < i+2;omega);have h0m_ge:d0+a<=d_mid:=(hGa_mem d0 hd0_G).2.2 d_mid (hGa_mem d_mid hdmid_G).1 h0m;have hm2_ge:d_mid+a<=d2:=(hGa_mem d_mid hdmid_G).2.2 d2 (hGa_mem d2 hd2_G).1 hm2;set b:ℕ:=d2-d0
     have hb_ge2a:2*a<=b:=by omega
     have hd2_eq:d2=d0+b:=by omega
     have hstep:=dyadicPrimeSet_third_diff_step hv hD hH hHD ha_pos hb_ge2a ha_lb
      (hS'_sub (hGa_mem d0 hd0_G).1) (hS'_sub (hGa_mem d0 hd0_G).2.1)
      (hd2_eq ▸ hS'_sub (hGa_mem d2 hd2_G).1) (hd2_eq ▸ hS'_sub (hGa_mem d2 hd2_G).2.1)
     have hdiff:(d2:E)-(d0:E)=(b:E):=by rw [hd2_eq];push_cast;ring
     rwa [hdiff]
    let q2:ℕ:=(k-1)/2
    have hq2_sep:(q2:E)*((D:E)^5/(9*(v:E)*(a:E)))^(1/3:E) ≤ 896*(H:E)*(D:E)^4/((v:E)*(a:E)^3):=by
     let fStep:ℕ->E:=fun j =>
      if h:2*(j+1) < k then
        (fEmb ⟨2*(j+1),h⟩:E)-(fEmb ⟨2*j,by omega⟩:E)
      else 0
     have htele:∑ j∈Finset.range q2,fStep j = (fEmb ⟨2*q2,by dsimp [q2,k];omega⟩:E)-(fEmb ⟨0,by omega⟩:E):=by
      have hgen:∀ n:ℕ,(hn:n<=q2) → ∑ j∈Finset.range n,fStep j = (fEmb ⟨2*n,by dsimp [q2,k] at *;omega⟩:E)-(fEmb ⟨0,by omega⟩:E):=by
        intro n hn;induction n with
        | zero=>simp
        | succ n ih =>
          rw [sum_range_succ,ih (by omega)];have hn':2*(n+1) < k:=by dsimp [q2,k] at hn ⊢;omega
          simp only [fStep,hn',↓reduceDIte];ring
      exact hgen q2 le_rfl
     have hle_span:(fEmb ⟨2*q2,by dsimp [q2,k];omega⟩:E)-(fEmb ⟨0,by omega⟩:E) ≤ (fEmb ⟨k-1,by omega⟩:E)-(fEmb ⟨0,by omega⟩:E):=by
      have:fEmb ⟨2*q2,by dsimp [q2,k];omega⟩<=fEmb ⟨k-1,by omega⟩ :=fEmb.monotone (by show 2*q2<=k-1;dsimp [q2,k];omega)
      linarith [show (fEmb ⟨2*q2,by dsimp [q2,k];omega⟩:E)<=(fEmb ⟨k-1,by omega⟩:E) by exact_mod_cast this]
     calc
      (q2:E)*((D:E)^5/(9*(v:E)*(a:E)))^(1/3:E)
          = ∑ _j∈Finset.range q2,((D:E)^5/(9*(v:E)*(a:E)))^(1/3:E):=by simp
      _ <= ∑ j∈Finset.range q2,fStep j:=by
        apply sum_le_sum;intro j hj;have hj':=Finset.mem_range.mp hj;have hlt:2*(j+1) < k:=by dsimp [q2,k] at hj' ⊢;omega
        have h:=hstep_F (2*j) (by omega)
        have heq:fStep j=(fEmb ⟨2*j+2,by omega⟩:E)-(fEmb ⟨2*j,by omega⟩:E):=by
          simp only [fStep,hlt,↓reduceDIte];have hfin:(⟨2*(j+1),hlt⟩:Fin k)=⟨2*j+2,by omega⟩:=Fin.ext (by dsimp;omega);rw [hfin]
        rw [heq];exact h
      _ = (fEmb ⟨2*q2,by dsimp [q2,k];omega⟩:E)-(fEmb ⟨0,by omega⟩:E):=htele
      _ <= (fEmb ⟨k-1,by omega⟩:E)-(fEmb ⟨0,by omega⟩:E):=hle_span
      _ <= 896*(H:E)*(D:E)^4/((v:E)*(a:E)^3):=hspan_F
    have hstep_pos:0 < ((D:E)^5/(9*(v:E)*(a:E)))^(1/3:E) :=rpow_pos_of_pos (by positivity) _;have hq2_le:(q2:E)<=(896*(H:E)*(D:E)^4/((v:E)*(a:E)^3)) / ((D:E)^5/(9*(v:E)*(a:E)))^(1/3:E) :=(le_div_iff₀ hstep_pos).mpr hq2_sep
    have hsimp:(896*(H:E)*(D:E)^4/((v:E)*(a:E)^3)) / ((D:E)^5/(9*(v:E)*(a:E)))^(1/3:E) ≤ 2000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E)):=by
     rw [div_rpow (by positivity) (by positivity),mul_rpow (by positivity) haR_pos.le,mul_rpow (by norm_num) hvR.le,← rpow_natCast (D:E) 5,← rpow_mul hDR.le,Nat.cast_ofNat]
     have h9:(9:E)^(1/3:E)<=2000/896:=by
      have hle:(9:E)<=(2000/896:E)^3:=by norm_num
      have hrp:=rpow_le_rpow (by norm_num) hle (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (2000/896:E) 3,← rpow_mul (by norm_num)] at hrp;norm_num at hrp ⊢;exact hrp
     have hD_id:(D:E)^4/(D:E)^((5:E)*(1/3:E))=(D:E)^(7/3:E):=by
      rw [div_eq_mul_inv,← rpow_natCast (D:E) 4,← rpow_neg hDR.le,← rpow_add hDR];norm_num
     have hv_id:(v:E)^(1/3:E)/(v:E)=1/(v:E)^(2/3:E):=by
      rw [div_eq_mul_inv]
      conv_rhs=>rw [one_div,← rpow_neg hvR.le]
      conv_lhs=>arg 2;arg 1;rw [← rpow_one (v:E)]
      rw [← rpow_neg hvR.le,← rpow_add hvR];norm_num
     have ha_id:(a:E)^(1/3:E)/(a:E)^3=1/(a:E)^(8/3:E):=by
      rw [div_eq_mul_inv,← rpow_natCast (a:E) 3,← rpow_neg haR_pos.le,← rpow_add haR_pos]
      conv_rhs=>rw [one_div,← rpow_neg haR_pos.le]
      norm_num
     have hre:(896*(H:E)*(D:E)^4/((v:E)*(a:E)^3)) / ((D:E)^((5:E)*(1/3:E))/((9:E)^(1/3:E)*(v:E)^(1/3:E)*(a:E)^(1/3:E))) = (896*(9:E)^(1/3:E))*(H:E)*((D:E)^4/(D:E)^((5:E)*(1/3:E))) * ((v:E)^(1/3:E)/(v:E))*((a:E)^(1/3:E)/(a:E)^3):=by
      field_simp [hvR.ne',haR_pos.ne',(rpow_pos_of_pos hDR ((5:E)*(1/3:E))).ne',(rpow_pos_of_pos (by norm_num:(0:E) < 9) (1/3:E)).ne',(rpow_pos_of_pos hvR (1/3:E)).ne',(rpow_pos_of_pos haR_pos (1/3:E)).ne']
     rw [hre,hD_id,hv_id,ha_id];have h896:896*(9:E)^(1/3:E)<=2000:=by linarith
     have hfac:(H:E)*(D:E)^(7/3:E)*(1/(v:E)^(2/3:E))*(1/(a:E)^(8/3:E)) = (H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E)):=by ring
     calc
      896*(9:E)^(1/3:E)*(H:E)*(D:E)^(7/3:E) * (1/(v:E)^(2/3:E))*(1/(a:E)^(8/3:E))
          = (896*(9:E)^(1/3:E)) * ((H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E))):=by
        rw [← hfac];ring
      _ <= 2000*((H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E))) :=mul_le_mul_of_nonneg_right h896 (by positivity)
      _ = _:=by ring
    have hk_le:(F.card:E)<=2*(q2:E)+2:=by
     have:k<=2*q2+2:=by dsimp [q2,k];omega
     exact_mod_cast this
    have h2k:2*(2000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E))) = 4000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E)):=by ring
    linarith
  have hGa_part:Ga.card=∑ r0∈R_set,(Ga.filter (fun d=>Ia d=r0)).card:=by
   rw [← card_biUnion]
   ·
    congr 1;ext d;simp only [Finset.mem_biUnion,mem_filter,R_set,Finset.mem_image];constructor
    · intro hd;exact ⟨Ia d,⟨d,hd,rfl⟩,hd,rfl⟩
    · rintro ⟨_,_,hd,_⟩;exact hd
   ·
    intro r1 _ r2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro d h1 h2;exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
  have hGa_cast:(Ga.card:E)<=(R_set.card:E) * (2+4000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E))):=by
   rw [hGa_part,Nat.cast_sum]
   calc
    _ <= ∑ _r0∈R_set,(2+4000*(H:E)*(D:E)^(7/3:E) / ((v:E)^(2/3:E)*(a:E)^(8/3:E))):=sum_le_sum hfib_le
    _ = _:=by simp only [sum_const,nsmul_eq_mul]
  have hprod_le:(R_set.card:E) * (2+4000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E))) ≤ (45*(v:E)*(a:E)^3/(D:E)^4) * (2+4000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E))) :=mul_le_mul_of_nonneg_right hR_card (by positivity)
  have hprod_eq:(45*(v:E)*(a:E)^3/(D:E)^4) * (2+4000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E))) = 90*(v:E)*(a:E)^3/(D:E)^4 + 180000*(H:E)*(v:E)^(1/3:E)*(a:E)^(1/3:E)/(D:E)^(5/3:E):=by
   have hv13:(v:E)/(v:E)^(2/3:E)=(v:E)^(1/3:E):=by
    rw [div_eq_mul_inv,← rpow_neg hvR.le]
    conv_lhs=>arg 1;rw [← rpow_one (v:E)]
    rw [← rpow_add hvR];norm_num
   have ha13:(a:E)^3/(a:E)^(8/3:E)=(a:E)^(1/3:E):=by
    rw [div_eq_mul_inv,← rpow_natCast (a:E) 3,← rpow_neg haR_pos.le,← rpow_add haR_pos];norm_num
   have hD53:(D:E)^(7/3:E)/(D:E)^4=1/(D:E)^(5/3:E):=by
    rw [div_eq_mul_inv,one_div,← rpow_natCast (D:E) 4,← rpow_neg hDR.le,← rpow_neg hDR.le,← rpow_add hDR];norm_num
   have h1:(45*(v:E)*(a:E)^3/(D:E)^4) * (4000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E))) = 180000*(H:E)*((v:E)/(v:E)^(2/3:E))*((a:E)^3/(a:E)^(8/3:E)) * ((D:E)^(7/3:E)/(D:E)^4):=by ring
   calc
    _ = 90*(v:E)*(a:E)^3/(D:E)^4 + (45*(v:E)*(a:E)^3/(D:E)^4) * (4000*(H:E)*(D:E)^(7/3:E)/((v:E)^(2/3:E)*(a:E)^(8/3:E))):=by ring
    _ = 90*(v:E)*(a:E)^3/(D:E)^4 + 180000*(H:E)*(v:E)^(1/3:E)*(a:E)^(1/3:E)*(1/(D:E)^(5/3:E)):=by rw [h1,hv13,ha13,hD53]
    _ = _:=by ring
  linarith
 ·
  rw [Finset.not_nonempty_iff_eq_empty.mp hGa,Finset.card_empty,Nat.cast_zero];positivity
lemma dyadicPrimeSet_rangeB_le {v H D:ℕ} {U:E} (hv:1<=v) (hD:1<=D) (hH:1<=H)
  (hU:1<=U) (hHD:704*H < D) (hHD2:256*H*D^2 < 3*v) :
  ((dyadicPrimeSet v H D).card:E) ≤ 2*(H:E)/U + 4000*(v:E)*U^4/(H:E)^4 + 4*10^5*(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E))+4:=by
 classical
 let S:=dyadicPrimeSet v H D;let t:=S.card;have hvR:(0:E) < (v:E):=by exact_mod_cast hv
 have hDR:(0:E) < (D:E):=by exact_mod_cast hD
 have hHR:(0:E) < (H:E):=by exact_mod_cast hH
 by_cases ht:t<=4
 ·
  have:(S.card:E)<=4:=by exact_mod_cast ht
  linarith [show (0:E)<=2*(H:E)/U+4000*(v:E)*U^4/(H:E)^4 + 4*10^5*(v:E)^(1/3:E)*U^(4/3:E) / ((H:E)^(1/3:E)*(D:E)^(1/3:E)) by positivity]
 ·
  let emb:=S.orderEmbOfFin rfl;let t':ℕ:=(t+1)/2;let S':Finset ℕ:=(Finset.range t').image (fun k=>if h:2*k < t then emb ⟨2*k,h⟩ else 0)
  have ht'_card:S'.card=t':=by
   rw [Finset.card_image_of_injOn]
   · exact card_range t'
   ·
    intro a ha b hb heq;have ha':2*a < t:=by have:=Finset.mem_range.mp ha;dsimp [t'] at this;omega
    have hb':2*b < t:=by have:=Finset.mem_range.mp hb;dsimp [t'] at this;omega
    simp only [ha',hb',↓reduceDIte] at heq
    have:=emb.injective heq
    simp at this;omega
  have hS_le_2S':S.card<=2*S'.card:=by rw [ht'_card];dsimp [t',t];omega
  have hS'_sub:S'⊆S:=by
   intro d hd;rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩;have hk':2*k < t:=by have:=Finset.mem_range.mp hk;dsimp [t'] at this;omega
   simp only [hk',↓reduceDIte];exact Finset.orderEmbOfFin_mem S rfl _
  have hS'_gap:∀ d1 d2:ℕ,d1∈S'->d2∈S'->d1 < d2 → ((D:E)^4/(22*(v:E)))^(1/3:E)<=((d2:E)-(d1:E)):=by
   intro d1 d2 hd1 hd2 hlt;rcases Finset.mem_image.mp hd1 with ⟨k1,hk1,rfl⟩;rcases Finset.mem_image.mp hd2 with ⟨k2,hk2,rfl⟩;have hk1':2*k1 < t:=by have:=Finset.mem_range.mp hk1;dsimp [t'] at this;omega
   have hk2':2*k2 < t:=by have:=Finset.mem_range.mp hk2;dsimp [t'] at this;omega
   simp only [hk1',hk2',↓reduceDIte] at hlt ⊢
   have hk12:k1 < k2:=by
    by_contra hge
    have:emb ⟨2*k2,hk2'⟩<=emb ⟨2*k1,hk1'⟩:=emb.monotone (by show 2*k2<=2*k1;omega)
    omega
   exact dyadicPrimeSet_second_diff_gap (emb ⟨2*k1,hk1'⟩) (emb ⟨2*k1+1,by omega⟩) (emb ⟨2*k2,hk2'⟩)
    hv hD hH hHD2
    (Finset.orderEmbOfFin_mem S rfl _) (Finset.orderEmbOfFin_mem S rfl _) (Finset.orderEmbOfFin_mem S rfl _)
    (emb.strictMono (by show 2*k1 < 2*k1+1;omega))
    (emb.strictMono (by show 2*k1+1 < 2*k2;omega))
  let emb':=S'.orderEmbOfFin ht'_card;let A_max:E:=(D:E)*U/(H:E)
  let bigIdx:=(Finset.range (t'-1)).filter (fun i =>
   if h:i+1 < t' then A_max < ((emb' ⟨i+1,h⟩-emb' ⟨i,by omega⟩:ℕ):E) else False)
  let smallIdx:=(Finset.range (t'-1)).filter (fun i =>
   if h:i+1 < t' then ((emb' ⟨i+1,h⟩-emb' ⟨i,by omega⟩:ℕ):E)<=A_max else False)
  have hidx_split:t'-1=bigIdx.card+smallIdx.card:=by
   have h:=(Finset.card_filter_add_card_filter_not (s:=Finset.range (t'-1))
    (p:=fun i=>if h:i+1 < t' then A_max < ((emb' ⟨i+1,h⟩-emb' ⟨i,by omega⟩:ℕ):E) else False)).symm
   rw [card_range] at h;rw [h];congr 1;apply congrArg Finset.card;ext i;simp only [mem_filter,Finset.mem_range,smallIdx];constructor <;> rintro ⟨hi,hp⟩ <;> refine ⟨hi,?_⟩
   · simp only [show i+1 < t' by omega,↓reduceDIte] at hp ⊢;linarith
   · simp only [show i+1 < t' by omega,↓reduceDIte] at hp ⊢;linarith
  have hbig_le:(bigIdx.card:E)<=(H:E)/U:=by
   have hA_pos:0 < A_max:=by positivity
   have hsum_big:(bigIdx.card:E)*A_max<=(D:E):=by
    let stepDiff:ℕ->E:=fun i =>
     if h:i+1 < t' then (emb' ⟨i+1,h⟩:E)-(emb' ⟨i,by omega⟩:E) else 0
    have htele:∑ i∈Finset.range (t'-1),stepDiff i = (emb' ⟨t'-1,by omega⟩:E)-(emb' ⟨0,by omega⟩:E):=by
     have hgen:∀ k:ℕ,(hk:k<=t'-1) → ∑ i∈Finset.range k,stepDiff i = (emb' ⟨k,by omega⟩:E)-(emb' ⟨0,by omega⟩:E):=by
      intro k hk;induction k with
      | zero=>simp
      | succ k ih =>
       rw [sum_range_succ,ih (by omega)];have hk':k+1 < t':=by omega
       simp only [stepDiff,hk',↓reduceDIte];ring
     exact hgen (t'-1) le_rfl
    have hspan:(emb' ⟨t'-1,by omega⟩:E)-(emb' ⟨0,by omega⟩:E)<=(D:E):=by
     have hhi:=(Finset.mem_Ico.mp (mem_filter.mp (hS'_sub (Finset.orderEmbOfFin_mem S' ht'_card ⟨t'-1,by omega⟩))).1).2;have hlo:=(Finset.mem_Ico.mp (mem_filter.mp (hS'_sub (Finset.orderEmbOfFin_mem S' ht'_card ⟨0,by omega⟩))).1).1
     have hhiR:(emb' ⟨t'-1,by omega⟩:E)<=2*(D:E):=by exact_mod_cast hhi.le
     have hloR:(D:E)<=(emb' ⟨0,by omega⟩:E):=by exact_mod_cast hlo
     linarith
    calc
     (bigIdx.card:E)*A_max=∑ _i∈bigIdx,A_max:=by simp
     _ <= ∑ i∈bigIdx,stepDiff i:=by
      apply sum_le_sum;intro i hi;have hfl:=mem_filter.mp hi;have hi_lt:i+1 < t':=by have:=Finset.mem_range.mp hfl.1;omega
      have hlt:A_max < ((emb' ⟨i+1,hi_lt⟩-emb' ⟨i,by omega⟩:ℕ):E):=by simpa [hi_lt] using hfl.2
      have hmono:emb' ⟨i,by omega⟩<=emb' ⟨i+1,hi_lt⟩:=emb'.monotone (by show i<=i+1;omega);rw [Nat.cast_sub hmono] at hlt;simpa [stepDiff,hi_lt] using hlt.le
     _ <= ∑ i∈Finset.range (t'-1),stepDiff i:=by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _);intro i _ _;dsimp [stepDiff];split_ifs with h
      ·
       have:emb' ⟨i,by omega⟩<=emb' ⟨i+1,h⟩:=emb'.monotone (by show i<=i+1;omega)
       linarith [show (emb' ⟨i,by omega⟩:E)<=(emb' ⟨i+1,h⟩:E) by exact_mod_cast this]
      · rfl
     _ <= (D:E):=htele ▸ hspan
   have h1:(bigIdx.card:E)<=(D:E)/A_max:=(le_div_iff₀ hA_pos).mpr hsum_big;have h2:(D:E)/A_max=(H:E)/U:=by dsimp [A_max];field_simp [hHR.ne',(by linarith:U≠0),hDR.ne']
   linarith
  let gapOf:ℕ->ℕ:=fun i=>if h:i+1 < t' then emb' ⟨i+1,h⟩-emb' ⟨i,by omega⟩ else 0;let A_nat:ℕ:=⌊A_max⌋₊
  let G:ℕ->Finset ℕ:=fun a =>
   (smallIdx.filter (fun i=>gapOf i=a)).image (fun i=>if h:i < t' then emb' ⟨i,h⟩ else 0)
  have hsmall_sum:(smallIdx.card:E)<=∑ a∈Finset.Icc 1 A_nat,((G a).card:E):=by
   have hpart:smallIdx.card=∑ a∈Finset.Icc 1 A_nat,(smallIdx.filter (fun i=>gapOf i=a)).card:=by
    rw [← card_biUnion]
    ·
     congr 1;ext i;simp only [Finset.mem_biUnion,mem_filter,Finset.mem_Icc];constructor
     ·
      intro hi;have hfl:=mem_filter.mp hi;have hi_lt:i+1 < t':=by have:=Finset.mem_range.mp hfl.1;omega
      have hga_pos:1<=gapOf i:=by
       simp only [gapOf,hi_lt,↓reduceDIte]
       have:=emb'.strictMono (show (⟨i,by omega⟩:Fin t') < ⟨i+1,hi_lt⟩ by simp)
       omega
      have hga_le:gapOf i<=A_nat:=by
       have hle:(gapOf i:E)<=A_max:=by simpa [gapOf,hi_lt] using hfl.2
       exact Nat.le_floor hle
      exact ⟨gapOf i,⟨hga_pos,hga_le⟩,hi,rfl⟩
     · rintro ⟨_,_,hi,_⟩;exact hi
    ·
     intro a _ b _ hab;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro i hi1 hi2;exact hab ((mem_filter.mp hi1).2.symm.trans (mem_filter.mp hi2).2)
   have hcard_G:∀ a,(G a).card=(smallIdx.filter (fun i=>gapOf i=a)).card:=by
    intro a;apply Finset.card_image_of_injOn;intro i1 hi1 i2 hi2 heq
    have h1:i1 < t':=by
     have:=Finset.mem_range.mp (mem_filter.mp (mem_filter.mp hi1).1).1;omega
    have h2:i2 < t':=by
     have:=Finset.mem_range.mp (mem_filter.mp (mem_filter.mp hi2).1).1;omega
    simp only [h1,h2,↓reduceDIte] at heq
    have:=emb'.injective heq;simpa using this
   rw [hpart,Nat.cast_sum];apply sum_le_sum;intro a _;rw [hcard_G a]
  have hG_bound:∀ a∈Finset.Icc 1 A_nat,((G a).card:E) ≤ 90*(v:E)*(a:E)^3/(D:E)^4 + 180000*(H:E)*(v:E)^(1/3:E)*(a:E)^(1/3:E)/(D:E)^(5/3:E):=by
   intro a ha;have ha_pos:0 < a:=(Finset.mem_Icc.mp ha).1
   have hGa_mem:∀ d∈G a,d∈S'/\d+a∈S' ∧ ∀ d'∈S',d < d'->d+a<=d':=by
    intro d hd;rcases Finset.mem_image.mp hd with ⟨i,hi,rfl⟩;have hfl1:=mem_filter.mp hi;have hfl2:=mem_filter.mp hfl1.1;have hi_lt:i+1 < t':=by have:=Finset.mem_range.mp hfl2.1;omega
    have hi_lt':i < t':=by omega
    have hga:emb' ⟨i+1,hi_lt⟩-emb' ⟨i,hi_lt'⟩=a:=by simpa [gapOf,hi_lt] using hfl1.2
    have hlt:emb' ⟨i,hi_lt'⟩ < emb' ⟨i+1,hi_lt⟩:=emb'.strictMono (by show i < i+1;omega);have hadd:emb' ⟨i,hi_lt'⟩+a=emb' ⟨i+1,hi_lt⟩:=by omega
    simp only [hi_lt',↓reduceDIte];refine ⟨Finset.orderEmbOfFin_mem S' ht'_card _,hadd ▸ Finset.orderEmbOfFin_mem S' ht'_card _,?_⟩;intro d' hd' hgt;have hd'_mem:d'∈Set.range emb':=by rw [Finset.range_orderEmbOfFin];exact hd'
    rcases hd'_mem with ⟨k,rfl⟩
    have hik:i < k.1:=by
     by_contra hle;have:=emb'.monotone (show k<=⟨i,hi_lt'⟩ by show k.1<=i;omega);omega
    have hk_ge:emb' ⟨i+1,hi_lt⟩<=emb' k:=emb'.monotone (by show i+1<=k.1;omega);omega
   exact dyadicPrimeSet_Ga_bound hv hD hH hHD ha_pos hS'_sub hS'_gap hGa_mem
  have hA_nat_le:(A_nat:E)<=A_max:=Nat.floor_le (by positivity)
  have hsmall_le:(smallIdx.card:E) ≤ 2000*(v:E)*U^4/(H:E)^4 + 2*10^5*(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E)):=by
   have h1:∑ a∈Finset.Icc 1 A_nat,((G a).card:E) ≤ (∑ a∈Finset.Icc 1 A_nat,(90*(v:E)*(a:E)^3/(D:E)^4)) + (∑ a∈Finset.Icc 1 A_nat,(180000*(H:E)*(v:E)^(1/3:E)*(a:E)^(1/3:E)/(D:E)^(5/3:E))):=by
    rw [← sum_add_distrib];exact sum_le_sum hG_bound
   have hsum1:∑ a∈Finset.Icc 1 A_nat,(90*(v:E)*(a:E)^3/(D:E)^4) ≤ 2000*(v:E)*U^4/(H:E)^4:=by
    calc
     _ <= ∑ _a∈Finset.Icc 1 A_nat,(90*(v:E)*A_max^3/(D:E)^4):=by
      apply sum_le_sum;intro a ha;have ha_le:(a:E)<=A_max:=le_trans (by exact_mod_cast (Finset.mem_Icc.mp ha).2) hA_nat_le;gcongr
     _ = ((Finset.Icc 1 A_nat).card:E)*(90*(v:E)*A_max^3/(D:E)^4):=by simp
     _ <= A_max*(90*(v:E)*A_max^3/(D:E)^4):=by
      rw [Nat.card_Icc];simp only [Nat.add_sub_cancel];exact mul_le_mul_of_nonneg_right hA_nat_le (by positivity)
     _ = 90*(v:E)*U^4/(H:E)^4:=by dsimp [A_max];field_simp [hDR.ne',hHR.ne']
     _ <= 2000*(v:E)*U^4/(H:E)^4:=by
      have h90:90*(v:E)*U^4/(H:E)^4=90*((v:E)*U^4/(H:E)^4):=by ring
      have h2k:2000*(v:E)*U^4/(H:E)^4=2000*((v:E)*U^4/(H:E)^4):=by ring
      have:0<=(v:E)*U^4/(H:E)^4:=by positivity
      linarith
   have hsum2:∑ a∈Finset.Icc 1 A_nat,(180000*(H:E)*(v:E)^(1/3:E)*(a:E)^(1/3:E)/(D:E)^(5/3:E)) ≤ 2*10^5*(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E)):=by
    calc
     _ <= ∑ _a∈Finset.Icc 1 A_nat,(180000*(H:E)*(v:E)^(1/3:E)*A_max^(1/3:E)/(D:E)^(5/3:E)):=by
      apply sum_le_sum;intro a ha;have ha_le:(a:E)<=A_max:=le_trans (by exact_mod_cast (Finset.mem_Icc.mp ha).2) hA_nat_le;have hrp:(a:E)^(1/3:E)<=A_max^(1/3:E) :=rpow_le_rpow (Nat.cast_nonneg a) ha_le (by norm_num);gcongr
     _ = ((Finset.Icc 1 A_nat).card:E) * (180000*(H:E)*(v:E)^(1/3:E)*A_max^(1/3:E)/(D:E)^(5/3:E)):=by simp
     _ <= A_max*(180000*(H:E)*(v:E)^(1/3:E)*A_max^(1/3:E)/(D:E)^(5/3:E)):=by
      rw [Nat.card_Icc];simp only [Nat.add_sub_cancel];exact mul_le_mul_of_nonneg_right hA_nat_le (by positivity)
     _ = 180000*(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E)):=by
      have hA_pos:0 < A_max:=by positivity
      have hA43:A_max*A_max^(1/3:E)=A_max^(4/3:E):=by
       conv_lhs=>arg 1;rw [← rpow_one A_max]
       rw [← rpow_add hA_pos];norm_num
      have hA_exp:A_max^(4/3:E) = (D:E)^(4/3:E)*U^(4/3:E)/(H:E)^(4/3:E):=by
       dsimp [A_max];rw [div_rpow (by positivity) hHR.le,mul_rpow hDR.le (by linarith)]
      have hH13:(H:E)/(H:E)^(4/3:E)=1/(H:E)^(1/3:E):=by
       rw [div_eq_mul_inv,one_div,← rpow_neg hHR.le,← rpow_neg hHR.le]
       conv_lhs=>arg 1;rw [← rpow_one (H:E)]
       rw [← rpow_add hHR];norm_num
      have hD13:(D:E)^(4/3:E)/(D:E)^(5/3:E)=1/(D:E)^(1/3:E):=by
       rw [div_eq_mul_inv,one_div,← rpow_neg hDR.le,← rpow_neg hDR.le,← rpow_add hDR];norm_num
      calc
       A_max*(180000*(H:E)*(v:E)^(1/3:E)*A_max^(1/3:E)/(D:E)^(5/3:E))
         = 180000*(H:E)*(v:E)^(1/3:E)*(A_max*A_max^(1/3:E))/(D:E)^(5/3:E):=by ring
       _ = 180000*(v:E)^(1/3:E)*U^(4/3:E) * ((H:E)/(H:E)^(4/3:E))*((D:E)^(4/3:E)/(D:E)^(5/3:E)):=by rw [hA43,hA_exp];ring
       _ = 180000*(v:E)^(1/3:E)*U^(4/3:E) * (1/(H:E)^(1/3:E))*(1/(D:E)^(1/3:E)):=by rw [hH13,hD13]
       _ = _:=by ring
     _ <= 2*10^5*(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E)):=by
      have h18:180000*(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E)) = 180000*((v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E))):=by ring
      have h20:2*10^5*(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E)) = 200000*((v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E))):=by ring
      have:0<=(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E)):=by positivity
      linarith
   linarith
  have hS_final:(S.card:E)<=2*((bigIdx.card:E)+(smallIdx.card:E)+1):=by
   have h1:t'<=bigIdx.card+smallIdx.card+1:=by omega
   have h2:S.card<=2*(bigIdx.card+smallIdx.card+1):=by
    have:=hS_le_2S';rw [ht'_card] at this;omega
   exact_mod_cast h2
  have h2H:2*((H:E)/U)=2*(H:E)/U:=by ring
  have h2_1:2*(2000*(v:E)*U^4/(H:E)^4)=4000*(v:E)*U^4/(H:E)^4:=by ring
  have h2_2:2*(2*10^5*(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E))) = 4*10^5*(v:E)^(1/3:E)*U^(4/3:E)/((H:E)^(1/3:E)*(D:E)^(1/3:E)):=by ring
  linarith
lemma exists_nat_rpow_ge (C δ:E) (hδ:0 < δ) :
  ∃ N₀:ℕ,1<=N₀/\∀ n:ℕ,N₀<=n->C<=(n:E)^δ:=by
 let M:E:=max C 1;have hM:1<=M:=le_max_right _ _;let N₀:ℕ:=⌈M^(1/δ)⌉₊+1;refine ⟨N₀,by omega,?_⟩;intro n hn
 have hnM:M^(1/δ)<=(n:E):=by
  have h1:M^(1/δ)<=(⌈M^(1/δ)⌉₊:E):=Nat.le_ceil _;have h2:(⌈M^(1/δ)⌉₊:E)<=(n:E):=by exact_mod_cast (show ⌈M^(1/δ)⌉₊<=n by omega)
  exact h1.trans h2
 have hrp:=rpow_le_rpow (by positivity) hnM hδ.le;rw [← rpow_mul (by linarith),one_div_mul_cancel hδ.ne',rpow_one] at hrp;exact (le_max_left C 1).trans hrp
lemma exists_nat_log_le_rpow (δ:E) (hδ:0 < δ) :
  ∃ N₀:ℕ,2<=N₀/\∀ n:ℕ,N₀<=n->((Nat.log 2 (2*n)+2:ℕ):E)<=(n:E)^δ:=by
 have hc_pos:0 < δ/2*Real.log 2:=mul_pos (half_pos hδ) (Real.log_pos (by norm_num));obtain ⟨N1,_,hN1⟩:=exists_nat_rpow_ge (2^(δ/2)/(δ/2*Real.log 2)+2) (δ/2) (half_pos hδ);refine ⟨max N1 2,le_max_right _ _,?_⟩;intro n hn
 have hn1:N1<=n:=le_trans (le_max_left _ _) hn;have hn_pos:(0:E) < (n:E):=by exact_mod_cast (show 0 < n by omega)
 have h2k:(2:E)^(Nat.log 2 (2*n))<=2*(n:E):=by exact_mod_cast Nat.pow_log_le_self 2 (by omega:2*n≠0)
 have hlog_le:(Nat.log 2 (2*n):E)*(δ/2*Real.log 2)<=(2*(n:E))^(δ/2):=by
  have h1:(Nat.log 2 (2*n):E)*(δ/2*Real.log 2) ≤ Real.exp ((Nat.log 2 (2*n):E)*(δ/2*Real.log 2)):=by linarith [Real.add_one_le_exp ((Nat.log 2 (2*n):E)*(δ/2*Real.log 2))]
  have h2:Real.exp ((Nat.log 2 (2*n):E)*(δ/2*Real.log 2)) = ((2:E)^(Nat.log 2 (2*n)))^(δ/2):=by rw [Real.rpow_def_of_pos (by positivity),log_pow];congr 1;ring
  have h3:((2:E)^(Nat.log 2 (2*n)))^(δ/2)<=(2*(n:E))^(δ/2) :=rpow_le_rpow (by positivity) h2k (half_pos hδ).le;exact h1.trans (h2 ▸ h3)
 have hdiv:(Nat.log 2 (2*n):E)<=(2^(δ/2)/(δ/2*Real.log 2))*(n:E)^(δ/2):=by
  rw [mul_rpow (by norm_num) hn_pos.le] at hlog_le;rw [div_mul_eq_mul_div,le_div_iff₀ hc_pos];linarith
 have hn_half_ge1:(1:E)<=(n:E)^(δ/2) :=one_le_rpow (by exact_mod_cast (show 1<=n by omega)) (half_pos hδ).le;have hN1_bd:=hN1 n hn1;have hsplit:(n:E)^δ=(n:E)^(δ/2)*(n:E)^(δ/2):=by rw [← rpow_add hn_pos];congr 1;ring
 push_cast
 calc
  (Nat.log 2 (2*n):E)+2
    ≤ (2^(δ/2)/(δ/2*Real.log 2))*(n:E)^(δ/2)+2*(n:E)^(δ/2):=by linarith
  _ = (2^(δ/2)/(δ/2*Real.log 2)+2)*(n:E)^(δ/2):=by ring
  _ <= (n:E)^(δ/2)*(n:E)^(δ/2) :=mul_le_mul_of_nonneg_right hN1_bd (rpow_nonneg hn_pos.le _)
  _ = (n:E)^δ:=hsplit.symm
set_option maxHeartbeats 1600000 in
theorem exists_squarefree_near {ε:E} (hε:0 < ε) (hε_le:ε<=1/1000) :
  ∃ V₀:ℕ,1000<=V₀/\∀ v:ℕ,V₀<=v → ∃ j∈Finset.Ioo 0 ⌈(v:E)^(1/5+ε)⌉₊,Squarefree (v+j):=by
 obtain ⟨N_log,_,hN_log⟩:=exists_nat_log_le_rpow (ε/10) (by linarith);obtain ⟨N_c1,_,hN_c1⟩:=exists_nat_rpow_ge (10^8:E) (ε/10) (by linarith);obtain ⟨N_c2,_,hN_c2⟩:=exists_nat_rpow_ge (10^8:E) (1/100:E) (by norm_num)
 let V₀:ℕ:=max 1000 (max N_log (max N_c1 N_c2));refine ⟨V₀,le_max_left _ _,?_⟩;intro v hv;have hv_1000:1000<=v:=le_trans (le_max_left _ _) hv;have hv_log:N_log<=v:=le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hv
 have hv_c1:N_c1<=v:=le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hv;have hv_c2:N_c2<=v:=le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hv
 have hvR:(0:E) < (v:E):=by exact_mod_cast (show 0 < v by omega)
 have hv_ge1:(1:E)<=(v:E):=by exact_mod_cast (show 1<=v by omega)
 have hv_c1_bd:(10^8:E)<=(v:E)^(ε/10):=hN_c1 v hv_c1;have hv_c2_bd:(10^8:E)<=(v:E)^(1/100:E):=hN_c2 v hv_c2;set H:ℕ:=⌈(v:E)^(1/5+ε)⌉₊;have hH_lo:(v:E)^(1/5+ε)<=(H:E):=Nat.le_ceil _
 have hH_ge_100:(10^8:E)<=(H:E):=by
  have h1:(v:E)^(1/100:E)<=(v:E)^(1/5+ε) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith);linarith
 have hH_100:10^8<=H:=by exact_mod_cast hH_ge_100
 have hH_hi:(H:E)<=2*(v:E)^(1/5+ε):=by
  have h1:(H:E) < (v:E)^(1/5+ε)+1:=Nat.ceil_lt_add_one (by positivity);have h2:(1:E)<=(v:E)^(1/5+ε):=one_le_rpow hv_ge1 (by linarith);linarith
 let K:ℕ:=Nat.log 2 (2*v)+2;have hK_le:(K:E)<=(v:E)^(ε/10):=hN_log v hv_log;have hK_pos:(0:E) < (K:E):=by exact_mod_cast (show 0 < K by dsimp [K];omega)
 let D_of:ℕ->ℕ:=fun t=>(H/4)*2^t
 have hdyad_bound:∀ D:ℕ,H/4<=D->D^2 < 2*v → ((dyadicPrimeSet v H D).card:E)<=(H:E)/(8*(K:E)):=by
  intro D hD_lo hD_hi;have hD_ge1:1<=D:=by omega
  have hDR:(0:E) < (D:E):=by exact_mod_cast hD_ge1
  have hDR_lo:(H:E)/8<=(D:E):=by
   have:H<=4*D+3:=by omega
   have h1:(H:E)<=4*(D:E)+3:=by exact_mod_cast this
   linarith
  have hDR_hi:(D:E)<=2*(v:E)^(1/2:E):=by
   have h1:(D:E)^2<=4*(v:E):=by
    have:(D:E)^2 < 2*(v:E):=by exact_mod_cast hD_hi
    linarith
   have hrp:=rpow_le_rpow (sq_nonneg _) h1 (by norm_num:(0:E)<=1/2);rw [← rpow_natCast (D:E) 2,← rpow_mul hDR.le,mul_rpow (by norm_num) hvR.le] at hrp;norm_num at hrp;exact hrp
  have hTarget_lb:(v:E)^(1/5+9*ε/10)/8<=(H:E)/(8*(K:E)):=by
   have h1:(v:E)^(1/5+ε)/(v:E)^(ε/10)=(v:E)^(1/5+9*ε/10):=by rw [div_eq_mul_inv,← rpow_neg hvR.le,← rpow_add hvR];congr 1;ring
   rw [← h1];have h2:(v:E)^(1/5+ε)/(v:E)^(ε/10)<=(H:E)/(K:E) :=div_le_div₀ (by positivity) hH_lo hK_pos hK_le;have h3:(H:E)/(8*(K:E))=((H:E)/(K:E))/8:=by ring
   rw [h3];linarith
  have hTarget_32:(v:E)^(1/5+9*ε/10)/32<=(H:E)/(32*(K:E)):=by
   have:(H:E)/(32*(K:E))=((H:E)/(8*(K:E)))/4:=by ring
   linarith
  by_cases hA:(D:E)<=(v:E)^(1/4:E)
  ·
   have h4H:4*H<=D^2:=by
    have h1:(H/4)^2<=D^2:=Nat.pow_le_pow_left hD_lo 2;have h2:H<=4*(H/4)+3:=by omega
    have h3:4*H<=(H/4)^2:=by nlinarith
    omega
   have hHS:=dyadicPrimeSet_rangeA_le (show 1<=v by omega) hD_ge1 (show 1<=H by omega) h4H
   have ht1:(v:E)^(1/10:E)*(D:E)^(2/5:E)<=(v:E)^(1/5:E):=by
    have h1:(D:E)^(2/5:E)<=((v:E)^(1/4:E))^(2/5:E) :=rpow_le_rpow hDR.le hA (by norm_num);rw [← rpow_mul hvR.le] at h1
    calc
     (v:E)^(1/10:E)*(D:E)^(2/5:E)
       ≤ (v:E)^(1/10:E)*(v:E)^((1/4:E)*(2/5:E)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
     _ = (v:E)^(1/5:E):=by rw [← rpow_add hvR];congr 1;norm_num
   have ht2:(D:E)^(2/3:E)*(H:E)^(1/6:E)<=2*(v:E)^(1/5+ε/6):=by
    have h1:(D:E)^(2/3:E)<=(v:E)^(1/6:E):=by
     have h:=rpow_le_rpow hDR.le hA (by norm_num:(0:E)<=2/3);rw [← rpow_mul hvR.le] at h;norm_num at h;exact h
    have h2:(H:E)^(1/6:E)<=2*(v:E)^((1/5+ε)/6):=by
     have h:=rpow_le_rpow (Nat.cast_nonneg H) hH_hi (by norm_num:(0:E)<=1/6);rw [mul_rpow (by norm_num) (by positivity),← rpow_mul hvR.le] at h
     have h216:(2:E)^(1/6:E)<=2:=by
      calc
       (2:E)^(1/6:E)<=(2:E)^(1:E):=rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
       _ = 2:=rpow_one 2
     calc
      (H:E)^(1/6:E)<=(2:E)^(1/6:E)*(v:E)^((1/5+ε)*(1/6:E)):=h
      _ <= 2*(v:E)^((1/5+ε)/6):=by
       rw [show (1/5+ε)*(1/6:E)=(1/5+ε)/6 by ring];exact mul_le_mul_of_nonneg_right h216 (by positivity)
    calc
     (D:E)^(2/3:E)*(H:E)^(1/6:E)
       ≤ (v:E)^(1/6:E)*(2*(v:E)^((1/5+ε)/6)) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
     _ = 2*((v:E)^(1/6:E)*(v:E)^((1/5+ε)/6)):=by ring
     _ = 2*(v:E)^(1/5+ε/6):=by rw [← rpow_add hvR];congr 1;ring
   have ht3:(H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E)<=2*(v:E)^(1/5+ε/6):=by
    have h1:(D:E)/(v:E)^(1/4:E)<=1:=(div_le_one (by positivity)).mpr hA
    have h2:(H:E)^(1/4:E)<=2*(v:E)^((1/5+ε)/4):=by
     have h:=rpow_le_rpow (Nat.cast_nonneg H) hH_hi (by norm_num:(0:E)<=1/4);rw [mul_rpow (by norm_num) (by positivity),← rpow_mul hvR.le] at h
     have h214:(2:E)^(1/4:E)<=2:=by
      calc
       (2:E)^(1/4:E)<=(2:E)^(1:E):=rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
       _ = 2:=rpow_one 2
     calc
      (H:E)^(1/4:E)<=(2:E)^(1/4:E)*(v:E)^((1/5+ε)*(1/4:E)):=h
      _ <= 2*(v:E)^((1/5+ε)/4):=by
       rw [show (1/5+ε)*(1/4:E)=(1/5+ε)/4 by ring];exact mul_le_mul_of_nonneg_right h214 (by positivity)
    have h3:(v:E)^((1/5+ε)/4)<=(v:E)^(1/5+ε/6) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
    calc
     (H:E)^(1/4:E)*(D:E)/(v:E)^(1/4:E)
       = (H:E)^(1/4:E)*((D:E)/(v:E)^(1/4:E)):=by ring
     _ <= (H:E)^(1/4:E)*1:=mul_le_mul_of_nonneg_left h1 (by positivity)
     _ = (H:E)^(1/4:E):=mul_one _
     _ <= 2*(v:E)^(1/5+ε/6):=by linarith
   have ht4:(1:E)<=(v:E)^(1/5+ε/6):=one_le_rpow hv_ge1 (by linarith);have ht1':(v:E)^(1/5:E)<=(v:E)^(1/5+ε/6) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith);have htot:((dyadicPrimeSet v H D).card:E)<=18*10^5*(v:E)^(1/5+ε/6):=by linarith
   have hgap_exp:8*(18*10^5:E)<=(v:E)^(9*ε/10-ε/6):=by
    have h1:(v:E)^(ε/10)<=(v:E)^(9*ε/10-ε/6) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith);linarith
   have hfinal:18*10^5*(v:E)^(1/5+ε/6)<=(v:E)^(1/5+9*ε/10)/8:=by
    rw [le_div_iff₀ (by norm_num)]
    calc
     18*10^5*(v:E)^(1/5+ε/6)*8
       = (8*(18*10^5:E))*(v:E)^(1/5+ε/6):=by ring
     _ <= (v:E)^(9*ε/10-ε/6)*(v:E)^(1/5+ε/6) :=mul_le_mul_of_nonneg_right hgap_exp (by positivity)
     _ = (v:E)^(1/5+9*ε/10):=by rw [← rpow_add hvR];congr 1;ring
   exact htot.trans (hfinal.trans hTarget_lb)
  ·
   push Not at hA
   by_cases hB:(D:E)<=(v:E)^(2/5-ε)
   ·
    have hHD:704*H < D:=by
     have h1:(704:E)*(H:E)<=1408*(v:E)^(1/5+ε):=by linarith
     have h2:(1408:E)<=(v:E)^(1/100:E):=by linarith
     have h3:(v:E)^(1/100:E)<=(v:E)^(1/20-ε) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
     have h4:1408*(v:E)^(1/5+ε) < (v:E)^(1/4:E):=by
      have hmul:(1408:E)*(v:E)^(1/5+ε)<=(v:E)^(1/20-ε)*(v:E)^(1/5+ε) :=mul_le_mul_of_nonneg_right (h2.trans h3) (by positivity);have heq:(v:E)^(1/20-ε)*(v:E)^(1/5+ε)=(v:E)^(1/4:E):=by rw [← rpow_add hvR];congr 1;ring
      have hstrict:(1408:E) < (v:E)^(1/20-ε):=by linarith
      calc
       1408*(v:E)^(1/5+ε) < (v:E)^(1/20-ε)*(v:E)^(1/5+ε) :=mul_lt_mul_of_pos_right hstrict (by positivity)
       _ = (v:E)^(1/4:E):=heq
     have:(704*(H:E)) < (D:E):=by linarith
     exact_mod_cast this
    have hHD2:256*H*D^2 < 3*v:=by
     have h1:256*(H:E)*(D:E)^2<=512*(v:E)^(1-ε):=by
      have hD2:(D:E)^2<=(v:E)^(4/5-2*ε):=by
       have h:=pow_le_pow_left₀ hDR.le hB 2;rw [← rpow_natCast ((v:E)^(2/5-ε)) 2,← rpow_mul hvR.le] at h;exact h.trans_eq (by congr 1;push_cast;ring)
      calc
       256*(H:E)*(D:E)^2<=256*(2*(v:E)^(1/5+ε))*(v:E)^(4/5-2*ε):=by
        have:=mul_le_mul hH_hi hD2 (sq_nonneg _) (by positivity)
        linarith
       _ = 512*((v:E)^(1/5+ε)*(v:E)^(4/5-2*ε)):=by ring
       _ = 512*(v:E)^(1-ε):=by rw [← rpow_add hvR];congr 1;ring
     have h512:(512:E) < 3*(v:E)^ε:=by
      have:(v:E)^(ε/10)<=(v:E)^ε:=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
      linarith
     have h2:512*(v:E)^(1-ε) < 3*(v:E):=by
      calc
       512*(v:E)^(1-ε) < (3*(v:E)^ε)*(v:E)^(1-ε) :=mul_lt_mul_of_pos_right h512 (by positivity)
       _ = 3*((v:E)^ε*(v:E)^(1-ε)):=by ring
       _ = 3*(v:E):=by rw [← rpow_add hvR];simp
     have:(256*(H:E)*(D:E)^2) < 3*(v:E):=lt_of_le_of_lt h1 h2
     exact_mod_cast this
    let U:E:=(v:E)^(ε/2);have hU_ge1:1<=U:=one_le_rpow hv_ge1 (by linarith);have hRB:=dyadicPrimeSet_rangeB_le (show 1<=v by omega) hD_ge1 (show 1<=H by omega) hU_ge1 hHD hHD2
    have hterm1:2*(H:E)/U<=(H:E)/(32*(K:E)):=by
     have h64K:64*(K:E)<=U:=by
      have h1:(v:E)^(ε/10)*(v:E)^(ε/10)<=(v:E)^(ε/2):=by
       rw [← rpow_add hvR];exact rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
      have h2:64*(K:E)<=(v:E)^(ε/10)*(v:E)^(ε/10) :=mul_le_mul (by linarith) hK_le hK_pos.le (by positivity);exact h2.trans h1
     have hU_pos:0 < U:=by positivity
     rw [div_le_div_iff₀ hU_pos (by positivity)];nlinarith [mul_nonneg (Nat.cast_nonneg H) (by linarith:(0:E)<=U-64*(K:E))]
    have hterm2:4000*(v:E)*U^4/(H:E)^4<=(H:E)/(32*(K:E)):=by
     have hU4:U^4=(v:E)^(2*ε):=by dsimp [U];rw [← rpow_natCast _ 4,← rpow_mul hvR.le];congr 1;ring
     have hH4:(v:E)^(4/5+4*ε)<=(H:E)^4:=by
      have h:=pow_le_pow_left₀ (by positivity) hH_lo 4;rw [← rpow_natCast ((v:E)^(1/5+ε)) 4,← rpow_mul hvR.le] at h;exact (by congr 1;push_cast;ring:(v:E)^(4/5+4*ε)=_).trans_le h
     have hle1:4000*(v:E)*U^4/(H:E)^4<=4000*(v:E)^(1/5-2*ε):=by
      rw [hU4]
      calc
       4000*(v:E)*(v:E)^(2*ε)/(H:E)^4
         ≤ 4000*(v:E)*(v:E)^(2*ε)/(v:E)^(4/5+4*ε) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hH4
       _ = 4000*((v:E)^(1:E)*(v:E)^(2*ε)*((v:E)^(4/5+4*ε))⁻¹):=by rw [rpow_one];ring
       _ = 4000*(v:E)^(1/5-2*ε):=by rw [← rpow_neg hvR.le,← rpow_add hvR,← rpow_add hvR];congr 2;ring
     have hle2:4000*(v:E)^(1/5-2*ε)<=(v:E)^(1/5+9*ε/10)/32:=by
      rw [le_div_iff₀ (by norm_num)]
      have h1:(32*4000:E)<=(v:E)^(29*ε/10):=by
       have:(v:E)^(ε/10)<=(v:E)^(29*ε/10) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
       linarith
      calc
       4000*(v:E)^(1/5-2*ε)*32=(32*4000:E)*(v:E)^(1/5-2*ε):=by ring
       _ <= (v:E)^(29*ε/10)*(v:E)^(1/5-2*ε) :=mul_le_mul_of_nonneg_right h1 (by positivity)
       _ = (v:E)^(1/5+9*ε/10):=by rw [← rpow_add hvR];congr 1;ring
     linarith
    have hterm3:4*10^5*(v:E)^(1/3:E)*U^(4/3:E) / ((H:E)^(1/3:E)*(D:E)^(1/3:E))<=(H:E)/(32*(K:E)):=by
     have hU43:U^(4/3:E)=(v:E)^(2*ε/3):=by dsimp [U];rw [← rpow_mul hvR.le];congr 1;ring
     have hH13:(v:E)^((1/5+ε)/3)<=(H:E)^(1/3:E):=by
      have h:=rpow_le_rpow (by positivity) hH_lo (by norm_num:(0:E)<=1/3);rw [← rpow_mul hvR.le] at h;convert h using 2;ring
     have hD13:(v:E)^(1/12:E)<=(D:E)^(1/3:E):=by
      have h:=rpow_le_rpow (by positivity) hA.le (by norm_num:(0:E)<=1/3);rw [← rpow_mul hvR.le] at h;norm_num at h;exact h
     have hle1:4*10^5*(v:E)^(1/3:E)*U^(4/3:E) / ((H:E)^(1/3:E)*(D:E)^(1/3:E)) ≤ 4*10^5*(v:E)^(11/60+ε/3):=by
      rw [hU43]
      calc
       _ <= 4*10^5*(v:E)^(1/3:E)*(v:E)^(2*ε/3) / ((v:E)^((1/5+ε)/3)*(v:E)^(1/12:E)) := div_le_div_of_nonneg_left (by positivity) (by positivity)
         (mul_le_mul hH13 hD13 (by positivity) (by positivity))
       _ = 4*10^5*((v:E)^(1/3:E)*(v:E)^(2*ε/3) * (((v:E)^((1/5+ε)/3))⁻¹*((v:E)^(1/12:E))⁻¹)):=by rw [div_eq_mul_inv,mul_inv];ring
       _ = 4*10^5*(v:E)^(11/60+ε/3):=by
        rw [← rpow_neg hvR.le,← rpow_neg hvR.le,← rpow_add hvR,← rpow_add hvR,← rpow_add hvR];congr 2;ring
     have hle2:4*10^5*(v:E)^(11/60+ε/3)<=(v:E)^(1/5+9*ε/10)/32:=by
      rw [le_div_iff₀ (by norm_num)]
      have h1:(32*(4*10^5):E)<=(v:E)^(1/60+17*ε/30):=by
       have:(v:E)^(1/100:E)<=(v:E)^(1/60+17*ε/30) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
       linarith
      calc
       4*10^5*(v:E)^(11/60+ε/3)*32
         = (32*(4*10^5):E)*(v:E)^(11/60+ε/3):=by ring
       _ <= (v:E)^(1/60+17*ε/30)*(v:E)^(11/60+ε/3) :=mul_le_mul_of_nonneg_right h1 (by positivity)
       _ = (v:E)^(1/5+9*ε/10):=by rw [← rpow_add hvR];congr 1;ring
     linarith
    have hterm4:(4:E)<=(H:E)/(32*(K:E)):=by
     have:(v:E)^(1/100:E)<=(v:E)^(1/5+9*ε/10) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
     linarith
    have h4x:4*((H:E)/(32*(K:E)))=(H:E)/(8*(K:E)):=by ring
    linarith
   ·
    push Not at hB
    have hHD:14*H < D:=by
     have h1:14*(H:E)<=28*(v:E)^(1/5+ε):=by linarith
     have h2:(28:E) < (v:E)^(1/5-2*ε):=by
      have:(v:E)^(1/100:E)<=(v:E)^(1/5-2*ε) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
      linarith
     have h3:28*(v:E)^(1/5+ε) < (v:E)^(2/5-ε):=by
      calc
       28*(v:E)^(1/5+ε) < (v:E)^(1/5-2*ε)*(v:E)^(1/5+ε) :=mul_lt_mul_of_pos_right h2 (by positivity)
       _ = (v:E)^(2/5-ε):=by rw [← rpow_add hvR];congr 1;ring
     have:14*(H:E) < (D:E):=by linarith
     exact_mod_cast this
    have hvD:8*(v+H) < D^3:=by
     have hH_le_v:(H:E)<=(v:E):=by
      have:(v:E)^(1/5+ε)<=(v:E)^(1/2:E) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
      have:(2:E)<=(v:E)^(1/2:E):=by
       have h:=rpow_le_rpow_of_exponent_le hv_ge1 (show (1/100:E)<=1/2 by norm_num);linarith
      have hv2:(v:E)^(1/2:E)*(v:E)^(1/2:E)=(v:E):=by rw [← rpow_add hvR];norm_num
      nlinarith
     have h1:8*((v:E)+(H:E))<=16*(v:E):=by linarith
     have h2:(16:E) < (v:E)^(1/5-3*ε):=by
      have:(v:E)^(1/100:E)<=(v:E)^(1/5-3*ε) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
      linarith
     have h3:16*(v:E) < (v:E)^(6/5-3*ε):=by
      calc
       16*(v:E) < (v:E)^(1/5-3*ε)*(v:E):=mul_lt_mul_of_pos_right h2 hvR
       _ = (v:E)^(6/5-3*ε):=by
        conv_lhs=>arg 2;rw [← rpow_one (v:E)]
        rw [← rpow_add hvR];congr 1;ring
     have h4:(v:E)^(6/5-3*ε) < (D:E)^3:=by
      have h:=pow_lt_pow_left₀ hB (by positivity) (by norm_num:3≠0);rw [← rpow_natCast _ 3,← rpow_mul hvR.le] at h;exact (by congr 1;push_cast;ring:(v:E)^(6/5-3*ε)=_).trans_lt h
     have:8*((v:E)+(H:E)) < (D:E)^3:=by linarith
     exact_mod_cast this
    have hRC:=dyadicPrimeSet_rangeC_le (show 1<=v by omega) hD_ge1 (show 1<=H by omega) hHD hvD
    have hle1:(2*(v:E)/(D:E))^(1/3:E)<=2*(v:E)^(1/5+ε/3):=by
     have h1:2*(v:E)/(D:E)<=2*(v:E)^(3/5+ε):=by
      calc
       2*(v:E)/(D:E)<=2*(v:E)/(v:E)^(2/5-ε) :=div_le_div_of_nonneg_left (by positivity) (by positivity) hB.le
       _ = 2*((v:E)^(1:E)*((v:E)^(2/5-ε))⁻¹):=by rw [rpow_one];ring
       _ = 2*(v:E)^(3/5+ε):=by rw [← rpow_neg hvR.le,← rpow_add hvR];congr 2;ring
     have hrp:=rpow_le_rpow (by positivity) h1 (by norm_num:(0:E)<=1/3);rw [mul_rpow (by norm_num) (by positivity),← rpow_mul hvR.le] at hrp
     have h213:(2:E)^(1/3:E)<=2:=by
      calc
       (2:E)^(1/3:E)<=(2:E)^(1:E):=rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
       _ = 2:=rpow_one 2
     calc
      (2*(v:E)/(D:E))^(1/3:E)<=(2:E)^(1/3:E)*(v:E)^((3/5+ε)*(1/3:E)):=hrp
      _ <= 2*(v:E)^(1/5+ε/3):=by
       rw [show (3/5+ε)*(1/3:E)=1/5+ε/3 by ring];exact mul_le_mul_of_nonneg_right h213 (by positivity)
    have hle2:2*(v:E)^(1/5+ε/3)+1<=(v:E)^(1/5+9*ε/10)/8:=by
     have h1:(1:E)<=(v:E)^(1/5+ε/3):=one_le_rpow hv_ge1 (by linarith)
     have h2:(24:E)<=(v:E)^(17*ε/30):=by
      have:(v:E)^(ε/10)<=(v:E)^(17*ε/30) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
      linarith
     rw [le_div_iff₀ (by norm_num)]
     calc
      (2*(v:E)^(1/5+ε/3)+1)*8<=24*(v:E)^(1/5+ε/3):=by linarith
      _ <= (v:E)^(17*ε/30)*(v:E)^(1/5+ε/3) :=mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (v:E)^(1/5+9*ε/10):=by rw [← rpow_add hvR];congr 1;ring
    linarith
 by_contra hnone
 push Not at hnone
 have hH_le_v:H<=v:=by
  have h1:(v:E)^(1/5+ε)<=(v:E)^(1/2:E) :=rpow_le_rpow_of_exponent_le hv_ge1 (by linarith)
  have h2:(2:E)<=(v:E)^(1/2:E):=by
   have:=rpow_le_rpow_of_exponent_le hv_ge1 (show (1/100:E)<=1/2 by norm_num)
   linarith
  have h3:(v:E)^(1/2:E)*(v:E)^(1/2:E)=(v:E):=by rw [← rpow_add hvR];norm_num
  have:(H:E)<=(v:E):=by nlinarith
  exact_mod_cast this
 let Jsmall:=(Finset.Ioo 0 H).filter (fun j=>∃ p,p < H/4/\Nat.Prime p/\p^2∣v+j)
 let Jdyad:ℕ->Finset ℕ:=fun t =>
  (Finset.Ioo 0 H).filter (fun j=>∃ p∈Finset.Ico (D_of t) (2*D_of t),Nat.Prime p/\p^2∣v+j)
 let Tgood:=(Finset.range K).filter (fun t=>(D_of t)^2 < 2*v)
 have hcover:Finset.Ioo 0 H⊆Jsmall∪Tgood.biUnion Jdyad:=by
  intro j hj;have hj_ioo:=Finset.mem_Ioo.mp hj;have hnsq:=hnone j hj;rw [Nat.squarefree_iff_prime_squarefree] at hnsq
  push Not at hnsq
  obtain ⟨p,hp_pr,hp_dvd⟩:=hnsq;have hp_sq_dvd:p^2∣v+j:=by simpa [sq] using hp_dvd
  have hp_sq_lt:p^2 < 2*v:=by
   have h1:p^2<=v+j:=Nat.le_of_dvd (by omega) hp_sq_dvd;omega
  by_cases hp_sm:p < H/4
  · exact Finset.mem_union_left _ (mem_filter.mpr ⟨hj,p,hp_sm,hp_pr,hp_sq_dvd⟩)
  ·
   apply Finset.mem_union_right;have hq_pos:1<=p/(H/4):=Nat.div_pos (by omega) (by omega);let t:=Nat.log 2 (p/(H/4));have ht_lo:2^t<=p/(H/4):=Nat.pow_log_le_self 2 (by omega);have ht_hi:p/(H/4) < 2^(t+1):=Nat.lt_pow_succ_log_self (by norm_num) _
   have hD_le_p:D_of t<=p:=by
    dsimp [D_of]
    calc
     (H/4)*2^t<=(H/4)*(p/(H/4)):=Nat.mul_le_mul_left _ ht_lo
     _ <= p:=Nat.mul_div_le p (H/4)
   have hp_lt_2D:p < 2*D_of t:=by
    dsimp [D_of]
    have h1:p < (H/4)*(p/(H/4)+1):=by
     have:=Nat.div_add_mod p (H/4)
     have:=Nat.mod_lt p (show 0 < H/4 by omega)
     nlinarith
    have h2:p/(H/4)+1<=2^(t+1):=ht_hi;have h3:(H/4)*2^(t+1)=2*((H/4)*2^t):=by rw [pow_succ];ring
    calc
     p < (H/4)*(p/(H/4)+1):=h1
     _ <= (H/4)*2^(t+1):=Nat.mul_le_mul_left _ h2
     _ = 2*((H/4)*2^t):=h3
   have ht_lt_K:t < K:=by
    have hle_2v:p/(H/4)<=2*v:=by
     have hp_le:p<=2*v:=by nlinarith
     exact le_trans (Nat.div_le_self p (H/4)) hp_le
    have hlog_le:t<=Nat.log 2 (2*v):=Nat.log_mono_right hle_2v;dsimp [K];omega
   have hD_sq_lt:(D_of t)^2 < 2*v:=lt_of_le_of_lt (Nat.pow_le_pow_left hD_le_p 2) hp_sq_lt;exact Finset.mem_biUnion.mpr ⟨t,mem_filter.mpr ⟨Finset.mem_range.mpr ht_lt_K,hD_sq_lt⟩,mem_filter.mpr ⟨hj,p,Finset.mem_Ico.mpr ⟨hD_le_p,hp_lt_2D⟩,hp_pr,hp_sq_dvd⟩⟩
 have hcard_union:((Finset.Ioo 0 H).card:E) ≤ (Jsmall.card:E)+∑ t∈Tgood,((Jdyad t).card:E):=by
  have h1:(Finset.Ioo 0 H).card<=Jsmall.card+(Tgood.biUnion Jdyad).card :=(Finset.card_le_card hcover).trans (Finset.card_union_le _ _);have h2:(Tgood.biUnion Jdyad).card<=∑ t∈Tgood,(Jdyad t).card:=Finset.card_biUnion_le
  exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
 have hsmall_lt:(Jsmall.card:E) < (3/4:E)*(H:E):=card_small_prime_sq_lt v H (by omega)
 have hdyad_sum:∑ t∈Tgood,((Jdyad t).card:E)<=(H:E)/8:=by
  calc
   ∑ t∈Tgood,((Jdyad t).card:E)<=∑ t∈Tgood,((dyadicPrimeSet v H (D_of t)).card:E):=by
    apply sum_le_sum;intro t _
    have hDH:H<=(D_of t)^2:=by
     have h1:H/4<=D_of t:=by dsimp [D_of];exact Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) t)
     have h2:H<=4*(H/4)+3:=by omega
     have h3:(H/4)^2<=(D_of t)^2:=Nat.pow_le_pow_left h1 2;nlinarith
    exact_mod_cast card_dyadic_covered_le v H (D_of t) hDH
   _ <= ∑ _t∈Tgood,((H:E)/(8*(K:E))):=by
    apply sum_le_sum;intro t ht;have hD_lo:H/4<=D_of t:=by dsimp [D_of];exact Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) t)
    exact hdyad_bound (D_of t) hD_lo (mem_filter.mp ht).2
   _ = (Tgood.card:E)*((H:E)/(8*(K:E))):=by simp
   _ <= (K:E)*((H:E)/(8*(K:E))):=by
    have hle:Tgood.card<=K:=(Finset.card_filter_le _ _).trans (card_range K).le;exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (by positivity)
   _ = (H:E)/8:=by field_simp [hK_pos.ne']
 have hIoo:((Finset.Ioo 0 H).card:E)=(H:E)-1:=by rw [Nat.card_Ioo,Nat.sub_zero,Nat.cast_sub (by omega:1<=H),Nat.cast_one]
 linarith
theorem exists_squarefree_in_interval_of_large {ε:E} (hε:0 < ε) (hε_le:ε<=1/1000) :
  ∃ N₀:ℕ,1000<=N₀/\∀ N:ℕ,N₀<=N->∀ v H:ℕ,v < N → (N:E)^(1/5+ε)<=(H:E) → ∃ j∈Finset.Ioo 0 H,Squarefree (v+j):=by
 obtain ⟨V₀,hV₀_ge,hnear⟩:=exists_squarefree_near hε hε_le;let N₀:ℕ:=(16*V₀)^5
 refine ⟨N₀,by
  dsimp [N₀]
  exact le_trans hV₀_ge (le_trans (by omega:V₀<=16*V₀) (Nat.le_self_pow (by norm_num) _)),?_⟩
 intro N hN v H hvN hH_ge;have hN_pos:(0:E) < (N:E):=by exact_mod_cast (show 0 < N by dsimp [N₀] at hN;nlinarith)
 by_cases hv:V₀<=v
 ·
  obtain ⟨j,hj,hsq⟩:=hnear v hv
  have hceil_le:⌈(v:E)^(1/5+ε)⌉₊<=H:=by
   apply Nat.ceil_le.mpr;have h1:(v:E)^(1/5+ε)<=(N:E)^(1/5+ε) :=rpow_le_rpow (Nat.cast_nonneg v) (by exact_mod_cast hvN.le) (by linarith);exact h1.trans hH_ge
  have hj_H:j∈Finset.Ioo 0 H:=by
   rcases Finset.mem_Ioo.mp hj with ⟨h1,h2⟩;exact Finset.mem_Ioo.mpr ⟨h1,lt_of_lt_of_le h2 hceil_le⟩
  exact ⟨j,hj_H,hsq⟩
 ·
  let M:ℕ:=16*V₀
  have hM_le_H:M<=H:=by
   have h1:(M:E)^5<=(N:E):=by exact_mod_cast hN
   have hrp:=rpow_le_rpow (by positivity) h1 (by norm_num:(0:E)<=1/5);rw [← rpow_natCast (M:E) 5,← rpow_mul (Nat.cast_nonneg M)] at hrp;norm_num at hrp
   have h2:(N:E)^(1/5:E)<=(N:E)^(1/5+ε) := rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1<=N by dsimp [N₀] at hN;nlinarith))
     (by linarith)
   have:(M:E)<=(H:E):=hrp.trans (h2.trans hH_ge)
   exact_mod_cast this
  have hvM:v+M<=(M/4)^2:=by
   have hM4:M/4=4*V₀:=by dsimp [M];omega
   rw [hM4];dsimp [M];nlinarith
  obtain ⟨j,hj,hsq⟩:=exists_squarefree_of_small_v v M (by dsimp [M];omega) hvM
  have hj_H:j∈Finset.Ioo 0 H:=by
   rcases Finset.mem_Ioo.mp hj with ⟨h1,h2⟩;exact Finset.mem_Ioo.mpr ⟨h1,lt_of_lt_of_le h2 hM_le_H⟩
  exact ⟨j,hj_H,hsq⟩
lemma exists_round_int_div (a b:ℤ) (hb:0 < b) :
  ∃ q:ℤ,|(q:E)*(b:E)-(a:E)| ≤ (b:E)/2:=by
 let r:ℤ:=a % b;let d:ℤ:=a/b;have hdiv:b*d+r=a:=Int.mul_ediv_add_emod a b;have hr0:0<=r:=Int.emod_nonneg a (ne_of_gt hb);have hrb:r < b:=Int.emod_lt_of_pos a hb
 by_cases hhalf:2*r<=b
 ·
  refine ⟨d,?_⟩
  have heq:(d:E)*(b:E)-(a:E)=-(r:E):=by
   have:(b:E)*(d:E)+(r:E)=(a:E):=by exact_mod_cast hdiv
   linarith
  rw [heq,abs_neg,abs_of_nonneg (by exact_mod_cast hr0)];have h2:2*(r:E)<=(b:E):=by exact_mod_cast hhalf
  linarith
 ·
  refine ⟨d+1,?_⟩
  have heq:((d+1:ℤ):E)*(b:E)-(a:E)=(b:E)-(r:E):=by
   have:(b:E)*(d:E)+(r:E)=(a:E):=by exact_mod_cast hdiv
   push_cast;linarith
  have hrbR:(r:E) < (b:E):=by exact_mod_cast hrb
  rw [heq,abs_of_nonneg (by linarith)];have h2:(b:E) < 2*(r:E):=by exact_mod_cast (lt_of_not_ge hhalf)
  linarith
lemma eq_of_nat_lt_of_dvd_sub {M i i':ℕ} (hi:i < M) (hi':i' < M)
  (hdvd:(M:ℤ)∣((i:ℤ)-(i':ℤ))):i=i':=by
 obtain ⟨k,hk⟩:=hdvd
 have hk0:k=0:=by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
   have:k<=-1:=by omega
   have:(M:ℤ)*k<=-(M:ℤ):=by nlinarith
   omega
  ·
   have:1<=k:=by omega
   have:(M:ℤ)<=(M:ℤ)*k:=by nlinarith
   omega
 rw [hk0,mul_zero] at hk;omega
lemma card_int_congr_interval (c r m:ℤ) (hm:0 < m) (hcop:IsCoprime c m)
  (lo hi:E) (hlo:lo<=hi) :
  (((Finset.Icc ⌊lo⌋ ⌈hi⌉).filter (fun z:ℤ=>m∣c*z-r)).card:E) ≤ (hi-lo)/(m:E)+3:=by
 let S:=(Finset.Icc ⌊lo⌋ ⌈hi⌉).filter (fun z:ℤ=>m∣c*z-r);change (S.card:E)<=(hi-lo)/(m:E)+3
 by_cases hne:S.Nonempty
 ·
  obtain ⟨z0,hz0⟩:=hne;have hz0_dvd:m∣c*z0-r:=(mem_filter.mp hz0).2
  have hstep:∀ z∈S,m∣z-z0:=by
   intro z hz;have hzd:m∣c*z-r:=(mem_filter.mp hz).2
   have hdiff:m∣c*(z-z0):=by
    have:c*(z-z0)=(c*z-r)-(c*z0-r):=by ring
    rw [this];exact dvd_sub hzd hz0_dvd
   exact hcop.symm.dvd_of_dvd_mul_left hdiff
  let zmin:=S.min' ⟨z0,hz0⟩;have hzmin_mem:zmin∈S:=Finset.min'_mem S _;have hlo_min:⌊lo⌋<=zmin:=(Finset.mem_Icc.mp (mem_filter.mp hzmin_mem).1).1;let g:ℤ->ℕ:=fun z=>((z-zmin)/m).toNat
  have hg_inj:Set.InjOn g (S:Set ℤ):=by
   intro x hx y hy hxy;have hxge:zmin<=x:=Finset.min'_le S x hx;have hyge:zmin<=y:=Finset.min'_le S y hy
   have hdx:m∣x-zmin:=by
    have:x-zmin=(x-z0)-(zmin-z0):=by ring
    rw [this];exact dvd_sub (hstep x hx) (hstep zmin hzmin_mem)
   have hdy:m∣y-zmin:=by
    have:y-zmin=(y-z0)-(zmin-z0):=by ring
    rw [this];exact dvd_sub (hstep y hy) (hstep zmin hzmin_mem)
   obtain ⟨kx,hkx⟩:=hdx;obtain ⟨ky,hky⟩:=hdy;have hkx0:0<=kx:=by nlinarith
   have hky0:0<=ky:=by nlinarith
   have hgx:g x=kx.toNat:=by dsimp [g];rw [hkx,Int.mul_ediv_cancel_left _ (ne_of_gt hm)]
   have hgy:g y=ky.toNat:=by dsimp [g];rw [hky,Int.mul_ediv_cancel_left _ (ne_of_gt hm)]
   rw [hgx,hgy] at hxy;have hkeq:kx=ky:=by omega
   rw [hkeq] at hkx;omega
  have hhi_max:∀ z∈S,(g z:E)<=(hi-lo)/(m:E)+2:=by
   intro z hz;have hzge:zmin<=z:=Finset.min'_le S z hz;have hzhi:z<=⌈hi⌉:=(Finset.mem_Icc.mp (mem_filter.mp hz).1).2
   have hdx:m∣z-zmin:=by
    have:z-zmin=(z-z0)-(zmin-z0):=by ring
    rw [this];exact dvd_sub (hstep z hz) (hstep zmin hzmin_mem)
   obtain ⟨k,hk⟩:=hdx;have hk0:0<=k:=by nlinarith
   have hgz:g z=k.toNat:=by dsimp [g];rw [hk,Int.mul_ediv_cancel_left _ (ne_of_gt hm)]
   rw [hgz];have hkR:((k.toNat:ℕ):E)=(k:E):=by exact_mod_cast Int.toNat_of_nonneg hk0
   rw [hkR];have hmR:(0:E) < (m:E):=by exact_mod_cast hm
   have h1:(z:E)<=hi+1:=by
    have:(z:E)<=(⌈hi⌉:E):=by exact_mod_cast hzhi
    linarith [Int.ceil_lt_add_one hi]
   have h2:lo-1 < (zmin:E):=by
    have:(⌊lo⌋:E)<=(zmin:E):=by exact_mod_cast hlo_min
    linarith [Int.sub_one_lt_floor lo]
   have hmk:(m:E)*(k:E)=(z:E)-(zmin:E):=by exact_mod_cast hk.symm
   have hm1:(1:E)<=(m:E):=by exact_mod_cast hm
   have hle_m:(k:E)*(m:E)<=(hi-lo)+2*(m:E):=by nlinarith
   have hdiv_le:(k:E)<=((hi-lo)+2*(m:E))/(m:E):=(le_div_iff₀ hmR).mpr hle_m;have hsimp:((hi-lo)+2*(m:E))/(m:E)=(hi-lo)/(m:E)+2:=by field_simp [hmR.ne']
   linarith
  let N:ℕ:=⌊(hi-lo)/(m:E)+2⌋₊+1
  have hsub:S.image g⊆Finset.range N:=by
   intro t ht;rcases Finset.mem_image.mp ht with ⟨z,hz,rfl⟩;rw [Finset.mem_range];have hle:=hhi_max z hz
   have hlt:(g z:E) < (N:E):=by
    dsimp [N];push_cast;linarith [Nat.lt_floor_add_one ((hi-lo)/(m:E)+2)]
   exact_mod_cast hlt
  have hcard:S.card<=N:=by
   calc
    S.card=(S.image g).card:=(Finset.card_image_iff.mpr hg_inj).symm
    _ <= (Finset.range N).card:=Finset.card_le_card hsub
    _ = N:=card_range N
  have hN:(N:E)<=(hi-lo)/(m:E)+3:=by
   dsimp [N];push_cast
   have hnn:0<=(hi-lo)/(m:E)+2:=by
    have hmR:(0:E) < (m:E):=by exact_mod_cast hm
    have:0<=(hi-lo)/(m:E):=div_nonneg (sub_nonneg.mpr hlo) hmR.le
    linarith
   linarith [Nat.floor_le hnn]
  exact (by exact_mod_cast hcard:(S.card:E)<=(N:E)).trans hN
 ·
  rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero];have hmR:(0:E) < (m:E):=by exact_mod_cast hm
  have:0<=(hi-lo)/(m:E):=div_nonneg (sub_nonneg.mpr hlo) hmR.le
  linarith
lemma card_int_interval (lo hi:E) (hlo:lo<=hi) :
  ((Finset.Icc ⌊lo⌋ ⌈hi⌉).card:E)<=(hi-lo)+3:=by
 have h:=card_int_congr_interval 1 0 1 (by decide) isCoprime_one_right lo hi hlo;simp only [one_mul,sub_zero,one_dvd,Finset.filter_true,Int.cast_one,div_one] at h;exact h
lemma exists_unimodular_basis_2d (N:E × E->E)
  (hadd:∀ u v,N (u.1+v.1,u.2+v.2)<=N u+N v)
  (hsmul:∀ (t:E) (u:E × E),N (t*u.1,t*u.2) = |t| * N u)
  (w1 w2:ℤ × ℤ) (hdet:w1.1*w2.2-w1.2*w2.1≠0)
  (hw1:N (w1.1,w1.2)<=1) (hw2:N (w2.1,w2.2)<=1) :
  ∃ e1 e2:ℤ × ℤ,(e1.1*e2.2-e1.2*e2.1=1\/e1.1*e2.2-e1.2*e2.1=-1) ∧ N (e1.1,e1.2)<=1/\N (e2.1,e2.2)<=3/2:=by
 have hw1_ne:w1.1≠0\/w1.2≠0:=by
  by_contra h;push Not at h;rw [h.1,h.2] at hdet;simp at hdet
 let g:ℤ:=(Int.gcd w1.1 w1.2:ℤ)
 have hg_pos:0 < g:=by
  have hnat:0 < Int.gcd w1.1 w1.2:=by
   rcases hw1_ne with h1 | h2
   · exact Int.gcd_pos_of_ne_zero_left w1.2 h1
   · exact Int.gcd_pos_of_ne_zero_right w1.1 h2
  dsimp [g];exact_mod_cast hnat
 have hgd1:g∣w1.1:=Int.gcd_dvd_left w1.1 w1.2;have hgd2:g∣w1.2:=Int.gcd_dvd_right w1.1 w1.2;let e1:ℤ × ℤ:=(w1.1/g,w1.2/g);have he1_mul1:g*e1.1=w1.1:=Int.mul_ediv_cancel' hgd1;have he1_mul2:g*e1.2=w1.2:=Int.mul_ediv_cancel' hgd2
 have hcop:IsCoprime e1.1 e1.2:=by
  have hbez:=Int.gcd_eq_gcd_ab w1.1 w1.2;refine ⟨Int.gcdA w1.1 w1.2,Int.gcdB w1.1 w1.2,?_⟩
  have hmul:g*(Int.gcdA w1.1 w1.2*e1.1+Int.gcdB w1.1 w1.2*e1.2)=g*1:=by
   calc
    g*(Int.gcdA w1.1 w1.2*e1.1+Int.gcdB w1.1 w1.2*e1.2)
     = (g*e1.1)*Int.gcdA w1.1 w1.2+(g*e1.2)*Int.gcdB w1.1 w1.2:=by ring
    _ = w1.1*Int.gcdA w1.1 w1.2+w1.2*Int.gcdB w1.1 w1.2:=by rw [he1_mul1,he1_mul2]
    _ = g:=hbez.symm
    _ = g*1:=(mul_one g).symm
  exact mul_left_cancel₀ (ne_of_gt hg_pos) hmul
 obtain ⟨u,v,huv⟩:=hcop;let f2:ℤ × ℤ:=(-v,u);have hdet_f2:e1.1*f2.2-e1.2*f2.1=1:=by dsimp [f2];linarith
 let a:ℤ:=w2.1*f2.2-w2.2*f2.1;let b:ℤ:=e1.1*w2.2-e1.2*w2.1
 have hw2_1:w2.1=a*e1.1+b*f2.1:=by
  have:(e1.1*f2.2-e1.2*f2.1)*w2.1=a*e1.1+b*f2.1:=by dsimp [a,b];ring
  rw [hdet_f2,one_mul] at this;exact this
 have hw2_2:w2.2=a*e1.2+b*f2.2:=by
  have:(e1.1*f2.2-e1.2*f2.1)*w2.2=a*e1.2+b*f2.2:=by dsimp [a,b];ring
  rw [hdet_f2,one_mul] at this;exact this
 have hb_ne:b≠0:=by
  intro hb0;apply hdet;rw [← he1_mul1,← he1_mul2]
  have:(g*e1.1)*w2.2-(g*e1.2)*w2.1=g*b:=by dsimp [b];ring
  rw [this,hb0,mul_zero]
 let sgn:ℤ:=if 0 < b then 1 else -1;have hsgn_sq:sgn*sgn=1:=by dsimp [sgn];split_ifs <;> norm_num
 let f2':ℤ × ℤ:=(sgn*f2.1,sgn*f2.2);let b':ℤ:=sgn*b;have hb'_pos:0 < b':=by dsimp [b',sgn];split_ifs with h <;> omega
 have hw2_1':w2.1=a*e1.1+b'*f2'.1:=by dsimp [b',f2'];rw [hw2_1];linear_combination -b*f2.1*hsgn_sq
 have hw2_2':w2.2=a*e1.2+b'*f2'.2:=by dsimp [b',f2'];rw [hw2_2];linear_combination -b*f2.2*hsgn_sq
 obtain ⟨q,hq⟩:=exists_round_int_div a b' hb'_pos;let e2:ℤ × ℤ:=(f2'.1+q*e1.1,f2'.2+q*e1.2)
 have hN_nn:∀ p:E × E,0<=N p:=by
  intro p;have h0:=hsmul 0 p;have hneg:=hadd p (-p.1,-p.2);have hneg2:=hsmul (-1) p;simp only [zero_mul,abs_zero,neg_one_mul,abs_neg,abs_one,one_mul] at h0 hneg2;have hzero:(p.1+-p.1,p.2+-p.2)=(0,0):=by simp
  rw [hzero,hneg2] at hneg;linarith
 have hNe1:N (e1.1,e1.2)<=1:=by
  have hgR:(0:E) < (g:E):=by exact_mod_cast hg_pos
  have hg1:(1:E)<=(g:E):=by exact_mod_cast hg_pos
  have h1:N (w1.1,w1.2)=(g:E)*N (e1.1,e1.2):=by
   have hm1:(w1.1:E)=(g:E)*(e1.1:E):=by exact_mod_cast he1_mul1.symm
   have hm2:(w1.2:E)=(g:E)*(e1.2:E):=by exact_mod_cast he1_mul2.symm
   rw [hm1,hm2,hsmul (g:E) (e1.1,e1.2),abs_of_pos hgR]
  nlinarith [hN_nn (e1.1,e1.2)]
 have hNe2:N (e2.1,e2.2)<=3/2:=by
  have hbR:(0:E) < (b':E):=by exact_mod_cast hb'_pos
  have hb1:(1:E)<=(b':E):=by exact_mod_cast hb'_pos
  let t1:E:=((q:E)*(b':E)-(a:E))/(b':E);let t2:E:=1/(b':E)
  have he2_eq:((e2.1:E),(e2.2:E)) = (t1*(e1.1:E)+t2*(w2.1:E),t1*(e1.2:E)+t2*(w2.2:E)):=by
   have h1:(w2.1:E)=(a:E)*(e1.1:E)+(b':E)*(f2'.1:E):=by exact_mod_cast hw2_1'
   have h2:(w2.2:E)=(a:E)*(e1.2:E)+(b':E)*(f2'.2:E):=by exact_mod_cast hw2_2'
   ext <;> dsimp [e2,t1,t2] <;> push_cast <;> field_simp [hbR.ne'] <;> linarith
  rw [he2_eq];have htri:=hadd (t1*(e1.1:E),t1*(e1.2:E)) (t2*(w2.1:E),t2*(w2.2:E));have hs1:=hsmul t1 (e1.1,e1.2);have hs2:=hsmul t2 (w2.1,w2.2);have ht1:|t1| ≤ 1/2:=by dsimp [t1];rw [abs_div,abs_of_pos hbR,div_le_iff₀ hbR];linarith
  have ht2:|t2| ≤ 1:=by dsimp [t2];rw [abs_of_pos (by positivity),div_le_one hbR];exact hb1
  nlinarith [hN_nn (e1.1,e1.2),hN_nn (w2.1,w2.2)]
 refine ⟨e1,e2,?_,hNe1,hNe2⟩;have hd:e1.1*e2.2-e1.2*e2.1=sgn:=by dsimp [e2,f2'];linear_combination sgn*hdet_f2
 rw [hd];dsimp [sgn];split_ifs <;> simp
theorem card_rank2_box_le {p1 p2 A B:E} (hp1:0 < p1) (hp2:0 < p2)
  (hA:0 < A) (hB:0 < B)
  (S:Finset (ℤ × ℤ))
  (hS:∀ v∈S,|p1*(v.1:E)| ≤ A/\|p1*(v.1:E)-p2*(v.2:E)| ≤ B)
  (hrank:∃ w1∈S,∃ w2∈S,w1.1*w2.2-w1.2*w2.1≠0) :
  (S.card:E)<=100*A*B/(p1*p2):=by
 let N:E × E->E:=fun u=>max (|p1*u.1| / A) (|p1*u.1-p2*u.2| / B)
 have hadd:∀ u v,N (u.1+v.1,u.2+v.2)<=N u+N v:=by
  intro u v;dsimp [N];apply max_le
  ·
    have h1:|p1*(u.1+v.1)| ≤ |p1*u.1| + |p1*v.1|:=by rw [mul_add];exact abs_add_le _ _
    have h2:|p1*(u.1+v.1)| / A ≤ |p1*u.1| / A + |p1*v.1| / A:=by rw [← add_div];exact div_le_div_of_nonneg_right h1 hA.le
    linarith [le_max_left (|p1*u.1| / A) (|p1*u.1-p2*u.2| / B),le_max_left (|p1*v.1| / A) (|p1*v.1-p2*v.2| / B)]
  ·
    have h1:|p1*(u.1+v.1)-p2*(u.2+v.2)| ≤
      |p1*u.1-p2*u.2| + |p1*v.1-p2*v.2|:=by
     have:p1*(u.1+v.1)-p2*(u.2+v.2) = (p1*u.1-p2*u.2)+(p1*v.1-p2*v.2):=by ring
     rw [this];exact abs_add_le _ _
    have h2:|p1*(u.1+v.1)-p2*(u.2+v.2)| / B ≤
      |p1*u.1-p2*u.2| / B + |p1*v.1-p2*v.2| / B:=by
     rw [← add_div];exact div_le_div_of_nonneg_right h1 hB.le
    linarith [le_max_right (|p1*u.1| / A) (|p1*u.1-p2*u.2| / B),le_max_right (|p1*v.1| / A) (|p1*v.1-p2*v.2| / B)]
 have hsmul:∀ (t:E) (u:E × E),N (t*u.1,t*u.2) = |t| * N u:=by
  intro t u;dsimp [N];have h1:|p1*(t*u.1)| / A = |t| * (|p1*u.1| / A):=by rw [show p1*(t*u.1)=t*(p1*u.1) by ring,abs_mul,mul_div_assoc]
  have h2:|p1*(t*u.1)-p2*(t*u.2)| / B = |t| * (|p1*u.1-p2*u.2| / B):=by
    rw [show p1*(t*u.1)-p2*(t*u.2)=t*(p1*u.1-p2*u.2) by ring,abs_mul,mul_div_assoc]
  rw [h1,h2,mul_max_of_nonneg _ _ (abs_nonneg t)]
 have hNS:∀ v∈S,N (v.1,v.2)<=1:=by
  intro v hv;dsimp [N];exact max_le ((div_le_one hA).mpr (hS v hv).1) ((div_le_one hB).mpr (hS v hv).2)
 obtain ⟨w1,hw1,w2,hw2,hdet⟩:=hrank;obtain ⟨e1,e2,hedet,hNe1,hNe2⟩ :=exists_unimodular_basis_2d N hadd hsmul w1 w2 hdet (hNS w1 hw1) (hNS w2 hw2);let M:ℕ:=⌈max (2*p1/A) (2*p2/B)⌉₊+10;have hM_pos:0 < M:=by dsimp [M];omega
 have hMR:(0:E) < (M:E):=by exact_mod_cast hM_pos
 have hM1:2*p1/A<=(M:E):=by
  have h1:2*p1/A<=max (2*p1/A) (2*p2/B):=le_max_left _ _;have h2:=Nat.le_ceil (max (2*p1/A) (2*p2/B));dsimp [M];push_cast;linarith
 have hM2:2*p2/B<=(M:E):=by
  have h1:2*p2/B<=max (2*p1/A) (2*p2/B):=le_max_right _ _;have h2:=Nat.le_ceil (max (2*p1/A) (2*p2/B));dsimp [M];push_cast;linarith
 let dom:=S×ˢ(Finset.range M×ˢFinset.range M)
 let φ:(ℤ × ℤ) × (ℕ × ℕ)->ℤ × ℤ:=fun t =>
  ((M:ℤ)*t.1.1+(t.2.1:ℤ)*e1.1+(t.2.2:ℤ)*e2.1,(M:ℤ)*t.1.2+(t.2.1:ℤ)*e1.2+(t.2.2:ℤ)*e2.2)
 have hφ_inj:Set.InjOn φ (dom:Set _):=by
  rintro ⟨v,i,j⟩ h1 ⟨v',i',j'⟩ h2 heq;simp only [dom,Finset.mem_coe,mem_product,Finset.mem_range] at h1 h2;have he1:=congrArg Prod.fst heq;have he2:=congrArg Prod.snd heq;dsimp [φ] at he1 he2
  have hdi:(M:ℤ)∣((i:ℤ)-(i':ℤ)):=by
    have hlin:(e1.1*e2.2-e1.2*e2.1)*((i:ℤ)-(i':ℤ)) = (M:ℤ)*((v'.1-v.1)*e2.2-(v'.2-v.2)*e2.1):=by linear_combination e2.2*he1-e2.1*he2
    rcases hedet with hd | hd
    · rw [hd,one_mul] at hlin;exact ⟨_,hlin⟩
    ·
     rw [hd,neg_one_mul] at hlin
     exact ⟨-((v'.1-v.1)*e2.2-(v'.2-v.2)*e2.1),by linarith⟩
  have hdj:(M:ℤ)∣((j:ℤ)-(j':ℤ)):=by
    have hlin:(e1.1*e2.2-e1.2*e2.1)*((j:ℤ)-(j':ℤ)) = (M:ℤ)*(e1.1*(v'.2-v.2)-e1.2*(v'.1-v.1)):=by linear_combination e1.1*he2-e1.2*he1
    rcases hedet with hd | hd
    · rw [hd,one_mul] at hlin;exact ⟨_,hlin⟩
    ·
     rw [hd,neg_one_mul] at hlin
     exact ⟨-(e1.1*(v'.2-v.2)-e1.2*(v'.1-v.1)),by linarith⟩
  have hi_eq:i=i':=eq_of_nat_lt_of_dvd_sub h1.2.1 h2.2.1 hdi;have hj_eq:j=j':=eq_of_nat_lt_of_dvd_sub h1.2.2 h2.2.2 hdj;subst hi_eq;subst hj_eq;have hv1:v.1=v'.1:=mul_left_cancel₀ (by exact_mod_cast hM_pos.ne') (by linarith:(M:ℤ)*v.1=(M:ℤ)*v'.1)
  have hv2:v.2=v'.2:=mul_left_cancel₀ (by exact_mod_cast hM_pos.ne') (by linarith:(M:ℤ)*v.2=(M:ℤ)*v'.2);exact Prod.ext (Prod.ext hv1 hv2) rfl
 have hφ_bd:∀ t∈dom,
    |p1*((φ t).1:E)| ≤ 4*(M:E)*A ∧
    |p1*((φ t).1:E)-p2*((φ t).2:E)| ≤ 4*(M:E)*B:=by
  rintro ⟨v,i,j⟩ ht;simp only [dom,mem_product,Finset.mem_range] at ht;have hiM:(i:E)<=(M:E):=by exact_mod_cast ht.2.1.le
  have hjM:(j:E)<=(M:E):=by exact_mod_cast ht.2.2.le
  have hNφ:N ((φ (v,i,j)).1,(φ (v,i,j)).2)<=4*(M:E):=by
    have heq:(((φ (v,i,j)).1:E),((φ (v,i,j)).2:E)) = (((M:E)*(v.1:E)+(i:E)*(e1.1:E))+(j:E)*(e2.1:E),((M:E)*(v.2:E)+(i:E)*(e1.2:E))+(j:E)*(e2.2:E)):=by ext <;> dsimp [φ] <;> push_cast <;> ring
    rw [heq]
    have h1:=hadd ((M:E)*(v.1:E)+(i:E)*(e1.1:E),(M:E)*(v.2:E)+(i:E)*(e1.2:E))
           ((j:E)*(e2.1:E),(j:E)*(e2.2:E))
    have h2:=hadd ((M:E)*(v.1:E),(M:E)*(v.2:E))
           ((i:E)*(e1.1:E),(i:E)*(e1.2:E))
    have hsM:=hsmul (M:E) (v.1,v.2);have hsi:=hsmul (i:E) (e1.1,e1.2);have hsj:=hsmul (j:E) (e2.1,e2.2);rw [abs_of_nonneg hMR.le] at hsM;rw [abs_of_nonneg (Nat.cast_nonneg i)] at hsi;rw [abs_of_nonneg (Nat.cast_nonneg j)] at hsj;have hvN:=hNS v ht.1
    have hNe1_nn:0<=N (e1.1,e1.2) :=le_trans (div_nonneg (abs_nonneg _) hA.le) (le_max_left _ _);have hNe2_nn:0<=N (e2.1,e2.2) :=le_trans (div_nonneg (abs_nonneg _) hA.le) (le_max_left _ _);nlinarith
  exact ⟨(div_le_iff₀ hA).mp ((le_max_left _ _).trans hNφ),(div_le_iff₀ hB).mp ((le_max_right _ _).trans hNφ)⟩
 let I1:=Finset.Icc ⌊-(4*(M:E)*A/p1)⌋ ⌈4*(M:E)*A/p1⌉
 let fiber:ℤ->Finset ℤ:=fun z1 =>
  Finset.Icc ⌊(p1*(z1:E)-4*(M:E)*B)/p2⌋
         ⌈(p1*(z1:E)+4*(M:E)*B)/p2⌉
 let box:=I1.sigma fiber
 have himg_sub:(dom.image φ)⊆box.image (fun p=>(p.1,p.2)):=by
  intro z hz;rcases Finset.mem_image.mp hz with ⟨t,ht,rfl⟩;have hbd:=hφ_bd t ht;refine Finset.mem_image.mpr ⟨⟨(φ t).1,(φ t).2⟩,?_,rfl⟩;rw [Finset.mem_sigma];refine ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩
  ·
    have hle:-(4*(M:E)*A/p1)<=((φ t).1:E):=by
     have:=(abs_le.mp hbd.1).1;rw [← neg_div,div_le_iff₀ hp1];linarith
    exact_mod_cast (Int.floor_le _).trans hle
  ·
    have hle:((φ t).1:E)<=4*(M:E)*A/p1:=by
     have:=(abs_le.mp hbd.1).2;rw [le_div_iff₀ hp1];linarith
    exact_mod_cast hle.trans (Int.le_ceil _)
  ·
    have hle:(p1*((φ t).1:E)-4*(M:E)*B)/p2<=((φ t).2:E):=by
     have:=(abs_le.mp hbd.2).2;rw [div_le_iff₀ hp2];linarith
    exact_mod_cast (Int.floor_le _).trans hle
  ·
    have hle:((φ t).2:E)<=(p1*((φ t).1:E)+4*(M:E)*B)/p2:=by
     have:=(abs_le.mp hbd.2).1;rw [le_div_iff₀ hp2];linarith
    exact_mod_cast hle.trans (Int.le_ceil _)
 have hcard_dom:(dom.card:E)=(S.card:E)*(M:E)^2:=by
  simp only [dom,Finset.card_product,card_range];push_cast;ring
 have hcard_I1:(I1.card:E)<=10*(M:E)*A/p1:=by
  have hlo:-(4*(M:E)*A/p1)<=4*(M:E)*A/p1:=by
    have:0<=4*(M:E)*A/p1:=by positivity
    linarith
  have h:=card_int_interval (-(4*(M:E)*A/p1)) (4*(M:E)*A/p1) hlo
  have h2:(3:E)<=2*(M:E)*A/p1:=by
    rw [le_div_iff₀ hp1]
    have:2*p1<=(M:E)*A:=(div_le_iff₀ hA).mp hM1
    linarith
  have hsum:4*(M:E)*A/p1 - -(4*(M:E)*A/p1)+2*(M:E)*A/p1 = 10*(M:E)*A/p1:=by ring
  change ((Finset.Icc ⌊-(4*(M:E)*A/p1)⌋ ⌈4*(M:E)*A/p1⌉).card:E)<=_;linarith
 have hcard_fib:∀ z1:ℤ,((fiber z1).card:E)<=10*(M:E)*B/p2:=by
  intro z1;have hlo:(p1*(z1:E)-4*(M:E)*B)/p2<=(p1*(z1:E)+4*(M:E)*B)/p2 :=div_le_div_of_nonneg_right (by linarith [mul_nonneg hMR.le hB.le]) hp2.le;have h:=card_int_interval _ _ hlo
  have hdiff:(p1*(z1:E)+4*(M:E)*B)/p2-(p1*(z1:E)-4*(M:E)*B)/p2 = 8*(M:E)*B/p2:=by ring
  rw [hdiff] at h
  have h2:(3:E)<=2*(M:E)*B/p2:=by
    rw [le_div_iff₀ hp2]
    have:2*p2<=(M:E)*B:=(div_le_iff₀ hB).mp hM2
    linarith
  have hsum:8*(M:E)*B/p2+2*(M:E)*B/p2=10*(M:E)*B/p2:=by ring
  change ((Finset.Icc ⌊(p1*(z1:E)-4*(M:E)*B)/p2⌋
         ⌈(p1*(z1:E)+4*(M:E)*B)/p2⌉).card:E)<=_
  linarith
 have hcard_box:(box.card:E)<=100*(M:E)^2*A*B/(p1*p2):=by
  rw [Finset.card_sigma,Nat.cast_sum]
  calc
    (∑ z1∈I1,((fiber z1).card:E))<=∑ _z1∈I1,(10*(M:E)*B/p2) :=sum_le_sum (fun z1 _=>hcard_fib z1)
    _ = (I1.card:E)*(10*(M:E)*B/p2):=by simp
    _ <= (10*(M:E)*A/p1)*(10*(M:E)*B/p2) :=mul_le_mul_of_nonneg_right hcard_I1 (by positivity)
    _ = 100*(M:E)^2*A*B/(p1*p2):=by ring
 have hle:(S.card:E)*(M:E)^2<=(100*A*B/(p1*p2))*(M:E)^2:=by
  calc
    (S.card:E)*(M:E)^2=(dom.card:E):=hcard_dom.symm
    _ = ((dom.image φ).card:E):=by exact_mod_cast (Finset.card_image_iff.mpr hφ_inj).symm
    _ <= ((box.image (fun p=>(p.1,p.2))).card:E):=by exact_mod_cast Finset.card_le_card himg_sub
    _ <= (box.card:E):=by exact_mod_cast card_image_le
    _ <= 100*(M:E)^2*A*B/(p1*p2):=hcard_box
    _ = (100*A*B/(p1*p2))*(M:E)^2:=by ring
 exact le_of_mul_le_mul_right hle (pow_pos hMR 2)
def det3 (u v w:ℤ × ℤ × ℤ):ℤ := u.1*(v.2.1*w.2.2-v.2.2*w.2.1) -
 u.2.1*(v.1*w.2.2-v.2.2*w.1) +
 u.2.2*(v.1*w.2.1-v.2.1*w.1)
lemma exists_unimodular_ext_3d (e1:ℤ × ℤ × ℤ)
  (hprim:Int.gcd (Int.gcd e1.1 e1.2.1:ℤ) e1.2.2=1) :
  ∃ u2 u3:ℤ × ℤ × ℤ,det3 e1 u2 u3=1\/det3 e1 u2 u3=-1:=by
 let g:ℤ:=(Int.gcd e1.1 e1.2.1:ℤ)
 by_cases hg0:g=0
 ·
  have hg_nat:Int.gcd e1.1 e1.2.1=0:=by dsimp [g] at hg0;exact_mod_cast hg0
  have ha0:e1.1=0:=(Int.gcd_eq_zero_iff.mp hg_nat).1;have hb0:e1.2.1=0:=(Int.gcd_eq_zero_iff.mp hg_nat).2;rw [hg_nat] at hprim;have hc_abs:e1.2.2.natAbs=1:=by simpa using hprim
  have hc:e1.2.2=1\/e1.2.2=-1:=Int.natAbs_eq_iff.mp hc_abs;refine ⟨(1,0,0),(0,1,0),?_⟩;dsimp [det3];rw [ha0,hb0];simp [hc]
 ·
  have hg_nat_pos:0 < Int.gcd e1.1 e1.2.1 :=Nat.pos_of_ne_zero (fun h=>hg0 (by dsimp [g];exact_mod_cast h));have hg_pos:0 < g:=by dsimp [g];exact_mod_cast hg_nat_pos
  let a':ℤ:=e1.1/g;let b':ℤ:=e1.2.1/g;have ha_eq:g*a'=e1.1:=Int.mul_ediv_cancel' (Int.gcd_dvd_left e1.1 e1.2.1);have hb_eq:g*b'=e1.2.1:=Int.mul_ediv_cancel' (Int.gcd_dvd_right e1.1 e1.2.1)
  have hcop_ab:IsCoprime a' b':=by
   have hbez:=Int.gcd_eq_gcd_ab e1.1 e1.2.1;refine ⟨Int.gcdA e1.1 e1.2.1,Int.gcdB e1.1 e1.2.1,?_⟩
   have hmul:g*(Int.gcdA e1.1 e1.2.1*a'+Int.gcdB e1.1 e1.2.1*b')=g*1:=by
    calc
     g*(Int.gcdA e1.1 e1.2.1*a'+Int.gcdB e1.1 e1.2.1*b')
       = (g*a')*Int.gcdA e1.1 e1.2.1+(g*b')*Int.gcdB e1.1 e1.2.1:=by ring
     _ = e1.1*Int.gcdA e1.1 e1.2.1+e1.2.1*Int.gcdB e1.1 e1.2.1:=by rw [ha_eq,hb_eq]
     _ = g:=hbez.symm
     _ = g*1:=(mul_one g).symm
   exact mul_left_cancel₀ (ne_of_gt hg_pos) hmul
  obtain ⟨y,x_neg,hxy⟩:=hcop_ab;let x:ℤ:=-x_neg;have hxy':a'*y-b'*x=1:=by dsimp [x];linarith
  have hcop_gc:IsCoprime g e1.2.2:=by
   have hbez:=Int.gcd_eq_gcd_ab g e1.2.2;have hgg:Int.gcd g e1.2.2=1:=hprim;rw [hgg] at hbez;refine ⟨Int.gcdA g e1.2.2,Int.gcdB g e1.2.2,?_⟩
   calc
    Int.gcdA g e1.2.2*g+Int.gcdB g e1.2.2*e1.2.2
      = g*Int.gcdA g e1.2.2+e1.2.2*Int.gcdB g e1.2.2:=by ring
    _ = 1:=by simpa using hbez.symm
  obtain ⟨s,r_neg,hrs⟩:=hcop_gc;let r:ℤ:=-r_neg;have hrs':g*s-e1.2.2*r=1:=by dsimp [r];linarith
  refine ⟨(x,y,0),(r*a',r*b',s),Or.inl ?_⟩;dsimp [det3];rw [← ha_eq,← hb_eq];have hident:g*a'*(y*s-0*(r*b'))-g*b'*(x*s-0*(r*a')) + e1.2.2*(x*(r*b')-y*(r*a'))=(g*s-e1.2.2*r)*(a'*y-b'*x):=by ring
  rw [hident,hrs',hxy',mul_one]
lemma exists_unimodular_basis_3d_rank2 (N:E × E × E->E)
  (hadd:∀ u v,N (u.1+v.1,u.2.1+v.2.1,u.2.2+v.2.2)<=N u+N v)
  (hsmul:∀ (t:E) (u:E × E × E),N (t*u.1,t*u.2.1,t*u.2.2) = |t| * N u)
  (w1 w2:ℤ × ℤ × ℤ)
  (hli:w1.2.1*w2.2.2-w1.2.2*w2.2.1≠0 ∨ w1.2.2*w2.1-w1.1*w2.2.2≠0 ∨ w1.1*w2.2.1-w1.2.1*w2.1≠0)
  (hw1:N (w1.1,w1.2.1,w1.2.2)<=1) (hw2:N (w2.1,w2.2.1,w2.2.2)<=1) :
  ∃ e1 e2 f3:ℤ × ℤ × ℤ,(det3 e1 e2 f3=1\/det3 e1 e2 f3=-1) ∧ (∃ g:ℤ,0 < g/\w1.1=g*e1.1/\w1.2.1=g*e1.2.1/\w1.2.2=g*e1.2.2) ∧ (∃ a b:ℤ,0 < b/\w2.1=a*e1.1+b*e2.1 ∧ w2.2.1=a*e1.2.1+b*e2.2.1/\w2.2.2=a*e1.2.2+b*e2.2.2) ∧ N (e1.1,e1.2.1,e1.2.2)<=1/\N (e2.1,e2.2.1,e2.2.2)<=3/2:=by
 have hw1_ne:w1.1≠0\/w1.2.1≠0\/w1.2.2≠0:=by
  by_contra h;push Not at h;rcases h with ⟨h1,h2,h3⟩
  rw [h1,h2,h3] at hli;simp at hli
 let g12:ℕ:=Int.gcd w1.1 w1.2.1;let g:ℕ:=Int.gcd (g12:ℤ) w1.2.2
 have hg_pos_nat:0 < g:=by
  dsimp [g,g12];rcases hw1_ne with h1 | h2 | h3
  ·
   have:(Int.gcd w1.1 w1.2.1:ℤ)≠0:=by exact_mod_cast (Int.gcd_pos_of_ne_zero_left w1.2.1 h1).ne'
   exact Int.gcd_pos_of_ne_zero_left w1.2.2 this
  ·
   have:(Int.gcd w1.1 w1.2.1:ℤ)≠0:=by exact_mod_cast (Int.gcd_pos_of_ne_zero_right w1.1 h2).ne'
   exact Int.gcd_pos_of_ne_zero_left w1.2.2 this
  · exact Int.gcd_pos_of_ne_zero_right _ h3
 let gZ:ℤ:=(g:ℤ);have hgZ_pos:0 < gZ:=by dsimp [gZ];exact_mod_cast hg_pos_nat
 have hgd12:gZ∣(g12:ℤ):=Int.gcd_dvd_left (g12:ℤ) w1.2.2;have hgd1:gZ∣w1.1:=dvd_trans hgd12 (Int.gcd_dvd_left w1.1 w1.2.1);have hgd2:gZ∣w1.2.1:=dvd_trans hgd12 (Int.gcd_dvd_right w1.1 w1.2.1);have hgd3:gZ∣w1.2.2:=Int.gcd_dvd_right (g12:ℤ) w1.2.2
 let e1:ℤ × ℤ × ℤ:=(w1.1/gZ,w1.2.1/gZ,w1.2.2/gZ);have he1_1:gZ*e1.1=w1.1:=Int.mul_ediv_cancel' hgd1;have he1_2:gZ*e1.2.1=w1.2.1:=Int.mul_ediv_cancel' hgd2;have he1_3:gZ*e1.2.2=w1.2.2:=Int.mul_ediv_cancel' hgd3
 have hprim:Int.gcd (Int.gcd e1.1 e1.2.1:ℤ) e1.2.2=1:=by
  have hmul1:Int.gcd w1.1 w1.2.1=g*Int.gcd e1.1 e1.2.1:=by
   rw [← he1_1,← he1_2];dsimp [gZ];simpa using Int.gcd_mul_left (g:ℤ) e1.1 e1.2.1
  have hmul2:g=g*Int.gcd (Int.gcd e1.1 e1.2.1:ℤ) e1.2.2:=by
   calc
    g=Int.gcd (Int.gcd w1.1 w1.2.1:ℤ) w1.2.2:=rfl
    _ = Int.gcd ((g:ℤ)*(Int.gcd e1.1 e1.2.1:ℤ)) ((g:ℤ)*e1.2.2):=by rw [hmul1,← he1_3];push_cast;rfl
    _ = g*Int.gcd (Int.gcd e1.1 e1.2.1:ℤ) e1.2.2:=by simpa using Int.gcd_mul_left (g:ℤ) (Int.gcd e1.1 e1.2.1:ℤ) e1.2.2
  exact Nat.eq_of_mul_eq_mul_left hg_pos_nat (by omega)
 obtain ⟨u2,u3,hu_det⟩:=exists_unimodular_ext_3d e1 hprim;let D:ℤ:=det3 e1 u2 u3;have hD_sq:D*D=1:=by rcases hu_det with h | h <;> simp [D,h]
 let c1:ℤ:=D*det3 w2 u2 u3;let c2:ℤ:=D*det3 e1 w2 u3;let c3:ℤ:=D*det3 e1 u2 w2
 have hc_1:w2.1=c1*e1.1+c2*u2.1+c3*u3.1:=by
  have hcr:(det3 e1 u2 u3)*w2.1 = (det3 w2 u2 u3)*e1.1+(det3 e1 w2 u3)*u2.1+(det3 e1 u2 w2)*u3.1:=by dsimp [det3];ring
  dsimp [c1,c2,c3,D] at hD_sq ⊢
  linear_combination -w2.1*hD_sq+det3 e1 u2 u3*hcr
 have hc_2:w2.2.1=c1*e1.2.1+c2*u2.2.1+c3*u3.2.1:=by
  have hcr:(det3 e1 u2 u3)*w2.2.1 = (det3 w2 u2 u3)*e1.2.1+(det3 e1 w2 u3)*u2.2.1+(det3 e1 u2 w2)*u3.2.1:=by dsimp [det3];ring
  dsimp [c1,c2,c3,D] at hD_sq ⊢
  linear_combination -w2.2.1*hD_sq+det3 e1 u2 u3*hcr
 have hc_3:w2.2.2=c1*e1.2.2+c2*u2.2.2+c3*u3.2.2:=by
  have hcr:(det3 e1 u2 u3)*w2.2.2 = (det3 w2 u2 u3)*e1.2.2+(det3 e1 w2 u3)*u2.2.2+(det3 e1 u2 w2)*u3.2.2:=by dsimp [det3];ring
  dsimp [c1,c2,c3,D] at hD_sq ⊢
  linear_combination -w2.2.2*hD_sq+det3 e1 u2 u3*hcr
 have hc23_ne:c2≠0\/c3≠0:=by
  by_contra h;push Not at h
  rw [h.1,h.2] at hc_1 hc_2 hc_3;simp only [zero_mul,add_zero] at hc_1 hc_2 hc_3;rw [← he1_1,← he1_2,← he1_3,hc_1,hc_2,hc_3] at hli;rcases hli with h1 | h2 | h3 <;> apply ‹_› <;> ring
 let b:ℤ:=(Int.gcd c2 c3:ℤ)
 have hb_pos:0 < b:=by
  have hnat:0 < Int.gcd c2 c3:=by
   rcases hc23_ne with h2 | h3
   · exact Int.gcd_pos_of_ne_zero_left c3 h2
   · exact Int.gcd_pos_of_ne_zero_right c2 h3
  dsimp [b];exact_mod_cast hnat
 let p2:ℤ:=c2/b;let p3:ℤ:=c3/b;have hp2_mul:b*p2=c2:=Int.mul_ediv_cancel' (Int.gcd_dvd_left c2 c3);have hp3_mul:b*p3=c3:=Int.mul_ediv_cancel' (Int.gcd_dvd_right c2 c3)
 have hcop_p:IsCoprime p2 p3:=by
  have hbez:=Int.gcd_eq_gcd_ab c2 c3;refine ⟨Int.gcdA c2 c3,Int.gcdB c2 c3,?_⟩
  have hmul:b*(Int.gcdA c2 c3*p2+Int.gcdB c2 c3*p3)=b*1:=by
   calc
    b*(Int.gcdA c2 c3*p2+Int.gcdB c2 c3*p3)
        = (b*p2)*Int.gcdA c2 c3+(b*p3)*Int.gcdB c2 c3:=by ring
    _ = c2*Int.gcdA c2 c3+c3*Int.gcdB c2 c3:=by rw [hp2_mul,hp3_mul]
    _ = b:=hbez.symm
    _ = b*1:=(mul_one b).symm
  exact mul_left_cancel₀ (ne_of_gt hb_pos) hmul
 obtain ⟨q3,q2_neg,hqp⟩:=hcop_p;let q2:ℤ:=-q2_neg;have hdet2:p2*q3-p3*q2=1:=by dsimp [q2];linarith
 let f2:ℤ × ℤ × ℤ:=(p2*u2.1+p3*u3.1,p2*u2.2.1+p3*u3.2.1,p2*u2.2.2+p3*u3.2.2);let f3:ℤ × ℤ × ℤ:=(q2*u2.1+q3*u3.1,q2*u2.2.1+q3*u3.2.1,q2*u2.2.2+q3*u3.2.2);have hw2_f2_1:w2.1=c1*e1.1+b*f2.1:=by dsimp [f2];rw [hc_1,← hp2_mul,← hp3_mul];ring
 have hw2_f2_2:w2.2.1=c1*e1.2.1+b*f2.2.1:=by dsimp [f2];rw [hc_2,← hp2_mul,← hp3_mul];ring
 have hw2_f2_3:w2.2.2=c1*e1.2.2+b*f2.2.2:=by dsimp [f2];rw [hc_3,← hp2_mul,← hp3_mul];ring
 obtain ⟨q,hq⟩:=exists_round_int_div c1 b hb_pos;let e2:ℤ × ℤ × ℤ:=(f2.1+q*e1.1,f2.2.1+q*e1.2.1,f2.2.2+q*e1.2.2)
 have hdet_e:det3 e1 e2 f3=D:=by
  have hmul:det3 e1 e2 f3=(det3 e1 u2 u3)*(p2*q3-p3*q2):=by dsimp [det3,e2,f2,f3];ring
  rw [hmul,hdet2,mul_one]
 have hN_nn:∀ u:E × E × E,0<=N u:=by
  intro u;have h0:=hsmul 0 u;have hneg:=hadd u (-u.1,-u.2.1,-u.2.2);have hneg2:=hsmul (-1) u;simp only [zero_mul,abs_zero,neg_one_mul,abs_neg,abs_one,one_mul] at h0 hneg2;have hzero:(u.1+-u.1,u.2.1+-u.2.1,u.2.2+-u.2.2)=(0,0,0):=by simp
  rw [hzero,hneg2] at hneg;linarith
 have hNe1:N (e1.1,e1.2.1,e1.2.2)<=1:=by
  have hgR:(0:E) < (gZ:E):=by exact_mod_cast hgZ_pos
  have hg1:(1:E)<=(gZ:E):=by exact_mod_cast hgZ_pos
  have h1:N (w1.1,w1.2.1,w1.2.2)=(gZ:E)*N (e1.1,e1.2.1,e1.2.2):=by
   have hm1:(w1.1:E)=(gZ:E)*(e1.1:E):=by exact_mod_cast he1_1.symm
   have hm2:(w1.2.1:E)=(gZ:E)*(e1.2.1:E):=by exact_mod_cast he1_2.symm
   have hm3:(w1.2.2:E)=(gZ:E)*(e1.2.2:E):=by exact_mod_cast he1_3.symm
   rw [hm1,hm2,hm3,hsmul (gZ:E) (e1.1,e1.2.1,e1.2.2),abs_of_pos hgR]
  nlinarith [hN_nn (e1.1,e1.2.1,e1.2.2)]
 have hNe2:N (e2.1,e2.2.1,e2.2.2)<=3/2:=by
  have hbR:(0:E) < (b:E):=by exact_mod_cast hb_pos
  have hb1:(1:E)<=(b:E):=by exact_mod_cast hb_pos
  let t1:E:=((q:E)*(b:E)-(c1:E))/(b:E);let t2:E:=1/(b:E)
  have he2_eq:((e2.1:E),(e2.2.1:E),(e2.2.2:E)) = (t1*(e1.1:E)+t2*(w2.1:E),t1*(e1.2.1:E)+t2*(w2.2.1:E),t1*(e1.2.2:E)+t2*(w2.2.2:E)):=by
   have h1:(w2.1:E)=(c1:E)*(e1.1:E)+(b:E)*(f2.1:E):=by exact_mod_cast hw2_f2_1
   have h2:(w2.2.1:E)=(c1:E)*(e1.2.1:E)+(b:E)*(f2.2.1:E):=by exact_mod_cast hw2_f2_2
   have h3:(w2.2.2:E)=(c1:E)*(e1.2.2:E)+(b:E)*(f2.2.2:E):=by exact_mod_cast hw2_f2_3
   refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    dsimp [e2,t1,t2] <;> push_cast <;> field_simp [hbR.ne'] <;> linarith
  rw [he2_eq]
  have htri:=hadd (t1*(e1.1:E),t1*(e1.2.1:E),t1*(e1.2.2:E))
         (t2*(w2.1:E),t2*(w2.2.1:E),t2*(w2.2.2:E))
  have hs1:=hsmul t1 (e1.1,e1.2.1,e1.2.2);have hs2:=hsmul t2 (w2.1,w2.2.1,w2.2.2);have ht1:|t1| ≤ 1/2:=by dsimp [t1];rw [abs_div,abs_of_pos hbR,div_le_iff₀ hbR];linarith
  have ht2:|t2| ≤ 1:=by dsimp [t2];rw [abs_of_pos (by positivity),div_le_one hbR];exact hb1
  nlinarith [hN_nn (e1.1,e1.2.1,e1.2.2),hN_nn (w2.1,w2.2.1,w2.2.2)]
 refine ⟨e1,e2,f3,?_,⟨gZ,hgZ_pos,he1_1.symm,he1_2.symm,he1_3.symm⟩,⟨c1-b*q,b,hb_pos,?_,?_,?_⟩,hNe1,hNe2⟩
 · rw [hdet_e];exact hu_det
 · dsimp [e2];rw [hw2_f2_1];ring
 · dsimp [e2];rw [hw2_f2_2];ring
 · dsimp [e2];rw [hw2_f2_3];ring
lemma exists_unimodular_basis_3d (N:E × E × E->E)
  (hadd:∀ u v,N (u.1+v.1,u.2.1+v.2.1,u.2.2+v.2.2)<=N u+N v)
  (hsmul:∀ (t:E) (u:E × E × E),N (t*u.1,t*u.2.1,t*u.2.2) = |t| * N u)
  (w1 w2 w3:ℤ × ℤ × ℤ) (hdet:det3 w1 w2 w3≠0)
  (hw1:N (w1.1,w1.2.1,w1.2.2)<=1)
  (hw2:N (w2.1,w2.2.1,w2.2.2)<=1)
  (hw3:N (w3.1,w3.2.1,w3.2.2)<=1) :
  ∃ e1 e2 e3:ℤ × ℤ × ℤ,(det3 e1 e2 e3=1\/det3 e1 e2 e3=-1) ∧ N (e1.1,e1.2.1,e1.2.2)<=1 ∧ N (e2.1,e2.2.1,e2.2.2)<=3/2 ∧ N (e3.1,e3.2.1,e3.2.2)<=9/4:=by
 have hli:w1.2.1*w2.2.2-w1.2.2*w2.2.1≠0 ∨ w1.2.2*w2.1-w1.1*w2.2.2≠0 ∨ w1.1*w2.2.1-w1.2.1*w2.1≠0:=by
  by_contra h;push Not at h;rcases h with ⟨h1,h2,h3⟩
  apply hdet
  have:det3 w1 w2 w3=w3.1*(w1.2.1*w2.2.2-w1.2.2*w2.2.1) + w3.2.1*(w1.2.2*w2.1-w1.1*w2.2.2) + w3.2.2*(w1.1*w2.2.1-w1.2.1*w2.1):=by dsimp [det3];ring
  rw [this,h1,h2,h3];ring
 obtain ⟨e1,e2,f3,hdet_f,hw1_rep,hw2_rep,hNe1,hNe2⟩ :=exists_unimodular_basis_3d_rank2 N hadd hsmul w1 w2 hli hw1 hw2;let D:ℤ:=det3 e1 e2 f3;have hD_sq:D*D=1:=by rcases hdet_f with h | h <;> simp [D,h]
 let d1:ℤ:=D*det3 w3 e2 f3;let d2:ℤ:=D*det3 e1 w3 f3;let d3:ℤ:=D*det3 e1 e2 w3
 have hw3_1:w3.1=d1*e1.1+d2*e2.1+d3*f3.1:=by
  have hcr:(det3 e1 e2 f3)*w3.1 = (det3 w3 e2 f3)*e1.1+(det3 e1 w3 f3)*e2.1+(det3 e1 e2 w3)*f3.1:=by dsimp [det3];ring
  dsimp [d1,d2,d3,D] at hD_sq ⊢
  linear_combination -w3.1*hD_sq+det3 e1 e2 f3*hcr
 have hw3_2:w3.2.1=d1*e1.2.1+d2*e2.2.1+d3*f3.2.1:=by
  have hcr:(det3 e1 e2 f3)*w3.2.1 = (det3 w3 e2 f3)*e1.2.1+(det3 e1 w3 f3)*e2.2.1+(det3 e1 e2 w3)*f3.2.1:=by dsimp [det3];ring
  dsimp [d1,d2,d3,D] at hD_sq ⊢
  linear_combination -w3.2.1*hD_sq+det3 e1 e2 f3*hcr
 have hw3_3:w3.2.2=d1*e1.2.2+d2*e2.2.2+d3*f3.2.2:=by
  have hcr:(det3 e1 e2 f3)*w3.2.2 = (det3 w3 e2 f3)*e1.2.2+(det3 e1 w3 f3)*e2.2.2+(det3 e1 e2 w3)*f3.2.2:=by dsimp [det3];ring
  dsimp [d1,d2,d3,D] at hD_sq ⊢
  linear_combination -w3.2.2*hD_sq+det3 e1 e2 f3*hcr
 have hd3_ne:d3≠0:=by
  intro hd0;apply hdet;obtain ⟨g,_,h11,h12,h13⟩:=hw1_rep;obtain ⟨a,b,_,h21,h22,h23⟩:=hw2_rep
  have hd_e:det3 e1 e2 w3=0:=by
    have:D*d3=det3 e1 e2 w3:=by dsimp [d3];linear_combination det3 e1 e2 w3*hD_sq
    rw [hd0,mul_zero] at this;exact this.symm
  have hrel:det3 w1 w2 w3=g*b*det3 e1 e2 w3:=by dsimp [det3];rw [h11,h12,h13,h21,h22,h23];ring
  rw [hrel,hd_e,mul_zero]
 let sgn:ℤ:=if 0 < d3 then 1 else -1;have hsgn_sq:sgn*sgn=1:=by dsimp [sgn];split_ifs <;> norm_num
 let f3':ℤ × ℤ × ℤ:=(sgn*f3.1,sgn*f3.2.1,sgn*f3.2.2);let c:ℤ:=sgn*d3;have hc_pos:0 < c:=by dsimp [c,sgn];split_ifs with h <;> omega
 have hw3_1':w3.1=d1*e1.1+d2*e2.1+c*f3'.1:=by dsimp [c,f3'];rw [hw3_1];linear_combination -d3*f3.1*hsgn_sq
 have hw3_2':w3.2.1=d1*e1.2.1+d2*e2.2.1+c*f3'.2.1:=by dsimp [c,f3'];rw [hw3_2];linear_combination -d3*f3.2.1*hsgn_sq
 have hw3_3':w3.2.2=d1*e1.2.2+d2*e2.2.2+c*f3'.2.2:=by dsimp [c,f3'];rw [hw3_3];linear_combination -d3*f3.2.2*hsgn_sq
 obtain ⟨k1,hk1⟩:=exists_round_int_div d1 c hc_pos;obtain ⟨k2,hk2⟩:=exists_round_int_div d2 c hc_pos;let e3:ℤ × ℤ × ℤ := (f3'.1+k1*e1.1+k2*e2.1,f3'.2.1+k1*e1.2.1+k2*e2.2.1,f3'.2.2+k1*e1.2.2+k2*e2.2.2)
 have hdet_e3:det3 e1 e2 e3=sgn*D:=by dsimp [det3,e3,f3',D];ring
 have hN_nn:∀ u:E × E × E,0<=N u:=by
  intro u;have h0:=hsmul 0 u;have hneg:=hadd u (-u.1,-u.2.1,-u.2.2);have hneg2:=hsmul (-1) u;simp only [zero_mul,abs_zero,neg_one_mul,abs_neg,abs_one,one_mul] at h0 hneg2;have hzero:(u.1+-u.1,u.2.1+-u.2.1,u.2.2+-u.2.2)=(0,0,0):=by simp
  rw [hzero,hneg2] at hneg;linarith
 have hNe3:N (e3.1,e3.2.1,e3.2.2)<=9/4:=by
  have hcR:(0:E) < (c:E):=by exact_mod_cast hc_pos
  have hc1:(1:E)<=(c:E):=by exact_mod_cast hc_pos
  let t1:E:=((k1:E)*(c:E)-(d1:E))/(c:E);let t2:E:=((k2:E)*(c:E)-(d2:E))/(c:E);let t3:E:=1/(c:E)
  have he3_eq:((e3.1:E),(e3.2.1:E),(e3.2.2:E)) = ((t1*(e1.1:E)+t2*(e2.1:E))+t3*(w3.1:E),(t1*(e1.2.1:E)+t2*(e2.2.1:E))+t3*(w3.2.1:E),(t1*(e1.2.2:E)+t2*(e2.2.2:E))+t3*(w3.2.2:E)):=by
    have h1:(w3.1:E)=(d1:E)*(e1.1:E)+(d2:E)*(e2.1:E)+(c:E)*(f3'.1:E):=by exact_mod_cast hw3_1'
    have h2:(w3.2.1:E)=(d1:E)*(e1.2.1:E)+(d2:E)*(e2.2.1:E)+(c:E)*(f3'.2.1:E):=by exact_mod_cast hw3_2'
    have h3:(w3.2.2:E)=(d1:E)*(e1.2.2:E)+(d2:E)*(e2.2.2:E)+(c:E)*(f3'.2.2:E):=by exact_mod_cast hw3_3'
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
     dsimp [e3,t1,t2,t3] <;> push_cast <;> field_simp [hcR.ne'] <;> linarith
  rw [he3_eq]
  have htri1:=hadd (t1*(e1.1:E)+t2*(e2.1:E),t1*(e1.2.1:E)+t2*(e2.2.1:E),t1*(e1.2.2:E)+t2*(e2.2.2:E))
         (t3*(w3.1:E),t3*(w3.2.1:E),t3*(w3.2.2:E))
  have htri2:=hadd (t1*(e1.1:E),t1*(e1.2.1:E),t1*(e1.2.2:E))
         (t2*(e2.1:E),t2*(e2.2.1:E),t2*(e2.2.2:E))
  have hs1:=hsmul t1 (e1.1,e1.2.1,e1.2.2);have hs2:=hsmul t2 (e2.1,e2.2.1,e2.2.2);have hs3:=hsmul t3 (w3.1,w3.2.1,w3.2.2);have ht1:|t1| ≤ 1/2:=by dsimp [t1];rw [abs_div,abs_of_pos hcR,div_le_iff₀ hcR];linarith
  have ht2:|t2| ≤ 1/2:=by dsimp [t2];rw [abs_div,abs_of_pos hcR,div_le_iff₀ hcR];linarith
  have ht3:|t3| ≤ 1:=by dsimp [t3];rw [abs_of_pos (by positivity),div_le_one hcR];exact hc1
  nlinarith [hN_nn (e1.1,e1.2.1,e1.2.2),hN_nn (e2.1,e2.2.1,e2.2.2),hN_nn (w3.1,w3.2.1,w3.2.2)]
 refine ⟨e1,e2,e3,?_,hNe1,hNe2,hNe3⟩;rw [hdet_e3];rcases hdet_f with hD | hD <;> dsimp [sgn,D] at hD ⊢ <;> rw [hD] <;> split_ifs <;> simp
private lemma sheared_norm3_props {p1 p2 p3 A B:E} (hA:0 < A) (hB:0 < B) :
  let N:E × E × E->E:=fun u =>
   max (|p3*u.2.2| / A) (max (|p2*u.2.1-p3*u.2.2| / B) (|p1*u.1-p3*u.2.2| / B))
  (∀ u v,N (u.1+v.1,u.2.1+v.2.1,u.2.2+v.2.2)<=N u+N v) ∧
  (∀ (t:E) (u:E × E × E),N (t*u.1,t*u.2.1,t*u.2.2) = |t| * N u):=by
 refine ⟨?_,?_⟩
 ·
  intro u v;refine max_le ?_ (max_le ?_ ?_)
  ·
   have h1:|p3*(u.2.2+v.2.2)| ≤ |p3*u.2.2| + |p3*v.2.2|:=by rw [mul_add];exact abs_add_le _ _
   have h2:=div_le_div_of_nonneg_right h1 hA.le;rw [add_div] at h2;have hu:=le_max_left (|p3*u.2.2| / A) (max (|p2*u.2.1-p3*u.2.2| / B) (|p1*u.1-p3*u.2.2| / B));have hv:=le_max_left (|p3*v.2.2| / A) (max (|p2*v.2.1-p3*v.2.2| / B) (|p1*v.1-p3*v.2.2| / B))
   linarith
  ·
   have h1:|p2*(u.2.1+v.2.1)-p3*(u.2.2+v.2.2)| ≤
     |p2*u.2.1-p3*u.2.2| + |p2*v.2.1-p3*v.2.2|:=by
    have:p2*(u.2.1+v.2.1)-p3*(u.2.2+v.2.2) = (p2*u.2.1-p3*u.2.2)+(p2*v.2.1-p3*v.2.2):=by ring
    rw [this];exact abs_add_le _ _
   have h2:=div_le_div_of_nonneg_right h1 hB.le;rw [add_div] at h2
   have hu:=le_trans (le_max_left (|p2*u.2.1-p3*u.2.2| / B) (|p1*u.1-p3*u.2.2| / B))
    (le_max_right (|p3*u.2.2| / A) _)
   have hv:=le_trans (le_max_left (|p2*v.2.1-p3*v.2.2| / B) (|p1*v.1-p3*v.2.2| / B))
    (le_max_right (|p3*v.2.2| / A) _)
   linarith
  ·
   have h1:|p1*(u.1+v.1)-p3*(u.2.2+v.2.2)| ≤
     |p1*u.1-p3*u.2.2| + |p1*v.1-p3*v.2.2|:=by
    have:p1*(u.1+v.1)-p3*(u.2.2+v.2.2) = (p1*u.1-p3*u.2.2)+(p1*v.1-p3*v.2.2):=by ring
    rw [this];exact abs_add_le _ _
   have h2:=div_le_div_of_nonneg_right h1 hB.le;rw [add_div] at h2
   have hu:=le_trans (le_max_right (|p2*u.2.1-p3*u.2.2| / B) (|p1*u.1-p3*u.2.2| / B))
    (le_max_right (|p3*u.2.2| / A) _)
   have hv:=le_trans (le_max_right (|p2*v.2.1-p3*v.2.2| / B) (|p1*v.1-p3*v.2.2| / B))
    (le_max_right (|p3*v.2.2| / A) _)
   linarith
 ·
  intro t u;have h1:|p3*(t*u.2.2)| / A = |t| * (|p3*u.2.2| / A):=by rw [show p3*(t*u.2.2)=t*(p3*u.2.2) by ring,abs_mul,mul_div_assoc]
  have h2:|p2*(t*u.2.1)-p3*(t*u.2.2)| / B = |t| * (|p2*u.2.1-p3*u.2.2| / B):=by
   rw [show p2*(t*u.2.1)-p3*(t*u.2.2)=t*(p2*u.2.1-p3*u.2.2) by ring,abs_mul,mul_div_assoc]
  have h3:|p1*(t*u.1)-p3*(t*u.2.2)| / B = |t| * (|p1*u.1-p3*u.2.2| / B):=by
   rw [show p1*(t*u.1)-p3*(t*u.2.2)=t*(p1*u.1-p3*u.2.2) by ring,abs_mul,mul_div_assoc]
  dsimp only;rw [h1,h2,h3,mul_max_of_nonneg _ _ (abs_nonneg t),mul_max_of_nonneg _ _ (abs_nonneg t)]
theorem card_rank3_box_le {p1 p2 p3 A B:E}
  (hp1:0 < p1) (hp2:0 < p2) (hp3:0 < p3) (hA:0 < A) (hB:0 < B)
  (S:Finset (ℤ × ℤ × ℤ))
  (hS:∀ v∈S,|p3*(v.2.2:E)| ≤ A ∧
         |p2*(v.2.1:E)-p3*(v.2.2:E)| ≤ B ∧
         |p1*(v.1:E)-p3*(v.2.2:E)| ≤ B)
  (hrank:∃ w1∈S,∃ w2∈S,∃ w3∈S,det3 w1 w2 w3≠0) :
  (S.card:E)<=3000*A*B^2/(p1*p2*p3):=by
 let N:E × E × E->E:=fun u =>
  max (|p3*u.2.2| / A) (max (|p2*u.2.1-p3*u.2.2| / B) (|p1*u.1-p3*u.2.2| / B))
 obtain ⟨hadd,hsmul⟩:=sheared_norm3_props (p1:=p1) (p2:=p2) (p3:=p3) hA hB
 have hNS:∀ v∈S,N (v.1,v.2.1,v.2.2)<=1:=by
  intro v hv;dsimp [N]
  exact max_le ((div_le_one hA).mpr (hS v hv).1)
    (max_le ((div_le_one hB).mpr (hS v hv).2.1) ((div_le_one hB).mpr (hS v hv).2.2))
 obtain ⟨w1,hw1,w2,hw2,w3,hw3,hdet⟩:=hrank;obtain ⟨e1,e2,e3,hedet,hNe1,hNe2,hNe3⟩ :=exists_unimodular_basis_3d N hadd hsmul w1 w2 w3 hdet (hNS w1 hw1) (hNS w2 hw2) (hNS w3 hw3);let M:ℕ:=⌈max (2*p3/A) (max (2*p2/B) (2*p1/B))⌉₊+10
 have hM_pos:0 < M:=by dsimp [M];omega
 have hMR:(0:E) < (M:E):=by exact_mod_cast hM_pos
 have hM3:2*p3/A<=(M:E):=by
  have h1:=le_max_left (2*p3/A) (max (2*p2/B) (2*p1/B));have h2:=Nat.le_ceil (max (2*p3/A) (max (2*p2/B) (2*p1/B)));dsimp [M];push_cast;linarith
 have hM2:2*p2/B<=(M:E):=by
  have h1:=le_trans (le_max_left (2*p2/B) (2*p1/B)) (le_max_right (2*p3/A) _);have h2:=Nat.le_ceil (max (2*p3/A) (max (2*p2/B) (2*p1/B)));dsimp [M];push_cast;linarith
 have hM1:2*p1/B<=(M:E):=by
  have h1:=le_trans (le_max_right (2*p2/B) (2*p1/B)) (le_max_right (2*p3/A) _);have h2:=Nat.le_ceil (max (2*p3/A) (max (2*p2/B) (2*p1/B)));dsimp [M];push_cast;linarith
 let dom:=S×ˢ(Finset.range M×ˢ(Finset.range M×ˢFinset.range M))
 let φ:(ℤ × ℤ × ℤ) × (ℕ × ℕ × ℕ)->ℤ × ℤ × ℤ:=fun t =>
  ((M:ℤ)*t.1.1+(t.2.1:ℤ)*e1.1+(t.2.2.1:ℤ)*e2.1+(t.2.2.2:ℤ)*e3.1,(M:ℤ)*t.1.2.1+(t.2.1:ℤ)*e1.2.1+(t.2.2.1:ℤ)*e2.2.1+(t.2.2.2:ℤ)*e3.2.1,(M:ℤ)*t.1.2.2+(t.2.1:ℤ)*e1.2.2+(t.2.2.1:ℤ)*e2.2.2+(t.2.2.2:ℤ)*e3.2.2)
 have hφ_inj:Set.InjOn φ (dom:Set _):=by
  rintro ⟨v,i,j,k⟩ h1 ⟨v',i',j',k'⟩ h2 heq;simp only [dom,Finset.mem_coe,mem_product,Finset.mem_range] at h1 h2;have he1:=congrArg Prod.fst heq;have he2:=congrArg (fun x=>x.2.1) heq;have he3:=congrArg (fun x=>x.2.2) heq;dsimp [φ] at he1 he2 he3
  let dv:ℤ × ℤ × ℤ:=(v'.1-v.1,v'.2.1-v.2.1,v'.2.2-v.2.2)
  have hdi:(M:ℤ)∣((i:ℤ)-(i':ℤ)):=by
    have hlin:det3 e1 e2 e3*((i:ℤ)-(i':ℤ))=(M:ℤ)*det3 dv e2 e3:=by
     dsimp [det3,dv]
     linear_combination (e2.2.1*e3.2.2-e2.2.2*e3.2.1)*he1 -
      (e2.1*e3.2.2-e2.2.2*e3.1)*he2+(e2.1*e3.2.1-e2.2.1*e3.1)*he3
    rcases hedet with hd | hd
    · rw [hd,one_mul] at hlin;exact ⟨_,hlin⟩
    · rw [hd,neg_one_mul] at hlin;exact ⟨-det3 dv e2 e3,by linarith⟩
  have hdj:(M:ℤ)∣((j:ℤ)-(j':ℤ)):=by
    have hlin:det3 e1 e2 e3*((j:ℤ)-(j':ℤ))=(M:ℤ)*det3 e1 dv e3:=by
     dsimp [det3,dv]
     linear_combination -(e1.2.1*e3.2.2-e1.2.2*e3.2.1)*he1 + (e1.1*e3.2.2-e1.2.2*e3.1)*he2-(e1.1*e3.2.1-e1.2.1*e3.1)*he3
    rcases hedet with hd | hd
    · rw [hd,one_mul] at hlin;exact ⟨_,hlin⟩
    · rw [hd,neg_one_mul] at hlin;exact ⟨-det3 e1 dv e3,by linarith⟩
  have hdk:(M:ℤ)∣((k:ℤ)-(k':ℤ)):=by
    have hlin:det3 e1 e2 e3*((k:ℤ)-(k':ℤ))=(M:ℤ)*det3 e1 e2 dv:=by
     dsimp [det3,dv]
     linear_combination (e1.2.1*e2.2.2-e1.2.2*e2.2.1)*he1 -
      (e1.1*e2.2.2-e1.2.2*e2.1)*he2+(e1.1*e2.2.1-e1.2.1*e2.1)*he3
    rcases hedet with hd | hd
    · rw [hd,one_mul] at hlin;exact ⟨_,hlin⟩
    · rw [hd,neg_one_mul] at hlin;exact ⟨-det3 e1 e2 dv,by linarith⟩
  have hi_eq:i=i':=eq_of_nat_lt_of_dvd_sub h1.2.1 h2.2.1 hdi;have hj_eq:j=j':=eq_of_nat_lt_of_dvd_sub h1.2.2.1 h2.2.2.1 hdj;have hk_eq:k=k':=eq_of_nat_lt_of_dvd_sub h1.2.2.2 h2.2.2.2 hdk;subst hi_eq;subst hj_eq;subst hk_eq
  have hv1:v.1=v'.1:=mul_left_cancel₀ (by exact_mod_cast hM_pos.ne') (by linarith:(M:ℤ)*v.1=(M:ℤ)*v'.1);have hv2:v.2.1=v'.2.1:=mul_left_cancel₀ (by exact_mod_cast hM_pos.ne') (by linarith:(M:ℤ)*v.2.1=(M:ℤ)*v'.2.1)
  have hv3:v.2.2=v'.2.2:=mul_left_cancel₀ (by exact_mod_cast hM_pos.ne') (by linarith:(M:ℤ)*v.2.2=(M:ℤ)*v'.2.2);exact Prod.ext (Prod.ext hv1 (Prod.ext hv2 hv3)) rfl
 have hφ_bd:∀ t∈dom,
    |p3*((φ t).2.2:E)| ≤ 6*(M:E)*A ∧
    |p2*((φ t).2.1:E)-p3*((φ t).2.2:E)| ≤ 6*(M:E)*B ∧
    |p1*((φ t).1:E)-p3*((φ t).2.2:E)| ≤ 6*(M:E)*B:=by
  rintro ⟨v,i,j,k⟩ ht;simp only [dom,mem_product,Finset.mem_range] at ht;have hiM:(i:E)<=(M:E):=by exact_mod_cast ht.2.1.le
  have hjM:(j:E)<=(M:E):=by exact_mod_cast ht.2.2.1.le
  have hkM:(k:E)<=(M:E):=by exact_mod_cast ht.2.2.2.le
  have hNφ:N ((φ (v,i,j,k)).1,(φ (v,i,j,k)).2.1,(φ (v,i,j,k)).2.2)<=6*(M:E):=by
    have heq:(((φ (v,i,j,k)).1:E),((φ (v,i,j,k)).2.1:E),((φ (v,i,j,k)).2.2:E)) = ((((M:E)*(v.1:E)+(i:E)*(e1.1:E))+(j:E)*(e2.1:E))+(k:E)*(e3.1:E),(((M:E)*(v.2.1:E)+(i:E)*(e1.2.1:E))+(j:E)*(e2.2.1:E))+(k:E)*(e3.2.1:E),(((M:E)*(v.2.2:E)+(i:E)*(e1.2.2:E))+(j:E)*(e2.2.2:E))+(k:E)*(e3.2.2:E)):=by
     refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp [φ] <;> push_cast <;> ring
    rw [heq]
    have h1:=hadd (((M:E)*(v.1:E)+(i:E)*(e1.1:E))+(j:E)*(e2.1:E),((M:E)*(v.2.1:E)+(i:E)*(e1.2.1:E))+(j:E)*(e2.2.1:E),((M:E)*(v.2.2:E)+(i:E)*(e1.2.2:E))+(j:E)*(e2.2.2:E))
          ((k:E)*(e3.1:E),(k:E)*(e3.2.1:E),(k:E)*(e3.2.2:E))
    have h2:=hadd ((M:E)*(v.1:E)+(i:E)*(e1.1:E),(M:E)*(v.2.1:E)+(i:E)*(e1.2.1:E),(M:E)*(v.2.2:E)+(i:E)*(e1.2.2:E))
          ((j:E)*(e2.1:E),(j:E)*(e2.2.1:E),(j:E)*(e2.2.2:E))
    have h3:=hadd ((M:E)*(v.1:E),(M:E)*(v.2.1:E),(M:E)*(v.2.2:E))
          ((i:E)*(e1.1:E),(i:E)*(e1.2.1:E),(i:E)*(e1.2.2:E))
    have hsM:=hsmul (M:E) (v.1,v.2.1,v.2.2);have hsi:=hsmul (i:E) (e1.1,e1.2.1,e1.2.2);have hsj:=hsmul (j:E) (e2.1,e2.2.1,e2.2.2);have hsk:=hsmul (k:E) (e3.1,e3.2.1,e3.2.2);rw [abs_of_nonneg hMR.le] at hsM;rw [abs_of_nonneg (Nat.cast_nonneg i)] at hsi
    rw [abs_of_nonneg (Nat.cast_nonneg j)] at hsj;rw [abs_of_nonneg (Nat.cast_nonneg k)] at hsk;have hnn:∀ u,0<=N u:=fun u=>le_trans (div_nonneg (abs_nonneg _) hA.le) (le_max_left _ _);have hvN:=hNS v ht.1
    nlinarith [hnn (e1.1,e1.2.1,e1.2.2),hnn (e2.1,e2.2.1,e2.2.2),hnn (e3.1,e3.2.1,e3.2.2)]
  exact ⟨(div_le_iff₀ hA).mp ((le_max_left _ _).trans hNφ),(div_le_iff₀ hB).mp ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hNφ),(div_le_iff₀ hB).mp ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hNφ)⟩
 let I3:=Finset.Icc ⌊-(6*(M:E)*A/p3)⌋ ⌈6*(M:E)*A/p3⌉
 let F2:ℤ->Finset ℤ:=fun z3 =>
  Finset.Icc ⌊(p3*(z3:E)-6*(M:E)*B)/p2⌋ ⌈(p3*(z3:E)+6*(M:E)*B)/p2⌉
 let F1:ℤ->Finset ℤ:=fun z3 =>
  Finset.Icc ⌊(p3*(z3:E)-6*(M:E)*B)/p1⌋ ⌈(p3*(z3:E)+6*(M:E)*B)/p1⌉
 let box:=I3.sigma (fun z3=>F1 z3×ˢF2 z3)
 have himg_sub:(dom.image φ)⊆box.image (fun p=>(p.2.1,p.2.2,p.1)):=by
  intro z hz;rcases Finset.mem_image.mp hz with ⟨t,ht,rfl⟩;have hbd:=hφ_bd t ht;refine Finset.mem_image.mpr ⟨⟨(φ t).2.2,((φ t).1,(φ t).2.1)⟩,?_,rfl⟩;rw [Finset.mem_sigma,mem_product]
  refine ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,Finset.mem_Icc.mpr ⟨?_,?_⟩,Finset.mem_Icc.mpr ⟨?_,?_⟩⟩
  ·
    have hle:-(6*(M:E)*A/p3)<=((φ t).2.2:E):=by
     have:=(abs_le.mp hbd.1).1;rw [← neg_div,div_le_iff₀ hp3];linarith
    exact_mod_cast (Int.floor_le _).trans hle
  ·
    have hle:((φ t).2.2:E)<=6*(M:E)*A/p3:=by
     have:=(abs_le.mp hbd.1).2;rw [le_div_iff₀ hp3];linarith
    exact_mod_cast hle.trans (Int.le_ceil _)
  ·
    have hle:(p3*((φ t).2.2:E)-6*(M:E)*B)/p1<=((φ t).1:E):=by
     have:=(abs_le.mp hbd.2.2).1;rw [div_le_iff₀ hp1];linarith
    exact_mod_cast (Int.floor_le _).trans hle
  ·
    have hle:((φ t).1:E)<=(p3*((φ t).2.2:E)+6*(M:E)*B)/p1:=by
     have:=(abs_le.mp hbd.2.2).2;rw [le_div_iff₀ hp1];linarith
    exact_mod_cast hle.trans (Int.le_ceil _)
  ·
    have hle:(p3*((φ t).2.2:E)-6*(M:E)*B)/p2<=((φ t).2.1:E):=by
     have:=(abs_le.mp hbd.2.1).1;rw [div_le_iff₀ hp2];linarith
    exact_mod_cast (Int.floor_le _).trans hle
  ·
    have hle:((φ t).2.1:E)<=(p3*((φ t).2.2:E)+6*(M:E)*B)/p2:=by
     have:=(abs_le.mp hbd.2.1).2;rw [le_div_iff₀ hp2];linarith
    exact_mod_cast hle.trans (Int.le_ceil _)
 have hcard_I3:(I3.card:E)<=14*(M:E)*A/p3:=by
  have hlo:-(6*(M:E)*A/p3)<=6*(M:E)*A/p3:=by
    have:0<=6*(M:E)*A/p3:=by positivity
    linarith
  have h:=card_int_interval (-(6*(M:E)*A/p3)) (6*(M:E)*A/p3) hlo;have h2:(3:E)<=2*(M:E)*A/p3:=by rw [le_div_iff₀ hp3];have:=(div_le_iff₀ hA).mp hM3;linarith
  have hsum:6*(M:E)*A/p3 - -(6*(M:E)*A/p3)+2*(M:E)*A/p3 = 14*(M:E)*A/p3:=by ring
  change ((Finset.Icc ⌊-(6*(M:E)*A/p3)⌋ ⌈6*(M:E)*A/p3⌉).card:E)<=_;linarith
 have hcard_F2:∀ z3:ℤ,((F2 z3).card:E)<=14*(M:E)*B/p2:=by
  intro z3;have hlo:(p3*(z3:E)-6*(M:E)*B)/p2<=(p3*(z3:E)+6*(M:E)*B)/p2 :=div_le_div_of_nonneg_right (by linarith [mul_nonneg hMR.le hB.le]) hp2.le;have h:=card_int_interval _ _ hlo
  have hd:(p3*(z3:E)+6*(M:E)*B)/p2-(p3*(z3:E)-6*(M:E)*B)/p2 = 12*(M:E)*B/p2:=by ring
  rw [hd] at h;have h2:(3:E)<=2*(M:E)*B/p2:=by rw [le_div_iff₀ hp2];have:=(div_le_iff₀ hB).mp hM2;linarith
  have hsum:12*(M:E)*B/p2+2*(M:E)*B/p2=14*(M:E)*B/p2:=by ring
  change ((Finset.Icc ⌊(p3*(z3:E)-6*(M:E)*B)/p2⌋
        ⌈(p3*(z3:E)+6*(M:E)*B)/p2⌉).card:E)<=_
  linarith
 have hcard_F1:∀ z3:ℤ,((F1 z3).card:E)<=14*(M:E)*B/p1:=by
  intro z3;have hlo:(p3*(z3:E)-6*(M:E)*B)/p1<=(p3*(z3:E)+6*(M:E)*B)/p1 :=div_le_div_of_nonneg_right (by linarith [mul_nonneg hMR.le hB.le]) hp1.le;have h:=card_int_interval _ _ hlo
  have hd:(p3*(z3:E)+6*(M:E)*B)/p1-(p3*(z3:E)-6*(M:E)*B)/p1 = 12*(M:E)*B/p1:=by ring
  rw [hd] at h;have h2:(3:E)<=2*(M:E)*B/p1:=by rw [le_div_iff₀ hp1];have:=(div_le_iff₀ hB).mp hM1;linarith
  have hsum:12*(M:E)*B/p1+2*(M:E)*B/p1=14*(M:E)*B/p1:=by ring
  change ((Finset.Icc ⌊(p3*(z3:E)-6*(M:E)*B)/p1⌋
        ⌈(p3*(z3:E)+6*(M:E)*B)/p1⌉).card:E)<=_
  linarith
 have hcard_box:(box.card:E)<=3000*(M:E)^3*A*B^2/(p1*p2*p3):=by
  rw [Finset.card_sigma,Nat.cast_sum]
  calc
    (∑ z3∈I3,(((F1 z3×ˢF2 z3).card:ℕ):E))
      ≤ ∑ _z3∈I3,((14*(M:E)*B/p1)*(14*(M:E)*B/p2)):=by
     apply sum_le_sum;intro z3 _;rw [Finset.card_product,Nat.cast_mul];exact mul_le_mul (hcard_F1 z3) (hcard_F2 z3) (Nat.cast_nonneg _) (by positivity)
    _ = (I3.card:E)*((14*(M:E)*B/p1)*(14*(M:E)*B/p2)):=by simp
    _ <= (14*(M:E)*A/p3)*((14*(M:E)*B/p1)*(14*(M:E)*B/p2)) :=mul_le_mul_of_nonneg_right hcard_I3 (by positivity)
    _ = 2744*((M:E)^3*A*B^2/(p1*p2*p3)):=by ring
    _ <= 3000*((M:E)^3*A*B^2/(p1*p2*p3)):=by
     have:0<=(M:E)^3*A*B^2/(p1*p2*p3):=by positivity
     linarith
    _ = 3000*(M:E)^3*A*B^2/(p1*p2*p3):=by ring
 have hcard_dom:(dom.card:E)=(S.card:E)*(M:E)^3:=by
  simp only [dom,Finset.card_product,card_range];push_cast;ring
 have hle:(S.card:E)*(M:E)^3<=(3000*A*B^2/(p1*p2*p3))*(M:E)^3:=by
  calc
    (S.card:E)*(M:E)^3=(dom.card:E):=hcard_dom.symm
    _ = ((dom.image φ).card:E):=by exact_mod_cast (Finset.card_image_iff.mpr hφ_inj).symm
    _ <= ((box.image (fun p=>(p.2.1,p.2.2,p.1))).card:E) := by exact_mod_cast Finset.card_le_card himg_sub
    _ <= (box.card:E):=by exact_mod_cast card_image_le
    _ <= 3000*(M:E)^3*A*B^2/(p1*p2*p3):=hcard_box
    _ = (3000*A*B^2/(p1*p2*p3))*(M:E)^3:=by ring
 exact le_of_mul_le_mul_right hle (pow_pos hMR 3)
theorem card_rank2_plane_le {p1 p2 p3 A B:E}
  (_hp1:0 < p1) (hp2:0 < p2) (hp3:0 < p3) (hA:0 < A) (hB:0 < B)
  (a1 a2 a3:ℤ) (ha1:a1≠0) (hprim:Int.gcd (Int.gcd a1 a2:ℤ) a3=1)
  (S:Finset (ℤ × ℤ × ℤ))
  (hplane:∀ v∈S,a1*v.1+a2*v.2.1+a3*v.2.2=0)
  (hS:∀ v∈S,|p3*(v.2.2:E)| ≤ A ∧
           |p2*(v.2.1:E)-p3*(v.2.2:E)| ≤ B ∧
           |p1*(v.1:E)-p3*(v.2.2:E)| ≤ B)
  (hrank:∃ w1∈S,∃ w2∈S,w1.2.1*w2.2.2-w1.2.2*w2.2.1≠0 ∨ w1.2.2*w2.1-w1.1*w2.2.2≠0 ∨ w1.1*w2.2.1-w1.2.1*w2.1≠0) :
  (S.card:E)<=100*A*B/(p2*p3 * |(a1:E)|):=by
 let N:E × E × E->E:=fun u =>
  max (|p3*u.2.2| / A) (max (|p2*u.2.1-p3*u.2.2| / B) (|p1*u.1-p3*u.2.2| / B))
 obtain ⟨hadd,hsmul⟩:=sheared_norm3_props (p1:=p1) (p2:=p2) (p3:=p3) hA hB
 have hNS:∀ v∈S,N (v.1,v.2.1,v.2.2)<=1:=by
  intro v hv;dsimp [N]
  exact max_le ((div_le_one hA).mpr (hS v hv).1)
    (max_le ((div_le_one hB).mpr (hS v hv).2.1) ((div_le_one hB).mpr (hS v hv).2.2))
 obtain ⟨w1,hw1,w2,hw2,hli⟩:=hrank;obtain ⟨e1,e2,f3,hdet_f,⟨g,hg_pos,hw1_1,hw1_2,hw1_3⟩,⟨ca,cb,hcb_pos,hw2_1,hw2_2,hw2_3⟩,hNe1,hNe2⟩ :=exists_unimodular_basis_3d_rank2 N hadd hsmul w1 w2 hli (hNS w1 hw1) (hNS w2 hw2)
 have he1_plane:a1*e1.1+a2*e1.2.1+a3*e1.2.2=0:=by
  have hp:=hplane w1 hw1;rw [hw1_1,hw1_2,hw1_3] at hp
  have:g*(a1*e1.1+a2*e1.2.1+a3*e1.2.2)=0:=by linarith
  exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hg_pos)
 have he2_plane:a1*e2.1+a2*e2.2.1+a3*e2.2.2=0:=by
  have hp:=hplane w2 hw2;rw [hw2_1,hw2_2,hw2_3] at hp
  have:cb*(a1*e2.1+a2*e2.2.1+a3*e2.2.2)=0:=by linear_combination hp-ca*he1_plane
  exact (mul_eq_zero.mp this).resolve_left (ne_of_gt hcb_pos)
 let g12:ℤ:=(Int.gcd a1 a2:ℤ);have hg12_pos:0 < g12:=by dsimp [g12];exact_mod_cast Int.gcd_pos_of_ne_zero_left a2 ha1
 let a1abs:ℤ:=|a1|;have ha1abs_pos:0 < a1abs:=abs_pos.mpr ha1
 have hg12_dvd_a1abs:g12∣a1abs:=by
  dsimp [a1abs,g12];rcases le_or_gt 0 a1 with h | h
  · rw [abs_of_nonneg h];exact Int.gcd_dvd_left a1 a2
  · rw [abs_of_neg h];exact (Int.gcd_dvd_left a1 a2).neg_right
 let m2:ℤ:=a1abs/g12;have hm2_mul:g12*m2=a1abs:=Int.mul_ediv_cancel' hg12_dvd_a1abs;have hm2_pos:0 < m2:=by nlinarith
 let a2':ℤ:=a2/g12;have ha2'_mul:g12*a2'=a2:=Int.mul_ediv_cancel' (Int.gcd_dvd_right a1 a2)
 have hcop_a2m2:IsCoprime a2' m2:=by
  have hbez:=Int.gcd_eq_gcd_ab a1 a2;let sgn1:ℤ:=if 0<=a1 then 1 else -1
  have hsgn1_mul:sgn1*a1abs=a1:=by
    dsimp [sgn1,a1abs];split_ifs with h
    · rw [abs_of_nonneg h];ring
    · rw [abs_of_neg (lt_of_not_ge h)];ring
  refine ⟨Int.gcdB a1 a2,sgn1*Int.gcdA a1 a2,?_⟩
  have hmul:g12*(Int.gcdB a1 a2*a2'+sgn1*Int.gcdA a1 a2*m2)=g12*1:=by
    calc
     g12*(Int.gcdB a1 a2*a2'+sgn1*Int.gcdA a1 a2*m2)
        = (g12*a2')*Int.gcdB a1 a2+(sgn1*(g12*m2))*Int.gcdA a1 a2:=by ring
     _ = a2*Int.gcdB a1 a2+a1*Int.gcdA a1 a2:=by rw [ha2'_mul,hm2_mul,hsgn1_mul]
     _ = g12:=by linarith [hbez]
     _ = g12*1:=(mul_one g12).symm
  exact mul_left_cancel₀ (ne_of_gt hg12_pos) hmul
 have hcop_g12_a3:IsCoprime g12 a3:=by
  have hbez:=Int.gcd_eq_gcd_ab g12 a3;have hgg:Int.gcd g12 a3=1:=hprim;rw [hgg] at hbez;refine ⟨Int.gcdA g12 a3,Int.gcdB g12 a3,?_⟩
  calc
    Int.gcdA g12 a3*g12+Int.gcdB g12 a3*a3
      = g12*Int.gcdA g12 a3+a3*Int.gcdB g12 a3:=by ring
    _ = 1:=by simpa using hbez.symm
 let M:ℕ:=⌈max (2*p3*(g12:E)/A) (2*p2*(m2:E)/B)⌉₊+10;have hM_pos:0 < M:=by dsimp [M];omega
 have hMR:(0:E) < (M:E):=by exact_mod_cast hM_pos
 have hM3:2*p3*(g12:E)/A<=(M:E):=by
  have h1:=le_max_left (2*p3*(g12:E)/A) (2*p2*(m2:E)/B);have h2:=Nat.le_ceil (max (2*p3*(g12:E)/A) (2*p2*(m2:E)/B));dsimp [M];push_cast;linarith
 have hM2:2*p2*(m2:E)/B<=(M:E):=by
  have h1:=le_max_right (2*p3*(g12:E)/A) (2*p2*(m2:E)/B);have h2:=Nat.le_ceil (max (2*p3*(g12:E)/A) (2*p2*(m2:E)/B));dsimp [M];push_cast;linarith
 let dom:=S×ˢ(Finset.range M×ˢFinset.range M)
 let φ3:(ℤ × ℤ × ℤ) × (ℕ × ℕ)->ℤ × ℤ × ℤ:=fun t =>
  ((M:ℤ)*t.1.1+(t.2.1:ℤ)*e1.1+(t.2.2:ℤ)*e2.1,(M:ℤ)*t.1.2.1+(t.2.1:ℤ)*e1.2.1+(t.2.2:ℤ)*e2.2.1,(M:ℤ)*t.1.2.2+(t.2.1:ℤ)*e1.2.2+(t.2.2:ℤ)*e2.2.2)
 let φ:(ℤ × ℤ × ℤ) × (ℕ × ℕ)->ℤ × ℤ:=fun t=>((φ3 t).2.1,(φ3 t).2.2)
 have hφ3_plane:∀ t∈dom,a1*(φ3 t).1+a2*(φ3 t).2.1+a3*(φ3 t).2.2=0:=by
  rintro ⟨v,i,j⟩ ht;have hv:=hplane v (mem_product.mp ht).1;dsimp [φ3]
  linear_combination (M:ℤ)*hv+(i:ℤ)*he1_plane+(j:ℤ)*he2_plane
 have hφ_inj:Set.InjOn φ (dom:Set _):=by
  rintro ⟨v,i,j⟩ h1 ⟨v',i',j'⟩ h2 heq;have h1':=h1;have h2':=h2;simp only [dom,Finset.mem_coe,mem_product,Finset.mem_range] at h1 h2;have he2:=congrArg Prod.fst heq;have he3:=congrArg Prod.snd heq;dsimp [φ] at he2 he3;have hpl1:=hφ3_plane (v,i,j) h1'
  have hpl2:=hφ3_plane (v',i',j') h2'
  have he1:(φ3 (v,i,j)).1=(φ3 (v',i',j')).1:=by
    have:a1*((φ3 (v,i,j)).1-(φ3 (v',i',j')).1)=0:=by linear_combination hpl1-hpl2-a2*he2-a3*he3
    have hsub:=(mul_eq_zero.mp this).resolve_left ha1;linarith
  dsimp [φ3] at he1 he2 he3;let dv:ℤ × ℤ × ℤ:=(v'.1-v.1,v'.2.1-v.2.1,v'.2.2-v.2.2)
  have hdi:(M:ℤ)∣((i:ℤ)-(i':ℤ)):=by
    have hlin:det3 e1 e2 f3*((i:ℤ)-(i':ℤ))=(M:ℤ)*det3 dv e2 f3:=by
     dsimp [det3,dv]
     linear_combination (e2.2.1*f3.2.2-e2.2.2*f3.2.1)*he1 -
      (e2.1*f3.2.2-e2.2.2*f3.1)*he2+(e2.1*f3.2.1-e2.2.1*f3.1)*he3
    rcases hdet_f with hd | hd
    · rw [hd,one_mul] at hlin;exact ⟨_,hlin⟩
    · rw [hd,neg_one_mul] at hlin;exact ⟨-det3 dv e2 f3,by linarith⟩
  have hdj:(M:ℤ)∣((j:ℤ)-(j':ℤ)):=by
    have hlin:det3 e1 e2 f3*((j:ℤ)-(j':ℤ))=(M:ℤ)*det3 e1 dv f3:=by
     dsimp [det3,dv]
     linear_combination -(e1.2.1*f3.2.2-e1.2.2*f3.2.1)*he1 + (e1.1*f3.2.2-e1.2.2*f3.1)*he2-(e1.1*f3.2.1-e1.2.1*f3.1)*he3
    rcases hdet_f with hd | hd
    · rw [hd,one_mul] at hlin;exact ⟨_,hlin⟩
    · rw [hd,neg_one_mul] at hlin;exact ⟨-det3 e1 dv f3,by linarith⟩
  have hi_eq:i=i':=eq_of_nat_lt_of_dvd_sub h1.2.1 h2.2.1 hdi;have hj_eq:j=j':=eq_of_nat_lt_of_dvd_sub h1.2.2 h2.2.2 hdj;subst hi_eq;subst hj_eq;have hv1:v.1=v'.1:=mul_left_cancel₀ (by exact_mod_cast hM_pos.ne') (by linarith:(M:ℤ)*v.1=(M:ℤ)*v'.1)
  have hv2:v.2.1=v'.2.1:=mul_left_cancel₀ (by exact_mod_cast hM_pos.ne') (by linarith:(M:ℤ)*v.2.1=(M:ℤ)*v'.2.1);have hv3:v.2.2=v'.2.2:=mul_left_cancel₀ (by exact_mod_cast hM_pos.ne') (by linarith:(M:ℤ)*v.2.2=(M:ℤ)*v'.2.2)
  exact Prod.ext (Prod.ext hv1 (Prod.ext hv2 hv3)) rfl
 have hφ_bd:∀ t∈dom,
    |p3*((φ t).2:E)| ≤ 4*(M:E)*A ∧
    |p2*((φ t).1:E)-p3*((φ t).2:E)| ≤ 4*(M:E)*B ∧
    g12∣(φ t).2/\m2∣a2'*(φ t).1+a3*((φ t).2/g12):=by
  rintro ⟨v,i,j⟩ ht;have hpl:=hφ3_plane (v,i,j) ht;simp only [dom,mem_product,Finset.mem_range] at ht;have hiM:(i:E)<=(M:E):=by exact_mod_cast ht.2.1.le
  have hjM:(j:E)<=(M:E):=by exact_mod_cast ht.2.2.le
  have hNφ:N ((φ3 (v,i,j)).1,(φ3 (v,i,j)).2.1,(φ3 (v,i,j)).2.2)<=4*(M:E):=by
    have heq:(((φ3 (v,i,j)).1:E),((φ3 (v,i,j)).2.1:E),((φ3 (v,i,j)).2.2:E)) = (((M:E)*(v.1:E)+(i:E)*(e1.1:E))+(j:E)*(e2.1:E),((M:E)*(v.2.1:E)+(i:E)*(e1.2.1:E))+(j:E)*(e2.2.1:E),((M:E)*(v.2.2:E)+(i:E)*(e1.2.2:E))+(j:E)*(e2.2.2:E)):=by
     refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp [φ3] <;> push_cast <;> ring
    rw [heq]
    have h1:=hadd ((M:E)*(v.1:E)+(i:E)*(e1.1:E),(M:E)*(v.2.1:E)+(i:E)*(e1.2.1:E),(M:E)*(v.2.2:E)+(i:E)*(e1.2.2:E))
            ((j:E)*(e2.1:E),(j:E)*(e2.2.1:E),(j:E)*(e2.2.2:E))
    have h2:=hadd ((M:E)*(v.1:E),(M:E)*(v.2.1:E),(M:E)*(v.2.2:E))
            ((i:E)*(e1.1:E),(i:E)*(e1.2.1:E),(i:E)*(e1.2.2:E))
    have hsM:=hsmul (M:E) (v.1,v.2.1,v.2.2);have hsi:=hsmul (i:E) (e1.1,e1.2.1,e1.2.2);have hsj:=hsmul (j:E) (e2.1,e2.2.1,e2.2.2);rw [abs_of_nonneg hMR.le] at hsM;rw [abs_of_nonneg (Nat.cast_nonneg i)] at hsi;rw [abs_of_nonneg (Nat.cast_nonneg j)] at hsj
    have hnn:∀ u,0<=N u:=fun u=>le_trans (div_nonneg (abs_nonneg _) hA.le) (le_max_left _ _);nlinarith [hNS v ht.1,hnn (e1.1,e1.2.1,e1.2.2),hnn (e2.1,e2.2.1,e2.2.2)]
  have hdv_a1:a1abs∣a2*(φ3 (v,i,j)).2.1+a3*(φ3 (v,i,j)).2.2:=by
    dsimp [a1abs];rw [abs_dvd];exact ⟨-(φ3 (v,i,j)).1,by linarith⟩
  have hdv_g12_prod:g12∣a3*(φ3 (v,i,j)).2.2:=by
    have h1:g12∣a2*(φ3 (v,i,j)).2.1+a3*(φ3 (v,i,j)).2.2 :=dvd_trans hg12_dvd_a1abs hdv_a1;have h2:g12∣a2*(φ3 (v,i,j)).2.1 :=dvd_mul_of_dvd_left (Int.gcd_dvd_right a1 a2) _
    have:=dvd_sub h1 h2
    simpa using this
  have hdv_z3:g12∣(φ3 (v,i,j)).2.2:=hcop_g12_a3.dvd_of_dvd_mul_left hdv_g12_prod
  have hdv_m2:m2∣a2'*(φ3 (v,i,j)).2.1+a3*((φ3 (v,i,j)).2.2/g12):=by
    obtain ⟨q,hq⟩:=hdv_a1;refine ⟨q,?_⟩;have hz3_mul:g12*((φ3 (v,i,j)).2.2/g12)=(φ3 (v,i,j)).2.2 :=Int.mul_ediv_cancel' hdv_z3
    have hmul:g12*(a2'*(φ3 (v,i,j)).2.1+a3*((φ3 (v,i,j)).2.2/g12)) = g12*(m2*q):=by
     calc
      g12*(a2'*(φ3 (v,i,j)).2.1+a3*((φ3 (v,i,j)).2.2/g12))
         = (g12*a2')*(φ3 (v,i,j)).2.1+a3*(g12*((φ3 (v,i,j)).2.2/g12)):=by ring
      _ = a2*(φ3 (v,i,j)).2.1+a3*(φ3 (v,i,j)).2.2:=by rw [ha2'_mul,hz3_mul]
      _ = a1abs*q:=hq
      _ = (g12*m2)*q:=by rw [hm2_mul]
      _ = g12*(m2*q):=by ring
    exact mul_left_cancel₀ (ne_of_gt hg12_pos) hmul
  exact ⟨(div_le_iff₀ hA).mp ((le_max_left _ _).trans hNφ),(div_le_iff₀ hB).mp ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hNφ),hdv_z3,hdv_m2⟩
 let I3:=(Finset.Icc ⌊-(4*(M:E)*A/p3)⌋ ⌈4*(M:E)*A/p3⌉).filter (fun z3=>g12∣1*z3-0)
 let F2:ℤ->Finset ℤ:=fun z3 =>
  (Finset.Icc ⌊(p3*(z3:E)-4*(M:E)*B)/p2⌋
          ⌈(p3*(z3:E)+4*(M:E)*B)/p2⌉).filter
    (fun z2=>m2∣a2'*z2-(-(a3*(z3/g12))))
 let box:=I3.sigma F2
 have himg_sub:(dom.image φ)⊆box.image (fun p=>(p.2,p.1)):=by
  intro z hz;rcases Finset.mem_image.mp hz with ⟨t,ht,rfl⟩;have hbd:=hφ_bd t ht;refine Finset.mem_image.mpr ⟨⟨(φ t).2,(φ t).1⟩,?_,rfl⟩;rw [Finset.mem_sigma];refine ⟨mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,?_⟩,mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,?_⟩⟩
  ·
    have hle:-(4*(M:E)*A/p3)<=((φ t).2:E):=by
     have:=(abs_le.mp hbd.1).1;rw [← neg_div,div_le_iff₀ hp3];linarith
    exact_mod_cast (Int.floor_le _).trans hle
  ·
    have hle:((φ t).2:E)<=4*(M:E)*A/p3:=by
     have:=(abs_le.mp hbd.1).2;rw [le_div_iff₀ hp3];linarith
    exact_mod_cast hle.trans (Int.le_ceil _)
  · simpa using hbd.2.2.1
  ·
    have hle:(p3*((φ t).2:E)-4*(M:E)*B)/p2<=((φ t).1:E):=by
     have:=(abs_le.mp hbd.2.1).1;rw [div_le_iff₀ hp2];linarith
    exact_mod_cast (Int.floor_le _).trans hle
  ·
    have hle:((φ t).1:E)<=(p3*((φ t).2:E)+4*(M:E)*B)/p2:=by
     have:=(abs_le.mp hbd.2.1).2;rw [le_div_iff₀ hp2];linarith
    exact_mod_cast hle.trans (Int.le_ceil _)
  · simpa [sub_neg_eq_add] using hbd.2.2.2
 have hg12R:(0:E) < (g12:E):=by exact_mod_cast hg12_pos
 have hm2R:(0:E) < (m2:E):=by exact_mod_cast hm2_pos
 have hcard_I3:(I3.card:E)<=10*(M:E)*A/(p3*(g12:E)):=by
  have hlo:-(4*(M:E)*A/p3)<=4*(M:E)*A/p3:=by
    have:0<=4*(M:E)*A/p3:=by positivity
    linarith
  have h:=card_int_congr_interval 1 0 g12 hg12_pos isCoprime_one_left
    (-(4*(M:E)*A/p3)) (4*(M:E)*A/p3) hlo
  have hd:(4*(M:E)*A/p3 - -(4*(M:E)*A/p3))/(g12:E) = 8*(M:E)*A/(p3*(g12:E)):=by ring
  rw [hd] at h
  have h2:(3:E)<=2*(M:E)*A/(p3*(g12:E)):=by
    rw [le_div_iff₀ (by positivity)];have hpos:0 < p3*(g12:E):=by positivity
    have:=(div_le_iff₀ hA).mp hM3
    linarith
  have hsum:8*(M:E)*A/(p3*(g12:E))+2*(M:E)*A/(p3*(g12:E)) = 10*(M:E)*A/(p3*(g12:E)):=by ring
  change (((Finset.Icc ⌊-(4*(M:E)*A/p3)⌋ ⌈4*(M:E)*A/p3⌉).filter _).card:E)<=_;linarith
 have hcard_F2:∀ z3:ℤ,((F2 z3).card:E)<=10*(M:E)*B/(p2*(m2:E)):=by
  intro z3;have hlo:(p3*(z3:E)-4*(M:E)*B)/p2<=(p3*(z3:E)+4*(M:E)*B)/p2 :=div_le_div_of_nonneg_right (by linarith [mul_nonneg hMR.le hB.le]) hp2.le;have h:=card_int_congr_interval a2' (-(a3*(z3/g12))) m2 hm2_pos hcop_a2m2 _ _ hlo
  have hd:((p3*(z3:E)+4*(M:E)*B)/p2-(p3*(z3:E)-4*(M:E)*B)/p2)/(m2:E) = 8*(M:E)*B/(p2*(m2:E)):=by ring
  rw [hd] at h
  have h2:(3:E)<=2*(M:E)*B/(p2*(m2:E)):=by
    rw [le_div_iff₀ (by positivity)];have hpos:0 < p2*(m2:E):=by positivity
    have:=(div_le_iff₀ hB).mp hM2
    linarith
  have hsum:8*(M:E)*B/(p2*(m2:E))+2*(M:E)*B/(p2*(m2:E)) = 10*(M:E)*B/(p2*(m2:E)):=by ring
  change (((Finset.Icc ⌊(p3*(z3:E)-4*(M:E)*B)/p2⌋
          ⌈(p3*(z3:E)+4*(M:E)*B)/p2⌉).filter _).card:E)<=_
  linarith
 have hprod_a1:(g12:E)*(m2:E) = |(a1:E)|:=by
  have:(g12:E)*(m2:E)=(a1abs:E):=by exact_mod_cast hm2_mul
  rw [this];dsimp [a1abs];exact Int.cast_abs
 have hcard_box:(box.card:E)<=100*(M:E)^2*A*B/(p2*p3 * |(a1:E)|):=by
  rw [Finset.card_sigma,Nat.cast_sum]
  calc
    (∑ z3∈I3,((F2 z3).card:E))
      ≤ ∑ _z3∈I3,(10*(M:E)*B/(p2*(m2:E))) :=
     sum_le_sum (fun z3 _=>hcard_F2 z3)
    _ = (I3.card:E)*(10*(M:E)*B/(p2*(m2:E))):=by simp
    _ <= (10*(M:E)*A/(p3*(g12:E)))*(10*(M:E)*B/(p2*(m2:E))) :=mul_le_mul_of_nonneg_right hcard_I3 (by positivity)
    _ = 100*(M:E)^2*A*B/(p2*p3*((g12:E)*(m2:E))):=by ring
    _ = 100*(M:E)^2*A*B/(p2*p3 * |(a1:E)|):=by rw [hprod_a1]
 have hcard_dom:(dom.card:E)=(S.card:E)*(M:E)^2:=by
  simp only [dom,Finset.card_product,card_range];push_cast;ring
 have hle:(S.card:E)*(M:E)^2 ≤ (100*A*B/(p2*p3 * |(a1:E)|))*(M:E)^2:=by
  calc
    (S.card:E)*(M:E)^2=(dom.card:E):=hcard_dom.symm
    _ = ((dom.image φ).card:E):=by exact_mod_cast (Finset.card_image_iff.mpr hφ_inj).symm
    _ <= ((box.image (fun p=>(p.2,p.1))).card:E) := by exact_mod_cast Finset.card_le_card himg_sub
    _ <= (box.card:E):=by exact_mod_cast card_image_le
    _ <= 100*(M:E)^2*A*B/(p2*p3 * |(a1:E)|):=hcard_box
    _ = (100*A*B/(p2*p3 * |(a1:E)|))*(M:E)^2:=by ring
 exact le_of_mul_le_mul_right hle (pow_pos hMR 2)
lemma int_dvd_abs {a b:ℤ} (h:a∣b):a∣|b|:=by
 rcases le_or_gt 0 b with hb | hb
 · rwa [abs_of_nonneg hb]
 · rw [abs_of_neg hb];exact h.neg_right
lemma min_le_weighted_rpow {A B θ:E} (hA:0<=A) (hB:0<=B) (hθ0:0<=θ) (hθ1:θ<=1) :
  min A B<=A^θ*B^(1-θ):=by
 by_cases hA0:A=0
 ·
  subst hA0;have hmin:min 0 B<=0:=min_le_left 0 B;exact hmin.trans (by positivity)
 ·
  by_cases hB0:B=0
  ·
   subst hB0;have hmin:min A 0<=0:=min_le_right A 0;exact hmin.trans (by positivity)
  ·
   have hAp:0 < A:=lt_of_le_of_ne hA (Ne.symm hA0);have hBp:0 < B:=lt_of_le_of_ne hB (Ne.symm hB0);rcases le_total A B with hAB | hBA
   ·
    rw [min_eq_left hAB];have h1:A^(1-θ)<=B^(1-θ):=rpow_le_rpow hA hAB (by linarith)
    calc
     A=A^(θ+(1-θ)):=by simp
     _ = A^θ*A^(1-θ):=rpow_add hAp θ (1-θ)
     _ <= A^θ*B^(1-θ):=mul_le_mul_of_nonneg_left h1 (rpow_nonneg hA θ)
   ·
    rw [min_eq_right hBA];have h1:B^θ<=A^θ:=rpow_le_rpow hB hBA hθ0
    calc
     B=B^(θ+(1-θ)):=by simp
     _ = B^θ*B^(1-θ):=rpow_add hBp θ (1-θ)
     _ <= A^θ*B^(1-θ):=mul_le_mul_of_nonneg_right h1 (rpow_nonneg hB (1-θ))
lemma sum_dyadic_min_le (T:ℕ) {U V:E} (hU:0<=U) (hV:0<=V) :
  ∑ t∈Finset.range T,min ((2:E)^t*U) (V/(2:E)^t) ≤ 4*(U*V)^(1/2:E):=by
 classical
 by_cases hUV:U*V=0
 ·
  rcases mul_eq_zero.mp hUV with rfl | rfl
  ·
   have h0:∀ t∈Finset.range T,min ((2:E)^t*0) (V/(2:E)^t)=0:=by
    intro t _;rw [mul_zero];exact min_eq_left (by positivity)
   rw [Finset.sum_eq_zero h0];positivity
  ·
   have h0:∀ t∈Finset.range T,min ((2:E)^t*U) (0/(2:E)^t)=0:=by
    intro t _;rw [zero_div];exact min_eq_right (by positivity)
   rw [Finset.sum_eq_zero h0];positivity
 ·
  have hU_pos:0 < U:=lt_of_le_of_ne hU (fun h=>hUV (by rw [← h,zero_mul]));have hV_pos:0 < V:=lt_of_le_of_ne hV (fun h=>hUV (by rw [← h,mul_zero]));let M:E:=(U*V)^(1/2:E);have hM_sq:M*M=U*V:=by dsimp [M];rw [← rpow_add (by positivity)];norm_num
  let Slo:=(Finset.range T).filter (fun t=>(2:E)^t*U<=M);let Shi:=(Finset.range T).filter (fun t=>¬ ((2:E)^t*U<=M));rw [← Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun t=>(2:E)^t*U<=M)]
  have hlo:∑ t∈Slo,min ((2:E)^t*U) (V/(2:E)^t)<=2*M:=by
   by_cases hne:Slo.Nonempty
   ·
    let tm:=Slo.max' hne;have htm_mem:tm∈Slo:=Finset.max'_mem Slo hne;have htm_le:(2:E)^tm*U<=M:=(mem_filter.mp htm_mem).2
    have hsub:Slo⊆Finset.range (tm+1):=fun t ht =>
     Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' Slo t ht))
    have hgeom:∑ t∈Finset.range (tm+1),(2:E)^t=(2:E)^(tm+1)-1:=by
     induction tm with
     | zero=>norm_num
     | succ n ih=>rw [sum_range_succ,ih,pow_succ];ring
    calc
     ∑ t∈Slo,min ((2:E)^t*U) (V/(2:E)^t)
       ≤ ∑ t∈Slo,((2:E)^t*U):=sum_le_sum (fun t _=>min_le_left _ _)
     _ <= ∑ t∈Finset.range (tm+1),((2:E)^t*U) :=Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by positivity)
     _ = (∑ t∈Finset.range (tm+1),(2:E)^t)*U:=(Finset.sum_mul _ _ _).symm
     _ = ((2:E)^(tm+1)-1)*U:=by rw [hgeom]
     _ <= 2*((2:E)^tm*U):=by rw [pow_succ];nlinarith
     _ <= 2*M:=by linarith
   · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty];positivity
  have hhi:∑ t∈Shi,min ((2:E)^t*U) (V/(2:E)^t)<=2*M:=by
   by_cases hne:Shi.Nonempty
   ·
    let t0:=Shi.min' hne;have ht0_mem:t0∈Shi:=Finset.min'_mem Shi hne;have ht0_gt:M < (2:E)^t0*U:=lt_of_not_ge (mem_filter.mp ht0_mem).2
    have hV_le:V/(2:E)^t0<=M:=by
     rw [div_le_iff₀ (by positivity)]
     have:M*M < (2:E)^t0*U*M:=by nlinarith [rpow_pos_of_pos (mul_pos hU_pos hV_pos) (1/2:E)]
     nlinarith
    have hgeom_half:∀ n:ℕ,∑ k∈Finset.range n,((1/2:E)^k)<=2:=by
     intro n
     have h:∑ k∈Finset.range n,((1/2:E)^k)=2-2*(1/2:E)^n:=by
      induction n with
      | zero=>norm_num
      | succ k ih=>rw [sum_range_succ,ih,pow_succ];ring
     rw [h];linarith [pow_nonneg (by norm_num:(0:E)<=1/2) n]
    have himg:∑ t∈Shi,(V/(2:E)^t) ≤ (V/(2:E)^t0)*∑ k∈Finset.range T,((1/2:E)^k):=by
     let shift:ℕ->ℕ:=fun t=>t-t0
     have hinj:Set.InjOn shift Shi:=by
      intro a ha b hb heq;have ha_ge:t0<=a:=Finset.min'_le Shi a ha;have hb_ge:t0<=b:=Finset.min'_le Shi b hb;dsimp [shift] at heq;omega
     have hsub:Shi.image shift⊆Finset.range T:=by
      intro k hk;rcases Finset.mem_image.mp hk with ⟨t,ht,rfl⟩;have htT:t < T:=Finset.mem_range.mp (mem_filter.mp ht).1;exact Finset.mem_range.mpr (by dsimp [shift];omega)
     calc
      ∑ t∈Shi,(V/(2:E)^t)
        = ∑ t∈Shi,((V/(2:E)^t0)*(1/2:E)^(t-t0)):=by
       apply sum_congr rfl;intro t ht;have ht_ge:t0<=t:=Finset.min'_le Shi t ht;have hpow:(2:E)^t=(2:E)^t0*(2:E)^(t-t0):=by rw [← pow_add,Nat.add_sub_cancel' ht_ge]
       rw [hpow,one_div,inv_pow];field_simp [pow_ne_zero t0 (by norm_num:(2:E)≠0),pow_ne_zero (t-t0) (by norm_num:(2:E)≠0)]
      _ = (V/(2:E)^t0)*∑ t∈Shi,((1/2:E)^(shift t)):=by rw [← Finset.mul_sum]
      _ = (V/(2:E)^t0)*∑ k∈Shi.image shift,((1/2:E)^k):=by rw [Finset.sum_image (fun a ha b hb h=>hinj ha hb h)]
      _ <= (V/(2:E)^t0)*∑ k∈Finset.range T,((1/2:E)^k) := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by positivity)) (by positivity)
    calc
     ∑ t∈Shi,min ((2:E)^t*U) (V/(2:E)^t)
       ≤ ∑ t∈Shi,(V/(2:E)^t):=sum_le_sum (fun t _=>min_le_right _ _)
     _ <= (V/(2:E)^t0)*∑ k∈Finset.range T,((1/2:E)^k):=himg
     _ <= (V/(2:E)^t0)*2:=mul_le_mul_of_nonneg_left (hgeom_half T) (by positivity)
     _ <= 2*M:=by linarith
   · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty];positivity
  linarith
lemma sum_dyadic_inv_rpow_le (T:ℕ) {α:E} (hα:0 < α) :
  ∑ t∈Finset.range T,((2:E)^t)^(-α)<=1/(1-(2:E)^(-α)):=by
 let r:E:=(2:E)^(-α);have hr_pos:0 < r:=rpow_pos_of_pos (by norm_num) _
 have hr_lt1:r < 1:=by
  dsimp [r];rw [rpow_neg (by norm_num)];exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hα)
 have h1r_pos:0 < 1-r:=by linarith
 have hterm:∀ t:ℕ,((2:E)^t)^(-α)=r^t:=by
  intro t;dsimp [r];rw [← rpow_natCast (2:E) t,← rpow_mul (by norm_num),← rpow_natCast ((2:E)^(-α)) t,← rpow_mul (by norm_num)];congr 1;ring
 have hsum:∑ t∈Finset.range T,r^t=(1-r^T)/(1-r):=by
  induction T with
  | zero=>simp
  | succ n ih =>
   rw [sum_range_succ,ih,pow_succ];field_simp [h1r_pos.ne'];ring
 calc
  ∑ t∈Finset.range T,((2:E)^t)^(-α)=∑ t∈Finset.range T,r^t :=sum_congr rfl (fun t _=>hterm t)
  _ = (1-r^T)/(1-r):=hsum
  _ <= 1/(1-r):=div_le_div_of_nonneg_right (by linarith [pow_nonneg hr_pos.le T]) h1r_pos.le
lemma sum_dyadic_rpow_le {S:Finset ℕ} {X α:E} (hX:0 < X) (hα:0 < α)
  (hS:∀ t∈S,(2:E)^t<=X) :
  ∑ t∈S,((2:E)^t)^α<=(1/(1-(2:E)^(-α)))*X^α:=by
 by_cases hne:S.Nonempty
 ·
  let tm:=S.max' hne;have htm_le:(2:E)^tm<=X:=hS tm (Finset.max'_mem S hne)
  have hsub:S⊆Finset.range (tm+1):=fun t ht =>
   Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S t ht))
  have h1:∑ t∈S,((2:E)^t)^α<=∑ t∈Finset.range (tm+1),((2:E)^t)^α :=Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by positivity)
  have hrev:∑ t∈Finset.range (tm+1),((2:E)^t)^α = ((2:E)^tm)^α*∑ k∈Finset.range (tm+1),((2:E)^k)^(-α):=by
   rw [Finset.mul_sum];rw [← Finset.sum_range_reflect (fun t=>((2:E)^t)^α) (tm+1)];apply sum_congr rfl;intro k hk;have hk_le:k<=tm:=by have:=Finset.mem_range.mp hk;omega
   have hidx:tm+1-1-k=tm-k:=by omega
   rw [hidx]
   have hpow:(2:E)^(tm-k)=(2:E)^tm*((2:E)^k)⁻¹:=by
    rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero k (by norm_num:(2:E)≠0)),← pow_add,Nat.sub_add_cancel hk_le]
   rw [hpow,mul_rpow (by positivity) (by positivity),Real.inv_rpow (by positivity),← rpow_neg (by positivity)]
  have hgeom:=sum_dyadic_inv_rpow_le (tm+1) hα;have hpow_le:((2:E)^tm)^α<=X^α:=rpow_le_rpow (by positivity) htm_le hα.le
  calc
   ∑ t∈S,((2:E)^t)^α<=((2:E)^tm)^α*∑ k∈Finset.range (tm+1),((2:E)^k)^(-α) :=hrev ▸ h1
   _ <= X^α*(1/(1-(2:E)^(-α))) :=mul_le_mul hpow_le hgeom (by positivity) (by positivity)
   _ = (1/(1-(2:E)^(-α)))*X^α:=mul_comm _ _
 ·
  rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
  have hr_lt1:(2:E)^(-α) < 1:=by
   rw [rpow_neg (by norm_num)];exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hα)
  have:0 < 1-(2:E)^(-α):=by linarith
  positivity
lemma card_separated_interval_le {ι:Type*} (S:Finset ι) (f:ι->E) {α0 R s:E}
  (hR:0<=R) (hs:0 < s)
  (hbd:∀ x∈S,|f x-α0| ≤ R)
  (hsep:∀ x∈S,∀ y∈S,x≠y->s ≤ |f x-f y|) :
  (S.card:E)<=1+2*R/s:=by
 classical
 by_cases hcard:S.card<=1
 ·
  have:(S.card:E)<=1:=by exact_mod_cast hcard
  linarith [show 0<=2*R/s by positivity]
 ·
  have hf_inj:Set.InjOn f S:=by
   intro x hx y hy heq
   by_contra hne
   have:=hsep x hx y hy hne
   rw [heq,sub_self,abs_zero] at this;linarith
  let img:=S.image f;have himg_card:img.card=S.card:=Finset.card_image_iff.mpr hf_inj;let t:=img.card;let emb:=img.orderEmbOfFin rfl
  have hstep:∀ i:ℕ,(hi:i+1 < t)->s<=emb ⟨i+1,hi⟩-emb ⟨i,by omega⟩:=by
   intro i hi;rcases Finset.mem_image.mp (Finset.orderEmbOfFin_mem img rfl ⟨i,by omega⟩) with ⟨x,hx,hfx⟩;rcases Finset.mem_image.mp (Finset.orderEmbOfFin_mem img rfl ⟨i+1,hi⟩) with ⟨y,hy,hfy⟩
   have hlt:emb ⟨i,by omega⟩ < emb ⟨i+1,hi⟩:=emb.strictMono (by show i < i+1;omega);have hne:x≠y:=fun h=>by subst h;linarith
   have hs_le:=hsep y hy x hx hne.symm;rw [hfx,hfy,abs_of_pos (sub_pos.mpr hlt)] at hs_le;exact hs_le
  let term:ℕ->E:=fun i =>
   if hi:i+1 < t then emb ⟨i+1,hi⟩-emb ⟨i,by omega⟩ else 0
  have htele:∀ k:ℕ,(hk:k<=t-1) → ∑ i∈Finset.range k,term i=emb ⟨k,by omega⟩-emb ⟨0,by omega⟩:=by
   intro k hk;induction k with
   | zero=>simp
   | succ k ih =>
    rw [sum_range_succ,ih (by omega)];have hlt:k+1 < t:=by omega
    simp only [term,hlt,↓reduceDIte];ring
  have hspan:emb ⟨t-1,by omega⟩-emb ⟨0,by omega⟩<=2*R:=by
   rcases Finset.mem_image.mp (Finset.orderEmbOfFin_mem img rfl ⟨0,by omega⟩) with ⟨x0,hx0,hfx0⟩;rcases Finset.mem_image.mp (Finset.orderEmbOfFin_mem img rfl ⟨t-1,by omega⟩) with ⟨x1,hx1,hfx1⟩;have h0:=abs_le.mp (hbd x0 hx0);have h1:=abs_le.mp (hbd x1 hx1)
   linarith
  have hprod:((t-1:ℕ):E)*s<=2*R:=by
   calc
    ((t-1:ℕ):E)*s=∑ _i∈Finset.range (t-1),s:=by simp
    _ <= ∑ i∈Finset.range (t-1),term i:=by
     apply sum_le_sum;intro i hi;have hlt:i+1 < t:=by have:=Finset.mem_range.mp hi;omega
     simp only [term,hlt,↓reduceDIte];exact hstep i hlt
    _ = emb ⟨t-1,by omega⟩-emb ⟨0,by omega⟩:=htele (t-1) le_rfl
    _ <= 2*R:=hspan
  have ht1:((t-1:ℕ):E)<=2*R/s:=(le_div_iff₀ hs).mpr hprod
  have ht_eq:(S.card:E)=((t-1:ℕ):E)+1:=by
   rw [← himg_card];change (t:E)=((t-1:ℕ):E)+1;rw [Nat.cast_sub (by omega:1<=t),Nat.cast_one];ring
  linarith
lemma card_filter_sq_congr_prime_sq_le_two {P p1 p2:ℕ} {a1 A:ℤ}
  (_hP:2<=P) (hp1_ico:p1∈Finset.Ico P (2*P)) (hp1:Nat.Prime p1)
  (hp2:Nat.Prime p2) (h12:p1≠p2) (ha1_ne:a1≠0) (ha1_lt:|a1| < (P:ℤ)^2) :
  ((Finset.Ico P (2*P)).filter (fun p3 =>
   Nat.Prime p3/\p3≠p1/\((p1:ℤ)^2∣a1*(p2:ℤ)^2*(p3:ℤ)^2-A))).card<=2:=by
 let F:=(Finset.Ico P (2*P)).filter (fun p3 =>
  Nat.Prime p3/\p3≠p1/\((p1:ℤ)^2∣a1*(p2:ℤ)^2*(p3:ℤ)^2-A))
 change F.card<=2
 by_contra hgt
 have hge3:3<=F.card:=by omega
 let emb:=F.orderEmbOfFin rfl;let x:=emb ⟨0,by omega⟩;let y:=emb ⟨1,by omega⟩;let z:=emb ⟨2,by omega⟩;have hx_mem:x∈F:=Finset.orderEmbOfFin_mem F rfl _;have hy_mem:y∈F:=Finset.orderEmbOfFin_mem F rfl _;have hz_mem:z∈F:=Finset.orderEmbOfFin_mem F rfl _
 have hxy:x < y:=emb.strictMono (show (⟨0,by omega⟩:Fin F.card) < ⟨1,by omega⟩ by show 0 < 1;omega);have hyz:y < z:=emb.strictMono (show (⟨1,by omega⟩:Fin F.card) < ⟨2,by omega⟩ by show 1 < 2;omega);have hp1_ge:P<=p1:=(Finset.mem_Ico.mp hp1_ico).1
 have hnot_p1sq_a1:¬ ((p1:ℤ)^2∣a1):=by
  intro hdvd;have hle:(p1:ℤ)^2 ≤ |a1|:=Int.le_of_dvd (abs_pos.mpr ha1_ne) (int_dvd_abs hdvd);have hp1sq:(P:ℤ)^2<=(p1:ℤ)^2:=by nlinarith
  linarith
 have hdvd_sum:∀ u v:ℕ,u∈F->v∈F->u < v->(p1:ℤ)∣(u:ℤ)+(v:ℤ):=by
  intro u v hu hv huv;have hu_fl:=mem_filter.mp hu;have hv_fl:=mem_filter.mp hv
  have hsub:(p1:ℤ)^2∣a1*(p2:ℤ)^2*((v:ℤ)^2-(u:ℤ)^2):=by
   have h1:=hv_fl.2.2.2;have h2:=hu_fl.2.2.2;have hdiff:a1*(p2:ℤ)^2*((v:ℤ)^2-(u:ℤ)^2) = (a1*(p2:ℤ)^2*(v:ℤ)^2-A)-(a1*(p2:ℤ)^2*(u:ℤ)^2-A):=by ring
   rw [hdiff];exact dvd_sub h1 h2
  have hcop_p2:IsCoprime ((p1:ℤ)^2) ((p2:ℤ)^2):=by
   have hcopN:Nat.Coprime p1 p2:=(Nat.coprime_primes hp1 hp2).mpr h12;exact ((Nat.isCoprime_iff_coprime.mpr hcopN).pow_left).pow_right
  have hdiv1:(p1:ℤ)^2∣a1*((v:ℤ)^2-(u:ℤ)^2):=by
   have hrew:a1*(p2:ℤ)^2*((v:ℤ)^2-(u:ℤ)^2) = (p2:ℤ)^2*(a1*((v:ℤ)^2-(u:ℤ)^2)):=by ring
   rw [hrew] at hsub;exact hcop_p2.dvd_of_dvd_mul_left hsub
  have hp1_int:Prime (p1:ℤ):=Nat.prime_iff_prime_int.mp hp1
  have hp1_dvd_sq:(p1:ℤ)∣(v:ℤ)^2-(u:ℤ)^2:=by
   by_cases hpa:(p1:ℤ)∣a1
   ·
    rcases hpa with ⟨a1',ha1'⟩
    have hnot_p1_a1':¬ ((p1:ℤ)∣a1'):=by
     intro h;rcases h with ⟨k,rfl⟩;exact hnot_p1sq_a1 ⟨k,by rw [ha1'];ring⟩
    have hd2:(p1:ℤ)∣a1'*((v:ℤ)^2-(u:ℤ)^2):=by
     rcases hdiv1 with ⟨k,hk⟩;refine ⟨k,?_⟩;have hmul:(p1:ℤ)*(a1'*((v:ℤ)^2-(u:ℤ)^2))=(p1:ℤ)*((p1:ℤ)*k):=by rw [ha1'] at hk;linarith
     exact mul_left_cancel₀ (by exact_mod_cast hp1.ne_zero) hmul
    exact (hp1_int.dvd_or_dvd hd2).resolve_left hnot_p1_a1'
   ·
    have h1:(p1:ℤ)∣a1*((v:ℤ)^2-(u:ℤ)^2) :=(dvd_pow_self (p1:ℤ) (by norm_num:2≠0)).trans hdiv1;exact (hp1_int.dvd_or_dvd h1).resolve_left hpa
  have hfac:(v:ℤ)^2-(u:ℤ)^2=((v:ℤ)-(u:ℤ))*((u:ℤ)+(v:ℤ)):=by ring
  rw [hfac] at hp1_dvd_sq;rcases hp1_int.dvd_or_dvd hp1_dvd_sq with hsub_d | hadd_d
  ·
   exfalso
   have hle:(p1:ℤ)<=(v:ℤ)-(u:ℤ):=Int.le_of_dvd (by omega) hsub_d;have hu_ge:P<=u:=(Finset.mem_Ico.mp hu_fl.1).1;have hv_lt:v < 2*P:=(Finset.mem_Ico.mp hv_fl.1).2;omega
  · exact hadd_d
 have h1:(p1:ℤ)∣(x:ℤ)+(y:ℤ):=hdvd_sum x y hx_mem hy_mem hxy;have h2:(p1:ℤ)∣(x:ℤ)+(z:ℤ):=hdvd_sum x z hx_mem hz_mem (hxy.trans hyz)
 have h3:(p1:ℤ)∣(z:ℤ)-(y:ℤ):=by
  have:(z:ℤ)-(y:ℤ)=((x:ℤ)+(z:ℤ))-((x:ℤ)+(y:ℤ)):=by ring
  rw [this];exact dvd_sub h2 h1
 have hle:(p1:ℤ)<=(z:ℤ)-(y:ℤ):=Int.le_of_dvd (by omega) h3;have hy_ge:P<=y:=(Finset.mem_Ico.mp (mem_filter.mp hy_mem).1).1;have hz_lt:z < 2*P:=(Finset.mem_Ico.mp (mem_filter.mp hz_mem).1).2;omega
def IsMinPrimeSqDiv (P p n:ℕ):Prop := p∈Finset.Ico P (2*P)/\Nat.Prime p/\p^2∣n ∧ ∀ q∈Finset.Ico P (2*P),Nat.Prime q->q^2∣n->p<=q
lemma isMinPrimeSqDiv_unique {P p p' n:ℕ} (h1:IsMinPrimeSqDiv P p n) (h2:IsMinPrimeSqDiv P p' n) :
  p=p' :=
 le_antisymm (h1.2.2.2 p' h2.1 h2.2.1 h2.2.2.1) (h2.2.2.2 p h1.1 h1.2.1 h1.2.2.1)
lemma isMinPrimeSqDiv_of_mul_dvd {P p r d:ℕ} (h:IsMinPrimeSqDiv P p (p^2*(d*r))) :
  IsMinPrimeSqDiv P p (p^2*r):=by
 refine ⟨h.1,h.2.1,dvd_mul_right _ _,?_⟩;intro q hq_ico hq_pr hq_dvd;apply h.2.2.2 q hq_ico hq_pr;have hmul:p^2*r∣p^2*(d*r):=⟨d,by ring⟩;exact hq_dvd.trans hmul
def PrimeTriples (P:ℕ):Finset (ℕ × ℕ × ℕ) := ((Finset.Ico P (2*P))×ˢ(Finset.Ico P (2*P))×ˢ(Finset.Ico P (2*P))).filter (fun t =>
  Nat.Prime t.1/\Nat.Prime t.2.1/\Nat.Prime t.2.2 ∧
  t.1≠t.2.1/\t.1≠t.2.2/\t.2.1≠t.2.2)
lemma card_primeTriples_le (P:ℕ):((PrimeTriples P).card:E)<=(P:E)^3:=by
 have h1:(PrimeTriples P).card ≤ ((Finset.Ico P (2*P))×ˢ(Finset.Ico P (2*P))×ˢ(Finset.Ico P (2*P))).card :=Finset.card_filter_le _ _;simp only [Finset.card_product,Nat.card_Ico] at h1;have h2:2*P-P=P:=by omega
 rw [h2] at h1;have hcast:((PrimeTriples P).card:E)<=(P:E)*((P:E)*(P:E)):=by exact_mod_cast h1
 linarith
noncomputable def sextupleFiber (N H P D D':ℕ) (t:ℕ × ℕ × ℕ):Finset (ℕ × ℕ × ℕ):=by
 classical
 let Qmax:=2*N/P^2
 exact ((Finset.Icc 1 Qmax)×ˢ(Finset.Icc 1 Qmax)×ˢ(Finset.Icc 1 Qmax)).filter (fun q =>
  t.1^2*q.1<=2*N/\t.2.1^2*q.2.1<=2*N/\t.2.2^2*q.2.2<=2*N ∧
  |((t.1:ℤ)^2*(q.1:ℤ)-(t.2.2:ℤ)^2*(q.2.2:ℤ))| < (H:ℤ) ∧
  |((t.2.1:ℤ)^2*(q.2.1:ℤ)-(t.2.2:ℤ)^2*(q.2.2:ℤ))| < (H:ℤ) ∧
  |((t.1:ℤ)^2*(q.1:ℤ)-(t.2.1:ℤ)^2*(q.2.1:ℤ))| < (H:ℤ) ∧
  IsMinPrimeSqDiv P t.1 (t.1^2*q.1) ∧
  IsMinPrimeSqDiv P t.2.1 (t.2.1^2*q.2.1) ∧
  IsMinPrimeSqDiv P t.2.2 (t.2.2^2*q.2.2) ∧
  Nat.gcd (Nat.gcd q.1 q.2.1) q.2.2<=D ∧
  Nat.gcd q.1 q.2.1<=D')
noncomputable def sextupleCount (N H P D D':ℕ):ℕ :=∑ t∈PrimeTriples P,(sextupleFiber N H P D D' t).card
def toIntTriple (q:ℕ × ℕ × ℕ):ℤ × ℤ × ℤ:=((q.1:ℤ),(q.2.1:ℤ),(q.2.2:ℤ))
lemma toIntTriple_injective:Function.Injective toIntTriple:=by
 intro a b h;simp only [toIntTriple,Prod.mk.injEq,Nat.cast_inj] at h;rcases a with ⟨a1,a2,a3⟩;rcases b with ⟨b1,b2,b3⟩;simp only [Prod.mk.injEq] at h ⊢;exact h
def FiberRank3 (Q:Finset (ℕ × ℕ × ℕ)):Prop :=∃ w1∈Q,∃ w2∈Q,∃ w3∈Q,det3 (toIntTriple w1) (toIntTriple w2) (toIntTriple w3)≠0
def FiberRank2 (Q:Finset (ℕ × ℕ × ℕ)):Prop := ¬ FiberRank3 Q ∧ ∃ w1∈Q,∃ w2∈Q,
  let u:=toIntTriple w1;let v:=toIntTriple w2
  u.2.1*v.2.2-u.2.2*v.2.1≠0 ∨
  u.2.2*v.1-u.1*v.2.2≠0 ∨
  u.1*v.2.1-u.2.1*v.1≠0
def FiberRank1 (Q:Finset (ℕ × ℕ × ℕ)):Prop :=Q.Nonempty/\¬ FiberRank3 Q/\¬ FiberRank2 Q
section
open Classical
lemma sum_rank3_fibers_le {N H P D D':ℕ} (hN:1<=N) (hH:1<=H) (hP:1<=P) :
  (∑ t∈(PrimeTriples P).filter (fun t=>FiberRank3 (sextupleFiber N H P D D' t)),((sextupleFiber N H P D D' t).card:E)) ≤ 6000*(N:E)*(H:E)^2/(P:E)^3:=by
 have hP_pos:(0:E) < (P:E):=by exact_mod_cast hP
 have hfib:∀ t∈(PrimeTriples P).filter (fun t=>FiberRank3 (sextupleFiber N H P D D' t)),((sextupleFiber N H P D D' t).card:E)<=6000*(N:E)*(H:E)^2/(P:E)^6:=by
  intro t ht;rcases mem_filter.mp ht with ⟨ht_pr,w1,hw1,w2,hw2,w3,hw3,hdet⟩;have ht_fl:=mem_filter.mp ht_pr;have ht_prod:=mem_product.mp ht_fl.1;have ht_prod2:=mem_product.mp ht_prod.2;have hp1_ge:P<=t.1:=(Finset.mem_Ico.mp ht_prod.1).1
  have hp2_ge:P<=t.2.1:=(Finset.mem_Ico.mp ht_prod2.1).1;have hp3_ge:P<=t.2.2:=(Finset.mem_Ico.mp ht_prod2.2).1;let Q:=sextupleFiber N H P D D' t;let S:Finset (ℤ × ℤ × ℤ):=Q.image toIntTriple
  have hcard_eq:(Q.card:E)=(S.card:E):=by exact_mod_cast (Finset.card_image_of_injective Q toIntTriple_injective).symm
  have hS_bd:∀ v∈S,
     |((t.2.2:E)^2)*(v.2.2:E)| ≤ 2*(N:E) ∧
     |((t.2.1:E)^2)*(v.2.1:E)-((t.2.2:E)^2)*(v.2.2:E)| ≤ (H:E) ∧
     |((t.1:E)^2)*(v.1:E)-((t.2.2:E)^2)*(v.2.2:E)| ≤ (H:E):=by
   intro v hv;rcases Finset.mem_image.mp hv with ⟨q,hq,rfl⟩;have hfl:=(mem_filter.mp hq).2;refine ⟨?_,?_,?_⟩
   ·
     dsimp [toIntTriple];rw [abs_of_nonneg (by positivity)];exact_mod_cast hfl.2.2.1
   ·
     dsimp [toIntTriple];have h:|((t.2.1:ℤ)^2*(q.2.1:ℤ)-(t.2.2:ℤ)^2*(q.2.2:ℤ))| ≤ (H:ℤ):=hfl.2.2.2.2.1.le;exact_mod_cast h
   ·
     dsimp [toIntTriple];have h:|((t.1:ℤ)^2*(q.1:ℤ)-(t.2.2:ℤ)^2*(q.2.2:ℤ))| ≤ (H:ℤ):=hfl.2.2.2.1.le;exact_mod_cast h
  have h3:=card_rank3_box_le (p1:=(t.1:E)^2) (p2:=(t.2.1:E)^2) (p3:=(t.2.2:E)^2)
   (A:=2*(N:E)) (B:=(H:E))
   (pow_pos (by exact_mod_cast (show 0 < t.1 by omega)) 2)
   (pow_pos (by exact_mod_cast (show 0 < t.2.1 by omega)) 2)
   (pow_pos (by exact_mod_cast (show 0 < t.2.2 by omega)) 2)
   (by positivity) (by positivity) S hS_bd
   ⟨toIntTriple w1,Finset.mem_image_of_mem _ hw1,toIntTriple w2,Finset.mem_image_of_mem _ hw2,toIntTriple w3,Finset.mem_image_of_mem _ hw3,hdet⟩
  rw [hcard_eq]
  have hden:(P:E)^6<=(t.1:E)^2*(t.2.1:E)^2*(t.2.2:E)^2:=by
   have h1:(P:E)^2<=(t.1:E)^2:=pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp1_ge) 2;have h2:(P:E)^2<=(t.2.1:E)^2:=pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp2_ge) 2;have h3':(P:E)^2<=(t.2.2:E)^2:=pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp3_ge) 2
   have h12:(P:E)^4<=(t.1:E)^2*(t.2.1:E)^2:=by
     calc
      (P:E)^4=(P:E)^2*(P:E)^2:=by ring
      _ <= (t.1:E)^2*(t.2.1:E)^2:=mul_le_mul h1 h2 (by positivity) (by positivity)
   calc
     (P:E)^6=(P:E)^4*(P:E)^2:=by ring
     _ <= (t.1:E)^2*(t.2.1:E)^2*(t.2.2:E)^2:=mul_le_mul h12 h3' (by positivity) (by positivity)
  calc
   (S.card:E)<=3000*(2*(N:E))*(H:E)^2/((t.1:E)^2*(t.2.1:E)^2*(t.2.2:E)^2):=h3
   _ = 6000*(N:E)*(H:E)^2/((t.1:E)^2*(t.2.1:E)^2*(t.2.2:E)^2):=by ring
   _ <= 6000*(N:E)*(H:E)^2/(P:E)^6 :=div_le_div_of_nonneg_left (by positivity) (pow_pos hP_pos 6) hden
 calc
  _ <= ∑ _t∈(PrimeTriples P).filter (fun t=>FiberRank3 (sextupleFiber N H P D D' t)),(6000*(N:E)*(H:E)^2/(P:E)^6):=sum_le_sum hfib
  _ = (((PrimeTriples P).filter (fun t=>FiberRank3 (sextupleFiber N H P D D' t))).card:E) * (6000*(N:E)*(H:E)^2/(P:E)^6):=by simp
  _ <= (P:E)^3*(6000*(N:E)*(H:E)^2/(P:E)^6):=by
   have h1:(((PrimeTriples P).filter (fun t=>FiberRank3 (sextupleFiber N H P D D' t))).card:E) ≤ ((PrimeTriples P).card:E):=by exact_mod_cast Finset.card_filter_le _ _
   exact mul_le_mul_of_nonneg_right (h1.trans (card_primeTriples_le P)) (by positivity)
  _ = 6000*(N:E)*(H:E)^2/(P:E)^3:=by field_simp [hP_pos.ne']
set_option maxHeartbeats 800000 in
lemma rank2_fiber_normal_and_bounds {N H P D D':ℕ} (hN:1<=N) (hH:1<=H) (hP:1<=P)
  {t:ℕ × ℕ × ℕ} (ht:t∈PrimeTriples P)
  (hrk2:FiberRank2 (sextupleFiber N H P D D' t)) :
  ∃ a1 a2 a3:ℤ,Int.gcd (Int.gcd a1 a2:ℤ) a3=1 ∧ (∀ q∈sextupleFiber N H P D D' t,a1*(q.1:ℤ)+a2*(q.2.1:ℤ)+a3*(q.2.2:ℤ)=0) ∧ ((sextupleFiber N H P D D' t).card:E) ≤ 200*(N:E)*(H:E)/((P:E)^4*max |(a1:E)| (max |(a2:E)| |(a3:E)|)) ∧ (let A:ℤ:=a1*(t.2.1:ℤ)^2*(t.2.2:ℤ)^2 + a2*(t.1:ℤ)^2*(t.2.2:ℤ)^2 + a3*(t.1:ℤ)^2*(t.2.1:ℤ)^2
    A≠0->((sextupleFiber N H P D D' t).card:E)<=3200*(H:E)^2 / |(A:E)|):=by
 let Q:=sextupleFiber N H P D D' t;rcases hrk2 with ⟨hno3,w1,hw1,w2,hw2,hcross⟩;let u:=toIntTriple w1;let v:=toIntTriple w2;let c1:ℤ:=u.2.1*v.2.2-u.2.2*v.2.1;let c2:ℤ:=u.2.2*v.1-u.1*v.2.2;let c3:ℤ:=u.1*v.2.1-u.2.1*v.1;have hc_ne:c1≠0\/c2≠0\/c3≠0:=hcross
 let g12:ℕ:=Int.gcd c1 c2;let gN:ℕ:=Int.gcd (g12:ℤ) c3;let g:ℤ:=(gN:ℤ)
 have hg_pos:0 < g:=by
  have:gN≠0:=by
   intro h0;have h3:c3=0:=(Int.gcd_eq_zero_iff.mp h0).2;have h12:(g12:ℤ)=0:=(Int.gcd_eq_zero_iff.mp h0).1;have hg12_0:g12=0:=by omega
   have h1:=(Int.gcd_eq_zero_iff.mp hg12_0).1;have h2:=(Int.gcd_eq_zero_iff.mp hg12_0).2;rcases hc_ne with h | h | h <;> contradiction
  dsimp [g];exact_mod_cast Nat.pos_of_ne_zero this
 have hg_dvd1:g∣c1:=(Int.gcd_dvd_left (g12:ℤ) c3).trans (Int.gcd_dvd_left c1 c2);have hg_dvd2:g∣c2:=(Int.gcd_dvd_left (g12:ℤ) c3).trans (Int.gcd_dvd_right c1 c2);have hg_dvd3:g∣c3:=Int.gcd_dvd_right (g12:ℤ) c3;let a1:ℤ:=c1/g;let a2:ℤ:=c2/g;let a3:ℤ:=c3/g
 have ha1_mul:g*a1=c1:=Int.mul_ediv_cancel' hg_dvd1;have ha2_mul:g*a2=c2:=Int.mul_ediv_cancel' hg_dvd2;have ha3_mul:g*a3=c3:=Int.mul_ediv_cancel' hg_dvd3
 have hprim:Int.gcd (Int.gcd a1 a2:ℤ) a3=1:=by
  set d:=Int.gcd (Int.gcd a1 a2:ℤ) a3
  have hd_pos:0 < d:=by
   apply Nat.pos_of_ne_zero;intro h0;have h3:a3=0:=(Int.gcd_eq_zero_iff.mp h0).2;have h12Z:(Int.gcd a1 a2:ℤ)=0:=(Int.gcd_eq_zero_iff.mp h0).1;have h12N:Int.gcd a1 a2=0:=by exact_mod_cast h12Z
   have h1:a1=0:=(Int.gcd_eq_zero_iff.mp h12N).1;have h2:a2=0:=(Int.gcd_eq_zero_iff.mp h12N).2;rw [h1,mul_zero] at ha1_mul;rw [h2,mul_zero] at ha2_mul;rw [h3,mul_zero] at ha3_mul;rcases hc_ne with h | h | h <;> exact h (by omega)
  have hd_dvd_a1:(d:ℤ)∣a1:=(Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left a1 a2);have hd_dvd_a2:(d:ℤ)∣a2:=(Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right a1 a2);have hd_dvd_a3:(d:ℤ)∣a3:=Int.gcd_dvd_right _ _
  have hgd_dvd_c1:((gN*d:ℕ):ℤ)∣c1:=by push_cast;exact ha1_mul ▸ mul_dvd_mul_left g hd_dvd_a1
  have hgd_dvd_c2:((gN*d:ℕ):ℤ)∣c2:=by push_cast;exact ha2_mul ▸ mul_dvd_mul_left g hd_dvd_a2
  have hgd_dvd_c3:((gN*d:ℕ):ℤ)∣c3:=by push_cast;exact ha3_mul ▸ mul_dvd_mul_left g hd_dvd_a3
  have hgd_dvd_g12:((gN*d:ℕ):ℤ)∣(g12:ℤ):=Int.ofNat_dvd.mpr (Int.dvd_gcd hgd_dvd_c1 hgd_dvd_c2);have hgd_dvd_gN:gN*d∣gN:=Int.dvd_gcd hgd_dvd_g12 hgd_dvd_c3;have hle:gN*d<=gN:=Nat.le_of_dvd (by dsimp [g] at hg_pos;omega) hgd_dvd_gN
  have hgN_pos:0 < gN:=by dsimp [g] at hg_pos;omega
  nlinarith
 have hplane:∀ q∈Q,a1*(q.1:ℤ)+a2*(q.2.1:ℤ)+a3*(q.2.2:ℤ)=0:=by
  intro q hq
  have hdet0:det3 u v (toIntTriple q)=0:=by
   by_contra hne;exact hno3 ⟨w1,hw1,w2,hw2,q,hq,hne⟩
  have hdot:c1*(q.1:ℤ)+c2*(q.2.1:ℤ)+c3*(q.2.2:ℤ)=0:=by dsimp [det3,toIntTriple,c1,c2,c3] at hdet0 ⊢;linarith
  have hmul:g*(a1*(q.1:ℤ)+a2*(q.2.1:ℤ)+a3*(q.2.2:ℤ))=0:=by linear_combination (q.1:ℤ)*ha1_mul+(q.2.1:ℤ)*ha2_mul+(q.2.2:ℤ)*ha3_mul+hdot
  exact (mul_eq_zero.mp hmul).resolve_left hg_pos.ne'
 have ht_fl:=mem_filter.mp ht;have ht_prod:=mem_product.mp ht_fl.1;have ht_prod2:=mem_product.mp ht_prod.2;have hp1_ico:=Finset.mem_Ico.mp ht_prod.1;have hp2_ico:=Finset.mem_Ico.mp ht_prod2.1;have hp3_ico:=Finset.mem_Ico.mp ht_prod2.2
 have hP_pos:(0:E) < (P:E):=by exact_mod_cast hP
 let Ma:E:=max |(a1:E)| (max |(a2:E)| |(a3:E)|)
 have hsym_bound:∀ A_bd:E,0 < A_bd → (∀ q∈Q,((t.1:E)^2*(q.1:E)<=A_bd) ∧ ((t.2.1:E)^2*(q.2.1:E)<=A_bd) ∧ ((t.2.2:E)^2*(q.2.2:E)<=A_bd)) → (Q.card:E)<=100*A_bd*(H:E)/((P:E)^4*Ma):=by
  intro A_bd hAbd hQbd
  have ha_ne:a1≠0\/a2≠0\/a3≠0:=by
   rcases hc_ne with h | h | h
   · left;intro h0;rw [h0,mul_zero] at ha1_mul;exact h ha1_mul.symm
   · right;left;intro h0;rw [h0,mul_zero] at ha2_mul;exact h ha2_mul.symm
   · right;right;intro h0;rw [h0,mul_zero] at ha3_mul;exact h ha3_mul.symm
  have hperm:∀ (p1 p2 p3:ℕ) (b1 b2 b3:ℤ) (perm:ℕ × ℕ × ℕ->ℤ × ℤ × ℤ),P<=p1->P<=p2->P<=p3 → Function.Injective perm → b1≠0->|(b1:E)| = Ma → Int.gcd (Int.gcd b1 b2:ℤ) b3=1 → (∀ q∈Q,b1*(perm q).1+b2*(perm q).2.1+b3*(perm q).2.2=0) → (∀ q∈Q,|((p3:E)^2)*((perm q).2.2:E)| ≤ A_bd ∧
            |((p2:E)^2)*((perm q).2.1:E)-((p3:E)^2)*((perm q).2.2:E)| ≤ (H:E) ∧
            |((p1:E)^2)*((perm q).1:E)-((p3:E)^2)*((perm q).2.2:E)| ≤ (H:E)) →
     (let pu:=perm w1;let pv:=perm w2
      pu.2.1*pv.2.2-pu.2.2*pv.2.1≠0 ∨
      pu.2.2*pv.1-pu.1*pv.2.2≠0 ∨
      pu.1*pv.2.1-pu.2.1*pv.1≠0) →
     (Q.card:E)<=100*A_bd*(H:E)/((P:E)^4*Ma):=by
   intro p1 p2 p3 b1 b2 b3 perm hp1 hp2 hp3 hinj hb1 hMa hpr hpl hbox hli;let S:=Q.image perm;have hcard:(Q.card:E)=(S.card:E):=by exact_mod_cast (Finset.card_image_of_injective Q hinj).symm
   have hres:=card_rank2_plane_le
     (p1:=(p1:E)^2) (p2:=(p2:E)^2) (p3:=(p3:E)^2)
     (A:=A_bd) (B:=(H:E))
     (pow_pos (by exact_mod_cast (show 0 < p1 by omega)) 2)
     (pow_pos (by exact_mod_cast (show 0 < p2 by omega)) 2)
     (pow_pos (by exact_mod_cast (show 0 < p3 by omega)) 2)
     hAbd (by positivity) b1 b2 b3 hb1 hpr S
     (by intro z hz;rcases Finset.mem_image.mp hz with ⟨q,hq,rfl⟩;exact hpl q hq)
     (by intro z hz;rcases Finset.mem_image.mp hz with ⟨q,hq,rfl⟩;exact hbox q hq)
     ⟨perm w1,Finset.mem_image_of_mem _ hw1,perm w2,Finset.mem_image_of_mem _ hw2,hli⟩
   rw [hMa] at hres;rw [hcard]
   have hden:(P:E)^4<=(p2:E)^2*(p3:E)^2:=by
     have h2:(P:E)^2<=(p2:E)^2:=pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp2) 2;have h3:(P:E)^2<=(p3:E)^2:=pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp3) 2
     calc
       (P:E)^4=(P:E)^2*(P:E)^2:=by ring
       _ <= (p2:E)^2*(p3:E)^2:=mul_le_mul h2 h3 (by positivity) (by positivity)
   have hMa_pos:0 < Ma:=by rw [← hMa];exact abs_pos.mpr (by exact_mod_cast hb1)
   have hden2:(P:E)^4*Ma<=(p2:E)^2*(p3:E)^2*Ma :=mul_le_mul_of_nonneg_right hden hMa_pos.le
   calc
     (S.card:E)<=100*A_bd*(H:E)/((p2:E)^2*(p3:E)^2*Ma):=hres
     _ <= 100*A_bd*(H:E)/((P:E)^4*Ma) :=div_le_div_of_nonneg_left (by positivity) (by positivity) hden2
  have hgcd_sym12:Int.gcd (Int.gcd a2 a1:ℤ) a3=1:=by rw [Int.gcd_comm a2 a1];exact hprim
  have hgcd_cyc:Int.gcd (Int.gcd a3 a1:ℤ) a2=1:=by
   set d:=Int.gcd (Int.gcd a3 a1:ℤ) a2;have hd_dvd3:(d:ℤ)∣a3:=(Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_left a3 a1);have hd_dvd1:(d:ℤ)∣a1:=(Int.gcd_dvd_left _ _).trans (Int.gcd_dvd_right a3 a1);have hd_dvd2:(d:ℤ)∣a2:=Int.gcd_dvd_right _ _
   have hd_dvd12:(d:ℤ)∣(Int.gcd a1 a2:ℤ):=Int.ofNat_dvd.mpr (Int.dvd_gcd hd_dvd1 hd_dvd2)
   have hd_dvd_1:d∣1:=by
     have:=Int.dvd_gcd hd_dvd12 hd_dvd3;rwa [hprim] at this
   exact Nat.eq_one_of_dvd_one hd_dvd_1
  have hMa_pos:0 < Ma:=by
   dsimp [Ma];rcases ha_ne with h | h | h
   · exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast h)) (le_max_left _ _)
   · exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast h)) (le_trans (le_max_left _ _) (le_max_right _ _))
   · exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast h)) (le_trans (le_max_right _ _) (le_max_right _ _))
  rcases le_total |(a1:E)| (max |(a2:E)| |(a3:E)|) with h1_le | h1_ge
  ·
   rcases le_total |(a2:E)| |(a3:E)| with h2_le | h2_ge
   ·
     have hMa3:|(a3:E)| = Ma:=by dsimp [Ma];rw [max_eq_right h1_le,max_eq_right h2_le]
     have ha3_ne:a3≠0:=by intro h;rw [h,Int.cast_zero,abs_zero] at hMa3;linarith
     refine hperm t.2.2 t.1 t.2.1 a3 a1 a2 (fun q=>((q.2.2:ℤ),(q.1:ℤ),(q.2.1:ℤ)))
       hp3_ico.1 hp1_ico.1 hp2_ico.1 ?_ ha3_ne hMa3 hgcd_cyc ?_ ?_ ?_
     ·
       intro x y h;simp only [Prod.mk.injEq,Nat.cast_inj] at h;rcases x with ⟨x1,x2,x3⟩;rcases y with ⟨y1,y2,y3⟩;simp only [Prod.mk.injEq] at h ⊢;exact ⟨h.2.1,h.2.2,h.1⟩
     · intro q hq;have:=hplane q hq;linarith
     ·
       intro q hq;have hfl:=(mem_filter.mp hq).2;have hqb:=hQbd q hq;refine ⟨?_,?_,?_⟩
       · dsimp only;rw [abs_of_nonneg (by positivity)];exact hqb.2.1
       ·
        dsimp only;have h:|((t.1:ℤ)^2*(q.1:ℤ)-(t.2.1:ℤ)^2*(q.2.1:ℤ))| ≤ (H:ℤ):=hfl.2.2.2.2.2.1.le;exact_mod_cast h
       ·
        dsimp only;have h:|((t.2.1:ℤ)^2*(q.2.1:ℤ)-(t.2.2:ℤ)^2*(q.2.2:ℤ))| ≤ (H:ℤ):=hfl.2.2.2.2.1.le;rw [abs_sub_comm];exact_mod_cast h
     ·
       dsimp [u,v,toIntTriple] at hcross ⊢;rcases hcross with h | h | h
       · right;left;exact h
       · right;right;exact h
       · left;exact h
   ·
     have hMa2:|(a2:E)| = Ma:=by dsimp [Ma];rw [max_eq_right h1_le,max_eq_left h2_ge]
     have ha2_ne:a2≠0:=by intro h;rw [h,Int.cast_zero,abs_zero] at hMa2;linarith
     refine hperm t.2.1 t.1 t.2.2 a2 a1 a3 (fun q=>((q.2.1:ℤ),(q.1:ℤ),(q.2.2:ℤ)))
       hp2_ico.1 hp1_ico.1 hp3_ico.1 ?_ ha2_ne hMa2 hgcd_sym12 ?_ ?_ ?_
     ·
       intro x y h;simp only [Prod.mk.injEq,Nat.cast_inj] at h;rcases x with ⟨x1,x2,x3⟩;rcases y with ⟨y1,y2,y3⟩;simp only [Prod.mk.injEq] at h ⊢;exact ⟨h.2.1,h.1,h.2.2⟩
     · intro q hq;have:=hplane q hq;linarith
     ·
       intro q hq;have hfl:=(mem_filter.mp hq).2;have hqb:=hQbd q hq;refine ⟨?_,?_,?_⟩
       · dsimp only;rw [abs_of_nonneg (by positivity)];exact hqb.2.2
       ·
        dsimp only;have h:|((t.1:ℤ)^2*(q.1:ℤ)-(t.2.2:ℤ)^2*(q.2.2:ℤ))| ≤ (H:ℤ):=hfl.2.2.2.1.le;exact_mod_cast h
       ·
        dsimp only;have h:|((t.2.1:ℤ)^2*(q.2.1:ℤ)-(t.2.2:ℤ)^2*(q.2.2:ℤ))| ≤ (H:ℤ):=hfl.2.2.2.2.1.le;exact_mod_cast h
     ·
       dsimp [u,v,toIntTriple] at hcross ⊢;rcases hcross with h | h | h
       · right;left;intro h0;exact h (by linarith)
       · left;intro h0;exact h (by linarith)
       · right;right;intro h0;exact h (by linarith)
  ·
   have hMa1:|(a1:E)| = Ma:=by dsimp [Ma];rw [max_eq_left h1_ge]
   have ha1_ne:a1≠0:=by intro h;rw [h,Int.cast_zero,abs_zero] at hMa1;linarith
   refine hperm t.1 t.2.1 t.2.2 a1 a2 a3 toIntTriple
     hp1_ico.1 hp2_ico.1 hp3_ico.1 toIntTriple_injective ha1_ne hMa1 hprim hplane ?_ hcross
   intro q hq;have hfl:=(mem_filter.mp hq).2;have hqb:=hQbd q hq;refine ⟨?_,?_,?_⟩
   · dsimp [toIntTriple];rw [abs_of_nonneg (by positivity)];exact hqb.2.2
   ·
     dsimp [toIntTriple];have h:|((t.2.1:ℤ)^2*(q.2.1:ℤ)-(t.2.2:ℤ)^2*(q.2.2:ℤ))| ≤ (H:ℤ):=hfl.2.2.2.2.1.le;exact_mod_cast h
   ·
     dsimp [toIntTriple];have h:|((t.1:ℤ)^2*(q.1:ℤ)-(t.2.2:ℤ)^2*(q.2.2:ℤ))| ≤ (H:ℤ):=hfl.2.2.2.1.le;exact_mod_cast h
 have hbd1:(Q.card:E)<=200*(N:E)*(H:E)/((P:E)^4*Ma):=by
  have h:=hsym_bound (2*(N:E)) (by positivity) (by
   intro q hq;have hfl:=(mem_filter.mp hq).2
   exact ⟨by exact_mod_cast hfl.1,by exact_mod_cast hfl.2.1,by exact_mod_cast hfl.2.2.1⟩)
  have hrew:100*(2*(N:E))*(H:E)/((P:E)^4*Ma) = 200*(N:E)*(H:E)/((P:E)^4*Ma):=by ring
  linarith
 refine ⟨a1,a2,a3,hprim,hplane,hbd1,?_⟩;dsimp only;intro hAne;set A:ℤ:=a1*(t.2.1:ℤ)^2*(t.2.2:ℤ)^2 + a2*(t.1:ℤ)^2*(t.2.2:ℤ)^2 + a3*(t.1:ℤ)^2*(t.2.1:ℤ)^2;have hAR_pos:0 < |(A:E)|:=abs_pos.mpr (by exact_mod_cast hAne)
 have hMa_pos:0 < Ma:=by
  dsimp [Ma]
  have ha_ne:a1≠0\/a2≠0\/a3≠0:=by
   by_contra hall;push Not at hall
   have h0:A=0:=by dsimp [A];rw [hall.1,hall.2.1,hall.2.2];ring
   exact hAne h0
  rcases ha_ne with h | h | h
  · exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast h)) (le_max_left _ _)
  · exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast h)) (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast h)) (le_trans (le_max_right _ _) (le_max_right _ _))
 have ha1_le:|(a1:E)| ≤ Ma:=le_max_left _ _;have ha2_le:|(a2:E)| ≤ Ma:=le_trans (le_max_left _ _) (le_max_right _ _);have ha3_le:|(a3:E)| ≤ Ma:=le_trans (le_max_right _ _) (le_max_right _ _)
 have hp1_sq:(t.1:E)^2<=4*(P:E)^2:=by
  have:(t.1:E)<=2*(P:E):=by exact_mod_cast hp1_ico.2.le
  nlinarith
 have hp2_sq:(t.2.1:E)^2<=4*(P:E)^2:=by
  have:(t.2.1:E)<=2*(P:E):=by exact_mod_cast hp2_ico.2.le
  nlinarith
 have hp3_sq:(t.2.2:E)^2<=4*(P:E)^2:=by
  have:(t.2.2:E)<=2*(P:E):=by exact_mod_cast hp3_ico.2.le
  nlinarith
 have hQ_Abd:∀ q∈Q,((t.1:E)^2*(q.1:E)<=32*(P:E)^4*Ma*(H:E) / |(A:E)|) ∧ ((t.2.1:E)^2*(q.2.1:E)<=32*(P:E)^4*Ma*(H:E) / |(A:E)|) ∧ ((t.2.2:E)^2*(q.2.2:E)<=32*(P:E)^4*Ma*(H:E) / |(A:E)|):=by
  intro q hq;have hfl:=(mem_filter.mp hq).2;have hplR:(a1:E)*(q.1:E)+(a2:E)*(q.2.1:E)+(a3:E)*(q.2.2:E)=0:=by exact_mod_cast hplane q hq
  have hd13:|(t.1:E)^2*(q.1:E)-(t.2.2:E)^2*(q.2.2:E)| ≤ (H:E):=by exact_mod_cast hfl.2.2.2.1.le
  have hd23:|(t.2.1:E)^2*(q.2.1:E)-(t.2.2:E)^2*(q.2.2:E)| ≤ (H:E):=by exact_mod_cast hfl.2.2.2.2.1.le
  have hd12:|(t.1:E)^2*(q.1:E)-(t.2.1:E)^2*(q.2.1:E)| ≤ (H:E):=by exact_mod_cast hfl.2.2.2.2.2.1.le
  have hA_cast:(A:E)=(a1:E)*(t.2.1:E)^2*(t.2.2:E)^2 + (a2:E)*(t.1:E)^2*(t.2.2:E)^2+(a3:E)*(t.1:E)^2*(t.2.1:E)^2:=by dsimp [A];push_cast;ring
  have hstep_coord:∀ (p_k q_k:E),0<=q_k->p_k^2<=4*(P:E)^2 →
     |(A:E)*q_k| ≤ 8*(P:E)^2*Ma*(H:E) →
     p_k^2*q_k<=32*(P:E)^4*Ma*(H:E) / |(A:E)|:=by
   intro pk qk hqk hpk hAq;rw [abs_mul,abs_of_nonneg hqk] at hAq;rw [le_div_iff₀ hAR_pos]
   calc
     pk^2*qk * |(A:E)| = pk^2*(|(A:E)| * qk):=by ring
     _ <= (4*(P:E)^2)*(8*(P:E)^2*Ma*(H:E)) :=mul_le_mul hpk hAq (by positivity) (by positivity)
     _ = 32*(P:E)^4*Ma*(H:E):=by ring
  refine ⟨hstep_coord (t.1:E) (q.1:E) (Nat.cast_nonneg _) hp1_sq ?_,hstep_coord (t.2.1:E) (q.2.1:E) (Nat.cast_nonneg _) hp2_sq ?_,hstep_coord (t.2.2:E) (q.2.2:E) (Nat.cast_nonneg _) hp3_sq ?_⟩
  ·
   have hid:(A:E)*(q.1:E) = (a2:E)*(t.2.2:E)^2*((t.1:E)^2*(q.1:E)-(t.2.1:E)^2*(q.2.1:E)) + (a3:E)*(t.2.1:E)^2*((t.1:E)^2*(q.1:E)-(t.2.2:E)^2*(q.2.2:E)):=by rw [hA_cast];linear_combination (t.2.1:E)^2*(t.2.2:E)^2*hplR
   rw [hid]
   calc
     _ <= |(a2:E)*(t.2.2:E)^2*((t.1:E)^2*(q.1:E)-(t.2.1:E)^2*(q.2.1:E))| +
        |(a3:E)*(t.2.1:E)^2*((t.1:E)^2*(q.1:E)-(t.2.2:E)^2*(q.2.2:E))|:=abs_add_le _ _
     _ = |(a2:E)| * (t.2.2:E)^2 * |(t.1:E)^2*(q.1:E)-(t.2.1:E)^2*(q.2.1:E)| +
        |(a3:E)| * (t.2.1:E)^2 * |(t.1:E)^2*(q.1:E)-(t.2.2:E)^2*(q.2.2:E)|:=by
       rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg (t.2.2:E)),abs_of_nonneg (sq_nonneg (t.2.1:E))]
     _ <= Ma*(4*(P:E)^2)*(H:E)+Ma*(4*(P:E)^2)*(H:E):=by gcongr
     _ = 8*(P:E)^2*Ma*(H:E):=by ring
  ·
   have hid:(A:E)*(q.2.1:E) = (a1:E)*(t.2.2:E)^2*((t.2.1:E)^2*(q.2.1:E)-(t.1:E)^2*(q.1:E)) + (a3:E)*(t.1:E)^2*((t.2.1:E)^2*(q.2.1:E)-(t.2.2:E)^2*(q.2.2:E)):=by rw [hA_cast];linear_combination (t.1:E)^2*(t.2.2:E)^2*hplR
   rw [hid]
   calc
     _ <= |(a1:E)*(t.2.2:E)^2*((t.2.1:E)^2*(q.2.1:E)-(t.1:E)^2*(q.1:E))| +
        |(a3:E)*(t.1:E)^2*((t.2.1:E)^2*(q.2.1:E)-(t.2.2:E)^2*(q.2.2:E))|:=abs_add_le _ _
     _ = |(a1:E)| * (t.2.2:E)^2 * |(t.1:E)^2*(q.1:E)-(t.2.1:E)^2*(q.2.1:E)| +
        |(a3:E)| * (t.1:E)^2 * |(t.2.1:E)^2*(q.2.1:E)-(t.2.2:E)^2*(q.2.2:E)|:=by
       rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg (t.2.2:E)),abs_of_nonneg (sq_nonneg (t.1:E)),abs_sub_comm ((t.2.1:E)^2*(q.2.1:E)) ((t.1:E)^2*(q.1:E))]
     _ <= Ma*(4*(P:E)^2)*(H:E)+Ma*(4*(P:E)^2)*(H:E):=by gcongr
     _ = 8*(P:E)^2*Ma*(H:E):=by ring
  ·
   have hid:(A:E)*(q.2.2:E) = (a1:E)*(t.2.1:E)^2*((t.2.2:E)^2*(q.2.2:E)-(t.1:E)^2*(q.1:E)) + (a2:E)*(t.1:E)^2*((t.2.2:E)^2*(q.2.2:E)-(t.2.1:E)^2*(q.2.1:E)):=by rw [hA_cast];linear_combination (t.1:E)^2*(t.2.1:E)^2*hplR
   rw [hid]
   calc
     _ <= |(a1:E)*(t.2.1:E)^2*((t.2.2:E)^2*(q.2.2:E)-(t.1:E)^2*(q.1:E))| +
        |(a2:E)*(t.1:E)^2*((t.2.2:E)^2*(q.2.2:E)-(t.2.1:E)^2*(q.2.1:E))|:=abs_add_le _ _
     _ = |(a1:E)| * (t.2.1:E)^2 * |(t.1:E)^2*(q.1:E)-(t.2.2:E)^2*(q.2.2:E)| +
        |(a2:E)| * (t.1:E)^2 * |(t.2.1:E)^2*(q.2.1:E)-(t.2.2:E)^2*(q.2.2:E)|:=by
       rw [abs_mul,abs_mul,abs_mul,abs_mul,abs_of_nonneg (sq_nonneg (t.2.1:E)),abs_of_nonneg (sq_nonneg (t.1:E)),abs_sub_comm ((t.2.2:E)^2*(q.2.2:E)) ((t.1:E)^2*(q.1:E)),abs_sub_comm ((t.2.2:E)^2*(q.2.2:E)) ((t.2.1:E)^2*(q.2.1:E))]
     _ <= Ma*(4*(P:E)^2)*(H:E)+Ma*(4*(P:E)^2)*(H:E):=by gcongr
     _ = 8*(P:E)^2*Ma*(H:E):=by ring
 have hbd2:=hsym_bound (32*(P:E)^4*Ma*(H:E) / |(A:E)|) (by positivity) hQ_Abd;have hsimp:100*(32*(P:E)^4*Ma*(H:E) / |(A:E)|)*(H:E)/((P:E)^4*Ma) = 3200*(H:E)^2 / |(A:E)|:=by field_simp [hP_pos.ne',hMa_pos.ne',hAR_pos.ne'];ring
 rw [hsimp] at hbd2;exact hbd2
set_option maxHeartbeats 800000 in
lemma sum_rank2_fibers_le {N H P D D':ℕ} (hN:1<=N) (hH:1<=H) (hP:4<=P) (hHP:H<=4*P) :
  (∑ t∈(PrimeTriples P).filter (fun t=>FiberRank2 (sextupleFiber N H P D D' t)),((sextupleFiber N H P D D' t).card:E)) ≤ 200*(N:E)*(H:E)/(P:E)^3 + 200000*(H:E)^3 + min (10^7*(N:E)*(H:E)/(P:E)^(3/2:E))
      (4*10^4*(N:E)^(1/2:E)*(H:E)^(3/2:E)*(P:E)^(1/2:E)):=by
 classical
 let R2:=(PrimeTriples P).filter (fun t=>FiberRank2 (sextupleFiber N H P D D' t));have hP_pos:(0:E) < (P:E):=by exact_mod_cast (show 0 < P by omega)
 have hN_pos:(0:E) < (N:E):=by exact_mod_cast hN
 have hH_pos:(0:E) < (H:E):=by exact_mod_cast hH
 have hex:∀ t∈R2,∃ a:ℤ × ℤ × ℤ,Int.gcd (Int.gcd a.1 a.2.1:ℤ) a.2.2=1 ∧ (∀ q∈sextupleFiber N H P D D' t,a.1*(q.1:ℤ)+a.2.1*(q.2.1:ℤ)+a.2.2*(q.2.2:ℤ)=0) ∧ ((sextupleFiber N H P D D' t).card:E) ≤ 200*(N:E)*(H:E)/((P:E)^4*max |(a.1:E)| (max |(a.2.1:E)| |(a.2.2:E)|)) ∧ (let A:ℤ:=a.1*(t.2.1:ℤ)^2*(t.2.2:ℤ)^2 + a.2.1*(t.1:ℤ)^2*(t.2.2:ℤ)^2 + a.2.2*(t.1:ℤ)^2*(t.2.1:ℤ)^2
    A≠0->((sextupleFiber N H P D D' t).card:E)<=3200*(H:E)^2 / |(A:E)|):=by
  intro t ht;rcases mem_filter.mp ht with ⟨ht_pr,hrk2⟩;obtain ⟨a1,a2,a3,h1,h2,h3,h4⟩:=rank2_fiber_normal_and_bounds hN hH (by omega) ht_pr hrk2;exact ⟨(a1,a2,a3),h1,h2,h3,h4⟩
 let normOf:(ℕ × ℕ × ℕ)->ℤ × ℤ × ℤ:=fun t=>if h:t∈R2 then Classical.choose (hex t h) else (0,0,0)
 have hnorm_spec:∀ t∈R2,
   let a:=normOf t
   Int.gcd (Int.gcd a.1 a.2.1:ℤ) a.2.2=1 ∧
   (∀ q∈sextupleFiber N H P D D' t,a.1*(q.1:ℤ)+a.2.1*(q.2.1:ℤ)+a.2.2*(q.2.2:ℤ)=0) ∧
   ((sextupleFiber N H P D D' t).card:E) ≤ 200*(N:E)*(H:E)/((P:E)^4*max |(a.1:E)| (max |(a.2.1:E)| |(a.2.2:E)|)) ∧
   (let A:ℤ:=a.1*(t.2.1:ℤ)^2*(t.2.2:ℤ)^2 + a.2.1*(t.1:ℤ)^2*(t.2.2:ℤ)^2 + a.2.2*(t.1:ℤ)^2*(t.2.1:ℤ)^2
    A≠0->((sextupleFiber N H P D D' t).card:E)<=3200*(H:E)^2 / |(A:E)|):=by
  intro t ht;simp only [normOf,ht,↓reduceDIte];exact Classical.choose_spec (hex t ht)
 let A_of:(ℕ × ℕ × ℕ)->ℤ:=fun t =>
  let a:=normOf t
  a.1*(t.2.1:ℤ)^2*(t.2.2:ℤ)^2 +
  a.2.1*(t.1:ℤ)^2*(t.2.2:ℤ)^2 +
  a.2.2*(t.1:ℤ)^2*(t.2.1:ℤ)^2
 let M_of:(ℕ × ℕ × ℕ)->ℤ:=fun t =>
  let a:=normOf t
  max |a.1| (max |a.2.1| |a.2.2|)
 let R2_big:=R2.filter (fun t=>(P:ℤ)^2<=M_of t);let R2_small:=R2.filter (fun t=>¬ ((P:ℤ)^2<=M_of t));let R2_zero:=R2_small.filter (fun t=>(normOf t).1*(normOf t).2.1*(normOf t).2.2=0)
 let R2_main:=R2_small.filter (fun t=>(normOf t).1*(normOf t).2.1*(normOf t).2.2≠0)
 have hsplit:∑ t∈R2,((sextupleFiber N H P D D' t).card:E) = (∑ t∈R2_big,((sextupleFiber N H P D D' t).card:E)) + (∑ t∈R2_zero,((sextupleFiber N H P D D' t).card:E)) + (∑ t∈R2_main,((sextupleFiber N H P D D' t).card:E)):=by
  rw [← Finset.sum_filter_add_sum_filter_not R2 (fun t=>(P:ℤ)^2<=M_of t)];rw [← Finset.sum_filter_add_sum_filter_not R2_small (fun t=>(normOf t).1*(normOf t).2.1*(normOf t).2.2=0)];ring
 have hA_ne_of_small:∀ t∈R2_small,A_of t≠0:=by
  intro t ht hA0;rcases mem_filter.mp ht with ⟨htR2,hMlt⟩
  push Not at hMlt
  have ht_pr:=(mem_filter.mp htR2).1;have ht_fl:=mem_filter.mp ht_pr;have ht_prod:=mem_product.mp ht_fl.1;have ht_prod2:=mem_product.mp ht_prod.2;have hsp:=hnorm_spec t htR2;set a:=normOf t
  have ha_ne:a.1≠0\/a.2.1≠0\/a.2.2≠0:=by
   by_contra hall;push Not at hall
   have:=hsp.1;rw [hall.1,hall.2.1,hall.2.2] at this;simp at this
  have hdvd_i:∀ (pi pj pk:ℕ) (ai aj ak:ℤ),Nat.Prime pi->Nat.Prime pj->Nat.Prime pk->pi≠pj->pi≠pk → ai*(pj:ℤ)^2*(pk:ℤ)^2+aj*(pi:ℤ)^2*(pk:ℤ)^2+ak*(pi:ℤ)^2*(pj:ℤ)^2=0 → (pi:ℤ)^2∣ai:=by
   intro pi pj pk ai aj ak hpi hpj hpk hij hik hsum0;have h1:(pi:ℤ)^2∣ai*((pj:ℤ)^2*(pk:ℤ)^2) :=⟨-(aj*(pk:ℤ)^2+ak*(pj:ℤ)^2),by linarith⟩
   have hcopj:IsCoprime ((pi:ℤ)^2) ((pj:ℤ)^2) :=((Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hpi hpj).mpr hij)).pow_left).pow_right
   have hcopk:IsCoprime ((pi:ℤ)^2) ((pk:ℤ)^2) :=((Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hpi hpk).mpr hik)).pow_left).pow_right;exact (hcopj.mul_right hcopk).dvd_of_dvd_mul_right h1
  rcases ha_ne with h1 | h2 | h3
  ·
   have hd:=hdvd_i t.1 t.2.1 t.2.2 a.1 a.2.1 a.2.2 ht_fl.2.1 ht_fl.2.2.1 ht_fl.2.2.2.1
     ht_fl.2.2.2.2.1 ht_fl.2.2.2.2.2.1 hA0
   have hle:(t.1:ℤ)^2 ≤ |a.1|:=Int.le_of_dvd (abs_pos.mpr h1) (int_dvd_abs hd);have hp1:P<=t.1:=(Finset.mem_Ico.mp ht_prod.1).1;have hPsq:(P:ℤ)^2<=(t.1:ℤ)^2:=by nlinarith
   have hM:|a.1| ≤ M_of t:=le_max_left _ _;omega
  ·
   have hd:=hdvd_i t.2.1 t.1 t.2.2 a.2.1 a.1 a.2.2 ht_fl.2.2.1 ht_fl.2.1 ht_fl.2.2.2.1
     ht_fl.2.2.2.2.1.symm ht_fl.2.2.2.2.2.2 (by dsimp [A_of] at hA0;linarith)
   have hle:(t.2.1:ℤ)^2 ≤ |a.2.1|:=Int.le_of_dvd (abs_pos.mpr h2) (int_dvd_abs hd);have hp2:P<=t.2.1:=(Finset.mem_Ico.mp ht_prod2.1).1;have hPsq:(P:ℤ)^2<=(t.2.1:ℤ)^2:=by nlinarith
   have hM:|a.2.1| ≤ M_of t:=le_trans (le_max_left _ _) (le_max_right _ _);omega
  ·
   have hd:=hdvd_i t.2.2 t.1 t.2.1 a.2.2 a.1 a.2.1 ht_fl.2.2.2.1 ht_fl.2.1 ht_fl.2.2.1
     ht_fl.2.2.2.2.2.1.symm ht_fl.2.2.2.2.2.2.symm (by dsimp [A_of] at hA0;linarith)
   have hle:(t.2.2:ℤ)^2 ≤ |a.2.2|:=Int.le_of_dvd (abs_pos.mpr h3) (int_dvd_abs hd);have hp3:P<=t.2.2:=(Finset.mem_Ico.mp ht_prod2.2).1;have hPsq:(P:ℤ)^2<=(t.2.2:ℤ)^2:=by nlinarith
   have hM:|a.2.2| ≤ M_of t:=le_trans (le_max_right _ _) (le_max_right _ _);omega
 have hbig:∑ t∈R2_big,((sextupleFiber N H P D D' t).card:E) ≤ 200*(N:E)*(H:E)/(P:E)^3:=by
  have hterm:∀ t∈R2_big,((sextupleFiber N H P D D' t).card:E) ≤ 200*(N:E)*(H:E)/(P:E)^6:=by
   intro t ht;rcases mem_filter.mp ht with ⟨htR2,hMge⟩;have hsp:=hnorm_spec t htR2
   have hMR:(P:E)^2<=max |((normOf t).1:E)| (max |((normOf t).2.1:E)| |((normOf t).2.2:E)|):=by
     have h1:(P:E)^2<=(M_of t:E):=by exact_mod_cast hMge
     have h2:(M_of t:E)=max |((normOf t).1:E)| (max |((normOf t).2.1:E)| |((normOf t).2.2:E)|):=by dsimp [M_of];push_cast;rfl
     linarith
   have hden:(P:E)^6<=(P:E)^4*max |((normOf t).1:E)| (max |((normOf t).2.1:E)| |((normOf t).2.2:E)|):=by
     calc
      (P:E)^6=(P:E)^4*(P:E)^2:=by ring
      _ <= _:=mul_le_mul_of_nonneg_left hMR (by positivity)
   exact hsp.2.2.1.trans (div_le_div_of_nonneg_left (by positivity) (pow_pos hP_pos 6) hden)
  calc
   _ <= ∑ _t∈R2_big,(200*(N:E)*(H:E)/(P:E)^6):=sum_le_sum hterm
   _ = (R2_big.card:E)*(200*(N:E)*(H:E)/(P:E)^6):=by simp
   _ <= (P:E)^3*(200*(N:E)*(H:E)/(P:E)^6):=by
     have h1:(R2_big.card:E)<=((PrimeTriples P).card:E):=by exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)
     exact mul_le_mul_of_nonneg_right (h1.trans (card_primeTriples_le P)) (by positivity)
   _ = 200*(N:E)*(H:E)/(P:E)^3:=by field_simp [hP_pos.ne']
 have hzero:∑ t∈R2_zero,((sextupleFiber N H P D D' t).card:E)<=200000*(H:E)^3:=by
  by_cases hne:R2_zero.Nonempty
  ·
   have hterm:∀ t∈R2_zero,((sextupleFiber N H P D D' t).card:E)<=3200*(H:E)^2/(P:E)^2:=by
     intro t ht;rcases mem_filter.mp ht with ⟨ht_sm,hprod0⟩;have htR2:t∈R2:=(mem_filter.mp ht_sm).1;have hAne:A_of t≠0:=hA_ne_of_small t ht_sm;have hsp:=hnorm_spec t htR2;have ht_prod:=mem_product.mp (mem_filter.mp (mem_filter.mp htR2).1).1
     have ht_prod2:=mem_product.mp ht_prod.2
     have hA_ge:(P:E)^2 ≤ |(A_of t:E)|:=by
      rcases mul_eq_zero.mp hprod0 with h12 | h3
      ·
       rcases mul_eq_zero.mp h12 with h1 | h2
       ·
        have hd:(t.1:ℤ)^2∣A_of t :=⟨(normOf t).2.1*(t.2.2:ℤ)^2+(normOf t).2.2*(t.2.1:ℤ)^2,by dsimp [A_of];rw [h1];ring⟩;have hle:(t.1:ℤ)^2 ≤ |A_of t|:=Int.le_of_dvd (abs_pos.mpr hAne) (int_dvd_abs hd);have hp:P<=t.1:=(Finset.mem_Ico.mp ht_prod.1).1
        have:(P:ℤ)^2 ≤ |A_of t|:=by nlinarith
        exact_mod_cast this
       ·
        have hd:(t.2.1:ℤ)^2∣A_of t :=⟨(normOf t).1*(t.2.2:ℤ)^2+(normOf t).2.2*(t.1:ℤ)^2,by dsimp [A_of];rw [h2];ring⟩;have hle:(t.2.1:ℤ)^2 ≤ |A_of t|:=Int.le_of_dvd (abs_pos.mpr hAne) (int_dvd_abs hd);have hp:P<=t.2.1:=(Finset.mem_Ico.mp ht_prod2.1).1
        have:(P:ℤ)^2 ≤ |A_of t|:=by nlinarith
        exact_mod_cast this
      ·
       have hd:(t.2.2:ℤ)^2∣A_of t :=⟨(normOf t).1*(t.2.1:ℤ)^2+(normOf t).2.1*(t.1:ℤ)^2,by dsimp [A_of];rw [h3];ring⟩;have hle:(t.2.2:ℤ)^2 ≤ |A_of t|:=Int.le_of_dvd (abs_pos.mpr hAne) (int_dvd_abs hd);have hp:P<=t.2.2:=(Finset.mem_Ico.mp ht_prod2.2).1
       have:(P:ℤ)^2 ≤ |A_of t|:=by nlinarith
       exact_mod_cast this
     exact (hsp.2.2.2 hAne).trans (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hP_pos) hA_ge)
   have hP_le:(P:E)<=60*(H:E):=by
     rcases hne with ⟨t0,ht0⟩;have h1:=hterm t0 ht0;have hrk2:=(mem_filter.mp (mem_filter.mp (mem_filter.mp ht0).1).1).2;rcases hrk2 with ⟨_,w1,hw1,_⟩;have hge1:(1:E)<=((sextupleFiber N H P D D' t0).card:E):=by exact_mod_cast Finset.card_pos.mpr ⟨w1,hw1⟩
     have hsq:(P:E)^2<=3200*(H:E)^2:=by
      have:=(le_div_iff₀ (sq_pos_of_pos hP_pos)).mp (hge1.trans h1);linarith
     nlinarith [sq_nonneg ((P:E)-60*(H:E))]
   calc
     _ <= ∑ _t∈R2_zero,(3200*(H:E)^2/(P:E)^2):=sum_le_sum hterm
     _ = (R2_zero.card:E)*(3200*(H:E)^2/(P:E)^2):=by simp
     _ <= (P:E)^3*(3200*(H:E)^2/(P:E)^2):=by
      have h1:(R2_zero.card:E)<=((PrimeTriples P).card:E):=by exact_mod_cast ((Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)).trans (Finset.card_filter_le _ _)
      exact mul_le_mul_of_nonneg_right (h1.trans (card_primeTriples_le P)) (by positivity)
     _ = 3200*(H:E)^2*(P:E):=by field_simp [hP_pos.ne']
     _ <= 3200*(H:E)^2*(60*(H:E)):=mul_le_mul_of_nonneg_left hP_le (by positivity)
     _ <= 200000*(H:E)^3:=by nlinarith [pow_pos hH_pos 3]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty];positivity
 let Kmax:ℕ:=3200*H^2+1;let B_log:ℕ:=Nat.log 2 Kmax+2
 let layer:ℕ->Finset (ℕ × ℕ × ℕ):=fun k =>
  R2_main.filter (fun t=>2^k<=(sextupleFiber N H P D D' t).card ∧ (sextupleFiber N H P D D' t).card < 2^(k+1))
 have hmain_layers:∑ t∈R2_main,((sextupleFiber N H P D D' t).card:E) ≤ ∑ k∈Finset.range B_log,(2*(2:E)^k*((layer k).card:E)):=by
  have hcov:R2_main=(Finset.range B_log).biUnion layer:=by
   ext t;simp only [Finset.mem_biUnion,Finset.mem_range,layer,mem_filter];constructor
   ·
     intro ht;have hrk2:=(mem_filter.mp (mem_filter.mp (mem_filter.mp ht).1).1).2;rcases hrk2 with ⟨_,w1,hw1,_⟩;have hpos:1<=(sextupleFiber N H P D D' t).card:=Finset.card_pos.mpr ⟨w1,hw1⟩;have hA_ne:A_of t≠0:=hA_ne_of_small t (mem_filter.mp ht).1
     have hA_ge1:(1:E) ≤ |(A_of t:E)|:=by exact_mod_cast Int.one_le_abs hA_ne
     have hsp:=hnorm_spec t (mem_filter.mp (mem_filter.mp ht).1).1;have hcard_le:((sextupleFiber N H P D D' t).card:E)<=3200*(H:E)^2 :=(hsp.2.2.2 hA_ne).trans (div_le_self (by positivity) hA_ge1)
     have hcard_nat:(sextupleFiber N H P D D' t).card<=Kmax:=by
      have:(sextupleFiber N H P D D' t).card<=3200*H^2:=by exact_mod_cast hcard_le
      dsimp [Kmax];omega
     let k:=Nat.log 2 (sextupleFiber N H P D D' t).card;refine ⟨k,?_,ht,Nat.pow_log_le_self 2 (by omega),Nat.lt_pow_succ_log_self (by norm_num) _⟩
     have:=Nat.log_mono_right (b:=2) hcard_nat
     dsimp [B_log];omega
   · rintro ⟨_,_,ht,_,_⟩;exact ht
  have hdisj:Set.PairwiseDisjoint (↑(Finset.range B_log):Set ℕ) layer:=by
   intro k1 _ k2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro t ht1 ht2;have h1:=(mem_filter.mp ht1).2;have h2:=(mem_filter.mp ht2).2;rcases lt_or_gt_of_ne hne with hlt | hgt
   ·
     have:2^(k1+1)<=2^k2:=Nat.pow_le_pow_right (by norm_num) (by omega)
     omega
   ·
     have:2^(k2+1)<=2^k1:=Nat.pow_le_pow_right (by norm_num) (by omega)
     omega
  rw [hcov,Finset.sum_biUnion hdisj];apply sum_le_sum;intro k _
  calc
   ∑ t∈layer k,((sextupleFiber N H P D D' t).card:E)
      ≤ ∑ _t∈layer k,(2*(2:E)^k):=by
     apply sum_le_sum;intro t ht;have hlt:(sextupleFiber N H P D D' t).card<=2^(k+1):=(mem_filter.mp ht).2.2.le
     have:((sextupleFiber N H P D D' t).card:E)<=(2:E)^(k+1):=by exact_mod_cast hlt
     rw [pow_succ'] at this;linarith
   _ = 2*(2:E)^k*((layer k).card:E):=by simp;ring
 have hlayer_triv:∀ k,((layer k).card:E)<=(P:E)^3:=fun k =>
  (by exact_mod_cast (((Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)).trans
   (Finset.card_filter_le _ _)).trans (Finset.card_filter_le _ _):((layer k).card:E)<=((PrimeTriples P).card:E)).trans
   (card_primeTriples_le P)
 have hlayer_MA:∀ k,∀ t∈layer k,(M_of t:E)<=200*(N:E)*(H:E)/((P:E)^4*(2:E)^k) ∧
   |(A_of t:E)| ≤ 3200*(H:E)^2/(2:E)^k:=by
  intro k t ht;rcases mem_filter.mp ht with ⟨ht_m,hge,_⟩;have ht_sm:t∈R2_small:=(mem_filter.mp ht_m).1;have htR2:t∈R2:=(mem_filter.mp ht_sm).1;have hsp:=hnorm_spec t htR2;have hK_le:(2:E)^k<=((sextupleFiber N H P D D' t).card:E):=by exact_mod_cast hge
  have hAne:A_of t≠0:=hA_ne_of_small t ht_sm;have hAR_pos:0 < |(A_of t:E)|:=abs_pos.mpr (by exact_mod_cast hAne);have hMR_eq:(M_of t:E)=max |((normOf t).1:E)| (max |((normOf t).2.1:E)| |((normOf t).2.2:E)|):=by dsimp [M_of];push_cast;rfl
  have hMR_pos:0 < (M_of t:E):=by
   have h1:(normOf t).1≠0:=by
     have:=(mem_filter.mp ht_m).2
     intro h0;exact this (by rw [h0];simp)
   rw [hMR_eq];exact lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast h1)) (le_max_left _ _)
  refine ⟨?_,?_⟩
  ·
   have h1:=hK_le.trans hsp.2.2.1;rw [← hMR_eq,le_div_iff₀ (by positivity)] at h1;rw [le_div_iff₀ (by positivity)];linarith
  ·
   have h1:=hK_le.trans (hsp.2.2.2 hAne);rw [le_div_iff₀ hAR_pos] at h1;rw [le_div_iff₀ (by positivity)];linarith
 have hlayer_2A:∀ k,((layer k).card:E) ≤ 4*10^11*(N:E)^2*(H:E)^2/((P:E)^6*((2:E)^k)^2):=by
  intro k;let K:E:=(2:E)^k;let Mmax:ℕ:=⌊200*(N:E)*(H:E)/((P:E)^4*K)⌋₊;let key:(ℕ × ℕ × ℕ)->ℕ × ℕ × ℤ × ℤ:=fun t=>(t.1,t.2.1,(normOf t).1,(normOf t).2.1)
  let Kset:=(Finset.Ico P (2*P))×ˢ(Finset.Ico P (2*P)) ×ˢ
     ((Finset.Icc (-(Mmax:ℤ)) (Mmax:ℤ)).erase 0)×ˢ((Finset.Icc (-(Mmax:ℤ)) (Mmax:ℤ)).erase 0)
  by_cases hM0:Mmax=0
  ·
   have hemp:layer k=∅:=by
     rw [Finset.eq_empty_iff_forall_notMem];intro t ht;have hM:=(hlayer_MA k t ht).1
     have hlt1:200*(N:E)*(H:E)/((P:E)^4*K) < 1:=by
      have:=Nat.floor_eq_zero.mp hM0;exact this
     have ha1_ne:(normOf t).1≠0:=by
      have:=(mem_filter.mp (mem_filter.mp ht).1).2
      intro h0;exact this (by rw [h0];simp)
     have hge1:(1:E)<=(M_of t:E):=by
      have:(1:ℤ) ≤ |(normOf t).1|:=Int.one_le_abs ha1_ne
      have:(1:ℤ)<=M_of t:=le_trans this (le_max_left _ _)
      exact_mod_cast this
     linarith
   rw [hemp,Finset.card_empty,Nat.cast_zero];positivity
  ·
   have hMmax_pos:1<=Mmax:=Nat.pos_of_ne_zero hM0;have hMmax_le:(Mmax:E)<=200*(N:E)*(H:E)/((P:E)^4*K) :=Nat.floor_le (by positivity)
   have hkey_in:∀ t∈layer k,key t∈Kset:=by
     intro t ht;have ht_pr:=(mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp ht).1).1).1).1;have ht_prod:=mem_product.mp (mem_filter.mp ht_pr).1;have ht_prod2:=mem_product.mp ht_prod.2;have hM:=(hlayer_MA k t ht).1
     have hM_nat:M_of t<=(Mmax:ℤ):=by
      have h1:(M_of t:E)<=200*(N:E)*(H:E)/((P:E)^4*K):=hM;have hnn:(0:ℤ)<=M_of t:=le_trans (abs_nonneg _) (le_max_left _ _);have hcast_tn:((M_of t).toNat:E)=(M_of t:E):=by exact_mod_cast Int.toNat_of_nonneg hnn
      have h2:(M_of t).toNat<=Mmax:=Nat.le_floor (by rw [hcast_tn];exact h1);omega
     have ha1_bd:|(normOf t).1| ≤ (Mmax:ℤ):=le_trans (le_max_left _ _) hM_nat;have ha2_bd:|(normOf t).2.1| ≤ (Mmax:ℤ):=le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM_nat
     have ha1_ne:(normOf t).1≠0:=by
      have:=(mem_filter.mp (mem_filter.mp ht).1).2
      intro h0;exact this (by rw [h0];simp)
     have ha2_ne:(normOf t).2.1≠0:=by
      have:=(mem_filter.mp (mem_filter.mp ht).1).2
      intro h0;exact this (by rw [h0];simp)
     simp only [Kset,key,mem_product,mem_erase,Finset.mem_Icc];exact ⟨ht_prod.1,ht_prod2.1,⟨ha1_ne,abs_le.mp ha1_bd⟩,⟨ha2_ne,abs_le.mp ha2_bd⟩⟩
   have hfib_2A:∀ w∈Kset,((layer k).filter (fun t=>key t=w)).card<=2*10^6:=by
     intro w _;let F:=(layer k).filter (fun t=>key t=w);let α0:E:=-((w.2.2.1:E)/(w.1:E)^2+(w.2.2.2:E)/(w.2.1:E)^2)
     have hF_bd:∀ t∈F,|((normOf t).2.2:E)/(t.2.2:E)^2-α0| ≤ 3200*(H:E)^2/(K*(P:E)^6):=by
      intro t ht;rcases mem_filter.mp ht with ⟨ht_lk,hkw⟩;have ht_pr:=(mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp ht_lk).1).1).1).1;have ht_prod:=mem_product.mp (mem_filter.mp ht_pr).1;have ht_prod2:=mem_product.mp ht_prod.2
      have hp1:(P:E)<=(t.1:E):=by exact_mod_cast (Finset.mem_Ico.mp ht_prod.1).1
      have hp2:(P:E)<=(t.2.1:E):=by exact_mod_cast (Finset.mem_Ico.mp ht_prod2.1).1
      have hp3:(P:E)<=(t.2.2:E):=by exact_mod_cast (Finset.mem_Ico.mp ht_prod2.2).1
      have hp1_pos:(0:E) < (t.1:E):=lt_of_lt_of_le hP_pos hp1;have hp2_pos:(0:E) < (t.2.1:E):=lt_of_lt_of_le hP_pos hp2;have hp3_pos:(0:E) < (t.2.2:E):=lt_of_lt_of_le hP_pos hp3
      have heq:((normOf t).2.2:E)/(t.2.2:E)^2-α0 = (A_of t:E)/((t.1:E)^2*(t.2.1:E)^2*(t.2.2:E)^2):=by
       have hw1:w.1=t.1:=congrArg Prod.fst hkw.symm;have hw2:w.2.1=t.2.1:=congrArg (fun x=>x.2.1) hkw.symm;have hw3:w.2.2.1=(normOf t).1:=congrArg (fun x=>x.2.2.1) hkw.symm;have hw4:w.2.2.2=(normOf t).2.1:=congrArg (fun x=>x.2.2.2) hkw.symm
       dsimp [α0,A_of];rw [hw1,hw2,hw3,hw4];push_cast;field_simp [hp1_pos.ne',hp2_pos.ne',hp3_pos.ne'];ring
      have hden_pos:0 < (t.1:E)^2*(t.2.1:E)^2*(t.2.2:E)^2 :=mul_pos (mul_pos (sq_pos_of_pos hp1_pos) (sq_pos_of_pos hp2_pos)) (sq_pos_of_pos hp3_pos);rw [heq,abs_div,abs_of_pos hden_pos];have hA:=(hlayer_MA k t ht_lk).2
      have hden:(P:E)^6<=(t.1:E)^2*(t.2.1:E)^2*(t.2.2:E)^2:=by
       have h12:(P:E)^4<=(t.1:E)^2*(t.2.1:E)^2:=by
        calc
          (P:E)^4=(P:E)^2*(P:E)^2:=by ring
          _ <= (t.1:E)^2*(t.2.1:E)^2 :=mul_le_mul (pow_le_pow_left₀ hP_pos.le hp1 2) (pow_le_pow_left₀ hP_pos.le hp2 2) (by positivity) (by positivity)
       calc
        (P:E)^6=(P:E)^4*(P:E)^2:=by ring
        _ <= _:=mul_le_mul h12 (pow_le_pow_left₀ hP_pos.le hp3 2) (by positivity) (by positivity)
      calc
       |(A_of t:E)| / ((t.1:E)^2*(t.2.1:E)^2*(t.2.2:E)^2)
          ≤ (3200*(H:E)^2/K)/(P:E)^6 :=
        div_le_div₀ (by positivity) hA (pow_pos hP_pos 6) hden
       _ = 3200*(H:E)^2/(K*(P:E)^6):=by ring
     have hF_sep:∀ t1∈F,∀ t2∈F,t1≠t2 → 1/(16*(P:E)^4) ≤ |((normOf t1).2.2:E)/(t1.2.2:E)^2 -
        ((normOf t2).2.2:E)/(t2.2.2:E)^2|:=by
      intro t1 ht1 t2 ht2 hne;rcases mem_filter.mp ht1 with ⟨ht1_lk,hkw1⟩;rcases mem_filter.mp ht2 with ⟨ht2_lk,hkw2⟩;have ht1_pr:=(mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp ht1_lk).1).1).1).1
      have ht2_pr:=(mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp ht2_lk).1).1).1).1;have hfl1:=mem_filter.mp ht1_pr;have hfl2:=mem_filter.mp ht2_pr;have hp3_1_ico:=Finset.mem_Ico.mp (mem_product.mp (mem_product.mp hfl1.1).2).2
      have hp3_2_ico:=Finset.mem_Ico.mp (mem_product.mp (mem_product.mp hfl2.1).2).2
      have hp3_ne:t1.2.2≠t2.2.2:=by
       intro heq;apply hne;have hkw:key t1=key t2:=hkw1.trans hkw2.symm;rcases t1 with ⟨a1,b1,c1⟩;rcases t2 with ⟨a2,b2,c2⟩;simp only [key,Prod.mk.injEq] at hkw heq ⊢;exact ⟨hkw.1,hkw.2.1,heq⟩
      have ha3_1_ne:(normOf t1).2.2≠0:=by
       have:=(mem_filter.mp (mem_filter.mp ht1_lk).1).2
       intro h0;exact this (by rw [h0];simp)
      have ha3_1_lt:|(normOf t1).2.2| < (P:ℤ)^2:=by
       have hlt:M_of t1 < (P:ℤ)^2:=lt_of_not_ge (mem_filter.mp (mem_filter.mp (mem_filter.mp ht1_lk).1).1).2
       have:|(normOf t1).2.2| ≤ M_of t1:=le_trans (le_max_right _ _) (le_max_right _ _)
       omega
      have hnum_ne:(normOf t1).2.2*(t2.2.2:ℤ)^2-(normOf t2).2.2*(t1.2.2:ℤ)^2≠0:=by
       intro h0;have hd:(t1.2.2:ℤ)^2∣(normOf t1).2.2*(t2.2.2:ℤ)^2:=⟨(normOf t2).2.2,by linarith⟩
       have hcop:IsCoprime ((t1.2.2:ℤ)^2) ((t2.2.2:ℤ)^2) :=((Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hfl1.2.2.2.1 hfl2.2.2.2.1).mpr hp3_ne)).pow_left).pow_right;have hd1:(t1.2.2:ℤ)^2∣(normOf t1).2.2:=hcop.dvd_of_dvd_mul_right hd
       have hle:(t1.2.2:ℤ)^2 ≤ |(normOf t1).2.2|:=Int.le_of_dvd (abs_pos.mpr ha3_1_ne) (int_dvd_abs hd1);have hPsq:(P:ℤ)^2<=(t1.2.2:ℤ)^2:=by have:=hp3_1_ico.1;nlinarith
       omega
      have hnum_ge1:(1:E) ≤ |((normOf t1).2.2:E)*(t2.2.2:E)^2-((normOf t2).2.2:E)*(t1.2.2:E)^2|:=by
       have:(1:ℤ) ≤ |(normOf t1).2.2*(t2.2.2:ℤ)^2-(normOf t2).2.2*(t1.2.2:ℤ)^2| :=Int.one_le_abs hnum_ne
       exact_mod_cast this
      have hp3_1_pos:(0:E) < (t1.2.2:E):=by exact_mod_cast (show 0 < t1.2.2 by have:=hp3_1_ico.1;omega)
      have hp3_2_pos:(0:E) < (t2.2.2:E):=by exact_mod_cast (show 0 < t2.2.2 by have:=hp3_2_ico.1;omega)
      have hdiff_eq:((normOf t1).2.2:E)/(t1.2.2:E)^2-((normOf t2).2.2:E)/(t2.2.2:E)^2 = (((normOf t1).2.2:E)*(t2.2.2:E)^2-((normOf t2).2.2:E)*(t1.2.2:E)^2) / ((t1.2.2:E)^2*(t2.2.2:E)^2):=by field_simp [hp3_1_pos.ne',hp3_2_pos.ne']
      have hden2_pos:0 < (t1.2.2:E)^2*(t2.2.2:E)^2 :=mul_pos (sq_pos_of_pos hp3_1_pos) (sq_pos_of_pos hp3_2_pos);rw [hdiff_eq,abs_div,abs_of_pos hden2_pos]
      have hden:(t1.2.2:E)^2*(t2.2.2:E)^2<=16*(P:E)^4:=by
       have h1:(t1.2.2:E)^2<=4*(P:E)^2:=by
        have:(t1.2.2:E)<=2*(P:E):=by exact_mod_cast hp3_1_ico.2.le
        nlinarith
       have h2:(t2.2.2:E)^2<=4*(P:E)^2:=by
        have:(t2.2.2:E)<=2*(P:E):=by exact_mod_cast hp3_2_ico.2.le
        nlinarith
       calc
        _ <= (4*(P:E)^2)*(4*(P:E)^2):=mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 16*(P:E)^4:=by ring
      exact div_le_div₀ (by norm_num) hnum_ge1 hden2_pos hden
     have hsep_res:=card_separated_interval_le F (fun t=>((normOf t).2.2:E)/(t.2.2:E)^2)
      (by positivity) (by positivity) hF_bd hF_sep
     have hbound:1+2*(3200*(H:E)^2/(K*(P:E)^6))/(1/(16*(P:E)^4))<=2*10^6:=by
      have hK_ge1:(1:E)<=K:=one_le_pow₀ (by norm_num:(1:E)<=2);have hHP_R:(H:E)<=4*(P:E):=by exact_mod_cast hHP
      have hHP2:(H:E)^2/(P:E)^2<=16:=by rw [div_le_iff₀ (sq_pos_of_pos hP_pos)];nlinarith
      have hrew:2*(3200*(H:E)^2/(K*(P:E)^6))/(1/(16*(P:E)^4)) = 102400*((H:E)^2/(P:E)^2)/K:=by field_simp [hP_pos.ne',(by positivity:K≠0)];ring
      rw [hrew]
      have hdiv:102400*((H:E)^2/(P:E)^2)/K<=102400*16:=by
       calc
        _ <= 102400*((H:E)^2/(P:E)^2):=div_le_self (by positivity) hK_ge1
        _ <= 102400*16:=by linarith
      linarith
     have hF_le:(F.card:E)<=2*10^6:=hsep_res.trans hbound;exact_mod_cast hF_le
   have hpart:(layer k).card=∑ w∈Kset,((layer k).filter (fun t=>key t=w)).card:=by
     rw [← card_biUnion]
     ·
      congr 1;ext t;simp only [Finset.mem_biUnion,mem_filter];constructor
      · intro ht;exact ⟨key t,hkey_in t ht,ht,rfl⟩
      · rintro ⟨_,_,ht,_⟩;exact ht
     ·
      intro w1 _ w2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro t h1 h2;exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
   have hKset_card:(Kset.card:E)<=4*(P:E)^2*(Mmax:E)^2:=by
     have herase:((Finset.Icc (-(Mmax:ℤ)) (Mmax:ℤ)).erase 0).card=2*Mmax:=by
      rw [card_erase_of_mem (Finset.mem_Icc.mpr ⟨by omega,by omega⟩),Int.card_Icc];omega
     have h1:Kset.card=P*(P*((2*Mmax)*(2*Mmax))):=by
      simp only [Kset,Finset.card_product,Nat.card_Ico,herase];have h2P:2*P-P=P:=by omega
      rw [h2P]
     have h2:Kset.card=4*P^2*Mmax^2:=by rw [h1];ring
     exact_mod_cast h2.le
   have htot:((layer k).card:E)<=(Kset.card:E)*(2*10^6:E):=by
     rw [hpart,Nat.cast_sum]
     calc
      _ <= ∑ _w∈Kset,(2*10^6:E):=sum_le_sum (fun w hw=>by exact_mod_cast hfib_2A w hw)
      _ = _:=by simp
   calc
     ((layer k).card:E)<=4*(P:E)^2*(Mmax:E)^2*(2*10^6):=by
      have:=mul_le_mul_of_nonneg_right hKset_card (by norm_num:(0:E)<=2*10^6)
      linarith
     _ <= 4*(P:E)^2*(200*(N:E)*(H:E)/((P:E)^4*K))^2*(2*10^6):=by
      have:=pow_le_pow_left₀ (Nat.cast_nonneg Mmax) hMmax_le 2
      gcongr
     _ = (32*10^10:E)*((N:E)^2*(H:E)^2/((P:E)^6*K^2)):=by field_simp [hP_pos.ne',(by positivity:K≠0)];ring
     _ <= (4*10^11:E)*((N:E)^2*(H:E)^2/((P:E)^6*K^2)) :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
     _ = 4*10^11*(N:E)^2*(H:E)^2/((P:E)^6*K^2):=by ring
 have hlayer_2B:∀ k,((layer k).card:E) ≤ 2*10^7*(N:E)*(H:E)^3/((P:E)^2*((2:E)^k)^2):=by
  intro k;let K:E:=(2:E)^k;let Mmax:ℕ:=⌊200*(N:E)*(H:E)/((P:E)^4*K)⌋₊;let Amax:ℕ:=⌊3200*(H:E)^2/K⌋₊
  by_cases hMA0:Mmax=0\/Amax=0
  ·
   have hemp:layer k=∅:=by
     rw [Finset.eq_empty_iff_forall_notMem];intro t ht;have hMA:=hlayer_MA k t ht;rcases hMA0 with hM0 | hA0
     ·
      have hlt1:200*(N:E)*(H:E)/((P:E)^4*K) < 1:=Nat.floor_eq_zero.mp hM0
      have ha1_ne:(normOf t).1≠0:=by
       have:=(mem_filter.mp (mem_filter.mp ht).1).2
       intro h0;exact this (by rw [h0];simp)
      have hge1:(1:E)<=(M_of t:E):=by
       have:(1:ℤ)<=M_of t:=le_trans (Int.one_le_abs ha1_ne) (le_max_left _ _)
       exact_mod_cast this
      linarith
     ·
      have hlt1:3200*(H:E)^2/K < 1:=Nat.floor_eq_zero.mp hA0;have hAne:A_of t≠0:=hA_ne_of_small t (mem_filter.mp (mem_filter.mp ht).1).1;have hge1:(1:E) ≤ |(A_of t:E)|:=by exact_mod_cast Int.one_le_abs hAne
      linarith
   rw [hemp,Finset.card_empty,Nat.cast_zero];positivity
  ·
   push Not at hMA0
   have hMmax_pos:1<=Mmax:=Nat.pos_of_ne_zero hMA0.1;have hAmax_pos:1<=Amax:=Nat.pos_of_ne_zero hMA0.2;have hMmax_le:(Mmax:E)<=200*(N:E)*(H:E)/((P:E)^4*K):=Nat.floor_le (by positivity);have hAmax_le:(Amax:E)<=3200*(H:E)^2/K:=Nat.floor_le (by positivity)
   let key:(ℕ × ℕ × ℕ)->ℕ × ℕ × ℤ × ℤ:=fun t=>(t.1,t.2.1,(normOf t).1,A_of t)
   let Kset:=(Finset.Ico P (2*P))×ˢ(Finset.Ico P (2*P)) ×ˢ
      ((Finset.Icc (-(Mmax:ℤ)) (Mmax:ℤ)).erase 0) ×ˢ
      ((Finset.Icc (-(Amax:ℤ)) (Amax:ℤ)).erase 0)
   have hkey_in:∀ t∈layer k,key t∈Kset:=by
     intro t ht;have ht_pr:=(mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp ht).1).1).1).1;have ht_prod:=mem_product.mp (mem_filter.mp ht_pr).1;have ht_prod2:=mem_product.mp ht_prod.2;have hMA:=hlayer_MA k t ht
     have hM_nat:M_of t<=(Mmax:ℤ):=by
      have hnn:(0:ℤ)<=M_of t:=le_trans (abs_nonneg _) (le_max_left _ _);have hcast_tn:((M_of t).toNat:E)=(M_of t:E):=by exact_mod_cast Int.toNat_of_nonneg hnn
      have h2:(M_of t).toNat<=Mmax:=Nat.le_floor (by rw [hcast_tn];exact hMA.1);omega
     have hA_nat:|A_of t| ≤ (Amax:ℤ):=by
      have hnn:(0:ℤ) ≤ |A_of t|:=abs_nonneg _
      have hcast_tn:((|A_of t|).toNat:E) = |(A_of t:E)|:=by
       have h1:((|A_of t|).toNat:E)=((|A_of t|:ℤ):E):=by exact_mod_cast Int.toNat_of_nonneg hnn
       rw [h1];exact Int.cast_abs
      have h2:(|A_of t|).toNat<=Amax:=Nat.le_floor (by rw [hcast_tn];exact hMA.2);omega
     have ha1_ne:(normOf t).1≠0:=by
      have:=(mem_filter.mp (mem_filter.mp ht).1).2
      intro h0;exact this (by rw [h0];simp)
     have hA_ne:A_of t≠0:=hA_ne_of_small t (mem_filter.mp (mem_filter.mp ht).1).1;simp only [Kset,key,mem_product,mem_erase,Finset.mem_Icc];exact ⟨ht_prod.1,ht_prod2.1,⟨ha1_ne,abs_le.mp (le_trans (le_max_left _ _) hM_nat)⟩,⟨hA_ne,abs_le.mp hA_nat⟩⟩
   have hfib_2B:∀ w∈Kset,((layer k).filter (fun t=>key t=w)).card<=2:=by
     intro w hw;let F:=(layer k).filter (fun t=>key t=w)
     by_cases hne:F.Nonempty
     ·
      rcases hne with ⟨t0,ht0⟩;have ht0_lk:=(mem_filter.mp ht0).1;have hkw0:=(mem_filter.mp ht0).2;have ht0_pr:=(mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp ht0_lk).1).1).1).1;have hfl0:=mem_filter.mp ht0_pr
      have hw1:w.1=t0.1:=congrArg Prod.fst hkw0.symm;have hw2:w.2.1=t0.2.1:=congrArg (fun x=>x.2.1) hkw0.symm;have hw3:w.2.2.1=(normOf t0).1:=congrArg (fun x=>x.2.2.1) hkw0.symm;have hp1_ico:w.1∈Finset.Ico P (2*P):=(mem_product.mp hw).1
      have hp1_pr:Nat.Prime w.1:=hw1 ▸ hfl0.2.1;have hp2_pr:Nat.Prime w.2.1:=hw2 ▸ hfl0.2.2.1;have h12:w.1≠w.2.1:=by rw [hw1,hw2];exact hfl0.2.2.2.2.1
      have ha1_ne:w.2.2.1≠0:=(mem_erase.mp (mem_product.mp (mem_product.mp (mem_product.mp hw).2).2).1).1
      have ha1_lt:|w.2.2.1| < (P:ℤ)^2:=by
       rw [hw3];have hlt:M_of t0 < (P:ℤ)^2:=lt_of_not_ge (mem_filter.mp (mem_filter.mp (mem_filter.mp ht0_lk).1).1).2;exact lt_of_le_of_lt (le_max_left _ _) hlt
      have hinj:Set.InjOn (fun t:ℕ × ℕ × ℕ=>t.2.2) F:=by
       intro t1 ht1 t2 ht2 heq;have hk1:=(mem_filter.mp ht1).2;have hk2:=(mem_filter.mp ht2).2;have hk:key t1=key t2:=hk1.trans hk2.symm;rcases t1 with ⟨a1,b1,c1⟩;rcases t2 with ⟨a2,b2,c2⟩;simp only [key,Prod.mk.injEq] at hk heq ⊢;exact ⟨hk.1,hk.2.1,heq⟩
      have hsub:F.image (fun t=>t.2.2) ⊆
        (Finset.Ico P (2*P)).filter (fun p3 =>
          Nat.Prime p3/\p3≠w.1/\((w.1:ℤ)^2∣w.2.2.1*(w.2.1:ℤ)^2*(p3:ℤ)^2-w.2.2.2)):=by
       intro p3 hp3;rcases Finset.mem_image.mp hp3 with ⟨t,htF,rfl⟩;rcases mem_filter.mp htF with ⟨ht_lk,hkw⟩;have ht_pr:=(mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp ht_lk).1).1).1).1;have hfl:=mem_filter.mp ht_pr
       have h1:t.1=w.1:=congrArg Prod.fst hkw;have h2:t.2.1=w.2.1:=congrArg (fun x=>x.2.1) hkw;have h3:(normOf t).1=w.2.2.1:=congrArg (fun x=>x.2.2.1) hkw;have h4:A_of t=w.2.2.2:=congrArg (fun x=>x.2.2.2) hkw
       refine mem_filter.mpr ⟨(mem_product.mp (mem_product.mp hfl.1).2).2,hfl.2.2.2.1,by rw [← h1];exact hfl.2.2.2.2.2.1.symm,?_⟩;refine ⟨-((normOf t).2.1*(t.2.2:ℤ)^2+(normOf t).2.2*(t.2.1:ℤ)^2),?_⟩;rw [← h1,← h2,← h3,← h4];dsimp [A_of];ring
      calc
       F.card=(F.image (fun t=>t.2.2)).card:=(Finset.card_image_iff.mpr hinj).symm
       _ <= _:=Finset.card_le_card hsub
       _ <= 2:=card_filter_sq_congr_prime_sq_le_two (by omega) hp1_ico hp1_pr hp2_pr h12 ha1_ne ha1_lt
     · change F.card<=2;rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty];omega
   have hpart:(layer k).card=∑ w∈Kset,((layer k).filter (fun t=>key t=w)).card:=by
     rw [← card_biUnion]
     ·
      congr 1;ext t;simp only [Finset.mem_biUnion,mem_filter];constructor
      · intro ht;exact ⟨key t,hkey_in t ht,ht,rfl⟩
      · rintro ⟨_,_,ht,_⟩;exact ht
     ·
      intro w1 _ w2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro t h1 h2;exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
   have hKset_card:(Kset.card:E)<=4*(P:E)^2*(Mmax:E)*(Amax:E):=by
     have herase:∀ m:ℕ,((Finset.Icc (-(m:ℤ)) (m:ℤ)).erase 0).card=2*m:=by
      intro m;rw [card_erase_of_mem (Finset.mem_Icc.mpr ⟨by omega,by omega⟩),Int.card_Icc];omega
     have h1:Kset.card=P*(P*((2*Mmax)*(2*Amax))):=by
      simp only [Kset,Finset.card_product,Nat.card_Ico,herase];have h2P:2*P-P=P:=by omega
      rw [h2P]
     have h2:Kset.card=4*P^2*Mmax*Amax:=by rw [h1];ring
     exact_mod_cast h2.le
   have htot:((layer k).card:E)<=(Kset.card:E)*2:=by
     rw [hpart,Nat.cast_sum]
     calc
      _ <= ∑ _w∈Kset,(2:E):=sum_le_sum (fun w hw=>by exact_mod_cast hfib_2B w hw)
      _ = _:=by simp
   calc
     ((layer k).card:E)<=8*(P:E)^2*(Mmax:E)*(Amax:E):=by linarith
     _ <= 8*(P:E)^2*(200*(N:E)*(H:E)/((P:E)^4*K))*(3200*(H:E)^2/K):=by gcongr
     _ = (5120000:E)*((N:E)*(H:E)^3/((P:E)^2*K^2)):=by field_simp [hP_pos.ne',(by positivity:K≠0)];ring
     _ <= (2*10^7:E)*((N:E)*(H:E)^3/((P:E)^2*K^2)) :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
     _ = 2*10^7*(N:E)*(H:E)^3/((P:E)^2*K^2):=by ring
 have hmain_2A:∑ t∈R2_main,((sextupleFiber N H P D D' t).card:E) ≤ 10^7*(N:E)*(H:E)/(P:E)^(3/2:E):=by
  have hsum:=sum_dyadic_min_le B_log (U:=(P:E)^3)
   (V:=4*10^11*(N:E)^2*(H:E)^2/(P:E)^6) (by positivity) (by positivity)
  have hterm:∀ k∈Finset.range B_log,2*(2:E)^k*((layer k).card:E) ≤ 2*min ((2:E)^k*(P:E)^3)
           (4*10^11*(N:E)^2*(H:E)^2/(P:E)^6/(2:E)^k):=by
   intro k _;have h1:(2:E)^k*((layer k).card:E)<=(2:E)^k*(P:E)^3 :=mul_le_mul_of_nonneg_left (hlayer_triv k) (by positivity)
   have h2:(2:E)^k*((layer k).card:E) ≤ 4*10^11*(N:E)^2*(H:E)^2/(P:E)^6/(2:E)^k:=by
     have h:=mul_le_mul_of_nonneg_left (hlayer_2A k) (by positivity:(0:E)<=(2:E)^k);have hrew:(2:E)^k*(4*10^11*(N:E)^2*(H:E)^2/((P:E)^6*((2:E)^k)^2)) = 4*10^11*(N:E)^2*(H:E)^2/(P:E)^6/(2:E)^k:=by field_simp [pow_ne_zero k (by norm_num:(2:E)≠0)]
     linarith
   linarith [le_min h1 h2]
  have hle1:∑ t∈R2_main,((sextupleFiber N H P D D' t).card:E) ≤ 8*((P:E)^3*(4*10^11*(N:E)^2*(H:E)^2/(P:E)^6))^(1/2:E):=by
   calc
     _ <= ∑ k∈Finset.range B_log,(2*(2:E)^k*((layer k).card:E)):=hmain_layers
     _ <= ∑ k∈Finset.range B_log,(2*min ((2:E)^k*(P:E)^3)
        (4*10^11*(N:E)^2*(H:E)^2/(P:E)^6/(2:E)^k)):=sum_le_sum hterm
     _ = 2*∑ k∈Finset.range B_log,min ((2:E)^k*(P:E)^3)
        (4*10^11*(N:E)^2*(H:E)^2/(P:E)^6/(2:E)^k):=(Finset.mul_sum _ _ _).symm
     _ <= 2*(4*((P:E)^3*(4*10^11*(N:E)^2*(H:E)^2/(P:E)^6))^(1/2:E)) :=mul_le_mul_of_nonneg_left hsum (by norm_num)
     _ = _:=by ring
  have hsimp:((P:E)^3*(4*10^11*(N:E)^2*(H:E)^2/(P:E)^6))^(1/2:E) ≤ 10^6*((N:E)*(H:E)/(P:E)^(3/2:E)):=by
   have hrew:(P:E)^3*(4*10^11*(N:E)^2*(H:E)^2/(P:E)^6) = (4*10^11:E)*(((N:E)*(H:E))^2/(P:E)^3):=by field_simp [hP_pos.ne']
   rw [hrew,mul_rpow (by positivity) (by positivity),div_rpow (by positivity) (by positivity),← rpow_natCast ((N:E)*(H:E)) 2,← rpow_mul (by positivity),← rpow_natCast (P:E) 3,← rpow_mul hP_pos.le];have h2half:(2:E)*(1/2:E)=1:=by norm_num
   have h3half:(3:E)*(1/2:E)=3/2:=by norm_num
   push_cast;rw [h2half,rpow_one,h3half]
   have hc:(4*10^11:E)^(1/2:E)<=10^6:=by
     have hle:(4*10^11:E)<=(10^6:E)^2:=by norm_num
     have hrp:=rpow_le_rpow (by positivity) hle (by norm_num:(0:E)<=1/2);rw [← rpow_natCast (10^6:E) 2,← rpow_mul (by positivity)] at hrp;push_cast at hrp;rw [h2half,rpow_one] at hrp;exact hrp
   exact mul_le_mul_of_nonneg_right hc (by positivity)
  calc
   ∑ t∈R2_main,((sextupleFiber N H P D D' t).card:E)
      ≤ 8*(10^6*((N:E)*(H:E)/(P:E)^(3/2:E))) :=
     hle1.trans (mul_le_mul_of_nonneg_left hsimp (by norm_num))
   _ = (8*10^6:E)*((N:E)*(H:E)/(P:E)^(3/2:E)):=by ring
   _ <= (10^7:E)*((N:E)*(H:E)/(P:E)^(3/2:E)) :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
   _ = 10^7*(N:E)*(H:E)/(P:E)^(3/2:E):=by ring
 have hmain_2B:∑ t∈R2_main,((sextupleFiber N H P D D' t).card:E) ≤ 4*10^4*(N:E)^(1/2:E)*(H:E)^(3/2:E)*(P:E)^(1/2:E):=by
  have hsum:=sum_dyadic_min_le B_log (U:=(P:E)^3)
   (V:=2*10^7*(N:E)*(H:E)^3/(P:E)^2) (by positivity) (by positivity)
  have hterm:∀ k∈Finset.range B_log,2*(2:E)^k*((layer k).card:E) ≤ 2*min ((2:E)^k*(P:E)^3)
           (2*10^7*(N:E)*(H:E)^3/(P:E)^2/(2:E)^k):=by
   intro k _;have h1:(2:E)^k*((layer k).card:E)<=(2:E)^k*(P:E)^3 :=mul_le_mul_of_nonneg_left (hlayer_triv k) (by positivity)
   have h2:(2:E)^k*((layer k).card:E) ≤ 2*10^7*(N:E)*(H:E)^3/(P:E)^2/(2:E)^k:=by
     have h:=mul_le_mul_of_nonneg_left (hlayer_2B k) (by positivity:(0:E)<=(2:E)^k);have hrew:(2:E)^k*(2*10^7*(N:E)*(H:E)^3/((P:E)^2*((2:E)^k)^2)) = 2*10^7*(N:E)*(H:E)^3/(P:E)^2/(2:E)^k:=by field_simp [pow_ne_zero k (by norm_num:(2:E)≠0)]
     linarith
   linarith [le_min h1 h2]
  have hle1:∑ t∈R2_main,((sextupleFiber N H P D D' t).card:E) ≤ 8*((P:E)^3*(2*10^7*(N:E)*(H:E)^3/(P:E)^2))^(1/2:E):=by
   calc
     _ <= ∑ k∈Finset.range B_log,(2*(2:E)^k*((layer k).card:E)):=hmain_layers
     _ <= ∑ k∈Finset.range B_log,(2*min ((2:E)^k*(P:E)^3)
        (2*10^7*(N:E)*(H:E)^3/(P:E)^2/(2:E)^k)):=sum_le_sum hterm
     _ = 2*∑ k∈Finset.range B_log,min ((2:E)^k*(P:E)^3)
        (2*10^7*(N:E)*(H:E)^3/(P:E)^2/(2:E)^k):=(Finset.mul_sum _ _ _).symm
     _ <= 2*(4*((P:E)^3*(2*10^7*(N:E)*(H:E)^3/(P:E)^2))^(1/2:E)) :=mul_le_mul_of_nonneg_left hsum (by norm_num)
     _ = _:=by ring
  have hsimp:((P:E)^3*(2*10^7*(N:E)*(H:E)^3/(P:E)^2))^(1/2:E) ≤ 5000*((N:E)^(1/2:E)*((H:E)^(3/2:E)*(P:E)^(1/2:E))):=by
   have hrew:(P:E)^3*(2*10^7*(N:E)*(H:E)^3/(P:E)^2) = (2*10^7:E)*((N:E)*((H:E)^3*(P:E))):=by field_simp [hP_pos.ne']
   rw [hrew,mul_rpow (by positivity) (by positivity),mul_rpow hN_pos.le (by positivity),mul_rpow (by positivity) hP_pos.le,← rpow_natCast (H:E) 3,← rpow_mul hH_pos.le];have h2half:(2:E)*(1/2:E)=1:=by norm_num
   have h3half:(3:E)*(1/2:E)=3/2:=by norm_num
   push_cast;rw [h3half]
   have hc:(2*10^7:E)^(1/2:E)<=5000:=by
     have hle:(2*10^7:E)<=(5000:E)^2:=by norm_num
     have hrp:=rpow_le_rpow (by positivity) hle (by norm_num:(0:E)<=1/2);rw [← rpow_natCast (5000:E) 2,← rpow_mul (by positivity)] at hrp;push_cast at hrp;rw [h2half,rpow_one] at hrp;exact hrp
   exact mul_le_mul_of_nonneg_right hc (by positivity)
  calc
   ∑ t∈R2_main,((sextupleFiber N H P D D' t).card:E)
      ≤ 8*(5000*((N:E)^(1/2:E)*((H:E)^(3/2:E)*(P:E)^(1/2:E)))) :=
     hle1.trans (mul_le_mul_of_nonneg_left hsimp (by norm_num))
   _ = 4*10^4*(N:E)^(1/2:E)*(H:E)^(3/2:E)*(P:E)^(1/2:E):=by ring
 have hmain_min:=le_min hmain_2A hmain_2B;linarith
set_option maxHeartbeats 400000 in
lemma rank1_fiber_primitive {N H P D D':ℕ} {t:ℕ × ℕ × ℕ}
  (hrk1:FiberRank1 (sextupleFiber N H P D D' t)) :
  ∃ r1 r2 r3 d0:ℕ,1<=r1/\1<=r2/\1<=r3 ∧ (sextupleFiber N H P D D' t).card<=d0/\d0<=D ∧ (d0*r1,d0*r2,d0*r3)∈sextupleFiber N H P D D' t:=by
 let Q:=sextupleFiber N H P D D' t;rcases hrk1 with ⟨⟨q0,hq0⟩,hno3,hno2⟩
 have hprop:∀ a∈Q,∀ b∈Q,a.2.1*b.2.2=a.2.2*b.2.1/\a.2.2*b.1=a.1*b.2.2/\a.1*b.2.1=a.2.1*b.1:=by
  intro a ha b hb
  have hnot:¬ ((toIntTriple a).2.1*(toIntTriple b).2.2-(toIntTriple a).2.2*(toIntTriple b).2.1≠0 ∨ (toIntTriple a).2.2*(toIntTriple b).1-(toIntTriple a).1*(toIntTriple b).2.2≠0 ∨ (toIntTriple a).1*(toIntTriple b).2.1-(toIntTriple a).2.1*(toIntTriple b).1≠0) := fun h=>hno2 ⟨hno3,a,ha,b,hb,h⟩
  push Not at hnot
  dsimp [toIntTriple] at hnot;exact ⟨by exact_mod_cast (sub_eq_zero.mp hnot.1),by exact_mod_cast (sub_eq_zero.mp hnot.2.1),by exact_mod_cast (sub_eq_zero.mp hnot.2.2)⟩
 let g0:=Nat.gcd (Nat.gcd q0.1 q0.2.1) q0.2.2
 have hq0_pos:1<=q0.1/\1<=q0.2.1/\1<=q0.2.2:=by
  have hprod:=mem_product.mp (mem_filter.mp hq0).1;have hprod2:=mem_product.mp hprod.2;exact ⟨(Finset.mem_Icc.mp hprod.1).1,(Finset.mem_Icc.mp hprod2.1).1,(Finset.mem_Icc.mp hprod2.2).1⟩
 have hg0_pos:0 < g0:=Nat.gcd_pos_of_pos_right _ (by omega);let r1:=q0.1/g0;let r2:=q0.2.1/g0;let r3:=q0.2.2/g0;have hr1_mul:g0*r1=q0.1:=Nat.mul_div_cancel' ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
 have hr2_mul:g0*r2=q0.2.1:=Nat.mul_div_cancel' ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _));have hr3_mul:g0*r3=q0.2.2:=Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
 have hr_pos:1<=r1/\1<=r2/\1<=r3:=by
  refine ⟨?_,?_,?_⟩
  · by_contra h;push Not at h;have h0:r1=0:=Nat.lt_one_iff.mp h;rw [h0,mul_zero] at hr1_mul;omega
  · by_contra h;push Not at h;have h0:r2=0:=Nat.lt_one_iff.mp h;rw [h0,mul_zero] at hr2_mul;omega
  · by_contra h;push Not at h;have h0:r3=0:=Nat.lt_one_iff.mp h;rw [h0,mul_zero] at hr3_mul;omega
 have hmul_all:∀ q∈Q,
   let d:=Nat.gcd (Nat.gcd q.1 q.2.1) q.2.2
   q=(d*r1,d*r2,d*r3)/\1<=d/\d<=D:=by
  intro q hq
  have hq_pos:1<=q.1/\1<=q.2.1/\1<=q.2.2:=by
   have hprod:=mem_product.mp (mem_filter.mp hq).1;have hprod2:=mem_product.mp hprod.2;exact ⟨(Finset.mem_Icc.mp hprod.1).1,(Finset.mem_Icc.mp hprod2.1).1,(Finset.mem_Icc.mp hprod2.2).1⟩
  set d:=Nat.gcd (Nat.gcd q.1 q.2.1) q.2.2;have hd_pos:1<=d:=Nat.gcd_pos_of_pos_right _ (by omega);have hd_le:d<=D:=(mem_filter.mp hq).2.2.2.2.2.2.2.2.2.2.1;have hp:=hprop q0 hq0 q hq;let s1:=q.1/d;let s2:=q.2.1/d;let s3:=q.2.2/d
  have hs1_mul:d*s1=q.1:=Nat.mul_div_cancel' ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _));have hs2_mul:d*s2=q.2.1:=Nat.mul_div_cancel' ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
  have hs3_mul:d*s3=q.2.2:=Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hprim_r:Nat.gcd (Nat.gcd r1 r2) r3=1:=by
   set k:=Nat.gcd (Nat.gcd r1 r2) r3;have hk1:g0*k∣q0.1:=hr1_mul ▸ mul_dvd_mul_left g0 ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _));have hk2:g0*k∣q0.2.1:=hr2_mul ▸ mul_dvd_mul_left g0 ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
   have hk3:g0*k∣q0.2.2:=hr3_mul ▸ mul_dvd_mul_left g0 (Nat.gcd_dvd_right _ _);have hkg:g0*k∣g0:=Nat.dvd_gcd (Nat.dvd_gcd hk1 hk2) hk3;have hle:g0*k<=g0:=Nat.le_of_dvd hg0_pos hkg;have hk_pos:0 < k:=Nat.gcd_pos_of_pos_right _ (by omega);nlinarith
  have hprim_s:Nat.gcd (Nat.gcd s1 s2) s3=1:=by
   set k:=Nat.gcd (Nat.gcd s1 s2) s3;have hk1:d*k∣q.1:=hs1_mul ▸ mul_dvd_mul_left d ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _));have hk2:d*k∣q.2.1:=hs2_mul ▸ mul_dvd_mul_left d ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _))
   have hk3:d*k∣q.2.2:=hs3_mul ▸ mul_dvd_mul_left d (Nat.gcd_dvd_right _ _);have hkd:d*k∣d:=Nat.dvd_gcd (Nat.dvd_gcd hk1 hk2) hk3;have hle:d*k<=d:=Nat.le_of_dvd (by omega) hkd
   have hs3_pos:1<=s3:=by
    by_contra h;push Not at h
    have hs0:s3=0:=Nat.lt_one_iff.mp h;rw [hs0,mul_zero] at hs3_mul;omega
   have hk_pos:0 < k:=Nat.gcd_pos_of_pos_right _ (by omega);nlinarith
  have hsr12:r1*s2=r2*s1:=by
   have:(g0*d)*(r1*s2)=(g0*d)*(r2*s1):=by
    calc
     (g0*d)*(r1*s2)=(g0*r1)*(d*s2):=by ring
     _ = q0.1*q.2.1:=by rw [hr1_mul,hs2_mul]
     _ = q0.2.1*q.1:=hp.2.2
     _ = (g0*r2)*(d*s1):=by rw [hr2_mul,hs1_mul]
     _ = (g0*d)*(r2*s1):=by ring
   exact mul_left_cancel₀ (by positivity) this
  have hsr13:r1*s3=r3*s1:=by
   have:(g0*d)*(r1*s3)=(g0*d)*(r3*s1):=by
    calc
     (g0*d)*(r1*s3)=(g0*r1)*(d*s3):=by ring
     _ = q0.1*q.2.2:=by rw [hr1_mul,hs3_mul]
     _ = q0.2.2*q.1:=hp.2.1.symm
     _ = (g0*r3)*(d*s1):=by rw [hr3_mul,hs1_mul]
     _ = (g0*d)*(r3*s1):=by ring
   exact mul_left_cancel₀ (by positivity) this
  have hr1_eq_s1:r1=s1:=by
   have h1:Nat.gcd (Nat.gcd (r1*s1) (r1*s2)) (r1*s3)=r1:=by rw [Nat.gcd_mul_left,Nat.gcd_mul_left,hprim_s,mul_one]
   have h2:Nat.gcd (Nat.gcd (s1*r1) (s1*r2)) (s1*r3)=s1:=by rw [Nat.gcd_mul_left,Nat.gcd_mul_left,hprim_r,mul_one]
   calc
    r1=Nat.gcd (Nat.gcd (r1*s1) (r1*s2)) (r1*s3):=h1.symm
    _ = Nat.gcd (Nat.gcd (s1*r1) (s1*r2)) (s1*r3):=by rw [mul_comm r1 s1,hsr12,hsr13,mul_comm r2 s1,mul_comm r3 s1]
    _ = s1:=h2
  have hr2_eq_s2:r2=s2:=by
   have:r1*s2=r1*r2:=by rw [hsr12,← hr1_eq_s1,mul_comm]
   exact (mul_left_cancel₀ (by omega) this).symm
  have hr3_eq_s3:r3=s3:=by
   have:r1*s3=r1*r3:=by rw [hsr13,← hr1_eq_s1,mul_comm]
   exact (mul_left_cancel₀ (by omega) this).symm
  refine ⟨?_,hd_pos,hd_le⟩;rcases q with ⟨q1,q2,q3⟩;simp only [Prod.mk.injEq];exact ⟨by rw [hr1_eq_s1,hs1_mul],by rw [hr2_eq_s2,hs2_mul],by rw [hr3_eq_s3,hs3_mul]⟩
 let dSet:=Q.image (fun q=>Nat.gcd (Nat.gcd q.1 q.2.1) q.2.2);have hdSet_ne:dSet.Nonempty:=⟨_,Finset.mem_image_of_mem _ hq0⟩;let d0:=dSet.max' hdSet_ne;rcases Finset.mem_image.mp (Finset.max'_mem dSet hdSet_ne) with ⟨qm,hqm,hd0_eq⟩
 have hd0_eq':Nat.gcd (Nat.gcd qm.1 qm.2.1) qm.2.2=d0:=hd0_eq;have hqm_spec:=hmul_all qm hqm
 have hcard_le_d0:Q.card<=d0:=by
  have hinj:Set.InjOn (fun q:ℕ × ℕ × ℕ=>Nat.gcd (Nat.gcd q.1 q.2.1) q.2.2) Q:=by
   intro a ha b hb heq;dsimp only at heq;rw [(hmul_all a ha).1,(hmul_all b hb).1,heq]
  have hsub:dSet⊆Finset.Icc 1 d0:=by
   intro d hd;rcases Finset.mem_image.mp hd with ⟨q,hq,rfl⟩;exact Finset.mem_Icc.mpr ⟨(hmul_all q hq).2.1,Finset.le_max' dSet _ hd⟩
  calc
   Q.card=dSet.card:=(Finset.card_image_iff.mpr hinj).symm
   _ <= (Finset.Icc 1 d0).card:=Finset.card_le_card hsub
   _ = d0:=by rw [Nat.card_Icc];omega
 refine ⟨r1,r2,r3,d0,hr_pos.1,hr_pos.2.1,hr_pos.2.2,hcard_le_d0,hd0_eq' ▸ hqm_spec.2.2,?_⟩;rw [← hd0_eq',← hqm_spec.1];exact hqm
set_option maxHeartbeats 2000000 in
lemma sum_rank1_fibers_le {N H P D D':ℕ} (hN:1<=N) (hH:1<=H) (hP:4<=P)
  (hHP:H<=4*P) (hD:1<=D) (hDH:D<=H) (hD':1<=D') :
  (∑ t∈(PrimeTriples P).filter (fun t=>FiberRank1 (sextupleFiber N H P D D' t)),((sextupleFiber N H P D D' t).card:E)) ≤ 300*(N:E)^(3/5:E)*(H:E)^(6/5:E) + 800*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E) + 2000*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E):=by
 classical
 let R1:=(PrimeTriples P).filter (fun t=>FiberRank1 (sextupleFiber N H P D D' t));have hP_pos:(0:E) < (P:E):=by exact_mod_cast (show 0 < P by omega)
 have hN_pos:(0:E) < (N:E):=by exact_mod_cast hN
 have hH_pos:(0:E) < (H:E):=by exact_mod_cast hH
 have hD'_pos:(0:E) < (D':E):=by exact_mod_cast hD'
 let B1:ℕ:=Nat.log 2 D+2
 let T1:ℕ->Finset (ℕ × ℕ × ℕ):=fun k =>
  R1.filter (fun t=>2^k<=(sextupleFiber N H P D D' t).card ∧ (sextupleFiber N H P D D' t).card < 2^(k+1))
 have hR1_layers:∑ t∈R1,((sextupleFiber N H P D D' t).card:E) ≤ ∑ k∈Finset.range B1,(2*(2:E)^k*((T1 k).card:E)):=by
  have hcov:R1=(Finset.range B1).biUnion T1:=by
   ext t;simp only [Finset.mem_biUnion,Finset.mem_range,T1,mem_filter];constructor
   ·
    intro ht;have hrk1:=(mem_filter.mp ht).2;obtain ⟨_,_,_,d0,_,_,_,hcd0,hd0D,_⟩:=rank1_fiber_primitive hrk1;have hpos:1<=(sextupleFiber N H P D D' t).card:=Finset.card_pos.mpr hrk1.1;have hleD:(sextupleFiber N H P D D' t).card<=D:=hcd0.trans hd0D
    let k:=Nat.log 2 (sextupleFiber N H P D D' t).card;refine ⟨k,?_,ht,Nat.pow_log_le_self 2 (by omega),Nat.lt_pow_succ_log_self (by norm_num) _⟩
    have:=Nat.log_mono_right (b:=2) hleD;dsimp [B1];omega
   · rintro ⟨_,_,ht,_,_⟩;exact ht
  have hdisj:Set.PairwiseDisjoint (↑(Finset.range B1):Set ℕ) T1:=by
   intro k1 _ k2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro t ht1 ht2;have h1:=(mem_filter.mp ht1).2;have h2:=(mem_filter.mp ht2).2;rcases lt_or_gt_of_ne hne with hlt | hgt
   · have:2^(k1+1)<=2^k2:=Nat.pow_le_pow_right (by norm_num) (by omega);omega
   · have:2^(k2+1)<=2^k1:=Nat.pow_le_pow_right (by norm_num) (by omega);omega
  rw [hcov,Finset.sum_biUnion hdisj];apply sum_le_sum;intro k _
  calc
   ∑ t∈T1 k,((sextupleFiber N H P D D' t).card:E)
      ≤ ∑ _t∈T1 k,(2*(2:E)^k):=by
    apply sum_le_sum;intro t ht
    have:((sextupleFiber N H P D D' t).card:E)<=(2:E)^(k+1):=by exact_mod_cast (mem_filter.mp ht).2.2.le
    rw [pow_succ'] at this;linarith
   _ = 2*(2:E)^k*((T1 k).card:E):=by simp;ring
 let PrimePairs:Finset (ℕ × ℕ) := ((Finset.Ico P (2*P))×ˢ(Finset.Ico P (2*P))).filter (fun p =>
   Nat.Prime p.1/\Nat.Prime p.2/\p.1≠p.2)
 have hPP_card:(PrimePairs.card:E)<=(P:E)^2:=by
  have h1:PrimePairs.card<=((Finset.Ico P (2*P))×ˢ(Finset.Ico P (2*P))).card :=Finset.card_filter_le _ _;simp only [Finset.card_product,Nat.card_Ico] at h1;have h2P:2*P-P=P:=by omega
  rw [h2P] at h1
  have:(PrimePairs.card:E)<=(P:E)*(P:E):=by exact_mod_cast h1
  linarith
 let pairFiber:ℕ->(ℕ × ℕ)->Finset (ℕ × ℕ):=fun k p =>
  let K:=2^k;let Rmax:=2*N/(K*P^2)
  ((Finset.Icc 1 Rmax)×ˢ(Finset.Icc 1 Rmax)).filter (fun r =>
   K*(p.1^2*r.1)<=2*N/\K*(p.2^2*r.2)<=2*N ∧
   1 ≤ |((p.1:ℤ)^2*(r.1:ℤ)-(p.2:ℤ)^2*(r.2:ℤ))| ∧
   (K:ℤ) * |((p.1:ℤ)^2*(r.1:ℤ)-(p.2:ℤ)^2*(r.2:ℤ))| < (H:ℤ) ∧
   Nat.gcd r.1 r.2<=D')
 let pairRank2:ℕ->(ℕ × ℕ)->Prop:=fun k p =>
  ∃ u∈pairFiber k p,∃ v∈pairFiber k p,(u.1:ℤ)*(v.2:ℤ)-(u.2:ℤ)*(v.1:ℤ)≠0
 have hT1_bound:∀ k∈Finset.range B1,2*(2:E)^k*((T1 k).card:E) ≤ 2*min ((2:E)^k*(P:E)^3)
           (600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2)) +
    6*(H:E)*(∑ p∈PrimePairs.filter (fun p=>(pairFiber k p).Nonempty/\¬ pairRank2 k p),((pairFiber k p).card:E)):=by
  intro k _
  by_cases hne:(T1 k).Nonempty
  ·
   have hK_le_H:2^k<=H:=by
    rcases hne with ⟨t0,ht0⟩;rcases mem_filter.mp ht0 with ⟨ht0_R1,hge,_⟩;obtain ⟨_,_,_,d0,_,_,_,hcd0,hd0D,_⟩:=rank1_fiber_primitive (mem_filter.mp ht0_R1).2;omega
   let K:=2^k;have hKR_pos:(0:E) < (K:E):=by positivity
   have hex_prim:∀ t∈T1 k,∃ r:ℕ × ℕ × ℕ,(r.1,r.2.1)∈pairFiber k (t.1,t.2.1) ∧ (K:ℤ) * |((t.1:ℤ)^2*(r.1:ℤ)-(t.2.2:ℤ)^2*(r.2.2:ℤ))| < (H:ℤ) ∧ IsMinPrimeSqDiv P t.2.2 (t.2.2^2*r.2.2):=by
    intro t ht;rcases mem_filter.mp ht with ⟨ht_R1,hge,_⟩;have ht_pr:=(mem_filter.mp ht_R1).1;have hfl_pr:=mem_filter.mp ht_pr;obtain ⟨r1,r2,r3,d0,hr1,hr2,hr3,hcd0,_,hmem⟩ :=rank1_fiber_primitive (mem_filter.mp ht_R1).2;have hK_le_d0:K<=d0:=hge.trans hcd0
    have hfl:=(mem_filter.mp hmem).2;have hp1_ge:P<=t.1:=(Finset.mem_Ico.mp (mem_product.mp hfl_pr.1).1).1;have hp2_ge:P<=t.2.1:=(Finset.mem_Ico.mp (mem_product.mp (mem_product.mp hfl_pr.1).2).1).1
    have h1_le:K*(t.1^2*r1)<=2*N:=by
      calc
        K*(t.1^2*r1)<=d0*(t.1^2*r1):=Nat.mul_le_mul_right _ hK_le_d0
        _ = t.1^2*(d0*r1):=by ring
        _ <= 2*N:=hfl.1
    have h2_le:K*(t.2.1^2*r2)<=2*N:=by
      calc
        K*(t.2.1^2*r2)<=d0*(t.2.1^2*r2):=Nat.mul_le_mul_right _ hK_le_d0
        _ = t.2.1^2*(d0*r2):=by ring
        _ <= 2*N:=hfl.2.1
    have hr1_le:r1<=2*N/(K*P^2):=by
      apply Nat.le_div_iff_mul_le (by positivity) |>.mpr
      calc
        r1*(K*P^2)=K*(P^2*r1):=by ring
        _ <= K*(t.1^2*r1):=Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hp1_ge 2))
        _ <= 2*N:=h1_le
    have hr2_le:r2<=2*N/(K*P^2):=by
      apply Nat.le_div_iff_mul_le (by positivity) |>.mpr
      calc
        r2*(K*P^2)=K*(P^2*r2):=by ring
        _ <= K*(t.2.1^2*r2):=Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hp2_ge 2))
        _ <= 2*N:=h2_le
    have h12_ne:(t.1:ℤ)^2*(r1:ℤ)-(t.2.1:ℤ)^2*(r2:ℤ)≠0:=by
      intro h0
      have heqN:t.1^2*(d0*r1)=t.2.1^2*(d0*r2):=by
        have:(t.1:ℤ)^2*((d0:ℤ)*(r1:ℤ))=(t.2.1:ℤ)^2*((d0:ℤ)*(r2:ℤ)):=by linear_combination (d0:ℤ)*h0
        exact_mod_cast this
      have hmin1:=hfl.2.2.2.2.2.2.1;have hmin2:=hfl.2.2.2.2.2.2.2.1;rw [heqN] at hmin1;exact hfl_pr.2.2.2.2.1 (isMinPrimeSqDiv_unique hmin1 hmin2)
    have h12_lt:(K:ℤ) * |((t.1:ℤ)^2*(r1:ℤ)-(t.2.1:ℤ)^2*(r2:ℤ))| < (H:ℤ):=by
      have h:=hfl.2.2.2.2.2.1;have hrew:(t.1:ℤ)^2*((d0*r1:ℕ):ℤ)-(t.2.1:ℤ)^2*((d0*r2:ℕ):ℤ) = (d0:ℤ)*((t.1:ℤ)^2*(r1:ℤ)-(t.2.1:ℤ)^2*(r2:ℤ)):=by push_cast;ring
      rw [hrew,abs_mul,abs_of_nonneg (Nat.cast_nonneg d0)] at h;have hKd:(K:ℤ)<=(d0:ℤ):=by exact_mod_cast hK_le_d0
      nlinarith [abs_nonneg ((t.1:ℤ)^2*(r1:ℤ)-(t.2.1:ℤ)^2*(r2:ℤ))]
    have h13_lt:(K:ℤ) * |((t.1:ℤ)^2*(r1:ℤ)-(t.2.2:ℤ)^2*(r3:ℤ))| < (H:ℤ):=by
      have h:=hfl.2.2.2.1;have hrew:(t.1:ℤ)^2*((d0*r1:ℕ):ℤ)-(t.2.2:ℤ)^2*((d0*r3:ℕ):ℤ) = (d0:ℤ)*((t.1:ℤ)^2*(r1:ℤ)-(t.2.2:ℤ)^2*(r3:ℤ)):=by push_cast;ring
      rw [hrew,abs_mul,abs_of_nonneg (Nat.cast_nonneg d0)] at h;have hKd:(K:ℤ)<=(d0:ℤ):=by exact_mod_cast hK_le_d0
      nlinarith [abs_nonneg ((t.1:ℤ)^2*(r1:ℤ)-(t.2.2:ℤ)^2*(r3:ℤ))]
    have hgcd12:Nat.gcd r1 r2<=D':=by
      have h:=hfl.2.2.2.2.2.2.2.2.2.2;rw [Nat.gcd_mul_left] at h;have hd0_pos:1<=d0:=by omega
      nlinarith
    refine ⟨(r1,r2,r3),?_,h13_lt,isMinPrimeSqDiv_of_mul_dvd hfl.2.2.2.2.2.2.2.2.1⟩;simp only [pairFiber,mem_filter,mem_product,Finset.mem_Icc];exact ⟨⟨⟨hr1,hr1_le⟩,⟨hr2,hr2_le⟩⟩,h1_le,h2_le,Int.one_le_abs h12_ne,h12_lt,hgcd12⟩
   let rOf:(ℕ × ℕ × ℕ)->ℕ × ℕ × ℕ:=fun t=>if h:t∈T1 k then Classical.choose (hex_prim t h) else (0,0,0)
   have hrOf_spec:∀ t∈T1 k,((rOf t).1,(rOf t).2.1)∈pairFiber k (t.1,t.2.1) ∧ (K:ℤ) * |((t.1:ℤ)^2*((rOf t).1:ℤ)-(t.2.2:ℤ)^2*((rOf t).2.2:ℤ))| < (H:ℤ) ∧ IsMinPrimeSqDiv P t.2.2 (t.2.2^2*(rOf t).2.2):=by
    intro t ht;simp only [rOf,ht,↓reduceDIte];exact Classical.choose_spec (hex_prim t ht)
   let T1_rk2:=(T1 k).filter (fun t=>pairRank2 k (t.1,t.2.1));let T1_rk1:=(T1 k).filter (fun t=>¬ pairRank2 k (t.1,t.2.1));have hT1_split:(T1 k).card=T1_rk2.card+T1_rk1.card :=(Finset.card_filter_add_card_filter_not _).symm
   have hproj:∀ (U:Finset (ℕ × ℕ × ℕ)) (PP_sub:Finset (ℕ × ℕ)),U⊆T1 k->(∀ t∈U,(t.1,t.2.1)∈PP_sub) → (U.card:E)<=(3*(H:E)/(K:E))*∑ p∈PP_sub,((pairFiber k p).card:E):=by
    intro U PP_sub hU_sub hU_pp;let proj:(ℕ × ℕ × ℕ)->(ℕ × ℕ) × (ℕ × ℕ):=fun t=>((t.1,t.2.1),((rOf t).1,(rOf t).2.1));let target:Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=PP_sub.biUnion (fun p=>(pairFiber k p).image (fun r=>(p,r)))
    have hproj_mem:∀ t∈U,proj t∈target:=by
      intro t ht;refine Finset.mem_biUnion.mpr ⟨(t.1,t.2.1),hU_pp t ht,?_⟩;exact Finset.mem_image_of_mem _ (hrOf_spec t (hU_sub ht)).1
    have hfib_proj:∀ w∈target,((U.filter (fun t=>proj t=w)).card:E)<=3*(H:E)/(K:E):=by
      intro w _;let F:=U.filter (fun t=>proj t=w);let mOf:(ℕ × ℕ × ℕ)->ℤ:=fun t=>((t.2.2^2*(rOf t).2.2:ℕ):ℤ)
      have hm_inj:Set.InjOn mOf F:=by
        intro t1 ht1 t2 ht2 heq;have h1:=mem_filter.mp ht1;have h2:=mem_filter.mp ht2;have hmeq:t1.2.2^2*(rOf t1).2.2=t2.2.2^2*(rOf t2).2.2:=by dsimp [mOf] at heq;exact_mod_cast heq
        have hm1:=(hrOf_spec t1 (hU_sub h1.1)).2.2;have hm2:=(hrOf_spec t2 (hU_sub h2.1)).2.2;rw [hmeq] at hm1;have hp3_eq:t1.2.2=t2.2.2:=isMinPrimeSqDiv_unique hm1 hm2;have hpeq:proj t1=proj t2:=h1.2.trans h2.2.symm
        rcases t1 with ⟨a1,b1,c1⟩;rcases t2 with ⟨a2,b2,c2⟩;simp only [proj,Prod.mk.injEq] at hpeq hp3_eq ⊢;exact ⟨hpeq.1.1,hpeq.1.2,hp3_eq⟩
      let center:ℤ:=(w.1.1:ℤ)^2*(w.2.1:ℤ);let rad:ℤ:=(H/K:ℕ)
      have hm_sub:F.image mOf⊆Finset.Icc (center-rad) (center+rad):=by
        intro m hm;rcases Finset.mem_image.mp hm with ⟨t,htF,rfl⟩;have hfl:=mem_filter.mp htF;have hlt:=(hrOf_spec t (hU_sub hfl.1)).2.1;have hp1:t.1=w.1.1:=congrArg (fun x=>x.1.1) hfl.2;have hr1:(rOf t).1=w.2.1:=congrArg (fun x=>x.2.1) hfl.2
        rw [hp1,hr1] at hlt
        have habs_le:|(center-mOf t)| ≤ rad:=by
          have h1:(K:ℤ) * |center-mOf t| < (H:ℤ):=by dsimp [center,mOf];exact hlt
          have hdiv:|center-mOf t| ≤ (H:ℤ)/(K:ℤ) :=Int.le_ediv_of_mul_le (by exact_mod_cast (show 0 < K by positivity)) (by linarith);dsimp [rad];exact_mod_cast hdiv
        have hbd:=abs_le.mp habs_le;exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
      have hcard:F.card<=2*(H/K)+1:=by
        calc
          F.card=(F.image mOf).card:=(Finset.card_image_iff.mpr hm_inj).symm
          _ <= (Finset.Icc (center-rad) (center+rad)).card:=Finset.card_le_card hm_sub
          _ = 2*(H/K)+1:=by rw [Int.card_Icc];dsimp [rad];omega
      have hdiv_le:((H/K:ℕ):E)<=(H:E)/(K:E):=by rw [le_div_iff₀ hKR_pos];exact_mod_cast Nat.div_mul_le_self H K
      have h1_le:(1:E)<=(H:E)/(K:E):=(one_le_div hKR_pos).mpr (by exact_mod_cast hK_le_H);have hcast:(F.card:E)<=2*((H/K:ℕ):E)+1:=by exact_mod_cast hcard
      change (F.card:E)<=3*(H:E)/(K:E);have h3:3*(H:E)/(K:E)=3*((H:E)/(K:E)):=by ring
      linarith
    have hpart:U.card=∑ w∈target,(U.filter (fun t=>proj t=w)).card:=by
      rw [← card_biUnion]
      ·
        congr 1;ext t;simp only [Finset.mem_biUnion,mem_filter];constructor
        · intro ht;exact ⟨proj t,hproj_mem t ht,ht,rfl⟩
        · rintro ⟨_,_,ht,_⟩;exact ht
      ·
        intro w1 _ w2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro t h1 h2;exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
    have htarget_card:(target.card:E)<=∑ p∈PP_sub,((pairFiber k p).card:E):=by
      have h1:target.card<=∑ p∈PP_sub,((pairFiber k p).image (fun r=>(p,r))).card :=Finset.card_biUnion_le
      have h2:∑ p∈PP_sub,((pairFiber k p).image (fun r=>(p,r))).card = ∑ p∈PP_sub,(pairFiber k p).card:=by
        apply sum_congr rfl;intro p _;exact Finset.card_image_of_injective _ (fun a b h=>(Prod.mk.inj h).2)
      exact_mod_cast (h2 ▸ h1)
    rw [hpart,Nat.cast_sum]
    calc
      _ <= ∑ _w∈target,(3*(H:E)/(K:E)):=sum_le_sum hfib_proj
      _ = (3*(H:E)/(K:E))*(target.card:E):=by simp;ring
      _ <= (3*(H:E)/(K:E))*∑ p∈PP_sub,((pairFiber k p).card:E) :=mul_le_mul_of_nonneg_left htarget_card (by positivity)
   have hT1_rk2_triv:(T1_rk2.card:E)<=(P:E)^3:=by
    have hnat:T1_rk2.card<=(PrimeTriples P).card :=((Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)).trans (Finset.card_filter_le _ _);exact (by exact_mod_cast hnat:(T1_rk2.card:E)<=((PrimeTriples P).card:E)).trans (card_primeTriples_le P)
   have hT1_rk2_lat:(T1_rk2.card:E)<=600*(N:E)*(H:E)^2/((K:E)^3*(P:E)^2):=by
    let PP2:=PrimePairs.filter (fun p=>pairRank2 k p)
    have h1:=hproj T1_rk2 PP2 (Finset.filter_subset _ _) (by
      intro t ht;rcases mem_filter.mp ht with ⟨ht_T1,hrk2⟩;have ht_pr:=(mem_filter.mp (mem_filter.mp ht_T1).1).1;have hfl:=mem_filter.mp ht_pr;have hp:=mem_product.mp hfl.1;have hp2:=mem_product.mp hp.2
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hp.1,hp2.1⟩,hfl.2.1,hfl.2.2.1,hfl.2.2.2.2.1⟩,hrk2⟩)
    have hfib2:∀ p∈PP2,((pairFiber k p).card:E)<=200*(N:E)*(H:E)/((K:E)^2*(P:E)^4):=by
      intro p hp;rcases mem_filter.mp hp with ⟨hp_PP,u,hu,v,hv,hdet2⟩;have hfl_p:=mem_filter.mp hp_PP;have hp1_ge:P<=p.1:=(Finset.mem_Ico.mp (mem_product.mp hfl_p.1).1).1;have hp2_ge:P<=p.2:=(Finset.mem_Ico.mp (mem_product.mp hfl_p.1).2).1
      let S2:Finset (ℤ × ℤ):=(pairFiber k p).image (fun r=>((r.1:ℤ),(r.2:ℤ)))
      have hinj2:Function.Injective (fun r:ℕ × ℕ=>((r.1:ℤ),(r.2:ℤ))):=by
        intro a b h;simp only [Prod.mk.injEq,Nat.cast_inj] at h;ext <;> [exact h.1;exact h.2]
      have hcard2:((pairFiber k p).card:E)=(S2.card:E):=by exact_mod_cast (Finset.card_image_of_injective _ hinj2).symm
      have hS2_bd:∀ z∈S2,
          |((p.1:E)^2)*(z.1:E)| ≤ 2*(N:E)/(K:E) ∧
          |((p.1:E)^2)*(z.1:E)-((p.2:E)^2)*(z.2:E)| ≤ (H:E)/(K:E):=by
        intro z hz;rcases Finset.mem_image.mp hz with ⟨r,hr,rfl⟩;have hfl:=(mem_filter.mp hr).2;refine ⟨?_,?_⟩
        ·
          dsimp only;rw [abs_of_nonneg (by positivity),le_div_iff₀ hKR_pos]
          have:(K:E)*((p.1:E)^2*(r.1:E))<=2*(N:E):=by exact_mod_cast hfl.1
          push_cast;linarith
        ·
          dsimp only;rw [le_div_iff₀ hKR_pos]
          have:(K:E) * |((p.1:E)^2*(r.1:E)-(p.2:E)^2*(r.2:E))| ≤ (H:E):=by exact_mod_cast hfl.2.2.2.1.le
          push_cast;linarith
      have hbox2:=card_rank2_box_le (p1:=(p.1:E)^2) (p2:=(p.2:E)^2)
        (A:=2*(N:E)/(K:E)) (B:=(H:E)/(K:E))
        (pow_pos (by exact_mod_cast (show 0 < p.1 by omega)) 2)
        (pow_pos (by exact_mod_cast (show 0 < p.2 by omega)) 2)
        (by positivity) (by positivity) S2 hS2_bd
        ⟨((u.1:ℤ),(u.2:ℤ)),Finset.mem_image_of_mem _ hu,((v.1:ℤ),(v.2:ℤ)),Finset.mem_image_of_mem _ hv,hdet2⟩
      rw [hcard2]
      have hden:(P:E)^4<=(p.1:E)^2*(p.2:E)^2:=by
        calc
          (P:E)^4=(P:E)^2*(P:E)^2:=by ring
          _ <= (p.1:E)^2*(p.2:E)^2 := mul_le_mul (pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp1_ge) 2)
            (pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp2_ge) 2) (by positivity) (by positivity)
      calc
        (S2.card:E)<=100*(2*(N:E)/(K:E))*((H:E)/(K:E))/((p.1:E)^2*(p.2:E)^2):=hbox2
        _ = (200*(N:E)*(H:E)/(K:E)^2)/((p.1:E)^2*(p.2:E)^2):=by ring
        _ <= (200*(N:E)*(H:E)/(K:E)^2)/(P:E)^4 :=div_le_div_of_nonneg_left (by positivity) (pow_pos hP_pos 4) hden
        _ = 200*(N:E)*(H:E)/((K:E)^2*(P:E)^4):=by ring
    have hsum2:∑ p∈PP2,((pairFiber k p).card:E)<=200*(N:E)*(H:E)/((K:E)^2*(P:E)^2):=by
      calc
        _ <= ∑ _p∈PP2,(200*(N:E)*(H:E)/((K:E)^2*(P:E)^4)):=sum_le_sum hfib2
        _ = (PP2.card:E)*(200*(N:E)*(H:E)/((K:E)^2*(P:E)^4)):=by simp
        _ <= (P:E)^2*(200*(N:E)*(H:E)/((K:E)^2*(P:E)^4)):=by
          have hle:(PP2.card:E)<=(PrimePairs.card:E):=by exact_mod_cast Finset.card_filter_le _ _
          exact mul_le_mul_of_nonneg_right (hle.trans hPP_card) (by positivity)
        _ = 200*(N:E)*(H:E)/((K:E)^2*(P:E)^2):=by field_simp [hP_pos.ne']
    calc
      (T1_rk2.card:E)<=(3*(H:E)/(K:E))*(200*(N:E)*(H:E)/((K:E)^2*(P:E)^2)) :=h1.trans (mul_le_mul_of_nonneg_left hsum2 (by positivity))
      _ = 600*(N:E)*(H:E)^2/((K:E)^3*(P:E)^2):=by ring
   let PP1:=PrimePairs.filter (fun p=>(pairFiber k p).Nonempty/\¬ pairRank2 k p)
   have hT1_rk1:(T1_rk1.card:E)<=(3*(H:E)/(K:E))*∑ p∈PP1,((pairFiber k p).card:E) := hproj T1_rk1 PP1 (Finset.filter_subset _ _) (by
      intro t ht;rcases mem_filter.mp ht with ⟨ht_T1,hnot2⟩;have ht_pr:=(mem_filter.mp (mem_filter.mp ht_T1).1).1;have hfl:=mem_filter.mp ht_pr;have hp:=mem_product.mp hfl.1;have hp2:=mem_product.mp hp.2
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hp.1,hp2.1⟩,hfl.2.1,hfl.2.2.1,hfl.2.2.2.2.1⟩,⟨_,(hrOf_spec t ht_T1).1⟩,hnot2⟩)
   have hK_cast:(K:E)=(2:E)^k:=by dsimp [K];push_cast;rfl
   have h2K_rk2:2*(2:E)^k*(T1_rk2.card:E) ≤ 2*min ((2:E)^k*(P:E)^3)
            (600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2)):=by
    have h1:(2:E)^k*(T1_rk2.card:E)<=(2:E)^k*(P:E)^3 :=mul_le_mul_of_nonneg_left hT1_rk2_triv (by positivity)
    have h2:(2:E)^k*(T1_rk2.card:E) ≤ 600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2):=by
      rw [hK_cast] at hT1_rk2_lat;have h:=mul_le_mul_of_nonneg_left hT1_rk2_lat (by positivity:(0:E)<=(2:E)^k)
      have hrew:(2:E)^k*(600*(N:E)*(H:E)^2/(((2:E)^k)^3*(P:E)^2)) = 600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2):=by field_simp [pow_ne_zero k (by norm_num:(2:E)≠0)]
      linarith
    linarith [le_min h1 h2]
   have h2K_rk1:2*(2:E)^k*(T1_rk1.card:E) ≤ 6*(H:E)*∑ p∈PP1,((pairFiber k p).card:E):=by
    rw [hK_cast] at hT1_rk1;have h:=mul_le_mul_of_nonneg_left hT1_rk1 (by positivity:(0:E)<=2*(2:E)^k)
    have hrew:2*(2:E)^k*(3*(H:E)/(2:E)^k*∑ p∈PP1,((pairFiber k p).card:E)) = 6*(H:E)*∑ p∈PP1,((pairFiber k p).card:E):=by
      generalize ∑ p∈PP1,((pairFiber k p).card:E)=S
      field_simp [pow_ne_zero k (by norm_num:(2:E)≠0)];ring
    linarith
   have hsplitR:((T1 k).card:E)=(T1_rk2.card:E)+(T1_rk1.card:E):=by exact_mod_cast hT1_split
   dsimp only [PP1] at h2K_rk1;rw [hsplitR];linarith
  ·
   rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero,mul_zero]
   have hmin_nn:0<=min ((2:E)^k*(P:E)^3)
      (600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2)) :=
    le_min (by positivity) (by positivity)
   have hsum_nn:0<=∑ p∈PrimePairs.filter (fun p=>(pairFiber k p).Nonempty/\¬ pairRank2 k p),((pairFiber k p).card:E):=Finset.sum_nonneg (fun _ _=>Nat.cast_nonneg _);exact add_nonneg (mul_nonneg (by norm_num) hmin_nn) (mul_nonneg (by positivity) hsum_nn)
 have hS1b:∑ k∈Finset.range B1,2*min ((2:E)^k*(P:E)^3)
          (600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2)) ≤
   300*(N:E)^(3/5:E)*(H:E)^(6/5:E):=by
  have hterm:∀ k∈Finset.range B1,2*min ((2:E)^k*(P:E)^3)
           (600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2)) ≤
      2*(600:E)^(3/5:E)*(N:E)^(3/5:E)*(H:E)^(6/5:E) * ((2:E)^k)^(-(4/5:E)):=by
   intro k _
   have hm:=min_le_weighted_rpow (A:=(2:E)^k*(P:E)^3)
    (B:=600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2))
    (θ:=2/5) (by positivity) (by positivity) (by norm_num) (by norm_num)
   have hK_pos:(0:E) < (2:E)^k:=by positivity
   have hA_exp:((2:E)^k*(P:E)^3)^(2/5:E) = ((2:E)^k)^(2/5:E)*(P:E)^(6/5:E):=by
    rw [mul_rpow hK_pos.le (by positivity),← rpow_natCast (P:E) 3,← rpow_mul hP_pos.le];norm_num
   have hB_exp:(600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2))^(1-2/5:E) = (600:E)^(3/5:E)*(N:E)^(3/5:E)*(H:E)^(6/5:E) * ((2:E)^k)^(-(6/5:E))*(P:E)^(-(6/5:E)):=by
    norm_num
    rw [div_rpow (by positivity) (by positivity),mul_rpow (by positivity) (by positivity),mul_rpow (by norm_num) hN_pos.le,mul_rpow (by positivity) (by positivity),← rpow_natCast (H:E) 2,← rpow_mul hH_pos.le,← rpow_natCast ((2:E)^k) 2,← rpow_mul hK_pos.le,← rpow_natCast (P:E) 2,← rpow_mul hP_pos.le]
    norm_num;rw [div_eq_mul_inv,mul_inv,← rpow_neg hK_pos.le,← rpow_neg hP_pos.le];ring
   rw [hA_exp,hB_exp] at hm;have hP_cancel:(P:E)^(6/5:E)*(P:E)^(-(6/5:E))=1:=by rw [← rpow_add hP_pos];simp
   have hK_comb:((2:E)^k)^(2/5:E)*((2:E)^k)^(-(6/5:E)) = ((2:E)^k)^(-(4/5:E)):=by rw [← rpow_add hK_pos];norm_num
   have hprod_eq:((2:E)^k)^(2/5:E)*(P:E)^(6/5:E) * ((600:E)^(3/5:E)*(N:E)^(3/5:E)*(H:E)^(6/5:E) * ((2:E)^k)^(-(6/5:E))*(P:E)^(-(6/5:E))) = (600:E)^(3/5:E)*(N:E)^(3/5:E)*(H:E)^(6/5:E) * ((2:E)^k)^(-(4/5:E)):=by
    calc
      _ = (600:E)^(3/5:E)*(N:E)^(3/5:E)*(H:E)^(6/5:E) * (((2:E)^k)^(2/5:E)*((2:E)^k)^(-(6/5:E))) * ((P:E)^(6/5:E)*(P:E)^(-(6/5:E))):=by ring
      _ = _:=by rw [hK_comb,hP_cancel,mul_one]
   rw [hprod_eq] at hm;linarith
  have hgeom:=sum_dyadic_inv_rpow_le B1 (α:=4/5) (by norm_num)
  have hgeom_le:1/(1-(2:E)^(-(4/5:E)))<=3:=by
   have h2:(2:E)^(-(4/5:E))<=2/3:=by
    rw [rpow_neg (by norm_num)]
    have hle:(3/2:E)<=(2:E)^(4/5:E):=by
      have h5:(3/2:E)^5<=(2:E)^4:=by norm_num
      have hrp:=rpow_le_rpow (by positivity) h5 (by norm_num:(0:E)<=1/5);rw [← rpow_natCast (3/2:E) 5,← rpow_mul (by norm_num),← rpow_natCast (2:E) 4,← rpow_mul (by norm_num)] at hrp;norm_num at hrp;exact hrp
    have hinv:=inv_anti₀ (by norm_num:(0:E) < 3/2) hle;norm_num at hinv;exact hinv
   have hpos:0 < 1-(2:E)^(-(4/5:E)):=by linarith
   rw [div_le_iff₀ hpos];linarith
  have h600:(600:E)^(3/5:E)<=50:=by
   have hle:(600:E)^3<=(50:E)^5:=by norm_num
   have hrp:=rpow_le_rpow (by positivity) hle (by norm_num:(0:E)<=1/5);rw [← rpow_natCast (600:E) 3,← rpow_mul (by norm_num),← rpow_natCast (50:E) 5,← rpow_mul (by norm_num)] at hrp;norm_num at hrp;exact hrp
  calc
   _ <= ∑ k∈Finset.range B1,(2*(600:E)^(3/5:E)*(N:E)^(3/5:E)*(H:E)^(6/5:E) * ((2:E)^k)^(-(4/5:E))):=sum_le_sum hterm
   _ = (2*(600:E)^(3/5:E)*(N:E)^(3/5:E)*(H:E)^(6/5:E)) * ∑ k∈Finset.range B1,((2:E)^k)^(-(4/5:E)):=(Finset.mul_sum _ _ _).symm
   _ <= (2*50*(N:E)^(3/5:E)*(H:E)^(6/5:E))*3:=by
    apply mul_le_mul _ (hgeom.trans hgeom_le) (by positivity) (by positivity)
    have:0<=(N:E)^(3/5:E)*(H:E)^(6/5:E):=by positivity
    nlinarith
   _ = 300*(N:E)^(3/5:E)*(H:E)^(6/5:E):=by ring
 have hS1a_k:∀ k∈Finset.range B1,6*(H:E)*(∑ p∈PrimePairs.filter (fun p=>(pairFiber k p).Nonempty/\¬ pairRank2 k p),((pairFiber k p).card:E)) ≤ 260*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E)) + 950*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E)):=by
  intro k _;let K:=2^k;have hKR_pos:(0:E) < (K:E):=by positivity
  let PP1:=PrimePairs.filter (fun p=>(pairFiber k p).Nonempty/\¬ pairRank2 k p)
  have hpair_prim:∀ p∈PP1,∃ t u e0:ℕ,1<=t/\1<=u ∧ (pairFiber k p).card<=e0/\e0<=D'/\(e0*t,e0*u)∈pairFiber k p:=by
   intro p hp;rcases mem_filter.mp hp with ⟨_,⟨r0,hr0⟩,hno2⟩
   have hprop:∀ a∈pairFiber k p,∀ b∈pairFiber k p,a.1*b.2=a.2*b.1:=by
    intro a ha b hb;have h:¬ ((a.1:ℤ)*(b.2:ℤ)-(a.2:ℤ)*(b.1:ℤ)≠0):=fun hne=>hno2 ⟨a,ha,b,hb,hne⟩
    push Not at h;exact_mod_cast (sub_eq_zero.mp h)
   have hr0_pos:1<=r0.1/\1<=r0.2:=by
    have h:=mem_product.mp (mem_filter.mp hr0).1;exact ⟨(Finset.mem_Icc.mp h.1).1,(Finset.mem_Icc.mp h.2).1⟩
   let g0:=Nat.gcd r0.1 r0.2;have hg0_pos:0 < g0:=Nat.gcd_pos_of_pos_left _ (by omega);let t:=r0.1/g0;let u:=r0.2/g0;have ht_mul:g0*t=r0.1:=Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _);have hu_mul:g0*u=r0.2:=Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
   have htu_pos:1<=t/\1<=u := ⟨by by_contra h;push Not at h;have h0:t=0:=Nat.lt_one_iff.mp h;rw [h0,mul_zero] at ht_mul;omega,by by_contra h;push Not at h;have h0:u=0:=Nat.lt_one_iff.mp h;rw [h0,mul_zero] at hu_mul;omega⟩
   have hprim_tu:Nat.gcd t u=1:=by
    set d:=Nat.gcd t u;have h1:g0*d∣r0.1:=ht_mul ▸ mul_dvd_mul_left g0 (Nat.gcd_dvd_left _ _);have h2:g0*d∣r0.2:=hu_mul ▸ mul_dvd_mul_left g0 (Nat.gcd_dvd_right _ _);have hle:g0*d<=g0:=Nat.le_of_dvd hg0_pos (Nat.dvd_gcd h1 h2)
    have hd_pos:0 < d:=Nat.gcd_pos_of_pos_left _ (by omega);nlinarith
   have hmul_all:∀ r∈pairFiber k p,
      let e:=Nat.gcd r.1 r.2
      r=(e*t,e*u)/\1<=e/\e<=D':=by
    intro r hr
    have hr_pos:1<=r.1/\1<=r.2:=by
      have h:=mem_product.mp (mem_filter.mp hr).1;exact ⟨(Finset.mem_Icc.mp h.1).1,(Finset.mem_Icc.mp h.2).1⟩
    set e:=Nat.gcd r.1 r.2;have he_pos:1<=e:=Nat.gcd_pos_of_pos_left _ (by omega);have he_le:e<=D':=(mem_filter.mp hr).2.2.2.2.2;let s1:=r.1/e;let s2:=r.2/e;have hs1:e*s1=r.1:=Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hs2:e*s2=r.2:=Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have hs_pos:1<=s1/\1<=s2 := ⟨by by_contra h;push Not at h;have h0:s1=0:=Nat.lt_one_iff.mp h;rw [h0,mul_zero] at hs1;omega,by by_contra h;push Not at h;have h0:s2=0:=Nat.lt_one_iff.mp h;rw [h0,mul_zero] at hs2;omega⟩
    have hprim_s:Nat.gcd s1 s2=1:=by
      set d:=Nat.gcd s1 s2;have h1:e*d∣r.1:=hs1 ▸ mul_dvd_mul_left e (Nat.gcd_dvd_left _ _);have h2:e*d∣r.2:=hs2 ▸ mul_dvd_mul_left e (Nat.gcd_dvd_right _ _);have hle:e*d<=e:=Nat.le_of_dvd (by omega) (Nat.dvd_gcd h1 h2)
      have hd_pos:0 < d:=Nat.gcd_pos_of_pos_left _ (by omega);nlinarith
    have hts:t*s2=u*s1:=by
      have:(g0*e)*(t*s2)=(g0*e)*(u*s1):=by
        calc
          (g0*e)*(t*s2)=(g0*t)*(e*s2):=by ring
          _ = r0.1*r.2:=by rw [ht_mul,hs2]
          _ = r0.2*r.1:=hprop r0 hr0 r hr
          _ = (g0*u)*(e*s1):=by rw [hu_mul,hs1]
          _ = (g0*e)*(u*s1):=by ring
      exact mul_left_cancel₀ (by positivity) this
    have ht_eq:t=s1:=by
      have h1:Nat.gcd (t*s1) (t*s2)=t:=by rw [Nat.gcd_mul_left,hprim_s,mul_one]
      have h2:Nat.gcd (s1*t) (s1*u)=s1:=by rw [Nat.gcd_mul_left,hprim_tu,mul_one]
      calc
        t=Nat.gcd (t*s1) (t*s2):=h1.symm
        _ = Nat.gcd (s1*t) (s1*u):=by rw [mul_comm t s1,hts,mul_comm u s1]
        _ = s1:=h2
    have hu_eq:u=s2:=by
      have:t*s2=t*u:=by rw [hts,← ht_eq,mul_comm]
      exact (mul_left_cancel₀ (by omega) this).symm
    refine ⟨?_,he_pos,he_le⟩;rcases r with ⟨a,b⟩;simp only [Prod.mk.injEq];exact ⟨by rw [ht_eq,hs1],by rw [hu_eq,hs2]⟩
   let eSet:=(pairFiber k p).image (fun r=>Nat.gcd r.1 r.2);have heSet_ne:eSet.Nonempty:=⟨_,Finset.mem_image_of_mem _ hr0⟩;let e0:=eSet.max' heSet_ne;rcases Finset.mem_image.mp (Finset.max'_mem eSet heSet_ne) with ⟨rm,hrm,he0_eq⟩
   have he0_eq':Nat.gcd rm.1 rm.2=e0:=he0_eq;have hrm_spec:=hmul_all rm hrm
   have hcard_le:(pairFiber k p).card<=e0:=by
    have hinj:Set.InjOn (fun r:ℕ × ℕ=>Nat.gcd r.1 r.2) (pairFiber k p):=by
      intro a ha b hb heq;dsimp only at heq;rw [(hmul_all a ha).1,(hmul_all b hb).1,heq]
    have hsub:eSet⊆Finset.Icc 1 e0:=by
      intro e he;rcases Finset.mem_image.mp he with ⟨r,hr,rfl⟩;exact Finset.mem_Icc.mpr ⟨(hmul_all r hr).2.1,Finset.le_max' eSet _ he⟩
    calc
      (pairFiber k p).card=eSet.card:=(Finset.card_image_iff.mpr hinj).symm
      _ <= (Finset.Icc 1 e0).card:=Finset.card_le_card hsub
      _ = e0:=by rw [Nat.card_Icc];omega
   refine ⟨t,u,e0,htu_pos.1,htu_pos.2,hcard_le,he0_eq' ▸ hrm_spec.2.2,?_⟩;rw [← he0_eq',← hrm_spec.1];exact hrm
  let B2:ℕ:=Nat.log 2 D'+1
  let Llay:ℕ->Finset (ℕ × ℕ):=fun s =>
   PP1.filter (fun p=>2^s<=(pairFiber k p).card/\(pairFiber k p).card < 2^(s+1))
  have hPP1_layers:∑ p∈PP1,((pairFiber k p).card:E) ≤ ∑ s∈Finset.range B2,(2*(2:E)^s*((Llay s).card:E)):=by
   have hcov:PP1=(Finset.range B2).biUnion Llay:=by
    ext p;simp only [Finset.mem_biUnion,Finset.mem_range,Llay,mem_filter];constructor
    ·
      intro hp;obtain ⟨_,_,e0,_,_,hce,heD',_⟩:=hpair_prim p hp;have hpos:1<=(pairFiber k p).card:=Finset.card_pos.mpr (mem_filter.mp hp).2.1;have hleD':(pairFiber k p).card<=D':=hce.trans heD';let s:=Nat.log 2 (pairFiber k p).card
      refine ⟨s,?_,hp,Nat.pow_log_le_self 2 (by omega),Nat.lt_pow_succ_log_self (by norm_num) _⟩
      have:=Nat.log_mono_right (b:=2) hleD';dsimp [B2];omega
    · rintro ⟨_,_,hp,_,_⟩;exact hp
   have hdisj:Set.PairwiseDisjoint (↑(Finset.range B2):Set ℕ) Llay:=by
    intro s1 _ s2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro p hp1 hp2;have h1:=(mem_filter.mp hp1).2;have h2:=(mem_filter.mp hp2).2;rcases lt_or_gt_of_ne hne with hlt | hgt
    · have:2^(s1+1)<=2^s2:=Nat.pow_le_pow_right (by norm_num) (by omega);omega
    · have:2^(s2+1)<=2^s1:=Nat.pow_le_pow_right (by norm_num) (by omega);omega
   rw [hcov,Finset.sum_biUnion hdisj];apply sum_le_sum;intro s _
   calc
    ∑ p∈Llay s,((pairFiber k p).card:E)<=∑ _p∈Llay s,(2*(2:E)^s):=by
      apply sum_le_sum;intro p hp
      have:((pairFiber k p).card:E)<=(2:E)^(s+1):=by exact_mod_cast (mem_filter.mp hp).2.2.le
      rw [pow_succ'] at this;linarith
    _ = 2*(2:E)^s*((Llay s).card:E):=by simp;ring
  have hLlay_bound:∀ s∈Finset.range B2,((Llay s).card:E) ≤ 80*(N:E)^2/(((2:E)^k)^2*((2:E)^s)^2*(P:E)^4) + 640*(N:E)*(H:E)/(((2:E)^k)^2*((2:E)^s)^2*(P:E)^2):=by
   intro s _;let L:ℕ:=2^s;have hLR_pos:(0:E) < (L:E):=by positivity
   let Tmax:ℕ:=2*N/(K*L*P^2);let Δ:E:=(H:E)/((K:E)*(L:E))
   have hex_tu:∀ p∈Llay s,∃ tu:ℕ × ℕ,1<=tu.1/\tu.1<=Tmax/\1<=tu.2/\tu.2<=20*tu.1 ∧
      |((p.1:E)^2*(tu.1:E)-(p.2:E)^2*(tu.2:E))| < Δ:=by
    intro p hp;rcases mem_filter.mp hp with ⟨hp_PP1,hLge,_⟩;obtain ⟨t,u,e0,ht1,hu1,hce,_,hmem⟩:=hpair_prim p hp_PP1;have hL_le_e0:L<=e0:=hLge.trans hce;have hfl:=(mem_filter.mp hmem).2;have hp_PP:=(mem_filter.mp hp_PP1).1
    have hp_prod:=mem_product.mp (mem_filter.mp hp_PP).1;have hp1_ico:=Finset.mem_Ico.mp hp_prod.1;have hp2_ico:=Finset.mem_Ico.mp hp_prod.2
    have ht_le:t<=Tmax:=by
      apply Nat.le_div_iff_mul_le (by positivity) |>.mpr
      calc
        t*(K*L*P^2)<=t*(K*e0*p.1^2) :=Nat.mul_le_mul_left t (Nat.mul_le_mul (Nat.mul_le_mul_left K hL_le_e0) (Nat.pow_le_pow_left hp1_ico.1 2))
        _ = K*(p.1^2*(e0*t)):=by ring
        _ <= 2*N:=hfl.1
    have hdiff_lt:|((p.1:E)^2*(t:E)-(p.2:E)^2*(u:E))| < Δ:=by
      have h1:(K:ℤ) * |((p.1:ℤ)^2*((e0*t:ℕ):ℤ)-(p.2:ℤ)^2*((e0*u:ℕ):ℤ))| < (H:ℤ) :=hfl.2.2.2.1;have hrew:(p.1:ℤ)^2*((e0*t:ℕ):ℤ)-(p.2:ℤ)^2*((e0*u:ℕ):ℤ) = (e0:ℤ)*((p.1:ℤ)^2*(t:ℤ)-(p.2:ℤ)^2*(u:ℤ)):=by push_cast;ring
      rw [hrew,abs_mul,abs_of_nonneg (Nat.cast_nonneg e0)] at h1;have h1R:(K:E)*((e0:E) * |((p.1:E)^2*(t:E)-(p.2:E)^2*(u:E))|) < (H:E):=by exact_mod_cast h1
      have hKL:(K:E)*(L:E)<=(K:E)*(e0:E) :=mul_le_mul_of_nonneg_left (by exact_mod_cast hL_le_e0) hKR_pos.le;have h2:(K:E)*(L:E) * |((p.1:E)^2*(t:E)-(p.2:E)^2*(u:E))| < (H:E):=by nlinarith [abs_nonneg ((p.1:E)^2*(t:E)-(p.2:E)^2*(u:E))]
      dsimp [Δ];rw [lt_div_iff₀ (by positivity)];linarith
    have hu_le:u<=20*t:=by
      have h1:(p.2:E)^2*(u:E)<=(p.1:E)^2*(t:E)+Δ:=by linarith [(abs_le.mp hdiff_lt.le).1]
      have hP2u:(P:E)^2*(u:E)<=(p.2:E)^2*(u:E) :=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp2_ico.1) 2) (Nat.cast_nonneg u)
      have hp1t:(p.1:E)^2*(t:E)<=4*(P:E)^2*(t:E):=by
        have h1p:(p.1:E)<=2*(P:E):=by exact_mod_cast hp1_ico.2.le
        have hsq:(p.1:E)^2<=4*(P:E)^2:=by nlinarith [(Nat.cast_nonneg p.1:(0:E)<=p.1)]
        exact mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg t)
      have hΔ_le:Δ<=(P:E)^2*(t:E):=by
        have hKL_ge1:(1:E)<=(K:E)*(L:E):=by
          have:1<=K*L:=Nat.mul_pos (pow_pos (by norm_num:0 < 2) k) (pow_pos (by norm_num:0 < 2) s)
          exact_mod_cast this
        have hΔH:Δ<=(H:E):=div_le_self hH_pos.le hKL_ge1;have hHP_R:(H:E)<=4*(P:E):=by exact_mod_cast hHP
        have h4P:4*(P:E)<=(P:E)^2:=by
          have:(4:E)<=(P:E):=by exact_mod_cast hP
          nlinarith
        have htR:(1:E)<=(t:E):=by exact_mod_cast ht1
        nlinarith [sq_nonneg (P:E)]
      have:(P:E)^2*(u:E)<=20*(P:E)^2*(t:E):=by linarith [mul_nonneg (sq_nonneg (P:E)) (Nat.cast_nonneg t)]
      have huR:(u:E)<=20*(t:E):=by nlinarith [sq_pos_of_pos hP_pos]
      exact_mod_cast huR
    exact ⟨(t,u),ht1,ht_le,hu1,hu_le,hdiff_lt⟩
   let tuOf:(ℕ × ℕ)->ℕ × ℕ:=fun p=>if h:p∈Llay s then Classical.choose (hex_tu p h) else (1,1)
   have htu_spec:∀ p∈Llay s,1<=(tuOf p).1/\(tuOf p).1<=Tmax/\1<=(tuOf p).2/\(tuOf p).2<=20*(tuOf p).1 ∧
      |((p.1:E)^2*((tuOf p).1:E)-(p.2:E)^2*((tuOf p).2:E))| < Δ:=by
    intro p hp;simp only [tuOf,hp,↓reduceDIte];exact Classical.choose_spec (hex_tu p hp)
   let TUset:Finset (ℕ × ℕ) :=(Finset.Icc 1 Tmax).biUnion (fun t=>(Finset.Icc 1 (20*t)).image (fun u=>(t,u)))
   have hfib_tu:∀ tu∈TUset,(((Llay s).filter (fun p=>tuOf p=tu)).card:E)<=1+16*Δ/(tu.1:E):=by
    intro tu htu;rcases Finset.mem_biUnion.mp htu with ⟨t0,ht0,htu_img⟩;rcases Finset.mem_image.mp htu_img with ⟨u0,hu0,rfl⟩;dsimp only;have ht0_pos:(0:E) < (t0:E):=by exact_mod_cast (Finset.mem_Icc.mp ht0).1
    let F:=(Llay s).filter (fun p=>tuOf p=(t0,u0));let α0:E:=Real.sqrt ((u0:E)/(t0:E))
    have hF_bd:∀ p∈F,|(p.1:E)/(p.2:E)-α0| ≤ 2*Δ/((P:E)^2*(t0:E)):=by
      intro p hp;rcases mem_filter.mp hp with ⟨hp_L,htu_eq⟩;have hsp:=htu_spec p hp_L;rw [htu_eq] at hsp;have hp_PP:=(mem_filter.mp (mem_filter.mp hp_L).1).1;have hp_prod:=mem_product.mp (mem_filter.mp hp_PP).1;have hp1_ico:=Finset.mem_Ico.mp hp_prod.1
      have hp2_ico:=Finset.mem_Ico.mp hp_prod.2;have hp1_pos:(0:E) < (p.1:E):=by exact_mod_cast (show 0 < p.1 by omega)
      have hp2_pos:(0:E) < (p.2:E):=by exact_mod_cast (show 0 < p.2 by omega)
      have hsum_ge:(1/2:E)<=(p.1:E)/(p.2:E)+α0:=by
        have h1:(1/2:E)<=(p.1:E)/(p.2:E):=by
          rw [div_le_div_iff₀ (by norm_num) hp2_pos];have h1':(P:E)<=(p.1:E):=by exact_mod_cast hp1_ico.1
          have h2':(p.2:E)<=2*(P:E):=by exact_mod_cast hp2_ico.2.le
          linarith
        linarith [Real.sqrt_nonneg ((u0:E)/(t0:E))]
      have hdiff_sq:((p.1:E)/(p.2:E)-α0)*((p.1:E)/(p.2:E)+α0) = ((p.1:E)^2*(t0:E)-(p.2:E)^2*(u0:E))/((p.2:E)^2*(t0:E)):=by
        have hsq:α0^2=(u0:E)/(t0:E):=Real.sq_sqrt (by positivity);have h1:((p.1:E)/(p.2:E)-α0)*((p.1:E)/(p.2:E)+α0) = ((p.1:E)/(p.2:E))^2-α0^2:=by ring
        rw [h1,hsq];field_simp [hp2_pos.ne',ht0_pos.ne']
      have hmul_abs:|(p.1:E)/(p.2:E)-α0| * ((p.1:E)/(p.2:E)+α0) ≤ Δ/((P:E)^2*(t0:E)):=by
        dsimp only at hsp;rw [← abs_of_pos (by linarith:0 < (p.1:E)/(p.2:E)+α0),← abs_mul,hdiff_sq,abs_div,abs_of_pos (mul_pos (sq_pos_of_pos hp2_pos) ht0_pos)]
        have hden:(P:E)^2*(t0:E)<=(p.2:E)^2*(t0:E) :=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hP_pos.le (by exact_mod_cast hp2_ico.1) 2) ht0_pos.le;exact div_le_div₀ (by positivity) hsp.2.2.2.2.le (by positivity) hden
      have hhalf:(1/2:E) * |(p.1:E)/(p.2:E)-α0| ≤ Δ/((P:E)^2*(t0:E)):=by
        calc
          (1/2:E) * |(p.1:E)/(p.2:E)-α0|
            = |(p.1:E)/(p.2:E)-α0| * (1/2):=mul_comm _ _
          _ <= |(p.1:E)/(p.2:E)-α0| * ((p.1:E)/(p.2:E)+α0) :=mul_le_mul_of_nonneg_left hsum_ge (abs_nonneg _)
          _ <= Δ/((P:E)^2*(t0:E)):=hmul_abs
      have h2Δ:2*Δ/((P:E)^2*(t0:E))=2*(Δ/((P:E)^2*(t0:E))):=by ring
      linarith
    have hF_sep:∀ p1∈F,∀ p2∈F,p1≠p2 → 1/(4*(P:E)^2) ≤ |(p1.1:E)/(p1.2:E)-(p2.1:E)/(p2.2:E)|:=by
      intro p1 hp1 p2 hp2 hne;have hfl1:=mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hp1).1).1).1;have hfl2:=mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hp2).1).1).1;have hp12_ico:=Finset.mem_Ico.mp (mem_product.mp hfl1.1).2
      have hp22_ico:=Finset.mem_Ico.mp (mem_product.mp hfl2.1).2
      have hnum_ne:(p1.1:ℤ)*(p2.2:ℤ)-(p2.1:ℤ)*(p1.2:ℤ)≠0:=by
        intro h0;have heqN:p1.1*p2.2=p2.1*p1.2:=by exact_mod_cast (sub_eq_zero.mp h0)
        have hd1:p1.1∣p2.1*p1.2:=⟨p2.2,by linarith⟩;rcases hfl1.2.1.dvd_mul.mp hd1 with h11 | h12
        ·
          have hp1_eq:p1.1=p2.1:=(Nat.prime_dvd_prime_iff_eq hfl1.2.1 hfl2.2.1).mp h11
          have hp2_eq:p1.2=p2.2:=by
           rw [hp1_eq] at heqN;exact (mul_left_cancel₀ hfl2.2.1.ne_zero heqN).symm
          exact hne (Prod.ext hp1_eq hp2_eq)
        · exact hfl1.2.2.2 ((Nat.prime_dvd_prime_iff_eq hfl1.2.1 hfl1.2.2.1).mp h12)
      have hnum_ge1:(1:E) ≤ |(p1.1:E)*(p2.2:E)-(p2.1:E)*(p1.2:E)|:=by exact_mod_cast Int.one_le_abs hnum_ne
      have hp12_pos:(0:E) < (p1.2:E):=by exact_mod_cast hfl1.2.2.1.pos
      have hp22_pos:(0:E) < (p2.2:E):=by exact_mod_cast hfl2.2.2.1.pos
      have heq:(p1.1:E)/(p1.2:E)-(p2.1:E)/(p2.2:E) = ((p1.1:E)*(p2.2:E)-(p2.1:E)*(p1.2:E))/((p1.2:E)*(p2.2:E)):=by field_simp [hp12_pos.ne',hp22_pos.ne']
      rw [heq,abs_div,abs_of_pos (mul_pos hp12_pos hp22_pos)]
      have hden:(p1.2:E)*(p2.2:E)<=4*(P:E)^2:=by
        have h1:(p1.2:E)<=2*(P:E):=by exact_mod_cast hp12_ico.2.le
        have h2:(p2.2:E)<=2*(P:E):=by exact_mod_cast hp22_ico.2.le
        calc
          _ <= (2*(P:E))*(2*(P:E)):=mul_le_mul h1 h2 hp22_pos.le (by positivity)
          _ = 4*(P:E)^2:=by ring
      exact div_le_div₀ (by norm_num) hnum_ge1 (mul_pos hp12_pos hp22_pos) hden
    have hsep:=card_separated_interval_le F (fun p=>(p.1:E)/(p.2:E))
      (by positivity) (by positivity) hF_bd hF_sep
    have hrew:1+2*(2*Δ/((P:E)^2*(t0:E)))/(1/(4*(P:E)^2)) = 1+16*Δ/(t0:E):=by field_simp [hP_pos.ne',ht0_pos.ne'];ring
    linarith
   have hpart:(Llay s).card=∑ tu∈TUset,((Llay s).filter (fun p=>tuOf p=tu)).card:=by
    rw [← card_biUnion]
    ·
      congr 1;ext p;simp only [Finset.mem_biUnion,mem_filter];constructor
      ·
        intro hp;have hsp:=htu_spec p hp;refine ⟨tuOf p,?_,hp,rfl⟩;exact Finset.mem_biUnion.mpr ⟨(tuOf p).1,Finset.mem_Icc.mpr ⟨hsp.1,hsp.2.1⟩,Finset.mem_image.mpr ⟨(tuOf p).2,Finset.mem_Icc.mpr ⟨hsp.2.2.1,hsp.2.2.2.1⟩,Prod.mk.eta⟩⟩
      · rintro ⟨_,_,hp,_⟩;exact hp
    ·
      intro a _ b _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro p h1 h2;exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
   have hsum_TU:∑ tu∈TUset,(1+16*Δ/(tu.1:E)) ≤ 20*(Tmax:E)^2+320*(Tmax:E)*Δ:=by
    have hdisj:Set.PairwiseDisjoint (↑(Finset.Icc 1 Tmax):Set ℕ)
        (fun t=>(Finset.Icc 1 (20*t)).image (fun u=>(t,u))):=by
      intro t1 _ t2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro x hx1 hx2;rcases Finset.mem_image.mp hx1 with ⟨u1,_,rfl⟩;rcases Finset.mem_image.mp hx2 with ⟨u2,_,heq⟩;exact hne (congrArg Prod.fst heq).symm
    rw [Finset.sum_biUnion hdisj]
    have hinner:∀ t∈Finset.Icc 1 Tmax,∑ tu∈(Finset.Icc 1 (20*t)).image (fun u=>(t,u)),(1+16*Δ/(tu.1:E)) = 20*(t:E)+320*Δ:=by
      intro t ht;have ht_pos:(0:E) < (t:E):=by exact_mod_cast (Finset.mem_Icc.mp ht).1
      rw [Finset.sum_image (fun a _ b _ h=>(Prod.mk.inj h).2)];simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul];push_cast;field_simp [ht_pos.ne'];ring
    rw [sum_congr rfl hinner,sum_add_distrib]
    have hs1:∑ t∈Finset.Icc 1 Tmax,(20*(t:E))<=20*(Tmax:E)^2:=by
      calc
        _ <= ∑ _t∈Finset.Icc 1 Tmax,(20*(Tmax:E)):=by
          apply sum_le_sum;intro t ht
          have:(t:E)<=(Tmax:E):=by exact_mod_cast (Finset.mem_Icc.mp ht).2
          linarith
        _ = ((Finset.Icc 1 Tmax).card:E)*(20*(Tmax:E)):=by simp
        _ = 20*(Tmax:E)^2:=by rw [Nat.card_Icc];simp only [Nat.add_sub_cancel];ring
    have hs2:∑ _t∈Finset.Icc 1 Tmax,(320*Δ)=320*(Tmax:E)*Δ:=by simp only [sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul];ring
    linarith
   have hTmax_le:(Tmax:E)<=2*(N:E)/((K:E)*(L:E)*(P:E)^2):=by
    rw [le_div_iff₀ (by positivity)]
    have:Tmax*(K*L*P^2)<=2*N:=Nat.div_mul_le_self (2*N) (K*L*P^2)
    exact_mod_cast this
   have hKL_cast:(K:E)*(L:E)=(2:E)^k*(2:E)^s:=by dsimp [K,L];push_cast;rfl
   calc
    ((Llay s).card:E)=∑ tu∈TUset,(((Llay s).filter (fun p=>tuOf p=tu)).card:E):=by rw [hpart,Nat.cast_sum]
    _ <= ∑ tu∈TUset,(1+16*Δ/(tu.1:E)):=sum_le_sum hfib_tu
    _ <= 20*(Tmax:E)^2+320*(Tmax:E)*Δ:=hsum_TU
    _ <= 20*(2*(N:E)/((K:E)*(L:E)*(P:E)^2))^2 + 320*(2*(N:E)/((K:E)*(L:E)*(P:E)^2))*((H:E)/((K:E)*(L:E))):=by
      have:=pow_le_pow_left₀ (Nat.cast_nonneg Tmax) hTmax_le 2
      dsimp [Δ];gcongr
    _ = 80*(N:E)^2/(((2:E)^k)^2*((2:E)^s)^2*(P:E)^4) + 640*(N:E)*(H:E)/(((2:E)^k)^2*((2:E)^s)^2*(P:E)^2):=by rw [hKL_cast];ring
  have hLlay_bal:∀ s∈Finset.range B2,12*(H:E)*(2:E)^s*((Llay s).card:E) ≤ 52*(H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E))*((2:E)^s)^(1/3:E) + 310*(H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E)):=by
   intro s hs
   have htriv:((Llay s).card:E)<=(P:E)^2 := (by exact_mod_cast ((Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)) :
      ((Llay s).card:E)<=(PrimePairs.card:E)).trans hPP_card
   have hbd:=hLlay_bound s hs;let X1:E:=80*(N:E)^2/(((2:E)^k)^2*((2:E)^s)^2*(P:E)^4);let X2:E:=640*(N:E)*(H:E)/(((2:E)^k)^2*((2:E)^s)^2*(P:E)^2)
   have hmin_sum:((Llay s).card:E)<=min ((P:E)^2) X1+min ((P:E)^2) X2:=by
    have h1:min ((P:E)^2) (X1+X2)<=min ((P:E)^2) X1+min ((P:E)^2) X2:=by
      rcases le_total ((P:E)^2) X1 with h1 | h1 <;> rcases le_total ((P:E)^2) X2 with h2 | h2
      · rw [min_eq_left h1,min_eq_left h2];linarith [min_le_left ((P:E)^2) (X1+X2),sq_nonneg (P:E)]
      · rw [min_eq_left h1,min_eq_right h2];linarith [min_le_left ((P:E)^2) (X1+X2),show 0<=X2 by positivity]
      · rw [min_eq_right h1,min_eq_left h2];linarith [min_le_left ((P:E)^2) (X1+X2),show 0<=X1 by positivity]
      · rw [min_eq_right h1,min_eq_right h2];exact min_le_right _ _
    exact (le_min htriv hbd).trans h1
   have hK_pos:(0:E) < (2:E)^k:=by positivity
   have hL_pos:(0:E) < (2:E)^s:=by positivity
   have hm1:min ((P:E)^2) X1<=(80:E)^(1/3:E)*(N:E)^(2/3:E) * ((2:E)^k)^(-(2/3:E))*((2:E)^s)^(-(2/3:E)):=by
    have h:=min_le_weighted_rpow (A:=(P:E)^2) (B:=X1) (θ:=2/3)
      (by positivity) (by positivity) (by norm_num) (by norm_num)
    have hA:((P:E)^2)^(2/3:E)=(P:E)^(4/3:E):=by rw [← rpow_natCast (P:E) 2,← rpow_mul hP_pos.le];norm_num
    have hB:X1^(1-2/3:E)=(80:E)^(1/3:E)*(N:E)^(2/3:E) * ((2:E)^k)^(-(2/3:E))*((2:E)^s)^(-(2/3:E))*(P:E)^(-(4/3:E)):=by
      dsimp [X1];norm_num
      rw [div_rpow (by positivity) (by positivity),mul_rpow (by norm_num) (by positivity),mul_rpow (by positivity) (by positivity),mul_rpow (by positivity) (by positivity),← rpow_natCast (N:E) 2,← rpow_mul hN_pos.le,← rpow_natCast ((2:E)^k) 2,← rpow_mul hK_pos.le,← rpow_natCast ((2:E)^s) 2,← rpow_mul hL_pos.le,← rpow_natCast (P:E) 4,← rpow_mul hP_pos.le]
      norm_num;rw [div_eq_mul_inv,mul_inv,mul_inv,← rpow_neg hK_pos.le,← rpow_neg hL_pos.le,← rpow_neg hP_pos.le];ring
    rw [hA,hB] at h;have hPc:(P:E)^(4/3:E)*(P:E)^(-(4/3:E))=1:=by rw [← rpow_add hP_pos];simp
    have hre:(P:E)^(4/3:E)*((80:E)^(1/3:E)*(N:E)^(2/3:E) * ((2:E)^k)^(-(2/3:E))*((2:E)^s)^(-(2/3:E))*(P:E)^(-(4/3:E))) = (80:E)^(1/3:E)*(N:E)^(2/3:E) * ((2:E)^k)^(-(2/3:E))*((2:E)^s)^(-(2/3:E)):=by
      calc
        _ = (80:E)^(1/3:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E)) * ((2:E)^s)^(-(2/3:E))*((P:E)^(4/3:E)*(P:E)^(-(4/3:E))):=by ring
        _ = _:=by rw [hPc,mul_one]
    rwa [hre] at h
   have hm2:min ((P:E)^2) X2<=(640:E)^(1/2:E)*(N:E)^(1/2:E)*(H:E)^(1/2:E) * ((2:E)^k)^(-(1:E))*((2:E)^s)^(-(1:E)):=by
    have h:=min_le_weighted_rpow (A:=(P:E)^2) (B:=X2) (θ:=1/2)
      (by positivity) (by positivity) (by norm_num) (by norm_num)
    have hA:((P:E)^2)^(1/2:E)=(P:E):=by rw [← rpow_natCast (P:E) 2,← rpow_mul hP_pos.le];norm_num
    have hB:X2^(1-1/2:E)=(640:E)^(1/2:E)*(N:E)^(1/2:E)*(H:E)^(1/2:E) * ((2:E)^k)^(-(1:E))*((2:E)^s)^(-(1:E))*(P:E)⁻¹:=by
      dsimp [X2];norm_num
      rw [div_rpow (by positivity) (by positivity),mul_rpow (by positivity) hH_pos.le,mul_rpow (by norm_num) hN_pos.le,mul_rpow (by positivity) (by positivity),mul_rpow (by positivity) (by positivity),← rpow_natCast ((2:E)^k) 2,← rpow_mul hK_pos.le,← rpow_natCast ((2:E)^s) 2,← rpow_mul hL_pos.le,← rpow_natCast (P:E) 2,← rpow_mul hP_pos.le]
      norm_num;rw [div_eq_mul_inv,mul_inv,mul_inv,Real.rpow_neg_one,Real.rpow_neg_one];ring
    rw [hA,hB] at h;have hPc:(P:E)*(P:E)⁻¹=1:=mul_inv_cancel₀ hP_pos.ne'
    have hre:(P:E)*((640:E)^(1/2:E)*(N:E)^(1/2:E)*(H:E)^(1/2:E) * ((2:E)^k)^(-(1:E))*((2:E)^s)^(-(1:E))*(P:E)⁻¹) = (640:E)^(1/2:E)*(N:E)^(1/2:E)*(H:E)^(1/2:E) * ((2:E)^k)^(-(1:E))*((2:E)^s)^(-(1:E)):=by
      calc
        _ = (640:E)^(1/2:E)*(N:E)^(1/2:E)*(H:E)^(1/2:E) * ((2:E)^k)^(-(1:E))*((2:E)^s)^(-(1:E))*((P:E)*(P:E)⁻¹):=by ring
        _ = _:=by rw [hPc,mul_one]
    rwa [hre] at h
   have h80:12*(80:E)^(1/3:E)<=52:=by
    have hle:(80:E)<=(52/12:E)^3:=by norm_num
    have hrp:=rpow_le_rpow (by norm_num) hle (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (52/12:E) 3,← rpow_mul (by norm_num)] at hrp;norm_num at hrp;linarith
   have h640:12*(640:E)^(1/2:E)<=310:=by
    have hle:(640:E)<=(310/12:E)^2:=by norm_num
    have hrp:=rpow_le_rpow (by norm_num) hle (by norm_num:(0:E)<=1/2);rw [← rpow_natCast (310/12:E) 2,← rpow_mul (by norm_num)] at hrp;norm_num at hrp;linarith
   have hL13:(2:E)^s*((2:E)^s)^(-(2/3:E))=((2:E)^s)^(1/3:E):=by
    conv_lhs=>arg 1;rw [← rpow_one ((2:E)^s)]
    rw [← rpow_add hL_pos];norm_num
   have hL0:(2:E)^s*((2:E)^s)^(-(1:E))=1:=by rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hL_pos.ne'
   have hH32:(H:E)*(H:E)^(1/2:E)=(H:E)^(3/2:E):=by
    conv_lhs=>arg 1;rw [← rpow_one (H:E)]
    rw [← rpow_add hH_pos];norm_num
   have ht1:12*(H:E)*(2:E)^s*min ((P:E)^2) X1 ≤ 52*(H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E))*((2:E)^s)^(1/3:E):=by
    calc
      _ <= 12*(H:E)*(2:E)^s*((80:E)^(1/3:E)*(N:E)^(2/3:E) * ((2:E)^k)^(-(2/3:E))*((2:E)^s)^(-(2/3:E))) :=mul_le_mul_of_nonneg_left hm1 (by positivity)
      _ = (12*(80:E)^(1/3:E))*((H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E)) * ((2:E)^s*((2:E)^s)^(-(2/3:E)))):=by ring
      _ = (12*(80:E)^(1/3:E))*((H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E)) * ((2:E)^s)^(1/3:E)):=by rw [hL13]
      _ <= 52*((H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E))*((2:E)^s)^(1/3:E)) :=mul_le_mul_of_nonneg_right h80 (by positivity)
      _ = _:=by ring
   have ht2:12*(H:E)*(2:E)^s*min ((P:E)^2) X2 ≤ 310*(H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E)):=by
    calc
      _ <= 12*(H:E)*(2:E)^s*((640:E)^(1/2:E)*(N:E)^(1/2:E)*(H:E)^(1/2:E) * ((2:E)^k)^(-(1:E))*((2:E)^s)^(-(1:E))) :=mul_le_mul_of_nonneg_left hm2 (by positivity)
      _ = (12*(640:E)^(1/2:E))*(((H:E)*(H:E)^(1/2:E))*(N:E)^(1/2:E) * ((2:E)^k)^(-(1:E))*((2:E)^s*((2:E)^s)^(-(1:E)))):=by ring
      _ = (12*(640:E)^(1/2:E))*((H:E)^(3/2:E)*(N:E)^(1/2:E) * ((2:E)^k)^(-(1:E))*1):=by rw [hH32,hL0]
      _ <= 310*((H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E))):=by rw [mul_one];exact mul_le_mul_of_nonneg_right h640 (by positivity)
      _ = _:=by ring
   have hmul:=mul_le_mul_of_nonneg_left hmin_sum (by positivity:(0:E)<=12*(H:E)*(2:E)^s);linarith
  have h2s_le:∀ s∈Finset.range B2,(2:E)^s<=(D':E):=by
   intro s hs;have hs':s<=Nat.log 2 D':=by have:=Finset.mem_range.mp hs;dsimp [B2] at this;omega
   have h1:2^s<=2^(Nat.log 2 D'):=Nat.pow_le_pow_right (by norm_num) hs';have h2:2^(Nat.log 2 D')<=D':=Nat.pow_log_le_self 2 (by omega);exact_mod_cast h1.trans h2
  have hsum_L13:∑ s∈Finset.range B2,((2:E)^s)^(1/3:E)<=5*(D':E)^(1/3:E):=by
   have h:=sum_dyadic_rpow_le hD'_pos (by norm_num:(0:E) < 1/3) h2s_le
   have hc:1/(1-(2:E)^(-(1/3:E)))<=5:=by
    have h2:(2:E)^(-(1/3:E))<=4/5:=by
      rw [rpow_neg (by norm_num)]
      have hle:(5/4:E)<=(2:E)^(1/3:E):=by
        have h3:(5/4:E)^3<=(2:E):=by norm_num
        have hrp:=rpow_le_rpow (by positivity) h3 (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (5/4:E) 3,← rpow_mul (by norm_num)] at hrp;norm_num at hrp;exact hrp
      have hinv:=inv_anti₀ (by norm_num:(0:E) < 5/4) hle;norm_num at hinv;exact hinv
    have hpos:0 < 1-(2:E)^(-(1/3:E)):=by linarith
    rw [div_le_iff₀ hpos];linarith
   exact h.trans (mul_le_mul_of_nonneg_right hc (by positivity))
  have hB2_le:(B2:E)<=3*(D':E)^(1/3:E):=by
   have h1:∀ m:ℕ,(m+1:E)<=3*((2:E)^m)^(1/3:E):=by
    intro m
    have hpow:((m+1:ℕ):E)^3<=27*(2:E)^m:=by
      have hnat:(m+1)^3<=27*2^m:=by
        induction m with
        | zero=>norm_num
        | succ n ih =>
          by_cases hn:n<=2
          · interval_cases n <;> norm_num
          ·
           have hn3:3<=n:=by omega
           have hstep:(n+2)^3<=2*(n+1)^3:=by
            have h1:(n+1)^3=n^3+3*n^2+3*n+1:=by ring
            have h2:(n+2)^3=n^3+6*n^2+12*n+8:=by ring
            have h3:3*n^2<=n^3:=by nlinarith
            have h4:9*n+7<=3*n^2+3*n+1:=by nlinarith
            omega
           calc
            (n+2)^3<=2*(n+1)^3:=hstep
            _ <= 2*(27*2^n):=Nat.mul_le_mul_left 2 ih
            _ = 27*2^(n+1):=by rw [pow_succ];ring
      exact_mod_cast hnat
    have hrp:=rpow_le_rpow (by positivity) hpow (by norm_num:(0:E)<=1/3);rw [← rpow_natCast _ 3,← rpow_mul (by positivity),mul_rpow (by norm_num) (by positivity)] at hrp;norm_num at hrp;exact hrp
   have h2:=h1 (Nat.log 2 D');have h3:((2:E)^(Nat.log 2 D'))^(1/3:E)<=(D':E)^(1/3:E) :=rpow_le_rpow (by positivity) (by exact_mod_cast Nat.pow_log_le_self 2 (by omega)) (by norm_num);have hB2_eq:(B2:E)=(Nat.log 2 D':E)+1:=by dsimp [B2];push_cast;rfl
   linarith
  calc
   6*(H:E)*∑ p∈PP1,((pairFiber k p).card:E)
      ≤ 6*(H:E)*∑ s∈Finset.range B2,(2*(2:E)^s*((Llay s).card:E)) :=
    mul_le_mul_of_nonneg_left hPP1_layers (by positivity)
   _ = ∑ s∈Finset.range B2,(12*(H:E)*(2:E)^s*((Llay s).card:E)):=by rw [Finset.mul_sum];apply sum_congr rfl;intro s _;ring
   _ <= ∑ s∈Finset.range B2,(52*(H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E))*((2:E)^s)^(1/3:E) + 310*(H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E))) :=sum_le_sum hLlay_bal
   _ = (52*(H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E))) * (∑ s∈Finset.range B2,((2:E)^s)^(1/3:E)) + (B2:E)*(310*(H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E))):=by rw [sum_add_distrib,← Finset.mul_sum,sum_const,card_range,nsmul_eq_mul]
   _ <= (52*(H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E)))*(5*(D':E)^(1/3:E)) + (3*(D':E)^(1/3:E))*(310*(H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E))) := add_le_add (mul_le_mul_of_nonneg_left hsum_L13 (by positivity))
             (mul_le_mul_of_nonneg_right hB2_le (by positivity))
   _ <= 260*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E)) + 950*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E)):=by
    have:0<=(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E)):=by positivity
    linarith
 have hS1a:∑ k∈Finset.range B1,6*(H:E)*(∑ p∈PrimePairs.filter (fun p=>(pairFiber k p).Nonempty/\¬ pairRank2 k p),((pairFiber k p).card:E)) ≤ 800*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E) + 2000*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E):=by
  have hgeom23:∑ k∈Finset.range B1,((2:E)^k)^(-(2/3:E))<=3:=by
   have h:=sum_dyadic_inv_rpow_le B1 (α:=2/3) (by norm_num)
   have hc:1/(1-(2:E)^(-(2/3:E)))<=3:=by
    have h2:(2:E)^(-(2/3:E))<=2/3:=by
      rw [rpow_neg (by norm_num)]
      have hle:(3/2:E)<=(2:E)^(2/3:E):=by
        have h3:(3/2:E)^3<=(2:E)^2:=by norm_num
        have hrp:=rpow_le_rpow (by positivity) h3 (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (3/2:E) 3,← rpow_mul (by norm_num),← rpow_natCast (2:E) 2,← rpow_mul (by norm_num)] at hrp;norm_num at hrp;exact hrp
      have hinv:=inv_anti₀ (by norm_num:(0:E) < 3/2) hle;norm_num at hinv;exact hinv
    have hpos:0 < 1-(2:E)^(-(2/3:E)):=by linarith
    rw [div_le_iff₀ hpos];linarith
   exact h.trans hc
  have hgeom1:∑ k∈Finset.range B1,((2:E)^k)^(-(1:E))<=2:=by
   have h:=sum_dyadic_inv_rpow_le B1 (α:=1) (by norm_num);norm_num at h;exact h
  calc
   _ <= ∑ k∈Finset.range B1,(260*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E)*((2:E)^k)^(-(2/3:E)) + 950*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E)*((2:E)^k)^(-(1:E))) :=sum_le_sum hS1a_k
   _ = (260*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E)) * (∑ k∈Finset.range B1,((2:E)^k)^(-(2/3:E))) + (950*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E)) * (∑ k∈Finset.range B1,((2:E)^k)^(-(1:E))):=by rw [sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
   _ <= (260*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E))*3 + (950*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E))*2 := add_le_add (mul_le_mul_of_nonneg_left hgeom23 (by positivity))
             (mul_le_mul_of_nonneg_left hgeom1 (by positivity))
   _ <= 800*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E) + 2000*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E):=by
    have h1:0<=(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E):=by positivity
    have h2:0<=(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E):=by positivity
    linarith
 have hsum_comb:∑ k∈Finset.range B1,(2*(2:E)^k*((T1 k).card:E)) ≤ (∑ k∈Finset.range B1,2*min ((2:E)^k*(P:E)^3)
           (600*(N:E)*(H:E)^2/(((2:E)^k)^2*(P:E)^2))) +
   (∑ k∈Finset.range B1,6*(H:E)*(∑ p∈PrimePairs.filter (fun p=>(pairFiber k p).Nonempty/\¬ pairRank2 k p),((pairFiber k p).card:E))):=by
  rw [← sum_add_distrib];exact sum_le_sum hT1_bound
 linarith
theorem sextupleCount_le {N H P D D':ℕ} (hN:1<=N) (hH:1<=H) (hP:4<=P)
  (hHP:H<=4*P) (hD:1<=D) (hDH:D<=H) (hD':1<=D') :
  (sextupleCount N H P D D':E) ≤ 6000*(N:E)*(H:E)^2/(P:E)^3 + 200*(N:E)*(H:E)/(P:E)^3 + 200000*(H:E)^3 + min (10^7*(N:E)*(H:E)/(P:E)^(3/2:E))
     (4*10^4*(N:E)^(1/2:E)*(H:E)^(3/2:E)*(P:E)^(1/2:E)) +
   300*(N:E)^(3/5:E)*(H:E)^(6/5:E) +
   800*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E) +
   2000*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E):=by
 classical
 let R3:=(PrimeTriples P).filter (fun t=>FiberRank3 (sextupleFiber N H P D D' t));let R2:=(PrimeTriples P).filter (fun t=>FiberRank2 (sextupleFiber N H P D D' t));let R1:=(PrimeTriples P).filter (fun t=>FiberRank1 (sextupleFiber N H P D D' t))
 let R0:=(PrimeTriples P).filter (fun t=>sextupleFiber N H P D D' t=∅)
 have hpart:(sextupleCount N H P D D':E) = (∑ t∈R3,((sextupleFiber N H P D D' t).card:E)) + (∑ t∈R2,((sextupleFiber N H P D D' t).card:E)) + (∑ t∈R1,((sextupleFiber N H P D D' t).card:E)):=by
  unfold sextupleCount;rw [Nat.cast_sum]
  have h1:=(Finset.sum_filter_add_sum_filter_not (PrimeTriples P)
   (fun t=>FiberRank3 (sextupleFiber N H P D D' t))
   (fun t=>((sextupleFiber N H P D D' t).card:E))).symm
  let Rest1:=(PrimeTriples P).filter (fun t=>¬ FiberRank3 (sextupleFiber N H P D D' t))
  have h2:=(Finset.sum_filter_add_sum_filter_not Rest1
   (fun t=>FiberRank2 (sextupleFiber N H P D D' t))
   (fun t=>((sextupleFiber N H P D D' t).card:E))).symm
  let Rest2:=Rest1.filter (fun t=>¬ FiberRank2 (sextupleFiber N H P D D' t))
  have hR2_eq:Rest1.filter (fun t=>FiberRank2 (sextupleFiber N H P D D' t))=R2:=by
   ext t;simp only [Rest1,R2,mem_filter];constructor
   · rintro ⟨⟨ht,_⟩,h2⟩;exact ⟨ht,h2⟩
   · rintro ⟨ht,h2⟩;exact ⟨⟨ht,h2.1⟩,h2⟩
  have hRest2_eq:∑ t∈Rest2,((sextupleFiber N H P D D' t).card:E) = ∑ t∈R1,((sextupleFiber N H P D D' t).card:E):=by
   have h3:=(Finset.sum_filter_add_sum_filter_not Rest2
    (fun t=>(sextupleFiber N H P D D' t).Nonempty)
    (fun t=>((sextupleFiber N H P D D' t).card:E))).symm
   have hR1_eq:Rest2.filter (fun t=>(sextupleFiber N H P D D' t).Nonempty)=R1:=by
    ext t;simp only [Rest2,Rest1,R1,mem_filter];dsimp only [FiberRank1];tauto
   have hemp0:∑ t∈Rest2.filter (fun t=>¬ (sextupleFiber N H P D D' t).Nonempty),((sextupleFiber N H P D D' t).card:E)=0:=by
    apply Finset.sum_eq_zero;intro t ht;have hemp:=Finset.not_nonempty_iff_eq_empty.mp (mem_filter.mp ht).2;rw [hemp,Finset.card_empty,Nat.cast_zero]
   rw [h3,hR1_eq,hemp0,add_zero]
  rw [h1,h2,hR2_eq,hRest2_eq];ring
 have h3:=sum_rank3_fibers_le (D:=D) (D':=D') hN hH (by omega:1<=P);have h2:=sum_rank2_fibers_le (D:=D) (D':=D') hN hH hP hHP;have h1:=sum_rank1_fibers_le hN hH hP hHP hD hDH hD';linarith
end
section
open Classical
lemma natLog2_add_one_le_rpow {H:ℕ} (hH:1<=H) {β:E} (hβ:0 < β) :
  ((Nat.log 2 H+1:ℕ):E)<=(2/β+1)*(H:E)^β:=by
 have hHR:(1:E)<=(H:E):=by exact_mod_cast hH
 have hH_pos:(0:E) < (H:E):=by linarith
 have hpow:((2:E)^(Nat.log 2 H))<=(H:E):=by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
 have hlog_pow:((Nat.log 2 H:ℕ):E)*Real.log 2<=Real.log (H:E):=by
  have h1:=log_le_log (by positivity) hpow;rwa [log_pow] at h1
 have hlog2_gt:(1/2:E) < Real.log 2:=by linarith [log_two_gt_d9]
 have hlogH_le:Real.log (H:E)<=(H:E)^β/β:=by
  have h1:Real.log ((H:E)^β)<=(H:E)^β-1 :=log_le_sub_one_of_pos (rpow_pos_of_pos hH_pos β);rw [log_rpow hH_pos] at h1;rw [le_div_iff₀ hβ];linarith
 have hlog_nat_le:((Nat.log 2 H:ℕ):E)<=(2/β)*(H:E)^β:=by
  have h1:((Nat.log 2 H:ℕ):E)*(1/2)<=(H:E)^β/β:=by
   have hnn:(0:E)<=((Nat.log 2 H:ℕ):E):=Nat.cast_nonneg _
   have:=mul_le_mul_of_nonneg_left hlog2_gt.le hnn
   linarith
  have h2:(2/β)*(H:E)^β=2*((H:E)^β/β):=by ring
  linarith
 have hH_rpow_ge1:(1:E)<=(H:E)^β:=one_le_rpow hHR hβ.le;push_cast;linarith
lemma exists_threshold_log_pow_le {C α:E} (hC:0 < C) (hα:0 < α) (m:ℕ) :
  ∃ H₀:ℕ,1000<=H₀/\∀ H:ℕ,H₀<=H → C*((Nat.log 2 H+1:ℕ):E)^m<=(H:E)^α:=by
 let β:E:=α/(2*((m:E)+1));have hβ_pos:0 < β:=by positivity
 let K:E:=C*(2/β+1)^m;have hK_pos:0 < K:=by positivity
 let H₀:ℕ:=max 1000 (⌈K^(2/α)⌉₊+1);refine ⟨H₀,le_max_left _ _,?_⟩;intro H hH;have hH_ge1:1<=H:=by omega
 have hHR_ge1:(1:E)<=(H:E):=by exact_mod_cast hH_ge1
 have hH_pos:(0:E) < (H:E):=by linarith
 have hH_ge_K:K^(2/α)<=(H:E):=by
  have h1:(⌈K^(2/α)⌉₊:E)<=(H:E):=by exact_mod_cast (le_trans (by omega) hH)
  exact (Nat.le_ceil _).trans h1
 have hK_le_Hhalf:K<=(H:E)^(α/2):=by
  have hrp:=rpow_le_rpow (by positivity) hH_ge_K (by positivity:(0:E)<=α/2);rw [← rpow_mul hK_pos.le] at hrp;have hmul:(2/α)*(α/2)=1:=by field_simp [hα.ne']
  rwa [hmul,rpow_one] at hrp
 have hlog:=natLog2_add_one_le_rpow hH_ge1 hβ_pos;have hpow:=pow_le_pow_left₀ (Nat.cast_nonneg _) hlog m;rw [mul_pow,← rpow_natCast ((H:E)^β) m,← rpow_mul hH_pos.le] at hpow
 have hmβ_le:β*(m:E)<=α/2:=by
  dsimp [β];rw [div_mul_eq_mul_div,div_le_div_iff₀ (by positivity) (by norm_num)];nlinarith
 have hH_mβ:(H:E)^(β*(m:E))<=(H:E)^(α/2) :=rpow_le_rpow_of_exponent_le hHR_ge1 hmβ_le
 calc
  C*((Nat.log 2 H+1:ℕ):E)^m
    ≤ C*((2/β+1)^m*(H:E)^(β*(m:E))) :=
   mul_le_mul_of_nonneg_left hpow hC.le
  _ = K*(H:E)^(β*(m:E)):=by dsimp [K];ring
  _ <= (H:E)^(α/2)*(H:E)^(α/2) :=mul_le_mul hK_le_Hhalf hH_mβ (by positivity) (by positivity)
  _ = (H:E)^α:=by rw [← rpow_add hH_pos];congr 1;ring
lemma sum_inv_sq_Icc_le (a b:ℕ) (ha:2<=a) :
  ∑ n∈Finset.Icc a b,(1:E)/(n:E)^2<=1/((a:E)-1):=by
 have ha1_pos:(0:E) < (a:E)-1:=by
  have:(2:E)<=(a:E):=by exact_mod_cast ha
  linarith
 by_cases hab:a<=b
 ·
  have hstep:∀ n∈Finset.Icc a b,(1:E)/(n:E)^2<=1/((n:E)-1)-1/(n:E):=by
   intro n hn;have hn_ge:a<=n:=(Finset.mem_Icc.mp hn).1;have hn2:(2:E)<=(n:E):=by exact_mod_cast (le_trans ha hn_ge)
   have hn_pos:(0:E) < (n:E):=by linarith
   have hn1_pos:(0:E) < (n:E)-1:=by linarith
   have hrhs:1/((n:E)-1)-1/(n:E)=1/(((n:E)-1)*(n:E)):=by field_simp [hn1_pos.ne',hn_pos.ne'];ring
   rw [hrhs];exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)
  have htele:∀ m:ℕ,a<=m → ∑ n∈Finset.Icc a m,(1/((n:E)-1)-1/(n:E)) = 1/((a:E)-1)-1/(m:E):=by
   intro m hm
   induction m,hm using Nat.le_induction with
   | base=>simp
   | succ k hk ih =>
    have hIcc:Finset.Icc a (k+1)=insert (k+1) (Finset.Icc a k):=by ext x;simp only [Finset.mem_Icc,Finset.mem_insert];omega
    rw [hIcc,Finset.sum_insert (by simp),ih];push_cast;ring
  calc
   ∑ n∈Finset.Icc a b,(1:E)/(n:E)^2
     ≤ ∑ n∈Finset.Icc a b,(1/((n:E)-1)-1/(n:E)):=sum_le_sum hstep
   _ = 1/((a:E)-1)-1/(b:E):=htele b hab
   _ <= 1/((a:E)-1):=by linarith [show (0:E)<=1/(b:E) by positivity]
 ·
  have hemp:Finset.Icc a b=∅:=Finset.Icc_eq_empty hab;rw [hemp,Finset.sum_empty];positivity
lemma sum_inv_cube_Icc_le (a b:ℕ) (ha:2<=a) :
  ∑ n∈Finset.Icc a b,(1:E)/(n:E)^3<=1/((a:E)-1)^2:=by
 have ha1_pos:(0:E) < (a:E)-1:=by
  have:(2:E)<=(a:E):=by exact_mod_cast ha
  linarith
 calc
  ∑ n∈Finset.Icc a b,(1:E)/(n:E)^3
    ≤ ∑ n∈Finset.Icc a b,(1/((a:E)-1))*((1:E)/(n:E)^2):=by
   apply sum_le_sum;intro n hn;have hn_ge:(a:E)<=(n:E):=by exact_mod_cast (Finset.mem_Icc.mp hn).1
   have hn_pos:(0:E) < (n:E):=by linarith
   have h1:(1:E)/(n:E)<=1/((a:E)-1) :=div_le_div_of_nonneg_left (by norm_num) ha1_pos (by linarith);have h2:(1:E)/(n:E)^3=(1/(n:E))*(1/(n:E)^2):=by ring
   rw [h2];exact mul_le_mul_of_nonneg_right h1 (by positivity)
  _ = (1/((a:E)-1))*∑ n∈Finset.Icc a b,(1:E)/(n:E)^2:=(Finset.mul_sum _ _ _).symm
  _ <= (1/((a:E)-1))*(1/((a:E)-1)) :=mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le a b ha) (by positivity)
  _ = 1/((a:E)-1)^2:=by rw [one_div_mul_one_div,sq]
noncomputable def badDyadic (N H:ℕ):Finset ℕ :=(Finset.Ico (N/2) N).filter (fun v=>∀ j∈Finset.Ioo 0 H,¬ Squarefree (v+j))
noncomputable def badLargePrimes (N H P₁:ℕ):Finset ℕ := (Finset.Ico (N/2) N).filter (fun v =>
  ∃ j∈Finset.Ioo 0 H,∃ p,P₁<=p/\Nat.Prime p/\p^2∣v+j)
lemma card_badLargePrimes_le {N H P₁:ℕ} (hP₁:2<=P₁) (hHN:H<=N) :
  ((badLargePrimes N H P₁).card:E)<=4*(N:E)*(H:E)/(P₁:E):=by
 let cover:Finset ℕ:=(Finset.Icc P₁ (2*N)).biUnion (fun p =>
  (Finset.Icc 1 (2*N/p^2)).biUnion (fun m =>
   (Finset.Ioo 0 H).image (fun j=>p^2*m-j)))
 have hsub:badLargePrimes N H P₁⊆cover:=by
  intro v hv;rcases mem_filter.mp hv with ⟨hv_ico,j,hj_ioo,p,hp_ge,hp_pr,m,hm⟩;have hv_lt:v < N:=(Finset.mem_Ico.mp hv_ico).2;have hj_bounds:=Finset.mem_Ioo.mp hj_ioo
  have hp_sq_le:p^2<=2*N:=by
   have hm_pos:1<=m:=by
    by_contra h0;push Not at h0
    have hm0:m=0:=Nat.lt_one_iff.mp h0;rw [hm0,mul_zero] at hm;omega
   have h1:p^2<=p^2*m:=Nat.le_mul_of_pos_right _ hm_pos;omega
  have hp_le:p<=2*N:=le_trans (Nat.le_self_pow (by norm_num) p) hp_sq_le
  have hm_pos:1<=m:=by
   by_contra h0;push Not at h0
   have hm0:m=0:=Nat.lt_one_iff.mp h0;rw [hm0,mul_zero] at hm;omega
  have hm_le:m<=2*N/p^2 :=Nat.le_div_iff_mul_le (pow_pos hp_pr.pos 2) |>.mpr (by rw [mul_comm];omega)
  refine Finset.mem_biUnion.mpr ⟨p,Finset.mem_Icc.mpr ⟨hp_ge,hp_le⟩,Finset.mem_biUnion.mpr ⟨m,Finset.mem_Icc.mpr ⟨hm_pos,hm_le⟩,Finset.mem_image.mpr ⟨j,hj_ioo,by omega⟩⟩⟩
 have hcard_nat:(badLargePrimes N H P₁).card ≤ ∑ p∈Finset.Icc P₁ (2*N),(2*N/p^2)*H:=by
  calc
   (badLargePrimes N H P₁).card<=cover.card:=Finset.card_le_card hsub
   _ <= ∑ p∈Finset.Icc P₁ (2*N),((Finset.Icc 1 (2*N/p^2)).biUnion (fun m =>
       (Finset.Ioo 0 H).image (fun j=>p^2*m-j))).card:=Finset.card_biUnion_le
   _ <= ∑ p∈Finset.Icc P₁ (2*N),(2*N/p^2)*H:=by
    apply sum_le_sum;intro p _
    calc
     _ <= ∑ m∈Finset.Icc 1 (2*N/p^2),((Finset.Ioo 0 H).image (fun j=>p^2*m-j)).card:=Finset.card_biUnion_le
     _ <= ∑ _m∈Finset.Icc 1 (2*N/p^2),H:=by
      apply sum_le_sum;intro m _
      calc
       ((Finset.Ioo 0 H).image (fun j=>p^2*m-j)).card
         ≤ (Finset.Ioo 0 H).card:=card_image_le
       _ = H-1:=Nat.card_Ioo 0 H
       _ <= H:=Nat.sub_le H 1
     _ = (2*N/p^2)*H:=by rw [sum_const,smul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
 have hcast:((badLargePrimes N H P₁).card:E) ≤ ∑ p∈Finset.Icc P₁ (2*N),(((2*N/p^2:ℕ):E)*(H:E)):=by
  have:((badLargePrimes N H P₁).card:E) ≤ ((∑ p∈Finset.Icc P₁ (2*N),(2*N/p^2)*H:ℕ):E):=by exact_mod_cast hcard_nat
  simpa [Nat.cast_sum,Nat.cast_mul] using this
 have hP₁R:(2:E)<=(P₁:E):=by exact_mod_cast hP₁
 have hP₁_pos:(0:E) < (P₁:E):=by linarith
 have hinv_le:1/((P₁:E)-1)<=2/(P₁:E):=by rw [div_le_div_iff₀ (by linarith) hP₁_pos];linarith
 calc
  ((badLargePrimes N H P₁).card:E)
    ≤ ∑ p∈Finset.Icc P₁ (2*N),(2*(N:E)*(H:E)*((1:E)/(p:E)^2)):=by
   refine hcast.trans (sum_le_sum (fun p hp=>?_));have hp_pos:(0:E) < (p:E):=by exact_mod_cast (show 0 < p by have:=(Finset.mem_Icc.mp hp).1;omega)
   have hdiv:((2*N/p^2:ℕ):E)<=(2*(N:E))/(p:E)^2:=by
    rw [le_div_iff₀ (pow_pos hp_pos 2)];exact_mod_cast Nat.div_mul_le_self (2*N) (p^2)
   calc
    ((2*N/p^2:ℕ):E)*(H:E)
      ≤ (2*(N:E)/(p:E)^2)*(H:E) :=
     mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg H)
    _ = 2*(N:E)*(H:E)*((1:E)/(p:E)^2):=by ring
  _ = 2*(N:E)*(H:E)*∑ p∈Finset.Icc P₁ (2*N),(1:E)/(p:E)^2 :=(Finset.mul_sum _ _ _).symm
  _ <= 2*(N:E)*(H:E)*(1/((P₁:E)-1)) :=mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le P₁ (2*N) hP₁) (by positivity)
  _ <= 2*(N:E)*(H:E)*(2/(P₁:E)) :=mul_le_mul_of_nonneg_left hinv_le (by positivity)
  _ = 4*(N:E)*(H:E)/(P₁:E):=by ring
noncomputable def badDyadicPrime (N H P L₀:ℕ):Finset ℕ := (Finset.Ico (N/2) N).filter (fun v =>
  L₀<=((Finset.Ioo 0 H).filter (fun j =>
   ∃ p∈Finset.Ico P (2*P),Nat.Prime p/\p^2∣v+j)).card)
set_option maxHeartbeats 800000 in
lemma card_badDyadicPrime_le_sextupleCount {N H P L₀ D D':ℕ}
  (_hN:1<=N) (hH:1<=H) (hHN:H<=N) (hP_sq:H<=P^2)
  (hL₀:10<=L₀) (hD:2<=D) (hD':2<=D')
  (hD_big:8*(H:E)^3/(D:E)^2<=(L₀:E)^3/8)
  (hD'_big:4*(L₀:E)*(H:E)^2/(D':E)<=(L₀:E)^3/8) :
  ((badDyadicPrime N H P L₀).card:E) ≤ 4*(H:E)/(L₀:E)^3*(sextupleCount N H P D D':E):=by
 let B:=badDyadicPrime N H P L₀
 let Jv:ℕ->Finset ℕ:=fun v =>
  (Finset.Ioo 0 H).filter (fun j=>∃ p∈Finset.Ico P (2*P),Nat.Prime p/\p^2∣v+j)
 have hexA:∀ v∈B,∃ A⊆Jv v,A.card=L₀:=fun v hv =>
  Finset.exists_subset_card_eq (mem_filter.mp hv).2
 let Av:ℕ->Finset ℕ:=fun v=>if h:v∈B then Classical.choose (hexA v h) else ∅;have hAv_sub:∀ v∈B,Av v⊆Jv v:=fun v hv=>by simp only [Av,hv,↓reduceDIte];exact (Classical.choose_spec (hexA v hv)).1
 have hAv_card:∀ v∈B,(Av v).card=L₀:=fun v hv=>by simp only [Av,hv,↓reduceDIte];exact (Classical.choose_spec (hexA v hv)).2
 let minP:ℕ->ℕ:=fun n =>
  let S:=(Finset.Ico P (2*P)).filter (fun p=>Nat.Prime p/\p^2∣n)
  if h:S.Nonempty then S.min' h else 0
 have hminP_spec:∀ n,(∃ p∈Finset.Ico P (2*P),Nat.Prime p/\p^2∣n) → IsMinPrimeSqDiv P (minP n) n:=by
  intro n hex;let S:=(Finset.Ico P (2*P)).filter (fun p=>Nat.Prime p/\p^2∣n)
  have hne:S.Nonempty:=by
    rcases hex with ⟨p,hp1,hp2,hp3⟩;exact ⟨p,mem_filter.mpr ⟨hp1,hp2,hp3⟩⟩
  have heq:minP n=S.min' hne:=dif_pos hne;rw [heq];have hmem:=mem_filter.mp (Finset.min'_mem S hne);refine ⟨hmem.1,hmem.2.1,hmem.2.2,?_⟩;intro q hq1 hq2 hq3;exact Finset.min'_le S q (mem_filter.mpr ⟨hq1,hq2,hq3⟩)
 let qOf:ℕ->ℕ:=fun n=>n/(minP n)^2
 have hminP_inj:∀ v∈B,∀ j1∈Av v,∀ j2∈Av v,j1≠j2->minP (v+j1)≠minP (v+j2):=by
  intro v hv j1 hj1 j2 hj2 hne heq;have hm1:=hminP_spec (v+j1) (mem_filter.mp (hAv_sub v hv hj1)).2;have hm2:=hminP_spec (v+j2) (mem_filter.mp (hAv_sub v hv hj2)).2;have hp_ge:P<=minP (v+j1):=(Finset.mem_Ico.mp hm1.1).1
  have hp_sq_ge:H<=(minP (v+j1))^2:=hP_sq.trans (Nat.pow_le_pow_left hp_ge 2);have hd1:(minP (v+j1))^2∣v+j1:=hm1.2.2.1;have hd2:(minP (v+j1))^2∣v+j2:=heq ▸ hm2.2.2.1;have hj1_ioo:=Finset.mem_Ioo.mp (mem_filter.mp (hAv_sub v hv hj1)).1
  have hj2_ioo:=Finset.mem_Ioo.mp (mem_filter.mp (hAv_sub v hv hj2)).1;rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    have hsub:(minP (v+j1))^2∣j2-j1:=by
     have:v+j2=(v+j1)+(j2-j1):=by omega
     exact (Nat.dvd_add_right hd1).mp (this ▸ hd2)
    have hle:=Nat.le_of_dvd (by omega) hsub;omega
  ·
    have hsub:(minP (v+j1))^2∣j1-j2:=by
     have:v+j1=(v+j2)+(j1-j2):=by omega
     exact (Nat.dvd_add_right hd2).mp (this ▸ hd1)
    have hle:=Nat.le_of_dvd (by omega) hsub;omega
 let Triples:ℕ->Finset (ℕ × ℕ × ℕ):=fun v =>
  (Av v×ˢAv v×ˢAv v).filter (fun x=>x.1≠x.2.1/\x.1≠x.2.2/\x.2.1≠x.2.2)
 let Good:ℕ->Finset (ℕ × ℕ × ℕ):=fun v =>
  (Triples v).filter (fun x =>
    Nat.gcd (Nat.gcd (qOf (v+x.1)) (qOf (v+x.2.1))) (qOf (v+x.2.2))<=D ∧
    Nat.gcd (qOf (v+x.1)) (qOf (v+x.2.1))<=D')
 have hGood_lb:∀ v∈B,(L₀:E)^3/4<=((Good v).card:E):=by
  intro v hv
  have hTriples_card:(Triples v).card=L₀*(L₀-1)*(L₀-2):=by
    have h1:(Triples v).card=∑ a∈Av v,∑ b∈(Av v).erase a,(((Av v).erase a).erase b).card:=by
     let F1:ℕ->Finset (ℕ × ℕ × ℕ):=fun a =>
      ((Av v).erase a).biUnion (fun b=>(((Av v).erase a).erase b).image (fun c=>(a,b,c)))
     have heq:Triples v=(Av v).biUnion F1:=by
      ext ⟨a,b,c⟩;simp only [Triples,F1,mem_filter,mem_product,Finset.mem_biUnion,mem_erase,Finset.mem_image,Prod.mk.injEq];constructor
      ·
       rintro ⟨⟨ha,hb,hc⟩,hab,hac,hbc⟩;exact ⟨a,ha,b,⟨hab.symm,hb⟩,c,⟨hbc.symm,hac.symm,hc⟩,rfl,rfl,rfl⟩
      ·
       rintro ⟨a',ha',b',⟨hba',hb'⟩,c',⟨hcb',hca',hc'⟩,rfl,rfl,rfl⟩;exact ⟨⟨ha',hb',hc'⟩,hba'.symm,hca'.symm,hcb'.symm⟩
     rw [heq,card_biUnion]
     ·
      apply sum_congr rfl;intro a _;rw [card_biUnion]
      ·
       apply sum_congr rfl;intro b _;exact Finset.card_image_of_injective _ (fun c1 c2 h=>by simpa using h)
      ·
       intro b1 _ b2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro x hx1 hx2;rcases Finset.mem_image.mp hx1 with ⟨c1,_,rfl⟩;rcases Finset.mem_image.mp hx2 with ⟨c2,_,h⟩;exact hne (congrArg (fun p=>p.2.1) h).symm
     ·
      intro a1 _ a2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro x hx1 hx2;rcases Finset.mem_biUnion.mp hx1 with ⟨b1,_,h1⟩;rcases Finset.mem_image.mp h1 with ⟨c1,_,rfl⟩;rcases Finset.mem_biUnion.mp hx2 with ⟨b2,_,h2⟩
      rcases Finset.mem_image.mp h2 with ⟨c2,_,h⟩;exact hne (congrArg Prod.fst h).symm
    rw [h1];have hcardA:=hAv_card v hv
    calc
     ∑ a∈Av v,∑ b∈(Av v).erase a,(((Av v).erase a).erase b).card
       = ∑ a∈Av v,∑ _b∈(Av v).erase a,(L₀-2):=by
      apply sum_congr rfl;intro a ha;apply sum_congr rfl;intro b hb;rw [card_erase_of_mem hb,card_erase_of_mem ha,hcardA];omega
     _ = ∑ a∈Av v,(L₀-1)*(L₀-2):=by
      apply sum_congr rfl;intro a ha;rw [sum_const,smul_eq_mul,card_erase_of_mem ha,hcardA]
     _ = L₀*((L₀-1)*(L₀-2)):=by rw [sum_const,smul_eq_mul,hcardA]
     _ = L₀*(L₀-1)*(L₀-2):=by ring
  have hTriples_ge:(L₀:E)^3/2<=((Triples v).card:E):=by
    have hL₀R:(10:E)<=(L₀:E):=by exact_mod_cast hL₀
    have hcast:((Triples v).card:E)=(L₀:E)*((L₀:E)-1)*((L₀:E)-2):=by
     rw [hTriples_card];push_cast [Nat.cast_sub (by omega:1<=L₀),Nat.cast_sub (by omega:2<=L₀)];ring
    rw [hcast];nlinarith [sq_nonneg ((L₀:E)-5)]
  let Bad1:=(Triples v).filter (fun x =>
    D < Nat.gcd (Nat.gcd (qOf (v+x.1)) (qOf (v+x.2.1))) (qOf (v+x.2.2)))
  have hBad1_le:(Bad1.card:E)<=(L₀:E)^3/8:=by
    let Md:ℕ->Finset ℕ:=fun d=>(Finset.Ioo 0 H).filter (fun j=>d∣v+j)
    have hsub1:Bad1⊆(Finset.Icc (D+1) H).biUnion (fun d=>Md d×ˢMd d×ˢMd d):=by
     intro x hx;rcases mem_filter.mp hx with ⟨hxT,hgtD⟩;rcases mem_filter.mp hxT with ⟨hxP,h12,_,_⟩;have hx1:=(mem_product.mp hxP).1;have hx2:=(mem_product.mp (mem_product.mp hxP).2).1;have hx3:=(mem_product.mp (mem_product.mp hxP).2).2
     set d:=Nat.gcd (Nat.gcd (qOf (v+x.1)) (qOf (v+x.2.1))) (qOf (v+x.2.2))
     have hq_dvd:∀ j∈Av v,qOf (v+j)∣v+j:=by
      intro j hj;have hm:=hminP_spec (v+j) (mem_filter.mp (hAv_sub v hv hj)).2;exact ⟨(minP (v+j))^2,(Nat.mul_div_cancel' hm.2.2.1).symm.trans (mul_comm _ _)⟩
     have hd1:d∣v+x.1 :=((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)).trans (hq_dvd x.1 hx1);have hd2:d∣v+x.2.1 :=((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)).trans (hq_dvd x.2.1 hx2)
     have hd3:d∣v+x.2.2 :=(Nat.gcd_dvd_right _ _).trans (hq_dvd x.2.2 hx3);have hj1_ioo:=(mem_filter.mp (hAv_sub v hv hx1)).1;have hj2_ioo:=(mem_filter.mp (hAv_sub v hv hx2)).1;have hj3_ioo:=(mem_filter.mp (hAv_sub v hv hx3)).1
     have hd_le_H:d<=H:=by
      have hb1:=Finset.mem_Ioo.mp hj1_ioo;have hb2:=Finset.mem_Ioo.mp hj2_ioo;rcases lt_or_gt_of_ne h12 with hlt | hgt
      ·
       have hsub:d∣x.2.1-x.1:=by
         have:v+x.2.1=(v+x.1)+(x.2.1-x.1):=by omega
         exact (Nat.dvd_add_right hd1).mp (this ▸ hd2)
       exact le_trans (Nat.le_of_dvd (by omega) hsub) (by omega)
      ·
       have hsub:d∣x.1-x.2.1:=by
         have:v+x.1=(v+x.2.1)+(x.1-x.2.1):=by omega
         exact (Nat.dvd_add_right hd2).mp (this ▸ hd1)
       exact le_trans (Nat.le_of_dvd (by omega) hsub) (by omega)
     refine Finset.mem_biUnion.mpr ⟨d,Finset.mem_Icc.mpr ⟨by omega,hd_le_H⟩,mem_product.mpr ⟨mem_filter.mpr ⟨hj1_ioo,hd1⟩,mem_product.mpr ⟨mem_filter.mpr ⟨hj2_ioo,hd2⟩,mem_filter.mpr ⟨hj3_ioo,hd3⟩⟩⟩⟩
    have hcard1:(Bad1.card:E)<=∑ d∈Finset.Icc (D+1) H,((Md d).card:E)^3:=by
     have hnat:Bad1.card<=∑ d∈Finset.Icc (D+1) H,(Md d).card^3:=by
      calc
       Bad1.card<=((Finset.Icc (D+1) H).biUnion (fun d=>Md d×ˢMd d×ˢMd d)).card :=Finset.card_le_card hsub1
       _ <= ∑ d∈Finset.Icc (D+1) H,(Md d×ˢMd d×ˢMd d).card:=Finset.card_biUnion_le
       _ = ∑ d∈Finset.Icc (D+1) H,(Md d).card^3:=by
         apply sum_congr rfl;intro d _;simp only [Finset.card_product];ring
     have:(Bad1.card:E)<=((∑ d∈Finset.Icc (D+1) H,(Md d).card^3:ℕ):E):=by exact_mod_cast hnat
     simpa [Nat.cast_sum,Nat.cast_pow] using this
    calc
     (Bad1.card:E)<=∑ d∈Finset.Icc (D+1) H,(8*(H:E)^3*((1:E)/(d:E)^3)):=by
      refine hcard1.trans (sum_le_sum (fun d hd=>?_));have hd_bounds:=Finset.mem_Icc.mp hd;have hd_pos:0 < d:=by omega
      have hMd:=card_dvd_in_Ioo_le v H d hd_pos;have hdR_pos:(0:E) < (d:E):=by exact_mod_cast hd_pos
      have h1_le:(1:E)<=(H:E)/(d:E):=(one_le_div hdR_pos).mpr (by exact_mod_cast hd_bounds.2)
      have hMd2:((Md d).card:E)<=2*(H:E)/(d:E):=by
       have:2*(H:E)/(d:E)=2*((H:E)/(d:E)):=by ring
       linarith
      calc
       ((Md d).card:E)^3<=(2*(H:E)/(d:E))^3 :=pow_le_pow_left₀ (Nat.cast_nonneg _) hMd2 3
       _ = 8*(H:E)^3*((1:E)/(d:E)^3):=by ring
     _ = 8*(H:E)^3*∑ d∈Finset.Icc (D+1) H,(1:E)/(d:E)^3 :=(Finset.mul_sum _ _ _).symm
     _ <= 8*(H:E)^3*(1/(((D+1:ℕ):E)-1)^2) :=mul_le_mul_of_nonneg_left (sum_inv_cube_Icc_le (D+1) H (by omega)) (by positivity)
     _ = 8*(H:E)^3/(D:E)^2:=by push_cast;ring
     _ <= (L₀:E)^3/8:=hD_big
  let Bad2:=(Triples v).filter (fun x=>D' < Nat.gcd (qOf (v+x.1)) (qOf (v+x.2.1)))
  have hBad2_le:(Bad2.card:E)<=(L₀:E)^3/8:=by
    let Md:ℕ->Finset ℕ:=fun d=>(Finset.Ioo 0 H).filter (fun j=>d∣v+j)
    have hsub2:Bad2⊆(Finset.Icc (D'+1) H).biUnion (fun d=>Md d×ˢMd d×ˢAv v):=by
     intro x hx;rcases mem_filter.mp hx with ⟨hxT,hgtD'⟩;rcases mem_filter.mp hxT with ⟨hxP,h12,_,_⟩;have hx1:=(mem_product.mp hxP).1;have hx2:=(mem_product.mp (mem_product.mp hxP).2).1;have hx3:=(mem_product.mp (mem_product.mp hxP).2).2
     set d:=Nat.gcd (qOf (v+x.1)) (qOf (v+x.2.1))
     have hq_dvd:∀ j∈Av v,qOf (v+j)∣v+j:=by
      intro j hj;have hm:=hminP_spec (v+j) (mem_filter.mp (hAv_sub v hv hj)).2;exact ⟨(minP (v+j))^2,(Nat.mul_div_cancel' hm.2.2.1).symm.trans (mul_comm _ _)⟩
     have hd1:d∣v+x.1:=(Nat.gcd_dvd_left _ _).trans (hq_dvd x.1 hx1);have hd2:d∣v+x.2.1:=(Nat.gcd_dvd_right _ _).trans (hq_dvd x.2.1 hx2);have hj1_ioo:=(mem_filter.mp (hAv_sub v hv hx1)).1;have hj2_ioo:=(mem_filter.mp (hAv_sub v hv hx2)).1
     have hd_le_H:d<=H:=by
      have hb1:=Finset.mem_Ioo.mp hj1_ioo;have hb2:=Finset.mem_Ioo.mp hj2_ioo;rcases lt_or_gt_of_ne h12 with hlt | hgt
      ·
       have hsub:d∣x.2.1-x.1:=by
         have:v+x.2.1=(v+x.1)+(x.2.1-x.1):=by omega
         exact (Nat.dvd_add_right hd1).mp (this ▸ hd2)
       exact le_trans (Nat.le_of_dvd (by omega) hsub) (by omega)
      ·
       have hsub:d∣x.1-x.2.1:=by
         have:v+x.1=(v+x.2.1)+(x.1-x.2.1):=by omega
         exact (Nat.dvd_add_right hd2).mp (this ▸ hd1)
       exact le_trans (Nat.le_of_dvd (by omega) hsub) (by omega)
     refine Finset.mem_biUnion.mpr ⟨d,Finset.mem_Icc.mpr ⟨by omega,hd_le_H⟩,mem_product.mpr ⟨mem_filter.mpr ⟨hj1_ioo,hd1⟩,mem_product.mpr ⟨mem_filter.mpr ⟨hj2_ioo,hd2⟩,hx3⟩⟩⟩
    have hcard2:(Bad2.card:E)<=∑ d∈Finset.Icc (D'+1) H,((Md d).card:E)^2*(L₀:E):=by
     have hnat:Bad2.card<=∑ d∈Finset.Icc (D'+1) H,(Md d).card^2*L₀:=by
      calc
       Bad2.card<=((Finset.Icc (D'+1) H).biUnion (fun d=>Md d×ˢMd d×ˢAv v)).card :=Finset.card_le_card hsub2
       _ <= ∑ d∈Finset.Icc (D'+1) H,(Md d×ˢMd d×ˢAv v).card:=Finset.card_biUnion_le
       _ = ∑ d∈Finset.Icc (D'+1) H,(Md d).card^2*L₀:=by
         apply sum_congr rfl;intro d _;simp only [Finset.card_product,hAv_card v hv];ring
     have:(Bad2.card:E)<=((∑ d∈Finset.Icc (D'+1) H,(Md d).card^2*L₀:ℕ):E):=by exact_mod_cast hnat
     simpa [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow] using this
    calc
     (Bad2.card:E)<=∑ d∈Finset.Icc (D'+1) H,(4*(L₀:E)*(H:E)^2*((1:E)/(d:E)^2)):=by
      refine hcard2.trans (sum_le_sum (fun d hd=>?_));have hd_bounds:=Finset.mem_Icc.mp hd;have hd_pos:0 < d:=by omega
      have hMd:=card_dvd_in_Ioo_le v H d hd_pos;have hdR_pos:(0:E) < (d:E):=by exact_mod_cast hd_pos
      have h1_le:(1:E)<=(H:E)/(d:E):=(one_le_div hdR_pos).mpr (by exact_mod_cast hd_bounds.2)
      have hMd2:((Md d).card:E)<=2*(H:E)/(d:E):=by
       have:2*(H:E)/(d:E)=2*((H:E)/(d:E)):=by ring
       linarith
      calc
       ((Md d).card:E)^2*(L₀:E)<=(2*(H:E)/(d:E))^2*(L₀:E) :=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hMd2 2) (Nat.cast_nonneg L₀)
       _ = 4*(L₀:E)*(H:E)^2*((1:E)/(d:E)^2):=by ring
     _ = 4*(L₀:E)*(H:E)^2*∑ d∈Finset.Icc (D'+1) H,(1:E)/(d:E)^2 :=(Finset.mul_sum _ _ _).symm
     _ <= 4*(L₀:E)*(H:E)^2*(1/(((D'+1:ℕ):E)-1)) :=mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_le (D'+1) H (by omega)) (by positivity)
     _ = 4*(L₀:E)*(H:E)^2/(D':E):=by push_cast;ring
     _ <= (L₀:E)^3/8:=hD'_big
  have hcov:Triples v⊆Good v∪(Bad1∪Bad2):=by
    intro x hx
    by_cases h1:Nat.gcd (Nat.gcd (qOf (v+x.1)) (qOf (v+x.2.1))) (qOf (v+x.2.2))<=D
    ·
     by_cases h2:Nat.gcd (qOf (v+x.1)) (qOf (v+x.2.1))<=D'
     · exact Finset.mem_union_left _ (mem_filter.mpr ⟨hx,h1,h2⟩)
     · exact Finset.mem_union_right _ (Finset.mem_union_right _ (mem_filter.mpr ⟨hx,by omega⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (mem_filter.mpr ⟨hx,by omega⟩))
  have hcard_cov:(Triples v).card<=(Good v).card+Bad1.card+Bad2.card:=by
    calc
     (Triples v).card<=(Good v∪(Bad1∪Bad2)).card:=Finset.card_le_card hcov
     _ <= (Good v).card+(Bad1∪Bad2).card:=Finset.card_union_le _ _
     _ <= (Good v).card+(Bad1.card+Bad2.card):=Nat.add_le_add_left (Finset.card_union_le _ _) _
     _ = (Good v).card+Bad1.card+Bad2.card:=by omega
  have hcast_cov:((Triples v).card:E)<=((Good v).card:E)+(Bad1.card:E)+(Bad2.card:E):=by exact_mod_cast hcard_cov
  linarith
 let Pairs:Finset (ℕ × (ℕ × ℕ × ℕ)):=B.biUnion (fun v=>(Good v).image (fun x=>(v,x)))
 have hPairs_lb:(B.card:E)*((L₀:E)^3/4)<=(Pairs.card:E):=by
  have hcard_eq:Pairs.card=∑ v∈B,(Good v).card:=by
    rw [card_biUnion]
    ·
     apply sum_congr rfl;intro v _;exact Finset.card_image_of_injective _ (fun a b h=>by simpa using h)
    ·
     intro v1 _ v2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro p hp1 hp2;rcases Finset.mem_image.mp hp1 with ⟨x1,_,rfl⟩;rcases Finset.mem_image.mp hp2 with ⟨x2,_,h⟩;exact hne (congrArg Prod.fst h).symm
  rw [hcard_eq,Nat.cast_sum]
  calc
    (B.card:E)*((L₀:E)^3/4)=∑ _v∈B,((L₀:E)^3/4):=by simp
    _ <= ∑ v∈B,((Good v).card:E):=sum_le_sum hGood_lb
 let AllSext:Finset ((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) :=(PrimeTriples P).biUnion (fun t=>(sextupleFiber N H P D D' t).image (fun q=>(t,q)))
 have hAllSext_card:AllSext.card=sextupleCount N H P D D':=by
  unfold sextupleCount;rw [card_biUnion]
  ·
    apply sum_congr rfl;intro t _;exact Finset.card_image_of_injective _ (fun a b h=>by simpa using h)
  ·
    intro t1 _ t2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro w hw1 hw2;rcases Finset.mem_image.mp hw1 with ⟨q1,_,rfl⟩;rcases Finset.mem_image.mp hw2 with ⟨q2,_,h⟩;exact hne (congrArg Prod.fst h).symm
 let Φ:(ℕ × (ℕ × ℕ × ℕ))->((ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)):=fun vx =>
  let v:=vx.1;let x:=vx.2
  ((minP (v+x.1),minP (v+x.2.1),minP (v+x.2.2)),(qOf (v+x.1),qOf (v+x.2.1),qOf (v+x.2.2)))
 have hΦ_mem:∀ vx∈Pairs,Φ vx∈AllSext:=by
  intro vx hvx;rcases Finset.mem_biUnion.mp hvx with ⟨v,hvB,hximg⟩;rcases Finset.mem_image.mp hximg with ⟨x,hxGood,rfl⟩;rcases mem_filter.mp hxGood with ⟨hxT,hgcd3,hgcd2⟩;rcases mem_filter.mp hxT with ⟨hxP,h12,h13,h23⟩;have hx1:=(mem_product.mp hxP).1
  have hx2:=(mem_product.mp (mem_product.mp hxP).2).1;have hx3:=(mem_product.mp (mem_product.mp hxP).2).2;have hm1:=hminP_spec (v+x.1) (mem_filter.mp (hAv_sub v hvB hx1)).2;have hm2:=hminP_spec (v+x.2.1) (mem_filter.mp (hAv_sub v hvB hx2)).2
  have hm3:=hminP_spec (v+x.2.2) (mem_filter.mp (hAv_sub v hvB hx3)).2;have hp12:=hminP_inj v hvB x.1 hx1 x.2.1 hx2 h12;have hp13:=hminP_inj v hvB x.1 hx1 x.2.2 hx3 h13;have hp23:=hminP_inj v hvB x.2.1 hx2 x.2.2 hx3 h23
  have ht_mem:(minP (v+x.1),minP (v+x.2.1),minP (v+x.2.2))∈PrimeTriples P := mem_filter.mpr ⟨mem_product.mpr ⟨hm1.1,mem_product.mpr ⟨hm2.1,hm3.1⟩⟩,hm1.2.1,hm2.2.1,hm3.2.1,hp12,hp13,hp23⟩;refine Finset.mem_biUnion.mpr ⟨_,ht_mem,Finset.mem_image.mpr ⟨_,?_,rfl⟩⟩
  have hv_lt:v < N:=(Finset.mem_Ico.mp (mem_filter.mp hvB).1).2;have hj1:=Finset.mem_Ioo.mp (mem_filter.mp (hAv_sub v hvB hx1)).1;have hj2:=Finset.mem_Ioo.mp (mem_filter.mp (hAv_sub v hvB hx2)).1
  have hj3:=Finset.mem_Ioo.mp (mem_filter.mp (hAv_sub v hvB hx3)).1;have heq1:(minP (v+x.1))^2*qOf (v+x.1)=v+x.1:=Nat.mul_div_cancel' hm1.2.2.1;have heq2:(minP (v+x.2.1))^2*qOf (v+x.2.1)=v+x.2.1:=Nat.mul_div_cancel' hm2.2.2.1
  have heq3:(minP (v+x.2.2))^2*qOf (v+x.2.2)=v+x.2.2:=Nat.mul_div_cancel' hm3.2.2.1
  have hq_range:∀ (p q j:ℕ),P<=p->0 < j->j < H->p^2*q=v+j → q∈Finset.Icc 1 (2*N/P^2):=by
    intro p q j hp hj0 hjH heq
    have hq1:1<=q:=by
     by_contra h0;push Not at h0
     have hq0:q=0:=Nat.lt_one_iff.mp h0;rw [hq0,mul_zero] at heq;omega
    have hP2_pos:0 < P^2:=by omega
    have hP2_le:P^2*q<=2*N:=by
     have h1:P^2*q<=p^2*q:=Nat.mul_le_mul_right q (Nat.pow_le_pow_left hp 2);omega
    have hq_le:q<=2*N/P^2:=(Nat.le_div_iff_mul_le hP2_pos).mpr (by rw [mul_comm];exact hP2_le);exact Finset.mem_Icc.mpr ⟨hq1,hq_le⟩
  unfold sextupleFiber;simp only [mem_filter,mem_product]
  refine ⟨⟨hq_range _ _ _ (Finset.mem_Ico.mp hm1.1).1 hj1.1 hj1.2 heq1,hq_range _ _ _ (Finset.mem_Ico.mp hm2.1).1 hj2.1 hj2.2 heq2,hq_range _ _ _ (Finset.mem_Ico.mp hm3.1).1 hj3.1 hj3.2 heq3⟩,by omega,by omega,by omega,?_,?_,?_,?_,?_,?_,hgcd3,hgcd2⟩
  ·
    have h1:((minP (v+x.1):ℤ)^2*(qOf (v+x.1):ℤ))=(v:ℤ)+(x.1:ℤ):=by exact_mod_cast heq1
    have h3:((minP (v+x.2.2):ℤ)^2*(qOf (v+x.2.2):ℤ))=(v:ℤ)+(x.2.2:ℤ):=by exact_mod_cast heq3
    rw [h1,h3,abs_lt];omega
  ·
    have h2:((minP (v+x.2.1):ℤ)^2*(qOf (v+x.2.1):ℤ))=(v:ℤ)+(x.2.1:ℤ):=by exact_mod_cast heq2
    have h3:((minP (v+x.2.2):ℤ)^2*(qOf (v+x.2.2):ℤ))=(v:ℤ)+(x.2.2:ℤ):=by exact_mod_cast heq3
    rw [h2,h3,abs_lt];omega
  ·
    have h1:((minP (v+x.1):ℤ)^2*(qOf (v+x.1):ℤ))=(v:ℤ)+(x.1:ℤ):=by exact_mod_cast heq1
    have h2:((minP (v+x.2.1):ℤ)^2*(qOf (v+x.2.1):ℤ))=(v:ℤ)+(x.2.1:ℤ):=by exact_mod_cast heq2
    rw [h1,h2,abs_lt];omega
  · rwa [heq1]
  · rwa [heq2]
  · rwa [heq3]
 have hfib_le:∀ w∈AllSext,(Pairs.filter (fun vx=>Φ vx=w)).card<=H:=by
  intro w _;let F:=Pairs.filter (fun vx=>Φ vx=w)
  have hinj:Set.InjOn (fun vx:ℕ × (ℕ × ℕ × ℕ)=>vx.2.1) F:=by
    intro a ha b hb heq;have ha_fl:=mem_filter.mp ha;have hb_fl:=mem_filter.mp hb;have hΦeq:Φ a=Φ b:=ha_fl.2.trans hb_fl.2.symm
    have extract_eq:∀ vx∈Pairs,(minP (vx.1+vx.2.1))^2*qOf (vx.1+vx.2.1)=vx.1+vx.2.1 ∧ (minP (vx.1+vx.2.2.1))^2*qOf (vx.1+vx.2.2.1)=vx.1+vx.2.2.1 ∧ (minP (vx.1+vx.2.2.2))^2*qOf (vx.1+vx.2.2.2)=vx.1+vx.2.2.2:=by
     intro vx hvx;rcases Finset.mem_biUnion.mp hvx with ⟨v,hvB,hximg⟩;rcases Finset.mem_image.mp hximg with ⟨x,hxGood,rfl⟩;have hxP:=(mem_filter.mp (mem_filter.mp hxGood).1).1;have hx1:=(mem_product.mp hxP).1;have hx2:=(mem_product.mp (mem_product.mp hxP).2).1
     have hx3:=(mem_product.mp (mem_product.mp hxP).2).2;have hm1:=hminP_spec (v+x.1) (mem_filter.mp (hAv_sub v hvB hx1)).2;have hm2:=hminP_spec (v+x.2.1) (mem_filter.mp (hAv_sub v hvB hx2)).2
     have hm3:=hminP_spec (v+x.2.2) (mem_filter.mp (hAv_sub v hvB hx3)).2;exact ⟨Nat.mul_div_cancel' hm1.2.2.1,Nat.mul_div_cancel' hm2.2.2.1,Nat.mul_div_cancel' hm3.2.2.1⟩
    have ha_eq:=extract_eq a ha_fl.1;have hb_eq:=extract_eq b hb_fl.1;dsimp only [Φ] at hΦeq;simp only [Prod.mk.injEq] at hΦeq;have h1:a.1+a.2.1=b.1+b.2.1:=by rw [← ha_eq.1,← hb_eq.1,hΦeq.1.1,hΦeq.2.1]
    have h2:a.1+a.2.2.1=b.1+b.2.2.1:=by rw [← ha_eq.2.1,← hb_eq.2.1,hΦeq.1.2.1,hΦeq.2.2.1]
    have h3:a.1+a.2.2.2=b.1+b.2.2.2:=by rw [← ha_eq.2.2,← hb_eq.2.2,hΦeq.1.2.2,hΦeq.2.2.2]
    dsimp only at heq;rcases a with ⟨va,xa1,xa2,xa3⟩;rcases b with ⟨vb,xb1,xb2,xb3⟩;simp only [Prod.mk.injEq] at h1 h2 h3 heq ⊢;omega
  have hsub_ioo:F.image (fun vx=>vx.2.1)⊆Finset.Ioo 0 H:=by
    intro j hj;rcases Finset.mem_image.mp hj with ⟨vx,hvx,rfl⟩;rcases Finset.mem_biUnion.mp (mem_filter.mp hvx).1 with ⟨v,hvB,hximg⟩;rcases Finset.mem_image.mp hximg with ⟨x,hxGood,rfl⟩;have hx1:=(mem_product.mp (mem_filter.mp (mem_filter.mp hxGood).1).1).1
    exact (mem_filter.mp (hAv_sub v hvB hx1)).1
  calc
    F.card=(F.image (fun vx=>vx.2.1)).card:=(Finset.card_image_iff.mpr hinj).symm
    _ <= (Finset.Ioo 0 H).card:=Finset.card_le_card hsub_ioo
    _ = H-1:=Nat.card_Ioo 0 H
    _ <= H:=Nat.sub_le H 1
 have hPairs_ub:(Pairs.card:E)<=(sextupleCount N H P D D':E)*(H:E):=by
  have hpart:Pairs.card=∑ w∈AllSext,(Pairs.filter (fun vx=>Φ vx=w)).card:=by
    rw [← card_biUnion]
    ·
     congr 1;ext vx;simp only [Finset.mem_biUnion,mem_filter];constructor
     · intro h;exact ⟨Φ vx,hΦ_mem vx h,h,rfl⟩
     · rintro ⟨_,_,h,_⟩;exact h
    ·
     intro w1 _ w2 _ hne;dsimp only [Function.onFun];rw [Finset.disjoint_left];intro vx h1 h2;exact hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)
  have hnat:Pairs.card<=AllSext.card*H:=by
    rw [hpart]
    calc
     _ <= ∑ _w∈AllSext,H:=sum_le_sum hfib_le
     _ = AllSext.card*H:=by simp
  rw [hAllSext_card] at hnat;exact_mod_cast hnat
 have hcomb:(B.card:E)*((L₀:E)^3/4)<=(sextupleCount N H P D D':E)*(H:E) :=hPairs_lb.trans hPairs_ub;have hL₀_pos:(0:E) < (L₀:E):=by exact_mod_cast (show 0 < L₀ by omega)
 have h4:(B.card:E)*(L₀:E)^3<=4*(H:E)*(sextupleCount N H P D D':E):=by linarith
 have hdiv:(B.card:E)<=(4*(H:E)*(sextupleCount N H P D D':E))/(L₀:E)^3 :=(le_div_iff₀ (pow_pos hL₀_pos 3)).mpr h4;have hrew:(4*(H:E)*(sextupleCount N H P D D':E))/(L₀:E)^3 = 4*(H:E)/(L₀:E)^3*(sextupleCount N H P D D':E):=by ring
 linarith
set_option maxHeartbeats 2500000 in
lemma card_badDyadic_le {r:E} (hr_lo:5/2<=r) (hr_hi:r < 8/3) :
  ∃ H₀:ℕ,64<=H₀/\∀ N H:ℕ,H₀<=H->4∣H → (H:E) < (N:E)^(1/5+(8/3-r)/100) → ((badDyadic N H).card:E)<=5*(N:E)/(H:E)^r:=by
 let ε:E:=(8/3-r)/100;have hε_pos:0 < ε:=by dsimp [ε];linarith
 have hε_le:ε<=1/600:=by dsimp [ε];linarith
 obtain ⟨H₁,hH₁_ge,hH₁_spec⟩ :=exists_threshold_log_pow_le (C:=10^17) (α:=10*ε) (by positivity) (by positivity) 5;obtain ⟨H₂,hH₂_ge,hH₂_spec⟩ :=exists_threshold_log_pow_le (C:=10^10) (α:=1/100) (by positivity) (by norm_num) 2;let H₀:ℕ:=max H₁ H₂
 refine ⟨H₀,by dsimp [H₀];omega,?_⟩;intro N H hH_ge h4H hH_lt_N;have hH_ge1000:1000<=H:=by dsimp [H₀] at hH_ge;omega
 have hHR_pos:(0:E) < (H:E):=by exact_mod_cast (show 0 < H by omega)
 have hHR_ge1:(1:E)<=(H:E):=by exact_mod_cast (show 1<=H by omega)
 have h10ε_le:10*ε<=1/60:=by linarith
 let LogH:E:=((Nat.log 2 H+1:ℕ):E);have hLogH_ge1:(1:E)<=LogH:=by dsimp [LogH];exact_mod_cast (Nat.succ_pos _)
 have hTh1:10^17*LogH^5<=(H:E)^(10*ε) :=hH₁_spec H (le_trans (le_max_left _ _) hH_ge);have hTh2:10^10*LogH^2<=(H:E)^(1/100:E) :=hH₂_spec H (le_trans (le_max_right _ _) hH_ge)
 have hN_pos:(0:E) < (N:E):=by
  by_contra hle;push Not at hle
  have hN0:N=0:=by
   have:(N:E)<=0:=hle
   have:N<=0:=by exact_mod_cast this
   omega
  rw [hN0,Nat.cast_zero,Real.zero_rpow (by positivity)] at hH_lt_N;linarith
 have hN_ge1:(1:E)<=(N:E):=by
  have:1<=N:=by
   by_contra h0;push Not at h0
   have hN0:N=0:=Nat.lt_one_iff.mp h0;rw [hN0,Nat.cast_zero] at hN_pos;linarith
  exact_mod_cast this
 have hN_lb:(H:E)^(5-25*ε)<=(N:E):=by
  have hrp:=rpow_le_rpow hHR_pos.le hH_lt_N.le (by linarith:(0:E)<=5-25*ε);rw [← rpow_mul hN_pos.le] at hrp;have hexp_le:(1/5+ε)*(5-25*ε)<=1:=by nlinarith
  calc
   (H:E)^(5-25*ε)<=(N:E)^((1/5+ε)*(5-25*ε)):=hrp
   _ <= (N:E)^(1:E):=rpow_le_rpow_of_exponent_le hN_ge1 hexp_le
   _ = (N:E):=rpow_one _
 have hN_ge_H4:(H:E)^4<=(N:E):=by
  calc
   (H:E)^4=(H:E)^(4:E):=(rpow_natCast _ 4).symm
   _ <= (H:E)^(5-25*ε):=rpow_le_rpow_of_exponent_le hHR_ge1 (by linarith)
   _ <= (N:E):=hN_lb
 have hHN:H<=N:=by
  have h1:(H:E)<=(H:E)^4:=by
   have:(H:E)^(1:E)<=(H:E)^((4:ℕ):E):=rpow_le_rpow_of_exponent_le hHR_ge1 (by norm_num)
   rwa [rpow_one,rpow_natCast] at this
  exact_mod_cast (h1.trans hN_ge_H4)
 let P₁:ℕ:=⌈(H:E)^(r+1)⌉₊;have hP₁_lb:(H:E)^(r+1)<=(P₁:E):=Nat.le_ceil _
 have hP₁_ge2:2<=P₁:=by
  have h1:(2:E)<=(H:E)^(r+1):=by
   calc
    (2:E)<=(H:E):=by exact_mod_cast (show 2<=H by omega)
    _ = (H:E)^(1:E):=(rpow_one _).symm
    _ <= (H:E)^(r+1):=rpow_le_rpow_of_exponent_le hHR_ge1 (by linarith)
  have:(2:E)<=(P₁:E):=h1.trans hP₁_lb
  exact_mod_cast this
 have hP₁_le_H4:P₁<=H^4:=by
  have h1:(H:E)^(r+1)<=(H:E)^4-1:=by
   have hH4:(H:E)^(r+1)<=(H:E)^(11/3:E) :=rpow_le_rpow_of_exponent_le hHR_ge1 (by linarith)
   have hgap:(2:E)<=(H:E)^(1/3:E):=by
    have:(2:E)^3<=(H:E):=by exact_mod_cast (show 8<=H by omega)
    have hrp:=rpow_le_rpow (by norm_num) this (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (2:E) 3,← rpow_mul (by norm_num)] at hrp;norm_num at hrp;exact hrp
   have hmul:2*(H:E)^(11/3:E)<=(H:E)^4:=by
    calc
     2*(H:E)^(11/3:E)<=(H:E)^(1/3:E)*(H:E)^(11/3:E) :=mul_le_mul_of_nonneg_right hgap (by positivity)
     _ = (H:E)^(4:E):=by rw [← rpow_add hHR_pos];norm_num
     _ = (H:E)^4:=rpow_natCast _ 4
   have hge1:(1:E)<=(H:E)^(11/3:E):=one_le_rpow hHR_ge1 (by norm_num);linarith
  have hlt:(P₁:E) < (H:E)^(r+1)+1:=Nat.ceil_lt_add_one (by positivity)
  have:(P₁:E)<=(H:E)^4:=by linarith
  exact_mod_cast this
 have hLarge_bd:((badLargePrimes N H P₁).card:E)<=4*(N:E)/(H:E)^r:=by
  have h1:=card_badLargePrimes_le hP₁_ge2 hHN
  calc
   ((badLargePrimes N H P₁).card:E)<=4*(N:E)*(H:E)/(P₁:E):=h1
   _ <= 4*(N:E)*(H:E)/(H:E)^(r+1) :=div_le_div_of_nonneg_left (by positivity) (by positivity) hP₁_lb
   _ = 4*(N:E)/(H:E)^r:=by
    rw [rpow_add hHR_pos,rpow_one];field_simp [hHR_pos.ne',(rpow_pos_of_pos hHR_pos r).ne']
 let P_of:ℕ->ℕ:=fun t=>(H/4)*2^t;let K_P:ℕ:=Nat.log 2 (4*P₁/H)+2;have hK_P_pos:(0:E) < (K_P:E):=by dsimp [K_P];positivity
 have hK_P_le:(K_P:E)<=6*LogH:=by
  have h4P₁:4*P₁/H<=H^4:=by
   have h1:4*P₁<=4*H^4:=Nat.mul_le_mul_left 4 hP₁_le_H4
   have h2:4*H^4/H<=H^4:=by
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have:4<=H:=by omega
    nlinarith [show H^4=H^3*H by ring]
   exact (Nat.div_le_div_right h1).trans h2
  have hlog_le:Nat.log 2 (4*P₁/H)<=Nat.log 2 (H^4):=Nat.log_mono_right h4P₁
  have hlog_pow:Nat.log 2 (H^4)<=4*(Nat.log 2 H+1):=by
   have hlt:H < 2^(Nat.log 2 H+1):=Nat.lt_pow_succ_log_self (by norm_num) H
   have hlt4:H^4 < 2^(4*(Nat.log 2 H+1)):=by
    calc
     H^4 < (2^(Nat.log 2 H+1))^4:=Nat.pow_lt_pow_left hlt (by norm_num)
     _ = 2^((Nat.log 2 H+1)*4):=(pow_mul 2 _ 4).symm
     _ = 2^(4*(Nat.log 2 H+1)):=by ring_nf
   exact (Nat.log_lt_of_lt_pow (by positivity) hlt4).le
  have hnat:K_P<=6*(Nat.log 2 H+1):=by dsimp [K_P];omega
  dsimp [LogH];exact_mod_cast hnat
 let L₀:ℕ:=H/(16*K_P)
 have h16K_le:32*(K_P:E)<=(H:E)/10:=by
  have h1:32*(K_P:E)<=192*LogH:=by linarith
  have h2:192*LogH<=10^10*LogH^2:=by nlinarith
  have h3:(H:E)^(1/100:E)<=(H:E)/10:=by
   have h10:(10:E)<=(H:E)^(99/100:E):=by
    have h1000:(1000:E)<=(H:E):=by exact_mod_cast hH_ge1000
    have:(10:E)^(1:E)<=(1000:E)^(99/100:E):=by
     have h10_3:(10:E)^3=1000:=by norm_num
     rw [← h10_3,← rpow_natCast (10:E) 3,← rpow_mul (by norm_num)];exact rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [rpow_one] at this;exact this.trans (rpow_le_rpow (by norm_num) h1000 (by norm_num))
   rw [le_div_iff₀ (by norm_num)]
   calc
    (H:E)^(1/100:E)*10<=(H:E)^(1/100:E)*(H:E)^(99/100:E) :=mul_le_mul_of_nonneg_left h10 (by positivity)
    _ = (H:E):=by rw [← rpow_add hHR_pos];norm_num
  linarith
 have hL₀_ge10:10<=L₀:=by
  have h1:10*(16*K_P)<=H:=by
   have:(160:E)*(K_P:E)<=(H:E):=by linarith
   have h160:160*K_P<=H:=by exact_mod_cast this
   omega
  exact (Nat.le_div_iff_mul_le (by dsimp [K_P];omega)).mpr h1
 have hL₀_lb:(H:E)/(32*(K_P:E))<=(L₀:E):=by
  have h1:(H:E)/(16*(K_P:E))-1<=(L₀:E):=by
   have hlt:H < (16*K_P)*(L₀+1):=by
    have:=Nat.div_add_mod H (16*K_P)
    have:=Nat.mod_lt H (show 0 < 16*K_P by dsimp [K_P];omega)
    dsimp [L₀];nlinarith
   have hltR:(H:E) < (16*(K_P:E))*((L₀:E)+1):=by exact_mod_cast hlt
   have hdiv:(H:E)/(16*(K_P:E)) < (L₀:E)+1 :=(div_lt_iff₀ (by positivity)).mpr (by linarith);linarith
  have h2:(1:E)<=(H:E)/(32*(K_P:E)) :=(one_le_div (by positivity)).mpr (by linarith);have h3:(H:E)/(16*(K_P:E))=2*((H:E)/(32*(K_P:E))):=by ring
  linarith
 have hcov:badDyadic N H ⊆
   badLargePrimes N H P₁∪(Finset.range K_P).biUnion (fun t=>badDyadicPrime N H (P_of t) L₀):=by
  intro v hv;rcases mem_filter.mp hv with ⟨hv_ico,hno_sq⟩
  by_cases hlg:v∈badLargePrimes N H P₁
  · exact Finset.mem_union_left _ hlg
  ·
   apply Finset.mem_union_right
   by_contra hnone
   simp only [Finset.mem_biUnion,Finset.mem_range,badDyadicPrime,mem_filter,not_exists,not_and,not_le] at hnone;let Jsmall:=(Finset.Ioo 0 H).filter (fun j=>∃ p,p < H/4/\Nat.Prime p/\p^2∣v+j)
   let Jdyad:ℕ->Finset ℕ:=fun t =>
    (Finset.Ioo 0 H).filter (fun j=>∃ p∈Finset.Ico (P_of t) (2*P_of t),Nat.Prime p/\p^2∣v+j)
   have hIoo_cov:Finset.Ioo 0 H⊆Jsmall∪(Finset.range K_P).biUnion Jdyad:=by
    intro j hj;have hnsq:=hno_sq j hj;rw [Nat.squarefree_iff_prime_squarefree] at hnsq
    push Not at hnsq
    obtain ⟨p,hp_pr,hp_dvd⟩:=hnsq;have hp_sq_dvd:p^2∣v+j:=by simpa [sq] using hp_dvd
    have hp_lt_P₁:p < P₁:=by
     by_contra hge
     exact hlg (mem_filter.mpr ⟨hv_ico,j,hj,p,by omega,hp_pr,hp_sq_dvd⟩)
    by_cases hsm:p < H/4
    · exact Finset.mem_union_left _ (mem_filter.mpr ⟨hj,p,hsm,hp_pr,hp_sq_dvd⟩)
    ·
     apply Finset.mem_union_right;have hH4_eq:4*(H/4)=H:=Nat.mul_div_cancel' h4H;have hq_pos:1<=p/(H/4):=Nat.div_pos (by omega) (by omega);let t:=Nat.log 2 (p/(H/4));have ht_lo:2^t<=p/(H/4):=Nat.pow_log_le_self 2 (by omega)
     have ht_hi:p/(H/4) < 2^(t+1):=Nat.lt_pow_succ_log_self (by norm_num) _
     have hP_le_p:P_of t<=p:=by
      dsimp [P_of];exact (Nat.mul_le_mul_left _ ht_lo).trans (Nat.mul_div_le p (H/4))
     have hp_lt_2P:p < 2*P_of t:=by
      dsimp [P_of]
      have h1:p < (H/4)*(p/(H/4)+1):=by
       have:=Nat.div_add_mod p (H/4)
       have:=Nat.mod_lt p (show 0 < H/4 by omega)
       nlinarith
      have h2:p/(H/4)+1<=2^(t+1):=ht_hi;have h3:(H/4)*2^(t+1)=2*((H/4)*2^t):=by rw [pow_succ];ring
      calc
       p < (H/4)*(p/(H/4)+1):=h1
       _ <= (H/4)*2^(t+1):=Nat.mul_le_mul_left _ h2
       _ = 2*((H/4)*2^t):=h3
     have ht_lt:t < K_P:=by
      have hdiv_le:p/(H/4)<=4*P₁/H:=by
       rw [Nat.le_div_iff_mul_le (by omega)];have h1:(H/4)*(p/(H/4))<=p:=Nat.mul_div_le p (H/4)
       have h2:(p/(H/4))*H=4*((H/4)*(p/(H/4))):=by
        calc
         (p/(H/4))*H=(p/(H/4))*(4*(H/4)):=by rw [hH4_eq]
         _ = 4*((H/4)*(p/(H/4))):=by ring
       omega
      have hlog_le:t<=Nat.log 2 (4*P₁/H):=Nat.log_mono_right hdiv_le;dsimp [K_P];omega
     exact Finset.mem_biUnion.mpr ⟨t,Finset.mem_range.mpr ht_lt,mem_filter.mpr ⟨hj,p,Finset.mem_Ico.mpr ⟨hP_le_p,hp_lt_2P⟩,hp_pr,hp_sq_dvd⟩⟩
   have hcard_tot:((Finset.Ioo 0 H).card:E) ≤ (Jsmall.card:E)+∑ t∈Finset.range K_P,((Jdyad t).card:E):=by
    have h1:(Finset.Ioo 0 H).card<=Jsmall.card+((Finset.range K_P).biUnion Jdyad).card :=(Finset.card_le_card hIoo_cov).trans (Finset.card_union_le _ _)
    have h2:((Finset.range K_P).biUnion Jdyad).card<=∑ t∈Finset.range K_P,(Jdyad t).card :=Finset.card_biUnion_le;exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
   have hsmall_lt:(Jsmall.card:E) < (3/4:E)*(H:E):=card_small_prime_sq_lt v H (by omega)
   have hdyad_le:∑ t∈Finset.range K_P,((Jdyad t).card:E)<=(H:E)/16:=by
    have h1:∑ t∈Finset.range K_P,(Jdyad t).card<=K_P*L₀:=by
     calc
      _ <= ∑ _t∈Finset.range K_P,L₀:=sum_le_sum (fun t ht =>
       (hnone t (Finset.mem_range.mp ht) hv_ico).le)
      _ = K_P*L₀:=by simp
    have h2:K_P*L₀<=H/16:=by
     have:(16*K_P)*L₀<=H:=Nat.mul_div_le H (16*K_P)
     exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
    have h3:((H/16:ℕ):E)<=(H:E)/16:=by rw [le_div_iff₀ (by norm_num)];exact_mod_cast Nat.div_mul_le_self H 16
    exact (by exact_mod_cast (h1.trans h2):_ <= ((H/16:ℕ):E)).trans h3
   have hIoo_eq:((Finset.Ioo 0 H).card:E)=(H:E)-1:=by rw [Nat.card_Ioo,Nat.sub_zero,Nat.cast_sub (by omega:1<=H),Nat.cast_one]
   have hHR1000:(1000:E)<=(H:E):=by exact_mod_cast hH_ge1000
   linarith
 have hP_bound:∀ t∈Finset.range K_P,((badDyadicPrime N H (P_of t) L₀).card:E)<=(N:E)/((K_P:E)*(H:E)^r):=by
  intro t _;set P:=P_of t;have hH4_eq:4*(H/4)=H:=Nat.mul_div_cancel' h4H;have hP_ge_H4:H/4<=P:=Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) t);have h4P_ge_H:H<=4*P:=by omega
  have hP_ge4:4<=P:=by omega
  have hP_pos:(0:E) < (P:E):=by exact_mod_cast (show 0 < P by omega)
  have h4H_le_P2:4*H<=P^2:=by
   have h1:(H/4)^2<=P^2:=Nat.pow_le_pow_left hP_ge_H4 2;have h2:4*H<=(H/4)^2:=by nlinarith
   omega
  have hP_cut_pos:0 < (H:E)^(10/9-60*ε):=by positivity
  by_cases hwin:(P:E)<=(H:E)^(10/9-60*ε)/\(N:E)<=(H:E)^(49/9-240*ε)
  ·
   have hemp:badDyadicPrime N H P L₀=∅:=by
    rw [Finset.eq_empty_iff_forall_notMem];intro v hv;rcases mem_filter.mp hv with ⟨hv_ico,hcard_ge⟩;have hv_lo:N/2<=v:=(Finset.mem_Ico.mp hv_ico).1;have hv_lt:v < N:=(Finset.mem_Ico.mp hv_ico).2
    have hv_ge1:1<=v:=by
     have hN2:2<=N:=by omega
     omega
    have hvR_le_N:(v:E)<=(N:E):=by exact_mod_cast hv_lt.le
    have hcov_dyad:=card_dyadic_covered_le v H P (by omega);have hRA:=dyadicPrimeSet_rangeA_le hv_ge1 (by omega) (by omega) h4H_le_P2;have hL₀_le_dyad:(L₀:E)<=((dyadicPrimeSet v H P).card:E):=by exact_mod_cast hcard_ge.trans hcov_dyad
    have ht1:(v:E)^(1/10:E)*(P:E)^(2/5:E)<=(H:E)^(99/100:E):=by
     have h1:(v:E)^(1/10:E)<=(H:E)^((49/9-240*ε)*(1/10:E)):=by
      calc
       (v:E)^(1/10:E)<=(N:E)^(1/10:E) :=rpow_le_rpow (Nat.cast_nonneg v) hvR_le_N (by norm_num)
       _ <= ((H:E)^(49/9-240*ε))^(1/10:E) :=rpow_le_rpow hN_pos.le hwin.2 (by norm_num)
       _ = (H:E)^((49/9-240*ε)*(1/10:E)):=(rpow_mul hHR_pos.le _ _).symm
     have h2:(P:E)^(2/5:E)<=(H:E)^((10/9-60*ε)*(2/5:E)):=by
      calc
       (P:E)^(2/5:E)<=((H:E)^(10/9-60*ε))^(2/5:E) :=rpow_le_rpow hP_pos.le hwin.1 (by norm_num)
       _ = (H:E)^((10/9-60*ε)*(2/5:E)):=(rpow_mul hHR_pos.le _ _).symm
     calc
      _ <= (H:E)^((49/9-240*ε)*(1/10:E)) * (H:E)^((10/9-60*ε)*(2/5:E)) :=mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (H:E)^((49/9-240*ε)*(1/10:E)+(10/9-60*ε)*(2/5:E)) :=(rpow_add hHR_pos _ _).symm
      _ <= (H:E)^(99/100:E) :=rpow_le_rpow_of_exponent_le hHR_ge1 (by linarith)
    have ht2:(P:E)^(2/3:E)*(H:E)^(1/6:E)<=(H:E)^(99/100:E):=by
     have h1:(P:E)^(2/3:E)<=(H:E)^((10/9-60*ε)*(2/3:E)):=by
      calc
       (P:E)^(2/3:E)<=((H:E)^(10/9-60*ε))^(2/3:E) :=rpow_le_rpow hP_pos.le hwin.1 (by norm_num)
       _ = (H:E)^((10/9-60*ε)*(2/3:E)):=(rpow_mul hHR_pos.le _ _).symm
     calc
      _ <= (H:E)^((10/9-60*ε)*(2/3:E))*(H:E)^(1/6:E) :=mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (H:E)^((10/9-60*ε)*(2/3:E)+1/6):=(rpow_add hHR_pos _ _).symm
      _ <= (H:E)^(99/100:E):=rpow_le_rpow_of_exponent_le hHR_ge1 (by linarith)
    have ht3:(H:E)^(1/4:E)*(P:E)/(v:E)^(1/4:E)<=2*(H:E)^(99/100:E):=by
     have hv_lb4:(H:E)^4/16<=(v:E):=by
      have h1:N<=2*v+1:=by omega
      have h1R:(N:E)<=2*(v:E)+1:=by exact_mod_cast h1
      have h1000:(1000:E)<=(H:E):=by exact_mod_cast hH_ge1000
      have hH4_big:(16:E)<=(H:E)^4:=by
       have hsq:(100:E)<=(H:E)^2:=by nlinarith
       nlinarith
      linarith
     have hv14:(H:E)/2<=(v:E)^(1/4:E):=by
      have h1:((H:E)/2)^4<=(v:E):=by
       have:((H:E)/2)^4=(H:E)^4/16:=by ring
       linarith
      have hrp:=rpow_le_rpow (by positivity) h1 (by norm_num:(0:E)<=1/4);rw [← rpow_natCast ((H:E)/2) 4,← rpow_mul (by positivity)] at hrp;norm_num at hrp;exact hrp
     calc
      (H:E)^(1/4:E)*(P:E)/(v:E)^(1/4:E)
        ≤ (H:E)^(1/4:E)*(H:E)^(10/9-60*ε)/((H:E)/2) :=
       div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hwin.1 (by positivity))
        (by positivity) hv14
      _ = 2*((H:E)^(1/4+(10/9-60*ε))*(H:E)^(-(1:E))):=by
       rw [rpow_add hHR_pos,rpow_neg hHR_pos.le,rpow_one];field_simp [hHR_pos.ne']
      _ = 2*(H:E)^(1/4+(10/9-60*ε)-1):=by rw [← rpow_add hHR_pos,← sub_eq_add_neg]
      _ <= 2*(H:E)^(99/100:E) :=mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hHR_ge1 (by linarith)) (by norm_num)
    have ht4:(1:E)<=(H:E)^(99/100:E):=one_le_rpow hHR_ge1 (by norm_num);have hdyad_ub:((dyadicPrimeSet v H P).card:E)<=15*10^5*(H:E)^(99/100:E):=by linarith
    have hL₀_gt:15*10^5*(H:E)^(99/100:E) < (L₀:E):=by
     have h1:32*(K_P:E)*(15*10^5) < (H:E)^(1/100:E):=by
      have h2:32*(K_P:E)*(15*10^5)<=288*10^6*LogH:=by linarith
      have h3:288*10^6*LogH < 10^10*LogH^2:=by nlinarith
      linarith
     have h2:(15*10^5)*(H:E)^(99/100:E) < (H:E)/(32*(K_P:E)):=by
      rw [lt_div_iff₀ (by positivity)]
      calc
       (15*10^5)*(H:E)^(99/100:E)*(32*(K_P:E))
         = (32*(K_P:E)*(15*10^5))*(H:E)^(99/100:E):=by ring
       _ < (H:E)^(1/100:E)*(H:E)^(99/100:E) :=mul_lt_mul_of_pos_right h1 (by positivity)
       _ = (H:E):=by rw [← rpow_add hHR_pos];norm_num
     linarith
    linarith
   rw [hemp,Finset.card_empty,Nat.cast_zero];positivity
  ·
   let D:ℕ:=⌈8*((H:E)/(L₀:E))^(3/2:E)⌉₊+2;let D':ℕ:=⌈32*((H:E)/(L₀:E))^2⌉₊+2
   have hHL₀_le:(H:E)/(L₀:E)<=192*LogH:=by
    have hL₀_pos:(0:E) < (L₀:E):=by exact_mod_cast (show 0 < L₀ by omega)
    calc
     (H:E)/(L₀:E)<=(H:E)/((H:E)/(32*(K_P:E))) :=div_le_div_of_nonneg_left hHR_pos.le (by positivity) hL₀_lb
     _ = 32*(K_P:E):=by field_simp [hHR_pos.ne',hK_P_pos.ne']
     _ <= 192*LogH:=by linarith
   have hD_big:8*(H:E)^3/(D:E)^2<=(L₀:E)^3/8:=by
    have h1:8*((H:E)/(L₀:E))^(3/2:E)<=(D:E):=by
     have:=Nat.le_ceil (8*((H:E)/(L₀:E))^(3/2:E))
     have h2:((⌈8*((H:E)/(L₀:E))^(3/2:E)⌉₊:ℕ):E)<=(D:E):=by dsimp [D];push_cast;linarith
     exact this.trans h2
    have hsq:64*((H:E)/(L₀:E))^3<=(D:E)^2:=by
     have hp:=pow_le_pow_left₀ (by positivity) h1 2;rw [mul_pow,← rpow_natCast (((H:E)/(L₀:E))^(3/2:E)) 2,← rpow_mul (by positivity)] at hp;have h32:(3/2:E)*((2:ℕ):E)=(3:ℕ):=by norm_num
     rw [h32,rpow_natCast] at hp;linarith
    have hL₀_pos:(0:E) < (L₀:E):=by exact_mod_cast (show 0 < L₀ by omega)
    have hD_pos:(0:E) < (D:E):=by dsimp [D];positivity
    rw [div_le_div_iff₀ (pow_pos hD_pos 2) (by norm_num)];have hmul:=mul_le_mul_of_nonneg_left hsq (pow_nonneg hL₀_pos.le 3);have hrew:(L₀:E)^3*(64*((H:E)/(L₀:E))^3)=64*(H:E)^3:=by field_simp [hL₀_pos.ne']
    linarith
   have hD'_big:4*(L₀:E)*(H:E)^2/(D':E)<=(L₀:E)^3/8:=by
    have h1:32*((H:E)/(L₀:E))^2<=(D':E):=by
     have:=Nat.le_ceil (32*((H:E)/(L₀:E))^2)
     have h2:((⌈32*((H:E)/(L₀:E))^2⌉₊:ℕ):E)<=(D':E):=by dsimp [D'];push_cast;linarith
     exact this.trans h2
    have hL₀_pos:(0:E) < (L₀:E):=by exact_mod_cast (show 0 < L₀ by omega)
    have hD'_pos:(0:E) < (D':E):=by dsimp [D'];positivity
    rw [div_le_div_iff₀ hD'_pos (by norm_num)];have hmul:=mul_le_mul_of_nonneg_left h1 (pow_nonneg hL₀_pos.le 3);have hrew:(L₀:E)^3*(32*((H:E)/(L₀:E))^2)=32*(L₀:E)*(H:E)^2:=by field_simp [hL₀_pos.ne']
    linarith
   have hD_le_H:D<=H:=by
    have h1:(D:E)<=8*(192*LogH)^(3/2:E)+3:=by
     have hlt:=Nat.ceil_lt_add_one (by positivity:(0:E)<=8*((H:E)/(L₀:E))^(3/2:E));have hrp:((H:E)/(L₀:E))^(3/2:E)<=(192*LogH)^(3/2:E) :=rpow_le_rpow (by positivity) hHL₀_le (by norm_num)
     have hDcast:(D:E)=(⌈8*((H:E)/(L₀:E))^(3/2:E)⌉₊:E)+2:=by dsimp [D];push_cast;ring
     linarith
    have h2:(192*LogH)^(3/2:E)<=(192*LogH)^2:=by
     have hge1:(1:E)<=192*LogH:=by linarith
     calc
      _ <= (192*LogH)^(2:E):=rpow_le_rpow_of_exponent_le hge1 (by norm_num)
      _ = (192*LogH)^2:=rpow_natCast _ 2
    have h3:(D:E)<=10^10*LogH^2:=by nlinarith
    have h4:(H:E)^(1/100:E)<=(H:E):=by
     calc
      _ <= (H:E)^(1:E):=rpow_le_rpow_of_exponent_le hHR_ge1 (by norm_num)
      _ = (H:E):=rpow_one _
    exact_mod_cast (h3.trans (hTh2.trans h4))
   have hD'_13:(D':E)^(1/3:E)<=200*LogH:=by
    have h1:(D':E)<=32*(192*LogH)^2+3:=by
     have hlt:=Nat.ceil_lt_add_one (by positivity:(0:E)<=32*((H:E)/(L₀:E))^2);have hsq:=pow_le_pow_left₀ (by positivity) hHL₀_le 2;have hcast:(D':E)=(⌈32*((H:E)/(L₀:E))^2⌉₊:E)+2:=by dsimp [D'];push_cast;ring
     linarith
    have h2:(D':E)<=(200*LogH)^3:=by nlinarith [sq_nonneg LogH]
    have hrp:=rpow_le_rpow (Nat.cast_nonneg D') h2 (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (200*LogH) 3,← rpow_mul (by positivity)] at hrp;norm_num at hrp;exact hrp
   have hdc:=card_badDyadicPrime_le_sextupleCount (P:=P) (show 1<=N by omega) (show 1<=H by omega)
    hHN (by omega) hL₀_ge10 (show 2<=D by dsimp [D];omega) (show 2<=D' by dsimp [D'];omega) hD_big hD'_big
   have hsex:=sextupleCount_le (show 1<=N by omega) (show 1<=H by omega) hP_ge4 h4P_ge_H
    (show 1<=D by dsimp [D];omega) hD_le_H (show 1<=D' by dsimp [D'];omega)
   have hpref:4*(H:E)/(L₀:E)^3*((K_P:E)*(H:E)^r) ≤ 2*10^8*LogH^4*(H:E)^(r-2):=by
    have h1:4*(H:E)/(L₀:E)^3<=4*(192*LogH)^3/(H:E)^2:=by
     have hL₀_pos:(0:E) < (L₀:E):=by exact_mod_cast (show 0 < L₀ by omega)
     have hcub:=pow_le_pow_left₀ (by positivity) hHL₀_le 3;have hrew:4*(H:E)/(L₀:E)^3=4*((H:E)/(L₀:E))^3/(H:E)^2:=by field_simp [hHR_pos.ne',hL₀_pos.ne']
     rw [hrew];exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcub (by norm_num)) (by positivity)
    have h2:(4*(192*LogH)^3/(H:E)^2)*((6*LogH)*(H:E)^r) = (4*192^3*6:E)*LogH^4*(H:E)^(r-2):=by
     have hHr:(H:E)^r/(H:E)^2=(H:E)^(r-2):=by
      rw [sub_eq_add_neg,rpow_add hHR_pos,rpow_neg hHR_pos.le,← div_eq_mul_inv,Real.rpow_two]
     calc
      (4*(192*LogH)^3/(H:E)^2)*((6*LogH)*(H:E)^r)
        = (4*192^3*6:E)*LogH^4*((H:E)^r/(H:E)^2):=by ring
      _ = (4*192^3*6:E)*LogH^4*(H:E)^(r-2):=by rw [hHr]
    calc
     4*(H:E)/(L₀:E)^3*((K_P:E)*(H:E)^r)
       ≤ (4*(192*LogH)^3/(H:E)^2)*((6*LogH)*(H:E)^r) :=
      mul_le_mul h1 (mul_le_mul_of_nonneg_right hK_P_le (by positivity)) (by positivity) (by positivity)
     _ = (4*192^3*6:E)*LogH^4*(H:E)^(r-2):=h2
     _ <= (2*10^8:E)*LogH^4*(H:E)^(r-2):=by
      have hnn:0<=LogH^4*(H:E)^(r-2):=by positivity
      have hnum:(4*192^3*6:E)<=2*10^8:=by norm_num
      nlinarith
   let W:E:=14*10^8*LogH^4*(H:E)^(r-2);have hW_pos:0 < W:=by dsimp [W];positivity
   have hH_10ε_le_13:(H:E)^(10*ε)<=(H:E)^(1/3:E) :=rpow_le_rpow_of_exponent_le hHR_ge1 (by linarith);have hH_10ε_le_110:(H:E)^(10*ε)<=(H:E)^(1/10:E) :=rpow_le_rpow_of_exponent_le hHR_ge1 (by linarith);have hLog5_10ε:10^17*LogH^5<=(H:E)^(10*ε):=hTh1
   have hLog4_10ε:10^17*LogH^4<=(H:E)^(10*ε):=by
    have:LogH^4<=LogH^5:=by nlinarith [pow_nonneg (show 0<=LogH by linarith) 4]
    linarith
   have hT1:W*(6000*(N:E)*(H:E)^2/(P:E)^3)<=(N:E):=by
    have hP3:(H:E)^3/64<=(P:E)^3:=by
     have h1:(H:E)/4<=(P:E):=by
      have:(H:E)<=4*(P:E):=by exact_mod_cast h4P_ge_H
      linarith
     have hp:=pow_le_pow_left₀ (by positivity) h1 3
     have:((H:E)/4)^3=(H:E)^3/64:=by ring
     linarith
    have hfrac:6000*(N:E)*(H:E)^2/(P:E)^3<=384000*(N:E)/(H:E):=by
     calc
      6000*(N:E)*(H:E)^2/(P:E)^3
        ≤ 6000*(N:E)*(H:E)^2/((H:E)^3/64) :=
       div_le_div_of_nonneg_left (by positivity) (by positivity) hP3
      _ = 384000*(N:E)/(H:E):=by field_simp [hHR_pos.ne'];ring
    have hHr3:(H:E)^(r-2)/(H:E)<=(H:E)^(-(1/3:E)):=by
     rw [div_eq_mul_inv,← Real.rpow_neg_one,← rpow_add hHR_pos];exact rpow_le_rpow_of_exponent_le hHR_ge1 (by linarith)
    calc
     W*(6000*(N:E)*(H:E)^2/(P:E)^3)
       ≤ W*(384000*(N:E)/(H:E)):=mul_le_mul_of_nonneg_left hfrac hW_pos.le
     _ = (14*10^8*384000*LogH^4)*((H:E)^(r-2)/(H:E))*(N:E):=by dsimp [W];ring
     _ <= (10^17*LogH^4)*(H:E)^(-(1/3:E))*(N:E):=by
      have hc:(14*10^8*384000:E)*LogH^4<=10^17*LogH^4 :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity);exact mul_le_mul_of_nonneg_right (mul_le_mul hc hHr3 (by positivity) (by positivity)) hN_pos.le
     _ <= (H:E)^(1/3:E)*(H:E)^(-(1/3:E))*(N:E) :=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hLog4_10ε.trans hH_10ε_le_13) (by positivity)) hN_pos.le
     _ = (N:E):=by rw [← rpow_add hHR_pos];norm_num
   have hT2:W*(200*(N:E)*(H:E)/(P:E)^3)<=(N:E):=by
    have hle:200*(N:E)*(H:E)/(P:E)^3<=6000*(N:E)*(H:E)^2/(P:E)^3:=by
     apply div_le_div_of_nonneg_right _ (by positivity);have hHsq:(H:E)<=(H:E)^2:=by nlinarith
     have h1:200*(H:E)<=6000*(H:E)^2:=by linarith
     have h2:=mul_le_mul_of_nonneg_left h1 hN_pos.le;linarith
    exact (mul_le_mul_of_nonneg_left hle hW_pos.le).trans hT1
   have hT3:W*(200000*(H:E)^3)<=(N:E):=by
    have hHr1:(H:E)^(r-2)*(H:E)^3<=(H:E)^(11/3:E):=by
     rw [← rpow_natCast (H:E) 3,← rpow_add hHR_pos];exact rpow_le_rpow_of_exponent_le hHR_ge1 (by push_cast;linarith)
    calc
     W*(200000*(H:E)^3)
       = (14*10^8*200000*LogH^4)*((H:E)^(r-2)*(H:E)^3):=by
      dsimp [W];ring
     _ <= (10^17*LogH^4)*(H:E)^(11/3:E):=by
      have hc:(14*10^8*200000:E)*LogH^4<=10^17*LogH^4 :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity);exact mul_le_mul hc hHr1 (by positivity) (by positivity)
     _ <= (H:E)^(1/3:E)*(H:E)^(11/3:E) :=mul_le_mul_of_nonneg_right (hLog4_10ε.trans hH_10ε_le_13) (by positivity)
     _ = (H:E)^4:=by rw [← rpow_add hHR_pos];norm_num
     _ <= (N:E):=hN_ge_H4
   have hT4:W*min (10^7*(N:E)*(H:E)/(P:E)^(3/2:E))
     (4*10^4*(N:E)^(1/2:E)*(H:E)^(3/2:E)*(P:E)^(1/2:E))<=(N:E):=by
    by_cases hPgt:(H:E)^(10/9-60*ε) < (P:E)
    ·
     have hP32:(H:E)^(5/3-90*ε)<=(P:E)^(3/2:E):=by
      have hrp:=rpow_le_rpow (by positivity) hPgt.le (by norm_num:(0:E)<=3/2);rw [← rpow_mul hHR_pos.le] at hrp;convert hrp using 2;ring
     have hHexp:(H:E)^(r-2)*(H:E)/(H:E)^(5/3-90*ε) = (H:E)^(-(10*ε)):=by
      rw [div_eq_mul_inv,← rpow_neg hHR_pos.le]
      conv_lhs=>arg 1;arg 2;rw [← rpow_one (H:E)]
      rw [← rpow_add hHR_pos,← rpow_add hHR_pos];congr 1;dsimp [ε];ring
     calc
      W*min _ _ <= W*(10^7*(N:E)*(H:E)/(P:E)^(3/2:E)) :=mul_le_mul_of_nonneg_left (min_le_left _ _) hW_pos.le
      _ <= W*(10^7*(N:E)*(H:E)/(H:E)^(5/3-90*ε)) :=mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (by positivity) (by positivity) hP32) hW_pos.le
      _ = (14*10^15*LogH^4)*((H:E)^(r-2)*(H:E)/(H:E)^(5/3-90*ε))*(N:E):=by dsimp [W];ring
      _ = (14*10^15*LogH^4)*(H:E)^(-(10*ε))*(N:E):=by rw [hHexp]
      _ <= (10^17*LogH^4)*(H:E)^(-(10*ε))*(N:E):=by
       have hc:(14*10^15:E)*LogH^4<=10^17*LogH^4 :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity);exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hN_pos.le
      _ <= (H:E)^(10*ε)*(H:E)^(-(10*ε))*(N:E) :=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLog4_10ε (by positivity)) hN_pos.le
      _ = (N:E):=by rw [← rpow_add hHR_pos];simp
    ·
     push Not at hPgt
     have hNgt:(H:E)^(49/9-240*ε) < (N:E):=by
      by_contra hle;push Not at hle;exact hwin ⟨hPgt,hle⟩
     have hP12:(P:E)^(1/2:E)<=(H:E)^(5/9-30*ε):=by
      have hrp:=rpow_le_rpow hP_pos.le hPgt (by norm_num:(0:E)<=1/2);rw [← rpow_mul hHR_pos.le] at hrp;convert hrp using 2;ring
     have hN12:(H:E)^(49/18-120*ε)<=(N:E)^(1/2:E):=by
      have hrp:=rpow_le_rpow (by positivity) hNgt.le (by norm_num:(0:E)<=1/2);rw [← rpow_mul hHR_pos.le] at hrp;convert hrp using 2;ring
     have hHprod:(H:E)^(r-2)*(H:E)^(3/2:E)*(H:E)^(5/9-30*ε) = (H:E)^(49/18-130*ε):=by
      rw [← rpow_add hHR_pos,← rpow_add hHR_pos];congr 1;dsimp [ε];ring
     calc
      W*min _ _ <= W*(4*10^4*(N:E)^(1/2:E)*(H:E)^(3/2:E)*(P:E)^(1/2:E)) :=mul_le_mul_of_nonneg_left (min_le_right _ _) hW_pos.le
      _ <= W*(4*10^4*(N:E)^(1/2:E)*(H:E)^(3/2:E)*(H:E)^(5/9-30*ε)):=by
       apply mul_le_mul_of_nonneg_left _ hW_pos.le;exact mul_le_mul_of_nonneg_left hP12 (by positivity)
      _ = (14*4*10^12*LogH^4) * ((H:E)^(r-2)*(H:E)^(3/2:E)*(H:E)^(5/9-30*ε)) * (N:E)^(1/2:E):=by dsimp [W];ring
      _ = (56*10^12*LogH^4)*(H:E)^(49/18-130*ε)*(N:E)^(1/2:E):=by rw [hHprod];ring
      _ <= (10^17*LogH^4)*(H:E)^(49/18-130*ε)*(N:E)^(1/2:E):=by
       have hc:(56*10^12:E)*LogH^4<=10^17*LogH^4 :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity);exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
      _ <= (H:E)^(10*ε)*(H:E)^(49/18-130*ε)*(N:E)^(1/2:E) :=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLog4_10ε (by positivity)) (by positivity)
      _ = (H:E)^(49/18-120*ε)*(N:E)^(1/2:E):=by rw [← rpow_add hHR_pos];congr 2;ring
      _ <= (N:E)^(1/2:E)*(N:E)^(1/2:E) :=mul_le_mul_of_nonneg_right hN12 (by positivity)
      _ = (N:E):=by rw [← rpow_add hN_pos];norm_num
   have hT5:W*(300*(N:E)^(3/5:E)*(H:E)^(6/5:E))<=(N:E):=by
    have hN25:(H:E)^(2-10*ε)<=(N:E)^(2/5:E):=by
     have hrp:=rpow_le_rpow (by positivity) hN_lb (by norm_num:(0:E)<=2/5);rw [← rpow_mul hHR_pos.le] at hrp;convert hrp using 2;ring
    have hHprod:(H:E)^(1/10:E)*((H:E)^(r-2)*(H:E)^(6/5:E)) ≤ (H:E)^(2-10*ε):=by
     rw [← rpow_add hHR_pos,← rpow_add hHR_pos];exact rpow_le_rpow_of_exponent_le hHR_ge1 (by dsimp [ε];linarith)
    calc
     W*(300*(N:E)^(3/5:E)*(H:E)^(6/5:E))
       = (42*10^10*LogH^4)*((H:E)^(r-2)*(H:E)^(6/5:E)) * (N:E)^(3/5:E):=by dsimp [W];ring
     _ <= (10^17*LogH^4)*((H:E)^(r-2)*(H:E)^(6/5:E)) * (N:E)^(3/5:E):=by
      have hc:(42*10^10:E)*LogH^4<=10^17*LogH^4 :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity);exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
     _ <= (H:E)^(1/10:E)*((H:E)^(r-2)*(H:E)^(6/5:E)) * (N:E)^(3/5:E) := mul_le_mul_of_nonneg_right
       (mul_le_mul_of_nonneg_right (hLog4_10ε.trans hH_10ε_le_110) (by positivity)) (by positivity)
     _ <= (H:E)^(2-10*ε)*(N:E)^(3/5:E) :=mul_le_mul_of_nonneg_right hHprod (by positivity)
     _ <= (N:E)^(2/5:E)*(N:E)^(3/5:E) :=mul_le_mul_of_nonneg_right hN25 (by positivity)
     _ = (N:E):=by rw [← rpow_add hN_pos];norm_num
   have hT6:W*(800*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E))<=(N:E):=by
    have hN13:(H:E)^(5/3-25*ε/3)<=(N:E)^(1/3:E):=by
     have hrp:=rpow_le_rpow (by positivity) hN_lb (by norm_num:(0:E)<=1/3);rw [← rpow_mul hHR_pos.le] at hrp;convert hrp using 2;ring
    have hHprod:(H:E)^(10*ε)*((H:E)^(r-2)*(H:E)) ≤ (H:E)^(5/3-25*ε/3):=by
     conv_lhs=>arg 2;arg 2;rw [← rpow_one (H:E)]
     rw [← rpow_add hHR_pos,← rpow_add hHR_pos];exact rpow_le_rpow_of_exponent_le hHR_ge1 (by dsimp [ε];linarith)
    calc
     W*(800*(D':E)^(1/3:E)*(H:E)*(N:E)^(2/3:E))
       ≤ W*(800*(200*LogH)*(H:E)*(N:E)^(2/3:E)):=by
      apply mul_le_mul_of_nonneg_left _ hW_pos.le;have h1:800*(D':E)^(1/3:E)<=800*(200*LogH) :=mul_le_mul_of_nonneg_left hD'_13 (by norm_num);exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hHR_pos.le) (by positivity)
     _ = (224*10^12*LogH^5)*((H:E)^(r-2)*(H:E))*(N:E)^(2/3:E):=by dsimp [W];ring
     _ <= (10^17*LogH^5)*((H:E)^(r-2)*(H:E))*(N:E)^(2/3:E):=by
      have hc:(224*10^12:E)*LogH^5<=10^17*LogH^5 :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity);exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
     _ <= (H:E)^(10*ε)*((H:E)^(r-2)*(H:E))*(N:E)^(2/3:E) :=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLog5_10ε (by positivity)) (by positivity)
     _ <= (H:E)^(5/3-25*ε/3)*(N:E)^(2/3:E) :=mul_le_mul_of_nonneg_right hHprod (by positivity)
     _ <= (N:E)^(1/3:E)*(N:E)^(2/3:E) :=mul_le_mul_of_nonneg_right hN13 (by positivity)
     _ = (N:E):=by rw [← rpow_add hN_pos];norm_num
   have hT7:W*(2000*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E))<=(N:E):=by
    have hN12:(H:E)^(5/2-25*ε/2)<=(N:E)^(1/2:E):=by
     have hrp:=rpow_le_rpow (by positivity) hN_lb (by norm_num:(0:E)<=1/2);rw [← rpow_mul hHR_pos.le] at hrp;convert hrp using 2;ring
    have hHprod:(H:E)^(1/3:E)*((H:E)^(r-2)*(H:E)^(3/2:E)) ≤ (H:E)^(5/2-25*ε/2):=by
     rw [← rpow_add hHR_pos,← rpow_add hHR_pos];exact rpow_le_rpow_of_exponent_le hHR_ge1 (by dsimp [ε];linarith)
    calc
     W*(2000*(D':E)^(1/3:E)*(H:E)^(3/2:E)*(N:E)^(1/2:E))
       ≤ W*(2000*(200*LogH)*(H:E)^(3/2:E)*(N:E)^(1/2:E)):=by
      apply mul_le_mul_of_nonneg_left _ hW_pos.le;have h1:2000*(D':E)^(1/3:E)<=2000*(200*LogH) :=mul_le_mul_of_nonneg_left hD'_13 (by norm_num);exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
     _ = (56*10^13*LogH^5)*((H:E)^(r-2)*(H:E)^(3/2:E)) * (N:E)^(1/2:E):=by dsimp [W];ring
     _ <= (10^17*LogH^5)*((H:E)^(r-2)*(H:E)^(3/2:E)) * (N:E)^(1/2:E):=by
      have hc:(56*10^13:E)*LogH^5<=10^17*LogH^5 :=mul_le_mul_of_nonneg_right (by norm_num) (by positivity);exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
     _ <= (H:E)^(1/3:E)*((H:E)^(r-2)*(H:E)^(3/2:E)) * (N:E)^(1/2:E) := mul_le_mul_of_nonneg_right
       (mul_le_mul_of_nonneg_right (hLog5_10ε.trans hH_10ε_le_13) (by positivity)) (by positivity)
     _ <= (H:E)^(5/2-25*ε/2)*(N:E)^(1/2:E) :=mul_le_mul_of_nonneg_right hHprod (by positivity)
     _ <= (N:E)^(1/2:E)*(N:E)^(1/2:E) :=mul_le_mul_of_nonneg_right hN12 (by positivity)
     _ = (N:E):=by rw [← rpow_add hN_pos];norm_num
   have hW_sex:W*(sextupleCount N H P D D':E)<=7*(N:E):=by
    have h1:=mul_le_mul_of_nonneg_left hsex hW_pos.le;rw [mul_add,mul_add,mul_add,mul_add,mul_add,mul_add] at h1;linarith
   have hprod_le:((badDyadicPrime N H P L₀).card:E)*((K_P:E)*(H:E)^r)<=(N:E):=by
    calc
     ((badDyadicPrime N H P L₀).card:E)*((K_P:E)*(H:E)^r)
       ≤ (4*(H:E)/(L₀:E)^3*(sextupleCount N H P D D':E)) * ((K_P:E)*(H:E)^r) :=
      mul_le_mul_of_nonneg_right hdc (by positivity)
     _ = (4*(H:E)/(L₀:E)^3*((K_P:E)*(H:E)^r)) * (sextupleCount N H P D D':E):=by ring
     _ <= (2*10^8*LogH^4*(H:E)^(r-2))*(sextupleCount N H P D D':E) :=mul_le_mul_of_nonneg_right hpref (Nat.cast_nonneg _)
     _ = (W*(sextupleCount N H P D D':E))/7:=by dsimp [W];ring
     _ <= (7*(N:E))/7:=div_le_div_of_nonneg_right hW_sex (by norm_num)
     _ = (N:E):=by ring
   exact (le_div_iff₀ (by positivity)).mpr hprod_le
 have htot:((badDyadic N H).card:E) ≤ ((badLargePrimes N H P₁).card:E) + ∑ t∈Finset.range K_P,((badDyadicPrime N H (P_of t) L₀).card:E):=by
  have h1:(badDyadic N H).card<=(badLargePrimes N H P₁).card + ((Finset.range K_P).biUnion (fun t=>badDyadicPrime N H (P_of t) L₀)).card :=(Finset.card_le_card hcov).trans (Finset.card_union_le _ _)
  have h2:((Finset.range K_P).biUnion (fun t=>badDyadicPrime N H (P_of t) L₀)).card ≤ ∑ t∈Finset.range K_P,(badDyadicPrime N H (P_of t) L₀).card:=Finset.card_biUnion_le;exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
 have hdyad_sum:∑ t∈Finset.range K_P,((badDyadicPrime N H (P_of t) L₀).card:E) ≤ (N:E)/(H:E)^r:=by
  calc
   _ <= ∑ _t∈Finset.range K_P,((N:E)/((K_P:E)*(H:E)^r)):=sum_le_sum hP_bound
   _ = (K_P:E)*((N:E)/((K_P:E)*(H:E)^r)):=by simp
   _ = (N:E)/(H:E)^r:=by field_simp [hK_P_pos.ne']
 have h5:4*(N:E)/(H:E)^r+(N:E)/(H:E)^r=5*(N:E)/(H:E)^r:=by ring
 linarith
theorem erdos_145_H2 :
  SquarefreeIntervalMoment.IntervalCount:=by
 intro r hr_pos hr_lt;let r':E:=max r (13/5);have hr'_lo:5/2<=r':=le_trans (by norm_num) (le_max_right r (13/5));have hr'_hi:r' < 8/3:=max_lt hr_lt (by norm_num);have hr_le_r':r<=r':=le_max_left _ _;let ε:E:=(8/3-r')/100
 have hε_pos:0 < ε:=by dsimp [ε];linarith
 have hε_le:ε<=1/1000:=by
  have:(13/5:E)<=r':=le_max_right _ _
  dsimp [ε];linarith
 obtain ⟨N_gap,hN_gap_ge,hGap⟩:=exists_squarefree_in_interval_of_large hε_pos hε_le;obtain ⟨H₀,hH₀_ge,hDyad⟩:=card_badDyadic_le hr'_lo hr'_hi;let K₀:ℕ:=Nat.log 2 (2*H₀)+4;let C:E:=max (10*((2:E)^r')^K₀) (100*(2:E)^r')
 have hC_pos:0 < C:=lt_of_lt_of_le (by positivity) (le_max_right _ _);refine ⟨C,hC_pos,?_⟩;rw [Filter.eventually_atTop];let X₀:E:=max (N_gap:E) ((N_gap:E)^3+100);refine ⟨X₀,?_⟩;intro x hx k;have hx_ge_gap:(N_gap:E)<=x:=le_trans (le_max_left _ _) hx
 have hx_ge_cube:(N_gap:E)^3+100<=x:=le_trans (le_max_right _ _) hx;have hx_ge100:(100:E)<=x:=by linarith [show (0:E)<=(N_gap:E)^3 by positivity]
 let X:ℕ:=2*⌊x⌋₊+5
 have hX_ge_gap:N_gap<=X:=by
  have hfl:x-1 < (⌊x⌋₊:E):=Nat.sub_one_lt_floor x;have h1:(N_gap:E)<=(X:E):=by dsimp [X];push_cast;linarith
  exact_mod_cast h1
 have hX_le_3x:(X:E)<=3*x:=by
  have hfl:(⌊x⌋₊:E)<=x:=Nat.floor_le (by linarith);dsimp [X];push_cast;linarith
 have h2r_le:((2:E)^r)^k<=((2:E)^r')^k:=by
  apply pow_le_pow_left₀ (by positivity);exact rpow_le_rpow_of_exponent_le (by norm_num) hr_le_r'
 let badX:=(Finset.range X).filter (fun v=>∀ j∈Finset.Ioo 0 (2^k/2),¬ Squarefree (v+j));have hbad_mem:∀ v,v∈badX<->v < X/\∀ j∈Finset.Ioo 0 (2^k/2),¬ Squarefree (v+j) := fun v=>by simp only [badX,mem_filter,Finset.mem_range]
 dsimp only
 suffices hmain:((2:E)^r')^k*(badX.card:E)<=C*x by
  have hstep:=(mul_le_mul_of_nonneg_right h2r_le (Nat.cast_nonneg badX.card)).trans hmain
  refine (le_of_eq ?_).trans hstep;congr 3;ext v;simp only [badX,X,mem_filter]
 by_cases hk:k < K₀
 ·
  have hcard:(badX.card:E)<=3*x:=by
   have h1:badX.card<=X := (Finset.card_le_card (fun v hv=>Finset.mem_range.mpr ((hbad_mem v).mp hv).1)).trans
     (card_range X).le
   exact (by exact_mod_cast h1:(badX.card:E)<=(X:E)).trans hX_le_3x
  have h2pow:((2:E)^r')^k<=((2:E)^r')^K₀:=by
   have hbase:(1:E)<=(2:E)^r':=one_le_rpow (by norm_num) (by linarith);exact pow_le_pow_right₀ hbase hk.le
  calc
   ((2:E)^r')^k*(badX.card:E)
     ≤ ((2:E)^r')^K₀*(3*x):=mul_le_mul h2pow hcard (Nat.cast_nonneg _) (by positivity)
   _ = (3*((2:E)^r')^K₀)*x:=by ring
   _ <= C*x:=by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have:=le_max_left (10*((2:E)^r')^K₀) (100*(2:E)^r')
    linarith [show (0:E)<=((2:E)^r')^K₀ by positivity]
 ·
  push Not at hk
  let H:ℕ:=2^k/2;have hk_ge4:4<=k:=by dsimp [K₀] at hk;omega
  have hH_eq:H=2^(k-1):=by
   dsimp [H];have hk1:k=(k-1)+1:=by omega
   conv_lhs=>rw [hk1,pow_succ,Nat.mul_div_cancel _ (by norm_num)]
  have h4H:4∣H:=by
   rw [hH_eq];have hk3:k-1=(k-3)+2:=by omega
   rw [hk3,pow_add];exact ⟨2^(k-3),by ring⟩
  have hH_ge_H₀:H₀<=H:=by
   rw [hH_eq];have hlt:2*H₀ < 2^(Nat.log 2 (2*H₀)+1):=Nat.lt_pow_succ_log_self (by norm_num) _;have hpow:2^(Nat.log 2 (2*H₀)+1)<=2^(k-1) :=Nat.pow_le_pow_right (by norm_num) (by dsimp [K₀] at hk;omega);omega
  have h2r'k:((2:E)^r')^k=(2:E)^r'*(H:E)^r':=by
   have hH_pos:(0:E) < (H:E):=by exact_mod_cast (show 0 < H by omega)
   have h2k:(2:E)^k=2*(H:E):=by
    rw [hH_eq];push_cast;have hk1:k=(k-1)+1:=by omega
    conv_lhs=>rw [hk1,pow_succ]
    ring
   calc
    ((2:E)^r')^k=((2:E)^k)^r':=by
     rw [← rpow_natCast ((2:E)^r') k,← rpow_mul (by norm_num),mul_comm,rpow_mul (by norm_num),rpow_natCast]
    _ = (2*(H:E))^r':=by rw [h2k]
    _ = (2:E)^r'*(H:E)^r':=mul_rpow (by norm_num) hH_pos.le
  by_cases hH_big:(X:E)^(1/5+ε)<=(H:E)
  ·
   have hemp:badX=∅:=by
    rw [Finset.eq_empty_iff_forall_notMem];intro v hv;rcases (hbad_mem v).mp hv with ⟨hv_lt,hno⟩;obtain ⟨j,hj,hsq⟩:=hGap X hX_ge_gap v H hv_lt hH_big;exact hno j hj hsq
   rw [hemp,Finset.card_empty,Nat.cast_zero,mul_zero];exact mul_nonneg hC_pos.le (by linarith)
  ·
   push Not at hH_big
   let M_lo:ℕ:=Nat.log 2 N_gap;let M_hi:ℕ:=Nat.log 2 X
   have hcov_X:badX⊆Finset.range N_gap ∪
     (Finset.Icc M_lo M_hi).biUnion (fun m=>badDyadic (2^(m+1)) H):=by
    intro v hv;rcases (hbad_mem v).mp hv with ⟨hv_lt,hno⟩
    by_cases hsm:v < N_gap
    · exact Finset.mem_union_left _ (Finset.mem_range.mpr hsm)
    ·
     apply Finset.mem_union_right
     push Not at hsm
     let m:=Nat.log 2 v;have hm_lo:M_lo<=m:=Nat.log_mono_right hsm;have hm_hi:m<=M_hi:=Nat.log_mono_right hv_lt.le;have hv_ge:2^m<=v:=Nat.pow_log_le_self 2 (by omega);have hv_lt2:v < 2^(m+1):=Nat.lt_pow_succ_log_self (by norm_num) v
     have hhalf:2^(m+1)/2=2^m:=by rw [pow_succ,Nat.mul_div_cancel _ (by norm_num)]
     exact Finset.mem_biUnion.mpr ⟨m,Finset.mem_Icc.mpr ⟨hm_lo,hm_hi⟩,mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hhalf ▸ hv_ge,hv_lt2⟩,hno⟩⟩
   have hcard_split:(badX.card:E) ≤ (N_gap:E)+∑ m∈Finset.Icc M_lo M_hi,((badDyadic (2^(m+1)) H).card:E):=by
    have h1:badX.card<=(Finset.range N_gap).card + ((Finset.Icc M_lo M_hi).biUnion (fun m=>badDyadic (2^(m+1)) H)).card :=(Finset.card_le_card hcov_X).trans (Finset.card_union_le _ _)
    have h2:((Finset.Icc M_lo M_hi).biUnion (fun m=>badDyadic (2^(m+1)) H)).card ≤ ∑ m∈Finset.Icc M_lo M_hi,(badDyadic (2^(m+1)) H).card:=Finset.card_biUnion_le;rw [card_range] at h1;exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
   have hblock:∀ m∈Finset.Icc M_lo M_hi,((badDyadic (2^(m+1)) H).card:E)<=5*((2^(m+1):ℕ):E)/(H:E)^r':=by
    intro m hm;have hm_lo:M_lo<=m:=(Finset.mem_Icc.mp hm).1
    have hNm_ge:N_gap<=2^(m+1):=by
     have h1:N_gap < 2^(M_lo+1):=Nat.lt_pow_succ_log_self (by norm_num) N_gap;have h2:2^(M_lo+1)<=2^(m+1):=Nat.pow_le_pow_right (by norm_num) (by omega);omega
    by_cases hH_ge_Nm:((2^(m+1):ℕ):E)^(1/5+ε)<=(H:E)
    ·
     have hemp:badDyadic (2^(m+1)) H=∅:=by
      rw [Finset.eq_empty_iff_forall_notMem];intro v hv;rcases mem_filter.mp hv with ⟨hv_ico,hno⟩;obtain ⟨j,hj,hsq⟩:=hGap (2^(m+1)) hNm_ge v H (Finset.mem_Ico.mp hv_ico).2 hH_ge_Nm;exact hno j hj hsq
     rw [hemp,Finset.card_empty,Nat.cast_zero];positivity
    ·
     push Not at hH_ge_Nm
     exact hDyad (2^(m+1)) H hH_ge_H₀ h4H hH_ge_Nm
   have hgeom:∑ m∈Finset.Icc M_lo M_hi,((2^(m+1):ℕ):E)<=4*(X:E):=by
    have hsub:Finset.Icc M_lo M_hi⊆Finset.range (M_hi+1):=by
     intro m hm;exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hm).2)
    have hsum_range:∑ m∈Finset.range (M_hi+1),(2:E)^(m+1) = 2*((2:E)^(M_hi+1)-1):=by
     induction M_hi with
     | zero=>norm_num
     | succ n ih =>
      rw [sum_range_succ,ih,pow_succ];ring
    have hpow_le:(2:E)^M_hi<=(X:E):=by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    calc
     ∑ m∈Finset.Icc M_lo M_hi,((2^(m+1):ℕ):E)
       ≤ ∑ m∈Finset.range (M_hi+1),((2^(m+1):ℕ):E) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>Nat.cast_nonneg _)
     _ = ∑ m∈Finset.range (M_hi+1),(2:E)^(m+1):=by apply sum_congr rfl;intro m _;push_cast;rfl
     _ = 2*((2:E)^(M_hi+1)-1):=hsum_range
     _ <= 4*(2:E)^M_hi:=by rw [pow_succ];linarith
     _ <= 4*(X:E):=by linarith
   have hsmall_term:(H:E)^r'*(N_gap:E)<=(X:E):=by
    have hX_pos:(0:E) < (X:E):=by exact_mod_cast (show 0 < X by omega)
    have hX_ge1:(1:E)<=(X:E):=by exact_mod_cast (show 1<=X by omega)
    have hHr':(H:E)^r'<=(X:E)^(2/3:E):=by
     calc
      (H:E)^r'<=((X:E)^(1/5+ε))^r' :=rpow_le_rpow (Nat.cast_nonneg H) hH_big.le (by linarith)
      _ = (X:E)^((1/5+ε)*r'):=(rpow_mul hX_pos.le _ _).symm
      _ <= (X:E)^(2/3:E) :=rpow_le_rpow_of_exponent_le hX_ge1 (by nlinarith)
    have hNgap_le:(N_gap:E)<=(X:E)^(1/3:E):=by
     have h1:(N_gap:E)^3<=(X:E):=by
      have hfl:x-1 < (⌊x⌋₊:E):=Nat.sub_one_lt_floor x;dsimp [X];push_cast;linarith
     have hrp:=rpow_le_rpow (by positivity) h1 (by norm_num:(0:E)<=1/3);rw [← rpow_natCast (N_gap:E) 3,← rpow_mul (Nat.cast_nonneg _)] at hrp;norm_num at hrp;exact hrp
    calc
     (H:E)^r'*(N_gap:E)<=(X:E)^(2/3:E)*(X:E)^(1/3:E) :=mul_le_mul hHr' hNgap_le (Nat.cast_nonneg _) (by positivity)
     _ = (X:E):=by rw [← rpow_add hX_pos];norm_num
   have hH_pos:(0:E) < (H:E):=by exact_mod_cast (show 0 < H by omega)
   have hHr'_pos:0 < (H:E)^r':=rpow_pos_of_pos hH_pos r'
   have hdyad_tot:(H:E)^r'*∑ m∈Finset.Icc M_lo M_hi,((badDyadic (2^(m+1)) H).card:E) ≤ 20*(X:E):=by
    calc
     (H:E)^r'*∑ m∈Finset.Icc M_lo M_hi,((badDyadic (2^(m+1)) H).card:E)
       ≤ (H:E)^r'*∑ m∈Finset.Icc M_lo M_hi,(5*((2^(m+1):ℕ):E)/(H:E)^r') :=
      mul_le_mul_of_nonneg_left (sum_le_sum hblock) hHr'_pos.le
     _ = 5*∑ m∈Finset.Icc M_lo M_hi,((2^(m+1):ℕ):E):=by
      rw [Finset.mul_sum,Finset.mul_sum];apply sum_congr rfl;intro m _;field_simp [hHr'_pos.ne']
     _ <= 5*(4*(X:E)):=mul_le_mul_of_nonneg_left hgeom (by norm_num)
     _ = 20*(X:E):=by ring
   calc
    ((2:E)^r')^k*(badX.card:E)
      = (2:E)^r'*((H:E)^r'*(badX.card:E)):=by rw [h2r'k];ring
    _ <= (2:E)^r'*((H:E)^r' * ((N_gap:E)+∑ m∈Finset.Icc M_lo M_hi,((badDyadic (2^(m+1)) H).card:E))) :=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcard_split hHr'_pos.le) (by positivity)
    _ = (2:E)^r'*((H:E)^r'*(N_gap:E) + (H:E)^r'*∑ m∈Finset.Icc M_lo M_hi,((badDyadic (2^(m+1)) H).card:E)):=by ring
    _ <= (2:E)^r'*((X:E)+20*(X:E)) :=mul_le_mul_of_nonneg_left (add_le_add hsmall_term hdyad_tot) (by positivity)
    _ = 21*(2:E)^r'*(X:E):=by ring
    _ <= 21*(2:E)^r'*(3*x) :=mul_le_mul_of_nonneg_left hX_le_3x (by positivity)
    _ = (63*(2:E)^r')*x:=by ring
    _ <= C*x:=by
     apply mul_le_mul_of_nonneg_right _ (by linarith)
     have:=le_max_right (10*((2:E)^r')^K₀) (100*(2:E)^r')
     linarith [show (0:E) < (2:E)^r' by positivity]
end
end Erdos145H2Proof

namespace SquarefreeIntervalMoment
open Filter Finset Erdos145

/-- The order-7/2 bound for all gaps starting by y, including the final gap. -/
theorem all_gaps (intervals : IntervalCount) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in atTop,
      (∑ n ∈ A y, ((s (n+1)-s n : ℕ):ℝ)^3 * Real.sqrt ((s (n+1)-s n : ℕ):ℝ)) ≤ C*y := by
  classical
  obtain ⟨B,hB⟩ := bounded_moments packing intervals (7/2) (by norm_num) (by norm_num)
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  filter_upwards [hB, eventually_gt_atTop (0:ℝ)] with y hb hy
  let g (n : ℕ) : ℝ := ((s (n+1)-s n : ℕ):ℝ)
  have hpos (n : ℕ) : 0 < g n := by
    have h := (Nat.nth_strictMono Nat.squarefree_infinite) (Nat.lt_succ_self n)
    dsimp only [g]
    exact_mod_cast (Nat.sub_pos_of_lt h : 0 < s (n+1)-s n)
  have weight (n : ℕ) : g n ^ 3 * Real.sqrt (g n) = g n ^ (7/2 : ℝ) := by
    rw [show (7/2:ℝ) = 3 + 1/2 by norm_num, Real.rpow_add (hpos n), ← Real.sqrt_eq_rpow]
    rw [show (g n)^(3:ℝ) = (g n)^3 from Real.rpow_natCast _ 3]
  change (1/y)*(∑ n ∈ A y, (g n)^(7/2:ℝ)) ≤ B at hb
  rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hy] at hb
  change (∑ n ∈ A y, (g n)^3 * Real.sqrt (g n)) ≤ max B 1*y
  calc
    _ = ∑ n ∈ A y, (g n)^(7/2:ℝ) := sum_congr rfl (fun n _ => weight n)
    _ ≤ B*y := hb
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hy.le

/-- The order-7/2 bound for all gaps completed by y. -/
theorem completed_gaps (intervals : IntervalCount) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in atTop,
      (∑ n ∈ (A y).filter (fun n => s (n+1) ≤ ⌊y⌋₊),
        ((s (n+1)-s n : ℕ):ℝ)^3 * Real.sqrt ((s (n+1)-s n : ℕ):ℝ)) ≤ C*y := by
  classical
  obtain ⟨C,hC,bound⟩ := all_gaps intervals
  refine ⟨C,hC,?_⟩
  filter_upwards [bound] with y hy
  apply le_trans _ hy
  exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun n _ _ => by positivity)

/-- Restriction to the completed gaps with no large prime-square witness. -/
theorem residual (intervals : IntervalCount) :
    OMA.R_Erdos145_erdos_145_variants_le_three_R2.H2 := by
  classical
  obtain ⟨C,hC,bound⟩ := completed_gaps intervals
  refine ⟨C,hC,?_⟩
  filter_upwards [bound] with y hy
  apply le_trans _ hy
  exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun n _ _ => by positivity)

end SquarefreeIntervalMoment

open Finset Filter Erdos145 in
theorem SquarefreeIntervalMoment.completed_seven_halves :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ y : ℝ in atTop,
      (∑ n ∈ (A y).filter (fun n => s (n+1) ≤ ⌊y⌋₊),
        ((s (n+1)-s n : ℕ):ℝ)^3 * Real.sqrt ((s (n+1)-s n : ℕ):ℝ)) ≤ C*y :=
  SquarefreeIntervalMoment.completed_gaps Erdos145H2Proof.erdos_145_H2

theorem OMA.solution : OMA.R_Erdos145_erdos_145_variants_le_three_R2.H2 :=
  SquarefreeIntervalMoment.residual Erdos145H2Proof.erdos_145_H2
