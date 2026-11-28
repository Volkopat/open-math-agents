import OMAReductions.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1
import Mathlib
/-! Proof of H2 for Serre's multiplicity conjectures (complete equicharacteristic and unramified mixed-characteristic regular local rings). -/
open IsLocalRing Module Ideal TensorProduct CategoryTheory Limits MonoidalCategory Pointwise Function OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1
namespace OMA.H2Proof
section BasicIterPowerSeries
abbrev z0 (C:Type) : ℕ → Type
 | 0=>C
 | n+1=>PowerSeries (z0 C n)
noncomputable instance instCommRingIterPowerSeries (C:Type) [CommRing C] :
  ∀ n : ℕ,CommRing (z0 C n)
 | 0=>inferInstanceAs (CommRing C)
 | n+1 =>
  let _:=instCommRingIterPowerSeries C n
  inferInstanceAs (CommRing (PowerSeries (z0 C n)))
noncomputable instance instIsLocalRingIterPowerSeries (C:Type) [CommRing C] [IsLocalRing C] :
  ∀ n : ℕ,IsLocalRing (z0 C n)
 | 0=>inferInstanceAs (IsLocalRing C)
 | n+1 =>
  let _:=instCommRingIterPowerSeries C n;let _:=instIsLocalRingIterPowerSeries C n
  inferInstanceAs (IsLocalRing (PowerSeries (z0 C n)))
instance instIsNoetherianRingIterPowerSeries (C:Type) [CommRing C] [IsNoetherianRing C] :
  ∀ n : ℕ,IsNoetherianRing (z0 C n)
 | 0=>inferInstanceAs (IsNoetherianRing C)
 | n+1 =>
  let _:=instCommRingIterPowerSeries C n;let _:=instIsNoetherianRingIterPowerSeries C n
  inferInstanceAs (IsNoetherianRing (PowerSeries (z0 C n)))
instance instIsDomainIterPowerSeries (C:Type) [CommRing C] [IsDomain C] :
  ∀ n : ℕ,IsDomain (z0 C n)
 | 0=>inferInstanceAs (IsDomain C)
 | n+1 =>
  let _:=instCommRingIterPowerSeries C n;let _:=instIsDomainIterPowerSeries C n
  inferInstanceAs (IsDomain (PowerSeries (z0 C n)))
lemma z3 {A:Type*} [CommRing A] [IsLocalRing A]
  (f:PowerSeries A) :
  f∈maximalIdeal (PowerSeries A)↔PowerSeries.constantCoeff f∈maximalIdeal A:=by
 simp only [mem_maximalIdeal,mem_nonunits_iff,PowerSeries.isUnit_iff_constantCoeff]
lemma z4 {A:Type*} [CommRing A] [IsLocalRing A] :
  (PowerSeries.X:PowerSeries A)∈maximalIdeal (PowerSeries A):=by
 rw [z3,PowerSeries.constantCoeff_X];exact (maximalIdeal A).zero_mem
lemma z5 {A:Type*} [CommRing A] [IsLocalRing A] :
  (maximalIdeal (PowerSeries A)).map PowerSeries.constantCoeff=maximalIdeal A:=by
 refine le_antisymm ?_ ?_
 ·
  rw [map_le_iff_le_comap];intro f hf;exact (z3 f).mp hf
 ·
  intro a ha
  have hCa:PowerSeries.C a∈maximalIdeal (PowerSeries A):=by
   rw [z3,PowerSeries.constantCoeff_C];exact ha
  have:=mem_map_of_mem PowerSeries.constantCoeff hCa;simpa using this
lemma z6 {A:Type*} [CommRing A] :
  ∀ (k : ℕ) (f:PowerSeries A),(∀ i < k,PowerSeries.coeff i f=0)→f∈span {(PowerSeries.X:PowerSeries A) ^ k}:=by
 intro k
 induction k with
 | zero =>
  intro f _;simp
 | succ k ih =>
  intro f hf
  have hf0:PowerSeries.constantCoeff f=0:=by
   have:=hf 0 (Nat.succ_pos k);simpa using this
  let g:PowerSeries A:=PowerSeries.mk fun i=>PowerSeries.coeff (i+1) f
  have hfg:f=PowerSeries.X*g:=by
   ext i
   cases i with
   | zero=>simpa using hf0
   | succ i =>
    rw [PowerSeries.coeff_succ_X_mul];simp [g]
  have hg:∀ i < k,PowerSeries.coeff i g=0:=fun i hi=>by
   simp only [g,PowerSeries.coeff_mk];exact hf (i+1) (Nat.succ_lt_succ hi)
  obtain ⟨q,hq⟩:=mem_span_singleton.mp (ih g hg);rw [mem_span_singleton]
  refine ⟨q,?_⟩
  rw [hfg,hq,pow_succ'];ring
lemma z7 {A:Type*} [CommRing A] {I J:Ideal A} (h:I ≤ J) (k : ℕ) :
  I ^ k ≤ J ^ k:=by
 induction k with
 | zero=>simp
 | succ k ih =>
  rw [pow_succ,pow_succ];exact Ideal.mul_mono ih h
lemma z8 {A:Type*} [CommRing A] [IsLocalRing A] :
  ∀ (k : ℕ) (f:PowerSeries A),
   f∈maximalIdeal (PowerSeries A) ^ k↔∀ i < k,PowerSeries.coeff i f∈maximalIdeal A ^ (k - i):=by
 intro k
 induction k with
 | zero =>
  intro f;simp
 | succ k ih =>
  intro f;constructor
  ·
   intro hf;rw [pow_succ] at hf
   refine Submodule.mul_induction_on hf ?_ ?_
   ·
    intro a ha b hb i hi;rw [PowerSeries.coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases hp2:p.2=0
    ·
     have hp1:p.1=i:=by omega
     rw [hp1,hp2]
     have hb0:PowerSeries.coeff 0 b∈maximalIdeal A:=by
      have:=(z3 b).mp hb;simpa using this
     by_cases hik:i < k
     ·
      have ha1:PowerSeries.coeff i a∈maximalIdeal A ^ (k - i):=(ih a).mp ha i hik;have q12:=mul_mem_mul ha1 hb0
      have q11:k+1 - i=(k - i)+1:=by omega
      rw [q11,pow_succ];exact q12
     ·
      have q7:i=k:=by omega
      rw [q7]
      have q11:k+1 - k=1:=by omega
      rw [q11,pow_one];exact (maximalIdeal A).mul_mem_left _ hb0
    ·
     have q5:p.1 < k:=by omega
     have ha1:PowerSeries.coeff p.1 a∈maximalIdeal A ^ (k - p.1):=(ih a).mp ha p.1 q5
     have hle:k+1 - i ≤ k - p.1:=by omega
     exact (maximalIdeal A ^ (k+1 - i)).mul_mem_right _ (pow_le_pow_right hle ha1)
   ·
    intro a b ha hb i hi;rw [map_add];exact Ideal.add_mem _ (ha i hi) (hb i hi)
  ·
   intro hf;let q10:PowerSeries A := ∑ i∈Finset.range (k+1),PowerSeries.C (PowerSeries.coeff i f)*PowerSeries.X ^ i
   have q0:q10∈maximalIdeal (PowerSeries A) ^ (k+1):=by
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi;have hci:PowerSeries.coeff i f∈maximalIdeal A ^ (k+1 - i):=hf i hi
    have q4:PowerSeries.C (PowerSeries.coeff i f) ∈
      maximalIdeal (PowerSeries A) ^ (k+1 - i):=by
     have hle:(maximalIdeal A).map PowerSeries.C ≤ maximalIdeal (PowerSeries A):=by
      rw [map_le_iff_le_comap];intro a ha;rw [mem_comap,z3,PowerSeries.constantCoeff_C];exact ha
     have q3:((maximalIdeal A).map PowerSeries.C) ^ (k+1 - i) ≤ maximalIdeal (PowerSeries A) ^ (k+1 - i):=z7 hle _;rw [← Ideal.map_pow] at q3;exact q3 (mem_map_of_mem PowerSeries.C hci)
    have q6:(PowerSeries.X:PowerSeries A) ^ i∈maximalIdeal (PowerSeries A) ^ i:=Ideal.pow_mem_pow z4 i;have q12:=mul_mem_mul q4 q6;rw [← pow_add,Nat.sub_add_cancel (by omega)] at q12;exact q12
   have q1:∀ i < k+1,PowerSeries.coeff i (f - q10)=0:=fun i hi=>by
    rw [map_sub,map_sum]
    have q13 : ∑ j∈Finset.range (k+1),PowerSeries.coeff i (PowerSeries.C (PowerSeries.coeff j f)*PowerSeries.X ^ j)=PowerSeries.coeff i f:=by
     rw [Finset.sum_eq_single i]
     · rw [PowerSeries.coeff_C_mul_X_pow,if_pos rfl]
     ·
      intro j _ hji;rw [PowerSeries.coeff_C_mul_X_pow,if_neg (Ne.symm hji)]
     ·
      intro hni;exact absurd (Finset.mem_range.mpr hi) hni
    rw [q13,sub_self]
   have q2:f - q10∈maximalIdeal (PowerSeries A) ^ (k+1):=by
    have q8:=z6 (k+1) (f - q10) q1
    have hle:span {(PowerSeries.X:PowerSeries A) ^ (k+1)} ≤ maximalIdeal (PowerSeries A) ^ (k+1):=by
     rw [span_singleton_le_iff_mem];exact Ideal.pow_mem_pow z4 (k+1)
    exact hle q8
   have q9:f=q10+(f - q10):=by ring
   rw [q9];exact Ideal.add_mem _ q0 q2
lemma z9 {A:Type*} [CommRing A] [IsLocalRing A]
  [IsAdicComplete (maximalIdeal A) A] :
  IsAdicComplete (maximalIdeal (PowerSeries A)) (PowerSeries A):=by
 refine { haus' := ?_,prec' := ?_ }
 ·
  intro f hf;ext i
  refine IsHausdorff.haus' (I:=maximalIdeal A) (M:=A) (PowerSeries.coeff i f) fun r => ?_
  rw [SModEq.zero,smul_eq_mul,mul_top];have hfi:=hf (i+r+1);rw [SModEq.zero,smul_eq_mul,mul_top] at hfi;have q4:=(z8 (i+r+1) f).mp hfi i (by omega)
  have hle:r ≤ i+r+1 - i:=by omega
  exact pow_le_pow_right hle q4
 ·
  intro seq hseq
  have q0:∀ (i : ℕ) {a b : ℕ},a ≤ b →
    PowerSeries.coeff i (seq (a+i+1)) ≡ PowerSeries.coeff i (seq (b+i+1))
     [SMOD (maximalIdeal A ^ a•(⊤ : Submodule A A))]:=by
   intro i a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top,← map_sub];have h1:=hseq (show a+i+1 ≤ b+i+1 by omega);rw [SModEq.sub_mem,smul_eq_mul,mul_top] at h1;have h2:=(z8 (a+i+1) _).mp h1 i (by omega)
   have hle:a ≤ a+i+1 - i:=by omega
   exact pow_le_pow_right hle h2
  let q2 : ℕ → A:=fun i =>
   (IsPrecomplete.prec' (I:=maximalIdeal A) (M:=A)
    (fun a=>PowerSeries.coeff i (seq (a+i+1))) (q0 i)).choose
  have q1:∀ i a,PowerSeries.coeff i (seq (a+i+1)) - q2 i∈maximalIdeal A ^ a:=fun i a=>by
   have h:=(IsPrecomplete.prec' (I:=maximalIdeal A) (M:=A)
    (fun a=>PowerSeries.coeff i (seq (a+i+1))) (q0 i)).choose_spec a
   rw [SModEq.sub_mem,smul_eq_mul,mul_top] at h;exact h
  let L:PowerSeries A:=PowerSeries.mk q2
  refine ⟨L,fun k => ?_⟩
  rw [SModEq.sub_mem,smul_eq_mul,mul_top,z8];intro i hi;rw [map_sub]
  have h1:PowerSeries.coeff i (seq k) - PowerSeries.coeff i (seq (k+i+1)) ∈
    maximalIdeal A ^ (k - i):=by
   rw [← map_sub];have hk:=hseq (show k ≤ k+i+1 by omega);rw [SModEq.sub_mem,smul_eq_mul,mul_top] at hk;exact (z8 k _).mp hk i hi
  have h2:PowerSeries.coeff i (seq (k+i+1)) - PowerSeries.coeff i L ∈
    maximalIdeal A ^ (k - i):=by
   simp only [L,PowerSeries.coeff_mk];exact pow_le_pow_right (Nat.sub_le k i) (q1 i k)
  have q3:PowerSeries.coeff i (seq k) - PowerSeries.coeff i L=(PowerSeries.coeff i (seq k) - PowerSeries.coeff i (seq (k+i+1)))+(PowerSeries.coeff i (seq (k+i+1)) - PowerSeries.coeff i L):=by ring
  rw [q3];exact Ideal.add_mem _ h1 h2
lemma z10 {A:Type*} [CommRing A] [IsRegularLocalRing A] :
  IsRegularLocalRing (PowerSeries A) ∧
   ringKrullDim (PowerSeries A)=ringKrullDim A+1:=by
 have q5:ringKrullDim A=((maximalIdeal A).spanFinrank:WithBot ℕ∞):=((isRegularLocalRing_iff A).mp ‹IsRegularLocalRing A›).symm
 have q1:(maximalIdeal (PowerSeries A)).spanFinrank ≤ (maximalIdeal A).spanFinrank+1:=by
  have h1:=PowerSeries.spanFinrank_le_spanFinrank_map_constantCoeff_add_one_of_X_mem
   (I:=maximalIdeal (PowerSeries A)) z4
  rwa [z5] at h1
 have q4:((maximalIdeal A).spanFinrank+1 : ℕ) ≤ ringKrullDim (PowerSeries A):=by
  have h1:=ringKrullDim_succ_le_ringKrullDim_powerseries (R:=A);rw [q5] at h1;simpa [Nat.cast_add,Nat.cast_one] using h1
 have q0:((maximalIdeal (PowerSeries A)).spanFinrank:WithBot ℕ∞) ≤
   ringKrullDim (PowerSeries A) :=
  (Nat.cast_le.mpr q1).trans q4
 have q6:IsRegularLocalRing (PowerSeries A):=IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ q0
 refine ⟨q6,?_⟩
 have q2:ringKrullDim (PowerSeries A) ≤ ((maximalIdeal A).spanFinrank+1 : ℕ):=(ringKrullDim_le_spanFinrank_maximalIdeal (PowerSeries A)).trans (Nat.cast_le.mpr q1);have q3:ringKrullDim (PowerSeries A)=((maximalIdeal A).spanFinrank+1 : ℕ):=le_antisymm q2 q4;rw [q3,q5];push_cast;rfl
instance instIsAdicCompleteIterPowerSeries (C:Type) [CommRing C] [IsLocalRing C]
  [IsAdicComplete (maximalIdeal C) C] :
  ∀ n : ℕ,IsAdicComplete (maximalIdeal (z0 C n)) (z0 C n)
 | 0=>inferInstanceAs (IsAdicComplete (maximalIdeal C) C)
 | n+1 =>
  let _:=instIsAdicCompleteIterPowerSeries C n
  z9
instance instIsRegularLocalRingIterPowerSeries (C:Type) [CommRing C] [IsRegularLocalRing C] :
  ∀ n : ℕ,IsRegularLocalRing (z0 C n)
 | 0=>inferInstanceAs (IsRegularLocalRing C)
 | n+1 =>
  let _:=instIsRegularLocalRingIterPowerSeries C n
  (z10 (A:=z0 C n)).1
lemma z11 (C:Type) [CommRing C] [IsRegularLocalRing C] :
  ∀ n : ℕ,ringKrullDim (z0 C n)=ringKrullDim C+(n:WithBot ℕ∞)
 | 0=>by
  change ringKrullDim C=ringKrullDim C+(0:WithBot ℕ∞);simp
 | n+1=>by
  have h1:=(z10 (A:=z0 C n)).2;have h2:=z11 C n;change ringKrullDim (PowerSeries (z0 C n))=_;rw [h1,h2];push_cast;rw [add_assoc]
lemma z12 {A R:Type*} [CommRing A] [IsLocalRing A]
  [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  (f:A →+* R) (q9:∀ a∈maximalIdeal A,f a∈maximalIdeal R)
  {x:R} (hx:x∈maximalIdeal R) :
  ∃ f':PowerSeries A →+* R,(∀ a:A,f' (PowerSeries.C a)=f a)∧f' PowerSeries.X=x∧(∀ u∈maximalIdeal (PowerSeries A),f' u∈maximalIdeal R):=by
 let mk:(n : ℕ)→R →+* R⧸maximalIdeal R ^ n:=fun n=>Ideal.Quotient.mk _
 let q12:(n : ℕ)→PowerSeries A→R⧸maximalIdeal R ^ n:=fun n F =>
  ∑ i∈Finset.range n,mk n (f (PowerSeries.coeff i F)*x ^ i)
 have hxn:∀ n i,n ≤ i→mk n (x ^ i)=0:=fun n i hni=>by
  rw [Ideal.Quotient.eq_zero_iff_mem];exact pow_le_pow_right hni (Ideal.pow_mem_pow hx i)
 let g:(n : ℕ)→PowerSeries A →+* R⧸maximalIdeal R ^ n:=fun n =>
  {
   toFun:=q12 n
   map_zero':=by simp [q12]
   map_add':=fun F G=>by
    simp only [q12,map_add,add_mul,Finset.sum_add_distrib]
   map_one':=by
    cases n with
    | zero =>
     have : Subsingleton (R⧸maximalIdeal R ^ 0):=by
      rw [pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
     exact Subsingleton.elim _ _
    | succ n =>
     dsimp only [q12];rw [Finset.sum_eq_single 0]
     · simp
     ·
      intro i _ hi0;simp [PowerSeries.coeff_one,hi0]
     ·
      intro h0;exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
   map_mul':=fun F G=>by
    dsimp only [q12]
    have q15 : ∑ i∈Finset.range n,mk n (f (PowerSeries.coeff i (F*G))*x ^ i) =
      ∑ i∈Finset.range n,∑ p∈Finset.HasAntidiagonal.antidiagonal i,mk n (f (PowerSeries.coeff p.1 F)*x ^ p.1)*mk n (f (PowerSeries.coeff p.2 G)*x ^ p.2):=by
     refine Finset.sum_congr rfl fun i _ => ?_
     rw [PowerSeries.coeff_mul,map_sum,Finset.sum_mul,map_sum]
     refine Finset.sum_congr rfl fun p hp => ?_
     rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp;rw [← map_mul,← hp,pow_add];congr 1;rw [map_mul];ring
    rw [q15,Finset.sum_mul];simp_rw [Finset.mul_sum]
    have q6 : ∑ a∈Finset.range n,∑ b∈Finset.range n,mk n (f (PowerSeries.coeff a F)*x ^ a)*mk n (f (PowerSeries.coeff b G)*x ^ b) =
      ∑ p∈(Finset.range n ×ˢ Finset.range n).filter (fun p=>p.1+p.2 < n),mk n (f (PowerSeries.coeff p.1 F)*x ^ p.1)*mk n (f (PowerSeries.coeff p.2 G)*x ^ p.2):=by
     rw [← Finset.sum_product']
     symm
     refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpnot => ?_
     have hge:n ≤ p.1+p.2:=by
      by_contra hlt
      push Not at hlt
      exact hpnot (Finset.mem_filter.mpr ⟨hp,hlt⟩)
     rw [← map_mul]
     have q5:(f (PowerSeries.coeff p.1 F)*x ^ p.1)*(f (PowerSeries.coeff p.2 G)*x ^ p.2)=(f (PowerSeries.coeff p.1 F)*f (PowerSeries.coeff p.2 G))*x ^ (p.1+p.2):=by
      rw [pow_add];ring
     rw [q5,map_mul,hxn n (p.1+p.2) hge,mul_zero]
    rw [q6];rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun q _=>q.2) ?_ ?_ ?_ ?_
    ·
     intro q hq;rw [Finset.mem_sigma,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal] at hq;rw [Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_range];exact ⟨⟨by omega,by omega⟩,by omega⟩
    ·
     intro q1 hq1 q2 hq2 heq;rw [Finset.mem_sigma,Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2
     refine Sigma.ext ?_ (heq_of_eq heq)
     rw [← hq1.2,← hq2.2,heq]
    ·
     intro p hp;rw [Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_range] at hp
     refine ⟨⟨p.1+p.2,p⟩,?_,rfl⟩
     rw [Finset.mem_sigma,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal];exact ⟨hp.2,rfl⟩
    · intro _ _;rfl }
 have q0:∀ n F,Ideal.Quotient.factor (pow_le_pow_right n.le_succ) (g (n+1) F)=g n F:=by
  intro n F;change Ideal.Quotient.factor (pow_le_pow_right n.le_succ) (q12 (n+1) F)=q12 n F;dsimp only [q12];rw [Finset.sum_range_succ,map_add,map_sum]
  have q11:Ideal.Quotient.factor (pow_le_pow_right n.le_succ)
    (mk (n+1) (f (PowerSeries.coeff n F)*x ^ n))=0:=by
   change mk n (f (PowerSeries.coeff n F)*x ^ n)=0;rw [map_mul,hxn n n le_rfl,mul_zero]
  rw [q11,add_zero];rfl
 let q8:PowerSeries A → ℕ → R:=fun F n =>
  ∑ i∈Finset.range n,f (PowerSeries.coeff i F)*x ^ i
 have q4:∀ F n,mk n (q8 F n)=g n F:=fun F n=>by
  simp [q8,g,q12,mk]
 have q7:∀ F {a b : ℕ},a ≤ b→q8 F a ≡ q8 F b [SMOD (maximalIdeal R ^ a•(⊤ : Submodule R R))]:=by
  intro F a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,sub_eq_zero];change mk a (q8 F a)=mk a (q8 F b);rw [q4 F a]
  have q14:∀ {u v : ℕ} (huv:u ≤ v),Ideal.Quotient.factor (pow_le_pow_right huv) (g v F)=g u F:=by
   intro u v huv
   induction v,huv using Nat.le_induction with
   | base=>simp
   | succ v huv ih =>
    rw [← Ideal.Quotient.factor_comp_apply (pow_le_pow_right v.le_succ)
     (pow_le_pow_right huv),q0,ih]
  rw [← q14 hab,← q4 F b];rfl
 let toF:PowerSeries A→R:=fun F =>
  (IsPrecomplete.prec' (I:=maximalIdeal R) (M:=R) (q8 F) (q7 F)).choose
 have q3:∀ F n,mk n (toF F)=g n F:=fun F n=>by
  have hL:=(IsPrecomplete.prec' (I:=maximalIdeal R) (M:=R) (q8 F) (q7 F)).choose_spec n;rw [SModEq.sub_mem,smul_eq_mul,mul_top] at hL;have q13:mk n (q8 F n - toF F)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hL;rw [map_sub,sub_eq_zero,q4 F n] at q13;exact q13.symm
 let f':PowerSeries A →+* R :=
  {
   toFun:=toF
   map_one':=by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (toF 1 - 1) fun n => ?_)
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub];change mk n (toF 1) - mk n 1=0;rw [q3,map_one,map_one,sub_self]
   map_zero':=by
    refine IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (toF 0) fun n => ?_
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem];change mk n (toF 0)=0;rw [q3,map_zero]
   map_add':=fun F G=>by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R)
     (toF (F+G) - (toF F+toF G)) fun n => ?_)
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,map_add];change mk n (toF (F+G)) - (mk n (toF F)+mk n (toF G))=0;rw [q3,q3,q3,map_add,sub_self]
   map_mul':=fun F G=>by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R)
     (toF (F*G) - toF F*toF G) fun n => ?_)
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul];change mk n (toF (F*G)) - mk n (toF F)*mk n (toF G)=0
    rw [q3,q3,q3,map_mul,sub_self] }
 refine ⟨f',?_,?_,?_⟩
 ·
  intro a
  refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (f' (PowerSeries.C a) - f a) fun n => ?_)
  rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub];change mk n (toF (PowerSeries.C a)) - mk n (f a)=0;rw [q3]
  cases n with
  | zero =>
   have : Subsingleton (R⧸maximalIdeal R ^ 0):=by
    rw [pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
   exact Subsingleton.elim _ _
  | succ n =>
   change q12 (n+1) (PowerSeries.C a) - mk (n+1) (f a)=0;dsimp only [q12];rw [Finset.sum_eq_single 0]
   · simp
   ·
    intro i _ hi0;simp [PowerSeries.coeff_C,hi0]
   ·
    intro h0;exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h0
 ·
  refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (f' PowerSeries.X - x) fun n => ?_)
  rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub];change mk n (toF PowerSeries.X) - mk n x=0;rw [q3]
  cases n with
  | zero =>
   have : Subsingleton (R⧸maximalIdeal R ^ 0):=by
    rw [pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
   exact Subsingleton.elim _ _
  | succ n =>
   cases n with
   | zero =>
    change q12 1 PowerSeries.X - mk 1 x=0
    have hmx:mk 1 x=0:=by
     rw [Ideal.Quotient.eq_zero_iff_mem,pow_one];exact hx
    simp [q12,hmx]
   | succ n =>
    change q12 (n+2) PowerSeries.X - mk (n+2) x=0;dsimp only [q12];rw [Finset.sum_eq_single 1]
    · simp
    ·
     intro i _ hi1;simp [PowerSeries.coeff_X,hi1]
    ·
     intro h1;exact absurd (Finset.mem_range.mpr (by omega)) h1
 ·
  intro u hu;have q10:mk 1 (toF u)=g 1 u:=q3 u 1
  have hg1:g 1 u=0:=by
   change q12 1 u=0;simp only [q12,Finset.sum_range_one,pow_zero,mul_one,PowerSeries.coeff_zero_eq_constantCoeff];rw [Ideal.Quotient.eq_zero_iff_mem,pow_one];exact q9 _ ((z3 u).mp hu)
  have h0:mk 1 (f' u)=0:=q10.trans hg1;rw [Ideal.Quotient.eq_zero_iff_mem,pow_one] at h0;exact h0
noncomputable def z13 (C:Type) [CommRing C] :
  ∀ n : ℕ,C →+* z0 C n
 | 0=>RingHom.id C
 | n+1=>(PowerSeries.C (R:=z0 C n)).comp (z13 C n)
noncomputable def z14 (C:Type) [CommRing C] :
  ∀ {n : ℕ},Fin n→z0 C n
 | 0,i=>Fin.elim0 i
 | n+1,i =>
  Fin.lastCases (PowerSeries.X:PowerSeries (z0 C n))
   (fun j=>PowerSeries.C (z14 C j)) i
noncomputable def z15 {C D:Type} [CommRing C] [CommRing D] (f:C →+* D) :
  ∀ n : ℕ,z0 C n →+* z0 D n
 | 0=>f
 | n+1=>PowerSeries.map (z15 f n)
lemma z16 (C:Type) [CommRing C] :
  ∀ n : ℕ,Injective (z13 C n)
 | 0=>Function.injective_id
 | n+1=>(PowerSeries.C_injective (R:=z0 C n)).comp (z16 C n)
lemma z17 {C:Type} [CommRing C] [IsLocalRing C] :
  ∀ (n : ℕ) {c:C},c∈maximalIdeal C→z13 C n c∈maximalIdeal (z0 C n)
 | 0,_,hc=>hc
 | n+1,_,hc=>by
  change PowerSeries.C (z13 C n _)∈maximalIdeal (PowerSeries (z0 C n));rw [z3,PowerSeries.constantCoeff_C];exact z17 n hc
lemma z18 {C:Type} [CommRing C] [IsLocalRing C] :
  ∀ {n : ℕ} (i:Fin n),z14 C i∈maximalIdeal (z0 C n)
 | 0,i=>Fin.elim0 i
 | n+1,i=>by
  refine Fin.lastCases ?_ ?_ i
  ·
   simp only [z14,Fin.lastCases_last];exact z4
  ·
   intro j;simp only [z14,Fin.lastCases_castSucc];rw [z3,PowerSeries.constantCoeff_C];exact z18 j
lemma z19 {C D:Type} [CommRing C] [CommRing D] (f:C →+* D) :
  ∀ (n : ℕ) (c:C),z15 f n (z13 C n c)=z13 D n (f c)
 | 0,_=>rfl
 | n+1,c=>by
  change PowerSeries.map (z15 f n) (PowerSeries.C (z13 C n c))=PowerSeries.C (z13 D n (f c));rw [PowerSeries.map_C,z19 f n c]
lemma z20 {C D:Type} [CommRing C] [CommRing D] (f:C →+* D) :
  ∀ {n : ℕ} (i:Fin n),z15 f n (z14 C i)=z14 D i
 | 0,i=>Fin.elim0 i
 | n+1,i=>by
  refine Fin.lastCases ?_ ?_ i
  ·
   simp only [z14,Fin.lastCases_last,z15];exact PowerSeries.map_X (z15 f n)
  ·
   intro j;simp only [z14,Fin.lastCases_castSucc,z15];rw [PowerSeries.map_C,z20 f j]
lemma z21 {C D:Type} [CommRing C] [CommRing D] {f:C →+* D}
  (hf:Injective f) :
  ∀ n : ℕ,Injective (z15 f n)
 | 0=>hf
 | n+1=>by
  intro a b hab;ext k;have hk:=congrArg (PowerSeries.coeff k) hab;change z15 f n (PowerSeries.coeff k a)=z15 f n (PowerSeries.coeff k b) at hk;exact z21 hf n hk
lemma z22 {C D:Type} [CommRing C] [CommRing D] {f:C →+* D}
  (hf:Surjective f) :
  ∀ n : ℕ,Surjective (z15 f n)
 | 0=>hf
 | n+1=>by
  intro b;have ih:=z22 hf n
  refine ⟨PowerSeries.mk fun k=>(ih (PowerSeries.coeff k b)).choose,?_⟩
  ext k;simp only [z15,PowerSeries.coeff_map,PowerSeries.coeff_mk];exact (ih (PowerSeries.coeff k b)).choose_spec
lemma z23 {C D:Type} [CommRing C] [IsLocalRing C] [CommRing D] [IsLocalRing D]
  {f:C →+* D} (hf:∀ c∈maximalIdeal C,f c∈maximalIdeal D) :
  ∀ (n : ℕ) {x:z0 C n},x∈maximalIdeal (z0 C n)→z15 f n x∈maximalIdeal (z0 D n)
 | 0,_,hx=>hf _ hx
 | n+1,x,hx=>by
  change PowerSeries.map (z15 f n) x∈maximalIdeal (PowerSeries (z0 D n));rw [z3];have hx0:PowerSeries.constantCoeff x∈maximalIdeal (z0 C n):=(z3 x).mp hx
  have q0:PowerSeries.constantCoeff (PowerSeries.map (z15 f n) x)=z15 f n (PowerSeries.constantCoeff x):=by
   rw [← PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_map,PowerSeries.coeff_zero_eq_constantCoeff]
  rw [q0];exact z23 hf n hx0
lemma z24 {C R:Type} [CommRing C] [IsLocalRing C]
  [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  (phi:C →+* R) (q0:∀ c∈maximalIdeal C,phi c∈maximalIdeal R) :
  ∀ (n : ℕ) (xs:Fin n→R),(∀ i,xs i∈maximalIdeal R) →
   ∃ f:z0 C n →+* R,(∀ c:C,f (z13 C n c)=phi c)∧(∀ i:Fin n,f (z14 C i)=xs i)∧(∀ u∈maximalIdeal (z0 C n),f u∈maximalIdeal R):=by
 intro n
 induction n with
 | zero =>
  intro xs _
  exact ⟨phi,fun _=>rfl,fun i=>Fin.elim0 i,q0⟩
 | succ n ih =>
  intro xs hxs
  obtain ⟨f0,hf0_C,hf0_var,hf0_loc⟩:=ih (fun j:Fin n=>xs j.castSucc) (fun j=>hxs j.castSucc)
  obtain ⟨f1,hf1_C,hf1_X,hf1_loc⟩:=z12 f0 hf0_loc (hxs (Fin.last n))
  refine ⟨f1,?_,?_,hf1_loc⟩
  ·
   intro c;change f1 (PowerSeries.C (z13 C n c))=phi c;rw [hf1_C,hf0_C]
  ·
   intro i
   refine Fin.lastCases ?_ ?_ i
   ·
    simp only [z14,Fin.lastCases_last];exact hf1_X
   ·
    intro j;simp only [z14,Fin.lastCases_castSucc];rw [hf1_C,hf0_var]
lemma z25 {S:Type*} [CommRing S] [IsNoetherianRing S] (I:Ideal S) :
  RingHom.ker (PowerSeries.map (Ideal.Quotient.mk I))=I.map (PowerSeries.C (R:=S)):=by
 refine le_antisymm ?_ ?_
 ·
  intro f hf;rw [RingHom.mem_ker] at hf
  have q0:∀ k : ℕ,PowerSeries.coeff k f∈I:=fun k=>by
   have hk:=congrArg (PowerSeries.coeff k) hf;rw [PowerSeries.coeff_map,map_zero,Ideal.Quotient.eq_zero_iff_mem] at hk;exact hk
  obtain ⟨T,hT⟩:=IsNoetherian.noetherian I
  have q2:∀ k : ℕ,∃ c:T→S,∑ t:T,c t*(t:S)=PowerSeries.coeff k f:=fun k=>by
   have h1:PowerSeries.coeff k f∈Submodule.span S (T:Set S):=hT▸q0 k;rw [Submodule.mem_span_finset] at h1;obtain ⟨g,_,hg⟩:=h1
   refine ⟨fun t=>g t.1,?_⟩
   simpa [smul_eq_mul] using (Finset.sum_coe_sort T (fun x=>g x*x)).trans hg
  let ps:T→PowerSeries S:=fun t=>PowerSeries.mk fun k=>(q2 k).choose t
  have q1:f = ∑ t:T,ps t*PowerSeries.C (t:S):=by
   ext k;rw [map_sum]
   have q3 : ∑ t:T,PowerSeries.coeff k (ps t*PowerSeries.C (t:S)) = ∑ t:T,(q2 k).choose t*(t:S):=by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [PowerSeries.coeff_mul_C];simp [ps]
   rw [q3,(q2 k).choose_spec]
  rw [q1]
  refine Ideal.sum_mem _ fun t _ => ?_
  refine Ideal.mul_mem_left _ _ ?_
  exact mem_map_of_mem PowerSeries.C (hT▸subset_span t.2)
 ·
  rw [map_le_iff_le_comap];intro a ha;rw [mem_comap,RingHom.mem_ker,PowerSeries.map_C];have ha0:Ideal.Quotient.mk I a=0:=Ideal.Quotient.eq_zero_iff_mem.mpr ha;rw [ha0,map_zero]
lemma z26 {S:Type} [CommRing S] [IsNoetherianRing S] (I:Ideal S) :
  ∀ n : ℕ,RingHom.ker (z15 (Ideal.Quotient.mk I) n)=I.map (z13 S n)
 | 0=>by
  change RingHom.ker (Ideal.Quotient.mk I)=I.map (RingHom.id S);rw [mk_ker,Ideal.map_id]
 | n+1=>by
  let _:=instIsNoetherianRingIterPowerSeries S n;let g:=z15 (Ideal.Quotient.mk I) n;have q0:Surjective g:=z22 Ideal.Quotient.mk_surjective n;have q3:RingHom.ker g=I.map (z13 S n):=z26 I n;let J:Ideal (z0 S n):=I.map (z13 S n);let eQ:(z0 S n⧸J) ≃+* z0 (S⧸I) n:=(Ideal.quotEquivOfEq q3.symm).trans (RingHom.quotientKerEquivOfSurjective q0)
  have q4:g=eQ.toRingHom.comp (Ideal.Quotient.mk J):=by
   ext x;rfl
  change RingHom.ker (PowerSeries.map g)=I.map ((PowerSeries.C).comp (z13 S n));rw [← Ideal.map_map,q4]
  have q1:PowerSeries.map (eQ.toRingHom.comp (Ideal.Quotient.mk J))=(PowerSeries.map eQ.toRingHom).comp (PowerSeries.map (Ideal.Quotient.mk J)):=by
   ext f k;simp [PowerSeries.coeff_map]
  rw [q1];ext f;rw [RingHom.mem_ker,RingHom.comp_apply]
  have q2:Injective (PowerSeries.map eQ.toRingHom):=by
   intro a b hab;ext k;have hk:=congrArg (PowerSeries.coeff k) hab;rw [PowerSeries.coeff_map,PowerSeries.coeff_map] at hk;exact eQ.injective hk
  rw [map_eq_zero_iff _ q2,← RingHom.mem_ker,z25 J]
noncomputable def z27 {S:Type} [CommRing S] [IsNoetherianRing S] (I:Ideal S) (n : ℕ) :
  (z0 S n⧸I.map (z13 S n)) ≃+* z0 (S⧸I) n :=
 (Ideal.quotEquivOfEq (z26 I n).symm).trans
  (RingHom.quotientKerEquivOfSurjective (z22 Ideal.Quotient.mk_surjective n))
noncomputable def z28 {A B:Type*} [CommRing A] [CommRing B]
  (f:A →+* B) (c:B) (k : ℕ) (hc:c ^ k=0) :
  PowerSeries A →+* B where
 toFun F := ∑ i∈Finset.range k,f (PowerSeries.coeff i F)*c ^ i
 map_zero':=by simp
 map_add' F G:=by simp [map_add,add_mul,Finset.sum_add_distrib]
 map_one':=by
  cases k with
  | zero =>
   rw [pow_zero] at hc;have : Subsingleton B:=subsingleton_of_zero_eq_one hc.symm;exact Subsingleton.elim _ _
  | succ k =>
   rw [Finset.sum_eq_single 0]
   · simp
   · intro i _ hi0;simp [PowerSeries.coeff_one,hi0]
   · intro h0;exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
 map_mul' F G:=by
  have hcn:∀ m,k ≤ m→c ^ m=0:=fun m hm=>by
   rw [← Nat.add_sub_of_le hm,pow_add,hc,zero_mul]
  have q4 : ∑ i∈Finset.range k,f (PowerSeries.coeff i (F*G))*c ^ i =
    ∑ i∈Finset.range k,∑ p∈Finset.HasAntidiagonal.antidiagonal i,(f (PowerSeries.coeff p.1 F)*c ^ p.1)*(f (PowerSeries.coeff p.2 G)*c ^ p.2):=by
   refine Finset.sum_congr rfl fun i _ => ?_
   rw [PowerSeries.coeff_mul,map_sum,Finset.sum_mul]
   refine Finset.sum_congr rfl fun p hp => ?_
   rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp;rw [← hp,pow_add,map_mul];ring
  rw [q4,Finset.sum_mul];simp_rw [Finset.mul_sum]
  have q0 : ∑ a∈Finset.range k,∑ b∈Finset.range k,(f (PowerSeries.coeff a F)*c ^ a)*(f (PowerSeries.coeff b G)*c ^ b) =
    ∑ p∈(Finset.range k ×ˢ Finset.range k).filter (fun p=>p.1+p.2 < k),(f (PowerSeries.coeff p.1 F)*c ^ p.1)*(f (PowerSeries.coeff p.2 G)*c ^ p.2):=by
   rw [← Finset.sum_product']
   symm
   refine Finset.sum_subset (Finset.filter_subset _ _) fun p hp hpnot => ?_
   have hge:k ≤ p.1+p.2:=by
    by_contra hlt;push Not at hlt
    exact hpnot (Finset.mem_filter.mpr ⟨hp,hlt⟩)
   have q3:(f (PowerSeries.coeff p.1 F)*c ^ p.1)*(f (PowerSeries.coeff p.2 G)*c ^ p.2)=(f (PowerSeries.coeff p.1 F)*f (PowerSeries.coeff p.2 G))*c ^ (p.1+p.2):=by
    rw [pow_add];ring
   rw [q3,hcn _ hge,mul_zero]
  rw [q0,Finset.sum_sigma']
  refine Finset.sum_bij (fun q _=>q.2) ?_ ?_ ?_ ?_
  ·
   intro q hq;rw [Finset.mem_sigma,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal] at hq;rw [Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_range];exact ⟨⟨by omega,by omega⟩,by omega⟩
  ·
   intro q1 hq1 q2 hq2 heq;rw [Finset.mem_sigma,Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2
   refine Sigma.ext ?_ (heq_of_eq heq)
   rw [← hq1.2,← hq2.2,heq]
  ·
   intro p hp;rw [Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_range] at hp
   refine ⟨⟨p.1+p.2,p⟩,?_,rfl⟩
   rw [Finset.mem_sigma,Finset.mem_range,Finset.HasAntidiagonal.mem_antidiagonal];exact ⟨hp.2,rfl⟩
  · intro _ _;rfl
lemma z29 {A B:Type*} [CommRing A] [CommRing B]
  (f:A →+* B) (c:B) (k : ℕ) (hc:c ^ k=0) (a:A) :
  z28 f c k hc (PowerSeries.C a)=f a:=by
 cases k with
 | zero =>
  rw [pow_zero] at hc;have : Subsingleton B:=subsingleton_of_zero_eq_one hc.symm;exact Subsingleton.elim _ _
 | succ k =>
  change ∑ i∈Finset.range (k+1),f (PowerSeries.coeff i (PowerSeries.C a))*c ^ i=f a;rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi0;simp [PowerSeries.coeff_C,hi0]
  · intro h0;exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
lemma z30 {A B:Type*} [CommRing A] [CommRing B]
  (f:A →+* B) (c:B) (k : ℕ) (hc:c ^ k=0) :
  z28 f c k hc PowerSeries.X=c:=by
 cases k with
 | zero =>
  rw [pow_zero] at hc;have : Subsingleton B:=subsingleton_of_zero_eq_one hc.symm;exact Subsingleton.elim _ _
 | succ k =>
  cases k with
  | zero =>
   rw [pow_one] at hc;change ∑ i∈Finset.range 1,f (PowerSeries.coeff i PowerSeries.X)*c ^ i=c;simp [hc]
  | succ k =>
   change ∑ i∈Finset.range (k+2),f (PowerSeries.coeff i PowerSeries.X)*c ^ i=c;rw [Finset.sum_eq_single 1]
   · simp
   · intro i _ hi1;simp [PowerSeries.coeff_X,hi1]
   · intro h1;exact absurd (Finset.mem_range.mpr (by omega)) h1
lemma z31 {A B:Type*} [CommRing A] [CommRing B]
    (g₁ g₂ : PowerSeries A →+* B)
    (hC:∀ a:A,g₁ (PowerSeries.C a)=g₂ (PowerSeries.C a))
    (hX:g₁ PowerSeries.X=g₂ PowerSeries.X)
    {k : ℕ} (q1:g₁ PowerSeries.X ^ k=0) :
    g₁ = g₂ := by
  ext F;let q2:PowerSeries A := ∑ i∈Finset.range k,PowerSeries.C (PowerSeries.coeff i F)*PowerSeries.X ^ i
  have q0:∀ i < k,PowerSeries.coeff i (F - q2)=0:=fun i hi=>by
    rw [map_sub,map_sum]
    have q3 : ∑ j∈Finset.range k,PowerSeries.coeff i (PowerSeries.C (PowerSeries.coeff j F)*PowerSeries.X ^ j)=PowerSeries.coeff i F:=by
      rw [Finset.sum_eq_single i]
      · rw [PowerSeries.coeff_C_mul_X_pow,if_pos rfl]
      · intro j _ hji;rw [PowerSeries.coeff_C_mul_X_pow,if_neg (Ne.symm hji)]
      · intro hni;exact absurd (Finset.mem_range.mpr hi) hni
    rw [q3,sub_self]
  obtain ⟨q,hq⟩:=mem_span_singleton.mp
    (z6 k (F - q2) q0)
  have hF:F=q2+PowerSeries.X ^ k*q:=by
    calc F=q2+(F - q2):=by ring
      _=q2+PowerSeries.X ^ k*q:=by rw [hq]
  rw [hF,map_add,map_add,map_mul,map_mul,map_pow,map_pow,q1,← hX,q1,zero_mul,zero_mul,add_zero,add_zero];simp only [q2,map_sum,map_mul,map_pow,hC,hX]
lemma z32 {C B:Type} [CommRing C] [CommRing B] :
  ∀ {n : ℕ} (g₁ g₂ : z0 C n →+* B),(∀ c:C,g₁ (z13 C n c)=g₂ (z13 C n c))→(∀ i:Fin n,g₁ (z14 C i)=g₂ (z14 C i))→(∀ i:Fin n,∃ k : ℕ,g₁ (z14 C i) ^ k=0) → g₁ = g₂
 | 0,g₁,g₂,hC,_,_=>RingHom.ext hC
 | n+1,g₁,g₂,hC,hvar,hnilp=>by
  let g₁':z0 C n →+* B:=g₁.comp PowerSeries.C;let g₂':z0 C n →+* B:=g₂.comp PowerSeries.C
  have q2:g₁'=g₂':=z32 g₁' g₂'
   (fun c=>hC c)
   (fun j=>by simpa [g₁',g₂',z14] using hvar j.castSucc)
   (fun j=>by simpa [g₁',z14] using hnilp j.castSucc)
  obtain ⟨k,hk⟩:=hnilp (Fin.last n)
  have q1:g₁ (PowerSeries.X:PowerSeries (z0 C n))=g₂ (PowerSeries.X:PowerSeries (z0 C n)):=by
   simpa [z14] using hvar (Fin.last n)
  have q0:g₁ (PowerSeries.X:PowerSeries (z0 C n)) ^ k=0:=by
   simpa [z14] using hk
  exact z31 g₁ g₂ (fun a=>RingHom.congr_fun q2 a) q1 q0
lemma z33 {C B:Type} [CommRing C] [CommRing B]
  (f:C →+* B) :
  ∀ (n : ℕ) (cs:Fin n→B),(∀ i,∃ k : ℕ,cs i ^ k=0) →
   ∃ g:z0 C n →+* B,(∀ c:C,g (z13 C n c)=f c)∧(∀ i:Fin n,g (z14 C i)=cs i):=by
 intro n
 induction n with
 | zero =>
  intro cs _
  exact ⟨f,fun _=>rfl,fun i=>Fin.elim0 i⟩
 | succ n ih =>
  intro cs hcs
  obtain ⟨g0,hg0_C,hg0_var⟩:=ih (fun j=>cs j.castSucc) (fun j=>hcs j.castSucc)
  obtain ⟨k,hk⟩:=hcs (Fin.last n)
  refine ⟨z28 g0 (cs (Fin.last n)) k hk,?_,?_⟩
  ·
   intro c;change z28 g0 (cs (Fin.last n)) k hk (PowerSeries.C (z13 C n c))=f c;rw [z29,hg0_C]
  ·
   intro i
   refine Fin.lastCases ?_ ?_ i
   ·
    simp only [z14,Fin.lastCases_last];exact z30 g0 (cs (Fin.last n)) k hk
   ·
    intro j;simp only [z14,Fin.lastCases_castSucc];rw [z29,hg0_var]
lemma z34 {C:Type} [CommRing C] [IsLocalRing C] :
  ∀ n : ℕ,maximalIdeal (z0 C n)=(maximalIdeal C).map (z13 C n)⊔span (Set.range (z14 C (n:=n)))
 | 0=>by
  change maximalIdeal C=(maximalIdeal C).map (RingHom.id C)⊔span (Set.range _);rw [Ideal.map_id,Set.range_eq_empty,Ideal.span_empty,sup_bot_eq]
 | n+1=>by
  refine le_antisymm ?_ ?_
  ·
   intro f hf;have hf0:PowerSeries.constantCoeff f∈maximalIdeal (z0 C n):=(z3 f).mp hf
   have q1:f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
     span {(PowerSeries.X:PowerSeries (z0 C n))}:=by
    have h1:=z6 1
     (f - PowerSeries.C (PowerSeries.constantCoeff f)) (fun i hi=>by
      have hi0:i=0:=by omega
      subst hi0
      simp)
    simpa using h1
   have q2:PowerSeries.C (PowerSeries.constantCoeff f) ∈
     (maximalIdeal C).map (z13 C (n+1))⊔span (Set.range (z14 C (n:=n+1))):=by
    rw [z34 n] at hf0
    have q3:PowerSeries.C (PowerSeries.constantCoeff f) ∈
      ((maximalIdeal C).map (z13 C n)⊔span (Set.range (z14 C (n:=n)))).map PowerSeries.C :=
     mem_map_of_mem PowerSeries.C hf0
    rw [Ideal.map_sup,Ideal.map_map] at q3
    have q6:(maximalIdeal C).map (PowerSeries.C.comp (z13 C n))⊔(span (Set.range (z14 C (n:=n)))).map PowerSeries.C ≤ (maximalIdeal C).map (z13 C (n+1))⊔span (Set.range (z14 C (n:=n+1))):=by
     refine sup_le_sup le_rfl ?_
     rw [map_span,span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;exact subset_span ⟨j.castSucc,by simp [z14]⟩
    exact q6 q3
   have q4:(PowerSeries.X:PowerSeries (z0 C n)) ∈
     (maximalIdeal C).map (z13 C (n+1))⊔span (Set.range (z14 C (n:=n+1))) :=
    mem_sup_right (subset_span ⟨Fin.last n,by simp [z14]⟩)
   have q0:f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
     (maximalIdeal C).map (z13 C (n+1))⊔span (Set.range (z14 C (n:=n+1))) :=
    (span_singleton_le_iff_mem _).mpr q4 q1
   have q5:=Ideal.add_mem _ q2 q0;simpa using q5
  ·
   refine sup_le ?_ ?_
   ·
    rw [map_le_iff_le_comap];intro c hc;exact z17 (n+1) hc
   ·
    rw [span_le];rintro _ ⟨i,rfl⟩;exact z18 i
lemma z35 {C:Type} [CommRing C] [IsLocalRing C] :
  ∀ n : ℕ,Surjective ((residue (z0 C n)).comp (z13 C n))
 | 0=>residue_surjective
 | n+1=>by
  intro y;obtain ⟨f,rfl⟩:=residue_surjective y
  have q2:f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
    maximalIdeal (PowerSeries (z0 C n)):=by
   rw [z3,map_sub,PowerSeries.constantCoeff_C,sub_self];exact (maximalIdeal _).zero_mem
  obtain ⟨c,hc⟩:=z35 n (residue _ (PowerSeries.constantCoeff f))
  have q0:PowerSeries.constantCoeff f - z13 C n c∈maximalIdeal (z0 C n):=by
   rw [← residue_eq_zero_iff,map_sub]
   change residue _ (PowerSeries.constantCoeff f) -
    ((residue _).comp (z13 C n)) c=0
   rw [hc,sub_self]
  refine ⟨c,?_⟩
  change residue _ (PowerSeries.C (z13 C n c))=residue _ f
  symm
  rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff]
  have q1:f - PowerSeries.C (z13 C n c)=(f - PowerSeries.C (PowerSeries.constantCoeff f))+PowerSeries.C (PowerSeries.constantCoeff f - z13 C n c):=by
   rw [map_sub];ring
  rw [q1]
  refine (maximalIdeal _).add_mem q2 ?_
  rw [z3,PowerSeries.constantCoeff_C];exact q0
end BasicIterPowerSeries
section DimensionInequality
lemma z36 {S:Type*} [CommRing S] [IsLocalRing S]
  (I:Ideal S) [Nontrivial (S⧸I)] : IsLocalRing (S⧸I) :=
 IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
lemma z37 {A B:Type*} [CommRing A] [CommRing B]
  [Algebra A B] [Algebra.IsIntegral A B] (q0:Injective (algebraMap A B)) :
  ringKrullDim B=ringKrullDim A:=by
 have q1:ringKrullDim B ≤ ringKrullDim A:=by
  rw [ringKrullDim,ringKrullDim,Order.krullDim,Order.krullDim]
  refine iSup_le fun c => ?_
  let c':LTSeries (PrimeSpectrum A) :=
   {
    length:=c.length
    toFun:=fun i=>PrimeSpectrum.comap (algebraMap A B) (c i)
    step:=fun i=>IsIntegral.comap_lt_comap (c.step i) }
  exact le_iSup (fun s:LTSeries (PrimeSpectrum A)=>(s.length:WithBot ℕ∞)) c'
 have q2:ringKrullDim A ≤ ringKrullDim B:=by
  rw [ringKrullDim,ringKrullDim,Order.krullDim,Order.krullDim]
  refine iSup_le fun c => ?_
  obtain ⟨Q₀,_,hQ₀_prime,hQ₀_over⟩ :=
   Ideal.exists_ideal_over_prime_of_isIntegral (c 0).asIdeal (⊥ : Ideal B)
    (by
     rw [← RingHom.ker_eq_comap_bot,(RingHom.injective_iff_ker_eq_bot _).mp q0]
     exact bot_le)
  have : Q₀.IsPrime:=hQ₀_prime;have : Q₀.LiesOver (RelSeries.head c).asIdeal:=⟨hQ₀_over.symm⟩;obtain ⟨cB,hcB_len,_,_⟩:=Ideal.exists_ltSeries_of_hasGoingUp (R:=A) (S:=B) c Q₀;rw [← hcB_len]
  exact le_iSup (fun s:LTSeries (PrimeSpectrum B)=>(s.length:WithBot ℕ∞)) cB
 exact le_antisymm q1 q2
lemma z38 {A:Type*} [CommRing A] [IsDomain A]
  [IsLocalRing A] [IsNoetherianRing A] {I:Ideal A} (q4:I ≠ ⊥) (q3:I ≠ ⊤) :
  ringKrullDim (A⧸I) < ringKrullDim A:=by
 obtain ⟨r,hr⟩ :=
  ringKrullDim_quotient_eq_natCast
   I q3
 obtain ⟨n,hn⟩ :=
  ringKrullDim_quotient_eq_natCast
   (⊥ : Ideal A) bot_ne_top
 have q5:ringKrullDim A=(n:WithBot ℕ∞):=by
  rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A),hn]
 have hkd:Order.krullDim (PrimeSpectrum.zeroLocus (I:Set A))=(r:WithBot ℕ∞):=by
  rw [← ringKrullDim_quotient,hr]
 obtain ⟨c,hc⟩ :=
  OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.exists_ltSeries_of_krullDim_eq_natCast
   hkd
 have q0:(⟨⊥,Ideal.isPrime_bot⟩ : PrimeSpectrum A) < (c 0).1:=by
  refine lt_of_le_of_ne bot_le fun heq=>q4 ?_
  have hle:I ≤ (c 0).1.asIdeal:=(c 0).2;rw [← heq] at hle;exact le_bot_iff.mp hle
 let c':LTSeries (PrimeSpectrum A) :=
  {
   length:=c.length+1
   toFun:=Fin.cons ⟨⊥,Ideal.isPrime_bot⟩ (fun i=>(c i).1)
   step:=fun i=>by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using q0
    · simpa using c.step j }
 have q2:(c'.length:WithBot ℕ∞) ≤ ringKrullDim A:=by
  rw [ringKrullDim,Order.krullDim]
  exact le_iSup (fun s:LTSeries (PrimeSpectrum A)=>(s.length:WithBot ℕ∞)) c'
 rw [hr,q5]
 have q6:c'.length=r+1:=by simp [c',hc]
 rw [q6,q5] at q2
 have hnat:r+1 ≤ n:=by exact_mod_cast q2
 have q1:r < n:=by omega
 exact_mod_cast q1
lemma z39 :
  ∀ (r : ℕ) (D:Type) [CommRing D] [IsLocalRing D] [IsNoetherianRing D],
   ringKrullDim D=(r:WithBot ℕ∞) →
   ∃ us:Fin r→D,(∀ i,us i∈maximalIdeal D)∧(span (Set.range us)).radical=maximalIdeal D:=by
 intro r
 induction r with
 | zero =>
  intro D _ _ _ hdim
  refine ⟨Fin.elim0,fun i=>Fin.elim0 i,?_⟩
  rw [Set.range_eq_empty,Ideal.span_empty]
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal D).isPrime.radical];exact Ideal.radical_mono bot_le
  ·
   rw [Ideal.radical_eq_sInf,le_sInf_iff];intro P ⟨_,hP⟩;have hzero:Ring.KrullDimLE 0 D:=(Ring.krullDimLE_iff (n:=0) (R:=D)).mpr (by rw [hdim]);have q23:P.IsMaximal:=Ideal.isMaximal_iff_isPrime.mpr hP;rw [eq_maximalIdeal q23]
 | succ r ih =>
  intro D _ _ _ hdim;have q22:(minimalPrimes D).Finite:=Ideal.finite_minimalPrimes_of_isNoetherianRing D ⊥
  have q6 : ¬ ((maximalIdeal D:Set D) ⊆ ⋃ p∈minimalPrimes D,(p:Set D)):=by
   intro q19
   obtain ⟨p,hp_mem,hle⟩:=(Ideal.subset_union_prime_finite q22 ⊥ ⊥ fun q hq _ _=>hq.1.1).mp q19
   have q14:p=maximalIdeal D:=le_antisymm (le_maximalIdeal hp_mem.1.1.ne_top) hle
   have q15:ringKrullDim D ≤ 0:=by
    rw [ringKrullDim,Order.krullDim]
    refine iSup_le fun c => ?_
    by_cases hlen:c.length=0
    · simp [hlen]
    ·
     exfalso;have q13:(c 0).asIdeal < (c ⟨1,by omega⟩).asIdeal:=c.strictMono (by simp [Fin.lt_def]);obtain ⟨q,hq_min,hq_le⟩:=Ideal.exists_minimalPrimes_le (I := ⊥) (J:=(c 0).asIdeal) bot_le;have q3:q ≤ maximalIdeal D:=le_maximalIdeal hq_min.1.1.ne_top
     have q17:q=maximalIdeal D:=by
      have q18:q ≤ p:=q14.symm▸q3;have q7:p ≤ q:=hp_mem.2 ⟨hq_min.1.1,bot_le⟩ q18;exact q14▸le_antisymm q18 q7
     have q16:(c 0).asIdeal=maximalIdeal D:=le_antisymm (le_maximalIdeal (c 0).isPrime.ne_top) (q17▸hq_le);have q12:(c ⟨1,by omega⟩).asIdeal ≤ maximalIdeal D:=le_maximalIdeal (c ⟨1,by omega⟩).isPrime.ne_top;rw [q16] at q13;exact not_lt_of_ge q12 q13
   rw [hdim] at q15
   have : r+1 ≤ 0:=by exact_mod_cast q15
   omega
  obtain ⟨u0,hu0_mem,hu0_not⟩:=Set.not_subset.mp q6
  have q1:∀ p∈(annihilator D D).minimalPrimes,u0∉p:=by
   intro p hp hmem
   have q21:annihilator D D = ⊥ := by
    ext x;simp only [Module.mem_annihilator,Submodule.mem_bot]
    exact ⟨fun h=>by simpa using h 1,fun h y=>by simp [h]⟩
   rw [q21] at hp;exact hu0_not (Set.mem_biUnion hp hmem)
  have q10:span {u0} ≠ ⊤ :=
   ne_top_of_le_ne_top (maximalIdeal.isMaximal D).ne_top
    ((span_singleton_le_iff_mem _).mpr hu0_mem)
  have q4:ringKrullDim (D⧸span {u0})=(r:WithBot ℕ∞):=by
   have h1:=Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (R:=D) (M:=D) q1 hu0_mem
   have hsp:span {u0} = (u0•(⊤ : Ideal D)):=by
    ext x;simp only [mem_span_singleton,Submodule.mem_smul_pointwise_iff_exists,Submodule.mem_top,true_and,smul_eq_mul,dvd_def]
    exact ⟨fun ⟨a,ha⟩=>⟨a,ha.symm⟩,fun ⟨a,ha⟩=>⟨a,ha.symm⟩⟩
   rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquivAlgOfEq D hsp).toRingEquiv];rw [Module.supportDim_self_eq_ringKrullDim,hdim] at h1;have q11:(u0•(⊤ : Ideal D)) ≠ ⊤ := hsp▸q10
   obtain ⟨m,hm⟩ :=
    ringKrullDim_quotient_eq_natCast
     (u0•(⊤ : Ideal D)) q11
   have hsd:supportDim D (QuotSMulTop u0 D)=ringKrullDim (D⧸(u0•(⊤ : Ideal D))):=Module.supportDim_quotient_eq_ringKrullDim (R:=D) (I:=u0•(⊤ : Ideal D));rw [hsd,hm] at h1;rw [hm]
   have hnat:m+1=r+1:=by exact_mod_cast h1
   have : m=r:=by omega
   exact_mod_cast this
  let D':=D⧸span {u0};have : Nontrivial D':=Ideal.Quotient.nontrivial_iff.mpr q10;have : IsLocalRing D':=z36 (span {u0});obtain ⟨us',hus'_mem,hus'_rad⟩:=ih D' q4
  let q8:Fin r→D:=fun j=>(Ideal.Quotient.mk_surjective (us' j)).choose
  have q0:∀ j,Ideal.Quotient.mk (span {u0}) (q8 j)=us' j:=fun j=>(Ideal.Quotient.mk_surjective (us' j)).choose_spec
  have q2:(maximalIdeal D').comap (Ideal.Quotient.mk (span {u0}))=maximalIdeal D :=
   eq_maximalIdeal
    (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  let us:Fin (r+1)→D:=Fin.cons u0 q8
  refine ⟨us,?_,?_⟩
  ·
   intro i
   refine Fin.cases hu0_mem (fun j => ?_) i
   change q8 j∈maximalIdeal D;rw [← q2,mem_comap,q0 j];exact hus'_mem j
  ·
   refine le_antisymm ?_ ?_
   ·
    rw [← (maximalIdeal.isMaximal D).isPrime.radical]
    refine Ideal.radical_mono (span_le.mpr ?_)
    rintro _ ⟨i,rfl⟩
    refine Fin.cases hu0_mem (fun j => ?_) i
    change q8 j∈maximalIdeal D;rw [← q2,mem_comap,q0 j];exact hus'_mem j
   ·
    intro x hx
    have hx':Ideal.Quotient.mk (span {u0}) x∈maximalIdeal D':=by
     rw [← q2] at hx;exact hx
    rw [← hus'_rad] at hx';obtain ⟨k,hk⟩:=hx';rw [← map_pow] at hk
    have q5:span (Set.range us')=(span (Set.range us)).map (Ideal.Quotient.mk (span {u0})):=by
     rw [map_span]
     refine le_antisymm (span_le.mpr ?_) (span_le.mpr ?_)
     ·
      rintro _ ⟨j,rfl⟩;exact subset_span ⟨us j.succ,⟨j.succ,rfl⟩,q0 j⟩
     ·
      rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
      refine Fin.cases ?_ (fun j => ?_) i
      ·
       change Ideal.Quotient.mk (span {u0}) u0∈span (Set.range us');have h0:Ideal.Quotient.mk (span {u0}) u0=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (subset_span rfl);rw [h0];exact Ideal.zero_mem _
      ·
       change Ideal.Quotient.mk (span {u0}) (q8 j)∈span (Set.range us');rw [q0 j];exact subset_span ⟨j,rfl⟩
    rw [q5,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hk;obtain ⟨y,hy_span,hy_eq⟩:=hk
    have q19:x ^ k - y∈span {u0}:=by
     rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,hy_eq,sub_self]
    have q9:span {u0} ≤ span (Set.range us):=(span_singleton_le_iff_mem _).mpr (subset_span ⟨0,rfl⟩)
    refine ⟨k,?_⟩
    have q20:=Ideal.add_mem _ hy_span (q9 q19);simpa using q20
lemma z40 {B D:Type*} [CommRing B] [IsLocalRing B]
  [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B]
  [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [Algebra B D] (q22:∀ b∈maximalIdeal B,algebraMap B D b∈maximalIdeal D)
  (q17:Surjective ((residue D).comp (algebraMap B D)))
  (q20:((maximalIdeal B).map (algebraMap B D)).radical=maximalIdeal D) :
  Module.Finite B D:=by
 let I:Ideal D:=(maximalIdeal B).map (algebraMap B D)
 have q13:∃ N : ℕ,maximalIdeal D ^ N ≤ I:=by
  have hfg:(maximalIdeal D).FG:=IsNoetherian.noetherian _;have hle:maximalIdeal D ≤ I.radical:=q20.symm.le;exact Ideal.exists_pow_le_of_le_radical_of_fg hle hfg
 obtain ⟨N,hN⟩:=q13
 have q3:∀ k : ℕ,∃ S:Finset D,
   ((maximalIdeal D ^ k:Ideal D).restrictScalars B) ≤ Submodule.span B (S:Set D)⊔((maximalIdeal D ^ (k+1) : Ideal D).restrictScalars B):=by
  intro k;obtain ⟨T,hT⟩:=IsNoetherian.noetherian (maximalIdeal D ^ k)
  refine ⟨T,?_⟩
  intro x hx;have hx':x∈Submodule.span D (T:Set D):=hT▸hx;rw [Submodule.mem_span_finset] at hx';obtain ⟨g,_,rfl⟩:=hx'
  refine Submodule.sum_mem _ fun t ht => ?_
  obtain ⟨b,hb⟩:=q17 (residue D (g t))
  have q15:g t - algebraMap B D b∈maximalIdeal D:=by
   rw [← residue_eq_zero_iff,map_sub];change residue D (g t) - ((residue D).comp (algebraMap B D)) b=0;rw [hb,sub_self]
  have q8:g t•t=b•t+(g t - algebraMap B D b)*t:=by
   simp only [smul_eq_mul,Algebra.smul_def];ring
  rw [q8]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.mem_sup_left (Submodule.smul_mem _ b (Submodule.subset_span ht))
  ·
   refine Submodule.mem_sup_right ?_
   change (g t - algebraMap B D b)*t∈maximalIdeal D ^ (k+1);rw [pow_succ'];exact mul_mem_mul q15 (hT▸subset_span ht)
 have q2:∀ k : ℕ,∃ S:Finset D,
   (⊤ : Submodule B D) ≤ Submodule.span B (S:Set D)⊔((maximalIdeal D ^ k:Ideal D).restrictScalars B):=by
  intro k
  induction k with
  | zero =>
   refine ⟨∅,fun x _=>Submodule.mem_sup_right ?_⟩
   change x∈maximalIdeal D ^ 0;rw [pow_zero,Ideal.one_eq_top];exact Submodule.mem_top
  | succ k ih =>
   obtain ⟨S1,hS1⟩:=ih;obtain ⟨S2,hS2⟩:=q3 k
   classical
   refine ⟨S1 ∪ S2,fun x _ => ?_⟩
   obtain ⟨a,ha,y,hy,hxy⟩:=Submodule.mem_sup.mp (hS1 (Submodule.mem_top:x∈(⊤ : Submodule B D)));obtain ⟨b,hb,z,hz,hyz⟩:=Submodule.mem_sup.mp (hS2 hy)
   have q11:x=(a+b)+z:=by rw [← hxy,← hyz,add_assoc]
   rw [q11]
   refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right hz)
   exact Submodule.add_mem _
    (Submodule.span_mono (Finset.coe_subset.mpr Finset.subset_union_left) ha)
    (Submodule.span_mono (Finset.coe_subset.mpr Finset.subset_union_right) hb)
 obtain ⟨S,hS⟩:=q2 N
 have q9:∀ x:D,x∈Submodule.span B (S:Set D)⊔(I.restrictScalars B):=fun x=>by
  obtain ⟨a,ha,y,hy,hxy⟩:=Submodule.mem_sup.mp (hS (Submodule.mem_top:x∈(⊤ : Submodule B D)));rw [← hxy];exact Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right (hN hy))
 obtain ⟨G,hG⟩:=IsNoetherian.noetherian (maximalIdeal B)
 have q7:∀ k : ℕ,∀ x∈I ^ k,
   ∃ c:S→B,(∀ s,c s∈maximalIdeal B ^ k)∧x - ∑ s:S,c s•(s:D)∈I ^ (k+1):=by
  intro k
  induction k with
  | zero =>
   intro x _;obtain ⟨a,ha,y,hy,hxy⟩:=Submodule.mem_sup.mp (q9 x);rw [Submodule.mem_span_finset] at ha;obtain ⟨f,_,rfl⟩:=ha
   refine ⟨fun s=>f s.1,fun _=>by simp,?_⟩
   have q19 : ∑ s:S,f s.1•(s:D) = ∑ s∈S,f s•s:=Finset.sum_coe_sort S (fun s=>f s•s)
   rw [q19,← hxy,add_sub_cancel_left,pow_one];exact hy
  | succ k ih =>
   intro x hx;rw [pow_succ] at hx
   refine Submodule.mul_induction_on hx ?_ ?_
   ·
    intro a ha b hb
    have hb':b∈Submodule.span D (Set.range (fun g:G=>algebraMap B D (g:B))):=by
     have q16:I=span (Set.range (fun g:G=>algebraMap B D (g:B))):=by
      dsimp only [I];rw [← hG,map_span];congr 1;ext y;simp
     rw [q16] at hb;exact hb
    rw [Submodule.mem_span_range_iff_exists_fun] at hb';obtain ⟨u,hu⟩:=hb'
    have q12:∀ g:G,∃ c:S→B,(∀ s,c s∈maximalIdeal B ^ k)∧a*u g - ∑ s:S,c s•(s:D)∈I ^ (k+1):=fun g =>
     ih (a*u g) ((I ^ k).mul_mem_right (u g) ha)
    let c:S→B:=fun s => ∑ g:G,(q12 g).choose s*(g:B)
    refine ⟨c,?_,?_⟩
    ·
     intro s
     refine Ideal.sum_mem _ fun g _ => ?_
     rw [pow_succ];exact mul_mem_mul ((q12 g).choose_spec.1 s) (hG▸subset_span g.2)
    ·
     have hab:a*b = ∑ g:G,(a*u g)*algebraMap B D (g:B):=by
      rw [← hu,Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp [smul_eq_mul,mul_assoc]
     have q10 : ∑ s:S,c s•(s:D) = ∑ g:G,(∑ s:S,(q12 g).choose s•(s:D))*algebraMap B D (g:B):=by
      simp only [c,Finset.sum_smul];rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [Algebra.smul_def,map_mul];ring
     rw [hab,q10,← Finset.sum_sub_distrib]
     refine Ideal.sum_mem _ fun g _ => ?_
     rw [← sub_mul,pow_succ]
     exact mul_mem_mul ((q12 g).choose_spec.2)
      (mem_map_of_mem (algebraMap B D) (hG▸subset_span g.2))
   ·
    intro a b ⟨ca,hca_mem,hca_diff⟩ ⟨cb,hcb_mem,hcb_diff⟩
    refine ⟨fun s=>ca s+cb s,fun s=>Ideal.add_mem _ (hca_mem s) (hcb_mem s),?_⟩
    simp only [add_smul,Finset.sum_add_distrib]
    have q8:a+b - (∑ s:S,ca s•(s:D) + ∑ s:S,cb s•(s:D))=(a - ∑ s:S,ca s•(s:D))+(b - ∑ s:S,cb s•(s:D)):=by ring
    rw [q8];exact Ideal.add_mem _ hca_diff hcb_diff
 have q1:I ≤ maximalIdeal D:=map_le_iff_le_comap.mpr q22
 refine ⟨⟨S,?_⟩⟩
 rw [eq_top_iff];intro x _
 let step:(k : ℕ)→{ p:S→B // x - ∑ s:S,p s•(s:D)∈I ^ k } →
   { p:S→B // x - ∑ s:S,p s•(s:D)∈I ^ (k+1) }:=fun k prev =>
  let c:=(q7 k (x - ∑ s:S,prev.1 s•(s:D)) prev.2).choose
  ⟨fun s=>prev.1 s+c s,by
   have q15:=(q7 k (x - ∑ s:S,prev.1 s•(s:D)) prev.2).choose_spec.2;simp only [add_smul,Finset.sum_add_distrib]
   have q8:x - (∑ s:S,prev.1 s•(s:D) + ∑ s:S,c s•(s:D))=(x - ∑ s:S,prev.1 s•(s:D)) - ∑ s:S,c s•(s:D):=by ring
   rw [q8]
   exact q15⟩
 let seq:(k : ℕ)→{ p:S→B // x - ∑ s:S,p s•(s:D)∈I ^ k }:=Nat.rec ⟨fun _=>0,by simp⟩ step
 have q0:∀ (k : ℕ) (s:S),(seq (k+1)).1 s - (seq k).1 s∈maximalIdeal B ^ k :=
  fun k s=>by
   change ((seq k).1 s+(q7 k _ (seq k).2).choose s) - (seq k).1 s∈maximalIdeal B ^ k;rw [add_sub_cancel_left];exact (q7 k _ (seq k).2).choose_spec.1 s
 have q6:∀ (s:S) {a b : ℕ},a ≤ b→(seq a).1 s ≡ (seq b).1 s [SMOD (maximalIdeal B ^ a•(⊤ : Submodule B B))]:=by
  intro s a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top]
  induction b,hab using Nat.le_induction with
  | base=>simp
  | succ b hab ih =>
   have h1:(seq a).1 s - (seq (b+1)).1 s=((seq a).1 s - (seq b).1 s) - ((seq (b+1)).1 s - (seq b).1 s):=by ring
   rw [h1];exact Ideal.sub_mem _ ih (pow_le_pow_right hab (q0 b s))
 let q21:S→B:=fun s =>
  (IsPrecomplete.prec' (I:=maximalIdeal B) (M:=B) (fun k=>(seq k).1 s) (q6 s)).choose
 have q14:∀ (s:S) (k : ℕ),(seq k).1 s - q21 s∈maximalIdeal B ^ k:=fun s k=>by
  have h:=(IsPrecomplete.prec' (I:=maximalIdeal B) (M:=B)
   (fun k=>(seq k).1 s) (q6 s)).choose_spec k
  rw [SModEq.sub_mem,smul_eq_mul,mul_top] at h;exact h
 have q11:x = ∑ s:S,q21 s•(s:D):=by
  refine sub_eq_zero.mp ?_
  have q5:x - ∑ s:S,q21 s•(s:D) ∈
    ⨅ k : ℕ,(maximalIdeal D ^ k•(⊤ : Submodule D D)):=by
   rw [Submodule.mem_iInf];intro k;rw [smul_eq_mul,mul_top]
   refine z7 q1 k ?_
   have q8:x - ∑ s:S,q21 s•(s:D)=(x - ∑ s:S,(seq k).1 s•(s:D)) + ∑ s:S,((seq k).1 s - q21 s)•(s:D):=by
    simp only [sub_smul,Finset.sum_sub_distrib];ring
   rw [q8]
   refine Ideal.add_mem _ (seq k).2 (Ideal.sum_mem _ fun s _ => ?_)
   rw [Algebra.smul_def]
   refine (I ^ k).mul_mem_right (s:D) ?_
   have q4:(algebraMap B D) ((seq k).1 s - q21 s) ∈
     (maximalIdeal B ^ k).map (algebraMap B D) :=
    mem_map_of_mem (algebraMap B D) (q14 s k)
   rwa [Ideal.map_pow] at q4
  have q18:=Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R:=D) (M:=D)
   (maximalIdeal D) (maximalIdeal.isMaximal D).ne_top
  rw [q18] at q5;exact q5
 rw [q11]
 exact Submodule.sum_mem _ fun s _=>Submodule.smul_mem _ (q21 s) (Submodule.subset_span s.2)
lemma z41 (K:Type*) [Field K]
  (V W:Type*) [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [Nontrivial V] [Nontrivial W] :
  Nontrivial (V ⊗[K] W):=by
 obtain ⟨u,hu⟩:=exists_ne (0:V);obtain ⟨v,hv⟩:=exists_ne (0:W);let bV:=Module.Basis.ofVectorSpace K V;let bW:=Module.Basis.ofVectorSpace K W
 have q0:∃ i,bV.repr u i≠0:=by
  by_contra h;push Not at h
  exact hu (bV.repr.injective (by ext i;simp [h i]))
 obtain ⟨i,hi⟩:=q0
 have q1:∃ j,bW.repr v j≠0:=by
  by_contra h;push Not at h
  exact hv (bW.repr.injective (by ext j;simp [h j]))
 obtain ⟨j,hj⟩:=q1
 let B:V ⊗[K] W →ₗ[K] K :=
  TensorProduct.lift (LinearMap.mk₂ K (fun x y=>bV.coord i x*bW.coord j y)
   (fun _ _ _=>by simp [add_mul])
   (fun _ _ _=>by simp [mul_assoc])
   (fun _ _ _=>by simp [mul_add])
   (fun _ _ _=>by simp [mul_left_comm]))
 refine ⟨⟨u ⊗ₜ[K] v,0,fun h => ?_⟩⟩
 have hB:B (u ⊗ₜ[K] v)=B 0:=congrArg B h;simp only [B,TensorProduct.lift.tmul,LinearMap.mk₂_apply,map_zero,mul_eq_zero] at hB
 rcases hB with h1 | h2
 · exact hi h1
 · exact hj h2
lemma z42 {B₁ D₁ K:Type*}
  [CommRing B₁] [IsDomain B₁] [CommRing D₁] [Field K]
  [Algebra B₁ D₁] [Algebra B₁ K]
  (hD:Injective (algebraMap B₁ D₁))
  (hK:Injective (algebraMap B₁ K)) :
  Nontrivial (K ⊗[B₁] D₁):=by
 let K₁ := FractionRing B₁
 let q1:K₁ →+* K:=IsLocalization.lift (M:=nonZeroDivisors B₁) (g:=algebraMap B₁ K)
  (fun y=>by
   have hy0:(y:B₁)≠0:=nonZeroDivisors.ne_zero y.2
   exact isUnit_iff_ne_zero.mpr fun h0=>hy0 (hK (by simpa using h0)))
 let _:Algebra K₁ K:=q1.toAlgebra
 have : IsScalarTower B₁ K₁ K:=IsScalarTower.of_algebraMap_eq fun b=>by
  change algebraMap B₁ K b=q1 (algebraMap B₁ K₁ b);exact (IsLocalization.lift_eq _ b).symm
 have q0:Injective ((Algebra.linearMap B₁ D₁).lTensor K₁):=Module.Flat.lTensor_preserves_injective_linearMap (Algebra.linearMap B₁ D₁) hD
 have hK₁D_nt:Nontrivial (K₁ ⊗[B₁] D₁):=by
  refine ⟨⟨1 ⊗ₜ[B₁] 1,0,fun h => ?_⟩⟩
  have h0:((Algebra.linearMap B₁ D₁).lTensor K₁) (1 ⊗ₜ[B₁] 1)=((Algebra.linearMap B₁ D₁).lTensor K₁) 0:=by
   simpa [LinearMap.lTensor_tmul] using h
  have h10:(1:K₁) ⊗ₜ[B₁] (1:B₁)=0:=q0 h0;let e:=TensorProduct.rid B₁ K₁;have h1:e (1 ⊗ₜ[B₁] 1)=e 0:=congrArg e h10;simp only [e,TensorProduct.rid_tmul,one_smul,map_zero] at h1;exact one_ne_zero h1
 let e:K ⊗[B₁] D₁ ≃ₗ[K₁] K ⊗[K₁] (K₁ ⊗[B₁] D₁):=(TensorProduct.AlgebraTensorModule.cancelBaseChange B₁ K₁ K₁ K D₁).symm;exact e.toEquiv.nontrivial_congr.mpr (z41 K₁ K (K₁ ⊗[B₁] D₁))
lemma z43 {S:Type*} [CommRing S] [IsLocalRing S]
  [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S] (I:Ideal S)
  [IsLocalRing (S⧸I)] :
  IsAdicComplete (maximalIdeal (S⧸I)) (S⧸I):=by
 have q1:maximalIdeal (S⧸I)=(maximalIdeal S).map (Ideal.Quotient.mk I):=by
  have q4:(maximalIdeal (S⧸I)).comap (Ideal.Quotient.mk I)=maximalIdeal S:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);rw [← q4,Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
 refine { haus' := ?_,prec' := ?_ }
 ·
  intro x hx
  have q6:x ∈ ⨅ k : ℕ,(maximalIdeal (S⧸I) ^ k•(⊤ : Submodule (S⧸I) (S⧸I))):=by
   rw [Submodule.mem_iInf];intro k;simpa [SModEq.zero] using hx k
  have q7:=Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R:=S⧸I) (M:=S⧸I)
   (maximalIdeal (S⧸I)) (maximalIdeal.isMaximal (S⧸I)).ne_top
  rw [q7] at q6;exact q6
 ·
  intro seq hseq
  have q5:∀ k : ℕ,∃ d:S,d∈maximalIdeal S ^ k∧Ideal.Quotient.mk I d=seq (k+1) - seq k:=fun k=>by
   have hk:=hseq (Nat.le_succ k);rw [SModEq.sub_mem,smul_eq_mul,mul_top,q1,← Ideal.map_pow,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hk;obtain ⟨d,hd,hdeq⟩:=hk
   refine ⟨-d,(maximalIdeal S ^ k).neg_mem hd,?_⟩
   rw [map_neg,hdeq,neg_sub]
  let a0:S:=(Ideal.Quotient.mk_surjective (seq 0)).choose;have ha0:Ideal.Quotient.mk I a0=seq 0:=(Ideal.Quotient.mk_surjective (seq 0)).choose_spec
  let q3 : ℕ → S:=fun k=>a0 + ∑ j∈Finset.range k,(q5 j).choose
  have q0:∀ k : ℕ,Ideal.Quotient.mk I (q3 k)=seq k:=fun k=>by
   induction k with
   | zero=>simp [q3,ha0]
   | succ k ih =>
    dsimp only [q3] at ih ⊢;rw [Finset.sum_range_succ,← add_assoc,map_add,ih,(q5 k).choose_spec.2];ring
  have q2:∀ {a b : ℕ},a ≤ b→q3 a ≡ q3 b [SMOD (maximalIdeal S ^ a•(⊤ : Submodule S S))]:=by
   intro a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top]
   induction b,hab using Nat.le_induction with
   | base=>simp
   | succ b hab ih =>
    have h1:q3 a - q3 (b+1)=(q3 a - q3 b) - (q5 b).choose:=by
     dsimp only [q3];rw [Finset.sum_range_succ];ring
    rw [h1];exact Ideal.sub_mem _ ih (pow_le_pow_right hab (q5 b).choose_spec.1)
  obtain ⟨L,hL⟩:=IsPrecomplete.prec' (I:=maximalIdeal S) (M:=S) q3 q2
  refine ⟨Ideal.Quotient.mk I L,fun k => ?_⟩
  rw [SModEq.sub_mem,smul_eq_mul,mul_top,q1,← Ideal.map_pow,← q0 k,← map_sub];have hLk:=hL k;rw [SModEq.sub_mem,smul_eq_mul,mul_top] at hLk;exact mem_map_of_mem (Ideal.Quotient.mk I) hLk
set_option maxHeartbeats 800000 in
lemma z44 {Λ : Type} [CommRing Λ] [IsRegularLocalRing Λ] [IsDomain Λ]
  [IsAdicComplete (maximalIdeal Λ) Λ]
  (n : ℕ) (P Q:Ideal (z0 Λ n)) [P.IsPrime] [Q.IsPrime]
  (r' s' : ℕ)
  (u:Fin r'→z0 Λ n) (q25:∀ i,u i∈maximalIdeal (z0 Λ n))
  (v:Fin s'→z0 Λ n) (q18:∀ j,v j∈maximalIdeal (z0 Λ n))
  (q21:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range u)⊔P).radical=maximalIdeal (z0 Λ n))
  (q24:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range v)⊔Q).radical=maximalIdeal (z0 Λ n))
  (q12:∀ f:z0 Λ r' →+* (z0 Λ n⧸P),(∀ c,f (z13 Λ r' c)=Ideal.Quotient.mk P (z13 Λ n c))→(∀ i,f (z14 Λ i)=Ideal.Quotient.mk P (u i))→Injective f)
  (q14:∀ f:z0 Λ s' →+* (z0 Λ n⧸Q),(∀ c,f (z13 Λ s' c)=Ideal.Quotient.mk Q (z13 Λ n c))→(∀ j,f (z14 Λ j)=Ideal.Quotient.mk Q (v j))→Injective f) :
  let R:=z0 Λ n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 Λ n) n;let i₂ : R →+* T:=z13 R n
  ringKrullDim Λ + (s':WithBot ℕ∞)+(r':WithBot ℕ∞) ≤
   ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
 intro R T i₁ i₂;let I:Ideal T:=P.map i₁ ⊔ Q.map i₂
 have q4:I ≤ maximalIdeal T:=by
  refine sup_le ?_ ?_
  ·
   rw [map_le_iff_le_comap];intro x hx
   exact z23 (fun c hc=>z17 n hc) n
    (le_maximalIdeal ‹P.IsPrime›.ne_top hx)
  ·
   rw [map_le_iff_le_comap];intro x hx;exact z17 n (le_maximalIdeal ‹Q.IsPrime›.ne_top hx)
 have q3:I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal T).ne_top q4;let A:=T⧸I;have : Nontrivial A:=Ideal.Quotient.nontrivial_iff.mpr q3;have : IsLocalRing A:=z36 I;have : IsLocalRing (R⧸P):=z36 P;have : IsLocalRing (R⧸Q):=z36 Q;have : IsAdicComplete (maximalIdeal A) A:=z43 I;have : IsAdicComplete (maximalIdeal (R⧸P)) (R⧸P):=z43 P
 have : IsAdicComplete (maximalIdeal (R⧸Q)) (R⧸Q):=z43 Q;have q1:(maximalIdeal (R⧸P)).comap (Ideal.Quotient.mk P)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);have q2:(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
 have q0:(maximalIdeal A).comap (Ideal.Quotient.mk I)=maximalIdeal T:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);let B₁ := z0 Λ r';let B₂ := z0 Λ s';let B:=z0 B₂ r'
 obtain ⟨f₁,hf₁_C,hf₁_var,hf₁_loc⟩ :=
  z24 (C := Λ) (R:=R⧸P)
   ((Ideal.Quotient.mk P).comp (z13 Λ n))
   (fun c hc=>by
    rw [RingHom.comp_apply,← mem_comap,q1]
    exact z17 n hc)
   r' (fun i=>Ideal.Quotient.mk P (u i))
   (fun i=>by rw [← mem_comap,q1];exact q25 i)
 obtain ⟨f₂,hf₂_C,hf₂_var,hf₂_loc⟩ :=
  z24 (C := Λ) (R:=R⧸Q)
   ((Ideal.Quotient.mk Q).comp (z13 Λ n))
   (fun c hc=>by
    rw [RingHom.comp_apply,← mem_comap,q2]
    exact z17 n hc)
   s' (fun j=>Ideal.Quotient.mk Q (v j))
   (fun j=>by rw [← mem_comap,q2];exact q18 j)
 have hf₁_inj:Injective f₁ := q12 f₁ hf₁_C hf₁_var;have hf₂_inj:Injective f₂ := q14 f₂ hf₂_C hf₂_var;let j₁ : B₁ →+* B:=z15 (z13 Λ s') r';let j₂ : B₂ →+* B:=z13 B₂ r';have hj₁_inj:Injective j₁ := z21 (z16 Λ s') r';have hj₂_inj:Injective j₂ := z16 B₂ r'
 obtain ⟨β₂,hβ₂_C,hβ₂_var,hβ₂_loc⟩ :=
  z24 (C := Λ) (R:=A)
   (((Ideal.Quotient.mk I).comp i₂).comp (z13 Λ n))
   (fun c hc=>by
    rw [RingHom.comp_apply,RingHom.comp_apply,← mem_comap,q0]
    exact z17 n (z17 n hc))
   s' (fun j=>Ideal.Quotient.mk I (i₂ (v j)))
   (fun j=>by
    rw [← mem_comap,q0]
    exact z17 n (q18 j))
 obtain ⟨β,hβ_C,hβ_var,hβ_loc⟩ :=
  z24 (C:=B₂) (R:=A) β₂ hβ₂_loc
   r' (fun i=>Ideal.Quotient.mk I (i₁ (u i)))
   (fun i=>by
    rw [← mem_comap,q0]
    exact z23 (fun c hc=>z17 n hc) n (q25 i))
 have hrad₁ : ((maximalIdeal B₁).map f₁).radical=maximalIdeal (R⧸P):=by
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal (R⧸P)).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr hf₁_loc)
  ·
   intro x hx;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective x;have hy:y∈maximalIdeal R:=q1▸hx;rw [← q21] at hy;obtain ⟨k,hk⟩:=hy
   refine ⟨k,?_⟩
   rw [← map_pow]
   have q13:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range u)⊔P).map
     (Ideal.Quotient.mk P) ≤ (maximalIdeal B₁).map f₁ := by
    rw [Ideal.map_sup,Ideal.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    ·
     rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap];have q35:Ideal.Quotient.mk P (z13 Λ n c)=f₁ (z13 Λ r' c):=(hf₁_C c).symm;rw [q35];exact mem_map_of_mem f₁ (z17 r' hc)
    ·
     rw [map_span,span_le];rintro _ ⟨_,⟨i,rfl⟩,rfl⟩;rw [← hf₁_var i];exact mem_map_of_mem f₁ (z18 i)
    ·
     rw [map_le_iff_le_comap];intro p hp;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr hp];exact Ideal.zero_mem _
   exact q13 (mem_map_of_mem (Ideal.Quotient.mk P) hk)
 have hrad₂ : ((maximalIdeal B₂).map f₂).radical=maximalIdeal (R⧸Q):=by
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal (R⧸Q)).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr hf₂_loc)
  ·
   intro x hx;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective x;have hy:y∈maximalIdeal R:=q2▸hx;rw [← q24] at hy;obtain ⟨k,hk⟩:=hy
   refine ⟨k,?_⟩
   rw [← map_pow]
   have q13:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range v)⊔Q).map
     (Ideal.Quotient.mk Q) ≤ (maximalIdeal B₂).map f₂ := by
    rw [Ideal.map_sup,Ideal.map_sup]
    refine sup_le (sup_le ?_ ?_) ?_
    ·
     rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap];have q35:Ideal.Quotient.mk Q (z13 Λ n c)=f₂ (z13 Λ s' c):=(hf₂_C c).symm;rw [q35];exact mem_map_of_mem f₂ (z17 s' hc)
    ·
     rw [map_span,span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;rw [← hf₂_var j];exact mem_map_of_mem f₂ (z18 j)
    ·
     rw [map_le_iff_le_comap];intro q hq;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr hq];exact Ideal.zero_mem _
   exact q13 (mem_map_of_mem (Ideal.Quotient.mk Q) hk)
 have q33:((maximalIdeal B).map β).radical=maximalIdeal A:=by
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal A).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr hβ_loc)
  ·
   have q9:maximalIdeal A=(maximalIdeal T).map (Ideal.Quotient.mk I):=by
    rw [← q0,Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
   rw [q9,z34 n,Ideal.map_sup]
   refine sup_le ?_ ?_
   ·
    rw [Ideal.map_map,map_le_iff_le_comap];intro y hy;rw [← q24] at hy;obtain ⟨k,hk⟩:=hy
    refine ⟨k,?_⟩
    rw [RingHom.comp_apply,← map_pow,← map_pow]
    have q13:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range v)⊔Q).map
      ((Ideal.Quotient.mk I).comp i₂) ≤ (maximalIdeal B).map β := by
     rw [Ideal.map_sup,Ideal.map_sup]
     refine sup_le (sup_le ?_ ?_) ?_
     ·
      rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap];change Ideal.Quotient.mk I (i₂ (z13 Λ n c))∈(maximalIdeal B).map β
      have q31:Ideal.Quotient.mk I (i₂ (z13 Λ n c)) = β (j₂ (z13 Λ s' c)):=by
       rw [hβ_C,hβ₂_C];rfl
      rw [q31];exact mem_map_of_mem β (z17 r' (z17 s' hc))
     ·
      rw [map_span,span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;change Ideal.Quotient.mk I (i₂ (v j))∈(maximalIdeal B).map β;rw [← hβ₂_var j,← hβ_C];exact mem_map_of_mem β (z17 r' (z18 j))
     ·
      rw [map_le_iff_le_comap];intro q hq;rw [mem_comap,RingHom.comp_apply];have hqI:i₂ q∈I:=mem_sup_right (mem_map_of_mem i₂ hq);rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqI];exact Ideal.zero_mem _
    exact q13 (mem_map_of_mem ((Ideal.Quotient.mk I).comp i₂) hk)
   ·
    rw [map_span,span_le];rintro _ ⟨_,⟨k,rfl⟩,rfl⟩;have q16:z14 R k=i₁ (z14 Λ k):=(z20 (z13 Λ n) k).symm;rw [q16];have hy:z14 Λ k∈maximalIdeal R:=z18 k;rw [← q21] at hy;obtain ⟨m,hm⟩:=hy
    refine ⟨m,?_⟩
    rw [← map_pow,← map_pow]
    have q13:((maximalIdeal Λ).map (z13 Λ n)⊔span (Set.range u)⊔P).map
      ((Ideal.Quotient.mk I).comp i₁) ≤ (maximalIdeal B).map β := by
     rw [Ideal.map_sup,Ideal.map_sup]
     refine sup_le (sup_le ?_ ?_) ?_
     ·
      rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,RingHom.comp_apply];have h12:i₁ (z13 Λ n c)=i₂ (z13 Λ n c):=z19 (z13 Λ n) n c;rw [h12]
      have q31:Ideal.Quotient.mk I (i₂ (z13 Λ n c)) = β (j₂ (z13 Λ s' c)):=by
       rw [hβ_C,hβ₂_C];rfl
      rw [q31];exact mem_map_of_mem β (z17 r' (z17 s' hc))
     ·
      rw [map_span,span_le];rintro _ ⟨_,⟨i,rfl⟩,rfl⟩;change Ideal.Quotient.mk I (i₁ (u i))∈(maximalIdeal B).map β;rw [← hβ_var i];exact mem_map_of_mem β (z18 i)
     ·
      rw [map_le_iff_le_comap];intro p hp;rw [mem_comap,RingHom.comp_apply];have hpI:i₁ p∈I:=mem_sup_left (mem_map_of_mem i₁ hp);rw [Ideal.Quotient.eq_zero_iff_mem.mpr hpI];exact Ideal.zero_mem _
    exact q13 (mem_map_of_mem ((Ideal.Quotient.mk I).comp i₁) hm)
 letI : Algebra B₁ (R⧸P):=f₁.toAlgebra
 letI : Algebra B₂ (R⧸Q):=f₂.toAlgebra
 letI : Algebra B₁ B:=j₁.toAlgebra
 letI : Algebra B₂ B:=j₂.toAlgebra
 letI : Algebra B A := β.toAlgebra
 have q29:Surjective ((residue (R⧸P)).comp f₁):=by
  intro y;obtain ⟨r,rfl⟩:=residue_surjective y;obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective r;obtain ⟨c,hc⟩:=z35 n (residue R x)
  refine ⟨z13 Λ r' c,?_⟩
  rw [RingHom.comp_apply,hf₁_C]
  symm
  rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,RingHom.comp_apply,← map_sub,← mem_comap,q1,← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 Λ n)) c=0;rw [hc,sub_self]
 have q32:Surjective ((residue (R⧸Q)).comp f₂):=by
  intro y;obtain ⟨r,rfl⟩:=residue_surjective y;obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective r;obtain ⟨c,hc⟩:=z35 n (residue R x)
  refine ⟨z13 Λ s' c,?_⟩
  rw [RingHom.comp_apply,hf₂_C]
  symm
  rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,RingHom.comp_apply,← map_sub,← mem_comap,q2,← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 Λ n)) c=0;rw [hc,sub_self]
 have q30:Surjective ((residue A).comp β):=by
  intro y;obtain ⟨a,rfl⟩:=residue_surjective y;obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;obtain ⟨x,hx⟩:=z35 n (residue T t);obtain ⟨c,hc⟩:=z35 n (residue R x)
  refine ⟨j₂ (z13 Λ s' c),?_⟩
  rw [RingHom.comp_apply,hβ_C,hβ₂_C]
  symm
  rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff];change Ideal.Quotient.mk I t - Ideal.Quotient.mk I (i₂ (z13 Λ n c))∈maximalIdeal A;rw [← map_sub,← mem_comap,q0]
  have ht1:t - i₂ x∈maximalIdeal T:=by
   rw [← residue_eq_zero_iff,map_sub];change residue T t - ((residue T).comp (z13 R n)) x=0;rw [hx,sub_self]
  have ht2:x - z13 Λ n c∈maximalIdeal R:=by
   rw [← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 Λ n)) c=0;rw [hc,sub_self]
  have q19:t - i₂ (z13 Λ n c)=(t - i₂ x)+i₂ (x - z13 Λ n c):=by
   rw [map_sub];ring
  rw [q19];exact (maximalIdeal T).add_mem ht1 (z17 n ht2)
 have : Module.Finite B₁ (R⧸P):=z40 hf₁_loc q29 hrad₁;have : Module.Finite B₂ (R⧸Q):=z40 hf₂_loc q32 hrad₂;have : Module.Finite B A:=z40 hβ_loc q30 q33;let A₁ := B ⊗[B₁] (R⧸P);let A₂ := B ⊗[B₂] (R⧸Q)
 letI : Algebra B A₁ := Algebra.TensorProduct.leftAlgebra
 letI : Algebra B A₂ := Algebra.TensorProduct.leftAlgebra
 let M:=A₁ ⊗[B] A₂
 letI : CommRing M:=inferInstanceAs (CommRing (A₁ ⊗[B] A₂))
 letI : Algebra B M:=inferInstanceAs (Algebra B (A₁ ⊗[B] A₂))
 have : Module.Finite B A₁ := inferInstance;have : Module.Finite B A₂ := inferInstance;have : Module.Finite B M:=inferInstance
 have hβ_inj:Injective β := by
  rw [injective_iff_map_eq_zero];intro b hb
  have q7:(algebraMap B M) b ∈ ⨅ t : ℕ,(maximalIdeal B ^ t•(⊤ : Submodule B M)):=by
   rw [Submodule.mem_iInf];intro t;let Jt:Ideal M:=(maximalIdeal B ^ t).map (algebraMap B M);let Mt:=M⧸Jt;let q41:M →+* Mt:=Ideal.Quotient.mk Jt;let toA₁ : (R⧸P) →+* A₁ := Algebra.TensorProduct.includeRight.toRingHom;let toA₂ : (R⧸Q) →+* A₂ := Algebra.TensorProduct.includeRight.toRingHom;let q39:A₁ →+* M:=Algebra.TensorProduct.includeLeftRingHom
   let q34:A₂ →+* M:=Algebra.TensorProduct.includeRight.toRingHom;let φ₁ : R →+* Mt:=q41.comp (q39.comp (toA₁.comp (Ideal.Quotient.mk P)));let φ₂ : R →+* Mt:=q41.comp (q34.comp (toA₂.comp (Ideal.Quotient.mk Q)))
   have q10:∀ z∈maximalIdeal B,(q41 (algebraMap B M z)) ^ t=0:=fun z hz=>by
    rw [← map_pow,← map_pow,Ideal.Quotient.eq_zero_iff_mem];exact mem_map_of_mem (algebraMap B M) (Ideal.pow_mem_pow hz t)
   have q8:∀ z:B₁,toA₁ (f₁ z)=algebraMap B A₁ (j₁ z):=fun z=>by
    change (1:B) ⊗ₜ[B₁] (f₁ z)=(j₁ z) ⊗ₜ[B₁] (1:R⧸P)
    have hz1:f₁ z=z•(1:R⧸P):=by rw [Algebra.smul_def,mul_one];rfl
    have hz2:j₁ z=z•(1:B):=by rw [Algebra.smul_def,mul_one];rfl
    rw [hz1,hz2,TensorProduct.tmul_smul,smul_tmul']
   have q11:∀ z:B₂,toA₂ (f₂ z)=algebraMap B A₂ (j₂ z):=fun z=>by
    change (1:B) ⊗ₜ[B₂] (f₂ z)=(j₂ z) ⊗ₜ[B₂] (1:R⧸Q)
    have hz1:f₂ z=z•(1:R⧸Q):=by rw [Algebra.smul_def,mul_one];rfl
    have hz2:j₂ z=z•(1:B):=by rw [Algebra.smul_def,mul_one];rfl
    rw [hz1,hz2,TensorProduct.tmul_smul,smul_tmul']
   have q6:∀ z:B,q39 (algebraMap B A₁ z)=q34 (algebraMap B A₂ z):=fun z=>by
    change (algebraMap B A₁ z) ⊗ₜ[B] (1:A₂)=(1:A₁) ⊗ₜ[B] (algebraMap B A₂ z);have hz1:algebraMap B A₁ z=z•(1:A₁):=Algebra.algebraMap_eq_smul_one z;have hz2:algebraMap B A₂ z=z•(1:A₂):=Algebra.algebraMap_eq_smul_one z;rw [hz1,hz2,TensorProduct.tmul_smul,smul_tmul']
   have hφ₁_nilp:∀ x∈maximalIdeal R,∃ k : ℕ,φ₁ x ^ k=0:=fun x hx=>by
    have hx':Ideal.Quotient.mk P x∈((maximalIdeal B₁).map f₁).radical:=by
     rw [hrad₁,← mem_comap,q1];exact hx
    obtain ⟨k,hk⟩:=hx'
    refine ⟨k*t,?_⟩
    rw [pow_mul,← map_pow];have q5:(Ideal.Quotient.mk P x) ^ k∈(maximalIdeal B₁).map f₁ := hk
    have hJt:toA₁ ((Ideal.Quotient.mk P x) ^ k)∈(maximalIdeal B).map (algebraMap B A₁):=by
     have hle:((maximalIdeal B₁).map f₁).map toA₁ ≤ (maximalIdeal B).map (algebraMap B A₁):=by
      rw [Ideal.map_map,map_le_iff_le_comap];intro z hz;rw [mem_comap,RingHom.comp_apply,q8 z]
      exact mem_map_of_mem (algebraMap B A₁)
       (z23 (fun c hc=>z17 s' hc) r' hz)
     exact hle (mem_map_of_mem toA₁ q5)
    have q17:q39 (toA₁ ((Ideal.Quotient.mk P x) ^ k)) ∈
      (maximalIdeal B).map (algebraMap B M):=by
     have hle:((maximalIdeal B).map (algebraMap B A₁)).map q39 ≤ (maximalIdeal B).map (algebraMap B M):=by
      rw [Ideal.map_map];exact le_of_eq rfl
     exact hle (mem_map_of_mem q39 hJt)
    have q37:(q39 (toA₁ ((Ideal.Quotient.mk P x) ^ k))) ^ t∈Jt:=by
     have h1:(q39 (toA₁ ((Ideal.Quotient.mk P x) ^ k))) ^ t ∈
       ((maximalIdeal B).map (algebraMap B M)) ^ t:=Ideal.pow_mem_pow q17 t
     rwa [← Ideal.map_pow] at h1
    change (q41 (q39 (toA₁ (Ideal.Quotient.mk P (x ^ k))))) ^ t=0;rw [map_pow (Ideal.Quotient.mk P),← map_pow q41];exact Ideal.Quotient.eq_zero_iff_mem.mpr q37
   obtain ⟨Ψ,hΨ_C,hΨ_var⟩:=z33 φ₂ n
    (fun k => φ₁ (z14 Λ k))
    (fun k=>hφ₁_nilp (z14 Λ k) (z18 k))
   have hφ12_C:∀ c : Λ,φ₁ (z13 Λ n c) = φ₂ (z13 Λ n c):=fun c=>by
    have h1:toA₁ (Ideal.Quotient.mk P (z13 Λ n c))=algebraMap B A₁ (j₁ (z13 Λ r' c)):=by
     have hc:Ideal.Quotient.mk P (z13 Λ n c)=f₁ (z13 Λ r' c):=(hf₁_C c).symm;rw [hc,q8]
    have h2:toA₂ (Ideal.Quotient.mk Q (z13 Λ n c))=algebraMap B A₂ (j₂ (z13 Λ s' c)):=by
     have hc:Ideal.Quotient.mk Q (z13 Λ n c)=f₂ (z13 Λ s' c):=(hf₂_C c).symm;rw [hc,q11]
    have q42:j₁ (z13 Λ r' c)=j₂ (z13 Λ s' c):=z19 (z13 Λ s') r' c;dsimp only [φ₁,φ₂];simp only [RingHom.comp_apply,h1,h2,q42];rw [q6]
   have hΨ_i₁ : Ψ.comp i₁ = φ₁ := by
    refine z32 (Ψ.comp i₁) φ₁ ?_ ?_ ?_
    ·
     intro c;rw [RingHom.comp_apply,z19 (z13 Λ n) n c];change Ψ (z13 R n (z13 Λ n c)) = φ₁ (z13 Λ n c);rw [hΨ_C,hφ12_C]
    ·
     intro k;rw [RingHom.comp_apply,z20 (z13 Λ n) k];exact hΨ_var k
    ·
     intro k;rw [RingHom.comp_apply,z20 (z13 Λ n) k,hΨ_var k];exact hφ₁_nilp (z14 Λ k) (z18 k)
   have q28:I ≤ RingHom.ker Ψ := by
    refine sup_le ?_ ?_
    ·
     rw [map_le_iff_le_comap];intro p hp;rw [mem_comap,RingHom.mem_ker];change (Ψ.comp i₁) p=0;rw [hΨ_i₁];dsimp only [φ₁];simp [Ideal.Quotient.eq_zero_iff_mem.mpr hp]
    ·
     rw [map_le_iff_le_comap];intro q hq;rw [mem_comap,RingHom.mem_ker];change Ψ (z13 R n q)=0;rw [hΨ_C];dsimp only [φ₂];simp [Ideal.Quotient.eq_zero_iff_mem.mpr hq]
   let barΨ : A →+* Mt:=Ideal.Quotient.lift I Ψ q28
   have hbarΨ_mk:∀ x:T,barΨ (Ideal.Quotient.mk I x) = Ψ x:=fun x =>
    Ideal.Quotient.lift_mk I Ψ q28
   have hbarΨ_β : barΨ.comp β = q41.comp (algebraMap B M):=by
    have q20:(barΨ.comp β).comp j₂ = (q41.comp (algebraMap B M)).comp j₂ := by
     refine z32 _ _ ?_ ?_ ?_
     ·
      intro c;dsimp only [j₂];simp only [RingHom.comp_apply,hβ_C,hβ₂_C];change barΨ (Ideal.Quotient.mk I (i₂ (z13 Λ n c)))=q41 (algebraMap B M (j₂ (z13 Λ s' c)));rw [hbarΨ_mk];change Ψ (z13 R n (z13 Λ n c))=_;rw [hΨ_C];dsimp only [φ₂];simp only [RingHom.comp_apply]
      have h2:toA₂ (Ideal.Quotient.mk Q (z13 Λ n c))=algebraMap B A₂ (j₂ (z13 Λ s' c)):=by
       have hc:Ideal.Quotient.mk Q (z13 Λ n c)=f₂ (z13 Λ s' c):=(hf₂_C c).symm;rw [hc,q11]
      rw [h2,← q6];rfl
     ·
      intro j;dsimp only [j₂];simp only [RingHom.comp_apply,hβ_C,hβ₂_var];change barΨ (Ideal.Quotient.mk I (i₂ (v j)))=q41 (algebraMap B M (j₂ (z14 Λ j)));rw [hbarΨ_mk];change Ψ (z13 R n (v j))=q41 (algebraMap B M (j₂ (z14 Λ j)));rw [hΨ_C];dsimp only [φ₂];simp only [RingHom.comp_apply]
      have h2:toA₂ (Ideal.Quotient.mk Q (v j))=algebraMap B A₂ (j₂ (z14 Λ j)):=by
       rw [← hf₂_var j,q11]
      rw [h2,← q6];rfl
     ·
      intro j
      refine ⟨t,?_⟩
      have q40:((barΨ.comp β).comp j₂) (z14 Λ j)=q41 (algebraMap B M (j₂ (z14 Λ j))):=by
       dsimp only [j₂];simp only [RingHom.comp_apply,hβ_C,hβ₂_var];change barΨ (Ideal.Quotient.mk I (i₂ (v j)))=q41 (algebraMap B M (j₂ (z14 Λ j)));rw [hbarΨ_mk];change Ψ (z13 R n (v j))=q41 (algebraMap B M (j₂ (z14 Λ j)));rw [hΨ_C];dsimp only [φ₂];simp only [RingHom.comp_apply]
       have h2:toA₂ (Ideal.Quotient.mk Q (v j))=algebraMap B A₂ (j₂ (z14 Λ j)):=by
        rw [← hf₂_var j,q11]
       rw [h2,← q6];rfl
      rw [q40];exact q10 _ (z17 r' (z18 j))
    refine z32 (barΨ.comp β) (q41.comp (algebraMap B M))
     (fun c=>RingHom.congr_fun q20 c) ?_ ?_
    ·
     intro i;simp only [RingHom.comp_apply,hβ_var];change barΨ (Ideal.Quotient.mk I (i₁ (u i)))=q41 (algebraMap B M (z14 B₂ i));rw [hbarΨ_mk];change (Ψ.comp i₁) (u i)=q41 (algebraMap B M (z14 B₂ i));rw [hΨ_i₁];dsimp only [φ₁];simp only [RingHom.comp_apply]
     have h1:toA₁ (Ideal.Quotient.mk P (u i))=algebraMap B A₁ (z14 B₂ i):=by
      rw [← hf₁_var i,← z20 (z13 Λ s') i];exact q8 (z14 Λ i)
     rw [h1];rfl
    ·
     intro i
     refine ⟨t,?_⟩
     have q40:(barΨ.comp β) (z14 B₂ i)=q41 (algebraMap B M (z14 B₂ i)):=by
      simp only [RingHom.comp_apply,hβ_var];change barΨ (Ideal.Quotient.mk I (i₁ (u i)))=q41 (algebraMap B M (z14 B₂ i));rw [hbarΨ_mk];change (Ψ.comp i₁) (u i)=q41 (algebraMap B M (z14 B₂ i));rw [hΨ_i₁];dsimp only [φ₁];simp only [RingHom.comp_apply]
      have h1:toA₁ (Ideal.Quotient.mk P (u i))=algebraMap B A₁ (z14 B₂ i):=by
       rw [← hf₁_var i,← z20 (z13 Λ s') i];exact q8 (z14 Λ i)
      rw [h1];rfl
     rw [q40];exact q10 _ (z18 i)
   have h0:q41 (algebraMap B M b)=0:=by
    have:=RingHom.congr_fun hbarΨ_β b;simp only [RingHom.comp_apply,hb,map_zero] at this;exact this.symm
   rw [Ideal.Quotient.eq_zero_iff_mem] at h0
   have q22:(Jt:Set M)⊆(((maximalIdeal B ^ t•(⊤ : Submodule B M)) : Submodule B M) : Set M):=by
    intro m hm
    have hle:(Jt.restrictScalars B) ≤ maximalIdeal B ^ t•(⊤ : Submodule B M):=by
     intro x hx;have hx':x∈span (algebraMap B M '' ((maximalIdeal B ^ t:Ideal B) : Set B)):=hx
     refine Submodule.span_induction ?_ (Submodule.zero_mem _) (fun _ _ _ _=>Submodule.add_mem _)
      (fun r y _ hy => ?_) hx'
     ·
      rintro _ ⟨a,ha,rfl⟩
      have : algebraMap B M a=a•(1:M):=by rw [Algebra.smul_def,mul_one]
      rw [this];exact Submodule.smul_mem_smul ha Submodule.mem_top
     ·
      refine Submodule.smul_induction_on hy ?_ ?_
      ·
       intro a ha z _
       have : r•(a•z)=a•(r*z):=by
        simp only [smul_eq_mul,Algebra.smul_def];ring
       rw [this];exact Submodule.smul_mem_smul ha Submodule.mem_top
      ·
       intro u v hu hv;rw [smul_add];exact Submodule.add_mem _ hu hv
    exact hle hm
   exact q22 h0
  have q38:=Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R:=B) (M:=M)
   (maximalIdeal B) (maximalIdeal.isMaximal B).ne_top
  rw [q38] at q7;have hbM:algebraMap B M b=0:=q7;let K:=FractionRing B;have q27:Injective (algebraMap B K):=IsFractionRing.injective B K
  have hKA₁_nt:Nontrivial (K ⊗[B] A₁):=by
   let e1:K ⊗[B] A₁ ≃ₗ[K] K ⊗[B₁] (R⧸P):=TensorProduct.AlgebraTensorModule.cancelBaseChange B₁ B K K (R⧸P)
   refine e1.toEquiv.nontrivial_congr.mpr ?_
   exact z42 hf₁_inj (q27.comp hj₁_inj)
  have hKA₂_nt:Nontrivial (K ⊗[B] A₂):=by
   let e2:K ⊗[B] A₂ ≃ₗ[K] K ⊗[B₂] (R⧸Q):=TensorProduct.AlgebraTensorModule.cancelBaseChange B₂ B K K (R⧸Q)
   refine e2.toEquiv.nontrivial_congr.mpr ?_
   exact z42 hf₂_inj (q27.comp hj₂_inj)
  have q26:Nontrivial (K ⊗[B] M):=by
   let eM:K ⊗[B] M ≃ₗ[K] (K ⊗[B] A₁) ⊗[K] (K ⊗[B] A₂):=TensorProduct.AlgebraTensorModule.distribBaseChange B K A₁ A₂
   exact eM.toEquiv.nontrivial_congr.mpr
    (z41 K (K ⊗[B] A₁) (K ⊗[B] A₂))
  by_contra hb0
  have q23:algebraMap B K b≠0:=fun h=>hb0 (q27 (by simpa using h))
  have h10:(1:K ⊗[B] M)=0:=by
   have q43:(algebraMap B K b)•(1:K ⊗[B] M)=0:=by
    change (algebraMap B K b)•((1:K) ⊗ₜ[B] (1:M))=0;rw [smul_tmul',smul_eq_mul,mul_one]
    have hbK:algebraMap B K b=b•(1:K):=by rw [Algebra.smul_def,mul_one]
    have hbM':b•(1:M)=0:=by rw [Algebra.smul_def,mul_one,hbM]
    rw [hbK,smul_tmul,hbM',tmul_zero]
   have q36:=congrArg (fun x=>(algebraMap B K b)⁻¹ • x) q43
   simp only [smul_smul,smul_zero,inv_mul_cancel₀ q23,one_smul] at q36;exact q36
  have : Subsingleton (K ⊗[B] M):=subsingleton_of_zero_eq_one h10.symm;exact not_subsingleton (K ⊗[B] M) this
 have : Algebra.IsIntegral B A:=Algebra.IsIntegral.of_finite B A;have q15:ringKrullDim A=ringKrullDim B:=z37 hβ_inj;rw [q15,z11 B₂ r',z11 Λ s']
lemma z45 {C R:Type} [CommRing C] [IsLocalRing C]
  [CommRing R] [IsLocalRing R] [IsHausdorff (maximalIdeal R) R] :
  ∀ {n : ℕ} (g₁ g₂ : z0 C n →+* R),(∀ c:C,g₁ (z13 C n c)=g₂ (z13 C n c))→(∀ i:Fin n,g₁ (z14 C i)=g₂ (z14 C i))→(∀ i:Fin n,g₁ (z14 C i)∈maximalIdeal R) → g₁ = g₂ := by
 intro n g₁ g₂ hC hvar hmem;ext x
 refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (g₁ x - g₂ x) fun t => ?_)
 rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,sub_eq_zero];let mk:R →+* R⧸maximalIdeal R ^ t:=Ideal.Quotient.mk _
 have heq:mk.comp g₁ = mk.comp g₂ := by
  refine z32 (mk.comp g₁) (mk.comp g₂)
   (fun c=>by simp [hC c])
   (fun i=>by simp [hvar i])
   (fun i=>⟨t,?_⟩)
  rw [RingHom.comp_apply,← map_pow,Ideal.Quotient.eq_zero_iff_mem];exact Ideal.pow_mem_pow (hmem i) t
 exact RingHom.congr_fun heq x
lemma z46 (D:Type) [CommRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D] (c:D) (hc:c∈maximalIdeal D) :
  ∃ e:PowerSeries D ≃+* PowerSeries D,(∀ d:D,e (PowerSeries.C d)=PowerSeries.C d)∧e PowerSeries.X=PowerSeries.X+PowerSeries.C c∧(∀ d:D,e.symm (PowerSeries.C d)=PowerSeries.C d)∧e.symm PowerSeries.X=PowerSeries.X - PowerSeries.C c:=by
 have q0:∀ d∈maximalIdeal D,(PowerSeries.C d:PowerSeries D)∈maximalIdeal (PowerSeries D):=by
  intro d hd;rw [z3,PowerSeries.constantCoeff_C];exact hd
 have hXc:(PowerSeries.X:PowerSeries D)+PowerSeries.C c∈maximalIdeal (PowerSeries D):=(maximalIdeal (PowerSeries D)).add_mem z4 (q0 c hc);have q1:(PowerSeries.X:PowerSeries D) - PowerSeries.C c∈maximalIdeal (PowerSeries D):=(maximalIdeal (PowerSeries D)).sub_mem z4 (q0 c hc);have : IsAdicComplete (maximalIdeal (PowerSeries D)) (PowerSeries D):=z9
 obtain ⟨φ,hφ_C,hφ_X,_⟩:=z12 PowerSeries.C q0 hXc;obtain ⟨ψ,hψ_C,hψ_X,_⟩:=z12 PowerSeries.C q0 q1
 have hψφ : ψ.comp φ = RingHom.id (PowerSeries D):=by
  refine z45 (C:=D) (n:=1) (ψ.comp φ) (RingHom.id _)
   (fun d=>by
    change ψ (φ (PowerSeries.C d))=PowerSeries.C d
    rw [hφ_C,hψ_C])
   (fun i=>by
    have hi:i=Fin.last 0:=Subsingleton.elim _ _;subst hi;change ψ (φ PowerSeries.X)=PowerSeries.X;rw [hφ_X,map_add,hψ_X,hψ_C]
    ring)
   (fun i=>by
    have hi:i=Fin.last 0:=Subsingleton.elim _ _;subst hi;change ψ (φ PowerSeries.X)∈maximalIdeal (PowerSeries D);rw [hφ_X,map_add,hψ_X,hψ_C]
    have : PowerSeries.X - PowerSeries.C c+PowerSeries.C c=(PowerSeries.X:PowerSeries D):=by
     ring
    rw [this]
    exact z4)
 have hφψ : φ.comp ψ = RingHom.id (PowerSeries D):=by
  refine z45 (C:=D) (n:=1) (φ.comp ψ) (RingHom.id _)
   (fun d=>by
    change φ (ψ (PowerSeries.C d))=PowerSeries.C d
    rw [hψ_C,hφ_C])
   (fun i=>by
    have hi:i=Fin.last 0:=Subsingleton.elim _ _;subst hi;change φ (ψ PowerSeries.X)=PowerSeries.X;rw [hψ_X,map_sub,hφ_X,hφ_C]
    ring)
   (fun i=>by
    have hi:i=Fin.last 0:=Subsingleton.elim _ _;subst hi;change φ (ψ PowerSeries.X)∈maximalIdeal (PowerSeries D);rw [hψ_X,map_sub,hφ_X,hφ_C]
    have : PowerSeries.X+PowerSeries.C c - PowerSeries.C c=(PowerSeries.X:PowerSeries D):=by
     ring
    rw [this]
    exact z4)
 let e:PowerSeries D ≃+* PowerSeries D :=
  {
   toFun := φ
   invFun := ψ
   left_inv:=RingHom.congr_fun hψφ
   right_inv:=RingHom.congr_fun hφψ
   map_mul' := φ.map_mul
   map_add' := φ.map_add }
 exact ⟨e,hφ_C,hφ_X,hψ_C,hψ_X⟩
lemma z47 (D:Type) [CommRing D] [IsLocalRing D]
  [IsAdicComplete (maximalIdeal D) D] :
  ∀ (n : ℕ) (cs:Fin n→D),(∀ i,cs i∈maximalIdeal D) →
   ∃ e:z0 D n ≃+* z0 D n,(∀ d:D,e (z13 D n d)=z13 D n d)∧(∀ i:Fin n,e (z14 D i)=z14 D i+z13 D n (cs i))∧(∀ d:D,e.symm (z13 D n d)=z13 D n d)∧(∀ i:Fin n,e.symm (z14 D i)=z14 D i - z13 D n (cs i)):=by
 intro n
 induction n with
 | zero =>
  intro cs _
  exact ⟨RingEquiv.refl D,fun _=>rfl,fun i=>Fin.elim0 i,fun _=>rfl,fun i=>Fin.elim0 i⟩
 | succ n ih =>
  intro cs hcs
  obtain ⟨e0,he0_C,he0_var,he0_symm_C,he0_symm_var⟩:=ih (fun j=>cs j.castSucc) (fun j=>hcs j.castSucc)
  let q2:PowerSeries (z0 D n) ≃+* PowerSeries (z0 D n) :=
   {
    toFun:=PowerSeries.map e0.toRingHom
    invFun:=PowerSeries.map e0.symm.toRingHom
    left_inv:=fun f=>by ext k;simp [PowerSeries.coeff_map]
    right_inv:=fun f=>by ext k;simp [PowerSeries.coeff_map]
    map_mul':=(PowerSeries.map e0.toRingHom).map_mul
    map_add':=(PowerSeries.map e0.toRingHom).map_add }
  have q1:∀ f,q2 f=PowerSeries.map e0.toRingHom f:=fun _=>rfl
  have q0:∀ f,q2.symm f=PowerSeries.map e0.symm.toRingHom f:=fun _=>rfl
  obtain ⟨eShift,heS_C,heS_X,heS_symm_C,heS_symm_X⟩ :=
   z46 (z0 D n) (z13 D n (cs (Fin.last n)))
    (z17 n (hcs (Fin.last n)))
  let e:z0 D (n+1) ≃+* z0 D (n+1):=q2.trans eShift
  refine ⟨e,?_,?_,?_,?_⟩
  ·
   intro d;simp only [e,z13,RingEquiv.trans_apply,RingHom.comp_apply,q1,PowerSeries.map_C];change eShift (PowerSeries.C (e0 (z13 D n d)))=PowerSeries.C (z13 D n d);rw [he0_C,heS_C]
  ·
   intro i
   refine Fin.lastCases ?_ ?_ i
   · simp only [e,z14,z13,Fin.lastCases_last,RingEquiv.trans_apply,RingHom.comp_apply,q1,PowerSeries.map_X,heS_X]
   ·
    intro j;simp only [e,z14,z13,Fin.lastCases_castSucc,RingEquiv.trans_apply,RingHom.comp_apply,q1,PowerSeries.map_C];change eShift (PowerSeries.C (e0 (z14 D j)))=PowerSeries.C (z14 D j)+PowerSeries.C (z13 D n (cs j.castSucc));rw [he0_var,heS_C,map_add]
  ·
   intro d;simp only [e,z13,RingEquiv.symm_trans_apply,RingHom.comp_apply,heS_symm_C,q0,PowerSeries.map_C];change PowerSeries.C (e0.symm (z13 D n d))=PowerSeries.C (z13 D n d);rw [he0_symm_C]
  ·
   intro i
   refine Fin.lastCases ?_ ?_ i
   ·
    simp only [e,z14,z13,Fin.lastCases_last,RingEquiv.symm_trans_apply,RingHom.comp_apply,heS_symm_X,map_sub,q0,PowerSeries.map_X,PowerSeries.map_C];change PowerSeries.X - PowerSeries.C (e0.symm (z13 D n (cs (Fin.last n))))=PowerSeries.X - PowerSeries.C (z13 D n (cs (Fin.last n)));rw [he0_symm_C]
   ·
    intro j;simp only [e,z14,z13,Fin.lastCases_castSucc,RingEquiv.symm_trans_apply,RingHom.comp_apply,heS_symm_C,q0,PowerSeries.map_C];change PowerSeries.C (e0.symm (z14 D j))=PowerSeries.C (z14 D j) - PowerSeries.C (z13 D n (cs j.castSucc));rw [he0_symm_var,map_sub]
noncomputable def z48 (D:Type) [CommRing D] :
  ∀ n : ℕ,z0 D n →+* D
 | 0=>RingHom.id D
 | n+1=>(z48 D n).comp PowerSeries.constantCoeff
lemma z49 (D:Type) [CommRing D] :
  ∀ (n : ℕ) (d:D),z48 D n (z13 D n d)=d
 | 0,_=>rfl
 | n+1,d=>by
  change z48 D n (PowerSeries.constantCoeff (PowerSeries.C (z13 D n d)))=d;rw [PowerSeries.constantCoeff_C,z49 D n d]
lemma z50 (D:Type) [CommRing D] :
  ∀ {n : ℕ} (i:Fin n),z48 D n (z14 D i)=0
 | 0,i=>Fin.elim0 i
 | n+1,i=>by
  refine Fin.lastCases ?_ ?_ i
  · simp only [z48,z14,Fin.lastCases_last,RingHom.comp_apply,PowerSeries.constantCoeff_X,map_zero]
  ·
   intro j;simp only [z48,z14,Fin.lastCases_castSucc,RingHom.comp_apply,PowerSeries.constantCoeff_C,z50 D j]
lemma z51 (D:Type) [CommRing D] :
  ∀ n : ℕ,RingHom.ker (z48 D n)=span (Set.range (z14 D (n:=n)))
 | 0=>by
  ext x;simp [z48,RingHom.mem_ker,Set.range_eq_empty]
 | n+1=>by
  refine le_antisymm ?_ ?_
  ·
   intro f hf;rw [RingHom.mem_ker] at hf;have hf0:PowerSeries.constantCoeff f∈RingHom.ker (z48 D n):=hf;rw [z51 D n] at hf0
   have q0:PowerSeries.C (PowerSeries.constantCoeff f) ∈
     span (Set.range (z14 D (n:=n+1))):=by
    have h1:=mem_map_of_mem PowerSeries.C hf0
    have hle:(span (Set.range (z14 D (n:=n)))).map PowerSeries.C ≤ span (Set.range (z14 D (n:=n+1))):=by
     rw [map_span,span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;exact subset_span ⟨j.castSucc,by simp [z14]⟩
    exact hle h1
   have q2:f - PowerSeries.C (PowerSeries.constantCoeff f) ∈
     span {(PowerSeries.X:PowerSeries (z0 D n))}:=by
    have h1:=z6 1
     (f - PowerSeries.C (PowerSeries.constantCoeff f)) (fun i hi=>by
      have hi0:i=0:=by omega
      subst hi0;simp)
    simpa using h1
   have q1:span {(PowerSeries.X:PowerSeries (z0 D n))} ≤ span (Set.range (z14 D (n:=n+1))):=(span_singleton_le_iff_mem _).mpr (subset_span ⟨Fin.last n,by simp [z14]⟩);have q3:=Ideal.add_mem _ q0 (q1 q2);simpa using q3
  ·
   rw [span_le];rintro _ ⟨i,rfl⟩;rw [SetLike.mem_coe,RingHom.mem_ker];exact z50 D i
lemma z52 {Λ : Type} [CommRing Λ] [IsLocalRing Λ]
  [IsAdicComplete (maximalIdeal Λ) Λ] (n : ℕ) :
  let R:=z0 Λ n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 Λ n) n;let i₂ : R →+* T:=z13 R n
  let Δ : Ideal T:=span (Set.range (fun k:Fin n=>z14 R k - i₂ (z14 Λ k)))
  ∃ μ : T →+* R,μ.comp i₁ = RingHom.id R ∧ μ.comp i₂ = RingHom.id R∧Surjective μ ∧ RingHom.ker μ = Δ := by
 intro R T i₁ i₂ Δ
 obtain ⟨eShift,heS_C,heS_var,heS_symm_C,heS_symm_var⟩:=z47 R n (z14 Λ) (fun k=>z18 k)
 let μ : T →+* R:=(z48 R n).comp eShift.toRingHom
 have hμ_i₂ : μ.comp i₂ = RingHom.id R:=by
  ext r;simp only [μ,i₂,RingHom.comp_apply,RingHom.id_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,heS_C,z49]
 have hμ_var:∀ k:Fin n,μ (z14 R k)=z14 Λ k:=fun k=>by
  simp only [μ,RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,heS_var,map_add,z50,z49,zero_add]
 have hμ_i₁ : μ.comp i₁ = RingHom.id R:=by
  refine z45 (C := Λ) (R:=R) (μ.comp i₁) (RingHom.id R) ?_ ?_ ?_
  ·
   intro c;rw [RingHom.comp_apply,RingHom.id_apply,z19 (z13 Λ n) n c];exact RingHom.congr_fun hμ_i₂ (z13 Λ n c)
  ·
   intro k;rw [RingHom.comp_apply,RingHom.id_apply,z20 (z13 Λ n) k];exact hμ_var k
  ·
   intro k;rw [RingHom.comp_apply,z20 (z13 Λ n) k,hμ_var k];exact z18 k
 have hμ_surj:Surjective μ := fun r=>⟨i₂ r,RingHom.congr_fun hμ_i₂ r⟩
 have hμ_ker:RingHom.ker μ = Δ := by
  refine le_antisymm ?_ ?_
  ·
   intro t ht;rw [RingHom.mem_ker] at ht;have h1:eShift t∈RingHom.ker (z48 R n):=ht;rw [z51 R n] at h1
   have h2:eShift.symm (eShift t) ∈
     (span (Set.range (z14 R (n:=n)))).map eShift.symm.toRingHom :=
    mem_map_of_mem eShift.symm.toRingHom h1
   rw [eShift.symm_apply_apply,map_span] at h2
   refine (span_le.mpr ?_) h2
   rintro _ ⟨_,⟨k,rfl⟩,rfl⟩;simp only [RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,heS_symm_var];exact subset_span ⟨k,rfl⟩
  ·
   rw [span_le];rintro _ ⟨k,rfl⟩;rw [SetLike.mem_coe,RingHom.mem_ker,map_sub,hμ_var k];have h2 : μ (i₂ (z14 Λ k))=z14 Λ k:=RingHom.congr_fun hμ_i₂ (z14 Λ k);rw [h2,sub_self]
 exact ⟨μ,hμ_i₁,hμ_i₂,hμ_surj,hμ_ker⟩
lemma z53 {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (maximalIdeal Λ) Λ]
    (n : ℕ) (P Q:Ideal (z0 Λ n)) [P.IsPrime] [Q.IsPrime]
    (hPQ:(P⊔Q).radical=maximalIdeal (z0 Λ n)) :
    let R:=z0 Λ n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 Λ n) n;let i₂ : R →+* T:=z13 R n
    ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)) ≤ (n:WithBot ℕ∞):=by
  intro R T i₁ i₂;let I:Ideal T:=P.map i₁ ⊔ Q.map i₂
  have q3:I ≤ maximalIdeal T:=by
    refine sup_le ?_ ?_
    · rw [map_le_iff_le_comap]
      intro x hx
      exact z23 (fun c hc=>z17 n hc) n
        (le_maximalIdeal ‹P.IsPrime›.ne_top hx)
    · rw [map_le_iff_le_comap]
      intro x hx;exact z17 n (le_maximalIdeal ‹Q.IsPrime›.ne_top hx)
  have q2:I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal T).ne_top q3;let A:=T⧸I;have : Nontrivial A:=Ideal.Quotient.nontrivial_iff.mpr q2;have : IsLocalRing A:=z36 I;obtain ⟨μ,hμ_i₁,hμ_i₂,hμ_surj,hμ_ker⟩:=z52 (Λ := Λ) n
  let Δ : Ideal T:=span (Set.range (fun k:Fin n=>z14 R k - i₂ (z14 Λ k)))
  let g:T →+* R⧸(P⊔Q):=(Ideal.Quotient.mk (P⊔Q)).comp μ;have q9:Surjective g:=Ideal.Quotient.mk_surjective.comp hμ_surj
  have q14:RingHom.ker g=I ⊔ Δ := by
    refine le_antisymm ?_ ?_
    · intro t ht
      rw [RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem] at ht;obtain ⟨p,hp,q,hq,hpq⟩:=Submodule.mem_sup.mp ht
      have q19:t - (i₁ p+i₂ q)∈RingHom.ker μ := by
        rw [RingHom.mem_ker,map_sub,map_add];have hp' : μ (i₁ p)=p:=RingHom.congr_fun hμ_i₁ p;have hq' : μ (i₂ q)=q:=RingHom.congr_fun hμ_i₂ q;rw [hp',hq',hpq,sub_self]
      rw [hμ_ker] at q19
      have q12:i₁ p+i₂ q∈I :=
        Ideal.add_mem _ (mem_sup_left (mem_map_of_mem i₁ hp))
          (mem_sup_right (mem_map_of_mem i₂ hq))
      have q22:=Ideal.add_mem _ (mem_sup_left q12) (mem_sup_right q19);simpa using q22
    · refine sup_le (sup_le ?_ ?_) ?_
      · rw [map_le_iff_le_comap]
        intro p hp;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply];have hp' : μ (i₁ p)=p:=RingHom.congr_fun hμ_i₁ p;rw [hp',Ideal.Quotient.eq_zero_iff_mem];exact mem_sup_left hp
      · rw [map_le_iff_le_comap]
        intro q hq;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply];have hq' : μ (i₂ q)=q:=RingHom.congr_fun hμ_i₂ q;rw [hq',Ideal.Quotient.eq_zero_iff_mem];exact mem_sup_right hq
      · have hΔ_eq : Δ = RingHom.ker μ := hμ_ker.symm
        rw [hΔ_eq];intro t ht;rw [RingHom.mem_ker,RingHom.comp_apply,RingHom.mem_ker.mp ht,map_zero]
  classical
  let S:Finset A:=Finset.univ.image (fun k:Fin n =>
    Ideal.Quotient.mk I (z14 R k - i₂ (z14 Λ k)))
  have q13:(S:Set A)⊆Ring.jacobson A:=by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal];intro a ha;rw [Finset.mem_coe,Finset.mem_image] at ha;obtain ⟨k,_,rfl⟩:=ha;have q0:(maximalIdeal A).comap (Ideal.Quotient.mk I)=maximalIdeal T:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);rw [SetLike.mem_coe,← mem_comap,q0]
    exact (maximalIdeal T).sub_mem (z18 k)
      (z17 n (z18 k))
  have q10:span (S:Set A) = Δ.map (Ideal.Quotient.mk I):=by
    rw [map_span];congr 1;ext a;simp [S]
  have q20:S.card ≤ n:=by
    calc S.card ≤ (Finset.univ:Finset (Fin n)).card:=Finset.card_image_le
      _=n:=Fintype.card_fin n
  have q1:(A⧸span (S:Set A)) ≃+* (R⧸(P⊔Q)):=by
    have q15:∀ a∈I,g a=0:=fun a ha =>
      RingHom.mem_ker.mp ((q14▸le_sup_left:I ≤ RingHom.ker g) ha)
    let gA:A →+* R⧸(P⊔Q):=Ideal.Quotient.lift I g q15
    have q6:Surjective gA:=fun y=>by
      obtain ⟨t,rfl⟩:=q9 y;exact ⟨Ideal.Quotient.mk I t,rfl⟩
    have q8:RingHom.ker gA=span (S:Set A):=by
      rw [q10];ext a;obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;rw [RingHom.mem_ker];dsimp only [gA];rw [Ideal.Quotient.lift_mk,← RingHom.mem_ker,q14,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective];constructor
      · intro ht
        obtain ⟨u,hu,v,hv,huv⟩:=Submodule.mem_sup.mp ht
        refine ⟨v,hv,?_⟩
        symm
        rw [← sub_eq_zero,← map_sub,Ideal.Quotient.eq_zero_iff_mem]
        have : t - v=u:=by rw [← huv];ring
        rw [this];exact hu
      · rintro ⟨v,hv,hvt⟩
        have q21:t - v∈I:=by
          rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,hvt,sub_self]
        have q22:=Ideal.add_mem _ (mem_sup_left q21) (mem_sup_right hv);simpa using q22
    exact (Ideal.quotEquivOfEq q8.symm).trans (RingHom.quotientKerEquivOfSurjective q6)
  have q7:ringKrullDim (R⧸(P⊔Q))=0:=by
    have q11:P⊔Q ≠ ⊤ := by
      intro q23
      have h1:(P⊔Q).radical = ⊤ := by rw [q23,Ideal.radical_top]
      rw [hPQ] at h1;exact (maximalIdeal.isMaximal R).ne_top h1
    have : Nontrivial (R⧸(P⊔Q)):=Ideal.Quotient.nontrivial_iff.mpr q11
    have q24:ringKrullDim (R⧸(P⊔Q)) ≤ 0:=by
      rw [ringKrullDim_quotient,Order.krullDim]
      refine iSup_le fun c => ?_
      by_cases hlen:c.length=0
      · simp [hlen]
      · exfalso
        have q17:(c 0).1.asIdeal < (c ⟨1,by omega⟩).1.asIdeal:=c.strictMono (by simp [Fin.lt_def]);have q4:(c 0).1.asIdeal ≤ maximalIdeal R:=le_maximalIdeal (c 0).1.isPrime.ne_top
        have q5:maximalIdeal R ≤ (c 0).1.asIdeal:=by
          rw [← hPQ,← (c 0).1.isPrime.radical];exact Ideal.radical_mono (c 0).2
        have q18:(c 0).1.asIdeal=maximalIdeal R:=le_antisymm q4 q5;have q16:(c ⟨1,by omega⟩).1.asIdeal ≤ maximalIdeal R:=le_maximalIdeal (c ⟨1,by omega⟩).1.isPrime.ne_top;rw [q18] at q17;exact not_lt_of_ge q16 q17
    exact le_antisymm q24 (ringKrullDim_nonneg_of_nontrivial (R:=R⧸(P⊔Q)))
  have hle:=ringKrullDim_le_ringKrullDim_quotient_add_card S q13;rw [ringKrullDim_eq_of_ringEquiv q1,q7,zero_add] at hle;exact hle.trans (Nat.cast_le.mpr q20)
lemma z54 {k:Type} [Field k] (n : ℕ)
  (P Q:Ideal (z0 k n)) [P.IsPrime] [Q.IsPrime]
  (hPQ:(P⊔Q).radical=maximalIdeal (z0 k n)) :
  let R:=z0 k n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 k n) n;let i₂ : R →+* T:=z13 R n
  ringKrullDim (R⧸P)+ringKrullDim (R⧸Q) ≤ ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)) ∧
  ringKrullDim (R⧸P)+ringKrullDim (R⧸Q) ≤ ringKrullDim R:=by
 intro R T i₁ i₂;have : IsLocalRing (R⧸P):=z36 P;have : IsLocalRing (R⧸Q):=z36 Q
 obtain ⟨r,hr⟩ :=
  ringKrullDim_quotient_eq_natCast
   P ‹P.IsPrime›.ne_top
 obtain ⟨s,hs⟩ :=
  ringKrullDim_quotient_eq_natCast
   Q ‹Q.IsPrime›.ne_top
 obtain ⟨u',hu'_mem,hu'_rad⟩:=z39 r (R⧸P) hr;obtain ⟨v',hv'_mem,hv'_rad⟩:=z39 s (R⧸Q) hs
 let u:Fin r→R:=fun i=>(Ideal.Quotient.mk_surjective (u' i)).choose
 have q18:∀ i,Ideal.Quotient.mk P (u i)=u' i:=fun i=>(Ideal.Quotient.mk_surjective (u' i)).choose_spec
 let v:Fin s→R:=fun j=>(Ideal.Quotient.mk_surjective (v' j)).choose
 have q17:∀ j,Ideal.Quotient.mk Q (v j)=v' j:=fun j=>(Ideal.Quotient.mk_surjective (v' j)).choose_spec
 have q0:(maximalIdeal (R⧸P)).comap (Ideal.Quotient.mk P)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);have q1:(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
 have q13:∀ i,u i∈maximalIdeal R:=fun i=>by
  rw [← q0,mem_comap,q18 i];exact hu'_mem i
 have q8:∀ j,v j∈maximalIdeal R:=fun j=>by
  rw [← q1,mem_comap,q17 j];exact hv'_mem j
 have q2:∀ {J:Ideal R} [J.IsPrime] {m : ℕ} (w:Fin m→R) (w':Fin m→R⧸J)
   (_:IsLocalRing (R⧸J)),
   (∀ i,Ideal.Quotient.mk J (w i)=w' i) →
   (∀ i,w i∈maximalIdeal R) →
   (span (Set.range w')).radical=maximalIdeal (R⧸J) →
   ((maximalIdeal k).map (z13 k n)⊔span (Set.range w)⊔J).radical=maximalIdeal R:=by
  intro J _ m w w' _ hw_eq hw_mem hw'_rad;have q15:(maximalIdeal (R⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  refine le_antisymm ?_ ?_
  ·
   rw [← (maximalIdeal.isMaximal R).isPrime.radical]
   refine Ideal.radical_mono (sup_le (sup_le ?_ ?_) (le_maximalIdeal ‹J.IsPrime›.ne_top))
   · rw [map_le_iff_le_comap];intro c hc;exact z17 n hc
   · rw [span_le];rintro _ ⟨i,rfl⟩;exact hw_mem i
  ·
   intro x hx
   have hx':Ideal.Quotient.mk J x∈(span (Set.range w')).radical:=by
    rw [hw'_rad,← mem_comap,q15];exact hx
   obtain ⟨t,ht⟩:=hx';rw [← map_pow] at ht
   have q23:span (Set.range w')=(span (Set.range w)).map (Ideal.Quotient.mk J):=by
    rw [map_span];congr 1;ext y;simp [hw_eq]
   rw [q23,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at ht;obtain ⟨y,hy_span,hy_eq⟩:=ht
   have q20:x ^ t - y∈J:=by
    rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,hy_eq,sub_self]
   refine ⟨t,?_⟩
   have q21:y+(x ^ t - y)∈(maximalIdeal k).map (z13 k n)⊔span (Set.range w)⊔J :=
    Ideal.add_mem _ (mem_sup_left (mem_sup_right hy_span))
     (mem_sup_right q20)
   simpa using q21
 have q9:=q2 u u' inferInstance q18 q13 hu'_rad;have q11:=q2 v v' inferInstance q17 q8 hv'_rad
 have q4:∀ {J:Ideal R} [J.IsPrime] {m : ℕ} (w:Fin m→R)
   (_:IsLocalRing (R⧸J)),
   ringKrullDim (R⧸J)=(m:WithBot ℕ∞) →
   ((maximalIdeal k).map (z13 k n)⊔span (Set.range w)⊔J).radical=maximalIdeal R →
   ∀ f:z0 k m →+* R⧸J,(∀ c,f (z13 k m c)=Ideal.Quotient.mk J (z13 k n c))→(∀ i,f (z14 k i)=Ideal.Quotient.mk J (w i))→Injective f:=by
  intro J _ m w _ hdimJ hw_rad f hfC hfvar;have q15:(maximalIdeal (R⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
  have q14:∀ x∈maximalIdeal (z0 k m),f x∈maximalIdeal (R⧸J):=by
   intro x hx;have q6:(maximalIdeal (R⧸J)).comap f ≠ ⊤ := (Ideal.comap_isPrime f (maximalIdeal (R⧸J))).ne_top;have hle:(maximalIdeal (R⧸J)).comap f ≤ maximalIdeal (z0 k m):=le_maximalIdeal q6;rw [z34 m] at hx
   have q16:(maximalIdeal k).map (z13 k m)⊔span (Set.range (z14 k (n:=m))) ≤ (maximalIdeal (R⧸J)).comap f:=by
    refine sup_le ?_ ?_
    ·
     rw [map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,hfC,← mem_comap,q15];exact z17 n hc
    ·
     rw [span_le];rintro _ ⟨i,rfl⟩;rw [SetLike.mem_coe,mem_comap,hfvar]
     have hwi:w i∈maximalIdeal R:=by
      rw [← hw_rad];exact Ideal.le_radical (mem_sup_left (mem_sup_right (subset_span ⟨i,rfl⟩)))
     rw [← mem_comap,q15];exact hwi
   exact q16 hx
  have q12:Surjective ((residue (R⧸J)).comp f):=by
   intro y;obtain ⟨r,rfl⟩:=residue_surjective y;obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective r;obtain ⟨c,hc⟩:=z35 n (residue R x)
   refine ⟨z13 k m c,?_⟩
   rw [RingHom.comp_apply,hfC]
   symm
   rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,← map_sub,← mem_comap,q15,← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 k n)) c=0;rw [hc,sub_self]
  have q10:((maximalIdeal (z0 k m)).map f).radical=maximalIdeal (R⧸J):=by
   refine le_antisymm ?_ ?_
   ·
    rw [← (maximalIdeal.isMaximal (R⧸J)).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr q14)
   ·
    intro x hx;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective x;have hy:y∈maximalIdeal R:=q15▸hx;rw [← hw_rad] at hy;obtain ⟨t,ht⟩:=hy
    refine ⟨t,?_⟩
    rw [← map_pow]
    have hle:((maximalIdeal k).map (z13 k n)⊔span (Set.range w)⊔J).map
      (Ideal.Quotient.mk J) ≤ (maximalIdeal (z0 k m)).map f:=by
     rw [Ideal.map_sup,Ideal.map_sup]
     refine sup_le (sup_le ?_ ?_) ?_
     ·
      rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,← hfC c];exact mem_map_of_mem f (z17 m hc)
     ·
      rw [map_span,span_le];rintro _ ⟨_,⟨i,rfl⟩,rfl⟩;rw [← hfvar i];exact mem_map_of_mem f (z18 i)
     ·
      rw [map_le_iff_le_comap];intro a ha;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr ha];exact Ideal.zero_mem _
    exact hle (mem_map_of_mem (Ideal.Quotient.mk J) ht)
  let _:Algebra (z0 k m) (R⧸J):=f.toAlgebra;have : Module.Finite (z0 k m) (R⧸J):=z40 q14 q12 q10;rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker_ne
  have q5:RingHom.ker f ≠ ⊤ := by
   intro q22;have h1:(1:z0 k m)∈RingHom.ker f:=q22▸Submodule.mem_top;rw [RingHom.mem_ker,map_one] at h1;exact one_ne_zero h1
  let q24:(z0 k m⧸RingHom.ker f) →+* R⧸J:=Ideal.Quotient.lift (RingHom.ker f) f (fun _ h=>h)
  have q3:Injective q24:=RingHom.kerLift_injective f;let _:Algebra (z0 k m⧸RingHom.ker f) (R⧸J):=q24.toAlgebra
  have : Module.Finite (z0 k m⧸RingHom.ker f) (R⧸J):=by
   obtain ⟨S,hS⟩:=Module.Finite.fg_top (R:=z0 k m) (M:=R⧸J)
   refine ⟨⟨S,eq_top_iff.mpr fun x _ => ?_⟩⟩
   have hx:x∈Submodule.span (z0 k m) (S:Set (R⧸J)):=hS▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hx ⊢;obtain ⟨c,hc,rfl⟩:=hx
   refine ⟨fun s=>Ideal.Quotient.mk (RingHom.ker f) (c s),fun s hs => ?_,?_⟩
   · exact hc (fun h0=>hs (by simp [h0]))
   ·
    refine Finset.sum_congr rfl fun s _ => ?_
    rfl
  have : Algebra.IsIntegral (z0 k m⧸RingHom.ker f) (R⧸J):=Algebra.IsIntegral.of_finite _ _;have q7:=z37 q3;have hlt:=z38 hker_ne q5;rw [← q7,hdimJ,z11 k m,ringKrullDim_eq_zero_of_field k,zero_add] at hlt;exact lt_irrefl _ hlt
 have hge:=z44 (Λ := k) n P Q r s u q13 v q8 q9 q11
  (q4 u inferInstance hr q9) (q4 v inferInstance hs q11)
 have hle:=z53 (Λ := k) n P Q hPQ;rw [ringKrullDim_eq_zero_of_field k,zero_add] at hge
 have hge':ringKrullDim (R⧸P)+ringKrullDim (R⧸Q) ≤
   ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
  rw [hr,hs,add_comm];exact hge
 have q19:ringKrullDim R=(n:WithBot ℕ∞):=by
  rw [z11 k n,ringKrullDim_eq_zero_of_field k,zero_add]
 exact ⟨hge',hge'.trans (hle.trans_eq q19.symm)⟩
lemma z55 {V:Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (maximalIdeal V) V] (p:V) (hp:maximalIdeal V=span {p})
  (n : ℕ) (P Q:Ideal (z0 V n)) [P.IsPrime] [Q.IsPrime]
  (hPQ:(P⊔Q).radical=maximalIdeal (z0 V n)) :
  let R:=z0 V n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 V n) n;let i₂ : R →+* T:=z13 R n
  ringKrullDim (R⧸P)+ringKrullDim (R⧸Q) ≤ ringKrullDim R ∧
  (ringKrullDim (R⧸P)+ringKrullDim (R⧸Q)=ringKrullDim R→(z13 V n p∉P∨z13 V n p∉Q) ∧
   ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂))=(n:WithBot ℕ∞)):=by
 intro R T i₁ i₂;have : IsLocalRing (R⧸P):=z36 P;have : IsLocalRing (R⧸Q):=z36 Q;have q51:ringKrullDim V=1:=IsDiscreteValuationRing.ringKrullDim_eq_one V
 have q52:ringKrullDim R=(n+1 : ℕ):=by
  rw [z11 V n,q51,add_comm];push_cast;rfl
 let k:=V⧸maximalIdeal V
 letI : Field k:=Ideal.Quotient.field (maximalIdeal V)
 let qR:R →+* z0 k n:=z15 (Ideal.Quotient.mk (maximalIdeal V)) n;have q9:Surjective qR:=z22 Ideal.Quotient.mk_surjective n
 have q20:RingHom.ker qR=span {z13 V n p}:=by
  rw [z26,hp,map_span,Set.image_singleton]
 have q48:=z53 (Λ := V) n P Q hPQ
 have q2:∀ (P' Q':Ideal R) [P'.IsPrime] [Q'.IsPrime],z13 V n p∈P'→z13 V n p∈Q'→(P'⊔Q').radical=maximalIdeal R →
   ringKrullDim (R⧸P')+ringKrullDim (R⧸Q') ≤
    ringKrullDim (T⧸(P'.map i₁ ⊔ Q'.map i₂)) ∧
   ringKrullDim (R⧸P')+ringKrullDim (R⧸Q') ≤ (n:WithBot ℕ∞):=by
  intro P' Q' _ _ hpP' hpQ' hP'Q'
  have hkerP':RingHom.ker qR ≤ P':=by
   rw [q20,span_singleton_le_iff_mem];exact hpP'
  have hkerQ':RingHom.ker qR ≤ Q':=by
   rw [q20,span_singleton_le_iff_mem];exact hpQ'
  let Pbar:Ideal (z0 k n):=P'.map qR;let Qbar:Ideal (z0 k n):=Q'.map qR;have : Pbar.IsPrime:=Ideal.map_isPrime_of_surjective q9 hkerP';have : Qbar.IsPrime:=Ideal.map_isPrime_of_surjective q9 hkerQ'
  have q11:(Pbar⊔Qbar).radical=maximalIdeal (z0 k n):=by
   refine le_antisymm ?_ ?_
   ·
    rw [← (maximalIdeal.isMaximal (z0 k n)).isPrime.radical]
    exact Ideal.radical_mono (sup_le (le_maximalIdeal ‹Pbar.IsPrime›.ne_top)
     (le_maximalIdeal ‹Qbar.IsPrime›.ne_top))
   ·
    intro y hy;obtain ⟨x,rfl⟩:=q9 y;have q3:(maximalIdeal (z0 k n)).comap qR=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective qR q9);have hx:x∈maximalIdeal R:=q3▸hy;rw [← hP'Q'] at hx;obtain ⟨m,hm⟩:=hx
    refine ⟨m,?_⟩
    rw [← map_pow,← Ideal.map_sup];exact mem_map_of_mem qR hm
  have hdimP':ringKrullDim (z0 k n⧸Pbar)=ringKrullDim (R⧸P'):=by
   let g:R →+* z0 k n⧸Pbar:=(Ideal.Quotient.mk Pbar).comp qR;have q22:Surjective g:=Ideal.Quotient.mk_surjective.comp q9
   have q41:RingHom.ker g=P':=by
    ext x;rw [RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem,mem_map_iff_of_surjective qR q9];constructor
    ·
     rintro ⟨y,hy,hyx⟩
     have q54:x - y∈RingHom.ker qR:=by rw [RingHom.mem_ker,map_sub,hyx,sub_self]
     have:=Ideal.add_mem _ hy (hkerP' q54);simpa using this
    · intro hx;exact ⟨x,hx,rfl⟩
   exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq q41.symm).trans (RingHom.quotientKerEquivOfSurjective q22))).symm
  have hdimQ':ringKrullDim (z0 k n⧸Qbar)=ringKrullDim (R⧸Q'):=by
   let g:R →+* z0 k n⧸Qbar:=(Ideal.Quotient.mk Qbar).comp qR;have q22:Surjective g:=Ideal.Quotient.mk_surjective.comp q9
   have q41:RingHom.ker g=Q':=by
    ext x;rw [RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem,mem_map_iff_of_surjective qR q9];constructor
    ·
     rintro ⟨y,hy,hyx⟩
     have q54:x - y∈RingHom.ker qR:=by rw [RingHom.mem_ker,map_sub,hyx,sub_self]
     have:=Ideal.add_mem _ hy (hkerQ' q54);simpa using this
    · intro hx;exact ⟨x,hx,rfl⟩
   exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq q41.symm).trans (RingHom.quotientKerEquivOfSurjective q22))).symm
  have hf:=z54 n Pbar Qbar q11;dsimp only at hf;rw [hdimP',hdimQ',z11 k n,ringKrullDim_eq_zero_of_field k,zero_add] at hf;let Tbar:=z0 (z0 k n) n;let qT:T →+* Tbar:=z15 qR n;have q16:Surjective qT:=z22 q9 n;let Ibar:Ideal Tbar:=Pbar.map (z15 (z13 k n) n)⊔Qbar.map (z13 (z0 k n) n);let fT:T →+* Tbar⧸Ibar:=(Ideal.Quotient.mk Ibar).comp qT
  have q13:Surjective fT:=Ideal.Quotient.mk_surjective.comp q16
  have q18:P'.map i₁ ⊔ Q'.map i₂ ≤ RingHom.ker fT:=by
   refine sup_le ?_ ?_
   ·
    rw [map_le_iff_le_comap];intro x hx;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem]
    have q53:qT (i₁ x)=z15 (z13 k n) n (qR x):=by
     have heq:qT.comp i₁ = (z15 (z13 k n) n).comp qR:=by
      have : ∀ m : ℕ,(z15 qR m).comp (z15 (z13 V n) m)=(z15 (z13 k n) m).comp (z15 (Ideal.Quotient.mk (maximalIdeal V)) m):=by
       intro m
       induction m with
       | zero =>
        ext c;change qR (z13 V n c)=z13 k n (Ideal.Quotient.mk (maximalIdeal V) c);exact z19 (Ideal.Quotient.mk (maximalIdeal V)) n c
       | succ m ihm =>
        ext F j;simp only [RingHom.comp_apply,z15,PowerSeries.coeff_map];exact RingHom.congr_fun ihm (PowerSeries.coeff j F)
      exact this n
     exact RingHom.congr_fun heq x
    rw [q53];exact mem_sup_left (mem_map_of_mem _ (mem_map_of_mem qR hx))
   ·
    rw [map_le_iff_le_comap];intro x hx;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem];have q53:qT (i₂ x)=z13 (z0 k n) n (qR x):=z19 qR n x;rw [q53];exact mem_sup_right (mem_map_of_mem _ (mem_map_of_mem qR hx))
  let q44:(T⧸(P'.map i₁ ⊔ Q'.map i₂)) →+* (Tbar⧸Ibar):=Ideal.Quotient.lift (P'.map i₁ ⊔ Q'.map i₂) fT q18
  have q0:Surjective q44:=fun y=>by
   obtain ⟨t,rfl⟩:=q13 y;exact ⟨Ideal.Quotient.mk _ t,rfl⟩
  have q6:=ringKrullDim_le_of_surjective q44 q0;exact ⟨hf.1.trans q6,hf.2⟩
 have q4:∀ (J:Ideal R) [J.IsPrime],z13 V n p∉J →
   ringKrullDim (R⧸(J⊔span {z13 V n p}))+1=ringKrullDim (R⧸J):=by
  intro J _ hpJ;have : IsLocalRing (R⧸J):=z36 J;let q56:R⧸J:=Ideal.Quotient.mk J (z13 V n p)
  have q15:q56≠0:=fun h=>hpJ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have q8:q56∈nonZeroDivisors (R⧸J):=mem_nonZeroDivisors_of_ne_zero q15
  have q5:q56∈maximalIdeal (R⧸J):=by
   have q43:(maximalIdeal (R⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);rw [← mem_comap,q43];exact z17 n (hp▸subset_span rfl)
  have h1:=ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
   q8 q5
  have q14:((R⧸J)⧸span {q56}) ≃+* (R⧸(J⊔span {z13 V n p})):=by
   let g:R →+* (R⧸J)⧸span {q56}:=(Ideal.Quotient.mk (span {q56})).comp (Ideal.Quotient.mk J);have q22:Surjective g:=Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
   have q41:RingHom.ker g=J⊔span {z13 V n p}:=by
    ext x;rw [RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem,mem_span_singleton];constructor
    ·
     rintro ⟨q,hq⟩;obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective q
     have q54:x - z13 V n p*r∈J:=by
      rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul];exact sub_eq_zero.mpr hq
     have q55:(x - z13 V n p*r)+z13 V n p*r∈J⊔span {z13 V n p} :=
      Ideal.add_mem _ (mem_sup_left q54)
       (mem_sup_right (mem_span_singleton.mpr ⟨r,rfl⟩))
     simpa using q55
    ·
     intro hx;obtain ⟨a,ha,b,hb,rfl⟩:=Submodule.mem_sup.mp hx;obtain ⟨r,rfl⟩:=mem_span_singleton.mp hb
     refine ⟨Ideal.Quotient.mk J r,?_⟩
     rw [map_add,Ideal.Quotient.eq_zero_iff_mem.mpr ha,zero_add,map_mul]
   exact ((Ideal.quotEquivOfEq q41.symm).trans
    (RingHom.quotientKerEquivOfSurjective q22)).symm
  rw [ringKrullDim_eq_of_ringEquiv q14] at h1;exact h1
 by_cases hpP:z13 V n p∈P
 ·
  by_cases hpQ:z13 V n p∈Q
  ·
   have hB1:=(q2 P Q hpP hpQ hPQ).2
   refine ⟨hB1.trans ?_,fun heq => ?_⟩
   ·
    rw [q52];exact_mod_cast Nat.le_succ n
   ·
    rw [heq,q52] at hB1
    have : n+1 ≤ n:=by exact_mod_cast hB1
    omega
  ·
   have q42:Q⊔span {z13 V n p} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (sup_le
     (le_maximalIdeal ‹Q.IsPrime›.ne_top)
     ((span_singleton_le_iff_mem _).mpr (z17 n (hp▸subset_span rfl))))
   obtain ⟨Q',hQ'_prime,hQ'_ge,hQ'_dim⟩ :=
    OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.exists_prime_ge_with_ringKrullDim_eq
     (Q⊔span {z13 V n p}) q42
   have : Q'.IsPrime:=hQ'_prime;have hpQ':z13 V n p∈Q':=hQ'_ge (mem_sup_right (subset_span rfl));have hQQ':Q ≤ Q':=le_sup_left.trans hQ'_ge
   have q10:(P⊔Q').radical=maximalIdeal R:=by
    refine le_antisymm ?_ ?_
    ·
     rw [← (maximalIdeal.isMaximal R).isPrime.radical]
     exact Ideal.radical_mono (sup_le (le_maximalIdeal ‹P.IsPrime›.ne_top)
      (le_maximalIdeal hQ'_prime.ne_top))
    ·
     rw [← hPQ];exact Ideal.radical_mono (sup_le_sup le_rfl hQQ')
   have q60:=q2 P Q' hpP hpQ' q10
   have q27:ringKrullDim (T⧸(P.map i₁ ⊔ Q'.map i₂)) ≤
     ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
     (sup_le_sup le_rfl (Ideal.map_mono hQQ')))
   have q19:ringKrullDim (R⧸Q')+1=ringKrullDim (R⧸Q):=by
    rw [hQ'_dim];exact q4 Q hpQ
   obtain ⟨r,hr⟩ :=
    ringKrullDim_quotient_eq_natCast
     P ‹P.IsPrime›.ne_top
   obtain ⟨s',hs'⟩ :=
    ringKrullDim_quotient_eq_natCast
     Q' hQ'_prime.ne_top
   have hs:ringKrullDim (R⧸Q)=((s'+1 : ℕ) : WithBot ℕ∞):=by
    rw [← q19,hs'];push_cast;rfl
   have q24:r+s' ≤ n:=by
    have:=q60.2;rw [hr,hs'] at this;exact_mod_cast this
   refine ⟨?_,fun heq=>⟨Or.inr hpQ,?_⟩⟩
   ·
    rw [hr,hs,q52];exact_mod_cast (show r+(s'+1) ≤ n+1 by omega)
   ·
    rw [hr,hs,q52] at heq
    have q26:r+(s'+1)=n+1:=by exact_mod_cast heq
    have q50:(n:WithBot ℕ∞) ≤ ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
     have h1:=q60.1.trans q27;rw [hr,hs'] at h1
     have q21:((n : ℕ) : WithBot ℕ∞)=(r:WithBot ℕ∞)+(s':WithBot ℕ∞):=by
      have : n=r+s':=by omega
      rw [this];push_cast;rfl
     exact q21.le.trans h1
    exact le_antisymm q48 q50
 ·
  by_cases hpQ:z13 V n p∈Q
  ·
   have q37:P⊔span {z13 V n p} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (sup_le
     (le_maximalIdeal ‹P.IsPrime›.ne_top)
     ((span_singleton_le_iff_mem _).mpr (z17 n (hp▸subset_span rfl))))
   obtain ⟨P',hP'_prime,hP'_ge,hP'_dim⟩ :=
    OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.exists_prime_ge_with_ringKrullDim_eq
     (P⊔span {z13 V n p}) q37
   have : P'.IsPrime:=hP'_prime;have hpP':z13 V n p∈P':=hP'_ge (mem_sup_right (subset_span rfl));have hPP':P ≤ P':=le_sup_left.trans hP'_ge
   have q12:(P'⊔Q).radical=maximalIdeal R:=by
    refine le_antisymm ?_ ?_
    ·
     rw [← (maximalIdeal.isMaximal R).isPrime.radical]
     exact Ideal.radical_mono (sup_le (le_maximalIdeal hP'_prime.ne_top)
      (le_maximalIdeal ‹Q.IsPrime›.ne_top))
    ·
     rw [← hPQ];exact Ideal.radical_mono (sup_le_sup hPP' le_rfl)
   have q60:=q2 P' Q hpP' hpQ q12
   have q27:ringKrullDim (T⧸(P'.map i₁ ⊔ Q.map i₂)) ≤
     ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective
     (sup_le_sup (Ideal.map_mono hPP') le_rfl))
   have q25:ringKrullDim (R⧸P')+1=ringKrullDim (R⧸P):=by
    rw [hP'_dim];exact q4 P hpP
   obtain ⟨r',hr'⟩ :=
    ringKrullDim_quotient_eq_natCast
     P' hP'_prime.ne_top
   obtain ⟨s,hs⟩ :=
    ringKrullDim_quotient_eq_natCast
     Q ‹Q.IsPrime›.ne_top
   have hr:ringKrullDim (R⧸P)=((r'+1 : ℕ) : WithBot ℕ∞):=by
    rw [← q25,hr'];push_cast;rfl
   have q24:r'+s ≤ n:=by
    have:=q60.2;rw [hr',hs] at this;exact_mod_cast this
   refine ⟨?_,fun heq=>⟨Or.inl hpP,?_⟩⟩
   ·
    rw [hr,hs,q52];exact_mod_cast (show (r'+1)+s ≤ n+1 by omega)
   ·
    rw [hr,hs,q52] at heq
    have q26:(r'+1)+s=n+1:=by exact_mod_cast heq
    have q50:(n:WithBot ℕ∞) ≤ ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
     have h1:=q60.1.trans q27;rw [hr',hs] at h1
     have q21:((n : ℕ) : WithBot ℕ∞)=(r':WithBot ℕ∞)+(s:WithBot ℕ∞):=by
      have : n=r'+s:=by omega
      rw [this];push_cast;rfl
     exact q21.le.trans h1
    exact le_antisymm q48 q50
  ·
   have q37:P⊔span {z13 V n p} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (sup_le
     (le_maximalIdeal ‹P.IsPrime›.ne_top)
     ((span_singleton_le_iff_mem _).mpr (z17 n (hp▸subset_span rfl))))
   have q42:Q⊔span {z13 V n p} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (sup_le
     (le_maximalIdeal ‹Q.IsPrime›.ne_top)
     ((span_singleton_le_iff_mem _).mpr (z17 n (hp▸subset_span rfl))))
   obtain ⟨r',hr'⟩ :=
    ringKrullDim_quotient_eq_natCast
     (P⊔span {z13 V n p}) q37
   obtain ⟨s',hs'⟩ :=
    ringKrullDim_quotient_eq_natCast
     (Q⊔span {z13 V n p}) q42
   have hr:ringKrullDim (R⧸P)=((r'+1 : ℕ) : WithBot ℕ∞):=by
    rw [← q4 P hpP,hr'];push_cast;rfl
   have hs:ringKrullDim (R⧸Q)=((s'+1 : ℕ) : WithBot ℕ∞):=by
    rw [← q4 Q hpQ,hs'];push_cast;rfl
   have : Nontrivial (R⧸(P⊔span {z13 V n p})):=Ideal.Quotient.nontrivial_iff.mpr q37;have : Nontrivial (R⧸(Q⊔span {z13 V n p})):=Ideal.Quotient.nontrivial_iff.mpr q42;have : IsLocalRing (R⧸(P⊔span {z13 V n p})):=z36 _;have : IsLocalRing (R⧸(Q⊔span {z13 V n p})):=z36 _;obtain ⟨u',hu'_mem,hu'_rad⟩:=z39 r' (R⧸(P⊔span {z13 V n p})) hr'
   obtain ⟨v',hv'_mem,hv'_rad⟩:=z39 s' (R⧸(Q⊔span {z13 V n p})) hs'
   let u:Fin r'→R:=fun i=>(Ideal.Quotient.mk_surjective (u' i)).choose
   have q49:∀ i,Ideal.Quotient.mk (P⊔span {z13 V n p}) (u i)=u' i:=fun i=>(Ideal.Quotient.mk_surjective (u' i)).choose_spec
   let v:Fin s'→R:=fun j=>(Ideal.Quotient.mk_surjective (v' j)).choose
   have q46:∀ j,Ideal.Quotient.mk (Q⊔span {z13 V n p}) (v j)=v' j:=fun j=>(Ideal.Quotient.mk_surjective (v' j)).choose_spec
   have q40:(maximalIdeal (R⧸(P⊔span {z13 V n p}))).comap
     (Ideal.Quotient.mk _)=maximalIdeal R :=
    eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
   have q31:(maximalIdeal (R⧸(Q⊔span {z13 V n p}))).comap
     (Ideal.Quotient.mk _)=maximalIdeal R :=
    eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
   have q36:∀ i,u i∈maximalIdeal R:=fun i=>by
    rw [← q40,mem_comap,q49 i];exact hu'_mem i
   have q29:∀ j,v j∈maximalIdeal R:=fun j=>by
    rw [← q31,mem_comap,q46 j];exact hv'_mem j
   have q1:∀ {J:Ideal R} [J.IsPrime] {m : ℕ} (w:Fin m→R)
     (w':Fin m→R⧸(J⊔span {z13 V n p}))
     (_:IsLocalRing (R⧸(J⊔span {z13 V n p}))),
     (∀ i,Ideal.Quotient.mk (J⊔span {z13 V n p}) (w i)=w' i) →
     (∀ i,w i∈maximalIdeal R) →
     (span (Set.range w')).radical=maximalIdeal (R⧸(J⊔span {z13 V n p})) →
     ((maximalIdeal V).map (z13 V n)⊔span (Set.range w)⊔J).radical=maximalIdeal R:=by
    intro J _ m w w' _ hw_eq hw_mem hw'_rad
    have q30:(maximalIdeal (R⧸(J⊔span {z13 V n p}))).comap
      (Ideal.Quotient.mk _)=maximalIdeal R :=
     eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    refine le_antisymm ?_ ?_
    ·
     rw [← (maximalIdeal.isMaximal R).isPrime.radical]
     refine Ideal.radical_mono (sup_le (sup_le ?_ ?_) (le_maximalIdeal ‹J.IsPrime›.ne_top))
     · rw [map_le_iff_le_comap];intro c hc;exact z17 n hc
     · rw [span_le];rintro _ ⟨i,rfl⟩;exact hw_mem i
    ·
     intro x hx
     have hx':Ideal.Quotient.mk (J⊔span {z13 V n p}) x ∈
       (span (Set.range w')).radical:=by
      rw [hw'_rad,← mem_comap,q30];exact hx
     obtain ⟨t,ht⟩:=hx';rw [← map_pow] at ht
     have q57:span (Set.range w')=(span (Set.range w)).map (Ideal.Quotient.mk (J⊔span {z13 V n p})):=by
      rw [map_span];congr 1;ext y;simp [hw_eq]
     rw [q57,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at ht;obtain ⟨y,hy_span,hy_eq⟩:=ht
     have q54:x ^ t - y∈J⊔span {z13 V n p}:=by
      rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,hy_eq,sub_self]
     obtain ⟨a,haJ,b,hbp,hab⟩:=Submodule.mem_sup.mp q54
     have hbp':b∈(maximalIdeal V).map (z13 V n):=by
      rw [hp,map_span,Set.image_singleton];exact hbp
     refine ⟨t,?_⟩
     have q55:=Ideal.add_mem _ (mem_sup_left (mem_sup_right hy_span))
      (Ideal.add_mem _ (mem_sup_right haJ) (mem_sup_left (mem_sup_left hbp')))
     have heq:y+(a+b)=x ^ t:=by rw [hab];ring
     rwa [heq] at q55
   have q32:=q1 u u' inferInstance q49 q36 hu'_rad;have q34:=q1 v v' inferInstance q46 q29 hv'_rad
   have q28:∀ {J:Ideal R} [J.IsPrime] {m : ℕ} (w:Fin m→R)
     (_:IsLocalRing (R⧸J)),
     ringKrullDim (R⧸J)=((m+1 : ℕ) : WithBot ℕ∞) →
     ((maximalIdeal V).map (z13 V n)⊔span (Set.range w)⊔J).radical=maximalIdeal R →
     ∀ f:z0 V m →+* R⧸J,(∀ c,f (z13 V m c)=Ideal.Quotient.mk J (z13 V n c))→(∀ i,f (z14 V i)=Ideal.Quotient.mk J (w i))→Injective f:=by
    intro J _ m w _ hdimJ hw_rad f hfC hfvar;have q43:(maximalIdeal (R⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    have q38:∀ x∈maximalIdeal (z0 V m),f x∈maximalIdeal (R⧸J):=by
     intro x hx;rw [z34 m] at hx
     have q45:(maximalIdeal V).map (z13 V m)⊔span (Set.range (z14 V (n:=m))) ≤ (maximalIdeal (R⧸J)).comap f:=by
      refine sup_le ?_ ?_
      ·
       rw [map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,hfC,← mem_comap,q43];exact z17 n hc
      ·
       rw [span_le];rintro _ ⟨i,rfl⟩;rw [SetLike.mem_coe,mem_comap,hfvar]
       have hwi:w i∈maximalIdeal R:=by
        rw [← hw_rad];exact Ideal.le_radical (mem_sup_left (mem_sup_right (subset_span ⟨i,rfl⟩)))
       rw [← mem_comap,q43];exact hwi
     exact q45 hx
    have q35:Surjective ((residue (R⧸J)).comp f):=by
     intro y;obtain ⟨r,rfl⟩:=residue_surjective y;obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective r;obtain ⟨c,hc⟩:=z35 n (residue R x)
     refine ⟨z13 V m c,?_⟩
     rw [RingHom.comp_apply,hfC]
     symm
     rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,← map_sub,← mem_comap,q43,← residue_eq_zero_iff,map_sub];change residue R x - ((residue R).comp (z13 V n)) c=0;rw [hc,sub_self]
    have q33:((maximalIdeal (z0 V m)).map f).radical=maximalIdeal (R⧸J):=by
     refine le_antisymm ?_ ?_
     ·
      rw [← (maximalIdeal.isMaximal (R⧸J)).isPrime.radical];exact Ideal.radical_mono (map_le_iff_le_comap.mpr q38)
     ·
      intro x hx;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective x;have hy:y∈maximalIdeal R:=q43▸hx;rw [← hw_rad] at hy;obtain ⟨t,ht⟩:=hy
      refine ⟨t,?_⟩
      rw [← map_pow]
      have hle:((maximalIdeal V).map (z13 V n)⊔span (Set.range w)⊔J).map
        (Ideal.Quotient.mk J) ≤ (maximalIdeal (z0 V m)).map f:=by
       rw [Ideal.map_sup,Ideal.map_sup]
       refine sup_le (sup_le ?_ ?_) ?_
       ·
        rw [map_le_iff_le_comap,map_le_iff_le_comap];intro c hc;rw [mem_comap,mem_comap,← hfC c];exact mem_map_of_mem f (z17 m hc)
       ·
        rw [map_span,span_le];rintro _ ⟨_,⟨i,rfl⟩,rfl⟩;rw [← hfvar i];exact mem_map_of_mem f (z18 i)
       ·
        rw [map_le_iff_le_comap];intro a ha;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr ha];exact Ideal.zero_mem _
      exact hle (mem_map_of_mem (Ideal.Quotient.mk J) ht)
    let _:Algebra (z0 V m) (R⧸J):=f.toAlgebra;have : Module.Finite (z0 V m) (R⧸J):=z40 q38 q35 q33;rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker_ne
    have q17:RingHom.ker f ≠ ⊤ := by
     intro q58;have h1:(1:z0 V m)∈RingHom.ker f:=q58▸Submodule.mem_top;rw [RingHom.mem_ker,map_one] at h1;exact one_ne_zero h1
    let q59:(z0 V m⧸RingHom.ker f) →+* R⧸J:=Ideal.Quotient.lift (RingHom.ker f) f (fun _ h=>h)
    have q7:Injective q59:=RingHom.kerLift_injective f;let _:Algebra (z0 V m⧸RingHom.ker f) (R⧸J):=q59.toAlgebra
    have : Module.Finite (z0 V m⧸RingHom.ker f) (R⧸J):=by
     obtain ⟨S,hS⟩:=Module.Finite.fg_top (R:=z0 V m) (M:=R⧸J)
     refine ⟨⟨S,eq_top_iff.mpr fun x _ => ?_⟩⟩
     have hx:x∈Submodule.span (z0 V m) (S:Set (R⧸J)):=hS▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hx ⊢;obtain ⟨c,hc,rfl⟩:=hx
     refine ⟨fun s=>Ideal.Quotient.mk (RingHom.ker f) (c s),fun s hs => ?_,?_⟩
     · exact hc (fun h0=>hs (by simp [h0]))
     ·
      refine Finset.sum_congr rfl fun s _ => ?_
      rfl
    have : Algebra.IsIntegral (z0 V m⧸RingHom.ker f) (R⧸J):=Algebra.IsIntegral.of_finite _ _;have q23:=z37 q7;have hlt:=z38 hker_ne q17;rw [← q23,hdimJ,z11 V m,q51] at hlt
    have q47:((m+1 : ℕ) : WithBot ℕ∞)=1+(m:WithBot ℕ∞):=by
     push_cast;rw [add_comm]
    rw [q47] at hlt;exact lt_irrefl _ hlt
   have hge:=z44 (Λ := V) n P Q r' s' u q36 v q29 q32 q34
    (q28 u inferInstance hr q32) (q28 v inferInstance hs q34)
   rw [q51] at hge;have q39:(1:WithBot ℕ∞)+(s':WithBot ℕ∞)+(r':WithBot ℕ∞) ≤ (n:WithBot ℕ∞):=hge.trans q48
   have hnat:1+s'+r' ≤ n:=by exact_mod_cast q39
   refine ⟨?_,fun heq=>⟨Or.inl hpP,?_⟩⟩
   ·
    rw [hr,hs,q52];exact_mod_cast (show (r'+1)+(s'+1) ≤ n+1 by omega)
   ·
    rw [hr,hs,q52] at heq
    have q26:(r'+1)+(s'+1)=n+1:=by exact_mod_cast heq
    have q50:(n:WithBot ℕ∞) ≤ ringKrullDim (T⧸(P.map i₁ ⊔ Q.map i₂)):=by
     have q21:((n : ℕ) : WithBot ℕ∞)=(1:WithBot ℕ∞)+(s':WithBot ℕ∞)+(r':WithBot ℕ∞):=by
      have : n=1+s'+r':=by omega
      rw [this];push_cast;rfl
     exact q21.le.trans hge
    exact le_antisymm q48 q50
end DimensionInequality
section TorAndFlatness
noncomputable abbrev z56 (R:Type) [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (i : ℕ) : ModuleCat.{0} R :=
 ((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)
noncomputable def z57 {R:Type} [CommRing R]
  (M:Type) [AddCommGroup M] [Module R M]
  {A B:Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (f:A →ₗ[R] B) (i : ℕ) :
  z56 R M A i →ₗ[R] z56 R M B i :=
 (((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).map (ModuleCat.ofHom f)).hom
noncomputable def z58 {R:Type} [CommRing R]
  {A B:Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (f:A →ₗ[R] B) (N:Type) [AddCommGroup N] [Module R N] (i : ℕ) :
  z56 R A N i →ₗ[R] z56 R B N i :=
 (((Tor (ModuleCat.{0} R) i).map (ModuleCat.ofHom f)).app (ModuleCat.of R N)).hom
noncomputable def z59 (R:Type) [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
  z56 R M N 0 ≃ₗ[R] (M ⊗[R] N) :=
 (((tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)).leftDerivedZeroIsoSelf.app
  (ModuleCat.of R N)).toLinearEquiv
lemma z60 {R:Type} [CommRing R]
  (M:Type) [AddCommGroup M] [Module R M]
  {A B:Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (f:A →ₗ[R] B) (x:z56 R M A 0) :
  z59 R M B (z57 M f 0 x)=LinearMap.lTensor M f (z59 R M A x):=by
 have q0:=(((tensoringLeft (ModuleCat.{0} R)).obj
  (ModuleCat.of R M)).leftDerivedZeroIsoSelf.hom.naturality (ModuleCat.ofHom f))
 exact congrArg (fun φ : z56 R M A 0 ⟶ ModuleCat.of R (M ⊗[R] B) => φ.hom x) q0
lemma z61 {R:Type} [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Projective R N] (i : ℕ) :
  Subsingleton (z56 R M N (i+1)) :=
 ModuleCat.isZero_iff_subsingleton.mp
  (isZero_Tor_succ_of_projective (ModuleCat.{0} R) (ModuleCat.of R M) (ModuleCat.of R N) i)
noncomputable def z62 {R:Type} [CommRing R]
  (B:Type) [AddCommGroup B] [Module R B]
  (K:ChainComplex (ModuleCat.{0} R) ℕ)
  (q5:∀ n,Module.Projective R (K.X n))
  (ε : (K.X 0) →ₗ[R] B)
  (hε_surj:Surjective ε)
  (hε_comp:∀ x:K.X 1,ε ((K.d 1 0).hom x)=0)
  (hε_exact:∀ x:K.X 0,ε x=0→∃ y:K.X 1,(K.d 1 0).hom y=x)
  (q4:∀ n : ℕ,∀ x:K.X (n+1),(K.d (n+1) n).hom x=0→∃ y:K.X (n+2),(K.d (n+2) (n+1)).hom y=x) :
  ProjectiveResolution (ModuleCat.of R B):=by
 let π : K ⟶ (ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B) :=
  (ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
   ⟨ModuleCat.ofHom ε,by ext x;exact hε_comp x⟩
 have hπ0:(π.f 0).hom = ε := by
  change ((ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
   ⟨ModuleCat.ofHom ε,_⟩ |>.f 0).hom = ε
  rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero];rfl
 have hq:QuasiIso π := by
  rw [quasiIso_iff];intro n
  cases n with
  | zero =>
   rw [quasiIsoAt_iff_isIso_homologyMap];have q8:(K.sc 0).g=0:=K.shape 0 _ (by simp);have q6:(((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).g=0:=((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).shape 0 _ (by simp);have _:IsIso (K.homologyι 0):=ShortComplex.isIso_homologyι (K.sc 0) q8
   have _:IsIso (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0):=ShortComplex.isIso_homologyι _ q6
   have q7:(HomologicalComplex.homologyMap π 0 ≫
     ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) =
     (K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0) :=
    HomologicalComplex.homologyι_naturality π 0
   have q2:Bijective (HomologicalComplex.opcyclesMap π 0).hom:=by
    constructor
    ·
     intro u v huv;have q3:Surjective (K.pOpcycles 0):=(ModuleCat.epi_iff_surjective (K.pOpcycles 0)).mp inferInstance;obtain ⟨x,rfl⟩:=q3 u;obtain ⟨y,rfl⟩:=q3 v
     have q10:HomologicalComplex.opcyclesMap π 0 (K.pOpcycles 0 (x - y))=0:=by
      change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y))=0;rw [map_sub,map_sub,huv,sub_self]
     have q11:(HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y)) =
       (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
        ((π.f 0).hom (x - y)) :=
      congrArg (fun φ : K.X 0 ⟶
       ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
        φ.hom (x - y))
       (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
     rw [q11] at q10;have q13:=(ShortComplex.moduleCat_pOpcycles_eq_zero_iff _ _).mp q10
     have q9:(((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f=0:=by
      simp [HomologicalComplex.sc];rfl
     obtain ⟨w,hw⟩:=q13
     have hε0 : ε (x - y)=0:=by
      rw [← hπ0]
      have hw0:((((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f).hom w=0:=by
       rw [q9];rfl
      exact hw.symm.trans hw0
     obtain ⟨z,hz⟩:=hε_exact (x - y) hε0
     have h0:(K.pOpcycles 0).hom (x - y)=0:=by
      rw [← hz]
      exact congrArg (fun φ : K.X 1 ⟶ K.opcycles 0 => φ.hom z) (K.d_pOpcycles 1 0)
     rw [map_sub] at h0;exact sub_eq_zero.mp h0
    ·
     intro w
     have q0:Surjective
       (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0) :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
     obtain ⟨b,rfl⟩:=q0 w;obtain ⟨x,hx⟩:=hε_surj b
     refine ⟨K.pOpcycles 0 x,?_⟩
     have q11:(HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x) =
       (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
        ((π.f 0).hom x) :=
      congrArg (fun φ : K.X 0 ⟶
       ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
        φ.hom x)
       (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
     change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x)=_;rw [q11]
     have hxb:(π.f 0).hom x=b:=by
      have h1:(π.f 0).hom x = ε x:=LinearMap.congr_fun hπ0 x;exact h1.trans hx
     exact congrArg
      (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom hxb
   have q1:IsIso (HomologicalComplex.opcyclesMap π 0) :=
    ⟨ModuleCat.ofHom (LinearEquiv.ofBijective _ q2).symm.toLinearMap,by ext u;exact (LinearEquiv.ofBijective _ q2).left_inv u,by ext v;exact (LinearEquiv.ofBijective _ q2).right_inv v⟩
   have q12:HomologicalComplex.homologyMap π 0 =
     K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0 ≫
      inv (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0):=by
    rw [← Category.assoc,← q7,Category.assoc,IsIso.hom_inv_id,Category.comp_id]
   rw [q12]
   infer_instance
  | succ m =>
   rw [quasiIsoAt_iff_exactAt' π (m+1) (ChainComplex.exactAt_succ_single_obj _ _)];rw [HomologicalComplex.exactAt_iff' K (m+2) (m+1) m (by simp) (by simp)];rw [ShortComplex.moduleCat_exact_iff];exact q4 m
 exact
  {
   complex:=K
   projective:=fun n=>by
    let _:=q5 n
    infer_instance
   π := π
   quasiIso:=hq }
lemma z63 {R:Type} [CommRing R]
  (M:Type) [AddCommGroup M] [Module R M]
  {A B C:Type} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  (i:A →ₗ[R] B) (p:B →ₗ[R] C)
  (hi:Injective i) (hp:Surjective p)
  (hip:LinearMap.range i=LinearMap.ker p) :
  ∃ δ : ∀ n : ℕ,z56 R M C (n+1) →ₗ[R] z56 R M A n,(∀ n,Function.Exact (δ n) (z57 M i n))∧(∀ n,Function.Exact (z57 M i n) (z57 M p n))∧(∀ n,Function.Exact (z57 M p (n+1)) (δ n)):=by
 let PA:ProjectiveResolution (ModuleCat.of R A):=projectiveResolution (ModuleCat.of R A);let PC:ProjectiveResolution (ModuleCat.of R C):=projectiveResolution (ModuleCat.of R C);have hPA_proj (n : ℕ) : Module.Projective R (PA.complex.X n):=ModuleCat.projective_of_module_projective (P:=PA.complex.X n)
 have hPC_proj (n : ℕ) : Module.Projective R (PC.complex.X n):=ModuleCat.projective_of_module_projective (P:=PC.complex.X n);let εA:PA.complex.X 0 →ₗ[R] A:=(PA.π.f 0).hom;let εC:PC.complex.X 0 →ₗ[R] C:=(PC.π.f 0).hom;have hεA_surj:Surjective εA:=(ModuleCat.epi_iff_surjective (PA.π.f 0)).mp inferInstance
 have hεC_surj:Surjective εC:=(ModuleCat.epi_iff_surjective (PC.π.f 0)).mp inferInstance
 have hεA_comp (x:PA.complex.X 1) : εA ((PA.complex.d 1 0).hom x)=0 :=
  congrArg (fun φ : PA.complex.X 1 ⟶ ModuleCat.of R A => φ.hom x) PA.complex_d_comp_π_f_zero
 have hεC_comp (x:PC.complex.X 1) : εC ((PC.complex.d 1 0).hom x)=0 :=
  congrArg (fun φ : PC.complex.X 1 ⟶ ModuleCat.of R C => φ.hom x) PC.complex_d_comp_π_f_zero
 have hε_exact_of_res {X:Type} [AddCommGroup X] [Module R X]
   (PX:ProjectiveResolution (ModuleCat.of R X)) (x:PX.complex.X 0)
   (hx:(PX.π.f 0).hom x=0) :
   ∃ y:PX.complex.X 1,(PX.complex.d 1 0).hom y=x:=by
  let Q:=PX.complex.X 0⧸LinearMap.range (PX.complex.d 1 0).hom;let q:PX.complex.X 0 ⟶ ModuleCat.of R Q:=ModuleCat.ofHom (LinearMap.range (PX.complex.d 1 0).hom).mkQ
  have hqw:(PX.complex.d 1 0 ≫ q)=0:=by
   ext z;exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z,rfl⟩
  let desc:ModuleCat.of R X ⟶ ModuleCat.of R Q:=PX.isColimitCokernelCofork.desc (CokernelCofork.ofπ q hqw);have q17:(PX.π.f 0 ≫ desc)=q:=PX.isColimitCokernelCofork.fac (CokernelCofork.ofπ q hqw) WalkingParallelPair.one
  have hqx:q.hom x=0:=by
   have h1:desc.hom ((PX.π.f 0).hom x)=q.hom x :=
    congrArg (fun φ : PX.complex.X 0 ⟶ ModuleCat.of R Q => φ.hom x) q17
   have hx0:(PX.π.f 0).hom x=(0:X):=hx;rw [← h1,hx0];exact map_zero desc.hom
  exact (Submodule.Quotient.mk_eq_zero _).mp hqx
 have hεA_exact:=hε_exact_of_res PA;have hεC_exact:=hε_exact_of_res PC
 have hPA_exact (n : ℕ) (x:PA.complex.X (n+1)) (hx:(PA.complex.d (n+1) n).hom x=0) :
   ∃ y:PA.complex.X (n+2),(PA.complex.d (n+2) (n+1)).hom y=x :=
  (ShortComplex.moduleCat_exact_iff _).mp (PA.exact_succ n) x hx
 have hPC_exact (n : ℕ) (x:PC.complex.X (n+1)) (hx:(PC.complex.d (n+1) n).hom x=0) :
   ∃ y:PC.complex.X (n+2),(PC.complex.d (n+2) (n+1)).hom y=x :=
  (ShortComplex.moduleCat_exact_iff _).mp (PC.exact_succ n) x hx
 have hPA_dd (n : ℕ) (x:PA.complex.X (n+2)) :
   (PA.complex.d (n+1) n).hom ((PA.complex.d (n+2) (n+1)).hom x)=0 :=
  congrArg (fun φ : PA.complex.X (n+2) ⟶ PA.complex.X n => φ.hom x)
   (PA.complex.d_comp_d (n+2) (n+1) n)
 have hPC_dd (n : ℕ) (x:PC.complex.X (n+2)) :
   (PC.complex.d (n+1) n).hom ((PC.complex.d (n+2) (n+1)).hom x)=0 :=
  congrArg (fun φ : PC.complex.X (n+2) ⟶ PC.complex.X n => φ.hom x)
   (PC.complex.d_comp_d (n+2) (n+1) n)
 let _:=hPC_proj 0;obtain ⟨s0,hs0⟩:=Module.projective_lifting_property p εC hp;let εB:(PA.complex.X 0×PC.complex.X 0) →ₗ[R] B:=(i.comp εA).coprod s0
 have q8:∃ h0:PC.complex.X 1 →ₗ[R] PA.complex.X 0,∀ c:PC.complex.X 1,i (εA (h0 c))+s0 ((PC.complex.d 1 0).hom c)=0:=by
  let _:=hPC_proj 1
  let q1:PC.complex.X 1 →ₗ[R] LinearMap.ker p :=
   LinearMap.codRestrict (LinearMap.ker p) (-(s0.comp (PC.complex.d 1 0).hom)) (fun c=>by
    rw [LinearMap.mem_ker,LinearMap.neg_apply,map_neg,LinearMap.comp_apply];have h1:p (s0 ((PC.complex.d 1 0).hom c)) = εC ((PC.complex.d 1 0).hom c):=LinearMap.congr_fun hs0 _
    rw [h1,hεC_comp,neg_zero])
  let q19:PA.complex.X 0 →ₗ[R] LinearMap.ker p :=
   LinearMap.codRestrict (LinearMap.ker p) (i.comp εA) (fun a=>by
    rw [LinearMap.mem_ker,LinearMap.comp_apply,← LinearMap.mem_ker,← hip]
    exact ⟨εA a,rfl⟩)
  have q0:Surjective q19:=by
   rintro ⟨b,hb⟩;rw [← hip] at hb;obtain ⟨a,rfl⟩:=hb;obtain ⟨x,rfl⟩:=hεA_surj a;exact ⟨x,rfl⟩
  obtain ⟨h0,hh0⟩:=Module.projective_lifting_property q19 q1 q0
  refine ⟨h0,fun c => ?_⟩
  have hc:=congrArg Subtype.val (LinearMap.congr_fun hh0 c);change i (εA (h0 c)) = -(s0 ((PC.complex.d 1 0).hom c)) at hc;rw [hc,neg_add_cancel]
 have q9:∀ (n : ℕ) (q15:PC.complex.X (n+1) →ₗ[R] PA.complex.X n),
   (∀ c:PC.complex.X (n+2),∃ a:PA.complex.X (n+1),(PA.complex.d (n+1) n).hom a = -(q15 ((PC.complex.d (n+2) (n+1)).hom c))) →
   ∃ hnxt:PC.complex.X (n+2) →ₗ[R] PA.complex.X (n+1),
    ∀ c:PC.complex.X (n+2),(PA.complex.d (n+1) n).hom (hnxt c)+q15 ((PC.complex.d (n+2) (n+1)).hom c)=0:=by
  intro n q15 hpre;let _:=hPC_proj (n+2)
  let q18:PC.complex.X (n+2) →ₗ[R] LinearMap.range (PA.complex.d (n+1) n).hom:=LinearMap.codRestrict _ (-(q15.comp (PC.complex.d (n+2) (n+1)).hom)) (fun c=>hpre c)
  obtain ⟨hnxt,hhnxt⟩:=Module.projective_lifting_property
   (LinearMap.rangeRestrict (PA.complex.d (n+1) n).hom) q18
   (LinearMap.surjective_rangeRestrict _)
  refine ⟨hnxt,fun c => ?_⟩
  have hc:=congrArg Subtype.val (LinearMap.congr_fun hhnxt c);change (PA.complex.d (n+1) n).hom (hnxt c) = -(q15 ((PC.complex.d (n+2) (n+1)).hom c)) at hc;rw [hc,neg_add_cancel]
 let q3:∀ n : ℕ,
   Σ' (h:PC.complex.X (n+1) →ₗ[R] PA.complex.X n),
    ∀ c:PC.complex.X (n+2),∃ a:PA.complex.X (n+1),(PA.complex.d (n+1) n).hom a = -(h ((PC.complex.d (n+2) (n+1)).hom c)) :=
  Nat.rec
   ⟨Classical.choose q8,fun c=>by
    have h0:=Classical.choose_spec q8 ((PC.complex.d 2 1).hom c);rw [hPC_dd 0 c,map_zero,add_zero] at h0
    have he : εA (-(Classical.choose q8 ((PC.complex.d 2 1).hom c)))=0:=by
     rw [map_neg,hi (h0.trans (map_zero i).symm),neg_zero]
    exact hεA_exact _ he⟩
   (fun n prev =>
    let hex:=q9 n prev.1 prev.2
    ⟨Classical.choose hex,fun c=>by
     have h1:=Classical.choose_spec hex ((PC.complex.d (n+3) (n+2)).hom c);rw [hPC_dd (n+1) c,map_zero,add_zero] at h1
     have q14:(PA.complex.d (n+1) n).hom
       (-(Classical.choose hex ((PC.complex.d (n+3) (n+2)).hom c)))=0:=by
      rw [map_neg,h1,neg_zero]
     exact hPA_exact n _ q14⟩)
 let h (n : ℕ) : PC.complex.X (n+1) →ₗ[R] PA.complex.X n:=(q3 n).1
 have hh0 (c:PC.complex.X 1) :
   i (εA (h 0 c))+s0 ((PC.complex.d 1 0).hom c)=0 :=
  Classical.choose_spec q8 c
 have hh_succ (n : ℕ) (c:PC.complex.X (n+2)) :
   (PA.complex.d (n+1) n).hom (h (n+1) c)+h n ((PC.complex.d (n+2) (n+1)).hom c)=0 :=
  Classical.choose_spec (q9 n (q3 n).1 (q3 n).2) c
 let dB (n : ℕ) : ModuleCat.of R (PA.complex.X (n+1)×PC.complex.X (n+1)) ⟶
   ModuleCat.of R (PA.complex.X n×PC.complex.X n) :=
  ModuleCat.ofHom
   {
    toFun:=fun x=>((PA.complex.d (n+1) n).hom x.1+h n x.2,(PC.complex.d (n+1) n).hom x.2)
    map_add':=fun x y=>by
     ext
     ·
      change (PA.complex.d (n+1) n).hom (x.1+y.1)+h n (x.2+y.2)=((PA.complex.d (n+1) n).hom x.1+h n x.2)+((PA.complex.d (n+1) n).hom y.1+h n y.2);rw [map_add,map_add];abel
     · exact map_add (PC.complex.d (n+1) n).hom x.2 y.2
    map_smul':=fun r x=>by
     ext
     ·
      change (PA.complex.d (n+1) n).hom (r•x.1)+h n (r•x.2)=r•((PA.complex.d (n+1) n).hom x.1+h n x.2);rw [map_smul,map_smul,smul_add]
     · exact map_smul (PC.complex.d (n+1) n).hom r x.2 }
 have hdB_sq (n : ℕ) : (dB (n+1) ≫ dB n)=0:=by
  apply ModuleCat.hom_ext;apply LinearMap.ext;rintro ⟨a,c⟩;ext
  ·
   change (PA.complex.d (n+1) n).hom ((PA.complex.d (n+2) (n+1)).hom a+h (n+1) c)+h n ((PC.complex.d (n+2) (n+1)).hom c)=0;rw [map_add,hPA_dd n a,zero_add,hh_succ n c]
  ·
   change (PC.complex.d (n+1) n).hom ((PC.complex.d (n+2) (n+1)).hom c)=0;exact hPC_dd n c
 let KB:ChainComplex (ModuleCat.{0} R) ℕ := ChainComplex.of (fun n=>ModuleCat.of R (PA.complex.X n×PC.complex.X n)) dB hdB_sq
 let ιK:PA.complex ⟶ KB :=
  {
   f:=fun n=>ModuleCat.ofHom (LinearMap.inl R (PA.complex.X n) (PC.complex.X n))
   comm':=fun n m hnm=>by
    cases hnm
    apply ModuleCat.hom_ext;apply LinearMap.ext;intro a;ext
    ·
     change ((KB.d (m+1) m).hom (a,0)).1=(PA.complex.d (m+1) m).hom a;simp [KB,ChainComplex.of_d,dB]
    ·
     change ((KB.d (m+1) m).hom (a,0)).2=0
     simp [KB,ChainComplex.of_d,dB] }
 let πK:KB ⟶ PC.complex :=
  {
   f:=fun n=>ModuleCat.ofHom (LinearMap.snd R (PA.complex.X n) (PC.complex.X n))
   comm':=fun n m hnm=>by
    cases hnm
    apply ModuleCat.hom_ext;apply LinearMap.ext;rintro ⟨a,c⟩;change (PC.complex.d (m+1) m).hom c=((KB.d (m+1) m).hom (a,c)).2
    simp [KB,ChainComplex.of_d,dB] }
 have q6:(ιK ≫ πK)=0:=by ext n a;rfl
 let SK:ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ):=ShortComplex.mk ιK πK q6
 have hKB_proj (n : ℕ) : Module.Projective R (KB.X n):=by
  let _:=hPA_proj n;let _:=hPC_proj n;change Module.Projective R (PA.complex.X n×PC.complex.X n)
  infer_instance
 have hps0 (c:PC.complex.X 0) : p (s0 c) = εC c:=LinearMap.congr_fun hs0 c
 have hεB_surj:Surjective εB:=fun b=>by
  obtain ⟨c,hc⟩:=hεC_surj (p b)
  have q16:b - s0 c∈LinearMap.ker p:=by
   rw [LinearMap.mem_ker,map_sub,hps0 c,hc,sub_self]
  rw [← hip] at q16;obtain ⟨a0,ha0⟩:=q16;obtain ⟨a,rfl⟩:=hεA_surj a0
  refine ⟨(a,c),?_⟩
  change i (εA a)+s0 c=b;rw [ha0,sub_add_cancel]
 have hεB_comp (x:KB.X 1) : εB ((KB.d 1 0).hom x)=0:=by
  rcases x with ⟨a,c⟩
  change i (εA ((PA.complex.d 1 0).hom a+h 0 c))+s0 ((PC.complex.d 1 0).hom c)=0;rw [map_add,map_add,hεA_comp a,map_zero,zero_add,hh0 c]
 have hεB_exact (x:KB.X 0) (hx : εB x=0) : ∃ y:KB.X 1,(KB.d 1 0).hom y=x:=by
  rcases x with ⟨a,c⟩
  change i (εA a)+s0 c=0 at hx
  have hpc : εC c=0:=by
   have hp0:=congrArg p hx;rw [map_add,map_zero,hps0 c] at hp0
   have hi0:p (i (εA a))=0:=by rw [← LinearMap.mem_ker,← hip];exact ⟨εA a,rfl⟩
   rw [hi0,zero_add] at hp0;exact hp0
  obtain ⟨c1,hc1⟩:=hεC_exact c hpc
  have q10 : εA (a - h 0 c1)=0:=by
   apply hi;rw [map_zero,map_sub,map_sub];have h1:=hh0 c1;rw [hc1] at h1;have hia:i (εA a) = - s0 c:=eq_neg_of_add_eq_zero_left hx;have hih:i (εA (h 0 c1)) = - s0 c:=eq_neg_of_add_eq_zero_left h1;rw [hia,hih,sub_self]
  obtain ⟨a1,ha1⟩:=hεA_exact _ q10
  refine ⟨(a1,c1),?_⟩
  change ((PA.complex.d 1 0).hom a1+h 0 c1,(PC.complex.d 1 0).hom c1)=(a,c);ext
  · rw [ha1,sub_add_cancel]
  · exact hc1
 have hKB_exact (n : ℕ) (x:KB.X (n+1)) (hx:(KB.d (n+1) n).hom x=0) :
   ∃ y:KB.X (n+2),(KB.d (n+2) (n+1)).hom y=x:=by
  rcases x with ⟨a,c⟩
  have hx':((PA.complex.d (n+1) n).hom a+h n c,(PC.complex.d (n+1) n).hom c)=(0,0):=by
   simpa [KB,ChainComplex.of_d,dB] using hx
  have hx1:(PA.complex.d (n+1) n).hom a+h n c=0:=congrArg Prod.fst hx';have hx2:(PC.complex.d (n+1) n).hom c=0:=congrArg Prod.snd hx';obtain ⟨c1,hc1⟩:=hPC_exact n c hx2
  have q10:(PA.complex.d (n+1) n).hom (a - h (n+1) c1)=0:=by
   rw [map_sub];have h1:=hh_succ n c1;rw [hc1] at h1;have h2:(PA.complex.d (n+1) n).hom a = - h n c:=eq_neg_of_add_eq_zero_left hx1;have h3:(PA.complex.d (n+1) n).hom (h (n+1) c1) = - h n c:=eq_neg_of_add_eq_zero_left h1;rw [h2,h3,sub_self]
  obtain ⟨a1,ha1⟩:=hPA_exact n _ q10
  refine ⟨(a1,c1),?_⟩
  have q11:(KB.d (n+2) (n+1)).hom (a1,c1) =
    ((PA.complex.d (n+2) (n+1)).hom a1+h (n+1) c1,(PC.complex.d (n+2) (n+1)).hom c1) :=
   congrArg (fun φ : KB.X (n+2) ⟶ KB.X (n+1) => φ.hom (a1,c1))
    (ChainComplex.of_d _ dB (n+1))
  rw [q11];ext
  · rw [ha1,sub_add_cancel]
  · exact hc1
 let PB:ProjectiveResolution (ModuleCat.of R B):=z62 B KB hKB_proj εB hεB_surj hεB_comp hεB_exact hKB_exact
 have q4:(ιK.f 0 ≫ PB.π.f 0)=(PA.π.f 0 ≫ ModuleCat.ofHom i):=by
  apply ModuleCat.hom_ext;apply LinearMap.ext;intro a;change εB (a,0)=i (εA a);simp [εB]
 have q5:(πK.f 0 ≫ PC.π.f 0)=(PB.π.f 0 ≫ ModuleCat.ofHom p):=by
  apply ModuleCat.hom_ext;apply LinearMap.ext;rintro ⟨a,c⟩;change εC c=p (εB (a,c));simp only [εB,LinearMap.coprod_apply,map_add,LinearMap.comp_apply]
  have hi0:p (i (εA a))=0:=by rw [← LinearMap.mem_ker,← hip];exact ⟨εA a,rfl⟩
  rw [hi0,zero_add,hps0 c]
 let F:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M);let SM:ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ):=SK.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
 have q2:SM.ShortExact:=by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact;intro n
  let q7:(SK.map (HomologicalComplex.eval _ _ n)).Splitting :=
   {
    r:=ModuleCat.ofHom (LinearMap.fst R (PA.complex.X n) (PC.complex.X n))
    s:=ModuleCat.ofHom (LinearMap.inr R (PA.complex.X n) (PC.complex.X n))
    f_r:=by apply ModuleCat.hom_ext;apply LinearMap.ext;intro a;rfl
    s_g:=by apply ModuleCat.hom_ext;apply LinearMap.ext;intro c;rfl
    id:=by
     apply ModuleCat.hom_ext;apply LinearMap.ext;rintro ⟨a,c⟩
     change (a,0)+(0,c)=(a,c);ext <;> simp }
  exact (q7.map F).shortExact
 let eA (n : ℕ) : z56 R M A n ≅ SM.X₁.homology n:=PA.isoLeftDerivedObj F n;let eB (n : ℕ) : z56 R M B n ≅ SM.X₂.homology n:=PB.isoLeftDerivedObj F n;let eC (n : ℕ) : z56 R M C n ≅ SM.X₃.homology n:=PC.isoLeftDerivedObj F n;let δ (n : ℕ) : z56 R M C (n+1) →ₗ[R] z56 R M A n:=((eC (n+1)).hom ≫ q2.δ (n+1) n rfl ≫ (eA n).inv).hom
 have htor_i_hom (n : ℕ) (x:z56 R M A n) :
   (eB n).hom.hom (z57 M i n x)=(HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x) :=
  congrArg (fun φ : z56 R M A n ⟶ SM.X₂.homology n => φ.hom x)
   (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom i) PA PB ιK q4 F n)
 have htor_p_hom (n : ℕ) (x:z56 R M B n) :
   (eC n).hom.hom (z57 M p n x)=(HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x) :=
  congrArg (fun φ : z56 R M B n ⟶ SM.X₃.homology n => φ.hom x)
   (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom p) PB PC πK q5 F n)
 have iso_hom_inv {X Y:ModuleCat.{0} R} (e:X ≅ Y) (y:Y) : e.hom.hom (e.inv.hom y)=y :=
  congrArg (fun φ : Y ⟶ Y => φ.hom y) e.inv_hom_id
 have iso_inv_hom {X Y:ModuleCat.{0} R} (e:X ≅ Y) (x:X) : e.inv.hom (e.hom.hom x)=x :=
  congrArg (fun φ : X ⟶ X => φ.hom x) e.hom_inv_id
 refine ⟨δ,?_,?_,?_⟩
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q2.homology_exact₁ (n+1) n rfl)
  have h1:z57 M i n x=0↔(HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x)=0:=by
   rw [← htor_i_hom n x];exact (eB n).toLinearEquiv.map_eq_zero_iff.symm
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eA n).hom.hom x) hx
   refine ⟨(eC (n+1)).inv.hom y,?_⟩
   change (eA n).inv.hom ((q2.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom ((eC (n+1)).inv.hom y)))=x;rw [iso_hom_inv (eC (n+1)) y,hy];exact iso_inv_hom (eA n) x
  ·
   rintro ⟨z,rfl⟩
   have q13:=congrArg (fun φ : SM.X₃.homology (n+1) ⟶ SM.X₂.homology n =>
    φ.hom ((eC (n+1)).hom.hom z)) (q2.δ_comp (n+1) n rfl)
   change (HomologicalComplex.homologyMap SM.f n).hom
    ((eA n).hom.hom ((eA n).inv.hom ((q2.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom z))))=0
   rw [iso_hom_inv (eA n)];exact q13
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q2.homology_exact₂ n)
  have h1:z57 M p n x=0↔(HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x)=0:=by
   rw [← htor_p_hom n x];exact (eC n).toLinearEquiv.map_eq_zero_iff.symm
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eB n).hom.hom x) hx
   refine ⟨(eA n).inv.hom y,?_⟩
   apply (eB n).toLinearEquiv.injective;change (eB n).hom.hom (z57 M i n ((eA n).inv.hom y))=(eB n).hom.hom x;rw [htor_i_hom n,iso_hom_inv (eA n) y,hy]
  ·
   rintro ⟨z,rfl⟩;rw [htor_i_hom n]
   have q12:(HomologicalComplex.homologyMap SM.f n ≫ HomologicalComplex.homologyMap SM.g n)=0:=by
    rw [← HomologicalComplex.homologyMap_comp,SM.zero,HomologicalComplex.homologyMap_zero]
   exact congrArg (fun φ : SM.X₁.homology n ⟶ SM.X₃.homology n => φ.hom ((eA n).hom.hom z)) q12
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q2.homology_exact₃ (n+1) n rfl)
  have h1 : δ n x=0↔(q2.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom x)=0:=by
   change (eA n).inv.hom ((q2.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom x))=0↔_;exact (eA n).toLinearEquiv.symm.map_eq_zero_iff
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eC (n+1)).hom.hom x) hx
   refine ⟨(eB (n+1)).inv.hom y,?_⟩
   apply (eC (n+1)).toLinearEquiv.injective;change (eC (n+1)).hom.hom (z57 M p (n+1) ((eB (n+1)).inv.hom y))=(eC (n+1)).hom.hom x;rw [htor_p_hom (n+1),iso_hom_inv (eB (n+1)) y,hy]
  ·
   rintro ⟨z,rfl⟩;rw [htor_p_hom (n+1)]
   exact congrArg (fun φ : SM.X₂.homology (n+1) ⟶ SM.X₁.homology n =>
    φ.hom ((eB (n+1)).hom.hom z)) (q2.comp_δ (n+1) n rfl)
lemma z64 {R:Type} [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (b:R) (i : ℕ) (x:z56 R M N i) :
  z57 M (b•LinearMap.id (R:=R) (M:=N)) i x=b•x:=by
 let PN:=projectiveResolution (ModuleCat.of R N);let F:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M);let e:z56 R M N i ≅ ((F.mapHomologicalComplex _).obj PN.complex).homology i:=PN.isoLeftDerivedObj F i;let q4:ModuleCat.of R N ⟶ ModuleCat.of R N:=ModuleCat.ofHom (b•LinearMap.id)
 let q2:PN.complex ⟶ PN.complex :=
  {
   f:=fun k=>ModuleCat.ofHom (b•LinearMap.id)
   comm':=fun k l _=>by
    apply ModuleCat.hom_ext;apply LinearMap.ext;intro y
    exact map_smul (PN.complex.d k l).hom b y }
 have q5:(q2.f 0 ≫ PN.π.f 0)=(PN.π.f 0 ≫ q4):=by
  apply ModuleCat.hom_ext;apply LinearMap.ext;intro y;exact map_smul (PN.π.f 0).hom b y
 have q6:=ProjectiveResolution.isoLeftDerivedObj_hom_naturality q4 PN PN q2 q5 F i
 have q1:((F.mapHomologicalComplex _).map q2) =
   {
    f:=fun k=>ModuleCat.ofHom (b•LinearMap.id)
    comm':=fun k l _=>by
     apply ModuleCat.hom_ext;apply LinearMap.ext;intro t
     exact map_smul (((F.mapHomologicalComplex _).obj PN.complex).d k l).hom b t }:=by
  apply HomologicalComplex.hom_ext;intro k;apply ModuleCat.hom_ext;apply TensorProduct.ext';intro m p;change m ⊗ₜ[R] (b•p)=b•(m ⊗ₜ[R] p);rw [TensorProduct.tmul_smul]
 have q0:∀ y:((F.mapHomologicalComplex _).obj PN.complex).homology i,(HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map q2) i).hom y=b•y:=by
  intro y;let K:=(F.mapHomologicalComplex _).obj PN.complex;have q3:Surjective (K.homologyπ i):=(ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance;obtain ⟨c,rfl⟩:=q3 y
  have h1:(HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map q2) i).hom
    ((K.homologyπ i).hom c) =
    (K.homologyπ i).hom ((HomologicalComplex.cyclesMap ((F.mapHomologicalComplex _).map q2) i).hom c) :=
   congrArg (fun φ : K.cycles i ⟶ K.homology i => φ.hom c)
    (HomologicalComplex.homologyπ_naturality ((F.mapHomologicalComplex _).map q2) i)
  rw [h1,← map_smul];congr 1;apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
  have h2:(K.iCycles i).hom
    ((HomologicalComplex.cyclesMap ((F.mapHomologicalComplex _).map q2) i).hom c) =
    (((F.mapHomologicalComplex _).map q2).f i).hom ((K.iCycles i).hom c) :=
   congrArg (fun φ : K.cycles i ⟶ K.X i => φ.hom c)
    (HomologicalComplex.cyclesMap_i ((F.mapHomologicalComplex _).map q2) i)
  rw [h2,map_smul,q1];rfl
 apply e.toLinearEquiv.injective
 have h1:e.hom.hom (z57 M (b•LinearMap.id) i x)=(HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map q2) i).hom (e.hom.hom x) :=
  congrArg (fun φ : z56 R M N i ⟶ _ => φ.hom x) q6
 change e.hom.hom (z57 M (b•LinearMap.id) i x)=e.hom.hom (b•x);rw [h1,q0,map_smul]
lemma z65 {R:Type} [CommRing R]
  {A B C:Type} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  (i:A →ₗ[R] B) (p:B →ₗ[R] C)
  (hi:Injective i) (hp:Surjective p)
  (hip:LinearMap.range i=LinearMap.ker p)
  (N:Type) [AddCommGroup N] [Module R N] :
  ∃ δ : ∀ n : ℕ,z56 R C N (n+1) →ₗ[R] z56 R A N n,(∀ n,Function.Exact (δ n) (z58 i N n))∧(∀ n,Function.Exact (z58 i N n) (z58 p N n))∧(∀ n,Function.Exact (z58 p N (n+1)) (δ n)):=by
 let PN:=projectiveResolution (ModuleCat.of R N);let FA:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R A);let FB:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R B);let FC:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R C);let KA:=(FA.mapHomologicalComplex (ComplexShape.down ℕ)).obj PN.complex;let KB:=(FB.mapHomologicalComplex (ComplexShape.down ℕ)).obj PN.complex
 let KC:=(FC.mapHomologicalComplex (ComplexShape.down ℕ)).obj PN.complex;let ηi:FA ⟶ FB:=(tensoringLeft (ModuleCat.{0} R)).map (ModuleCat.ofHom i);let ηp:FB ⟶ FC:=(tensoringLeft (ModuleCat.{0} R)).map (ModuleCat.ofHom p);let fi:KA ⟶ KB:=(NatTrans.mapHomologicalComplex ηi (ComplexShape.down ℕ)).app PN.complex
 let fp:KB ⟶ KC:=(NatTrans.mapHomologicalComplex ηp (ComplexShape.down ℕ)).app PN.complex
 have q5:(fi ≫ fp)=0:=by
  apply HomologicalComplex.hom_ext;intro n
  have hpi:p.comp i=0:=by
   ext a;rw [LinearMap.comp_apply,LinearMap.zero_apply,← LinearMap.mem_ker,← hip];exact ⟨a,rfl⟩
  apply ModuleCat.hom_ext;apply TensorProduct.ext';intro a y;change p (i a) ⊗ₜ[R] y=0;have : p (i a)=0:=LinearMap.congr_fun hpi a;rw [this,zero_tmul]
 let S:ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ):=ShortComplex.mk fi fp q5
 have q3:S.ShortExact:=by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact;intro n;have q1:Module.Projective R (PN.complex.X n):=ModuleCat.projective_of_module_projective (P:=PN.complex.X n);have q2:Module.Flat R (PN.complex.X n):=inferInstance
  have q4:Mono (S.map (HomologicalComplex.eval _ _ n)).f:=by
   rw [ModuleCat.mono_iff_injective];exact Module.Flat.rTensor_preserves_injective_linearMap i hi
  have q7:Epi (S.map (HomologicalComplex.eval _ _ n)).g:=by
   rw [ModuleCat.epi_iff_surjective];exact LinearMap.rTensor_surjective (PN.complex.X n) hp
  have hex:(S.map (HomologicalComplex.eval _ _ n)).Exact:=by
   rw [ShortComplex.moduleCat_exact_iff];intro x hx;exact (rTensor_exact (PN.complex.X n) (LinearMap.exact_iff.mpr hip.symm) hp x).mp hx
  exact { exact:=hex,mono_f:=q4,epi_g:=q7 }
 let eA (n : ℕ) : z56 R A N n ≅ KA.homology n:=PN.isoLeftDerivedObj FA n;let eB (n : ℕ) : z56 R B N n ≅ KB.homology n:=PN.isoLeftDerivedObj FB n;let eC (n : ℕ) : z56 R C N n ≅ KC.homology n:=PN.isoLeftDerivedObj FC n;let δ (n : ℕ) : z56 R C N (n+1) →ₗ[R] z56 R A N n:=((eC (n+1)).hom ≫ q3.δ (n+1) n rfl ≫ (eA n).inv).hom
 have q0:∀ {X Y:Type} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
   (f:X →ₗ[R] Y) (n : ℕ) (x:z56 R X N n),
   let FX:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R X);let FY:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R Y);let η : FX ⟶ FY:=(tensoringLeft (ModuleCat.{0} R)).map (ModuleCat.ofHom f);let φ := (NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app PN.complex
   (PN.isoLeftDerivedObj FY n).hom.hom (z58 f N n x)=(HomologicalComplex.homologyMap φ n).hom ((PN.isoLeftDerivedObj FX n).hom.hom x):=by
  intro X Y _ _ _ _ f n x FX FY η φ;have h0:=ProjectiveResolution.leftDerived_app_eq η PN n
  have h1:CategoryStruct.comp ((NatTrans.leftDerived η n).app (ModuleCat.of R N))
    (PN.isoLeftDerivedObj FY n).hom =
    CategoryStruct.comp (PN.isoLeftDerivedObj FX n).hom
     ((HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) n).map φ):=by
   rw [h0,Category.assoc,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact congrArg (fun ψ : z56 R X N n ⟶ ((FY.mapHomologicalComplex _).obj PN.complex).homology n =>
   ψ.hom x) h1
 have htor_i (n : ℕ) (x:z56 R A N n) :
   (eB n).hom.hom (z58 i N n x)=(HomologicalComplex.homologyMap S.f n).hom ((eA n).hom.hom x) :=
  q0 i n x
 have htor_p (n : ℕ) (x:z56 R B N n) :
   (eC n).hom.hom (z58 p N n x)=(HomologicalComplex.homologyMap S.g n).hom ((eB n).hom.hom x) :=
  q0 p n x
 have iso_hom_inv {X Y:ModuleCat.{0} R} (e:X ≅ Y) (y:Y) : e.hom.hom (e.inv.hom y)=y :=
  congrArg (fun φ : Y ⟶ Y => φ.hom y) e.inv_hom_id
 have iso_inv_hom {X Y:ModuleCat.{0} R} (e:X ≅ Y) (x:X) : e.inv.hom (e.hom.hom x)=x :=
  congrArg (fun φ : X ⟶ X => φ.hom x) e.hom_inv_id
 refine ⟨δ,?_,?_,?_⟩
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q3.homology_exact₁ (n+1) n rfl)
  have h1:z58 i N n x=0↔(HomologicalComplex.homologyMap S.f n).hom ((eA n).hom.hom x)=0:=by
   rw [← htor_i n x];exact (eB n).toLinearEquiv.map_eq_zero_iff.symm
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eA n).hom.hom x) hx
   refine ⟨(eC (n+1)).inv.hom y,?_⟩
   change (eA n).inv.hom ((q3.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom ((eC (n+1)).inv.hom y)))=x;rw [iso_hom_inv (eC (n+1)) y,hy];exact iso_inv_hom (eA n) x
  ·
   rintro ⟨z,rfl⟩
   have q6:=congrArg (fun φ : S.X₃.homology (n+1) ⟶ S.X₂.homology n =>
    φ.hom ((eC (n+1)).hom.hom z)) (q3.δ_comp (n+1) n rfl)
   change (HomologicalComplex.homologyMap S.f n).hom
    ((eA n).hom.hom ((eA n).inv.hom ((q3.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom z))))=0
   rw [iso_hom_inv (eA n)];exact q6
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q3.homology_exact₂ n)
  have h1:z58 p N n x=0↔(HomologicalComplex.homologyMap S.g n).hom ((eB n).hom.hom x)=0:=by
   rw [← htor_p n x];exact (eC n).toLinearEquiv.map_eq_zero_iff.symm
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eB n).hom.hom x) hx
   refine ⟨(eA n).inv.hom y,?_⟩
   apply (eB n).toLinearEquiv.injective;change (eB n).hom.hom (z58 i N n ((eA n).inv.hom y))=(eB n).hom.hom x;rw [htor_i n,iso_hom_inv (eA n) y,hy]
  ·
   rintro ⟨z,rfl⟩;rw [htor_i n]
   have hzero':(HomologicalComplex.homologyMap S.f n ≫ HomologicalComplex.homologyMap S.g n)=0:=by
    rw [← HomologicalComplex.homologyMap_comp,S.zero,HomologicalComplex.homologyMap_zero]
   exact congrArg (fun φ : S.X₁.homology n ⟶ S.X₃.homology n => φ.hom ((eA n).hom.hom z)) hzero'
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (q3.homology_exact₃ (n+1) n rfl)
  have h1 : δ n x=0↔(q3.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom x)=0:=by
   change (eA n).inv.hom ((q3.δ (n+1) n rfl).hom ((eC (n+1)).hom.hom x))=0↔_;exact (eA n).toLinearEquiv.symm.map_eq_zero_iff
  rw [h1];constructor
  ·
   intro hx;obtain ⟨y,hy⟩:=hex ((eC (n+1)).hom.hom x) hx
   refine ⟨(eB (n+1)).inv.hom y,?_⟩
   apply (eC (n+1)).toLinearEquiv.injective;change (eC (n+1)).hom.hom (z58 p N (n+1) ((eB (n+1)).inv.hom y))=(eC (n+1)).hom.hom x;rw [htor_p (n+1),iso_hom_inv (eB (n+1)) y,hy]
  ·
   rintro ⟨z,rfl⟩;rw [htor_p (n+1)]
   exact congrArg (fun φ : S.X₂.homology (n+1) ⟶ S.X₁.homology n =>
    φ.hom ((eB (n+1)).hom.hom z)) (q3.comp_δ (n+1) n rfl)
lemma z66 {R:Type} [CommRing R]
  {A B:Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  (f:A →ₗ[R] B) (N:Type) [AddCommGroup N] [Module R N] (x:z56 R A N 0) :
  z59 R B N (z58 f N 0 x)=LinearMap.rTensor N f (z59 R A N x):=by
 let PN:=projectiveResolution (ModuleCat.of R N);let FA:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R A);let FB:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R B);let η : FA ⟶ FB:=(tensoringLeft (ModuleCat.{0} R)).map (ModuleCat.ofHom f)
 have hop:CategoryStruct.comp
   (HomologicalComplex.opcyclesMap ((NatTrans.mapHomologicalComplex η _).app PN.complex) 0)
   (PN.fromLeftDerivedZero' FB) =
   CategoryStruct.comp (PN.fromLeftDerivedZero' FA) (η.app (ModuleCat.of R N)):=by
  simp only [← cancel_epi (HomologicalComplex.pOpcycles _ _),HomologicalComplex.p_opcyclesMap_assoc,ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero',ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero'_assoc];exact (η.naturality (PN.π.f 0)).symm
 have h1:CategoryStruct.comp ((NatTrans.leftDerived η 0).app (ModuleCat.of R N))
   (FB.fromLeftDerivedZero.app (ModuleCat.of R N)) =
   CategoryStruct.comp (FA.fromLeftDerivedZero.app (ModuleCat.of R N))
    (η.app (ModuleCat.of R N)):=by
  rw [ProjectiveResolution.fromLeftDerivedZero_eq PN FA,ProjectiveResolution.fromLeftDerivedZero_eq PN FB,ProjectiveResolution.leftDerived_app_eq η PN 0];simp only [Category.assoc,Iso.inv_hom_id_assoc];congr 1;let φ := (NatTrans.mapHomologicalComplex η (ComplexShape.down ℕ)).app PN.complex
  have hι : CategoryStruct.comp (HomologicalComplex.homologyMap φ 0)
    (HomologicalComplex.homologyι ((FB.mapHomologicalComplex _).obj PN.complex) 0) =
    CategoryStruct.comp
     (HomologicalComplex.homologyι ((FA.mapHomologicalComplex _).obj PN.complex) 0)
     (HomologicalComplex.opcyclesMap φ 0) :=
   HomologicalComplex.homologyι_naturality φ 0
  change CategoryStruct.comp (HomologicalComplex.homologyMap φ 0)
   (CategoryStruct.comp (HomologicalComplex.homologyι ((FB.mapHomologicalComplex _).obj PN.complex) 0)
    (PN.fromLeftDerivedZero' FB)) =
   CategoryStruct.comp
    (HomologicalComplex.homologyι ((FA.mapHomologicalComplex _).obj PN.complex) 0)
    (CategoryStruct.comp (PN.fromLeftDerivedZero' FA) (η.app (ModuleCat.of R N)))
  rw [← Category.assoc,hι,Category.assoc,hop]
 exact congrArg (fun φ : z56 R A N 0 ⟶ ModuleCat.of R (B ⊗[R] N) => φ.hom x) h1
lemma z67 {R:Type} [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [Module.Flat R M]
  [AddCommGroup N] [Module R N] (i : ℕ) :
  Subsingleton (z56 R M N (i+1)):=by
 let PN:=projectiveResolution (ModuleCat.of R N);let F:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M);let e:z56 R M N (i+1) ≅ ((F.mapHomologicalComplex _).obj PN.complex).homology (i+1):=PN.isoLeftDerivedObj F (i+1)
 have hex:((F.mapHomologicalComplex _).obj PN.complex).ExactAt (i+1):=by
  rw [HomologicalComplex.exactAt_iff' _ (i+2) (i+1) i (by simp) (by simp)];rw [ShortComplex.moduleCat_exact_iff]
  have q1:Function.Exact (PN.complex.d (i+2) (i+1)).hom (PN.complex.d (i+1) i).hom:=by
   intro x;constructor
   · exact (ShortComplex.moduleCat_exact_iff _).mp (PN.exact_succ i) x
   ·
    rintro ⟨y,rfl⟩
    exact congrArg (fun φ : PN.complex.X (i+2) ⟶ PN.complex.X i => φ.hom y)
     (PN.complex.d_comp_d (i+2) (i+1) i)
  intro t ht;exact (Module.Flat.lTensor_exact M q1 t).mp ht
 have q0:IsZero (((F.mapHomologicalComplex _).obj PN.complex).homology (i+1)):=hex.isZero_homology;exact ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_iso q0 e)
private lemma z68 {R:Type} [CommRing R]
  {A B C:ModuleCat.{0} R}
  (f:A →ₗ[R] B) (g:B →ₗ[R] C) (hf:Injective f) (hfg:Function.Exact f g) :
  Nonempty (A ≃ₗ[R] LinearMap.ker g):=by
 refine ⟨LinearEquiv.ofBijective
  {
   toFun:=fun a=>⟨f a,LinearMap.mem_ker.mpr ((hfg (f a)).mpr ⟨a,rfl⟩)⟩
   map_add':=fun x y=>Subtype.ext (map_add f x y)
   map_smul':=fun r x=>Subtype.ext (map_smul f r x) }
  ⟨fun x y h=>hf (congrArg Subtype.val h),fun ⟨b,hb⟩=>let ⟨a,ha⟩:=(hfg b).mp (LinearMap.mem_ker.mp hb);⟨a,Subtype.ext ha⟩⟩⟩
private lemma z69 {R:Type} [CommRing R]
    {A B A' B':ModuleCat.{0} R}
    (f:A →ₗ[R] B) (f':A' →ₗ[R] B')
    (eA:A ≃ₗ[R] A') (eB:B ≃ₗ[R] B')
    (hsq:∀ a,eB (f a)=f' (eA a)) :
    Nonempty (LinearMap.ker f ≃ₗ[R] LinearMap.ker f') :=
  ⟨{ toFun:=fun x=>⟨eA x.1,by rw [LinearMap.mem_ker,← hsq x.1,LinearMap.mem_ker.mp x.2,map_zero]⟩
     invFun:=fun y=>⟨eA.symm y.1,by
       rw [LinearMap.mem_ker];apply eB.injective;rw [map_zero,hsq,eA.apply_symm_apply]
       exact LinearMap.mem_ker.mp y.2⟩
     map_add':=fun _ _=>Subtype.ext (map_add eA _ _)
     map_smul':=fun _ _=>Subtype.ext (map_smul eA _ _)
     left_inv:=fun _=>Subtype.ext (eA.symm_apply_apply _)
     right_inv:=fun _=>Subtype.ext (eA.apply_symm_apply _) }⟩
private lemma z70 {R M N F K:Type} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup F] [Module R F] [Module.Projective R F] [Module.Flat R F]
  [AddCommGroup K] [Module R K]
  (incl:K →ₗ[R] F) (p:F →ₗ[R] M)
  (q1:Injective incl) (hp:Surjective p)
  (hex:LinearMap.range incl=LinearMap.ker p) :
  Nonempty (z56 R M N 1 ≃ₗ[R] z56 R N M 1) ∧
  (∀ k : ℕ,Nonempty (z56 R K N (k+1) ≃ₗ[R] z56 R N K (k+1))→Nonempty (z56 R M N (k+2) ≃ₗ[R] z56 R N M (k+2))):=by
 obtain ⟨δL,hL1,_,hL3⟩:=z65 incl p q1 hp hex N;obtain ⟨δR,hR1,_,hR3⟩:=z63 N incl p q1 hp hex;constructor
 ·
  have : Subsingleton (z56 R F N 1):=z67 F N 0;have : Subsingleton (z56 R N F 1):=z61 N F 0
  have hδL_inj:Injective (δL 0):=by
   rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hL3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
  have hδR_inj:Injective (δR 0):=by
   rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hR3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
  obtain ⟨eL1⟩:=z68 (δL 0) (z58 incl N 0) hδL_inj (hL1 0);obtain ⟨eR1⟩:=z68 (δR 0) (z57 N incl 0) hδR_inj (hR1 0);let q2:z56 R K N 0 ≃ₗ[R] z56 R N K 0:=(z59 R K N).trans ((TensorProduct.comm R K N).trans (z59 R N K).symm);let q0:z56 R F N 0 ≃ₗ[R] z56 R N F 0:=(z59 R F N).trans ((TensorProduct.comm R F N).trans (z59 R N F).symm)
  have hsq:∀ x:z56 R K N 0,q0 (z58 incl N 0 x)=z57 N incl 0 (q2 x):=fun x=>by
   apply (z59 R N F).injective;rw [z60];simp only [q0,q2,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,z66]
   generalize z59 R K N x=t
   induction t using TensorProduct.induction_on with
   | zero=>simp
   | tmul k n=>simp
   | add t₁ t₂ ih₁ ih₂=>simp [ih₁,ih₂]
  obtain ⟨eKer⟩:=z69 (z58 incl N 0) (z57 N incl 0) q2 q0 hsq;exact ⟨eL1.trans (eKer.trans eR1.symm)⟩
 ·
  intro k ⟨eIH⟩;have : Subsingleton (z56 R F N (k+2)):=z67 F N (k+1);have : Subsingleton (z56 R N F (k+2)):=z61 N F (k+1);have : Subsingleton (z56 R F N (k+1)):=z67 F N k;have : Subsingleton (z56 R N F (k+1)):=z61 N F k
  have hδL_bij:Bijective (δL (k+1)):=by
   constructor
   ·
    rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hL3 (k+1) x).mp hx;rw [Subsingleton.elim y 0,map_zero]
   · intro y;exact (hL1 (k+1) y).mp (Subsingleton.elim _ 0)
  have hδR_bij:Bijective (δR (k+1)):=by
   constructor
   ·
    rw [injective_iff_map_eq_zero];intro x hx;obtain ⟨y,rfl⟩:=(hR3 (k+1) x).mp hx;rw [Subsingleton.elim y 0,map_zero]
   · intro y;exact (hR1 (k+1) y).mp (Subsingleton.elim _ 0)
  exact ⟨(LinearEquiv.ofBijective (δL (k+1)) hδL_bij).trans
   (eIH.trans (LinearEquiv.ofBijective (δR (k+1)) hδR_bij).symm)⟩
lemma z71 {R:Type} [CommRing R] :
  ∀ (i : ℕ) (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],Nonempty (z56 R M N i ≃ₗ[R] z56 R N M i):=by
 intro i
 induction i with
 | zero =>
  intro M N _ _ _ _;exact ⟨(z59 R M N).trans ((TensorProduct.comm R M N).trans (z59 R N M).symm)⟩
 | succ i ih =>
  intro M N _ _ _ _;let F:=M →₀ R;let p:F →ₗ[R] M:=Finsupp.linearCombination R id
  have hp:Surjective p:=fun m =>
   ⟨Finsupp.single m 1,by
    dsimp only [p]
    rw [Finsupp.linearCombination_single,one_smul,id_eq]⟩
  let K:=LinearMap.ker p
  have q0:=z70 (R:=R) (M:=M) (N:=N) (F:=F) (K := ↥K)
   K.subtype p Subtype.val_injective hp (Submodule.range_subtype K)
  cases i with
  | zero=>exact q0.1
  | succ k=>exact q0.2 k (ih (↥K) N)
lemma z72 {R:Type} [CommRing R]
  (M N:Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
  intersectionMultiplicity R M N=intersectionMultiplicity R N M:=by
 unfold intersectionMultiplicity
 refine finsum_congr fun i => ?_
 obtain ⟨e⟩:=z71 (R:=R) i M N;rw [e.length_eq]
set_option maxHeartbeats 800000 in
lemma z73 {R₁ S₁ : Type} [CommRing R₁] [IsNoetherianRing R₁]
  [CommRing S₁] [IsLocalRing S₁] [IsNoetherianRing S₁] [Algebra R₁ S₁]
  (x:R₁) (q24:algebraMap R₁ S₁ x∈maximalIdeal S₁)
  (q37:IsSMulRegular R₁ x) (q36:IsSMulRegular S₁ (algebraMap R₁ S₁ x))
  (q4 :
   let R₀ := R₁ ⧸ span {x};let S₀ := S₁ ⧸ span {algebraMap R₁ S₁ x}
   let f₀ : R₀ →+* S₀ := Ideal.Quotient.lift (span {x})
    ((Ideal.Quotient.mk (span {algebraMap R₁ S₁ x})).comp (algebraMap R₁ S₁))
    (fun a ha=>by
     obtain ⟨r,rfl⟩:=mem_span_singleton.mp ha;rw [RingHom.comp_apply,map_mul,Ideal.Quotient.eq_zero_iff_mem]
     exact Ideal.mul_mem_right _ _ (subset_span rfl))
   letI : Algebra R₀ S₀ := f₀.toAlgebra
   Module.Flat R₀ S₀) :
  Module.Flat R₁ S₁ := by
 let R₀ := R₁ ⧸ span {x};let S₀ := S₁ ⧸ span {algebraMap R₁ S₁ x}
 let f₀ : R₀ →+* S₀ := Ideal.Quotient.lift (span {x})
  ((Ideal.Quotient.mk (span {algebraMap R₁ S₁ x})).comp (algebraMap R₁ S₁))
  (fun a ha=>by
   obtain ⟨r,rfl⟩:=mem_span_singleton.mp ha;rw [RingHom.comp_apply,map_mul,Ideal.Quotient.eq_zero_iff_mem]
   exact Ideal.mul_mem_right _ _ (subset_span rfl))
 let : Algebra R₀ S₀ := f₀.toAlgebra;have : Module.Flat R₀ S₀ := q4
 have q10:Subsingleton (z56 R₁ S₁ R₀ 1):=by
  let q25:R₁ →ₗ[R₁] R₁ := x•LinearMap.id;have q5:Injective q25:=q37;have q11:Surjective (span {x}).mkQ:=Submodule.mkQ_surjective _
  have q34:LinearMap.range q25=LinearMap.ker (span {x}).mkQ:=by
   rw [Submodule.ker_mkQ];ext r;simp only [LinearMap.mem_range,q25,LinearMap.smul_apply,LinearMap.id_apply,smul_eq_mul,mem_span_singleton,dvd_def]
   exact ⟨fun ⟨a,ha⟩=>⟨a,ha.symm⟩,fun ⟨a,ha⟩=>⟨a,ha.symm⟩⟩
  obtain ⟨δ,h1,_,h3⟩:=z63 S₁ q25 (span {x}).mkQ q5 q11 q34;have : Subsingleton (z56 R₁ S₁ R₁ 1):=z61 S₁ R₁ 0
  refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
  have hδ0 : δ 0 z=0:=by
   apply (z59 R₁ S₁ R₁).injective;rw [map_zero];apply (TensorProduct.rid R₁ S₁).injective;rw [map_zero];apply q36;dsimp only;rw [smul_eq_mul,smul_eq_mul,mul_zero];have q30:z57 S₁ q25 0 (δ 0 z)=0:=(h1 0 (δ 0 z)).mpr ⟨z,rfl⟩;have h2:=congrArg (TensorProduct.rid R₁ S₁ ∘ z59 R₁ S₁ R₁) q30;simp only [Function.comp_apply,map_zero,z60] at h2
   have h3':∀ t:S₁ ⊗[R₁] R₁,
     TensorProduct.rid R₁ S₁ (LinearMap.lTensor S₁ q25 t)=algebraMap R₁ S₁ x*TensorProduct.rid R₁ S₁ t:=fun t=>by
    induction t using TensorProduct.induction_on with
    | zero=>simp
    | tmul s r =>
     rw [LinearMap.lTensor_tmul,TensorProduct.rid_tmul,TensorProduct.rid_tmul];change (x*r)•s=algebraMap R₁ S₁ x*(r•s);rw [Algebra.smul_def,Algebra.smul_def,map_mul];ring
    | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂,mul_add]
   rw [← h3'];exact h2
  obtain ⟨w,hw⟩:=(h3 0 z).mp hδ0;rw [← hw,Subsingleton.elim w 0,map_zero]
 have q2:∀ m : ℕ,Subsingleton (z56 R₁ S₁ (Fin m→R₀) 1):=by
  intro m
  induction m with
  | zero =>
   have : Module.Projective R₁ (Fin 0→R₀) :=
    Module.Projective.of_split (0:(Fin 0→R₀) →ₗ[R₁] (Fin 0→R₁)) 0
     (by ext f i;exact Fin.elim0 i)
   exact z61 S₁ (Fin 0→R₀) 0
  | succ m ih =>
   let i0:R₀ →ₗ[R₁] (Fin (m+1)→R₀) :=
    {
     toFun:=fun a=>Fin.cons a 0
     map_add':=fun a b=>by ext i;refine Fin.cases rfl (fun _=>by simp) i
     map_smul':=fun r a=>by ext i;refine Fin.cases rfl (fun _=>by simp) i }
   let p0:(Fin (m+1)→R₀) →ₗ[R₁] (Fin m→R₀) :=
    {
     toFun:=fun f j=>f j.succ
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl }
   have hi0:Injective i0:=fun a b h=>congrFun h 0
   have hp0:Surjective p0:=fun f=>⟨Fin.cons 0 f,by ext j;rfl⟩
   have q34:LinearMap.range i0=LinearMap.ker p0:=by
    ext f;simp only [LinearMap.mem_range,LinearMap.mem_ker,i0,p0,LinearMap.coe_mk,AddHom.coe_mk];constructor
    · rintro ⟨a,rfl⟩;ext j;rfl
    ·
     intro hf;refine ⟨f 0,?_⟩;ext i
     refine Fin.cases rfl (fun j => ?_) i
     exact (congrFun hf j).symm
   obtain ⟨_,_,h2,_⟩:=z63 S₁ i0 p0 hi0 hp0 q34
   refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
   have hpz:z57 S₁ p0 1 z=0:=Subsingleton.elim _ 0;obtain ⟨w,rfl⟩:=(h2 1 z).mp hpz;rw [Subsingleton.elim w 0,map_zero]
 have q3:∀ (M:Type) [AddCommGroup M] [Module R₁ M] [Module.Finite R₁ M],(∀ m:M,x•m=0)→Subsingleton (z56 R₁ S₁ M 1):=by
  intro M _ _ _ hMx
  let : Module R₀ M :=
   {
    smul:=fun r m=>Quotient.liftOn' r (fun a=>a•m) (fun a b hab=>by
     have q33:b - a∈span {x}:=by
      simpa [sub_eq_neg_add] using QuotientAddGroup.leftRel_apply.mp hab
     obtain ⟨c,hc⟩:=mem_span_singleton.mp q33
     have hba:b=a+x*c:=by rw [← hc];ring
     rw [hba,add_smul,mul_comm,mul_smul,hMx,smul_zero,add_zero])
    one_smul:=fun m=>one_smul R₁ m
    mul_smul:=fun r s m=>Quotient.inductionOn₂' r s fun a b=>mul_smul a b m
    smul_zero:=fun r=>Quotient.inductionOn' r fun a=>smul_zero a
    smul_add:=fun r m₁ m₂=>Quotient.inductionOn' r fun a=>smul_add a m₁ m₂
    add_smul:=fun r s m=>Quotient.inductionOn₂' r s fun a b=>add_smul a b m
    zero_smul:=fun m=>zero_smul R₁ m }
  have : IsScalarTower R₁ R₀ M:=⟨fun a r m=>Quotient.inductionOn' r fun b=>mul_smul a b m⟩
  obtain ⟨T,hT⟩:=Module.Finite.fg_top (R:=R₁) (M:=M);let m:=T.card;let eT:Fin m ≃ T:=(Fintype.equivFinOfCardEq (Fintype.card_coe T)).symm
  let pM:(Fin m→R₀) →ₗ[R₀] M :=
   {
    toFun:=fun g => ∑ i:Fin m,g i•(eT i:M)
    map_add':=fun g₁ g₂=>by simp [add_smul,Finset.sum_add_distrib]
    map_smul':=fun r g=>by simp [Finset.smul_sum,mul_smul] }
  have q13:Surjective pM:=fun y=>by
   have hy:y∈Submodule.span R₁ (T:Set M):=hT▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hy;obtain ⟨c,_,rfl⟩:=hy
   refine ⟨fun i=>Ideal.Quotient.mk (span {x}) (c (eT i).1),?_⟩
   change ∑ i:Fin m,c (eT i).1•(eT i:M) = ∑ t∈T,c t•t
   rw [← Finset.sum_coe_sort T (fun t=>c t•t)]
   exact Fintype.sum_equiv eT _ _ fun _=>rfl
  let K:=LinearMap.ker pM;let iK:K →ₗ[R₀] (Fin m→R₀):=K.subtype;have q18:Injective iK:=Subtype.val_injective;let iK₁ : K →ₗ[R₁] (Fin m→R₀):=iK.restrictScalars R₁;let pM₁ : (Fin m→R₀) →ₗ[R₁] M:=pM.restrictScalars R₁
  have q34:LinearMap.range iK₁ = LinearMap.ker pM₁ := by
   ext g
   exact ⟨fun ⟨⟨y,hy⟩,h⟩=>h▸hy,fun hg=>⟨⟨g,hg⟩,rfl⟩⟩
  obtain ⟨δ,h1,_,h3⟩:=z63 S₁ iK₁ pM₁ q18 q13 q34;have : Subsingleton (z56 R₁ S₁ (Fin m→R₀) 1):=q2 m
  have q1:Injective (LinearMap.lTensor S₁ iK₁):=by
   have q8:∀ (N:Type) [AddCommGroup N] [Module R₁ N] [Module R₀ N] [IsScalarTower R₁ R₀ N],
     ∃ e:(S₁ ⊗[R₁] N) ≃ₗ[R₁] (S₀ ⊗[R₀] N),∀ (s:S₁) (n:N),e (s ⊗ₜ[R₁] n)=Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s ⊗ₜ[R₀] n:=by
    intro N _ _ _ _
    let fwd:(S₁ ⊗[R₁] N) →ₗ[R₁] (S₀ ⊗[R₀] N) :=
     TensorProduct.lift
      {
       toFun:=fun s =>
        {
         toFun:=fun n=>Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s ⊗ₜ[R₀] n
         map_add':=fun n₁ n₂=>tmul_add _ _ _
         map_smul':=fun r n=>by
          change Ideal.Quotient.mk _ s ⊗ₜ[R₀] (r•n)=r•(Ideal.Quotient.mk _ s ⊗ₜ[R₀] n);rw [← algebraMap_smul R₀ r n,TensorProduct.tmul_smul];have hL:(algebraMap R₁ R₀ r)•(Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s ⊗ₜ[R₀] n)=((algebraMap R₁ R₀ r)•Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s) ⊗ₜ[R₀] n:=(smul_tmul' _ _ _).symm
          have hR:r•(Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s ⊗ₜ[R₀] n)=(r•Ideal.Quotient.mk (span {algebraMap R₁ S₁ x}) s) ⊗ₜ[R₀] n:=(smul_tmul' _ _ _).symm;rw [hL,hR];congr 1;rw [Algebra.smul_def,Algebra.smul_def]
          rfl }
       map_add':=fun s₁ s₂=>by ext n;simp [add_tmul]
       map_smul':=fun r s=>by
        ext n;let mkS:S₁ →+* S₀ := Ideal.Quotient.mk (span {algebraMap R₁ S₁ x});change mkS (r•s) ⊗ₜ[R₀] n=r•(mkS s ⊗ₜ[R₀] n)
        have h1:mkS (r•s)=r•mkS s:=by
         rw [Algebra.smul_def,map_mul,Algebra.smul_def];rfl
        rw [h1,smul_tmul'] }
    have hxt:∀ t':S₁ ⊗[R₁] N,x•t'=0:=fun t'=>by
     induction t' using TensorProduct.induction_on with
     | zero=>simp
     | tmul s n =>
      rw [← TensorProduct.tmul_smul,← algebraMap_smul R₀ x n];have hx0:algebraMap R₁ R₀ x=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (subset_span rfl);rw [hx0,zero_smul,tmul_zero]
     | add t₁ t₂ ih₁ ih₂=>rw [smul_add,ih₁,ih₂,add_zero]
    let : Module R₀ (S₁ ⊗[R₁] N) :=
     {
      smul:=fun r t=>Quotient.liftOn' r (fun a=>a•t) (fun a b hab=>by
       have q33:b - a∈span {x}:=by
        simpa [sub_eq_neg_add] using QuotientAddGroup.leftRel_apply.mp hab
       obtain ⟨c,hc⟩:=mem_span_singleton.mp q33
       have hba:b=a+x*c:=by rw [← hc];ring
       rw [hba,add_smul,mul_comm,mul_smul,hxt,smul_zero,add_zero])
      one_smul:=fun t=>one_smul R₁ t
      mul_smul:=fun r s t=>Quotient.inductionOn₂' r s fun a b=>mul_smul a b t
      smul_zero:=fun r=>Quotient.inductionOn' r fun a=>smul_zero a
      smul_add:=fun r t₁ t₂=>Quotient.inductionOn' r fun a=>smul_add a t₁ t₂
      add_smul:=fun r s t=>Quotient.inductionOn₂' r s fun a b=>add_smul a b t
      zero_smul:=fun t=>zero_smul R₁ t }
    have : IsScalarTower R₁ R₀ (S₁ ⊗[R₁] N):=⟨fun a r t=>Quotient.inductionOn' r fun b=>mul_smul a b t⟩
    let q31:S₁ →ₗ[R₁] (N →ₗ[R₀] (S₁ ⊗[R₁] N)) :=
     {
      toFun:=fun s =>
       {
        toFun:=fun n=>s ⊗ₜ[R₁] n
        map_add':=fun n₁ n₂=>tmul_add s n₁ n₂
        map_smul':=fun r n=>Quotient.inductionOn' r fun a=>by
         change s ⊗ₜ[R₁] (algebraMap R₁ R₀ a•n)=a•(s ⊗ₜ[R₁] n)
         rw [algebraMap_smul,TensorProduct.tmul_smul] }
      map_add':=fun s₁ s₂=>by ext n;exact add_tmul s₁ s₂ n
      map_smul':=fun a s=>by
       ext n;change (a•s) ⊗ₜ[R₁] n=a•(s ⊗ₜ[R₁] n)
       rw [smul_tmul'] }
    let q20:S₀ →ₗ[R₀] (N →ₗ[R₀] (S₁ ⊗[R₁] N)) :=
     {
      toFun:=fun s0=>Quotient.liftOn' s0 (fun s=>q31 s) (fun s₁ s₂ hs=>by
       have q33:s₂ - s₁ ∈ span {algebraMap R₁ S₁ x}:=by
        simpa [sub_eq_neg_add] using QuotientAddGroup.leftRel_apply.mp hs
       obtain ⟨c,hc⟩:=mem_span_singleton.mp q33
       have hs2:s₂ = s₁ + algebraMap R₁ S₁ x*c:=by rw [← hc];ring
       ext n;change s₁ ⊗ₜ[R₁] n=s₂ ⊗ₜ[R₁] n;rw [hs2,add_tmul,← Algebra.smul_def,smul_tmul,← algebraMap_smul R₀ x n];have hx0:algebraMap R₁ R₀ x=0:=Ideal.Quotient.eq_zero_iff_mem.mpr (subset_span rfl)
       rw [hx0,zero_smul,tmul_zero,add_zero])
      map_add':=fun s₁ s₂=>Quotient.inductionOn₂' s₁ s₂ fun a b=>by
       ext n;exact add_tmul a b n
      map_smul':=fun r s0=>Quotient.inductionOn₂' r s0 fun a s=>by
       ext n;change (algebraMap R₁ S₁ a*s) ⊗ₜ[R₁] n=a•(s ⊗ₜ[R₁] n)
       rw [← Algebra.smul_def,smul_tmul'] }
    let bwd:(S₀ ⊗[R₀] N) →ₗ[R₀] (S₁ ⊗[R₁] N):=TensorProduct.lift q20
    let bwd₁ : (S₀ ⊗[R₀] N) →ₗ[R₁] (S₁ ⊗[R₁] N) :=
     {
      toFun:=bwd
      map_add':=bwd.map_add
      map_smul':=fun a t=>by
       induction t using TensorProduct.induction_on with
       | zero=>simp
       | tmul s0 n =>
        refine Quotient.inductionOn' s0 fun s => ?_
        change bwd ((Ideal.Quotient.mk _ (a•s)) ⊗ₜ[R₀] n)=a•(s ⊗ₜ[R₁] n);exact smul_tmul' a s n
       | add t₁ t₂ ih₁ ih₂=>simp [map_add,smul_add,ih₁,ih₂] }
    refine ⟨LinearEquiv.ofLinearMap fwd bwd₁ ?_ ?_,fun s n=>rfl⟩
    ·
     ext t
     induction t using TensorProduct.induction_on with
     | zero=>simp
     | tmul s0 n=>refine Quotient.inductionOn' s0 fun s=>rfl
     | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
    ·
     apply TensorProduct.ext';intro s n;rfl
   obtain ⟨eK,heK⟩:=q8 K;obtain ⟨eF,heF⟩:=q8 (Fin m→R₀)
   have q32:∀ t:S₁ ⊗[R₁] K,eF (LinearMap.lTensor S₁ iK₁ t)=LinearMap.lTensor S₀ iK (eK t):=fun t=>by
    induction t using TensorProduct.induction_on with
    | zero=>simp
    | tmul s k=>simp [heK,heF,iK₁]
    | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
   intro t₁ t₂ ht;apply eK.injective;apply Module.Flat.lTensor_preserves_injective_linearMap iK q18;rw [← q32,← q32,ht]
  refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
  have hδ0 : δ 0 z=0:=by
   apply (z59 R₁ S₁ K).injective;rw [map_zero];apply q1;rw [map_zero,← z60];have q30:z57 S₁ iK₁ 0 (δ 0 z)=0:=(h1 0 (δ 0 z)).mpr ⟨z,rfl⟩;rw [q30,map_zero]
  obtain ⟨w,hw⟩:=(h3 0 z).mp hδ0;rw [← hw,Subsingleton.elim w 0,map_zero]
 have q0:∀ (k : ℕ) (M:Type) [AddCommGroup M] [Module R₁ M] [Module.Finite R₁ M],(∀ m:M,(x ^ k)•m=0)→Subsingleton (z56 R₁ S₁ M 1):=by
  intro k
  induction k with
  | zero =>
   intro M _ _ _ hM0
   have : Subsingleton M:=subsingleton_iff_forall_eq 0 |>.mpr fun m=>by
    simpa using hM0 m
   have : Module.Projective R₁ M:=Module.Projective.of_split (0:M →ₗ[R₁] (Fin 0→R₁)) 0 (by ext m;exact Subsingleton.elim _ _);exact z61 S₁ M 0
  | succ k ih =>
   intro M _ _ _ hMk;let N:Submodule R₁ M:=LinearMap.range (x•LinearMap.id (R:=R₁) (M:=M));have : Module.Finite R₁ N:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)
   have hNk:∀ y:N,(x ^ k)•y=0:=fun ⟨y,hy⟩=>by
    apply Subtype.ext;obtain ⟨m,rfl⟩:=hy;change (x ^ k)•(x•m)=0;rw [← mul_smul,← pow_succ];exact hMk m
   have hQx:∀ q:M⧸N,x•q=0:=fun q=>by
    obtain ⟨m,rfl⟩:=Submodule.Quotient.mk_surjective N q
    change Submodule.Quotient.mk (p:=N) (x•m)=0
    rw [Submodule.Quotient.mk_eq_zero];exact ⟨m,rfl⟩
   have : Subsingleton (z56 R₁ S₁ N 1):=ih N hNk;have : Subsingleton (z56 R₁ S₁ (M⧸N) 1):=q3 (M⧸N) hQx
   obtain ⟨_,_,h2,_⟩:=z63 S₁ N.subtype N.mkQ
    Subtype.val_injective (Submodule.mkQ_surjective N)
    (by rw [Submodule.range_subtype,Submodule.ker_mkQ])
   refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
   obtain ⟨w,rfl⟩:=(h2 1 z).mp (Subsingleton.elim _ 0);rw [Subsingleton.elim w 0,map_zero]
 have q12:∀ (M:Type) [AddCommGroup M] [Module R₁ M] [Module.Finite R₁ M],Subsingleton (z56 R₁ S₁ M 1):=by
  intro M _ _ _
  let M0:Submodule R₁ M :=
   {
    carrier:={ m:M | ∃ k : ℕ,(x ^ k)•m=0 }
    add_mem':=fun {a b} ⟨ka,hka⟩ ⟨kb,hkb⟩=>⟨ka+kb,by
     rw [smul_add,pow_add,mul_smul,mul_smul,hkb,smul_zero,add_zero,smul_comm,hka,smul_zero]⟩
    zero_mem':=⟨0,by simp⟩
    smul_mem':=fun r {a} ⟨k,hk⟩=>⟨k,by rw [smul_comm,hk,smul_zero]⟩ }
  have : Module.Finite R₁ M0:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian M0);obtain ⟨U,hU⟩:=Module.Finite.fg_top (R:=R₁) (M:=M0)
  let Nmax : ℕ := U.sup fun u=>u.2.choose
  have q9:∀ u:M0,(x ^ Nmax)•u=0:=fun u=>by
   have hu:u∈Submodule.span R₁ (U:Set M0):=hU▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hu;obtain ⟨c,_,rfl⟩:=hu;rw [Finset.smul_sum]
   refine Finset.sum_eq_zero fun v hv => ?_
   rw [smul_comm]
   have hle:v.2.choose ≤ Nmax:=Finset.le_sup (f:=fun w:M0=>w.2.choose) hv
   have h0:(x ^ Nmax)•v=0:=by
    apply Subtype.ext;change (x ^ Nmax)•(v:M)=0;rw [← Nat.sub_add_cancel hle,pow_add,mul_smul,v.2.choose_spec,smul_zero]
   rw [h0,smul_zero]
  have : Subsingleton (z56 R₁ S₁ M0 1):=q0 Nmax M0 q9;let Mbar:=M⧸M0
  have q15:Injective (x•LinearMap.id (R:=R₁) (M:=Mbar)):=by
   rw [injective_iff_map_eq_zero];intro q hq;obtain ⟨m,rfl⟩:=Submodule.Quotient.mk_surjective M0 q
   change Submodule.Quotient.mk (p:=M0) (x•m)=0 at hq
   rw [Submodule.Quotient.mk_eq_zero] at hq;obtain ⟨k,hk⟩:=hq;rw [Submodule.Quotient.mk_eq_zero]
   refine ⟨k+1,?_⟩
   rw [pow_succ,mul_smul];exact hk
  have q6:Subsingleton (z56 R₁ S₁ Mbar 1):=by
   let q29:Submodule R₁ Mbar:=LinearMap.range (x•LinearMap.id (R:=R₁) (M:=Mbar));let Qbar:=Mbar⧸q29
   have q16:∀ q:Qbar,x•q=0:=fun q=>by
    obtain ⟨m,rfl⟩:=Submodule.Quotient.mk_surjective q29 q
    change Submodule.Quotient.mk (p:=q29) (x•m)=0
    rw [Submodule.Quotient.mk_eq_zero];exact ⟨m,rfl⟩
   have : Subsingleton (z56 R₁ S₁ Qbar 1):=q3 Qbar q16;have q21:LinearMap.range (x•LinearMap.id (R:=R₁) (M:=Mbar))=LinearMap.ker q29.mkQ:=(Submodule.ker_mkQ q29).symm
   obtain ⟨_,_,h2_x,_⟩:=z63 S₁ (x•LinearMap.id (R:=R₁) (M:=Mbar))
    q29.mkQ q15 (Submodule.mkQ_surjective q29) q21
   have q17:Surjective (fun z:z56 R₁ S₁ Mbar 1=>x•z):=fun z=>by
    obtain ⟨w,hw⟩:=(h2_x 1 z).mp (Subsingleton.elim _ 0);exact ⟨w,(z64 S₁ Mbar x 1 w).symm.trans hw⟩
   obtain ⟨Tm,hTm⟩:=Module.Finite.fg_top (R:=R₁) (M:=Mbar);let r:=Tm.card;let eTm:Fin r ≃ Tm:=(Fintype.equivFinOfCardEq (Fintype.card_coe Tm)).symm
   let pF:(Fin r→R₁) →ₗ[R₁] Mbar :=
    {
     toFun:=fun g => ∑ i:Fin r,g i•(eTm i:Mbar)
     map_add':=fun g₁ g₂=>by simp [add_smul,Finset.sum_add_distrib]
     map_smul':=fun a g=>by simp [Finset.smul_sum,mul_smul] }
   have q7:Surjective pF:=fun y=>by
    have hy:y∈Submodule.span R₁ (Tm:Set Mbar):=hTm▸Submodule.mem_top;rw [Submodule.mem_span_finset] at hy;obtain ⟨c,_,rfl⟩:=hy
    refine ⟨fun i=>c (eTm i).1,?_⟩
    change ∑ i:Fin r,c (eTm i).1•(eTm i:Mbar) = ∑ t∈Tm,c t•t
    rw [← Finset.sum_coe_sort Tm (fun t=>c t•t)]
    exact Fintype.sum_equiv eTm _ _ fun _=>rfl
   let L:=LinearMap.ker pF;have : Module.Finite R₁ L:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian L)
   obtain ⟨δF,hF1,_,hF3⟩:=z63 S₁ L.subtype pF
    Subtype.val_injective q7 (Submodule.range_subtype L)
   have : Subsingleton (z56 R₁ S₁ (Fin r→R₁) 1):=z61 S₁ (Fin r→R₁) 0
   have hδF_inj:Injective (δF 0):=by
    rw [injective_iff_map_eq_zero];intro z hz;obtain ⟨w,rfl⟩:=(hF3 0 z).mp hz;rw [Subsingleton.elim w 0,map_zero]
   let q26:(S₁ ⊗[R₁] L) →ₗ[S₁] (S₁ ⊗[R₁] (Fin r→R₁)):=LinearMap.baseChange S₁ L.subtype;let K':Submodule S₁ (S₁ ⊗[R₁] L):=LinearMap.ker q26;have : Module.Finite S₁ (S₁ ⊗[R₁] L):=inferInstance;have q22:K'.FG:=IsNoetherian.noetherian K'
   have q23:K' ≤ maximalIdeal S₁ • K':=by
    intro t ht
    have q28:z57 S₁ L.subtype 0 ((z59 R₁ S₁ L).symm t)=0:=by
     apply (z59 R₁ S₁ (Fin r→R₁)).injective;rw [z60,LinearEquiv.apply_symm_apply,map_zero];exact ht
    obtain ⟨z,hz⟩:=(hF1 0 _).mp q28;obtain ⟨z',hz'⟩:=q17 z;dsimp only at hz';let t':S₁ ⊗[R₁] L:=z59 R₁ S₁ L (δF 0 z')
    have q14:t'∈K':=by
     change LinearMap.lTensor S₁ L.subtype (z59 R₁ S₁ L (δF 0 z'))=0;rw [← z60];have : z57 S₁ L.subtype 0 (δF 0 z')=0:=(hF1 0 (δF 0 z')).mpr ⟨z',rfl⟩;rw [this,map_zero]
    have q27:t=(algebraMap R₁ S₁ x)•t':=by
     rw [algebraMap_smul];change t=x•z59 R₁ S₁ L (δF 0 z');rw [← map_smul,← map_smul,hz',hz,LinearEquiv.apply_symm_apply]
    rw [q27];exact Submodule.smul_mem_smul q24 q14
   have q19:K' = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (I:=maximalIdeal S₁) (N:=K') q22 q23
     (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
   refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
   apply hδF_inj;rw [map_zero];apply (z59 R₁ S₁ L).injective;rw [map_zero]
   have q35:z59 R₁ S₁ L (δF 0 z)∈K':=by
    change LinearMap.lTensor S₁ L.subtype (z59 R₁ S₁ L (δF 0 z))=0;rw [← z60];have : z57 S₁ L.subtype 0 (δF 0 z)=0:=(hF1 0 (δF 0 z)).mpr ⟨z,rfl⟩;rw [this,map_zero]
   rw [q19] at q35;exact q35
  obtain ⟨_,_,h2_M,_⟩:=z63 S₁ M0.subtype M0.mkQ
   Subtype.val_injective (Submodule.mkQ_surjective M0)
   (by rw [Submodule.range_subtype,Submodule.ker_mkQ])
  refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
  obtain ⟨w,rfl⟩:=(h2_M 1 z).mp (Subsingleton.elim _ 0);rw [Subsingleton.elim w 0,map_zero]
 rw [Module.Flat.iff_lTensor_injective'];intro I;have : Subsingleton (z56 R₁ S₁ (R₁ ⧸ I) 1):=q12 (R₁ ⧸ I)
 obtain ⟨δ,h1,_,_⟩:=z63 S₁ I.subtype I.mkQ
  Subtype.val_injective (Submodule.mkQ_surjective I)
  (by rw [Submodule.range_subtype,Submodule.ker_mkQ])
 rw [injective_iff_map_eq_zero];intro t ht
 have h0:z57 S₁ I.subtype 0 ((z59 R₁ S₁ I).symm t)=0:=by
  apply (z59 R₁ S₁ R₁).injective;rw [z60,LinearEquiv.apply_symm_apply,map_zero];exact ht
 obtain ⟨w,hw⟩:=(h1 0 _).mp h0;rw [Subsingleton.elim w 0,map_zero] at hw;exact (z59 R₁ S₁ I).symm.injective (hw.symm.trans (map_zero _).symm)
private lemma z74 {R₀ S₀ A B:Type} [CommRing R₀] [CommRing S₀]
  [CommRing A] [CommRing B] [Algebra R₀ S₀] [Algebra A B] [Module.Flat A B]
  (eA:R₀ ≃+* A) (eB:S₀ ≃+* B)
  (q1:∀ r:R₀,eB (algebraMap R₀ S₀ r)=algebraMap A B (eA r)) :
  Module.Flat R₀ S₀ := by
 rw [Module.Flat.iff_lTensor_injective'];intro I;let IA:Ideal A:=I.map eA.toRingHom;have q0:Injective (LinearMap.lTensor B IA.subtype):=Module.Flat.lTensor_preserves_injective_linearMap IA.subtype Subtype.val_injective;let : Module R₀ IA:=Module.compHom IA eA.toRingHom;let : Module R₀ (B ⊗[A] IA):=Module.compHom (B ⊗[A] IA) eA.toRingHom
 let : Module A (S₀ ⊗[R₀] I):=Module.compHom (S₀ ⊗[R₀] I) eA.symm.toRingHom;let : Module R₀ (B ⊗[A] A):=Module.compHom (B ⊗[A] A) eA.toRingHom
 let eI:I ≃ₗ[R₀] IA :=
  {
   toFun:=fun x=>⟨eA x.1,mem_map_of_mem eA.toRingHom x.2⟩
   invFun:=fun y=>⟨eA.symm y.1,by
    obtain ⟨a,ha,hay⟩:=(mem_map_iff_of_surjective eA.toRingHom eA.surjective).mp y.2;have : eA.symm y.1=a:=eA.injective (by simpa using hay.symm)
    exact this▸ha⟩
   map_add':=fun _ _=>Subtype.ext (map_add eA _ _)
   map_smul':=fun r x=>Subtype.ext (map_mul eA r x.1)
   left_inv:=fun _=>Subtype.ext (eA.symm_apply_apply _)
   right_inv:=fun _=>Subtype.ext (eA.apply_symm_apply _) }
 let Φ₁ : (S₀ ⊗[R₀] I) →ₗ[R₀] (B ⊗[A] IA) :=
  TensorProduct.lift
   {
    toFun:=fun s0 =>
     {
      toFun:=fun x=>eB s0 ⊗ₜ[A] eI x
      map_add':=fun x₁ x₂=>by rw [map_add,tmul_add]
      map_smul':=fun r0 x=>by
       rw [RingHom.id_apply,map_smul eI]
       exact TensorProduct.tmul_smul (eA r0) (eB s0) (eI x) }
    map_add':=fun s₁ s₂=>by
     apply LinearMap.ext;intro x;exact (congrArg (· ⊗ₜ[A] eI x) (map_add eB s₁ s₂)).trans (add_tmul _ _ _)
    map_smul':=fun r0 s0=>by
     apply LinearMap.ext;intro x;change eB (r0•s0) ⊗ₜ[A] eI x=eA r0•(eB s0 ⊗ₜ[A] eI x);rw [Algebra.smul_def,map_mul,q1,← Algebra.smul_def]
     exact smul_tmul' (eA r0) (eB s0) (eI x) }
 let Ψ₁ : (B ⊗[A] IA) →ₗ[A] (S₀ ⊗[R₀] I) :=
  TensorProduct.lift
   {
    toFun:=fun b =>
     {
      toFun:=fun y=>eB.symm b ⊗ₜ[R₀] eI.symm y
      map_add':=fun y₁ y₂=>by rw [map_add,tmul_add]
      map_smul':=fun a y=>by
       have hsm:eI.symm (a•y)=eA.symm a•eI.symm y:=by
        apply Subtype.ext;exact map_mul eA.symm a y.1
       change eB.symm b ⊗ₜ[R₀] eI.symm (a•y)=eA.symm a•(eB.symm b ⊗ₜ[R₀] eI.symm y);rw [hsm]
       exact TensorProduct.tmul_smul (eA.symm a) (eB.symm b) (eI.symm y) }
    map_add':=fun b₁ b₂=>by
     apply LinearMap.ext;intro y;exact (congrArg (· ⊗ₜ[R₀] eI.symm y) (map_add eB.symm b₁ b₂)).trans (add_tmul _ _ _)
    map_smul':=fun a b=>by
     apply LinearMap.ext;intro y;change eB.symm (a•b) ⊗ₜ[R₀] eI.symm y=eA.symm a•(eB.symm b ⊗ₜ[R₀] eI.symm y)
     have hfa:eB.symm (algebraMap A B a)=algebraMap R₀ S₀ (eA.symm a):=by
      apply eB.injective;rw [eB.apply_symm_apply,q1,eA.apply_symm_apply]
     rw [Algebra.smul_def,map_mul,hfa,← Algebra.smul_def]
     exact smul_tmul' (eA.symm a) (eB.symm b) (eI.symm y) }
 have hΨΦ : ∀ t:S₀ ⊗[R₀] I,Ψ₁ (Φ₁ t)=t:=fun t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp
  | tmul s0 x =>
   change eB.symm (eB s0) ⊗ₜ[R₀] eI.symm (eI x)=s0 ⊗ₜ[R₀] x;rw [eB.symm_apply_apply,eI.symm_apply_apply]
  | add t₁ t₂ ih₁ ih₂=>rw [map_add,map_add,ih₁,ih₂]
 let Φ₂ : (S₀ ⊗[R₀] R₀) →ₗ[R₀] (B ⊗[A] A) :=
  TensorProduct.lift
   {
    toFun:=fun s0 =>
     {
      toFun:=fun r0=>eB s0 ⊗ₜ[A] eA r0
      map_add':=fun x₁ x₂=>by rw [map_add,tmul_add]
      map_smul':=fun r x=>by
       change eB s0 ⊗ₜ[A] eA (r*x)=eA r•(eB s0 ⊗ₜ[A] eA x);rw [map_mul,← smul_eq_mul]
       exact TensorProduct.tmul_smul (eA r) (eB s0) (eA x) }
    map_add':=fun s₁ s₂=>by
     apply LinearMap.ext;intro x;exact (congrArg (· ⊗ₜ[A] eA x) (map_add eB s₁ s₂)).trans (add_tmul _ _ _)
    map_smul':=fun r s0=>by
     apply LinearMap.ext;intro x;change eB (r•s0) ⊗ₜ[A] eA x=eA r•(eB s0 ⊗ₜ[A] eA x);rw [Algebra.smul_def,map_mul,q1,← Algebra.smul_def]
     exact smul_tmul' (eA r) (eB s0) (eA x) }
 have hsq:∀ t:S₀ ⊗[R₀] I,Φ₂ (LinearMap.lTensor S₀ I.subtype t)=LinearMap.lTensor B IA.subtype (Φ₁ t):=fun t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp
  | tmul s0 x=>rfl
  | add t₁ t₂ ih₁ ih₂=>rw [map_add,map_add,map_add,map_add,ih₁,ih₂]
 intro t₁ t₂ ht
 have h1:LinearMap.lTensor B IA.subtype (Φ₁ t₁)=LinearMap.lTensor B IA.subtype (Φ₁ t₂):=by
  rw [← hsq,← hsq,ht]
 have h2 : Φ₁ t₁ = Φ₁ t₂ := q0 h1;rw [← hΨΦ t₁,← hΨΦ t₂,h2]
private lemma z75 {V D:Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [CommRing D] [IsDomain D] [Algebra V D]
  (q0:Injective (algebraMap V D)) : Module.Flat V D:=by
 rw [IsDedekindDomain.flat_iff_torsion_eq_bot,← Submodule.isTorsionFree_iff_torsion_eq_bot]
 exact Module.IsTorsionFree.of_smul_eq_zero fun {v d} hvd=>by
  rw [Algebra.smul_def,mul_eq_zero] at hvd
  exact hvd.imp (fun hv=>q0 (hv.trans (map_zero _).symm)) id
lemma z76 {A B:Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
  (f:A →+* B) (q4:∀ a∈maximalIdeal A,f a∈maximalIdeal B)
  (q5:letI : Algebra A B:=f.toAlgebra;Module.Flat A B) :
  letI : Algebra (PowerSeries A) (PowerSeries B):=(PowerSeries.map f).toAlgebra
  Module.Flat (PowerSeries A) (PowerSeries B):=by
 let : Algebra A B:=f.toAlgebra;let : Algebra (PowerSeries A) (PowerSeries B):=(PowerSeries.map f).toAlgebra;have : Module.Flat A B:=q5
 have q3:algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X ∈
   maximalIdeal (PowerSeries B):=by
  change PowerSeries.map f PowerSeries.X∈maximalIdeal (PowerSeries B);rw [PowerSeries.map_X];exact z4
 have q1:∀ (C:Type) [CommRing C],IsSMulRegular (PowerSeries C) (PowerSeries.X:PowerSeries C):=by
  intro C _ a b hab;ext k;have hk:=congrArg (PowerSeries.coeff (k+1)) hab;simpa [smul_eq_mul,PowerSeries.coeff_succ_X_mul] using hk
 have q7:IsSMulRegular (PowerSeries B) (algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X):=by
  change IsSMulRegular (PowerSeries B) (PowerSeries.map f PowerSeries.X);rw [PowerSeries.map_X];exact q1 B
 refine z73 PowerSeries.X q3 (q1 A) q7 ?_
 have q0:∀ (C:Type) [CommRing C],RingHom.ker (PowerSeries.constantCoeff (R:=C))=span {(PowerSeries.X:PowerSeries C)}:=by
  intro C _
  refine le_antisymm ?_ ?_
  ·
   intro F hF;rw [RingHom.mem_ker] at hF
   have h1:=z6 1 F (fun i hi=>by
    have hi0:i=0:=by omega
    subst hi0;simpa using hF)
   simpa using h1
  · rw [span_singleton_le_iff_mem,RingHom.mem_ker,PowerSeries.constantCoeff_X]
 let eA:(PowerSeries A⧸span {(PowerSeries.X:PowerSeries A)}) ≃+* A :=
  (Ideal.quotEquivOfEq (q0 A).symm).trans
   (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj)
 have q2:span {algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X} = span {(PowerSeries.X:PowerSeries B)}:=by
  change span {PowerSeries.map f PowerSeries.X} = _;rw [PowerSeries.map_X]
 let eB:(PowerSeries B⧸span {algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X}) ≃+* B :=
  (Ideal.quotEquivOfEq q2).trans
   ((Ideal.quotEquivOfEq (q0 B).symm).trans
    (RingHom.quotientKerEquivOfSurjective PowerSeries.constantCoeff_surj))
 let R₀ := PowerSeries A⧸span {(PowerSeries.X:PowerSeries A)};let S₀ := PowerSeries B⧸span {algebraMap (PowerSeries A) (PowerSeries B) PowerSeries.X}
 let f₀ : R₀ →+* S₀ := Ideal.Quotient.lift (span {PowerSeries.X})
  ((Ideal.Quotient.mk _).comp (algebraMap (PowerSeries A) (PowerSeries B)))
  (fun a ha=>by
   obtain ⟨r,rfl⟩:=mem_span_singleton.mp ha;rw [RingHom.comp_apply,map_mul,Ideal.Quotient.eq_zero_iff_mem]
   exact Ideal.mul_mem_right _ _ (subset_span rfl))
 let : Algebra R₀ S₀ := f₀.toAlgebra
 have q6:∀ r0:R₀,eB (algebraMap R₀ S₀ r0)=algebraMap A B (eA r0):=fun r0=>by
  obtain ⟨F,rfl⟩:=Ideal.Quotient.mk_surjective r0;change PowerSeries.constantCoeff (PowerSeries.map f F)=f (PowerSeries.constantCoeff F);rw [← PowerSeries.coeff_zero_eq_constantCoeff,PowerSeries.coeff_map,PowerSeries.coeff_zero_eq_constantCoeff]
 exact z74 eA eB q6
lemma z77 {V D:Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
  (f:V →+* D) (p:V) (hp:maximalIdeal V=span {p})
  (q0:f p∈maximalIdeal D) (q1:f p≠0) :
  ∀ n : ℕ,
   letI : Algebra (z0 V n) (z0 D n):=(z15 f n).toAlgebra
   Module.Flat (z0 V n) (z0 D n):=by
 have q2:∀ v∈maximalIdeal V,f v∈maximalIdeal D:=fun v hv=>by
  rw [hp,mem_span_singleton] at hv;obtain ⟨a,rfl⟩:=hv;rw [map_mul];exact (maximalIdeal D).mul_mem_right _ q0
 have q3:Injective f:=by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨v,hv_ker,hv_ne⟩ : ∃ v∈RingHom.ker f,v≠0:=by
   by_contra h;push Not at h
   exact hker (le_antisymm (fun x hx=>h x hx) bot_le)
  obtain ⟨k,u,hv_eq⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv_ne
   ((IsDiscreteValuationRing.irreducible_iff_uniformizer p).mpr hp)
  rw [hv_eq,RingHom.mem_ker,map_mul,map_pow] at hv_ker
  have q4:f u≠0:=fun h0=>by
   have h1:f (u*u⁻¹)=0:=by rw [map_mul,h0,zero_mul]
   rw [Units.mul_inv,map_one] at h1;exact one_ne_zero h1
  exact (mul_ne_zero q4 (pow_ne_zero k q1)) hv_ker
 intro n
 induction n with
 | zero =>
  dsimp only [z0,z15];let : Algebra V D:=f.toAlgebra;exact z75 q3
 | succ n ih =>
  exact z76 (z15 f n) (fun a ha=>z23 q2 n ha) ih
end TorAndFlatness
section KoszulComplex
open CategoryTheory
lemma z78 {R:Type} [CommRing R]
  (K:ChainComplex (ModuleCat.{0} R) ℕ) :
  Nonempty (K.homology 0 ≃ₗ[R] (K.X 0⧸LinearMap.range (K.d 1 0).hom)):=by
 have hg0:(K.sc' 1 0 0).g=0:=K.shape 0 0 (by simp);have _:IsIso (K.sc' 1 0 0).homologyι := ShortComplex.isIso_homologyι (K.sc' 1 0 0) hg0;let e1:K.homology 0 ≅ (K.sc' 1 0 0).homology:=K.homologyIsoSc' 1 0 0 (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero;let e2:(K.sc' 1 0 0).homology ≅ (K.sc' 1 0 0).opcycles:=asIso (K.sc' 1 0 0).homologyι
 let e3:(K.sc' 1 0 0).opcycles ≅ ModuleCat.of R (K.X 0⧸LinearMap.range (K.d 1 0).hom):=(K.sc' 1 0 0).moduleCatOpcyclesIso;exact ⟨(e1 ≪≫ e2 ≪≫ e3).toLinearEquiv⟩
lemma z79 {R:Type} [CommRing R]
  (K:ChainComplex (ModuleCat.{0} R) ℕ) (k : ℕ) :
  Nonempty (K.homology (k+1) ≃ₗ[R]
   (LinearMap.ker (K.d (k+1) k).hom ⧸
    (LinearMap.range (K.d (k+2) (k+1)).hom).comap
     (LinearMap.ker (K.d (k+1) k).hom).subtype)):=by
 let eH:K.homology (k+1) ≅ (K.sc' (k+2) (k+1) k).moduleCatLeftHomologyData.H :=
  K.homologyIsoSc' (k+2) (k+1) k (ChainComplex.prev ℕ (k+1)) (ChainComplex.next_nat_succ k) ≪≫
   (K.sc' (k+2) (k+1) k).moduleCatHomologyIso
 have q0:(LinearMap.range (K.d (k+2) (k+1)).hom).comap
   (LinearMap.ker (K.d (k+1) k).hom).subtype =
   LinearMap.range (K.sc' (k+2) (k+1) k).moduleCatToCycles:=by
  ext ⟨y,hy⟩;constructor
  ·
   rintro ⟨a,ha⟩;exact ⟨a,Subtype.ext ha⟩
  ·
   rintro ⟨a,ha⟩;exact ⟨a,congrArg Subtype.val ha⟩
 exact ⟨eH.toLinearEquiv.trans (Submodule.quotEquivOfEq _ _ q0.symm)⟩
abbrev z80 (R M:Type) : List R → ℕ → Type
 | [],0=>M
 | [],_+1=>PUnit
 | _ :: zs,0=>z80 R M zs 0
 | _ :: zs,i+1=>z80 R M zs (i+1)×z80 R M zs i
instance instAddCommGroupKoszulObj (R M:Type) [AddCommGroup M] :
  ∀ (zs:List R) (k : ℕ),AddCommGroup (z80 R M zs k)
 | [],0=>inferInstance
 | [],_+1=>inferInstance
 | _ :: zs,0=>instAddCommGroupKoszulObj R M zs 0
 | _ :: zs,i+1 =>
  letI:=instAddCommGroupKoszulObj R M zs (i+1)
  letI:=instAddCommGroupKoszulObj R M zs i
  inferInstance
instance instModuleKoszulObj (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ),Module R (z80 R M zs k)
 | [],0=>inferInstance
 | [],_+1=>inferInstance
 | _ :: zs,0=>instModuleKoszulObj R M zs 0
 | _ :: zs,i+1 =>
  letI:=instModuleKoszulObj R M zs (i+1)
  letI:=instModuleKoszulObj R M zs i
  inferInstance
def z81 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R),z80 R M zs 0 ≃ₗ[R] M
 | []=>LinearEquiv.refl R M
 | _ :: zs=>z81 R M zs
def z82 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ),z80 R M zs (k+1) →ₗ[R] z80 R M zs k
 | [],_=>0
 | z :: zs,0 =>
  {
   toFun:=fun p=>z82 R M zs 0 p.1+z•p.2
   map_add':=fun p q=>by
    change z82 R M zs 0 (p.1+q.1)+z•(p.2+q.2)=(z82 R M zs 0 p.1+z•p.2)+(z82 R M zs 0 q.1+z•q.2);rw [map_add,smul_add];abel
   map_smul':=fun r p=>by
    change z82 R M zs 0 (r•p.1)+z•(r•p.2)=r•(z82 R M zs 0 p.1+z•p.2)
    rw [map_smul,smul_add,smul_comm] }
 | z :: zs,i+1 =>
  {
   toFun:=fun p=>(z82 R M zs (i+1) p.1+z•p.2,-(z82 R M zs i p.2))
   map_add':=fun p q=>by
    apply Prod.ext
    ·
     change z82 R M zs (i+1) (p.1+q.1)+z•(p.2+q.2)=(z82 R M zs (i+1) p.1+z•p.2)+(z82 R M zs (i+1) q.1+z•q.2);rw [map_add,smul_add];abel
    ·
     change -(z82 R M zs i (p.2+q.2)) = -(z82 R M zs i p.2) + -(z82 R M zs i q.2);rw [map_add,neg_add]
   map_smul':=fun r p=>by
    apply Prod.ext
    ·
     change z82 R M zs (i+1) (r•p.1)+z•(r•p.2)=r•(z82 R M zs (i+1) p.1+z•p.2);rw [map_smul,smul_add,smul_comm]
    ·
     change -(z82 R M zs i (r•p.2))=r • -(z82 R M zs i p.2)
     rw [map_smul,smul_neg] }
lemma z83 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M zs (k+2)),z82 R M zs k (z82 R M zs (k+1) x)=0
 | [],_,_=>rfl
 | z :: zs,0,(a,b)=>by
  change z82 R M zs 0 (z82 R M zs 1 a+z•b)+z•(-(z82 R M zs 0 b))=0;rw [map_add,map_smul,z83 zs 0 a,zero_add,smul_neg,add_neg_cancel]
 | z :: zs,i+1,(a,b)=>by
  apply Prod.ext
  ·
   change z82 R M zs (i+1) (z82 R M zs (i+2) a+z•b)+z•(-(z82 R M zs (i+1) b))=0;rw [map_add,map_smul,z83 zs (i+1) a,zero_add,smul_neg,add_neg_cancel]
  ·
   change -(z82 R M zs i (-(z82 R M zs (i+1) b)))=0;rw [map_neg,z83 zs i b,neg_zero,neg_zero]
def z84 {R M N:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (f:M →ₗ[R] N) :
  ∀ (zs:List R) (k : ℕ),z80 R M zs k →ₗ[R] z80 R N zs k
 | [],0=>f
 | [],_+1=>0
 | _ :: zs,0=>z84 f zs 0
 | _ :: zs,i+1=>LinearMap.prodMap (z84 f zs (i+1)) (z84 f zs i)
lemma z85 {R M N:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (f:M →ₗ[R] N) :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M zs (k+1)),z84 f zs k (z82 R M zs k x)=z82 R N zs k (z84 f zs (k+1) x)
 | [],_,_=>by simp [z82,z84]
 | z :: zs,0,(a,b)=>by
  change z84 f zs 0 (z82 R M zs 0 a+z•b)=z82 R N zs 0 (z84 f zs 1 a)+z•z84 f zs 0 b;rw [map_add,map_smul,z85 f zs 0 a]
 | z :: zs,i+1,(a,b)=>by
  apply Prod.ext
  ·
   change z84 f zs (i+1) (z82 R M zs (i+1) a+z•b)=z82 R N zs (i+1) (z84 f zs (i+2) a)+z•z84 f zs (i+1) b;rw [map_add,map_smul,z85 f zs (i+1) a]
  ·
   change z84 f zs i (-(z82 R M zs i b)) = -(z82 R N zs i (z84 f zs (i+1) b));rw [map_neg,z85 f zs i b]
lemma z86 {R M N:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {f:M →ₗ[R] N} (hf:Injective f) :
  ∀ (zs:List R) (k : ℕ),Injective (z84 f zs k)
 | [],0=>hf
 | [],_+1=>fun _ _ _=>rfl
 | _ :: zs,0=>z86 hf zs 0
 | _ :: zs,i+1=>Prod.map_injective.mpr
   ⟨z86 hf zs (i+1),z86 hf zs i⟩
lemma z87 {R M N:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {f:M →ₗ[R] N} (hf:Surjective f) :
  ∀ (zs:List R) (k : ℕ),Surjective (z84 f zs k)
 | [],0=>hf
 | [],_+1=>fun _=>⟨PUnit.unit,rfl⟩
 | _ :: zs,0=>z87 hf zs 0
 | _ :: zs,i+1=>Prod.map_surjective.mpr
   ⟨z87 hf zs (i+1),z87 hf zs i⟩
lemma z88 {R A B C:Type} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {i:A →ₗ[R] B} {p:B →ₗ[R] C} (hip:LinearMap.range i=LinearMap.ker p) :
  ∀ (zs:List R) (k : ℕ),LinearMap.range (z84 i zs k)=LinearMap.ker (z84 p zs k)
 | [],0=>hip
 | [],_+1=>by ext ⟨⟩;simp [z84]
 | _ :: zs,0=>z88 hip zs 0
 | _ :: zs,k+1=>by
  have h1:=z88 hip zs (k+1);have h2:=z88 hip zs k;ext ⟨b₁,b₂⟩;simp only [LinearMap.mem_range,LinearMap.mem_ker,z84,LinearMap.prodMap_apply,Prod.mk.injEq,Prod.ext_iff,Prod.fst_zero,Prod.snd_zero];constructor
  ·
   rintro ⟨⟨a₁,a₂⟩,ha₁,ha₂⟩;exact ⟨LinearMap.mem_ker.mp (h1▸⟨a₁,ha₁⟩),LinearMap.mem_ker.mp (h2▸⟨a₂,ha₂⟩)⟩
  ·
   rintro ⟨hb₁,hb₂⟩;obtain ⟨a₁,ha₁⟩:=(LinearMap.mem_range.mp (h1.symm▸LinearMap.mem_ker.mpr hb₁));obtain ⟨a₂,ha₂⟩:=(LinearMap.mem_range.mp (h2.symm▸LinearMap.mem_ker.mpr hb₂));exact ⟨(a₁,a₂),ha₁,ha₂⟩
lemma z89 {R M:Type} :
  ∀ (zs:List R) (k : ℕ),zs.length < k→Subsingleton (z80 R M zs k)
 | [],0,h=>by omega
 | [],_+1,_=>inferInstance
 | _ :: zs,0,h=>by omega
 | _ :: zs,i+1,h=>by
  simp only [List.length_cons] at h;have : Subsingleton (z80 R M zs (i+1)):=z89 zs (i+1) (by omega);have : Subsingleton (z80 R M zs i):=z89 zs i (by omega);exact inferInstance
lemma z90 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] :
  ∀ (zs:List R) (k : ℕ),Module.Finite R (z80 R M zs k)
 | [],0=>inferInstance
 | [],_+1=>inferInstance
 | _ :: zs,0=>z90 zs 0
 | _ :: zs,i+1=>by
  have : Module.Finite R (z80 R M zs (i+1)):=z90 zs (i+1);have : Module.Finite R (z80 R M zs i):=z90 zs i;exact inferInstance
lemma z91 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Projective R M] :
  ∀ (zs:List R) (k : ℕ),Module.Projective R (z80 R M zs k)
 | [],0=>inferInstance
 | [],_+1 =>
  Module.Projective.of_split (0:PUnit →ₗ[R] (Fin 0→R)) 0 (by ext ⟨⟩)
 | _ :: zs,0=>z91 zs 0
 | _ :: zs,i+1=>by
  have : Module.Projective R (z80 R M zs (i+1)):=z91 zs (i+1);have : Module.Projective R (z80 R M zs i):=z91 zs i;exact inferInstance
lemma z92 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  {z:R} (hz:IsSMulRegular M z) :
  ∀ (zs:List R) (k : ℕ),IsSMulRegular (z80 R M zs k) z
 | [],0=>hz
 | [],_+1=>fun _ _ _=>rfl
 | _ :: zs,0=>z92 hz zs 0
 | _ :: zs,i+1=>fun ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ h=>Prod.ext
   (z92 hz zs (i+1) (congrArg Prod.fst h))
   (z92 hz zs i (congrArg Prod.snd h))
lemma z93 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  {a:R} (ha:∀ m:M,a•m=0) :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M zs k),a•x=0
 | [],0,m=>ha m
 | [],_+1,_=>rfl
 | _ :: zs,0,x=>z93 ha zs 0 x
 | _ :: zs,i+1,(x,y)=>Prod.ext
   (z93 ha zs (i+1) x)
   (z93 ha zs i y)
abbrev z94 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] (zs:List R) : ℕ → Type
 | 0=>z80 R M zs 0⧸LinearMap.range (z82 R M zs 0)
 | i+1 =>
  LinearMap.ker (z82 R M zs i) ⧸
   (LinearMap.range (z82 R M zs (i+1))).comap (LinearMap.ker (z82 R M zs i)).subtype
instance instAddCommGroupKoszulH (R M:Type) [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) : ∀ k : ℕ,AddCommGroup (z94 R M zs k)
 | 0=>inferInstance
 | _+1=>inferInstance
instance instModuleKoszulH (R M:Type) [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) : ∀ k : ℕ,Module R (z94 R M zs k)
 | 0=>inferInstance
 | _+1=>inferInstance
lemma z95 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) (h:zs.length < k) :
  Subsingleton (z94 R M zs k):=by
 cases k with
 | zero=>omega
 | succ i =>
  have : Subsingleton (z80 R M zs (i+1)):=z89 zs (i+1) h;have : Subsingleton (LinearMap.ker (z82 R M zs i)):=inferInstance;exact inferInstance
lemma z96 {R M:Type} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M] (zs:List R) (k : ℕ) :
  Module.Finite R (z94 R M zs k):=by
 cases k with
 | zero =>
  have : Module.Finite R (z80 R M zs 0):=z90 zs 0;exact inferInstance
 | succ i =>
  have : Module.Finite R (z80 R M zs (i+1)):=z90 zs (i+1);have : Module.Finite R (LinearMap.ker (z82 R M zs i)):=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _);exact inferInstance
def z97 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M] (zs:List R) :
  ChainComplex (ModuleCat.{0} R) ℕ :=
 ChainComplex.of
  (fun k=>ModuleCat.of R (z80 R M zs k))
  (fun k=>ModuleCat.ofHom (z82 R M zs k))
  (fun k=>by
   apply ModuleCat.hom_ext;apply LinearMap.ext;intro x
   exact z83 zs k x)
lemma z98 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) :
  ((z97 R M zs).d (k+1) k).hom=z82 R M zs k:=by
 simp [z97];rfl
lemma z99 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) :
  Nonempty ((z97 R M zs).homology k ≃ₗ[R] z94 R M zs k):=by
 cases k with
 | zero =>
  obtain ⟨e⟩:=z78 (z97 R M zs)
  have hr:LinearMap.range ((z97 R M zs).d 1 0).hom=LinearMap.range (z82 R M zs 0):=by
   rw [z98];rfl
  exact ⟨e.trans (Submodule.quotEquivOfEq _ _ hr)⟩
 | succ i =>
  obtain ⟨e⟩:=z79 (z97 R M zs) i;have hd0:=z98 (R:=R) (M:=M) zs i;have hd1:=z98 (R:=R) (M:=M) zs (i+1)
  have q1:LinearMap.ker ((z97 R M zs).d (i+1) i).hom=LinearMap.ker (z82 R M zs i):=by rw [hd0];rfl
  let q0:LinearMap.ker ((z97 R M zs).d (i+1) i).hom ≃ₗ[R]
    LinearMap.ker (z82 R M zs i):=LinearEquiv.ofEq _ _ q1
  have q2:Submodule.map q0.toLinearMap
    ((LinearMap.range ((z97 R M zs).d (i+2) (i+1)).hom).comap
     (LinearMap.ker ((z97 R M zs).d (i+1) i).hom).subtype) =
    (LinearMap.range (z82 R M zs (i+1))).comap (LinearMap.ker (z82 R M zs i)).subtype:=by
   ext ⟨y,hy⟩;simp only [Submodule.mem_map,Submodule.mem_comap,Submodule.coe_subtype,hd1]
   exact ⟨fun ⟨⟨x,hx⟩,hmem,hxy⟩=>by
     have hxy':x=y:=congrArg Subtype.val hxy
     exact hxy'▸hmem,
    fun hmem=>⟨⟨y,q1.symm▸hy⟩,hmem,rfl⟩⟩
  exact ⟨e.trans (Submodule.Quotient.equiv _ _ q0 q2)⟩
lemma z100 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R),
   Submodule.map (z81 R M zs).toLinearMap
    (LinearMap.range (z82 R M zs 0)) =
   ofList zs•(⊤ : Submodule R M)
 | []=>by
  rw [Ideal.ofList_nil,Submodule.bot_smul];ext m;simp [z82,z81]
 | z :: zs=>by
  have ih:=z100 (M:=M) zs;rw [Ideal.ofList_cons,Submodule.sup_smul]
  have q0:span {z}•(⊤ : Submodule R M)=LinearMap.range (z•LinearMap.id (R:=R) (M:=M)):=by
   refine le_antisymm ?_ ?_
   ·
    rw [Submodule.smul_le];intro r hr m _;obtain ⟨a,rfl⟩:=mem_span_singleton.mp hr;exact ⟨a•m,by change z•(a•m)=(z*a)•m;rw [mul_smul]⟩
   ·
    rintro _ ⟨m,rfl⟩;exact Submodule.smul_mem_smul (subset_span rfl) Submodule.mem_top
  rw [q0,← ih];ext m;constructor
  ·
   rintro ⟨_,⟨⟨a,b⟩,rfl⟩,rfl⟩;rw [Submodule.mem_sup]
   refine ⟨z•(z81 R M zs b),⟨z81 R M zs b,rfl⟩,z81 R M zs (z82 R M zs 0 a),⟨z82 R M zs 0 a,⟨a,rfl⟩,rfl⟩,?_⟩
   change z•z81 R M zs b+z81 R M zs (z82 R M zs 0 a)=z81 R M zs (z82 R M zs 0 a+z•b);rw [map_add,map_smul,add_comm]
  ·
   intro hm;rw [Submodule.mem_sup] at hm;obtain ⟨_,⟨m₁,rfl⟩,_,⟨_,⟨a,rfl⟩,rfl⟩,rfl⟩:=hm
   refine ⟨z82 R M (z :: zs) 0 (a,(z81 R M zs).symm m₁),⟨_,rfl⟩,?_⟩
   change z81 R M zs (z82 R M zs 0 a+z•(z81 R M zs).symm m₁)=z•m₁ + z81 R M zs (z82 R M zs 0 a);rw [map_add,map_smul,LinearEquiv.apply_symm_apply,add_comm]
lemma z101 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] (zs:List R) :
  Nonempty (z94 R M zs 0 ≃ₗ[R] (M⧸(ofList zs•(⊤ : Submodule R M)))) :=
 ⟨Submodule.Quotient.equiv (LinearMap.range (z82 R M zs 0))
  (ofList zs•(⊤ : Submodule R M)) (z81 R M zs) (z100 zs)⟩
lemma z102 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) {a:R} (ha:∀ m:M,a•m=0) (x:z94 R M zs k) :
  a•x=0:=by
 cases k with
 | zero =>
  obtain ⟨u,rfl⟩:=Submodule.Quotient.mk_surjective _ x;change Submodule.Quotient.mk (a•u)=0;rw [z93 ha zs 0 u,Submodule.Quotient.mk_zero]
 | succ i =>
  obtain ⟨⟨u,hu⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;have hau:a•u∈LinearMap.ker (z82 R M zs i):=LinearMap.mem_ker.mpr (by rw [map_smul,LinearMap.mem_ker.mp hu,smul_zero]);change Submodule.Quotient.mk (⟨a•u,hau⟩ : LinearMap.ker (z82 R M zs i))=0;have h0:(⟨a•u,hau⟩ : LinearMap.ker (z82 R M zs i))=0:=Subtype.ext (z93 ha zs (i+1) u)
  rw [h0,Submodule.Quotient.mk_zero]
private noncomputable def z103 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (w:R),w∈zs→∀ k : ℕ,z80 R M zs k →ₗ[R] z80 R M zs (k+1)
 | [],_,hw,_=>absurd hw (List.not_mem_nil)
 | z :: zs,w,hw,k =>
  letI:=Classical.dec (w=z)
  if h:w=z then
   match k with
   | 0=>{ toFun:=fun a=>(0,a),map_add':=fun _ _=>by simp,map_smul':=fun _ _=>by simp }
   | _+1=>{ toFun:=fun p=>(0,p.1),map_add':=fun _ _=>by simp,map_smul':=fun _ _=>by simp }
  else
   have hw':w∈zs:=(List.mem_cons.mp hw).resolve_left h
   match k with
   | 0 =>
    {
     toFun:=fun a=>(z103 (M:=M) zs w hw' 0 a,0)
     map_add':=fun _ _=>by simp [map_add]
     map_smul':=fun _ _=>by simp [map_smul] }
   | i+1 =>
    {
     toFun:=fun p=>(z103 (M:=M) zs w hw' (i+1) p.1,-(z103 (M:=M) zs w hw' i p.2))
     map_add':=fun _ _=>by simp [map_add];abel
     map_smul':=fun _ _=>by simp [map_smul,smul_neg] }
private lemma z104 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (w:R) (hw:w∈zs) (x:z80 R M zs 0),z82 R M zs 0 (z103 (M:=M) zs w hw 0 x)=w•x
 | [],_,hw,_=>absurd hw List.not_mem_nil
 | z :: zs,w,hw,x=>by
  unfold z103
  split_ifs with h
  ·
   subst h;change z82 R M zs 0 0+w•x=w•x;rw [map_zero,zero_add]
  ·
   have hw':w∈zs:=(List.mem_cons.mp hw).resolve_left h
   change z82 R M zs 0 (z103 (M:=M) zs w hw' 0 x)+z•(0:z80 R M zs 0)=w•x
   rw [smul_zero,add_zero];exact z104 zs w hw' x
private lemma z105 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (w:R) (hw:w∈zs) (i : ℕ) (x:z80 R M zs (i+1)),
   z82 R M zs (i+1) (z103 (M:=M) zs w hw (i+1) x)+z103 (M:=M) zs w hw i (z82 R M zs i x)=w•x
 | [],_,hw,_,_=>absurd hw List.not_mem_nil
 | z :: zs,w,hw,i,(a,b)=>by
  unfold z103
  split_ifs with h
  ·
   subst h
   cases i with
   | zero =>
    apply Prod.ext
    ·
     change (z82 R M zs 1 0+w•a)+0=w•a;rw [map_zero,zero_add,add_zero]
    ·
     change (-(z82 R M zs 0 a))+(z82 R M zs 0 a+w•b)=w•b;abel
   | succ j =>
    apply Prod.ext
    ·
     change (z82 R M zs (j+2) 0+w•a)+0=w•a;rw [map_zero,zero_add,add_zero]
    ·
     change (-(z82 R M zs (j+1) a))+(z82 R M zs (j+1) a+w•b)=w•b;abel
  ·
   have hw':w∈zs:=(List.mem_cons.mp hw).resolve_left h
   cases i with
   | zero =>
    apply Prod.ext
    ·
     change (z82 R M zs 1 (z103 (M:=M) zs w hw' 1 a)+z•(-(z103 (M:=M) zs w hw' 0 b)))+z103 (M:=M) zs w hw' 0 (z82 R M zs 0 a+z•b)=w•a
     rw [map_add,map_smul,smul_neg];have h1:=z105 zs w hw' 0 a;rw [← h1];abel
    ·
     change (-(z82 R M zs 0 (-(z103 (M:=M) zs w hw' 0 b))))+0=w•b
     rw [map_neg,neg_neg,add_zero];exact z104 zs w hw' b
   | succ j =>
    apply Prod.ext
    ·
     change (z82 R M zs (j+2) (z103 (M:=M) zs w hw' (j+2) a)+z•(-(z103 (M:=M) zs w hw' (j+1) b)))+z103 (M:=M) zs w hw' (j+1) (z82 R M zs (j+1) a+z•b)=w•a
     rw [map_add,map_smul,smul_neg];have h1:=z105 zs w hw' (j+1) a;rw [← h1];abel
    ·
     change (-(z82 R M zs (j+1) (-(z103 (M:=M) zs w hw' (j+1) b))))+(-(z103 (M:=M) zs w hw' j (-(z82 R M zs j b))))=w•b
     rw [map_neg,neg_neg,map_neg,neg_neg];exact z105 zs w hw' j b
lemma z106 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) (k : ℕ) {w:R} (hw:w∈zs) (x:z94 R M zs k) :
  w•x=0:=by
 cases k with
 | zero =>
  obtain ⟨u,rfl⟩:=Submodule.Quotient.mk_surjective _ x;change Submodule.Quotient.mk (w•u)=0;rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨z103 (M:=M) zs w hw 0 u,z104 zs w hw u⟩
 | succ i =>
  obtain ⟨⟨u,hu⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;have hwu:w•u∈LinearMap.ker (z82 R M zs i):=LinearMap.mem_ker.mpr (by rw [map_smul,LinearMap.mem_ker.mp hu,smul_zero]);change Submodule.Quotient.mk (⟨w•u,hwu⟩ : LinearMap.ker (z82 R M zs i))=0;rw [Submodule.Quotient.mk_eq_zero,Submodule.mem_comap,Submodule.coe_subtype]
  refine ⟨z103 (M:=M) zs w hw (i+1) u,?_⟩
  have h1:=z105 zs w hw i u;rw [LinearMap.mem_ker.mp hu,map_zero,add_zero] at h1;exact h1
lemma z107 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (z:R) (zs:List R) (hz:∀ m:M,z•m=0) :
  Nonempty (z94 R M (z :: zs) 0 ≃ₗ[R] z94 R M zs 0):=by
 have q0:LinearMap.range (z82 R M (z :: zs) 0)=LinearMap.range (z82 R M zs 0):=by
  ext x;constructor
  ·
   rintro ⟨⟨a,b⟩,rfl⟩
   refine ⟨a,?_⟩
   change z82 R M zs 0 a=z82 R M zs 0 a+z•b;rw [z93 hz zs 0 b,add_zero]
  ·
   rintro ⟨a,rfl⟩
   refine ⟨(a,0),?_⟩
   change z82 R M zs 0 a+z•0=z82 R M zs 0 a;rw [smul_zero,add_zero]
 exact ⟨Submodule.quotEquivOfEq _ _ q0⟩
lemma z108 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (z:R) (zs:List R) (hz:∀ m:M,z•m=0) (i : ℕ) :
  Nonempty (z94 R M (z :: zs) (i+1) ≃ₗ[R] (z94 R M zs (i+1)×z94 R M zs i)):=by
 have hd:∀ (k : ℕ) (a:z80 R M zs (k+2)) (b:z80 R M zs (k+1)),z82 R M (z :: zs) (k+1) (a,b)=(z82 R M zs (k+1) a,-(z82 R M zs k b)):=by
  intro k a b;apply Prod.ext
  ·
   change z82 R M zs (k+1) a+z•b=z82 R M zs (k+1) a;rw [z93 hz zs (k+1) b,add_zero]
  · rfl
 cases i with
 | zero =>
  have q0:∀ p:z80 R M zs 1×z80 R M zs 0,p∈LinearMap.ker (z82 R M (z :: zs) 0)↔p.1∈LinearMap.ker (z82 R M zs 0):=by
   intro ⟨a,b⟩;simp only [LinearMap.mem_ker];change z82 R M zs 0 a+z•b=0↔z82 R M zs 0 a=0;rw [z93 hz zs 0 b,add_zero]
  let Φ : LinearMap.ker (z82 R M (z :: zs) 0) →ₗ[R]
    (z94 R M zs 1×z94 R M zs 0) :=
   {
    toFun:=fun p =>
     (Submodule.Quotient.mk ⟨p.1.1,(q0 p.1).mp p.2⟩,Submodule.Quotient.mk p.1.2)
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }
  have hΦ_surj:Surjective Φ := by
   rintro ⟨x,y⟩;obtain ⟨⟨a,ha⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;obtain ⟨b,rfl⟩:=Submodule.Quotient.mk_surjective _ y;exact ⟨⟨(a,b),(q0 (a,b)).mpr ha⟩,rfl⟩
  have hΦ_ker:LinearMap.ker Φ =
    (LinearMap.range (z82 R M (z :: zs) 1)).comap
     (LinearMap.ker (z82 R M (z :: zs) 0)).subtype:=by
   ext ⟨⟨a,b⟩,hab⟩;rw [LinearMap.mem_ker];change (Submodule.Quotient.mk _,Submodule.Quotient.mk _)=0↔_;rw [Prod.mk_eq_zero,Submodule.Quotient.mk_eq_zero,Submodule.Quotient.mk_eq_zero];simp only [Submodule.mem_comap,Submodule.coe_subtype,LinearMap.mem_range];constructor
   ·
    rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    refine ⟨(u,-v),?_⟩
    rw [hd 0 u (-v),map_neg,neg_neg,hu,hv]
   ·
    rintro ⟨⟨u,v⟩,huv⟩;rw [hd 0 u v,Prod.mk.injEq] at huv;exact ⟨⟨u,huv.1⟩,⟨-v,by rw [map_neg,huv.2]⟩⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hΦ_ker.symm).trans (Φ.quotKerEquivOfSurjective hΦ_surj)⟩
 | succ j =>
  have q0:∀ p:z80 R M zs (j+2)×z80 R M zs (j+1),
    p∈LinearMap.ker (z82 R M (z :: zs) (j+1))↔p.1∈LinearMap.ker (z82 R M zs (j+1))∧p.2∈LinearMap.ker (z82 R M zs j):=by
   intro ⟨a,b⟩;simp only [LinearMap.mem_ker,hd j a b,Prod.mk_eq_zero,neg_eq_zero]
  let Φ : LinearMap.ker (z82 R M (z :: zs) (j+1)) →ₗ[R]
    (z94 R M zs (j+2)×z94 R M zs (j+1)) :=
   {
    toFun:=fun p =>
     (Submodule.Quotient.mk ⟨p.1.1,((q0 p.1).mp p.2).1⟩,Submodule.Quotient.mk ⟨p.1.2,((q0 p.1).mp p.2).2⟩)
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }
  have hΦ_surj:Surjective Φ := by
   rintro ⟨x,y⟩;obtain ⟨⟨a,ha⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;obtain ⟨⟨b,hb⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ y;exact ⟨⟨(a,b),(q0 (a,b)).mpr ⟨ha,hb⟩⟩,rfl⟩
  have hΦ_ker:LinearMap.ker Φ =
    (LinearMap.range (z82 R M (z :: zs) (j+2))).comap
     (LinearMap.ker (z82 R M (z :: zs) (j+1))).subtype:=by
   ext ⟨⟨a,b⟩,hab⟩;rw [LinearMap.mem_ker];change (Submodule.Quotient.mk _,Submodule.Quotient.mk _)=0↔_;rw [Prod.mk_eq_zero,Submodule.Quotient.mk_eq_zero,Submodule.Quotient.mk_eq_zero];simp only [Submodule.mem_comap,Submodule.coe_subtype,LinearMap.mem_range];constructor
   ·
    rintro ⟨⟨u,hu⟩,⟨v,hv⟩⟩
    refine ⟨(u,-v),?_⟩
    rw [hd (j+1) u (-v),map_neg,neg_neg,hu,hv]
   ·
    rintro ⟨⟨u,v⟩,huv⟩;rw [hd (j+1) u v,Prod.mk.injEq] at huv;exact ⟨⟨u,huv.1⟩,⟨-v,by rw [map_neg,huv.2]⟩⟩
  exact ⟨(Submodule.quotEquivOfEq _ _ hΦ_ker.symm).trans (Φ.quotKerEquivOfSurjective hΦ_surj)⟩
lemma z109 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M]
  (z:R) (zs:List R) (hz:IsSMulRegular M z) (k : ℕ) :
  Nonempty (z94 R M (z :: zs) k ≃ₗ[R]
   z94 R (M⧸LinearMap.range (z•LinearMap.id (R:=R) (M:=M))) zs k):=by
 let zM:Submodule R M:=LinearMap.range (z•LinearMap.id (R:=R) (M:=M));let Mbar:=M⧸zM;let π : M →ₗ[R] Mbar:=zM.mkQ;have hπ_surj:Surjective π := Submodule.mkQ_surjective zM
 have hπ_ker:∀ (k' : ℕ) (x:z80 R M zs k'),z84 π zs k' x=0↔∃ y:z80 R M zs k',z•y=x:=by
  intro k' x
  have h1:=z88 (R:=R) (i:=z•LinearMap.id (R:=R) (M:=M)) (p := π)
   (Submodule.ker_mkQ zM).symm zs k'
  have h2:z84 (z•LinearMap.id (R:=R) (M:=M)) zs k'=z•LinearMap.id:=by
   clear x h1
   induction zs generalizing k' with
   | nil =>
    cases k' with
    | zero=>rfl
    | succ _=>ext ⟨⟩
   | cons w ws ih =>
    cases k' with
    | zero=>exact ih 0
    | succ j =>
     apply LinearMap.ext;rintro ⟨a,b⟩
     exact Prod.ext (congrFun (congrArg DFunLike.coe (ih (j+1))) a)
      (congrFun (congrArg DFunLike.coe (ih j)) b)
  rw [← LinearMap.mem_ker,← h1,h2];simp [LinearMap.mem_range]
 cases k with
 | zero =>
  let Φ : z80 R M zs 0 →ₗ[R] z94 R Mbar zs 0:=(LinearMap.range (z82 R Mbar zs 0)).mkQ.comp (z84 π zs 0);have hΦ_surj:Surjective Φ := (Submodule.mkQ_surjective _).comp (z87 hπ_surj zs 0)
  have hΦ_ker:LinearMap.ker Φ = LinearMap.range (z82 R M (z :: zs) 0):=by
   ext a;simp only [LinearMap.mem_ker,Φ,LinearMap.comp_apply,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero,LinearMap.mem_range];constructor
   ·
    rintro ⟨ubar,hubar⟩;obtain ⟨u,rfl⟩:=z87 hπ_surj zs 1 ubar;rw [← z85 π zs 0 u,← sub_eq_zero,← map_sub] at hubar;obtain ⟨b,hb⟩:=(hπ_ker 0 (a - z82 R M zs 0 u)).mp (by rw [← neg_eq_zero,← map_neg,neg_sub];exact hubar)
    refine ⟨(u,b),?_⟩
    change z82 R M zs 0 u+z•b=a;rw [hb];abel
   ·
    rintro ⟨⟨u,b⟩,rfl⟩
    refine ⟨z84 π zs 1 u,?_⟩
    change z82 R Mbar zs 0 (z84 π zs 1 u)=z84 π zs 0 (z82 R M zs 0 u+z•b);rw [map_add,z85 π zs 0 u];have hzb:z84 π zs 0 (z•b)=0:=(hπ_ker 0 (z•b)).mpr ⟨b,rfl⟩;rw [hzb,add_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hΦ_ker.symm).trans (Φ.quotKerEquivOfSurjective hΦ_surj)⟩
 | succ i =>
  have q0:∀ p:LinearMap.ker (z82 R M (z :: zs) i),z84 π zs (i+1) p.1.1∈LinearMap.ker (z82 R Mbar zs i):=by
   intro ⟨⟨a,b⟩,hab⟩;rw [LinearMap.mem_ker,← z85 π zs i a]
   have h1:z82 R M zs i a+z•b=0:=by
    cases i with
    | zero=>exact LinearMap.mem_ker.mp hab
    | succ j=>exact congrArg Prod.fst (LinearMap.mem_ker.mp hab)
   have ha:z82 R M zs i a = -(z•b):=eq_neg_of_add_eq_zero_left h1;rw [ha,map_neg,neg_eq_zero];exact (hπ_ker i (z•b)).mpr ⟨b,rfl⟩
  let Φ : LinearMap.ker (z82 R M (z :: zs) i) →ₗ[R] z94 R Mbar zs (i+1) :=
   {
    toFun:=fun p=>Submodule.Quotient.mk ⟨z84 π zs (i+1) p.1.1,q0 p⟩
    map_add':=fun _ _=>by simp [map_add];rfl
    map_smul':=fun _ _=>by simp [map_smul];rfl }
  have hΦ_surj:Surjective Φ := by
   intro x;obtain ⟨⟨abar,habar⟩,rfl⟩:=Submodule.Quotient.mk_surjective _ x;obtain ⟨a,ha⟩:=z87 hπ_surj zs (i+1) abar
   have q4:z84 π zs i (z82 R M zs i a)=0:=by
    rw [z85 π zs i a,ha];exact LinearMap.mem_ker.mp habar
   obtain ⟨b',hb'⟩:=(hπ_ker i (z82 R M zs i a)).mp q4
   have hab:(a,-b')∈LinearMap.ker (z82 R M (z :: zs) i):=by
    rw [LinearMap.mem_ker]
    cases i with
    | zero =>
     change z82 R M zs 0 a+z•(-b')=0;rw [smul_neg,hb',add_neg_cancel]
    | succ j =>
     apply Prod.ext
     ·
      change z82 R M zs (j+1) a+z•(-b')=0;rw [smul_neg,hb',add_neg_cancel]
     ·
      change -(z82 R M zs j (-b'))=0;rw [map_neg,neg_neg];apply z92 hz zs j;dsimp only;rw [smul_zero,← map_smul,hb',z83 zs j a]
   refine ⟨⟨(a,-b'),hab⟩,?_⟩
   change Submodule.Quotient.mk (⟨z84 π zs (i+1) a,q0 ⟨(a,-b'),hab⟩⟩ : LinearMap.ker (z82 R Mbar zs i))=Submodule.Quotient.mk (⟨abar,habar⟩ : LinearMap.ker (z82 R Mbar zs i));congr 1;exact Subtype.ext ha
  have hΦ_ker:LinearMap.ker Φ =
    (LinearMap.range (z82 R M (z :: zs) (i+1))).comap
     (LinearMap.ker (z82 R M (z :: zs) i)).subtype:=by
   ext ⟨⟨a,b⟩,hab⟩;simp only [LinearMap.mem_ker,Φ,LinearMap.coe_mk,AddHom.coe_mk,Submodule.Quotient.mk_eq_zero,Submodule.mem_comap,Submodule.coe_subtype,LinearMap.mem_range];constructor
   ·
    rintro ⟨ubar,hubar⟩;obtain ⟨u,rfl⟩:=z87 hπ_surj zs (i+2) ubar;rw [← z85 π zs (i+1) u] at hubar
    have q3:z84 π zs (i+1) (a - z82 R M zs (i+1) u)=0:=by
     rw [map_sub,hubar,sub_self]
    obtain ⟨v,hv⟩:=(hπ_ker (i+1) (a - z82 R M zs (i+1) u)).mp q3
    have q1:a=z82 R M zs (i+1) u+z•v:=by rw [hv];abel
    have h1:z82 R M zs i a+z•b=0:=by
     cases i with
     | zero=>exact LinearMap.mem_ker.mp hab
     | succ j=>exact congrArg Prod.fst (LinearMap.mem_ker.mp hab)
    have q2 : -(z82 R M zs i v)=b:=by
     apply z92 hz zs i;dsimp only;rw [smul_neg,← map_smul]
     have h2:z82 R M zs i a=z82 R M zs i (z•v):=by
      rw [q1,map_add,z83 zs i u,zero_add]
     rw [← h2];exact (eq_neg_of_add_eq_zero_right h1).symm
    refine ⟨(u,v),?_⟩
    apply Prod.ext
    · exact q1.symm
    · exact q2
   ·
    rintro ⟨⟨u,v⟩,huv⟩;have h1:z82 R M zs (i+1) u+z•v=a:=congrArg Prod.fst huv
    refine ⟨z84 π zs (i+2) u,?_⟩
    rw [← z85 π zs (i+1) u,← h1,map_add];have hzv:z84 π zs (i+1) (z•v)=0:=(hπ_ker (i+1) (z•v)).mpr ⟨v,rfl⟩;rw [hzv,add_zero]
  exact ⟨(Submodule.quotEquivOfEq _ _ hΦ_ker.symm).trans (Φ.quotKerEquivOfSurjective hΦ_surj)⟩
def z110 {R:Type} [CommRing R] :
  (M:Type) → [AddCommGroup M] → [Module R M]→List R→Prop
 | _,_,_,[]=>True
 | M,_,_,z :: zs =>
  IsSMulRegular M z∧z110 (M⧸LinearMap.range (z•LinearMap.id (R:=R) (M:=M))) zs
lemma z111 {R:Type} [CommRing R] :
  ∀ (zs:List R) (M:Type) [AddCommGroup M] [Module R M],z110 M zs→∀ i : ℕ,Subsingleton (z94 R M zs (i+1))
 | [],M,_,_,_,i=>z95 [] (i+1) (by simp)
 | z :: zs,M,_,_,⟨hz,hrest⟩,i=>by
  obtain ⟨e⟩:=z109 z zs hz (i+1);have : Subsingleton (z94 R (M⧸LinearMap.range (z•LinearMap.id (R:=R) (M:=M))) zs (i+1)):=z111 zs _ hrest i;exact e.toEquiv.subsingleton
private def z112 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ),(M ⊗[R] z80 R R zs k) ≃ₗ[R] z80 R M zs k
 | [],0=>TensorProduct.rid R M
 | [],_+1 =>
  {
   toFun:=fun _=>PUnit.unit
   invFun:=fun _=>0
   map_add':=fun _ _=>rfl
   map_smul':=fun _ _=>rfl
   left_inv:=fun t=>by
    induction t using TensorProduct.induction_on with
    | zero=>rfl
    | tmul m u =>
     have : u=0:=Subsingleton.elim u 0;rw [this,tmul_zero]
    | add t₁ t₂ ih₁ ih₂=>rw [← ih₁,← ih₂,add_zero]
   right_inv:=fun _=>rfl }
 | _ :: zs,0=>z112 zs 0
 | _ :: zs,i+1 =>
  (TensorProduct.prodRight R R M (z80 R R zs (i+1)) (z80 R R zs i)).trans
   (LinearEquiv.prodCongr (z112 zs (i+1)) (z112 zs i))
private lemma z113 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ) (t:M ⊗[R] z80 R R zs (k+1)),
   z112 (M:=M) zs k (LinearMap.lTensor M (z82 R R zs k) t)=z82 R M zs k (z112 (M:=M) zs (k+1) t)
 | [],0,t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp [z82]
  | tmul m u=>simp [z82,z112]
  | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
 | [],_+1,_=>rfl
 | z :: zs,0,t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp
  | tmul m p =>
   rcases p with ⟨a,b⟩
   have ih0:=z113 (M:=M) zs 0 (m ⊗ₜ[R] a);simp only [LinearMap.lTensor_tmul] at ih0 ⊢
   change z112 (M:=M) zs 0 (m ⊗ₜ[R] (z82 R R zs 0 a+z•b)) =
    z82 R M zs 0 (z112 (M:=M) zs 1 (m ⊗ₜ[R] a))+z•z112 (M:=M) zs 0 (m ⊗ₜ[R] b)
   rw [tmul_add,map_add,TensorProduct.tmul_smul,map_smul,ih0]
  | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
 | z :: zs,i+1,t=>by
  induction t using TensorProduct.induction_on with
  | zero=>simp
  | tmul m p =>
   rcases p with ⟨a,b⟩
   have ih1:=z113 (M:=M) zs (i+1) (m ⊗ₜ[R] a);have ih2:=z113 (M:=M) zs i (m ⊗ₜ[R] b);simp only [LinearMap.lTensor_tmul] at ih1 ih2 ⊢;apply Prod.ext
   ·
    change z112 (M:=M) zs (i+1) (m ⊗ₜ[R] (z82 R R zs (i+1) a+z•b)) =
     z82 R M zs (i+1) (z112 (M:=M) zs (i+2) (m ⊗ₜ[R] a))+z•z112 (M:=M) zs (i+1) (m ⊗ₜ[R] b)
    rw [tmul_add,map_add,TensorProduct.tmul_smul,map_smul,ih1]
   ·
    change z112 (M:=M) zs i (m ⊗ₜ[R] (-(z82 R R zs i b))) = -(z82 R M zs i (z112 (M:=M) zs (i+1) (m ⊗ₜ[R] b)))
    rw [tmul_neg,map_neg,ih2]
  | add t₁ t₂ ih₁ ih₂=>simp [map_add,ih₁,ih₂]
lemma z114 {R:Type} [CommRing R]
  (zs:List R) (q3:z110 R zs)
  (M:Type) [AddCommGroup M] [Module R M] (i : ℕ) :
  Nonempty (z56 R M (R⧸ofList zs) i ≃ₗ[R] z94 R M zs i):=by
 let KR:=z97 R R zs;let ε : z80 R R zs 0 →ₗ[R] (R⧸ofList zs):=(ofList zs).mkQ.comp (z81 R R zs).toLinearMap;have hε_surj:Surjective ε := (Submodule.mkQ_surjective _).comp (z81 R R zs).surjective
 have hε_ker:LinearMap.range (z82 R R zs 0)=LinearMap.ker ε := by
  have hr:=z100 (R:=R) (M:=R) zs;rw [smul_eq_mul,mul_top] at hr;ext x;rw [LinearMap.mem_ker];change x∈(z82 R R zs 0).range↔Submodule.Quotient.mk (z81 R R zs x)=0;rw [Submodule.Quotient.mk_eq_zero,← hr,Submodule.mem_map]
  exact ⟨fun hx=>⟨x,hx,rfl⟩,fun ⟨y,hy,hyx⟩=>((z81 R R zs).injective hyx)▸hy⟩
 have q1:∀ k : ℕ,Module.Projective R (KR.X k):=fun k=>z91 zs k
 have hε_comp:∀ x:KR.X 1,ε ((KR.d 1 0).hom x)=0:=fun x=>by
  let x':z80 R R zs 1:=x;change ε (z82 R R zs 0 x')=0;rw [← LinearMap.mem_ker,← hε_ker];exact ⟨x',rfl⟩
 have hε_exact:∀ x:KR.X 0,ε x=0→∃ y:KR.X 1,(KR.d 1 0).hom y=x:=fun x hx=>by
  let x':z80 R R zs 0:=x;have hx' : ε x'=0:=hx;obtain ⟨y,hy⟩:=LinearMap.mem_range.mp (hε_ker.symm▸LinearMap.mem_ker.mpr hx');exact ⟨y,by rw [z98];exact hy⟩
 have q0:∀ n : ℕ,∀ x:KR.X (n+1),(KR.d (n+1) n).hom x=0→∃ y:KR.X (n+2),(KR.d (n+2) (n+1)).hom y=x:=fun n x hx=>by
  let x':z80 R R zs (n+1):=x
  have hx':z82 R R zs n x'=0:=by rw [← z98];exact hx
  have hsub:Subsingleton (z94 R R zs (n+1)):=z111 zs R q3 n;have hq0:(Submodule.Quotient.mk ⟨x',LinearMap.mem_ker.mpr hx'⟩ : z94 R R zs (n+1))=0:=Subsingleton.elim _ 0;rw [Submodule.Quotient.mk_eq_zero,Submodule.mem_comap,Submodule.coe_subtype,LinearMap.mem_range] at hq0;obtain ⟨y,hy⟩:=hq0;exact ⟨y,by rw [z98];exact hy⟩
 let P:ProjectiveResolution (ModuleCat.of R (R⧸ofList zs)):=z62 (R⧸ofList zs) KR q1 ε hε_surj hε_comp hε_exact q0;let F:=(tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M);let e1:z56 R M (R⧸ofList zs) i ≅ ((F.mapHomologicalComplex _).obj P.complex).homology i:=P.isoLeftDerivedObj F i;have hPK:P.complex=KR:=rfl
 let q2:(F.mapHomologicalComplex _).obj KR ≅ z97 R M zs :=
  HomologicalComplex.Hom.isoOfComponents
   (fun k=>(z112 (R:=R) (M:=M) zs k).toModuleIso)
   (fun k l hkl=>by
    have hk:k=l+1:=by
     change l+1=k at hkl;exact hkl.symm
    subst hk;apply ModuleCat.hom_ext;apply LinearMap.ext;intro t
    change ((z97 R M zs).d (l+1) l).hom (z112 (M:=M) zs (l+1) t)=z112 (M:=M) zs l (LinearMap.lTensor M ((KR.d (l+1) l).hom) t)
    rw [z98,z98]
    exact (z113 (M:=M) zs l t).symm)
 let e2:((F.mapHomologicalComplex _).obj P.complex).homology i ≅ (z97 R M zs).homology i:=(HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ) i).mapIso q2;obtain ⟨e3⟩:=z99 (R:=R) (M:=M) zs i;exact ⟨(e1 ≪≫ e2).toLinearEquiv.trans e3⟩
noncomputable def z115 (R M:Type) [CommRing R] [AddCommGroup M] [Module R M]
  (zs:List R) : ℤ :=
 ∑ i∈Finset.range (zs.length+1),(-1 : ℤ) ^ i*(Module.length R (z94 R M zs i)).toNat
lemma z116 {R A B C:Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  (i:A →ₗ[R] B) (p:B →ₗ[R] C)
  (hi:Injective i) (hp:Surjective p)
  (hip:LinearMap.range i=LinearMap.ker p) (zs:List R) :
  ∃ (f:∀ n,z94 R A zs n →ₗ[R] z94 R B zs n)
   (g:∀ n,z94 R B zs n →ₗ[R] z94 R C zs n)
   (δ : ∀ n,z94 R C zs (n+1) →ₗ[R] z94 R A zs n),
   (∀ n,Function.Exact (δ n) (f n)) ∧
   (∀ n,Function.Exact (f n) (g n)) ∧
   (∀ n,Function.Exact (g (n+1)) (δ n)) ∧
   Surjective (g 0):=by
 let KA:=z97 R A zs;let KB:=z97 R B zs;let KC:=z97 R C zs
 let fi:KA ⟶ KB :=
  {
   f:=fun n=>ModuleCat.ofHom (z84 i zs n)
   comm':=fun k l hkl=>by
    have hk:k=l+1:=by change l+1=k at hkl;exact hkl.symm
    subst hk;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;change ((KB.d (l+1) l).hom) (z84 i zs (l+1) x)=z84 i zs l (((KA.d (l+1) l).hom) x);rw [z98,z98]
    exact (z85 i zs l x).symm }
 let fp:KB ⟶ KC :=
  {
   f:=fun n=>ModuleCat.ofHom (z84 p zs n)
   comm':=fun k l hkl=>by
    have hk:k=l+1:=by change l+1=k at hkl;exact hkl.symm
    subst hk;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;change ((KC.d (l+1) l).hom) (z84 p zs (l+1) x)=z84 p zs l (((KB.d (l+1) l).hom) x);rw [z98,z98]
    exact (z85 p zs l x).symm }
 have q4:CategoryStruct.comp fi fp=0:=by
  apply HomologicalComplex.hom_ext;intro n;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;change z84 p zs n (z84 i zs n x)=0;rw [← LinearMap.mem_ker,← z88 hip zs n];exact ⟨x,rfl⟩
 let S:ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ):=ShortComplex.mk fi fp q4
 have hS:S.ShortExact:=by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact;intro n
  have q3:Mono (S.map (HomologicalComplex.eval _ _ n)).f:=by
   rw [ModuleCat.mono_iff_injective];exact z86 hi zs n
  have q7:Epi (S.map (HomologicalComplex.eval _ _ n)).g:=by
   rw [ModuleCat.epi_iff_surjective];exact z87 hp zs n
  have hex:(S.map (HomologicalComplex.eval _ _ n)).Exact:=by
   rw [ShortComplex.moduleCat_exact_iff];intro x hx;let x':z80 R B zs n:=x;have hx':z84 p zs n x'=0:=hx;obtain ⟨a,ha⟩:=LinearMap.mem_range.mp ((z88 hip zs n).symm▸LinearMap.mem_ker.mpr hx');exact ⟨a,ha⟩
  exact { exact:=hex,mono_f:=q3,epi_g:=q7 }
 let eA (n : ℕ) : KA.homology n ≃ₗ[R] z94 R A zs n:=(z99 (R:=R) (M:=A) zs n).some;let eB (n : ℕ) : KB.homology n ≃ₗ[R] z94 R B zs n:=(z99 (R:=R) (M:=B) zs n).some;let eC (n : ℕ) : KC.homology n ≃ₗ[R] z94 R C zs n:=(z99 (R:=R) (M:=C) zs n).some
 let f (n : ℕ) : z94 R A zs n →ₗ[R] z94 R B zs n:=(eB n).toLinearMap.comp ((HomologicalComplex.homologyMap S.f n).hom.comp (eA n).symm.toLinearMap);let g (n : ℕ) : z94 R B zs n →ₗ[R] z94 R C zs n:=(eC n).toLinearMap.comp ((HomologicalComplex.homologyMap S.g n).hom.comp (eB n).symm.toLinearMap)
 let δ (n : ℕ) : z94 R C zs (n+1) →ₗ[R] z94 R A zs n:=(eA n).toLinearMap.comp ((hS.δ (n+1) n rfl).hom.comp (eC (n+1)).symm.toLinearMap)
 refine ⟨f,g,δ,?_,?_,?_,?_⟩
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₁ (n+1) n rfl);constructor
  ·
   intro hx;have hx':(HomologicalComplex.homologyMap S.f n).hom ((eA n).symm x)=0:=(eB n).injective (by simpa [f] using hx);obtain ⟨y,hy⟩:=hex ((eA n).symm x) hx';exact ⟨eC (n+1) y,by simp [δ,hy]⟩
  ·
   rintro ⟨z,rfl⟩
   have q6:=congrArg (fun φ : S.X₃.homology (n+1) ⟶ S.X₂.homology n =>
    φ.hom ((eC (n+1)).symm z)) (hS.δ_comp (n+1) n rfl)
   simp only [f,δ,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply]
   rw [show (HomologicalComplex.homologyMap S.f n).hom ((hS.δ (n+1) n rfl).hom ((eC (n+1)).symm z))=0
    from q6,map_zero]
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₂ n);constructor
  ·
   intro hx;have hx':(HomologicalComplex.homologyMap S.g n).hom ((eB n).symm x)=0:=(eC n).injective (by simpa [g] using hx);obtain ⟨y,hy⟩:=hex ((eB n).symm x) hx';exact ⟨eA n y,by simp [f,hy]⟩
  ·
   rintro ⟨z,rfl⟩
   have h0:CategoryStruct.comp (HomologicalComplex.homologyMap S.f n)
     (HomologicalComplex.homologyMap S.g n)=0:=by
    rw [← HomologicalComplex.homologyMap_comp,S.zero,HomologicalComplex.homologyMap_zero]
   have q6:=congrArg (fun φ : S.X₁.homology n ⟶ S.X₃.homology n =>
    φ.hom ((eA n).symm z)) h0
   simp only [g,f,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply]
   rw [show (HomologicalComplex.homologyMap S.g n).hom
     ((HomologicalComplex.homologyMap S.f n).hom ((eA n).symm z))=0 from q6,map_zero]
 ·
  intro n x;have hex:=(ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₃ (n+1) n rfl);constructor
  ·
   intro hx;have hx':(hS.δ (n+1) n rfl).hom ((eC (n+1)).symm x)=0:=(eA n).injective (by simpa [δ] using hx);obtain ⟨y,hy⟩:=hex ((eC (n+1)).symm x) hx';exact ⟨eB (n+1) y,by simp [g,hy]⟩
  ·
   rintro ⟨z,rfl⟩
   have q6:=congrArg (fun φ : S.X₂.homology (n+1) ⟶ S.X₁.homology n =>
    φ.hom ((eB (n+1)).symm z)) (hS.comp_δ (n+1) n rfl)
   simp only [δ,g,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,LinearEquiv.symm_apply_apply]
   rw [show (hS.δ (n+1) n rfl).hom
     ((HomologicalComplex.homologyMap S.g (n+1)).hom ((eB (n+1)).symm z))=0 from q6,map_zero]
 ·
  intro c
  have q0:Epi (S.g.f 0):=by
   rw [ModuleCat.epi_iff_surjective];exact z87 hp zs 0
  have q1:Epi (HomologicalComplex.opcyclesMap S.g 0):=epi_of_epi_fac (HomologicalComplex.p_opcyclesMap S.g 0)
  have q2:CategoryStruct.comp (HomologicalComplex.homologyMap S.g 0)
    (ChainComplex.isoHomologyι₀ KC).hom =
    CategoryStruct.comp (ChainComplex.isoHomologyι₀ KB).hom
     (HomologicalComplex.opcyclesMap S.g 0) :=
   HomologicalComplex.homologyι_naturality S.g 0
  have q5:Epi (HomologicalComplex.homologyMap S.g 0):=by
   have h1:=congrArg (fun φ=>CategoryStruct.comp φ (ChainComplex.isoHomologyι₀ KC).inv) q2
   simp only [Category.assoc,Iso.hom_inv_id,Category.comp_id] at h1;rw [h1];exact epi_comp _ _
  obtain ⟨b,hb⟩:=(ModuleCat.epi_iff_surjective _).mp q5 ((eC 0).symm c);exact ⟨eB 0 b,by simp [g,hb]⟩
private lemma z117 {R M N:Type} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f:M →ₗ[R] N) (hM:IsFiniteLength R M) :
  (Module.length R M).toNat=(Module.length R (LinearMap.ker f)).toNat+(Module.length R (LinearMap.range f)).toNat:=by
 have h1:Module.length R M=Module.length R (LinearMap.ker f)+Module.length R (LinearMap.range f):=by
  have hq:=Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
   Subtype.val_injective (Submodule.mkQ_surjective _)
   (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ,Submodule.range_subtype]))
  rw [hq,(f.quotKerEquivRange).length_eq]
 have q2:Module.length R M ≠ ⊤ := Module.length_ne_top_iff.mpr hM;have q1:Module.length R (LinearMap.ker f) ≠ ⊤ := ne_top_of_le_ne_top q2 (Module.length_le_of_injective (LinearMap.ker f).subtype Subtype.val_injective);have q0:Module.length R (LinearMap.range f) ≠ ⊤ := ne_top_of_le_ne_top q2 (Module.length_le_of_surjective f.rangeRestrict (LinearMap.surjective_rangeRestrict f))
 rw [h1,ENat.toNat_add q1 q0]
lemma z118 {R A B C:Type} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  (i:A →ₗ[R] B) (p:B →ₗ[R] C)
  (hi:Injective i) (hp:Surjective p)
  (hip:LinearMap.range i=LinearMap.ker p) (zs:List R)
  (hA:∀ k,IsFiniteLength R (z94 R A zs k))
  (hB:∀ k,IsFiniteLength R (z94 R B zs k))
  (hC:∀ k,IsFiniteLength R (z94 R C zs k)) :
  z115 R B zs=z115 R A zs+z115 R C zs:=by
 obtain ⟨f,g,δ,h1,h2,h3,hg0⟩:=z116 i p hi hp hip zs;let r (n : ℕ) : ℤ := (Module.length R (LinearMap.range (δ n))).toNat
 have q4:((Module.length R (z94 R B zs 0)).toNat : ℤ) -
   ((Module.length R (z94 R A zs 0)).toNat : ℤ) -
   ((Module.length R (z94 R C zs 0)).toNat : ℤ) = - r 0:=by
  have hA0:=z117 (f 0) (hA 0);have hB0:=z117 (g 0) (hB 0);have hkA:LinearMap.ker (f 0)=LinearMap.range (δ 0):=LinearMap.exact_iff.mp (h1 0);have hkB:LinearMap.ker (g 0)=LinearMap.range (f 0):=LinearMap.exact_iff.mp (h2 0);have hrC:LinearMap.range (g 0) = ⊤ := LinearMap.range_eq_top.mpr hg0;rw [hkA] at hA0;rw [hkB,hrC,Module.length_top] at hB0;dsimp only [r];omega
 have q3:∀ n : ℕ,
   ((Module.length R (z94 R B zs (n+1))).toNat : ℤ) -
    ((Module.length R (z94 R A zs (n+1))).toNat : ℤ) -
    ((Module.length R (z94 R C zs (n+1))).toNat : ℤ) =
   - r (n+1) - r n:=by
  intro n;have hAn:=z117 (f (n+1)) (hA (n+1));have hBn:=z117 (g (n+1)) (hB (n+1));have hCn:=z117 (δ n) (hC (n+1));have hkA:LinearMap.ker (f (n+1))=LinearMap.range (δ (n+1)):=LinearMap.exact_iff.mp (h1 (n+1));have hkB:LinearMap.ker (g (n+1))=LinearMap.range (f (n+1)):=LinearMap.exact_iff.mp (h2 (n+1))
  have hkC:LinearMap.ker (δ n)=LinearMap.range (g (n+1)):=LinearMap.exact_iff.mp (h3 n);rw [hkA] at hAn;rw [hkB] at hBn;rw [hkC] at hCn;dsimp only [r];omega
 have q2:∀ m : ℕ,
   ∑ k∈Finset.range (m+1),
    (-1 : ℤ) ^ k *
     (((Module.length R (z94 R B zs k)).toNat : ℤ) -
      ((Module.length R (z94 R A zs k)).toNat : ℤ) -
      ((Module.length R (z94 R C zs k)).toNat : ℤ)) =
   (-1 : ℤ) ^ (m+1)*r m:=by
  intro m
  induction m with
  | zero =>
   rw [Finset.sum_range_one,pow_zero,one_mul,pow_one,q4];ring
  | succ m ih =>
   rw [Finset.sum_range_succ,ih,q3 m];ring
 have q0:r zs.length=0:=by
  have : Subsingleton (z94 R C zs (zs.length+1)):=z95 zs (zs.length+1) (Nat.lt_succ_self _)
  have : Subsingleton (LinearMap.range (δ zs.length)) :=
   subsingleton_iff_forall_eq 0 |>.mpr fun z=>by
    rcases z with ⟨y,⟨x,rfl⟩⟩
    apply Subtype.ext;change δ zs.length x=0;rw [Subsingleton.elim x 0,map_zero]
  dsimp only [r];rw [Module.length_eq_zero];rfl
 have q5:=q2 zs.length;rw [q0,mul_zero] at q5;unfold z115
 have q1 :
   ∑ k∈Finset.range (zs.length+1),
    (-1 : ℤ) ^ k *
     (((Module.length R (z94 R B zs k)).toNat : ℤ) -
      ((Module.length R (z94 R A zs k)).toNat : ℤ) -
      ((Module.length R (z94 R C zs k)).toNat : ℤ)) =
   (∑ k∈Finset.range (zs.length+1),(-1 : ℤ) ^ k*(Module.length R (z94 R B zs k)).toNat) -
   (∑ k∈Finset.range (zs.length+1),(-1 : ℤ) ^ k*(Module.length R (z94 R A zs k)).toNat) -
   (∑ k∈Finset.range (zs.length+1),(-1 : ℤ) ^ k*(Module.length R (z94 R C zs k)).toNat):=by
  simp only [mul_sub,Finset.sum_sub_distrib]
 linarith
end KoszulComplex
section KoszulPositivity
open IsLocalRing
lemma z119 {A M:Type} [CommRing A]
  [IsLocalRing A] [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
  (h:(annihilator A M).radical=maximalIdeal A∨Subsingleton M) :
  IsFiniteLength A M:=by
 rcases h with hrad | q4
 ·
  have hfg:(maximalIdeal A).FG:=IsNoetherian.noetherian (maximalIdeal A)
  have q5:∃ k : ℕ,maximalIdeal A ^ k ≤ annihilator A M:=by
   have hle:maximalIdeal A ≤ (annihilator A M).radical:=hrad.symm.le;exact Ideal.exists_pow_le_of_le_radical_of_fg hle hfg
  obtain ⟨k,hk⟩:=q5
  suffices ∀ (k : ℕ) (N:Type) [AddCommGroup N] [Module A N] [Module.Finite A N],maximalIdeal A ^ k ≤ annihilator A N→IsFiniteLength A N from
   this k M hk
  intro k
  induction k with
  | zero =>
   intro N _ _ _ hN;have h1:(1:A)∈annihilator A N:=hN (by simp)
   have : Subsingleton N:=subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
    have:=Module.mem_annihilator.mp h1 x;simpa using this
   rw [← Module.length_ne_top_iff,Module.length_eq_zero];exact ENat.zero_ne_top
  | succ k ih =>
   intro N _ _ _ hN;let J:Submodule A N:=maximalIdeal A•(⊤ : Submodule A N);have : Module.Finite A J:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian J)
   have q1:IsFiniteLength A J:=ih J (fun a ha=>by
    rw [Module.mem_annihilator];intro ⟨y,hy⟩;apply Subtype.ext;change a•y=0
    refine Submodule.smul_induction_on hy ?_ ?_
    ·
     intro r hr z _;rw [smul_smul]
     have q6:a*r∈maximalIdeal A ^ (k+1):=by
      rw [pow_succ];exact mul_mem_mul ha hr
     exact Module.mem_annihilator.mp (hN q6) z
    ·
     intro u v hu hv
     rw [smul_add,hu,hv,add_zero])
   let kA:=A⧸maximalIdeal A
   letI : Field kA:=Ideal.Quotient.field (maximalIdeal A)
   have q0:∀ a∈maximalIdeal A,∀ q:N⧸J,a•q=0:=fun a ha q=>by
    obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective J q
    change Submodule.Quotient.mk (p:=J) (a•x)=0
    rw [Submodule.Quotient.mk_eq_zero];exact Submodule.smul_mem_smul ha Submodule.mem_top
   letI : Module kA (N⧸J) :=
    {
     smul:=fun r q=>Quotient.liftOn' r (fun a=>a•q) (fun a b hab=>by
      have q4:b - a∈maximalIdeal A:=by
       simpa [sub_eq_neg_add] using QuotientAddGroup.leftRel_apply.mp hab
      have hba:b=a+(b - a):=by ring
      rw [hba,add_smul,q0 _ q4 q,add_zero])
     one_smul:=fun q=>one_smul A q
     mul_smul:=fun r s q=>Quotient.inductionOn₂' r s fun a b=>mul_smul a b q
     smul_zero:=fun r=>Quotient.inductionOn' r fun a=>smul_zero a
     smul_add:=fun r q₁ q₂=>Quotient.inductionOn' r fun a=>smul_add a q₁ q₂
     add_smul:=fun r s q=>Quotient.inductionOn₂' r s fun a b=>add_smul a b q
     zero_smul:=fun q=>zero_smul A q }
   haveI : IsScalarTower A kA (N⧸J):=⟨fun a r q=>Quotient.inductionOn' r fun b=>mul_smul a b q⟩
   have : Module.Finite kA (N⧸J):=Module.Finite.of_restrictScalars_finite A kA (N⧸J);have q2:Module.length A (N⧸J)=Module.length kA (N⧸J):=Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
   have q3:IsFiniteLength A (N⧸J):=by
    rw [← Module.length_ne_top_iff,q2,Module.length_eq_finrank];exact ENat.coe_ne_top _
   rw [← Module.length_ne_top_iff]
   rw [Module.length_eq_add_of_exact J.subtype J.mkQ Subtype.val_injective
    (Submodule.mkQ_surjective J) (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ,Submodule.range_subtype]))]
   exact WithTop.add_ne_top.mpr ⟨Module.length_ne_top_iff.mpr q1,Module.length_ne_top_iff.mpr q3⟩
 ·
  rw [← Module.length_ne_top_iff,Module.length_eq_zero];exact ENat.zero_ne_top
lemma z120 {A M:Type} [CommRing A] [IsNoetherianRing A]
  [AddCommGroup M] [Module A M] [Module.Finite A M]
  (Pred:∀ (N:Type) [AddCommGroup N] [Module A N],Prop)
  (q8:∀ (N₁ N₂ : Type) [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂],(N₁ ≃ₗ[A] N₂)→Pred N₁ → Pred N₂)
  (q11:∀ (N:Type) [AddCommGroup N] [Module A N],Subsingleton N→Pred N)
  (q7:∀ (P:Ideal A),P.IsPrime→annihilator A M ≤ P→Pred (A⧸P))
  (q12:∀ (N₁ N₂ N₃ : Type) [AddCommGroup N₁] [Module A N₁] [AddCommGroup N₂] [Module A N₂]
   [AddCommGroup N₃] [Module A N₃] (i:N₁ →ₗ[A] N₂) (p:N₂ →ₗ[A] N₃),
   Injective i→Surjective p→LinearMap.range i=LinearMap.ker p →
   Module.Finite A N₁ → Module.Finite A N₂ → Module.Finite A N₃ →
   annihilator A M ≤ annihilator A N₁ →
   annihilator A M ≤ annihilator A N₂ →
   annihilator A M ≤ annihilator A N₃ →
   Pred N₁ → Pred N₃ → Pred N₂) :
  Pred M:=by
 let S:Set (Submodule A M):={ N:Submodule A M | Pred N };have q14:(⊥ : Submodule A M)∈S:=q11 (⊥ : Submodule A M) inferInstance;obtain ⟨N₀,hN₀_mem,hN₀_max⟩:=set_has_maximal_iff_noetherian.mpr (inferInstance:IsNoetherian A M) S ⟨⊥,q14⟩
 by_cases htop:N₀ = ⊤
 ·
  subst htop;exact q8 (⊤ : Submodule A M) M Submodule.topEquiv hN₀_mem
 ·
  have hnt:∃ x:M⧸N₀,x≠0:=by
   by_contra h;push Not at h
   apply htop;rw [eq_top_iff];intro m _;exact (Submodule.Quotient.mk_eq_zero N₀).mp (h (Submodule.Quotient.mk m))
  let elAnn (x:M⧸N₀) : Ideal A :=
   {
    carrier:={ a:A | a•x=0 }
    add_mem':=fun {a b} ha hb=>by simp only [Set.mem_setOf_eq] at ha hb ⊢;rw [add_smul,ha,hb,add_zero]
    zero_mem':=by simp
    smul_mem':=fun r {a} ha=>by simp only [Set.mem_setOf_eq] at ha ⊢;rw [smul_eq_mul,mul_smul,ha,smul_zero] }
  let T:Set (Ideal A):={ I:Ideal A | ∃ x:M⧸N₀,x≠0∧I=elAnn x };obtain ⟨x_init,hx_init⟩:=hnt
  obtain ⟨P,⟨x₀,hx₀_ne,rfl⟩,hP_max⟩ :=
   set_has_maximal_iff_noetherian.mpr (inferInstance:IsNoetherian A A) T
    ⟨elAnn x_init,x_init,hx_init,rfl⟩
  have q1:(elAnn x₀).IsPrime:=by
   refine ⟨?_,?_⟩
   ·
    intro h1;have q13:(1:A)∈elAnn x₀ := h1.symm▸Submodule.mem_top;exact hx₀_ne (by simpa [elAnn] using q13)
   ·
    intro a b hab
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨ha,hb⟩
    have hbx:b•x₀ ≠ 0:=hb
    have hle:elAnn x₀ ≤ elAnn (b•x₀):=fun r hr=>by
     change r•(b•x₀)=0;rw [smul_comm,hr,smul_zero]
    have heq:elAnn x₀ = elAnn (b•x₀):=eq_of_le_of_not_lt hle (hP_max (elAnn (b•x₀)) ⟨b•x₀,hbx,rfl⟩)
    have q5:a∈elAnn (b•x₀):=by
     change a•(b•x₀)=0;rw [← mul_smul];exact hab
    exact ha (heq▸q5)
  have q2:annihilator A M ≤ elAnn x₀ := fun a ha=>by
   obtain ⟨m,rfl⟩:=Submodule.Quotient.mk_surjective N₀ x₀
   change Submodule.Quotient.mk (p:=N₀) (a•m)=0
   rw [Module.mem_annihilator.mp ha m,Submodule.Quotient.mk_zero]
  have q3:Pred (A⧸elAnn x₀):=q7 (elAnn x₀) q1 q2;obtain ⟨m₀,hm₀⟩:=Submodule.Quotient.mk_surjective N₀ x₀;let N₁ : Submodule A M:=N₀ ⊔ Submodule.span A {m₀}
  have hN₀_lt:N₀ < N₁ := by
   refine lt_of_le_of_ne le_sup_left fun heq=>hx₀_ne ?_
   rw [← hm₀,Submodule.Quotient.mk_eq_zero,heq];exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  let q10:N₀ →ₗ[A] N₁ := Submodule.inclusion le_sup_left;let K:Submodule A N₁ := N₀.comap N₁.subtype
  let ψ : A →ₗ[A] (N₁ ⧸ K) :=
   {
    toFun:=fun a=>Submodule.Quotient.mk
     ⟨a•m₀,Submodule.mem_sup_right (Submodule.smul_mem _ a (Submodule.subset_span rfl))⟩
    map_add':=fun a b=>by
     change Submodule.Quotient.mk _=Submodule.Quotient.mk _+Submodule.Quotient.mk _;rw [← Submodule.Quotient.mk_add];congr 1;apply Subtype.ext;exact add_smul a b m₀
    map_smul':=fun r a=>by
     change Submodule.Quotient.mk _=r•Submodule.Quotient.mk _;rw [← Submodule.Quotient.mk_smul]
     congr 1;apply Subtype.ext;exact mul_smul r a m₀ }
  have hψ_surj:Surjective ψ := fun q=>by
   obtain ⟨⟨y,hy⟩,rfl⟩:=Submodule.Quotient.mk_surjective K q;rw [Submodule.mem_sup] at hy;obtain ⟨n,hn,z,hz,rfl⟩:=hy;rw [Submodule.mem_span_singleton] at hz;obtain ⟨a,rfl⟩:=hz
   refine ⟨a,?_⟩
   change Submodule.Quotient.mk (p:=K) ⟨a•m₀,_⟩=Submodule.Quotient.mk (p:=K) ⟨n+a•m₀,_⟩
   rw [Submodule.Quotient.eq];change a•m₀ - (n+a•m₀)∈N₀
   have : a•m₀ - (n+a•m₀) = -n:=by abel
   rw [this];exact N₀.neg_mem hn
  have hψ_ker:LinearMap.ker ψ = elAnn x₀ := by
   ext a;simp only [LinearMap.mem_ker,ψ,LinearMap.coe_mk,AddHom.coe_mk,Submodule.Quotient.mk_eq_zero,K,Submodule.mem_comap,Submodule.coe_subtype];change a•m₀ ∈ N₀ ↔ a•x₀ = 0;rw [← hm₀]
   change a•m₀ ∈ N₀ ↔ Submodule.Quotient.mk (p:=N₀) (a•m₀)=0
   rw [Submodule.Quotient.mk_eq_zero]
  let eQ:(A⧸elAnn x₀) ≃ₗ[A] (N₁ ⧸ K):=(Submodule.quotEquivOfEq _ _ hψ_ker.symm).trans (ψ.quotKerEquivOfSurjective hψ_surj);have q4:Pred (N₁ ⧸ K):=q8 (A⧸elAnn x₀) (N₁ ⧸ K) eQ q3;have : Module.Finite A N₀ := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N₀);have : Module.Finite A N₁ := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N₁)
  have : Module.Finite A (N₁ ⧸ K):=inferInstance
  have hAnn_N₀ : annihilator A M ≤ annihilator A N₀ := fun a ha =>
   Module.mem_annihilator.mpr fun ⟨y,_⟩=>Subtype.ext (Module.mem_annihilator.mp ha y)
  have hAnn_N₁ : annihilator A M ≤ annihilator A N₁ := fun a ha =>
   Module.mem_annihilator.mpr fun ⟨y,_⟩=>Subtype.ext (Module.mem_annihilator.mp ha y)
  have q9:annihilator A M ≤ annihilator A (N₁ ⧸ K):=fun a ha =>
   Module.mem_annihilator.mpr fun q=>by
    obtain ⟨⟨y,hy⟩,rfl⟩:=Submodule.Quotient.mk_surjective K q;have h0:(⟨a•y,N₁.smul_mem a hy⟩ : N₁)=0:=Subtype.ext (Module.mem_annihilator.mp ha y)
    change Submodule.Quotient.mk (p:=K) (⟨a•y,N₁.smul_mem a hy⟩ : N₁)=0
    rw [h0,Submodule.Quotient.mk_zero]
  have q0:Injective q10:=Submodule.inclusion_injective le_sup_left
  have q6:LinearMap.range q10=LinearMap.ker K.mkQ:=by
   rw [Submodule.ker_mkQ];ext ⟨y,hy⟩
   exact ⟨fun ⟨⟨z,hz⟩,h⟩=>by
     have hzy:z=y:=congrArg (fun u:N₁=>(u:M)) h
     exact hzy▸hz,
    fun h=>⟨⟨y,h⟩,rfl⟩⟩
  have hPred_N₁ : Pred N₁ :=
   q12 N₀ N₁ (N₁ ⧸ K) q10 K.mkQ q0 (Submodule.mkQ_surjective K) q6
    inferInstance inferInstance inferInstance hAnn_N₀ hAnn_N₁ q9 hN₀_mem q4
  exact absurd hN₀_lt (hN₀_max N₁ hPred_N₁)
private lemma z121 {R M₁ M₂ M₃ : Type} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
  (f:M₁ →ₗ[R] M₂) (g:M₂ →ₗ[R] M₃) :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M₁ zs k),z84 g zs k (z84 f zs k x)=z84 (g.comp f) zs k x
 | [],0,_=>rfl
 | [],_+1,_=>rfl
 | _ :: zs,0,x=>z121 f g zs 0 x
 | _ :: zs,i+1,(a,b)=>Prod.ext (z121 f g zs (i+1) a) (z121 f g zs i b)
private lemma z122 {R M:Type} [CommRing R] [AddCommGroup M] [Module R M] :
  ∀ (zs:List R) (k : ℕ) (x:z80 R M zs k),z84 (LinearMap.id:M →ₗ[R] M) zs k x=x
 | [],0,_=>rfl
 | [],_+1,_=>rfl
 | _ :: zs,0,x=>z122 zs 0 x
 | _ :: zs,i+1,(a,b)=>Prod.ext (z122 zs (i+1) a) (z122 zs i b)
lemma z123 {A:Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
  ∀ (zs:List A),(∀ z∈zs,z∈maximalIdeal A) →
  ∀ (M:Type) [AddCommGroup M] [Module A M] [Module.Finite A M],((annihilator A M⊔ofList zs).radical=maximalIdeal A∨Subsingleton M)→(∀ k,IsFiniteLength A (z94 A M zs k))∧(supportDim A M < (zs.length:WithBot ℕ∞)→z115 A M zs=0)∧(supportDim A M=(zs.length:WithBot ℕ∞)→0 < z115 A M zs):=by
 intro zs hzs
 induction zs with
 | nil =>
  intro M _ _ _ hM
  have q59:∀ k,IsFiniteLength A (z94 A M [] k):=fun k=>by
   have : Module.Finite A (z94 A M [] k):=z96 [] k
   refine z119 ?_
   rcases hM with hrad | hsub
   ·
    simp only [Ideal.ofList_nil,sup_bot_eq] at hrad
    by_cases hnt:Subsingleton (z94 A M [] k)
    · exact Or.inr hnt
    ·
     left
     refine le_antisymm ?_ ?_
     ·
      rw [(maximalIdeal.isMaximal A).isPrime.radical_le_iff]
      have hne:annihilator A (z94 A M [] k) ≠ ⊤ := fun h1=>hnt <|
       subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
        simpa using Module.mem_annihilator.mp (h1▸Submodule.mem_top:(1:A)∈_) x
      exact le_maximalIdeal hne
     ·
      rw [← hrad]
      exact Ideal.radical_mono fun a ha =>
       Module.mem_annihilator.mpr (z102 [] k (Module.mem_annihilator.mp ha))
   ·
    right
    cases k with
    | zero=>exact inferInstance
    | succ i=>exact z95 [] (i+1) (by simp)
  refine ⟨q59,?_,?_⟩
  ·
   intro hlt
   have q58:supportDim A M = ⊥ := by
    cases hd:supportDim A M with
    | bot=>rfl
    | coe d =>
     rw [hd] at hlt;simp only [List.length_nil,Nat.cast_zero] at hlt;exact absurd hlt (not_lt.mpr (WithBot.coe_le_coe.mpr (OrderBot.bot_le d)))
   have : Subsingleton M:=(Module.supportDim_eq_bot_iff_subsingleton A M).mp q58;have : Subsingleton (z94 A M [] 0):=inferInstance;unfold z115;simp [Module.length_eq_zero]
  ·
   intro heq;have hnt:Nontrivial M:=(Module.supportDim_ne_bot_iff_nontrivial A M).mp (by rw [heq];simp);obtain ⟨e0⟩:=z101 (R:=A) (M:=M) []
   have q6:ofList ([] : List A)•(⊤ : Submodule A M) = ⊥ := by simp
   let eM:z94 A M [] 0 ≃ₗ[A] M:=e0.trans ((Submodule.quotEquivOfEq _ _ q6).trans (Submodule.quotEquivOfEqBot ⊥ rfl))
   have q17:0 < Module.length A (z94 A M [] 0):=by
    rw [eM.length_eq];exact Module.length_pos
   have q0:Module.length A (z94 A M [] 0) ≠ ⊤ := Module.length_ne_top_iff.mpr (q59 0)
   have q5:0 < (Module.length A (z94 A M [] 0)).toNat:=by
    cases hL:Module.length A (z94 A M [] 0) with
    | top=>exact absurd hL q0
    | coe n =>
     rw [hL] at q17;simpa using q17
   unfold z115;simp only [List.length_nil,zero_add,Finset.sum_range_one,pow_zero,one_mul];exact Int.natCast_pos.mpr q5
 | cons z zs ih =>
  have q34:z∈maximalIdeal A:=hzs z List.mem_cons_self
  have hzs':∀ w∈zs,w∈maximalIdeal A:=fun w hw=>hzs w (List.mem_cons_of_mem z hw)
  intro M _ _ _ hM
  have q24:∀ (N:Type) [AddCommGroup N] [Module A N] [Module.Finite A N],annihilator A M ≤ annihilator A N→∀ k,IsFiniteLength A (z94 A N (z :: zs) k):=fun N _ _ _ hAnn k=>by
   have : Module.Finite A (z94 A N (z :: zs) k):=z96 (z :: zs) k
   refine z119 ?_
   by_cases hsub:Subsingleton (z94 A N (z :: zs) k)
   · exact Or.inr hsub
   ·
    rcases hM with hrad | hMsub
    ·
     left
     refine le_antisymm ?_ ?_
     ·
      rw [(maximalIdeal.isMaximal A).isPrime.radical_le_iff]
      have hne:annihilator A (z94 A N (z :: zs) k) ≠ ⊤ := fun h1=>hsub <|
       subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
        simpa using Module.mem_annihilator.mp (h1▸Submodule.mem_top:(1:A)∈_) x
      exact le_maximalIdeal hne
     ·
      rw [← hrad]
      refine Ideal.radical_mono (sup_le ?_ ?_)
      ·
       intro a ha
       exact Module.mem_annihilator.mpr
        (z102 (z :: zs) k (Module.mem_annihilator.mp (hAnn ha)))
      ·
       rw [ofList,span_le];intro w hw;exact Module.mem_annihilator.mpr (z106 (z :: zs) k hw)
    ·
     right
     have h1:(1:A)∈annihilator A M:=Module.mem_annihilator.mpr fun m=>Subsingleton.elim _ _
     have : Subsingleton N:=subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
      simpa using Module.mem_annihilator.mp (hAnn h1) x
     have h0:∀ x:z94 A N (z :: zs) k,(1:A)•x=0:=z102 (z :: zs) k fun n=>Subsingleton.elim _ _
     exact subsingleton_iff_forall_eq 0 |>.mpr fun x=>by simpa using h0 x
  let Pred (N:Type) [AddCommGroup N] [Module A N] : Prop:=(supportDim A N < ((z :: zs).length:WithBot ℕ∞)→z115 A N (z :: zs)=0)∧(supportDim A N=((z :: zs).length:WithBot ℕ∞)→0 < z115 A N (z :: zs))
  have q46:Pred M:=by
   refine z120 (A:=A) (M:=M) Pred ?_ ?_ ?_ ?_
   ·
    intro N₁ N₂ _ _ _ _ e ⟨h1,h2⟩;have q50:supportDim A N₁ = supportDim A N₂ := Module.supportDim_eq_of_equiv e
    have q54:z115 A N₁ (z :: zs)=z115 A N₂ (z :: zs):=by
     unfold z115
     refine Finset.sum_congr rfl fun k _ => ?_
     congr 2
     let q52:z97 A N₁ (z :: zs) ≅ z97 A N₂ (z :: zs) :=
      HomologicalComplex.Hom.isoOfComponents
       (fun j =>
        {
         hom:=ModuleCat.ofHom (z84 e.toLinearMap (z :: zs) j)
         inv:=ModuleCat.ofHom (z84 e.symm.toLinearMap (z :: zs) j)
         hom_inv_id:=by
          apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;let x':z80 A N₁ (z :: zs) j:=x;change z84 e.symm.toLinearMap (z :: zs) j (z84 e.toLinearMap (z :: zs) j x')=x';rw [z121,LinearEquiv.symm_comp,z122]
         inv_hom_id:=by
          apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;let x':z80 A N₂ (z :: zs) j:=x;change z84 e.toLinearMap (z :: zs) j (z84 e.symm.toLinearMap (z :: zs) j x')=x'
          rw [z121,LinearEquiv.comp_symm,z122] })
       (fun j l hjl=>by
        have hj:j=l+1:=by change l+1=j at hjl;exact hjl.symm
        subst hj;apply ModuleCat.hom_ext;apply LinearMap.ext;intro x;change ((z97 A N₂ (z :: zs)).d (l+1) l).hom (z84 e.toLinearMap (z :: zs) (l+1) x)=z84 e.toLinearMap (z :: zs) l (((z97 A N₁ (z :: zs)).d (l+1) l).hom x);rw [z98,z98]
        exact (z85 e.toLinearMap (z :: zs) l x).symm)
     obtain ⟨eH1⟩:=z99 (R:=A) (M:=N₁) (z :: zs) k;obtain ⟨eH2⟩:=z99 (R:=A) (M:=N₂) (z :: zs) k
     let eH:=eH1.symm.trans (((HomologicalComplex.homologyFunctor (ModuleCat.{0} A)
      (ComplexShape.down ℕ) k).mapIso q52).toLinearEquiv.trans eH2)
     exact congrArg ENat.toNat eH.length_eq
    exact ⟨fun hlt=>q54▸h1 (q50▸hlt),fun heq=>q54▸h2 (q50▸heq)⟩
   ·
    intro N _ _ hsub
    have q45:z115 A N (z :: zs)=0:=by
     unfold z115
     refine Finset.sum_eq_zero fun k _ => ?_
     have : Subsingleton (z94 A N (z :: zs) k) :=
      subsingleton_iff_forall_eq 0 |>.mpr fun x=>by
       have:=z102 (z :: zs) k (a:=(1:A)) (fun n=>Subsingleton.elim _ _) x
       simpa using this
     simp [Module.length_eq_zero]
    exact ⟨fun _=>q45,fun heq=>by
     rw [Module.supportDim_eq_bot_of_subsingleton] at heq
     exact absurd heq WithBot.bot_ne_coe⟩
   ·
    intro P hP hAnnP
    have q38:(P⊔ofList (z :: zs)).radical=maximalIdeal A:=by
     rcases hM with hrad | hMsub
     ·
      refine le_antisymm ?_ ?_
      ·
       rw [(maximalIdeal.isMaximal A).isPrime.radical_le_iff]
       refine sup_le (le_maximalIdeal hP.ne_top) ?_
       rw [ofList,span_le]
       exact fun w hw=>hzs w hw
      ·
       rw [← hrad];exact Ideal.radical_mono (sup_le_sup_right hAnnP _)
     ·
      exfalso
      have h1:(1:A)∈annihilator A M:=Module.mem_annihilator.mpr fun m=>Subsingleton.elim _ _
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P (hAnnP h1) isUnit_one)
    have q16:supportDim A (A⧸P)=ringKrullDim (A⧸P):=Module.supportDim_quotient_eq_ringKrullDim P
    by_cases hzP:z∈P
    ·
     have q31:∀ x:A⧸P,z•x=0:=fun x=>by
      obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x;change Ideal.Quotient.mk P (z*a)=0;rw [Ideal.Quotient.eq_zero_iff_mem];exact P.mul_mem_right a hzP
     have hradP':(P⊔ofList zs).radical=maximalIdeal A:=by
      have q57:P⊔ofList (z :: zs)=P⊔ofList zs:=by
       rw [Ideal.ofList_cons,← sup_assoc,sup_eq_left.mpr (span_le.mpr (Set.singleton_subset_iff.mpr hzP))]
      rwa [← q57]
     have q23:∀ k,IsFiniteLength A (z94 A (A⧸P) zs k):=(ih hzs' (A⧸P) (Or.inl (by rwa [Ideal.annihilator_quotient]))).1
     have q43:z115 A (A⧸P) (z :: zs)=0:=by
      unfold z115;simp only [List.length_cons];rw [Finset.sum_range_succ'];obtain ⟨e0⟩:=z107 (R:=A) (M:=A⧸P) z zs q31
      have q42:∀ i : ℕ,
        (Module.length A (z94 A (A⧸P) (z :: zs) (i+1))).toNat =
         (Module.length A (z94 A (A⧸P) zs (i+1))).toNat+(Module.length A (z94 A (A⧸P) zs i)).toNat:=fun i=>by
       obtain ⟨ei⟩:=z108 (R:=A) (M:=A⧸P) z zs q31 i
       rw [ei.length_eq,Module.length_prod,
        ENat.toNat_add (Module.length_ne_top_iff.mpr (q23 (i+1)))
         (Module.length_ne_top_iff.mpr (q23 i))]
      have q2:∀ m : ℕ,
        (∑ i∈Finset.range (m+1),
         (-1 : ℤ) ^ (i+1) *
          (((Module.length A (z94 A (A⧸P) zs (i+1))).toNat : ℤ)+((Module.length A (z94 A (A⧸P) zs i)).toNat : ℤ))) +
         (-1 : ℤ) ^ 0*((Module.length A (z94 A (A⧸P) zs 0)).toNat : ℤ) =
        (-1 : ℤ) ^ (m+1)*((Module.length A (z94 A (A⧸P) zs (m+1))).toNat : ℤ):=by
       intro m
       induction m with
       | zero=>simp
       | succ m ihm =>
        rw [Finset.sum_range_succ];push_cast at ihm ⊢;ring_nf at ihm ⊢
        linarith
      have q47:(Module.length A (z94 A (A⧸P) (z :: zs) 0)).toNat=(Module.length A (z94 A (A⧸P) zs 0)).toNat:=by rw [e0.length_eq]
      have q30 : ∑ i∈Finset.range (zs.length+1),(-1 : ℤ) ^ (i+1)*(Module.length A (z94 A (A⧸P) (z :: zs) (i+1))).toNat =
        ∑ i∈Finset.range (zs.length+1),
         (-1 : ℤ) ^ (i+1) *
          (((Module.length A (z94 A (A⧸P) zs (i+1))).toNat : ℤ)+((Module.length A (z94 A (A⧸P) zs i)).toNat : ℤ)):=by
       refine Finset.sum_congr rfl fun i _ => ?_
       rw [q42 i,Nat.cast_add]
      rw [q30,q47,q2 zs.length];have : Subsingleton (z94 A (A⧸P) zs (zs.length+1)):=z95 zs (zs.length+1) (Nat.lt_succ_self _);rw [Module.length_eq_zero];simp
     have q20:ringKrullDim (A⧸P) ≤ (zs.length:WithBot ℕ∞):=by
      classical
      let : IsLocalRing (A⧸P):=z36 P;let s:Finset (A⧸P):=(zs.map (Ideal.Quotient.mk P)).toFinset;have q22:s.card ≤ zs.length:=(List.toFinset_card_le _).trans (by rw [List.length_map]);let J:Ideal (A⧸P):=span (s:Set (A⧸P))
      have q39:J=(ofList zs).map (Ideal.Quotient.mk P):=by
       change span (s:Set (A⧸P))=_;rw [ofList,map_span];congr 1;ext y;change y∈(s:Set (A⧸P))↔_;rw [Finset.mem_coe,List.mem_toFinset,List.mem_map,Set.mem_image];rfl
      have q35:(maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P)=maximalIdeal A:=by
       have : (maximalIdeal (A⧸P)).IsMaximal:=maximalIdeal.isMaximal _;have : ((maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P)).IsMaximal:=comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective;exact eq_maximalIdeal ‹_›
      have q32:J.radical=maximalIdeal (A⧸P):=by
       rw [q39];ext x;obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective x;change (Ideal.Quotient.mk P a∈((ofList zs).map (Ideal.Quotient.mk P)).radical)↔a∈(maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P);rw [q35,← hradP'];constructor
       ·
        rintro ⟨k,hk⟩;rw [← map_pow,mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hk;obtain ⟨b,hb,hab⟩:=hk;have q48:a ^ k - b∈P:=Ideal.Quotient.eq.mp hab.symm
        refine ⟨k,?_⟩
        have : a ^ k=(a ^ k - b)+b:=by ring
        rw [this];exact Ideal.add_mem _ (mem_sup_left q48) (mem_sup_right hb)
       ·
        rintro ⟨k,hk⟩;rw [Submodule.mem_sup] at hk;obtain ⟨p,hp,q,hq,ha⟩:=hk
        refine ⟨k,?_⟩
        rw [← map_pow,← ha,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hp,zero_add];exact mem_map_of_mem _ hq
      have q9:J ≠ ⊤ := fun h=>(maximalIdeal.isMaximal (A⧸P)).ne_top
       (by rw [← q32,h,Ideal.radical_top])
      have q41:ringKrullDim ((A⧸P)⧸J)=0:=by
       have : Nontrivial ((A⧸P)⧸J):=Ideal.Quotient.nontrivial_iff.mpr q9;let : IsLocalRing ((A⧸P)⧸J):=z36 J
       refine le_antisymm ?_ (ringKrullDim_nonneg_of_nontrivial)
       have q33:∀ (q:Ideal ((A⧸P)⧸J)),q.IsPrime→q=maximalIdeal ((A⧸P)⧸J):=fun q hq=>by
        have hle:J ≤ q.comap (Ideal.Quotient.mk J):=by
         intro x hx;rw [mem_comap,Ideal.Quotient.eq_zero_iff_mem.mpr hx];exact q.zero_mem
        have q21:maximalIdeal (A⧸P) ≤ q.comap (Ideal.Quotient.mk J):=by
         rw [← q32];exact (Ideal.IsPrime.radical_le_iff (Ideal.comap_isPrime _ q)).mpr hle
        have q4:q.comap (Ideal.Quotient.mk J)=maximalIdeal (A⧸P):=le_antisymm (le_maximalIdeal (Ideal.comap_isPrime _ q).ne_top) q21;have q44:=Ideal.Quotient.mk_surjective (I:=J)
        have q3:(maximalIdeal ((A⧸P)⧸J)).comap (Ideal.Quotient.mk J)=maximalIdeal (A⧸P):=by
         have : (maximalIdeal ((A⧸P)⧸J)).IsMaximal:=maximalIdeal.isMaximal _;have : ((maximalIdeal ((A⧸P)⧸J)).comap (Ideal.Quotient.mk J)).IsMaximal:=comap_isMaximal_of_surjective _ q44;exact eq_maximalIdeal ‹_›
        exact Ideal.comap_injective_of_surjective _ q44 (q4.trans q3.symm)
       rw [ringKrullDim,Order.krullDim_eq_iSup_length];simp only [WithBot.coe_iSup (OrderTop.bddAbove _),iSup_le_iff];intro c
       have q53:c.length=0:=by
        by_contra hne
        have hlt:c ⟨0,by omega⟩ < c ⟨1,by omega⟩:=c.strictMono (Fin.mk_lt_mk.mpr (by omega));have h0:=q33 (c ⟨0,by omega⟩).asIdeal (c ⟨0,by omega⟩).isPrime;have h1:=q33 (c ⟨1,by omega⟩).asIdeal (c ⟨1,by omega⟩).isPrime;exact hlt.ne (PrimeSpectrum.ext (h0.trans h1.symm))
       simp [q53]
      have hkr:=ringKrullDim_le_ringKrullDim_quotient_add_card (R:=A⧸P) s
       (fun y hy=>by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal];simp only [s,Finset.mem_coe,List.mem_toFinset,List.mem_map] at hy;obtain ⟨w,hw,rfl⟩:=hy;change w∈(maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P);rw [q35]
        exact hzs' w hw)
      rw [q41,zero_add] at hkr;exact hkr.trans (WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr q22))
     refine ⟨fun _=>q43,fun heq => ?_⟩
     exfalso;rw [q16] at heq
     have hlt:ringKrullDim (A⧸P) < ((z :: zs).length:WithBot ℕ∞):=by
      refine lt_of_le_of_lt q20 ?_
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one];exact WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self _))
     exact hlt.ne heq
    ·
     have q28:IsSMulRegular (A⧸P) z:=fun a b hab=>by
      obtain ⟨x,rfl⟩:=Ideal.Quotient.mk_surjective a;obtain ⟨y,rfl⟩:=Ideal.Quotient.mk_surjective b;change Ideal.Quotient.mk P (z*x)=Ideal.Quotient.mk P (z*y) at hab;rw [Ideal.Quotient.eq] at hab ⊢
      have q61:z*(x - y)∈P:=by simpa [mul_sub] using hab
      exact (hP.mem_or_mem q61).resolve_left hzP
     let zAP:Submodule A (A⧸P):=LinearMap.range (z•LinearMap.id (R:=A) (M:=A⧸P));let Qz:=(A⧸P)⧸zAP;let q56:A →ₗ[A] Qz:=zAP.mkQ.comp P.mkQ;have q1:Surjective q56:=(Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
     have q7:LinearMap.ker q56=P⊔span {z}:=by
      ext a;rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (p:=zAP) (Ideal.Quotient.mk P a)=0↔a∈P⊔span {z}
      rw [Submodule.Quotient.mk_eq_zero];constructor
      ·
       rintro ⟨q,hq⟩;obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective q;have hq':Ideal.Quotient.mk P (z*b)=Ideal.Quotient.mk P a:=hq;have q48:a - z*b∈P:=Ideal.Quotient.eq.mp hq'.symm
       have : a=(a - z*b)+z*b:=by ring
       rw [this]
       exact Ideal.add_mem _ (mem_sup_left q48)
        (mem_sup_right (Ideal.mul_mem_right b _ (subset_span rfl)))
      ·
       intro ha;rw [Submodule.mem_sup] at ha;obtain ⟨p,hp,r,hr,rfl⟩:=ha;obtain ⟨b,rfl⟩:=mem_span_singleton.mp hr
       refine ⟨Ideal.Quotient.mk P b,?_⟩
       change Ideal.Quotient.mk P (z*b)=Ideal.Quotient.mk P (p+z*b);rw [Ideal.Quotient.eq]
       have : z*b - (p+z*b) = -p:=by ring
       rw [this];exact P.neg_mem hp
     let eQz:(A⧸(P⊔span {z})) ≃ₗ[A] Qz:=(Submodule.quotEquivOfEq _ _ q7.symm).trans (q56.quotKerEquivOfSurjective q1)
     have q36:(annihilator A Qz⊔ofList zs).radical=maximalIdeal A:=by
      have q27:annihilator A Qz=P⊔span {z}:=by
       rw [← Ideal.annihilator_quotient (I:=P⊔span {z})]
       ext a;simp only [Module.mem_annihilator]
       exact ⟨fun h x=>eQz.injective (by rw [map_smul,map_zero];exact h (eQz x)),
        fun h y=>by
         have:=h (eQz.symm y);rw [← map_smul,map_eq_zero_iff eQz.symm eQz.symm.injective] at this
         exact this⟩
      rw [q27,sup_assoc,← Ideal.ofList_cons];exact q38
     have q18:z115 A (A⧸P) (z :: zs)=z115 A Qz zs:=by
      unfold z115;simp only [List.length_cons];rw [Finset.sum_range_succ]
      have q55:(Module.length A (z94 A (A⧸P) (z :: zs) (zs.length+1))).toNat=0:=by
       obtain ⟨e⟩:=z109 z zs q28 (zs.length+1);have : Subsingleton (z94 A Qz zs (zs.length+1)):=z95 zs (zs.length+1) (Nat.lt_succ_self _);rw [e.length_eq,Module.length_eq_zero];rfl
      rw [q55,Nat.cast_zero,mul_zero,add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      obtain ⟨ek⟩:=z109 z zs q28 k;rw [ek.length_eq]
     have q25:supportDim A Qz+1=supportDim A (A⧸P):=by
      rw [← Module.supportDim_eq_of_equiv eQz,Module.supportDim_quotient_eq_ringKrullDim,q16];let : IsLocalRing (A⧸P):=z36 P;have q10:IsSMulRegular (A⧸P) (Ideal.Quotient.mk P z):=q28
      have q11:Ideal.Quotient.mk P z∈maximalIdeal (A⧸P):=by
       have q35:(maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P)=maximalIdeal A:=by
        have : (maximalIdeal (A⧸P)).IsMaximal:=maximalIdeal.isMaximal _;have : ((maximalIdeal (A⧸P)).comap (Ideal.Quotient.mk P)).IsMaximal:=comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective;exact eq_maximalIdeal ‹_›
       rw [← mem_comap,q35];exact q34
      have q14:ringKrullDim ((A⧸P)⧸span {Ideal.Quotient.mk P z})+1 =
        ringKrullDim (A⧸P) :=
       ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim q10 q11
      let mkD:A →+* ((A⧸P)⧸span {Ideal.Quotient.mk P z}):=(Ideal.Quotient.mk _).comp (Ideal.Quotient.mk P);have q8:Surjective mkD:=Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
      have q12:RingHom.ker mkD=P⊔span {z}:=by
       ext a;simp only [mkD,RingHom.mem_ker,RingHom.comp_apply,Ideal.Quotient.eq_zero_iff_mem,mem_span_singleton];constructor
       ·
        rintro ⟨q,hq⟩;obtain ⟨b,rfl⟩:=Ideal.Quotient.mk_surjective q;have q48:a - z*b∈P:=Ideal.Quotient.eq.mp hq
        have : a=(a - z*b)+z*b:=by ring
        rw [this]
        exact Ideal.add_mem _ (mem_sup_left q48)
         (mem_sup_right (Ideal.mul_mem_right b _ (subset_span rfl)))
       ·
        intro ha;rw [Submodule.mem_sup] at ha;obtain ⟨p,hp,r,hr,rfl⟩:=ha;obtain ⟨b,rfl⟩:=mem_span_singleton.mp hr
        refine ⟨Ideal.Quotient.mk P b,?_⟩
        change Ideal.Quotient.mk P (p+z*b)=Ideal.Quotient.mk P (z*b);rw [Ideal.Quotient.eq]
        have : p+z*b - z*b=p:=by ring
        rw [this];exact hp
      let q37:(A⧸(P⊔span {z})) ≃+* ((A⧸P)⧸span {Ideal.Quotient.mk P z}):=(Ideal.quotEquivOfEq q12.symm).trans (RingHom.quotientKerEquivOfSurjective q8);rw [RingEquiv.ringKrullDim q37,q14]
     obtain ⟨_,ih_lt,ih_eq⟩:=ih hzs' Qz (Or.inl q36);dsimp only [Pred];rw [q18]
     refine ⟨fun hlt=>ih_lt ?_,fun heq=>ih_eq ?_⟩
     ·
      rw [← q25,List.length_cons,Nat.cast_add,Nat.cast_one] at hlt
      cases hd:supportDim A Qz with
      | bot=>simp
      | coe d =>
       rw [hd] at hlt
       cases d with
       | top =>
        exfalso
        have q55:(↑(⊤ : ℕ∞) : WithBot ℕ∞)+1=(⊤ : WithBot ℕ∞):=by
         change (↑((⊤ : ℕ∞)+1) : WithBot ℕ∞)=↑(⊤ : ℕ∞);simp
        rw [q55] at hlt;exact not_lt.mpr le_top hlt
       | coe m =>
        have hm:(↑(m : ℕ∞) : WithBot ℕ∞)+1=((m+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        have hz:((zs.length : ℕ) : WithBot ℕ∞)+1=((zs.length+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        rw [hm,hz] at hlt
        have hlt':m+1 < zs.length+1:=by exact_mod_cast hlt
        have hlt'':m < zs.length:=by omega
        exact_mod_cast hlt''
     ·
      rw [← q25,List.length_cons,Nat.cast_add,Nat.cast_one] at heq
      cases hd:supportDim A Qz with
      | bot =>
       exfalso
       have hz:((zs.length : ℕ) : WithBot ℕ∞)+1=((zs.length+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
       rw [hd,WithBot.bot_add,hz] at heq;exact WithBot.bot_ne_coe heq
      | coe d =>
       rw [hd] at heq
       cases d with
       | top =>
        exfalso
        have hz:((zs.length : ℕ) : WithBot ℕ∞)+1=((zs.length+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        have q55:(↑(⊤ : ℕ∞) : WithBot ℕ∞)+1=(↑(⊤ : ℕ∞) : WithBot ℕ∞):=by
         change (↑((⊤ : ℕ∞)+1) : WithBot ℕ∞)=↑(⊤ : ℕ∞);simp
        rw [q55,hz] at heq;exact ENat.natCast_ne_top _ (WithBot.coe_inj.mp heq).symm
       | coe m =>
        have hm:(↑(m : ℕ∞) : WithBot ℕ∞)+1=((m+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        have hz:((zs.length : ℕ) : WithBot ℕ∞)+1=((zs.length+1 : ℕ) : WithBot ℕ∞):=by push_cast;rfl
        rw [hm,hz] at heq
        have heq':m+1=zs.length+1:=by exact_mod_cast heq
        have heq'':m=zs.length:=by omega
        exact_mod_cast heq''
   ·
    intro N₁ N₂ N₃ _ _ _ _ _ _ fi fp hfi hfp hker _ _ _ hAnn1 hAnn2 hAnn3 ⟨h1_lt,h1_eq⟩ ⟨h3_lt,h3_eq⟩;have q54:z115 A N₂ (z :: zs)=z115 A N₁ (z :: zs)+z115 A N₃ (z :: zs):=z118 fi fp hfi hfp hker (z :: zs) (q24 N₁ hAnn1) (q24 N₂ hAnn2) (q24 N₃ hAnn3);have q40:supportDim A N₁ ≤ supportDim A N₂ := Module.supportDim_le_of_injective fi hfi
    have q49:supportDim A N₃ ≤ supportDim A N₂ := Module.supportDim_le_of_surjective fp hfp
    have q13:supportDim A N₂ ≤ max (supportDim A N₁) (supportDim A N₃):=by
     by_cases hsub2:Subsingleton N₂
     · rw [Module.supportDim_eq_bot_of_subsingleton];exact bot_le
     ·
      have hnt2:Nontrivial N₂ := not_subsingleton_iff_nontrivial.mp hsub2
      have q15:annihilator A N₂ ≠ ⊤ := fun h1=>hsub2 <|
       subsingleton_iff_forall_eq 0 |>.mpr fun y=>by
        simpa using Module.mem_annihilator.mp (h1▸Submodule.mem_top:(1:A)∈_) y
      haveI : Nonempty (PrimeSpectrum.zeroLocus (annihilator A N₂ : Set A)) :=
       ⟨⟨⟨maximalIdeal A,(maximalIdeal.isMaximal A).isPrime⟩,by
        rw [PrimeSpectrum.mem_zeroLocus]
        exact le_maximalIdeal q15⟩⟩
      have q26:annihilator A N₁ * annihilator A N₃ ≤ annihilator A N₂ := by
       rw [Ideal.mul_le];intro a ha b hb;rw [Module.mem_annihilator];intro y
       have hpy:fp (b•y)=0:=by
        rw [map_smul];exact Module.mem_annihilator.mp hb (fp y)
       obtain ⟨x,hx⟩:=LinearMap.mem_range.mp (hker.symm▸LinearMap.mem_ker.mpr hpy);rw [mul_smul,← hx,← map_smul,Module.mem_annihilator.mp ha x,map_zero]
      rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,Module.supportDim_eq_ringKrullDim_quotient_annihilator,Module.supportDim_eq_ringKrullDim_quotient_annihilator,
       ringKrullDim_quotient,ringKrullDim_quotient,ringKrullDim_quotient]
      rw [Order.krullDim_eq_iSup_length];simp only [WithBot.coe_iSup (OrderTop.bddAbove _),iSup_le_iff];intro c
      have q29:annihilator A N₂ ≤ (c 0).1.asIdeal:=by
       have:=(c 0).2;rwa [PrimeSpectrum.mem_zeroLocus] at this
      have hor:annihilator A N₁ ≤ (c 0).1.asIdeal∨annihilator A N₃ ≤ (c 0).1.asIdeal:=(c 0).1.isPrime.mul_le.mp (q26.trans q29)
      rcases hor with h1 | h3
      ·
       refine le_trans ?_ (le_max_left _ _)
       let c1:LTSeries (PrimeSpectrum.zeroLocus (annihilator A N₁ : Set A)) :=
        {
         length:=c.length
         toFun:=fun j=>⟨(c j).1,by
          rw [PrimeSpectrum.mem_zeroLocus]
          exact h1.trans (c.monotone (Fin.zero_le j))⟩
         step:=fun j=>c.step j }
       haveI : Nonempty (PrimeSpectrum.zeroLocus (annihilator A N₁ : Set A)):=⟨c1 0⟩
       rw [Order.krullDim_eq_iSup_length]
       exact WithBot.coe_le_coe.mpr (le_iSup (fun s:LTSeries _=>(s.length : ℕ∞)) c1)
      ·
       refine le_trans ?_ (le_max_right _ _)
       let c3:LTSeries (PrimeSpectrum.zeroLocus (annihilator A N₃ : Set A)) :=
        {
         length:=c.length
         toFun:=fun j=>⟨(c j).1,by
          rw [PrimeSpectrum.mem_zeroLocus]
          exact h3.trans (c.monotone (Fin.zero_le j))⟩
         step:=fun j=>c.step j }
       haveI : Nonempty (PrimeSpectrum.zeroLocus (annihilator A N₃ : Set A)):=⟨c3 0⟩
       rw [Order.krullDim_eq_iSup_length]
       exact WithBot.coe_le_coe.mpr (le_iSup (fun s:LTSeries _=>(s.length : ℕ∞)) c3)
    refine ⟨fun hlt => ?_,fun heq => ?_⟩
    · rw [q54,h1_lt (lt_of_le_of_lt q40 hlt),h3_lt (lt_of_le_of_lt q49 hlt),add_zero]
    ·
     rw [q54];have q60:supportDim A N₁ ≤ ((z :: zs).length:WithBot ℕ∞):=heq▸q40;have q51:supportDim A N₃ ≤ ((z :: zs).length:WithBot ℕ∞):=heq▸q49
     rcases q60.eq_or_lt with h1e | h1l
     ·
      rcases q51.eq_or_lt with h3e | h3l
      · linarith [h1_eq h1e,h3_eq h3e]
      · rw [h3_lt h3l,add_zero];exact h1_eq h1e
     ·
      rcases q51.eq_or_lt with h3e | h3l
      · rw [h1_lt h1l,zero_add];exact h3_eq h3e
      ·
       exfalso;have q19:max (supportDim A N₁) (supportDim A N₃) < ((z :: zs).length:WithBot ℕ∞):=max_lt h1l h3l;exact (lt_of_le_of_lt q13 q19).ne heq
  exact ⟨q24 M le_rfl,q46.1,q46.2⟩
end KoszulPositivity
section DiagonalTorAndPositivity
noncomputable def z124 (D:Type) [CommRing D] : (n : ℕ)→List (z0 D n)
 | 0=>[]
 | n+1=>PowerSeries.X :: (z124 D n).map PowerSeries.C
lemma z125 (D:Type) [CommRing D] :
  ∀ n : ℕ,(z124 D n).length=n
 | 0=>rfl
 | n+1=>by simp [z124,z125 D n]
lemma z126 (D:Type) [CommRing D] :
  ∀ n : ℕ,ofList (z124 D n)=span (Set.range (z14 D (n:=n)))
 | 0=>by
  simp [z124,ofList,Set.range_eq_empty]
 | n+1=>by
  rw [z124,Ideal.ofList_cons]
  have q0:ofList ((z124 D n).map PowerSeries.C)=(ofList (z124 D n)).map PowerSeries.C:=by
   rw [ofList,ofList,map_span];congr 1;ext y;simp
  rw [q0,z126 D n,map_span]
  refine le_antisymm (sup_le ?_ ?_) ?_
  ·
   rw [span_singleton_le_iff_mem];exact subset_span ⟨Fin.last n,by simp [z14]⟩
  ·
   rw [span_le];rintro _ ⟨_,⟨j,rfl⟩,rfl⟩;exact subset_span ⟨j.castSucc,by simp [z14]⟩
  ·
   rw [span_le];rintro _ ⟨i,rfl⟩
   refine Fin.lastCases ?_ ?_ i
   · exact mem_sup_left (by simp [z14])
   ·
    intro j;exact mem_sup_right (subset_span ⟨z14 D j,⟨j,rfl⟩,by simp [z14]⟩)
lemma z127 (D:Type) [CommRing D] [IsLocalRing D] :
  ∀ (n : ℕ) (z:z0 D n),z∈z124 D n→z∈maximalIdeal (z0 D n)
 | 0,_,hz=>absurd hz List.not_mem_nil
 | n+1,z,hz=>by
  rw [z124,List.mem_cons] at hz
  rcases hz with rfl | hz'
  · exact z4
  ·
   rw [List.mem_map] at hz';obtain ⟨w,hw,rfl⟩:=hz';rw [z3,PowerSeries.constantCoeff_C];exact z127 D n w hw
lemma z128 {R S:Type} [CommRing R] [CommRing S] (eR:R ≃+* S) :
  ∀ (zs:List R) {M' N':Type} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module S N']
   (eM:M' ≃+ N'),(∀ (r:R) (x:M'),eM (r•x)=eR r•eM x) →
   z110 M' zs→z110 N' (zs.map eR)
 | [],_,_,_,_,_,_,_,_,_=>trivial
 | z :: zs,M',N',_,_,_,_,eM,hsmul,⟨hz,hrest⟩=>by
  have q0:∀ (s:S) (y:N'),eM.symm (s•y)=eR.symm s•eM.symm y:=fun s y=>by
   apply eM.injective;rw [eM.apply_symm_apply,hsmul,eR.apply_symm_apply,eM.apply_symm_apply]
  have hzN:IsSMulRegular N' (eR z):=fun y₁ y₂ hy=>by
   apply eM.symm.injective;apply hz;have h1:eM.symm (eR z•y₁)=eM.symm (eR z•y₂):=congrArg eM.symm hy;rw [q0,q0,eR.symm_apply_apply] at h1;exact h1
  refine ⟨hzN,?_⟩
  let zM:Submodule R M':=LinearMap.range (z•LinearMap.id (R:=R) (M:=M'));let zN:Submodule S N':=LinearMap.range (eR z•LinearMap.id (R:=S) (M:=N'))
  have q2:∀ x:M',x∈zM↔eM x∈zN:=fun x=>by
   simp only [zM,zN,LinearMap.mem_range,LinearMap.smul_apply,LinearMap.id_apply];constructor
   ·
    rintro ⟨a,rfl⟩;exact ⟨eM a,(hsmul z a).symm⟩
   ·
    rintro ⟨b,hb⟩
    refine ⟨eM.symm b,eM.injective ?_⟩
    rw [hsmul z (eM.symm b),eM.apply_symm_apply,hb]
  let eQ:(M'⧸zM) ≃+ (N'⧸zN) :=
   {
    toFun:=QuotientAddGroup.lift zM.toAddSubgroup
     ((QuotientAddGroup.mk' zN.toAddSubgroup).comp eM.toAddMonoidHom) (fun x hx=>by
      rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
      exact (q2 x).mp hx)
    invFun:=QuotientAddGroup.lift zN.toAddSubgroup
     ((QuotientAddGroup.mk' zM.toAddSubgroup).comp eM.symm.toAddMonoidHom) (fun y hy=>by
      rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff];change eM.symm y∈zM;rw [q2,eM.apply_symm_apply]
      exact hy)
    map_add':=fun a b=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zM a;obtain ⟨y,rfl⟩:=Submodule.Quotient.mk_surjective zM b;change Submodule.Quotient.mk (eM (x+y))=Submodule.Quotient.mk (eM x)+Submodule.Quotient.mk (eM y);rw [map_add,Submodule.Quotient.mk_add]
    left_inv:=fun a=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zM a;change Submodule.Quotient.mk (eM.symm (eM x))=Submodule.Quotient.mk x;rw [eM.symm_apply_apply]
    right_inv:=fun b=>by
     obtain ⟨y,rfl⟩:=Submodule.Quotient.mk_surjective zN b;change Submodule.Quotient.mk (eM (eM.symm y))=Submodule.Quotient.mk y
     rw [eM.apply_symm_apply] }
  have q1:∀ (r:R) (a:M'⧸zM),eQ (r•a)=eR r•eQ a:=fun r a=>by
   obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zM a;change Submodule.Quotient.mk (eM (r•x))=eR r•Submodule.Quotient.mk (eM x);rw [hsmul,Submodule.Quotient.mk_smul]
  exact z128 eR zs eQ q1 hrest
lemma z129 {A B:Type} [CommRing A] [CommRing B]
  (e:A ≃+* B) (zs:List A) (h:z110 A zs) :
  z110 B (zs.map e) :=
 z128 e zs e.toAddEquiv (fun r x=>e.map_mul r x) h
lemma z130 {T S:Type} [CommRing T] [CommRing S] [Algebra T S] :
  ∀ (zs:List T) (M:Type) [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M],z110 (R:=S) M (zs.map (algebraMap T S))→z110 (R:=T) M zs
 | [],_,_,_,_,_,_=>trivial
 | z :: zs,M,_,_,_,_,⟨hz,hrest⟩=>by
  have hzT:IsSMulRegular M z:=fun x y hxy =>
   hz (by simpa [algebraMap_smul] using hxy)
  refine ⟨hzT,?_⟩
  let zMT:Submodule T M:=LinearMap.range (z•LinearMap.id (R:=T) (M:=M));let zMS:Submodule S M:=LinearMap.range ((algebraMap T S z)•LinearMap.id (R:=S) (M:=M))
  have q0:(zMT:Set M)=(zMS:Set M):=by
   ext m;simp only [SetLike.mem_coe,zMT,zMS,LinearMap.mem_range,LinearMap.smul_apply,LinearMap.id_apply,algebraMap_smul]
  let eQ:(M⧸zMS) ≃+ (M⧸zMT) :=
   {
    toFun:=QuotientAddGroup.lift zMS.toAddSubgroup (QuotientAddGroup.mk' zMT.toAddSubgroup) (fun x hx=>by
     rw [AddMonoidHom.mem_ker,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
     change x∈(zMT:Set M);rw [q0];exact hx)
    invFun:=QuotientAddGroup.lift zMT.toAddSubgroup (QuotientAddGroup.mk' zMS.toAddSubgroup) (fun x hx=>by
     rw [AddMonoidHom.mem_ker,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
     change x∈(zMS:Set M);rw [← q0];exact hx)
    map_add':=fun a b=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zMS a;obtain ⟨y,rfl⟩:=Submodule.Quotient.mk_surjective zMS b;rfl
    left_inv:=fun a=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zMS a;rfl
    right_inv:=fun b=>by
     obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zMT b;rfl }
  have q1:∀ (t:T) (a:M⧸zMS),eQ (t•a)=t•eQ a:=fun t a=>by
   obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective zMS a
   change Submodule.Quotient.mk (p:=zMT) (t•x)=t•Submodule.Quotient.mk (p:=zMT) x
   rfl
  have q2:z110 (R:=T) (M⧸zMS) zs:=z130 zs (M⧸zMS) hrest;simpa [List.map_id] using z128 (RingEquiv.refl T) zs eQ q1 q2
lemma z131 (D:Type) [CommRing D] :
  ∀ n : ℕ,z110 (z0 D n) (z124 D n)
 | 0=>trivial
 | n+1=>by
  let S:=z0 D n;let PS:=PowerSeries S
  have q3:IsSMulRegular PS (PowerSeries.X:PS):=fun a b hab=>by
   ext k;have hk:=congrArg (PowerSeries.coeff (k+1)) hab;simpa [smul_eq_mul,PowerSeries.coeff_succ_X_mul] using hk
  refine ⟨q3,?_⟩
  let : Algebra PS S:=PowerSeries.constantCoeff.toAlgebra
  let cc:PS →ₗ[PS] S :=
   {
    toFun:=PowerSeries.constantCoeff
    map_add':=map_add _
    map_smul':=fun f g=>map_mul PowerSeries.constantCoeff f g }
  have q0:Surjective cc:=PowerSeries.constantCoeff_surj
  have q1:LinearMap.ker cc=LinearMap.range ((PowerSeries.X:PS)•LinearMap.id):=by
   ext f;simp only [LinearMap.mem_ker,cc,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.mem_range,LinearMap.smul_apply,LinearMap.id_apply,smul_eq_mul];constructor
   ·
    intro hf
    have h1:=z6 1 f fun i hi=>by
     have hi0:i=0:=by omega
     subst hi0;simpa using hf
    obtain ⟨q,hq⟩:=mem_span_singleton.mp (by simpa using h1);exact ⟨q,hq.symm⟩
   ·
    rintro ⟨q,rfl⟩;rw [map_mul,PowerSeries.constantCoeff_X,zero_mul]
  let eQ:(PS⧸LinearMap.range ((PowerSeries.X:PS)•LinearMap.id)) ≃ₗ[PS] S:=(Submodule.quotEquivOfEq _ _ q1.symm).trans (cc.quotKerEquivOfSurjective q0)
  have q2:((z124 D n).map PowerSeries.C).map (algebraMap PS S)=z124 D n:=by
   rw [List.map_map]
   have q5:(algebraMap PS S)∘PowerSeries.C=id:=by
    ext a;exact PowerSeries.constantCoeff_C a
   rw [q5,List.map_id]
  have : IsScalarTower PS S S:=IsScalarTower.right
  have q4:z110 (R:=PS) S ((z124 D n).map PowerSeries.C) :=
   z130 ((z124 D n).map PowerSeries.C) S
    (q2.symm▸z131 D n)
  simpa [List.map_id] using z128 (RingEquiv.refl PS)
   ((z124 D n).map PowerSeries.C) eQ.symm.toAddEquiv (fun r x=>eQ.symm.map_smul r x) q4
private def z132 {T S M:Type} [CommRing T] [CommRing S] [Algebra T S]
  [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M] :
  ∀ (zs:List T) (k : ℕ),z80 T M zs k ≃+ z80 S M (zs.map (algebraMap T S)) k
 | [],0=>AddEquiv.refl M
 | [],_+1=>AddEquiv.refl PUnit
 | _ :: zs,0=>z132 (T:=T) (S:=S) (M:=M) zs 0
 | _ :: zs,i+1 =>
  AddEquiv.prodCongr
   (z132 (T:=T) (S:=S) (M:=M) zs (i+1))
   (z132 (T:=T) (S:=S) (M:=M) zs i)
private lemma z133 {T S M:Type} [CommRing T] [CommRing S] [Algebra T S]
  [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M] :
  ∀ (zs:List T) (k : ℕ) (t:T) (x:z80 T M zs k),
   z132 (T:=T) (S:=S) (M:=M) zs k (t•x)=algebraMap T S t•z132 (T:=T) (S:=S) (M:=M) zs k x
 | [],0,t,m=>(algebraMap_smul S t m).symm
 | [],_+1,_,_=>rfl
 | _ :: zs,0,t,x=>z133 (T:=T) (S:=S) (M:=M) zs 0 t x
 | _ :: zs,i+1,t,(a,b) =>
  Prod.ext (z133 (T:=T) (S:=S) (M:=M) zs (i+1) t a)
   (z133 (T:=T) (S:=S) (M:=M) zs i t b)
private lemma z134 {T S M:Type} [CommRing T] [CommRing S] [Algebra T S]
  [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M] :
  ∀ (zs:List T) (k : ℕ) (x:z80 T M zs (k+1)),
   z132 (T:=T) (S:=S) (M:=M) zs k (z82 T M zs k x) =
    z82 S M (zs.map (algebraMap T S)) k
     (z132 (T:=T) (S:=S) (M:=M) zs (k+1) x)
 | [],0,_=>rfl
 | [],_+1,_=>rfl
 | z :: zs,0,(a,b)=>by
  change z132 (T:=T) (S:=S) (M:=M) zs 0 (z82 T M zs 0 a+z•b) =
   z82 S M (zs.map (algebraMap T S)) 0 (z132 (T:=T) (S:=S) (M:=M) zs 1 a)+algebraMap T S z•z132 (T:=T) (S:=S) (M:=M) zs 0 b
  rw [map_add,z133,z134 (T:=T) (S:=S) (M:=M) zs 0 a]
 | z :: zs,i+1,(a,b)=>by
  apply Prod.ext
  ·
   change z132 (T:=T) (S:=S) (M:=M) zs (i+1) (z82 T M zs (i+1) a+z•b) =
    z82 S M (zs.map (algebraMap T S)) (i+1)
     (z132 (T:=T) (S:=S) (M:=M) zs (i+2) a) +
     algebraMap T S z•z132 (T:=T) (S:=S) (M:=M) zs (i+1) b
   rw [map_add,z133,z134 (T:=T) (S:=S) (M:=M) zs (i+1) a]
  ·
   change z132 (T:=T) (S:=S) (M:=M) zs i (-(z82 T M zs i b)) =
    -(z82 S M (zs.map (algebraMap T S)) i
     (z132 (T:=T) (S:=S) (M:=M) zs (i+1) b))
   rw [map_neg,z134 (T:=T) (S:=S) (M:=M) zs i b]
lemma z135 {T S M:Type} [CommRing T] [CommRing S] [Algebra T S]
    [AddCommGroup M] [Module T M] [Module S M] [IsScalarTower T S M]
    (zs:List T) (k : ℕ) :
    Nonempty (z94 T M zs k ≃ₗ[T] RestrictScalars T S (z94 S M (zs.map (algebraMap T S)) k)):=by
  let zS:=zs.map (algebraMap T S)
  cases k with
  | zero =>
    let e0:=z132 (T:=T) (S:=S) (M:=M) zs 0;let e1:=z132 (T:=T) (S:=S) (M:=M) zs 1
    have q0:∀ x:z80 T M zs 0,x∈LinearMap.range (z82 T M zs 0)↔e0 x∈LinearMap.range (z82 S M zS 0):=fun x=>by
      constructor
      · rintro ⟨a,rfl⟩
        exact ⟨e1 a,(z134 (T:=T) (S:=S) (M:=M) zs 0 a).symm⟩
      · rintro ⟨b,hb⟩
        refine ⟨e1.symm b,e0.injective ?_⟩
        rw [z134 (T:=T) (S:=S) (M:=M) zs 0 (e1.symm b)]
        change z82 S M zS 0 (e1 (e1.symm b))=e0 x;rw [e1.apply_symm_apply,hb]
    let dT:=LinearMap.range (z82 T M zs 0);let dS:=LinearMap.range (z82 S M zS 0)
    let f0 :=
      QuotientAddGroup.lift dT.toAddSubgroup
        ((QuotientAddGroup.mk' dS.toAddSubgroup).comp e0.toAddMonoidHom)
        (fun x hx=>by
          rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
          exact (q0 x).mp hx)
    let g0 :=
      QuotientAddGroup.lift dS.toAddSubgroup
        ((QuotientAddGroup.mk' dT.toAddSubgroup).comp e0.symm.toAddMonoidHom)
        (fun y hy=>by
          rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff];change e0.symm y∈LinearMap.range (z82 T M zs 0);rw [q0,e0.apply_symm_apply]
          exact hy)
    exact ⟨{
      toFun:=fun a=>(RestrictScalars.addEquiv T S _).symm (f0 a)
      invFun:=fun b=>g0 (RestrictScalars.addEquiv T S _ b)
      map_add':=fun a b=>f0.map_add a b
      map_smul':=fun t a=>by
        obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective dT a;apply (RestrictScalars.addEquiv T S _).injective
        change Submodule.Quotient.mk (p:=dS) (e0 (t•x))=Submodule.Quotient.mk (p:=dS) (algebraMap T S t•e0 x)
        rw [z133]
      left_inv:=fun a=>by
        obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective dT a
        change Submodule.Quotient.mk (p:=dT) (e0.symm (e0 x))=Submodule.Quotient.mk (p:=dT) x
        rw [e0.symm_apply_apply]
      right_inv:=fun b=>by
        apply (RestrictScalars.addEquiv T S _).injective;let b':z94 S M zS 0:=RestrictScalars.addEquiv T S _ b;obtain ⟨y,hy⟩:=Submodule.Quotient.mk_surjective dS b';change f0 (g0 b')=b';rw [← hy]
        change Submodule.Quotient.mk (p:=dS) (e0 (e0.symm y))=Submodule.Quotient.mk (p:=dS) y
        rw [e0.apply_symm_apply] }⟩
  | succ i =>
    let e0:=z132 (T:=T) (S:=S) (M:=M) zs i;let e1:=z132 (T:=T) (S:=S) (M:=M) zs (i+1);let e2:=z132 (T:=T) (S:=S) (M:=M) zs (i+2)
    have q4:∀ x:z80 T M zs (i+1),x∈LinearMap.ker (z82 T M zs i)↔e1 x∈LinearMap.ker (z82 S M zS i):=fun x=>by
      simp only [LinearMap.mem_ker];have hc:=z134 (T:=T) (S:=S) (M:=M) zs i x;change e0 (z82 T M zs i x)=z82 S M zS i (e1 x) at hc;rw [← hc];exact (e0.map_eq_zero_iff).symm
    have q0:∀ x:z80 T M zs (i+1),
        x∈LinearMap.range (z82 T M zs (i+1))↔e1 x∈LinearMap.range (z82 S M zS (i+1)):=fun x=>by
      constructor
      · rintro ⟨a,rfl⟩
        exact ⟨e2 a,(z134 (T:=T) (S:=S) (M:=M) zs (i+1) a).symm⟩
      · rintro ⟨b,hb⟩
        refine ⟨e2.symm b,e1.injective ?_⟩
        rw [z134 (T:=T) (S:=S) (M:=M) zs (i+1) (e2.symm b)]
        change z82 S M zS (i+1) (e2 (e2.symm b))=e1 x;rw [e2.apply_symm_apply,hb]
    let q3:LinearMap.ker (z82 T M zs i) ≃+ LinearMap.ker (z82 S M zS i) :=
      { toFun:=fun p=>⟨e1 p.1,(q4 p.1).mp p.2⟩
        invFun:=fun q=>⟨e1.symm q.1,(q4 (e1.symm q.1)).mpr (by rw [e1.apply_symm_apply];exact q.2)⟩
        map_add':=fun p₁ p₂=>Subtype.ext (e1.map_add p₁.1 p₂.1)
        left_inv:=fun p=>Subtype.ext (e1.symm_apply_apply p.1)
        right_inv:=fun q=>Subtype.ext (e1.apply_symm_apply q.1) }
    let q2:=(LinearMap.range (z82 T M zs (i+1))).comap (LinearMap.ker (z82 T M zs i)).subtype;let q1:=(LinearMap.range (z82 S M zS (i+1))).comap (LinearMap.ker (z82 S M zS i)).subtype
    let fS0 :=
      QuotientAddGroup.lift q2.toAddSubgroup
        ((QuotientAddGroup.mk' q1.toAddSubgroup).comp q3.toAddMonoidHom)
        (fun p hp=>by
          rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff]
          exact (q0 p.1).mp hp)
    let gS0 :=
      QuotientAddGroup.lift q1.toAddSubgroup
        ((QuotientAddGroup.mk' q2.toAddSubgroup).comp q3.symm.toAddMonoidHom)
        (fun q hq=>by
          rw [AddMonoidHom.mem_ker,AddMonoidHom.comp_apply,QuotientAddGroup.mk'_apply,QuotientAddGroup.eq_zero_iff];change e1.symm q.1∈LinearMap.range (z82 T M zs (i+1))
          rw [q0,e1.apply_symm_apply];exact hq)
    let fS:z94 T M zs (i+1)→z94 S M zS (i+1):=fun a=>fS0 a
    let gS:z94 S M zS (i+1)→z94 T M zs (i+1):=fun b=>gS0 b
    exact ⟨{
      toFun:=fun a=>(RestrictScalars.addEquiv T S _).symm (fS a)
      invFun:=fun b=>gS (RestrictScalars.addEquiv T S _ b)
      map_add':=fun a b=>fS0.map_add a b
      map_smul':=fun t a=>by
        obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective q2 a;apply (RestrictScalars.addEquiv T S _).injective
        change Submodule.Quotient.mk (p:=q1) (q3 (t•x))=Submodule.Quotient.mk (p:=q1) (algebraMap T S t•q3 x)
        have hsm:q3 (t•x)=algebraMap T S t•q3 x:=Subtype.ext (z133 (T:=T) (S:=S) (M:=M) zs (i+1) t x.1);rw [hsm]
      left_inv:=fun a=>by
        obtain ⟨x,rfl⟩:=Submodule.Quotient.mk_surjective q2 a
        change Submodule.Quotient.mk (p:=q2) (q3.symm (q3 x))=Submodule.Quotient.mk (p:=q2) x
        rw [q3.symm_apply_apply]
      right_inv:=fun b=>by
        apply (RestrictScalars.addEquiv T S _).injective;let b':z94 S M zS (i+1):=RestrictScalars.addEquiv T S _ b;obtain ⟨y,hy⟩:=Submodule.Quotient.mk_surjective q1 b';change fS (gS b')=b';rw [← hy]
        change Submodule.Quotient.mk (p:=q1) (q3 (q3.symm y))=Submodule.Quotient.mk (p:=q1) y
        rw [q3.apply_symm_apply] }⟩
private def z136 (R T:Type) [CommRing R] [CommRing T] [Algebra R T]
  {X Y:Type} [AddCommMonoid X] [Module T X] [AddCommMonoid Y] [Module T Y]
  (e:X ≃ₗ[T] Y) : RestrictScalars R T X ≃ₗ[R] RestrictScalars R T Y :=
 { e.toAddEquiv with map_smul':=fun r x=>e.map_smul (algebraMap R T r) x }
private lemma z137 {T S N:Type} [CommRing T] [AddCommGroup S] [Module T S]
  [AddCommGroup N] [Module T N]
  (hS:∀ q : ℕ,Subsingleton (z56 T S N (q+1))) :
  ∀ (r q : ℕ),Subsingleton (z56 T (Fin r→S) N (q+1))
 | 0,q=>by
  have : Module.Projective T (Fin 0→S) :=
   Module.Projective.of_split (0:(Fin 0→S) →ₗ[T] (Fin 0→T)) 0
    (LinearMap.ext fun _=>funext fun i=>Fin.elim0 i)
  exact z67 (Fin 0→S) N q
 | r+1,q=>by
  let i0:S →ₗ[T] (Fin (r+1)→S) :=
   {
    toFun:=fun a=>Fin.cons a 0
    map_add':=fun a b=>by ext i;refine Fin.cases rfl (fun _=>by simp) i
    map_smul':=fun t a=>by ext i;refine Fin.cases rfl (fun _=>by simp) i }
  let p0:(Fin (r+1)→S) →ₗ[T] (Fin r→S) :=
   {
    toFun:=fun f j=>f j.succ
    map_add':=fun _ _=>rfl
    map_smul':=fun _ _=>rfl }
  have hi0:Injective i0:=fun a b h=>congrFun h 0
  have hp0:Surjective p0:=fun f=>⟨Fin.cons 0 f,by ext j;rfl⟩
  have q0:LinearMap.range i0=LinearMap.ker p0:=by
   ext f;simp only [LinearMap.mem_range,LinearMap.mem_ker,i0,p0,LinearMap.coe_mk,AddHom.coe_mk];constructor
   · rintro ⟨a,rfl⟩;ext j;rfl
   ·
    intro hf;refine ⟨f 0,?_⟩;ext i
    refine Fin.cases rfl (fun j=>(congrFun hf j).symm) i
  obtain ⟨_,_,h2,_⟩:=z65 i0 p0 hi0 hp0 q0 N;have : Subsingleton (z56 T S N (q+1)):=hS q;have : Subsingleton (z56 T (Fin r→S) N (q+1)):=z137 hS r q
  refine subsingleton_iff_forall_eq 0 |>.mpr fun z => ?_
  have hpz:z58 p0 N (q+1) z=0:=Subsingleton.elim _ 0;obtain ⟨w,rfl⟩:=(h2 (q+1) z).mp hpz;rw [Subsingleton.elim w 0,map_zero]
private noncomputable def z138 {R T S M₁ M₂ : Type} [CommRing R] [CommRing T] [CommRing S]
  [Algebra R S] [Algebra T S] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  (f:M₁ →ₗ[R] M₂) : (S ⊗[R] M₁) →ₗ[T] (S ⊗[R] M₂) :=
 {
  toFun:=LinearMap.lTensor S f
  map_add':=map_add _
  map_smul':=fun t x=>by
   induction x using TensorProduct.induction_on with
   | zero=>simp
   | tmul s m =>
    change LinearMap.lTensor S f ((t•s) ⊗ₜ[R] m)=t•(LinearMap.lTensor S f (s ⊗ₜ[R] m));simp [LinearMap.lTensor_tmul,smul_tmul']
   | add x₁ x₂ ih₁ ih₂=>simp [map_add,smul_add,ih₁,ih₂] }
private noncomputable def z139 {R T S N B:Type}
  [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  (e₀ : RestrictScalars R T (S ⊗[T] N) ≃ₗ[R] B)
  (M:Type) [AddCommGroup M] [Module R M] :
  (M ⊗[R] B) ≃ₗ[R] RestrictScalars R T ((S ⊗[R] M) ⊗[T] N):=by
 let toF0 (m:M) : (S ⊗[T] N) →ₗ[T] ((S ⊗[R] M) ⊗[T] N) :=
  TensorProduct.lift
   {
    toFun:=fun s =>
     {
      toFun:=fun n=>(s ⊗ₜ[R] m) ⊗ₜ[T] n
      map_add':=fun n₁ n₂=>tmul_add _ _ _
      map_smul':=fun t n=>by
       change (s ⊗ₜ[R] m) ⊗ₜ[T] (t•n)=t•((s ⊗ₜ[R] m) ⊗ₜ[T] n)
       rw [TensorProduct.tmul_smul] }
    map_add':=fun s₁ s₂=>by
     apply LinearMap.ext;intro n;simp [add_tmul]
    map_smul':=fun t s=>by
     apply LinearMap.ext;intro n;change ((t•s) ⊗ₜ[R] m) ⊗ₜ[T] n=t•((s ⊗ₜ[R] m) ⊗ₜ[T] n)
     rw [smul_tmul',smul_tmul'] }
 let q3:M →ₗ[R] (RestrictScalars R T (S ⊗[T] N)) →ₗ[R] RestrictScalars R T ((S ⊗[R] M) ⊗[T] N) :=
  {
   toFun:=fun m =>
    {
     toFun:=fun u=>toF0 m u
     map_add':=fun u₁ u₂=>(toF0 m).map_add u₁ u₂
     map_smul':=fun r u=>(toF0 m).map_smul (algebraMap R T r) u }
   map_add':=fun m₁ m₂=>by
    apply LinearMap.ext;intro u;change toF0 (m₁ + m₂) u=toF0 m₁ u+toF0 m₂ u
    induction u using TensorProduct.induction_on with
    | zero=>simp
    | tmul s n =>
     change (s ⊗ₜ[R] (m₁ + m₂)) ⊗ₜ[T] n=(s ⊗ₜ[R] m₁) ⊗ₜ[T] n+(s ⊗ₜ[R] m₂) ⊗ₜ[T] n;rw [tmul_add,add_tmul]
    | add u₁ u₂ ih₁ ih₂=>simp only [map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂];abel
   map_smul':=fun r m=>by
    apply LinearMap.ext;intro u;change toF0 (r•m) u=algebraMap R T r•toF0 m u
    induction u using TensorProduct.induction_on with
    | zero=>simp
    | tmul s n =>
     change (s ⊗ₜ[R] (r•m)) ⊗ₜ[T] n=algebraMap R T r•((s ⊗ₜ[R] m) ⊗ₜ[T] n)
     have q1:r•s=algebraMap R T r•s:=by
      rw [Algebra.smul_def,Algebra.smul_def,IsScalarTower.algebraMap_apply R T S]
     have h1:s ⊗ₜ[R] (r•m)=algebraMap R T r•(s ⊗ₜ[R] m):=by
      rw [← smul_tmul,q1];rfl
     rw [h1];exact smul_tmul' (algebraMap R T r) (s ⊗ₜ[R] m) n
    | add u₁ u₂ ih₁ ih₂ =>
     simp only [map_add,smul_add] at ih₁ ih₂ ⊢
     rw [ih₁,ih₂] }
 let fwd:(M ⊗[R] B) →ₗ[R] RestrictScalars R T ((S ⊗[R] M) ⊗[T] N) :=
  TensorProduct.lift
   {
    toFun:=fun m=>(q3 m).comp e₀.symm.toLinearMap
    map_add':=fun m₁ m₂=>by
     apply LinearMap.ext;intro b;change q3 (m₁ + m₂) (e₀.symm b)=q3 m₁ (e₀.symm b)+q3 m₂ (e₀.symm b);rw [map_add];rfl
    map_smul':=fun r m=>by
     apply LinearMap.ext;intro b;change q3 (r•m) (e₀.symm b)=r•q3 m (e₀.symm b)
     rw [map_smul];rfl }
 letI : SMulCommClass R T (S ⊗[T] N) :=
  ⟨fun r t u=>by
   induction u using TensorProduct.induction_on with
   | zero=>simp
   | tmul s n =>
    change (r•(t•s)) ⊗ₜ[T] n=(t•(r•s)) ⊗ₜ[T] n;rw [smul_comm]
   | add u₁ u₂ ih₁ ih₂=>simp [smul_add,ih₁,ih₂]⟩
 let bwd_atom (n:N) : (S ⊗[R] M) →ₗ[R] ((S ⊗[T] N) ⊗[R] M) :=
  TensorProduct.lift
   {
    toFun:=fun s =>
     {
      toFun:=fun m=>(s ⊗ₜ[T] n) ⊗ₜ[R] m
      map_add':=fun m₁ m₂=>tmul_add _ _ _
      map_smul':=fun r m=>by
       change (s ⊗ₜ[T] n) ⊗ₜ[R] (r•m)=r•((s ⊗ₜ[T] n) ⊗ₜ[R] m)
       rw [TensorProduct.tmul_smul] }
    map_add':=fun s₁ s₂=>by
     apply LinearMap.ext;intro m;simp [add_tmul]
    map_smul':=fun r s=>by
     apply LinearMap.ext;intro m;change ((r•s) ⊗ₜ[T] n) ⊗ₜ[R] m=r•((s ⊗ₜ[T] n) ⊗ₜ[R] m);have h1:(r•s) ⊗ₜ[T] n=r•(s ⊗ₜ[T] n):=rfl;rw [h1]
     exact smul_tmul' r (s ⊗ₜ[T] n) m }
 let q0:((S ⊗[R] M) ⊗[T] N) →ₗ[T] ((S ⊗[T] N) ⊗[R] M) :=
  TensorProduct.lift
   {
    toFun:=fun sm =>
     {
      toFun:=fun n=>bwd_atom n sm
      map_add':=fun n₁ n₂=>by
       induction sm using TensorProduct.induction_on with
       | zero=>simp
       | tmul s m =>
        change (s ⊗ₜ[T] (n₁ + n₂)) ⊗ₜ[R] m=(s ⊗ₜ[T] n₁) ⊗ₜ[R] m+(s ⊗ₜ[T] n₂) ⊗ₜ[R] m;rw [tmul_add,add_tmul]
       | add u₁ u₂ ih₁ ih₂=>simp only [map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂];abel
      map_smul':=fun t n=>by
       induction sm using TensorProduct.induction_on with
       | zero=>simp
       | tmul s m =>
        change (s ⊗ₜ[T] (t•n)) ⊗ₜ[R] m=(t•(s ⊗ₜ[T] n)) ⊗ₜ[R] m;rw [TensorProduct.tmul_smul]
       | add u₁ u₂ ih₁ ih₂=>simp only [map_add,smul_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
    map_add':=fun sm₁ sm₂=>by
     apply LinearMap.ext;intro n;change bwd_atom n (sm₁ + sm₂)=bwd_atom n sm₁ + bwd_atom n sm₂;rw [map_add]
    map_smul':=fun t sm=>by
     apply LinearMap.ext;intro n;change bwd_atom n (t•sm)=t•bwd_atom n sm
     induction sm using TensorProduct.induction_on with
     | zero=>simp
     | tmul s m =>
      change ((t•s) ⊗ₜ[T] n) ⊗ₜ[R] m=(t•(s ⊗ₜ[T] n)) ⊗ₜ[R] m;rw [smul_tmul']
     | add u₁ u₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
 let e₀':(S ⊗[T] N) →ₗ[R] B :=
  {
   toFun:=fun u=>e₀ ((RestrictScalars.addEquiv R T _).symm u)
   map_add':=fun u₁ u₂=>e₀.map_add _ _
   map_smul':=fun r u=>by
    have hsm:r•u=algebraMap R T r•u:=by
     induction u using TensorProduct.induction_on with
     | zero=>simp
     | tmul s n =>
      change (r•s) ⊗ₜ[T] n=(algebraMap R T r•s) ⊗ₜ[T] n;congr 1;rw [Algebra.smul_def,Algebra.smul_def,IsScalarTower.algebraMap_apply R T S]
     | add u₁ u₂ ih₁ ih₂=>rw [smul_add,smul_add,ih₁,ih₂]
    change e₀ ((RestrictScalars.addEquiv R T _).symm (r•u))=r•e₀ ((RestrictScalars.addEquiv R T _).symm u);rw [hsm]
    exact e₀.map_smul r ((RestrictScalars.addEquiv R T _).symm u) }
 let q2:((S ⊗[T] N) ⊗[R] M) →ₗ[R] (M ⊗[R] B):=(LinearMap.lTensor M e₀').comp (TensorProduct.comm R (S ⊗[T] N) M).toLinearMap
 let bwd:RestrictScalars R T ((S ⊗[R] M) ⊗[T] N) →ₗ[R] (M ⊗[R] B) :=
  {
   toFun:=fun x=>q2 (q0 (RestrictScalars.addEquiv R T _ x))
   map_add':=fun x₁ x₂=>by rw [map_add,map_add,map_add]
   map_smul':=fun r x=>by
    change q2 (q0 (algebraMap R T r•RestrictScalars.addEquiv R T _ x))=r•q2 (q0 (RestrictScalars.addEquiv R T _ x));rw [map_smul]
    have h:∀ y:(S ⊗[T] N) ⊗[R] M,q2 (algebraMap R T r•y)=r•q2 y:=fun y=>by
     induction y using TensorProduct.induction_on with
     | zero=>simp
     | tmul u m =>
      change m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm (algebraMap R T r•u))=r•(m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm u));rw [← TensorProduct.tmul_smul];congr 1;exact e₀.map_smul r ((RestrictScalars.addEquiv R T _).symm u)
     | add y₁ y₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂]
    exact h (q0 (RestrictScalars.addEquiv R T _ x)) }
 refine LinearEquiv.ofLinearMap fwd bwd ?_ ?_
 ·
  apply LinearMap.ext;intro x;apply (RestrictScalars.addEquiv R T _).injective;let x':(S ⊗[R] M) ⊗[T] N:=RestrictScalars.addEquiv R T _ x;change (RestrictScalars.addEquiv R T _) (fwd (q2 (q0 x')))=x'
  induction x' using TensorProduct.induction_on with
  | zero=>rw [map_zero,map_zero,map_zero,map_zero]
  | tmul sm n =>
   induction sm using TensorProduct.induction_on with
   | zero=>rw [zero_tmul,map_zero,map_zero,map_zero,map_zero]
   | tmul s m =>
    change (RestrictScalars.addEquiv R T _) (fwd (m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))))=(s ⊗ₜ[R] m) ⊗ₜ[T] n;change toF0 m (RestrictScalars.addEquiv R T _ (e₀.symm (e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n)))))=(s ⊗ₜ[R] m) ⊗ₜ[T] n;rw [e₀.symm_apply_apply];rfl
   | add u₁ u₂ ih₁ ih₂ =>
    rw [add_tmul,map_add,map_add,map_add,map_add,ih₁,ih₂]
  | add x₁ x₂ ih₁ ih₂ =>
   rw [map_add,map_add,map_add,map_add,ih₁,ih₂]
 ·
  apply LinearMap.ext;intro y;change bwd (fwd y)=y
  induction y using TensorProduct.induction_on with
  | zero=>rw [map_zero,map_zero]
  | tmul m b =>
   obtain ⟨u,rfl⟩:=e₀.surjective b;let u':S ⊗[T] N:=RestrictScalars.addEquiv R T _ u;change bwd (fwd (m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm u')))=m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm u')
   induction u' using TensorProduct.induction_on with
   | zero =>
    have h0:e₀ ((RestrictScalars.addEquiv R T _).symm 0)=0:=by rw [map_zero,map_zero]
    rw [h0,tmul_zero,map_zero,map_zero]
   | tmul s n =>
    change q2 (q0 (toF0 m (RestrictScalars.addEquiv R T _
     (e₀.symm (e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))))))) =
     m ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))
    rw [e₀.symm_apply_apply];rfl
   | add u₁ u₂ ih₁ ih₂ =>
    have he:e₀ ((RestrictScalars.addEquiv R T _).symm (u₁ + u₂))=e₀ ((RestrictScalars.addEquiv R T _).symm u₁)+e₀ ((RestrictScalars.addEquiv R T _).symm u₂):=by
     rw [map_add,map_add]
    rw [he,tmul_add,map_add,map_add,ih₁,ih₂]
  | add y₁ y₂ ih₁ ih₂ =>
   rw [map_add,map_add,ih₁,ih₂]
private lemma z140 {R T S N B M₁ M₂ : Type}
  [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  (e₀ : RestrictScalars R T (S ⊗[T] N) ≃ₗ[R] B) (f:M₁ →ₗ[R] M₂) (t:M₁ ⊗[R] B) :
  (RestrictScalars.addEquiv R T _) (z139 e₀ M₂ (LinearMap.rTensor B f t))=LinearMap.rTensor N (z138 f) ((RestrictScalars.addEquiv R T _) (z139 e₀ M₁ t)):=by
 induction t using TensorProduct.induction_on with
 | zero=>simp
 | tmul m b =>
  obtain ⟨u,rfl⟩:=e₀.surjective b
  induction u using TensorProduct.induction_on with
  | zero =>
   have h0:e₀ 0=0:=map_zero e₀;change (RestrictScalars.addEquiv R T _) (z139 e₀ M₂ (LinearMap.rTensor B f (m ⊗ₜ[R] e₀ 0)))=LinearMap.rTensor N (z138 f) ((RestrictScalars.addEquiv R T _) (z139 e₀ M₁ (m ⊗ₜ[R] e₀ 0)));rw [h0,tmul_zero,map_zero,map_zero,map_zero,map_zero,map_zero,map_zero]
  | tmul s n =>
   simp only [LinearMap.rTensor_tmul]
   have h1:∀ {X:Type} [AddCommGroup X] [Module R X] (x:X),
     (RestrictScalars.addEquiv R T _) (z139 e₀ X (x ⊗ₜ[R] e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))))=(s ⊗ₜ[R] x) ⊗ₜ[T] n:=fun {X} _ _ x=>by
    unfold z139;rw [LinearEquiv.coe_ofLinearMap]
    change (TensorProduct.lift _:S ⊗[T] N →ₗ[T] (S ⊗[R] X) ⊗[T] N)
     (e₀.symm (e₀ ((RestrictScalars.addEquiv R T _).symm (s ⊗ₜ[T] n))))=(s ⊗ₜ[R] x) ⊗ₜ[T] n
    rw [e₀.symm_apply_apply];rfl
   have hfm:=h1 (f m);have hm:=h1 m;exact (hfm.trans (by rw [LinearMap.rTensor_tmul];rfl)).trans (congrArg (LinearMap.rTensor N (z138 f)) hm.symm)
  | add u₁ u₂ ih₁ ih₂ =>
   have he:e₀ (u₁ + u₂)=e₀ u₁ + e₀ u₂ := e₀.map_add u₁ u₂;change (RestrictScalars.addEquiv R T _) (z139 e₀ M₂ (LinearMap.rTensor B f (m ⊗ₜ[R] e₀ (u₁ + u₂))))=LinearMap.rTensor N (z138 f) ((RestrictScalars.addEquiv R T _) (z139 e₀ M₁ (m ⊗ₜ[R] e₀ (u₁ + u₂))));rw [he,tmul_add,map_add,map_add,map_add,map_add,map_add,map_add,ih₁,ih₂]
 | add t₁ t₂ ih₁ ih₂ =>
  rw [map_add,map_add,map_add,map_add,map_add,map_add,ih₁,ih₂]
private lemma z141 {R T S N B K F M:Type}
  [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] [Module.Flat R S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F] [Module.Flat R F]
  [AddCommGroup M] [Module R M]
  (e₀ : RestrictScalars R T (S ⊗[T] N) ≃ₗ[R] B)
  (i:K →ₗ[R] F) (p:F →ₗ[R] M)
  (hi:Injective i) (hp:Surjective p)
  (q2:LinearMap.range i=LinearMap.ker p)
  (hSF:Subsingleton (z56 T (S ⊗[R] F) N 1)) :
  Nonempty (z56 R M B 1 ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] M) N 1)):=by
 have : Subsingleton (z56 R F B 1):=z67 F B 0;obtain ⟨δR,hR1,_,hR3⟩:=z65 i p hi hp q2 B
 have hδR_inj:Injective (δR 0) :=
  (injective_iff_map_eq_zero _).mpr fun x hx=>by
   obtain ⟨y,rfl⟩:=(hR3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
 have hδR_rng:LinearMap.range (δR 0)=LinearMap.ker (z58 i B 0):=LinearMap.exact_iff.mp (hR1 0) |>.symm;let e1R:z56 R M B 1 ≃ₗ[R] LinearMap.ker (z58 i B 0):=(LinearEquiv.ofInjective (δR 0) hδR_inj).trans (LinearEquiv.ofEq _ _ hδR_rng);have hiS:Injective (z138 (T:=T) (S:=S) i):=Module.Flat.lTensor_preserves_injective_linearMap i hi
 have hpS:Surjective (z138 (T:=T) (S:=S) p):=LinearMap.lTensor_surjective S hp
 have q0:LinearMap.range (z138 (T:=T) (S:=S) i)=LinearMap.ker (z138 (T:=T) (S:=S) p):=by
  ext x;exact (lTensor_exact S (LinearMap.exact_iff.mpr q2.symm) hp x).symm
 obtain ⟨δT,hT1,_,hT3⟩:=z65 (z138 (T:=T) (S:=S) i) (z138 (T:=T) (S:=S) p)
  hiS hpS q0 N
 have hδT_inj:Injective (δT 0) :=
  (injective_iff_map_eq_zero _).mpr fun x hx=>by
   obtain ⟨y,rfl⟩:=(hT3 0 x).mp hx;rw [Subsingleton.elim y 0,map_zero]
 have hδT_rng:LinearMap.range (δT 0)=LinearMap.ker (z58 (z138 (T:=T) (S:=S) i) N 0):=LinearMap.exact_iff.mp (hT1 0) |>.symm
 let e1T:z56 T (S ⊗[R] M) N 1 ≃ₗ[T]
   LinearMap.ker (z58 (z138 (T:=T) (S:=S) i) N 0) :=
  (LinearEquiv.ofInjective (δT 0) hδT_inj).trans (LinearEquiv.ofEq _ _ hδT_rng)
 let eK:z56 R K B 0 ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] K) N 0) :=
  ((z59 R K B).trans (z139 e₀ K)).trans
   (z136 R T (z59 T (S ⊗[R] K) N).symm)
 let eF:z56 R F B 0 ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] F) N 0) :=
  ((z59 R F B).trans (z139 e₀ F)).trans
   (z136 R T (z59 T (S ⊗[R] F) N).symm)
 have hsq:∀ x:z56 R K B 0,
   (RestrictScalars.addEquiv R T _) (eF (z58 i B 0 x))=z58 (z138 (T:=T) (S:=S) i) N 0 ((RestrictScalars.addEquiv R T _) (eK x)):=fun x=>by
  apply (z59 T (S ⊗[R] F) N).injective;rw [z66]
  change (z59 T (S ⊗[R] F) N) ((z59 T (S ⊗[R] F) N).symm
   ((RestrictScalars.addEquiv R T _) (z139 e₀ F (z59 R F B (z58 i B 0 x))))) =
   LinearMap.rTensor N (z138 (T:=T) (S:=S) i)
    ((z59 T (S ⊗[R] K) N) ((z59 T (S ⊗[R] K) N).symm
     ((RestrictScalars.addEquiv R T _) (z139 e₀ K (z59 R K B x)))))
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply,z66];exact z140 e₀ i (z59 R K B x)
 let q1:LinearMap.ker (z58 i B 0) ≃ₗ[R]
   RestrictScalars R T (LinearMap.ker (z58 (z138 (T:=T) (S:=S) i) N 0)) :=
  {
   toFun:=fun p=>⟨(RestrictScalars.addEquiv R T _) (eK p.1),by
    rw [LinearMap.mem_ker,← hsq p.1,LinearMap.mem_ker.mp p.2,map_zero,map_zero]⟩
   invFun:=fun q=>⟨eK.symm ((RestrictScalars.addEquiv R T _).symm q.1),by
    rw [LinearMap.mem_ker];apply eF.injective;apply (RestrictScalars.addEquiv R T _).injective;rw [map_zero,map_zero,hsq]
    have hq':(RestrictScalars.addEquiv R T _) (eK (eK.symm ((RestrictScalars.addEquiv R T _).symm q.1)))=q.1:=by
     rw [eK.apply_symm_apply];rfl
    rw [hq']
    exact LinearMap.mem_ker.mp q.2⟩
   map_add':=fun p₁ p₂=>Subtype.ext (by
    change (RestrictScalars.addEquiv R T _) (eK (p₁.1+p₂.1))=(RestrictScalars.addEquiv R T _) (eK p₁.1)+(RestrictScalars.addEquiv R T _) (eK p₂.1)
    rw [map_add,map_add])
   map_smul':=fun r p=>Subtype.ext (by
    change (RestrictScalars.addEquiv R T _) (eK (r•p.1))=algebraMap R T r•(RestrictScalars.addEquiv R T _) (eK p.1)
    rw [eK.map_smul];rfl)
   left_inv:=fun p=>Subtype.ext (eK.symm_apply_apply p.1)
   right_inv:=fun q=>Subtype.ext (by
    change (RestrictScalars.addEquiv R T _) (eK (eK.symm ((RestrictScalars.addEquiv R T _).symm q.1)))=q.1
    rw [eK.apply_symm_apply];rfl) }
 exact ⟨(e1R.trans q1).trans (z136 R T e1T.symm)⟩
private lemma z142 {R T S N B K F M:Type}
  [CommRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] [Module.Flat R S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F] [Module.Flat R F]
  [AddCommGroup M] [Module R M]
  (i:K →ₗ[R] F) (p:F →ₗ[R] M)
  (hi:Injective i) (hp:Surjective p)
  (q1:LinearMap.range i=LinearMap.ker p) (j : ℕ)
  (hSF1:Subsingleton (z56 T (S ⊗[R] F) N (j+1)))
  (hSF2:Subsingleton (z56 T (S ⊗[R] F) N (j+2)))
  (eIH:z56 R K B (j+1) ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] K) N (j+1))) :
  Nonempty (z56 R M B (j+2) ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] M) N (j+2))):=by
 have : Subsingleton (z56 R F B (j+1)):=z67 F B j;have : Subsingleton (z56 R F B (j+2)):=z67 F B (j+1);obtain ⟨δR,hR1,_,hR3⟩:=z65 i p hi hp q1 B
 have hδR_bij:Bijective (δR (j+1)):=by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_,fun y => ?_⟩
  ·
   obtain ⟨z,rfl⟩:=(hR3 (j+1) x).mp hx;rw [Subsingleton.elim z 0,map_zero]
  · exact (hR1 (j+1) y).mp (Subsingleton.elim _ 0)
 have hiS:Injective (z138 (T:=T) (S:=S) i):=Module.Flat.lTensor_preserves_injective_linearMap i hi;have hpS:Surjective (z138 (T:=T) (S:=S) p):=LinearMap.lTensor_surjective S hp
 have q0:LinearMap.range (z138 (T:=T) (S:=S) i)=LinearMap.ker (z138 (T:=T) (S:=S) p):=by
  ext x;exact (lTensor_exact S (LinearMap.exact_iff.mpr q1.symm) hp x).symm
 obtain ⟨δT,hT1,_,hT3⟩:=z65 (z138 (T:=T) (S:=S) i) (z138 (T:=T) (S:=S) p)
  hiS hpS q0 N
 have hδT_bij:Bijective (δT (j+1)):=by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx => ?_,fun y => ?_⟩
  ·
   obtain ⟨z,rfl⟩:=(hT3 (j+1) x).mp hx;rw [Subsingleton.elim z 0,map_zero]
  · exact (hT1 (j+1) y).mp (Subsingleton.elim _ 0)
 let eR:z56 R M B (j+2) ≃ₗ[R] z56 R K B (j+1):=LinearEquiv.ofBijective (δR (j+1)) hδR_bij;let eT:z56 T (S ⊗[R] M) N (j+2) ≃ₗ[T] z56 T (S ⊗[R] K) N (j+1):=LinearEquiv.ofBijective (δT (j+1)) hδT_bij;exact ⟨(eR.trans eIH).trans (z136 R T eT.symm)⟩
private noncomputable def z143 {R T S:Type} [CommRing R] [CommRing T] [CommRing S]
  [Algebra R S] [Algebra T S] (r : ℕ) :
  (S ⊗[R] (Fin r→R)) ≃ₗ[T] (Fin r→S):=by
 let q0:(S ⊗[R] (Fin r→R)) →ₗ[R] (Fin r→S) :=
  TensorProduct.lift
   {
    toFun:=fun s =>
     {
      toFun:=fun g i=>g i•s
      map_add':=fun g₁ g₂=>by ext i;simp [add_smul]
      map_smul':=fun a g=>by ext i;simp [mul_smul] }
    map_add':=fun s₁ s₂=>by apply LinearMap.ext;intro g;ext i;simp [smul_add]
    map_smul':=fun a s=>by apply LinearMap.ext;intro g;ext i;exact (smul_comm a (g i) s).symm }
 let fwd:(S ⊗[R] (Fin r→R)) →ₗ[T] (Fin r→S) :=
  {
   toFun:=q0
   map_add':=q0.map_add
   map_smul':=fun t x=>by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul s g =>
     ext i;change g i•(t•s)=t•(g i•s);rw [smul_comm]
    | add x₁ x₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
 let bwd:(Fin r→S) →ₗ[T] (S ⊗[R] (Fin r→R)) :=
  {
   toFun:=fun f => ∑ i:Fin r,f i ⊗ₜ[R] Pi.single i (1:R)
   map_add':=fun f₁ f₂=>by simp [add_tmul,Finset.sum_add_distrib]
   map_smul':=fun t f=>by simp [smul_tmul',Finset.smul_sum] }
 refine LinearEquiv.ofLinearMap fwd bwd ?_ ?_
 ·
  apply LinearMap.ext;intro f;ext j
  simp only [LinearMap.comp_apply,LinearMap.id_apply,bwd,fwd,q0,LinearMap.coe_mk,AddHom.coe_mk,
   map_sum,TensorProduct.lift.tmul,Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij;simp [Pi.single_eq_of_ne (Ne.symm hij)]
  · intro hj;exact absurd (Finset.mem_univ j) hj
 ·
  apply LinearMap.ext;intro x
  induction x using TensorProduct.induction_on with
  | zero=>simp
  | tmul s g =>
   simp only [LinearMap.comp_apply,LinearMap.id_apply,bwd,fwd,q0,LinearMap.coe_mk,AddHom.coe_mk,TensorProduct.lift.tmul]
   have hg:g = ∑ i:Fin r,g i•Pi.single i (1:R):=by
    ext j;rw [Finset.sum_apply,Finset.sum_eq_single j]
    · simp
    · intro i _ hij;simp [Pi.single_eq_of_ne (Ne.symm hij)]
    · intro hj;exact absurd (Finset.mem_univ j) hj
   conv_rhs=>rw [hg]
   rw [TensorProduct.tmul_sum]
   refine Finset.sum_congr rfl fun i _ => ?_
   rw [smul_tmul]
  | add x₁ x₂ ih₁ ih₂ =>
   simp only [LinearMap.comp_apply,LinearMap.id_apply,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂]
private lemma z144 {T A B N:Type} [CommRing T]
  [AddCommGroup A] [Module T A] [AddCommGroup B] [Module T B] [AddCommGroup N] [Module T N]
  (e:A ≃ₗ[T] B) (k : ℕ) :
  Nonempty (z56 T A N k ≃ₗ[T] z56 T B N k):=by
 let iso:ModuleCat.of T A ≅ ModuleCat.of T B:=e.toModuleIso;exact ⟨(((Tor (ModuleCat.{0} T) k).mapIso iso).app (ModuleCat.of T N)).toLinearEquiv⟩
lemma z145 {R T S N B:Type}
  [CommRing R] [IsNoetherianRing R] [CommRing T] [CommRing S]
  [Algebra R T] [Algebra R S] [Algebra T S] [IsScalarTower R T S] [Module.Flat R S]
  [AddCommGroup N] [Module T N] [AddCommGroup B] [Module R B]
  (q0:∀ q : ℕ,Subsingleton (z56 T S N (q+1)))
  (e₀ : RestrictScalars R T (S ⊗[T] N) ≃ₗ[R] B) :
  ∀ (i : ℕ) (M:Type) [AddCommGroup M] [Module R M] [Module.Finite R M],Nonempty (z56 R M B i ≃ₗ[R] RestrictScalars R T (z56 T (S ⊗[R] M) N i))
 | 0,M,_,_,_ =>
  ⟨((z59 R M B).trans (z139 e₀ M)).trans
   (z136 R T (z59 T (S ⊗[R] M) N).symm)⟩
 | 1,M,_,_,_=>by
  obtain ⟨r,f,hf⟩:=Module.Finite.exists_fin (R:=R) (M:=M)
  let p:(Fin r→R) →ₗ[R] M :=
   {
    toFun:=fun g => ∑ i:Fin r,g i•f i
    map_add':=fun g₁ g₂=>by simp [add_smul,Finset.sum_add_distrib]
    map_smul':=fun a g=>by simp [Finset.smul_sum,mul_smul] }
  have hp:Surjective p:=fun m=>by
   have hm:m∈Submodule.span R (Set.range f):=hf▸Submodule.mem_top;rw [Submodule.mem_span_range_iff_exists_fun] at hm;obtain ⟨c,rfl⟩:=hm;exact ⟨c,rfl⟩
  let K:=LinearMap.ker p;have : Module.Finite R K:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K);have q1:LinearMap.range K.subtype=LinearMap.ker p:=Submodule.range_subtype K;obtain ⟨eT⟩:=z144 (T:=T) (N:=N) (z143 (R:=R) (T:=T) (S:=S) r) 1
  have q3:Subsingleton (z56 T (S ⊗[R] (Fin r→R)) N 1):=by
   have : Subsingleton (z56 T (Fin r→S) N 1):=z137 q0 r 0;exact eT.toEquiv.subsingleton
  exact z141 e₀ K.subtype p Subtype.val_injective hp q1 q3
 | j+2,M,_,_,_=>by
  obtain ⟨r,f,hf⟩:=Module.Finite.exists_fin (R:=R) (M:=M)
  let p:(Fin r→R) →ₗ[R] M :=
   {
    toFun:=fun g => ∑ i:Fin r,g i•f i
    map_add':=fun g₁ g₂=>by simp [add_smul,Finset.sum_add_distrib]
    map_smul':=fun a g=>by simp [Finset.smul_sum,mul_smul] }
  have hp:Surjective p:=fun m=>by
   have hm:m∈Submodule.span R (Set.range f):=hf▸Submodule.mem_top;rw [Submodule.mem_span_range_iff_exists_fun] at hm;obtain ⟨c,rfl⟩:=hm;exact ⟨c,rfl⟩
  let K:=LinearMap.ker p;have : Module.Finite R K:=Module.Finite.iff_fg.mpr (IsNoetherian.noetherian K);have q1:LinearMap.range K.subtype=LinearMap.ker p:=Submodule.range_subtype K;obtain ⟨eT1⟩:=z144 (T:=T) (N:=N) (z143 (R:=R) (T:=T) (S:=S) r) (j+1);obtain ⟨eT2⟩:=z144 (T:=T) (N:=N) (z143 (R:=R) (T:=T) (S:=S) r) (j+2)
  have q3:Subsingleton (z56 T (S ⊗[R] (Fin r→R)) N (j+1)):=by
   have : Subsingleton (z56 T (Fin r→S) N (j+1)):=z137 q0 r j;exact eT1.toEquiv.subsingleton
  have q2:Subsingleton (z56 T (S ⊗[R] (Fin r→R)) N (j+2)):=by
   have : Subsingleton (z56 T (Fin r→S) N (j+2)):=z137 q0 r (j+1);exact eT2.toEquiv.subsingleton
  obtain ⟨eIH⟩:=z145 q0 e₀ (j+1) K;exact z142 K.subtype p Subtype.val_injective hp q1 j q3 q2 eIH
private lemma z146 {R A E M:Type}
  [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]
  [AddCommGroup E] [Module A E] [AddCommGroup M] [Module R M]
  (e:M ≃+ E) (q1:∀ (r:R) (x:M),e (r•x)=algebraMap R A r•e x)
  (q0:Module.length (ResidueField R) (ResidueField A)=1) :
  Module.length R M=Module.length A E:=by
 letI : Module R E:=Module.restrictScalars R A E
 haveI : IsScalarTower R A E:=IsScalarTower.restrictScalars R A E
 let q2:M ≃ₗ[R] E:={ e with map_smul':=q1 };rw [q2.length_eq];have h1:=IsLocalRing.length_restrictScalars R A E;rw [q0,mul_one] at h1;exact h1
private lemma z147 {R T:Type}
  [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
  [Algebra R T]
  (P Q:Ideal R) (Q₂ I:Ideal T) (hI:I=P.map (algebraMap R T)⊔Q₂)
  [IsLocalRing (T⧸I)]
  (Δ_list:List T)
  (π : T →+* R) (hπ_alg:∀ r:R,π (algebraMap R T r)=r)
  (hker_π : RingHom.ker π = ofList Δ_list)
  (hQ₂_le:Q₂ ≤ RingHom.ker ((Ideal.Quotient.mk Q).comp π))
  (q6:∀ q∈Q,∃ d∈ofList Δ_list,Ideal.Quotient.mk Q₂ (algebraMap R T q)=Ideal.Quotient.mk Q₂ d)
  (hΔ_reg:z110 T Δ_list)
  (q7:Module.Flat R (T⧸Q₂))
  (q8:∀ q : ℕ,Subsingleton (z56 T (T⧸Q₂) (T⧸ofList Δ_list) (q+1)))
  (q3:∀ r∈maximalIdeal R,algebraMap R T r∈maximalIdeal T)
  (q2:Surjective
   ((residue (T⧸I)).comp ((Ideal.Quotient.mk I).comp (algebraMap R T)))) :
  ∀ i : ℕ,Module.length R (z56 R (R⧸P) (R⧸Q) i)=Module.length (T⧸I) (z94 (T⧸I) (T⧸I) (Δ_list.map (Ideal.Quotient.mk I)) i):=by
 intro i;let A:=T⧸I;let Δ : Ideal T:=ofList Δ_list;let S:=T⧸Q₂;let qS:T →+* S:=Ideal.Quotient.mk Q₂;let qA:T →+* A:=Ideal.Quotient.mk I;let fRS:R →+* S:=algebraMap R S
 let ψ : S →+* R⧸Q:=Ideal.Quotient.lift Q₂ ((Ideal.Quotient.mk Q).comp π) (fun t ht=>hQ₂_le ht)
 let πQ:(T ⧸ Δ) →+* R⧸Q:=Ideal.Quotient.lift Δ ((Ideal.Quotient.mk Q).comp π) (fun t ht=>by
  have ht0 : π t=0:=RingHom.mem_ker.mp (hker_π.symm▸ht)
  rw [RingHom.comp_apply,ht0,map_zero])
 have hψ_fRS:∀ r:R,ψ (fRS r)=Ideal.Quotient.mk Q r:=fun r=>by
  change Ideal.Quotient.mk Q (π (algebraMap R T r))=Ideal.Quotient.mk Q r;rw [hπ_alg]
 have hψ_qS:∀ t:T,ψ (qS t)=Ideal.Quotient.mk Q (π t):=fun _=>rfl
 let e₀ : RestrictScalars R T (S ⊗[T] (T ⧸ Δ)) ≃ₗ[R] (R⧸Q):=by
  letI : Algebra T (R⧸Q):=((Ideal.Quotient.mk Q).comp π).toAlgebra
  let e₀_fwdT:(S ⊗[T] (T ⧸ Δ)) →ₗ[T] (R⧸Q) :=
   TensorProduct.lift
    {
     toFun:=fun s =>
      {
       toFun:=fun u => ψ s * πQ u
       map_add':=fun u₁ u₂=>by rw [map_add,mul_add]
       map_smul':=fun t u=>by
        change ψ s * πQ (Ideal.Quotient.mk Δ t*u)=Ideal.Quotient.mk Q (π t)*(ψ s * πQ u);rw [map_mul];change ψ s*(Ideal.Quotient.mk Q (π t) * πQ u)=_
        ring }
     map_add':=fun s₁ s₂=>by apply LinearMap.ext;intro u;simp [map_add,add_mul]
     map_smul':=fun t s=>by
      apply LinearMap.ext;intro u;change ψ (qS t*s) * πQ u=Ideal.Quotient.mk Q (π t)*(ψ s * πQ u)
      rw [map_mul,hψ_qS];ring }
  let e₀_fwd:RestrictScalars R T (S ⊗[T] (T ⧸ Δ)) →ₗ[R] (R⧸Q) :=
   {
    toFun:=fun x=>e₀_fwdT (RestrictScalars.addEquiv R T _ x)
    map_add':=fun x₁ x₂=>e₀_fwdT.map_add _ _
    map_smul':=fun r x=>by
     change e₀_fwdT (algebraMap R T r•RestrictScalars.addEquiv R T _ x)=r•e₀_fwdT (RestrictScalars.addEquiv R T _ x);rw [e₀_fwdT.map_smul];change Ideal.Quotient.mk Q (π (algebraMap R T r))*e₀_fwdT _=Ideal.Quotient.mk Q r*e₀_fwdT _
     rw [hπ_alg] }
  let e₀_bwd0:(R⧸Q) →+ (S ⊗[T] (T ⧸ Δ)) :=
   QuotientAddGroup.lift Q.toAddSubgroup
    {
     toFun:=fun r=>fRS r ⊗ₜ[T] (1:T ⧸ Δ)
     map_zero':=by rw [map_zero,zero_tmul]
     map_add':=fun r₁ r₂=>by rw [map_add,add_tmul] }
    (fun q hq=>by
     rw [AddMonoidHom.mem_ker];change qS (algebraMap R T q) ⊗ₜ[T] (1:T ⧸ Δ)=0;obtain ⟨d,hd,hqd⟩:=q6 q hq;rw [hqd]
     have h2:qS d ⊗ₜ[T] (1:T ⧸ Δ)=(1:S) ⊗ₜ[T] (d•(1:T ⧸ Δ)):=by
      have : qS d=d•(1:S):=by change qS d=qS d*1;rw [mul_one]
      rw [this,smul_tmul]
     rw [h2]
     have h3:d•(1:T ⧸ Δ)=0:=by
      change Ideal.Quotient.mk Δ d*1=0;rw [mul_one,Ideal.Quotient.eq_zero_iff_mem];exact hd
     rw [h3,tmul_zero])
  let e₀_bwd:(R⧸Q) →ₗ[R] RestrictScalars R T (S ⊗[T] (T ⧸ Δ)) :=
   {
    toFun:=fun y=>(RestrictScalars.addEquiv R T _).symm (e₀_bwd0 y)
    map_add':=fun y₁ y₂=>e₀_bwd0.map_add y₁ y₂
    map_smul':=fun a y=>by
     obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective y;apply (RestrictScalars.addEquiv R T _).injective;change fRS (a*r) ⊗ₜ[T] (1:T ⧸ Δ)=algebraMap R T a•(fRS r ⊗ₜ[T] (1:T ⧸ Δ))
     rw [smul_tmul',map_mul];rfl }
  refine LinearEquiv.ofLinearMap e₀_fwd e₀_bwd ?_ ?_
  ·
   apply LinearMap.ext;intro y;obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective y;change ψ (fRS r) * πQ 1=Ideal.Quotient.mk Q r;rw [hψ_fRS,map_one,mul_one]
  ·
   apply LinearMap.ext;intro x;apply (RestrictScalars.addEquiv R T _).injective;let x':S ⊗[T] (T ⧸ Δ):=RestrictScalars.addEquiv R T _ x;change e₀_bwd0 (e₀_fwdT x')=x'
   induction x' using TensorProduct.induction_on with
   | zero=>rw [map_zero,map_zero]
   | tmul s u =>
    obtain ⟨t₁,rfl⟩:=Ideal.Quotient.mk_surjective s;obtain ⟨t₂,rfl⟩:=Ideal.Quotient.mk_surjective u;change e₀_bwd0 (Ideal.Quotient.mk Q (π t₁)*Ideal.Quotient.mk Q (π t₂))=qS t₁ ⊗ₜ[T] Ideal.Quotient.mk Δ t₂;rw [← map_mul (Ideal.Quotient.mk Q)];change fRS (π t₁ * π t₂) ⊗ₜ[T] (1:T ⧸ Δ)=qS t₁ ⊗ₜ[T] Ideal.Quotient.mk Δ t₂
    have q15:algebraMap R T (π (t₁ * t₂)) - t₁ * t₂ ∈ Δ := by
     change _∈ofList Δ_list;rw [← hker_π,RingHom.mem_ker,map_sub,hπ_alg,sub_self]
    have q11:Ideal.Quotient.mk Δ (algebraMap R T (π (t₁ * t₂)))=Ideal.Quotient.mk Δ (t₁ * t₂):=Ideal.Quotient.eq.mpr q15
    have hL:fRS (π t₁ * π t₂) ⊗ₜ[T] (1:T ⧸ Δ)=(1:S) ⊗ₜ[T] Ideal.Quotient.mk Δ (algebraMap R T (π (t₁ * t₂))):=by
     rw [← map_mul π]
     have : fRS (π (t₁ * t₂))=algebraMap R T (π (t₁ * t₂))•(1:S):=by
      change qS (algebraMap R T (π (t₁ * t₂)))=qS (algebraMap R T (π (t₁ * t₂)))*1;rw [mul_one]
     rw [this,smul_tmul];congr 1;change Ideal.Quotient.mk Δ (algebraMap R T (π (t₁ * t₂)))*1=_;rw [mul_one]
    have hR:qS t₁ ⊗ₜ[T] Ideal.Quotient.mk Δ t₂ = (1:S) ⊗ₜ[T] Ideal.Quotient.mk Δ (t₁ * t₂):=by
     have : qS t₁ = t₁ • (1:S):=by change qS t₁ = qS t₁ * 1;rw [mul_one]
     rw [this,smul_tmul];congr 1
    rw [hL,hR,q11]
   | add x₁ x₂ ih₁ ih₂=>rw [map_add,map_add,ih₁,ih₂]
 let qSA:S →+* A:=Ideal.Quotient.lift Q₂ qA (fun t ht =>
  Ideal.Quotient.eq_zero_iff_mem.mpr (hI.symm▸mem_sup_right ht))
 let qPA:(R⧸P) →+* A:=Ideal.Quotient.lift P (algebraMap R A) (fun r hr =>
  Ideal.Quotient.eq_zero_iff_mem.mpr (hI.symm▸mem_sup_left (mem_map_of_mem (algebraMap R T) hr)))
 let q5:(S ⊗[R] (R⧸P)) →ₗ[R] A :=
  TensorProduct.lift
   {
    toFun:=fun s =>
     {
      toFun:=fun u=>qSA s*qPA u
      map_add':=fun u₁ u₂=>by rw [map_add,mul_add]
      map_smul':=fun r u=>by
       rw [Algebra.smul_def,RingHom.id_apply,Algebra.smul_def,map_mul];change qSA s*(algebraMap R A r*qPA u)=algebraMap R A r*(qSA s*qPA u)
       ring }
    map_add':=fun s₁ s₂=>by apply LinearMap.ext;intro u;simp [map_add,add_mul]
    map_smul':=fun r s=>by
     apply LinearMap.ext;intro u;simp only [LinearMap.coe_mk,AddHom.coe_mk,LinearMap.smul_apply,RingHom.id_apply,Algebra.smul_def,map_mul];change (algebraMap R A r*qSA s)*qPA u=algebraMap R A r*(qSA s*qPA u)
     ring }
 let q12:(S ⊗[R] (R⧸P)) →ₗ[T] A :=
  {
   toFun:=q5
   map_add':=q5.map_add
   map_smul':=fun t x=>by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul s u =>
     change qSA (qS t*s)*qPA u=qA t*(qSA s*qPA u);rw [map_mul];change (qA t*qSA s)*qPA u=_;ring
    | add x₁ x₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
 let q10:A →ₗ[T] (S ⊗[R] (R⧸P)) :=
  Submodule.liftQ I
   {
    toFun:=fun t=>qS t ⊗ₜ[R] (1:R⧸P)
    map_add':=fun t₁ t₂=>by rw [map_add,add_tmul]
    map_smul':=fun t₁ t₂=>by
     change (t₁ • qS t₂) ⊗ₜ[R] (1:R⧸P)=t₁ • (qS t₂ ⊗ₜ[R] (1:R⧸P))
     rw [smul_tmul'] }
   (by
    rw [hI]
    refine sup_le ?_ ?_
    ·
     rw [map_le_iff_le_comap];intro r hr;rw [mem_comap,LinearMap.mem_ker];change qS (algebraMap R T r) ⊗ₜ[R] (1:R⧸P)=0
     have : qS (algebraMap R T r)=r•(1:S):=by rw [Algebra.smul_def,mul_one];rfl
     rw [this,smul_tmul]
     have h0:r•(1:R⧸P)=0:=by
      rw [Algebra.smul_def,mul_one];exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
     rw [h0,tmul_zero]
    ·
     intro x hx;rw [LinearMap.mem_ker];change qS x ⊗ₜ[R] (1:R⧸P)=0
     rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx,zero_tmul])
 let eA:(S ⊗[R] (R⧸P)) ≃ₗ[T] A :=
  LinearEquiv.ofLinearMap q12 q10
   (by
    apply LinearMap.ext;intro a;obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;change qSA (qS t)*qPA 1=qA t
    rw [map_one,mul_one];rfl)
   (by
    apply LinearMap.ext;intro x
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul s u =>
     obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective s;obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective u;change q10 (qA t*qA (algebraMap R T r))=qS t ⊗ₜ[R] Ideal.Quotient.mk P r;rw [← map_mul];change qS (t*algebraMap R T r) ⊗ₜ[R] (1:R⧸P)=qS t ⊗ₜ[R] Ideal.Quotient.mk P r;rw [map_mul]
     have : qS t*qS (algebraMap R T r)=r•qS t:=by rw [Algebra.smul_def,mul_comm];rfl
     rw [this,smul_tmul];congr 1;rw [Algebra.smul_def,mul_one];rfl
    | add x₁ x₂ ih₁ ih₂ =>
     simp only [LinearMap.comp_apply,LinearMap.id_apply,map_add] at ih₁ ih₂ ⊢
     rw [ih₁,ih₂])
 have q1:(maximalIdeal A).comap qA=maximalIdeal T:=eq_maximalIdeal (comap_isMaximal_of_surjective qA Ideal.Quotient.mk_surjective)
 haveI : IsLocalHom (algebraMap R A):=by
  refine ⟨fun r hr => ?_⟩
  by_contra hnu
  have hrm:r∈maximalIdeal R:=(mem_maximalIdeal r).mpr hnu
  have ham:algebraMap R A r∈maximalIdeal A:=by
   change algebraMap R T r∈(maximalIdeal A).comap qA;rw [q1];exact q3 r hrm
  exact (mem_maximalIdeal (algebraMap R A r)).mp ham hr
 have hres_surj':Surjective (algebraMap (ResidueField R) (ResidueField A)):=fun y=>by
  obtain ⟨r,hr⟩:=q2 y;exact ⟨residue R r,hr⟩
 have q4:Module.length (ResidueField R) (ResidueField A)=1:=by
  let q14:ResidueField R ≃ₗ[ResidueField R] ResidueField A :=
   LinearEquiv.ofBijective (Algebra.linearMap (ResidueField R) (ResidueField A))
    ⟨(algebraMap (ResidueField R) (ResidueField A)).injective,hres_surj'⟩
  rw [← q14.length_eq,Module.length_eq_one]
 obtain ⟨e1⟩:=z145 (R:=R) (T:=T) (S:=S) (N:=T ⧸ Δ) (B:=R⧸Q)
  q8 e₀ i (R⧸P)
 obtain ⟨e2⟩:=z144 (T:=T) (N:=T ⧸ Δ) eA i;obtain ⟨e3⟩:=z114 Δ_list hΔ_reg A i;obtain ⟨e4⟩:=z135 (T:=T) (S:=A) (M:=A) Δ_list i
 let q13:z56 T (S ⊗[R] (R⧸P)) (T ⧸ Δ) i ≃ₗ[T]
   RestrictScalars T A (z94 A A (Δ_list.map qA) i) :=
  (e2.trans e3).trans e4
 let q9:z56 R (R⧸P) (R⧸Q) i ≃+ z94 A A (Δ_list.map qA) i :=
  (e1.toAddEquiv.trans (RestrictScalars.addEquiv R T _)).trans
   (q13.toAddEquiv.trans (RestrictScalars.addEquiv T A _))
 have q0:∀ (r:R) (x:z56 R (R⧸P) (R⧸Q) i),q9 (r•x)=algebraMap R A r•q9 x:=fun r x=>by
  change (RestrictScalars.addEquiv T A _) (q13 ((RestrictScalars.addEquiv R T _) (e1 (r•x))))=algebraMap R A r•(RestrictScalars.addEquiv T A _) (q13 ((RestrictScalars.addEquiv R T _) (e1 x)));rw [e1.map_smul];change (RestrictScalars.addEquiv T A _) (q13 (algebraMap R T r•(RestrictScalars.addEquiv R T _) (e1 x)))=_;rw [q13.map_smul];rfl
 exact z146 q9 q0 q4
private lemma z148
    {V:Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] (p:V) (hp:maximalIdeal V=span {p})
    (n : ℕ) (P Q:Ideal (z0 V n)) [P.IsPrime] [Q.IsPrime]
    (hPQ:(P⊔Q).radical=maximalIdeal (z0 V n))
    (hpQ:z13 V n p∉Q)
    (q28:ringKrullDim (z0 (z0 V n) n ⧸
      (P.map (z15 (z13 V n) n)⊔Q.map (z13 (z0 V n) n))) =
      (n:WithBot ℕ∞)) :
    0 < intersectionMultiplicity (z0 V n)
      (z0 V n⧸P) (z0 V n⧸Q):=by
  let R:=z0 V n;let T:=z0 R n;let i₁ : R →+* T:=z15 (z13 V n) n;let i₂ : R →+* T:=z13 R n;let I:Ideal T:=P.map i₁ ⊔ Q.map i₂;let A:=T⧸I;let qA:T →+* A:=Ideal.Quotient.mk I;let S:=T⧸Q.map i₂;let qS:T →+* S:=Ideal.Quotient.mk (Q.map i₂);have : IsLocalRing (R⧸Q):=z36 Q;have : IsAdicComplete (maximalIdeal (R⧸Q)) (R⧸Q):=z43 Q
  obtain ⟨eT,heT_C,heT_var,heT_symm_C,heT_symm_var⟩:=z47 R n (fun j=>z14 V j) (fun j=>z18 j)
  let Δ_list:List T:=(z124 R n).map eT.symm;let Δ : Ideal T:=ofList Δ_list
  have hΔ_reg:z110 T Δ_list:=z129 eT.symm (z124 R n)
    (z131 R n)
  let π : T →+* R:=(z48 R n).comp eT.toRingHom
  have hπ_i₂ : ∀ r:R,π (i₂ r)=r:=fun r=>by
    change z48 R n (eT (z13 R n r))=r;rw [heT_C,z49]
  have hπ_var:∀ j:Fin n,π (z14 R j)=z14 V j:=fun j=>by
    change z48 R n (eT (z14 R j))=z14 V j;rw [heT_var,map_add,z50,zero_add,z49]
  have hπ_i₁ : ∀ r:R,π (i₁ r)=r:=by
    have q29 : π.comp i₁ = RingHom.id R:=by
      refine z45 (C:=V) (n:=n) (π.comp i₁) (RingHom.id R)
        (fun c=>by
          change π (z15 (z13 V n) n (z13 V n c))=z13 V n c
          rw [z19];exact hπ_i₂ (z13 V n c))
        (fun j=>by
          change π (z15 (z13 V n) n (z14 V j))=z14 V j
          rw [z20];exact hπ_var j)
        (fun j=>by
          change π (z15 (z13 V n) n (z14 V j))∈maximalIdeal R
          rw [z20,hπ_var j];exact z18 j)
    exact fun r=>RingHom.congr_fun q29 r
  have hker_π : RingHom.ker π = Δ := by
    ext t;rw [RingHom.mem_ker];change eT t∈RingHom.ker (z48 R n)↔t∈ofList ((z124 R n).map eT.symm);rw [z51 R n,← z126 R n]
    have q32:ofList ((z124 R n).map eT.symm)=(ofList (z124 R n)).map eT.symm.toRingHom:=by
      rw [ofList,ofList,map_span];congr 1;ext y;simp
    rw [q32,mem_map_iff_of_surjective eT.symm.toRingHom eT.symm.surjective]
    exact ⟨fun ht=>⟨eT t,ht,eT.symm_apply_apply t⟩,fun ⟨u,hu,hut⟩=>by
      have hu':eT.symm u=t:=hut
      rw [← hu',eT.apply_symm_apply];exact hu⟩
  let eS:S ≃+* z0 (R⧸Q) n:=z27 Q n;let fRS:R →+* S:=qS.comp i₁
  have q5:letI : Algebra R S:=fRS.toAlgebra;Module.Flat R S:=by
    letI : Algebra R S:=fRS.toAlgebra
    let gV:V →+* R⧸Q:=(Ideal.Quotient.mk Q).comp (z13 V n)
    have q8:gV p∈maximalIdeal (R⧸Q):=by
      have q25:(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective);change z13 V n p∈(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q);rw [q25];exact z17 n (hp▸subset_span rfl)
    have q12:gV p≠0:=fun h0=>hpQ (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    letI : Algebra R (z0 (R⧸Q) n):=(z15 gV n).toAlgebra
    have : Module.Flat R (z0 (R⧸Q) n):=z77 gV p hp q8 q12 n
    have q30:∀ r:R,eS (algebraMap R S r)=algebraMap R (z0 (R⧸Q) n) r:=by
      have heq:(eS.toRingHom.comp fRS)=z15 gV n:=by
        refine z45 (C:=V) (n:=n) (eS.toRingHom.comp fRS) (z15 gV n)
          (fun c=>by
            change eS (qS (i₁ (z13 V n c)))=z15 gV n (z13 V n c);rw [z19,z19];change z15 (Ideal.Quotient.mk Q) n (z13 R n (z13 V n c))=_
            rw [z19];rfl)
          (fun j=>by
            change eS (qS (i₁ (z14 V j)))=z15 gV n (z14 V j);rw [z20,z20];change z15 (Ideal.Quotient.mk Q) n (z14 R j)=_
            rw [z20])
          (fun j=>by
            change eS (qS (i₁ (z14 V j)))∈maximalIdeal (z0 (R⧸Q) n)
            rw [show eS (qS (i₁ (z14 V j)))=z14 (R⧸Q) j from by
              change z15 (Ideal.Quotient.mk Q) n (i₁ (z14 V j))=_
              rw [z20,z20]]
            exact z18 j)
      exact fun r=>RingHom.congr_fun heq r
    exact z74 (RingEquiv.refl R) eS q30
  have q23:∀ q : ℕ,Subsingleton (z56 T S (T ⧸ Δ) (q+1)):=by
    have q27:(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q)=maximalIdeal R:=eq_maximalIdeal (comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    have q7:∀ j:Fin n,Ideal.Quotient.mk Q (z14 V j)∈maximalIdeal (R⧸Q):=fun j=>by
      change z14 V j∈(maximalIdeal (R⧸Q)).comap (Ideal.Quotient.mk Q);rw [q27];exact z18 j
    obtain ⟨eS_shift,heSs_C,_,heSs_symm_C,heSs_symm_var⟩:=z47 (R⧸Q) n (fun j=>Ideal.Quotient.mk Q (z14 V j)) q7
    have q6:∀ t:T,eS (qS (eT.symm t))=eS_shift.symm (eS (qS t)):=by
      have heq:(eS.toRingHom.comp qS).comp eT.symm.toRingHom=eS_shift.symm.toRingHom.comp (eS.toRingHom.comp qS):=by
        refine z45 (C:=R) (n:=n) _ _
          (fun r=>by
            simp only [RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingHom.coe_coe,heT_symm_C];change z15 (Ideal.Quotient.mk Q) n (z13 R n r)=eS_shift.symm (z15 (Ideal.Quotient.mk Q) n (z13 R n r))
            rw [z19,heSs_symm_C])
          (fun j=>by
            simp only [RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingHom.coe_coe,heT_symm_var,
              map_sub]
            change z15 (Ideal.Quotient.mk Q) n (z14 R j) -
                z15 (Ideal.Quotient.mk Q) n (z13 R n (z14 V j)) =
              eS_shift.symm (z15 (Ideal.Quotient.mk Q) n (z14 R j))
            rw [z20,z19,heSs_symm_var])
          (fun j=>by
            simp only [RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingHom.coe_coe,heT_symm_var,
              map_sub]
            change z15 (Ideal.Quotient.mk Q) n (z14 R j) -
                z15 (Ideal.Quotient.mk Q) n (z13 R n (z14 V j)) ∈
              maximalIdeal (z0 (R⧸Q) n)
            rw [z20,z19]
            exact (maximalIdeal (z0 (R⧸Q) n)).sub_mem (z18 j)
              (z17 n (q7 j)))
      exact fun t=>RingHom.congr_fun heq t
    have q0:∀ m : ℕ,(z124 R m).map (z15 (Ideal.Quotient.mk Q) m)=z124 (R⧸Q) m:=by
      intro m
      induction m with
      | zero=>rfl
      | succ m ihm =>
        simp only [z124,List.map_cons,List.map_map];congr 1
        · exact PowerSeries.map_X _
        · rw [← ihm,List.map_map]
          congr 1;funext x;change PowerSeries.map (z15 (Ideal.Quotient.mk Q) m) (PowerSeries.C x)=PowerSeries.C (z15 (Ideal.Quotient.mk Q) m x);exact PowerSeries.map_C (z15 (Ideal.Quotient.mk Q) m) x
    have hΔS_eq : Δ_list.map qS=(z124 (R⧸Q) n).map (eS_shift.symm.trans eS.symm):=by
      have h1:(z124 R n).map (fun t=>eS (qS (eT.symm t)))=(z124 (R⧸Q) n).map eS_shift.symm:=by
        rw [← q0 n,List.map_map]
        refine List.map_congr_left fun t _ => ?_
        exact q6 t
      calc Δ_list.map qS=(z124 R n).map (fun t=>eS.symm (eS (qS (eT.symm t)))):=by
            simp only [Δ_list,List.map_map];refine List.map_congr_left fun t _ => ?_;simp
        _=((z124 R n).map (fun t=>eS (qS (eT.symm t)))).map eS.symm:=by rw [List.map_map];rfl
        _=((z124 (R⧸Q) n).map eS_shift.symm).map eS.symm:=by rw [h1]
        _=(z124 (R⧸Q) n).map (eS_shift.symm.trans eS.symm):=by rw [List.map_map];rfl
    have q14:z110 S (Δ_list.map qS):=by
      rw [hΔS_eq]
      exact z129 (eS_shift.symm.trans eS.symm) (z124 (R⧸Q) n)
        (z131 (R⧸Q) n)
    have q13:z110 (R:=T) S Δ_list:=z130 Δ_list S q14;intro q;obtain ⟨e⟩:=z114 Δ_list hΔ_reg S (q+1);have : Subsingleton (z94 T S Δ_list (q+1)):=z111 Δ_list S q13 q;exact e.toEquiv.subsingleton
  have hi₁_loc:∀ r∈maximalIdeal R,i₁ r∈maximalIdeal T:=fun r hr =>
    z23 (fun c hc=>z17 n hc) n hr
  have q3:I ≤ maximalIdeal T:=by
    refine sup_le ?_ ?_
    · rw [map_le_iff_le_comap]
      intro r hr;exact hi₁_loc r (le_maximalIdeal ‹P.IsPrime›.ne_top hr)
    · rw [map_le_iff_le_comap]
      intro r hr;exact z17 n (le_maximalIdeal ‹Q.IsPrime›.ne_top hr)
  have q2:I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal T).ne_top q3;have : Nontrivial A:=Ideal.Quotient.nontrivial_iff.mpr q2;have : IsLocalRing A:=z36 I;have q1:(maximalIdeal A).comap qA=maximalIdeal T:=eq_maximalIdeal (comap_isMaximal_of_surjective qA Ideal.Quotient.mk_surjective)
  have q4:Surjective ((residue A).comp (qA.comp i₁)):=by
    intro y;obtain ⟨a,rfl⟩:=residue_surjective y;obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;obtain ⟨r,hr⟩:=z35 (C:=R) n (residue T t)
    refine ⟨r,?_⟩
    change residue A (qA (i₁ r))=residue A (qA t);rw [← sub_eq_zero,← map_sub,residue_eq_zero_iff,← map_sub,← mem_comap,q1]
    have q18:i₁ r - i₂ r∈maximalIdeal T:=by
      have hΔ_le : Δ ≤ maximalIdeal T:=by
        change ofList Δ_list ≤ maximalIdeal T;rw [ofList,span_le];intro w hw;rw [Set.mem_setOf_eq,List.mem_map] at hw;obtain ⟨v,hv,rfl⟩:=hw;have q22:v∈maximalIdeal T:=z127 R n v hv
        by_contra hnu
        have hu:IsUnit (eT.symm v):=by
          by_contra h;exact hnu ((mem_maximalIdeal (eT.symm v)).mpr h)
        have q33:IsUnit v:=by
          have:=hu.map eT.toRingHom;simpa using this
        exact (mem_maximalIdeal v).mp q22 q33
      exact hΔ_le (by rw [← hker_π,RingHom.mem_ker,map_sub,hπ_i₁,hπ_i₂,sub_self])
    have q24:i₂ r - t∈maximalIdeal T:=by
      rw [← residue_eq_zero_iff,map_sub];change ((residue T).comp (z13 R n)) r - residue T t=0;rw [hr,sub_self]
    have : i₁ r - t=(i₁ r - i₂ r)+(i₂ r - t):=by ring
    rw [this];exact (maximalIdeal T).add_mem q18 q24
  let Δ_A:List A := Δ_list.map qA
  have hΔ_A_len : Δ_A.length=n:=by simp [Δ_A,Δ_list,z125]
  have hΔ_A_max:∀ z ∈ Δ_A,z∈maximalIdeal A:=fun z hz=>by
    rw [List.mem_map] at hz;obtain ⟨w,hw,rfl⟩:=hz;rw [List.mem_map] at hw;obtain ⟨v,hv,rfl⟩:=hw;have q22:v∈maximalIdeal T:=z127 R n v hv
    have q21:eT.symm v∈maximalIdeal T:=by
      by_contra hnu
      have hu:IsUnit (eT.symm v):=by
        by_contra h;exact hnu ((mem_maximalIdeal (eT.symm v)).mpr h)
      have q33:IsUnit v:=by
        have:=hu.map eT.toRingHom;simpa using this
      exact (mem_maximalIdeal v).mp q22 q33
    change eT.symm v∈(maximalIdeal A).comap qA;rw [q1];exact q21
  have hΔ_A_rad:(annihilator A A⊔ofList Δ_A).radical=maximalIdeal A:=by
    have q26:annihilator A A = ⊥ := by
      ext a;simp only [Module.mem_annihilator,Ideal.mem_bot]
      exact ⟨fun h=>by simpa using h 1,fun h x=>by rw [h,zero_smul]⟩
    rw [q26,bot_sup_eq]
    refine le_antisymm ?_ ?_
    · rw [(maximalIdeal.isMaximal A).isPrime.radical_le_iff,ofList,span_le]
      exact fun z hz=>hΔ_A_max z hz
    · intro a ha
      obtain ⟨t,rfl⟩:=Ideal.Quotient.mk_surjective a;have q20:t∈maximalIdeal T:=q1▸ha
      have hπt_max : π t∈maximalIdeal R:=by
        have q17:eT t∈maximalIdeal T:=by
          by_contra hnu
          have hu:IsUnit (eT t):=by
            by_contra h;exact hnu ((mem_maximalIdeal (eT t)).mpr h)
          have q31:IsUnit t:=by
            have:=hu.map eT.symm.toRingHom;simpa using this
          exact (mem_maximalIdeal t).mp q20 q31
        have q15:∀ m : ℕ,∀ f∈maximalIdeal (z0 R m),z48 R m f∈maximalIdeal R:=by
          intro m
          induction m with
          | zero=>exact fun f hf=>hf
          | succ m ihm =>
            intro f hf;exact ihm (PowerSeries.constantCoeff f) ((z3 f).mp hf)
        exact q15 n (eT t) q17
      rw [← hPQ] at hπt_max;obtain ⟨k,hk⟩:=hπt_max;rw [Submodule.mem_sup] at hk;obtain ⟨p',hp',q',hq',hpq⟩:=hk;let d:T:=t ^ k - (i₁ p'+i₂ q')
      have q19:d ∈ Δ := by
        rw [← hker_π,RingHom.mem_ker];dsimp only [d];rw [map_sub,map_add,map_pow,hπ_i₁,hπ_i₂,← hpq,sub_self]
      have hmap_Δ : ofList Δ_A = Δ.map qA:=by
        change ofList Δ_A=(ofList Δ_list).map qA;rw [ofList,ofList,map_span];congr 1;ext y;simp [Δ_A]
      refine ⟨k,?_⟩
      rw [hmap_Δ,← map_pow]
      have q35:qA (t ^ k)=qA d:=by
        dsimp only [d];rw [map_sub,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr (mem_sup_left (mem_map_of_mem i₁ hp')),Ideal.Quotient.eq_zero_iff_mem.mpr (mem_sup_right (mem_map_of_mem i₂ hq')),add_zero,sub_zero]
      rw [q35];exact mem_map_of_mem qA q19
  have hQ₂_le:Q.map i₂ ≤ RingHom.ker ((Ideal.Quotient.mk Q).comp π):=by
    rw [map_le_iff_le_comap];intro q hq;rw [mem_comap,RingHom.mem_ker,RingHom.comp_apply,hπ_i₂];exact Ideal.Quotient.eq_zero_iff_mem.mpr hq
  have q11:∀ q∈Q,∃ d∈ofList Δ_list,qS (i₁ q)=qS d:=fun q hq =>
    ⟨i₁ q - i₂ q,by change i₁ q - i₂ q ∈ Δ;rw [← hker_π,RingHom.mem_ker,map_sub,hπ_i₁,hπ_i₂,sub_self],by
      rw [map_sub,Ideal.Quotient.eq_zero_iff_mem.mpr (mem_map_of_mem i₂ hq),sub_zero]⟩
  have q16:∀ i : ℕ,Module.length R (z56 R (R⧸P) (R⧸Q) i)=Module.length A (z94 A A Δ_A i) :=
    @z147 R T _ _ _ _ _ _ i₁.toAlgebra P Q (Q.map i₂) I rfl ‹IsLocalRing A›
      Δ_list π hπ_i₁ hker_π hQ₂_le q11 hΔ_reg q5 q23 hi₁_loc q4
  obtain ⟨_,_,hchi_pos⟩:=z123 Δ_A hΔ_A_max A (Or.inl hΔ_A_rad)
  have q9:supportDim A A=(Δ_A.length:WithBot ℕ∞):=by
    rw [hΔ_A_len,Module.supportDim_self_eq_ringKrullDim,q28]
  have q34:0 < z115 A A Δ_A:=hchi_pos q9
  have q10:intersectionMultiplicity R (R⧸P) (R⧸Q)=z115 A A Δ_A:=by
    unfold intersectionMultiplicity z115;rw [hΔ_A_len]
    rw [finsum_eq_sum_of_support_subset _ (s:=Finset.range (n+1))]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [q16 i]
    · intro i hi
      simp only [Function.mem_support,ne_eq] at hi;rw [Finset.coe_range,Set.mem_Iio]
      by_contra hge
      push Not at hge
      have hgt : Δ_A.length < i:=by omega
      have : Subsingleton (z94 A A Δ_A i):=z95 Δ_A i hgt
      have h0:Module.length R (z56 R (R⧸P) (R⧸Q) i)=0:=by
        rw [q16 i,Module.length_eq_zero]
      exact hi (by rw [h0];simp)
  rw [q10];exact q34
lemma z149 {V:Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (maximalIdeal V) V] (p:V) (hp:maximalIdeal V=span {p})
  (n : ℕ) (P Q:Ideal (z0 V n)) [P.IsPrime] [Q.IsPrime]
  (hPQ:(P⊔Q).radical=maximalIdeal (z0 V n)) :
  ringKrullDim (z0 V n⧸P)+ringKrullDim (z0 V n⧸Q) ≤
   ringKrullDim (z0 V n) ∧
  (ringKrullDim (z0 V n⧸P)+ringKrullDim (z0 V n⧸Q) =
   ringKrullDim (z0 V n) →
   0 < intersectionMultiplicity (z0 V n)
    (z0 V n⧸P) (z0 V n⧸Q)):=by
 have h1:=z55 p hp n P Q hPQ
 refine ⟨h1.1,fun heq => ?_⟩
 obtain ⟨hor,hdimA⟩:=h1.2 heq
 rcases hor with hpP | hpQ
 ·
  have hQP:(Q⊔P).radical=maximalIdeal (z0 V n):=by rwa [sup_comm]
  have heq':ringKrullDim (z0 V n⧸Q)+ringKrullDim (z0 V n⧸P) =
    ringKrullDim (z0 V n):=by rw [add_comm];exact heq
  have hdimA':=((z55 p hp n Q P hQP).2 heq').2;rw [z72];exact z148 p hp n Q P hQP hpP hdimA'
 · exact z148 p hp n P Q hPQ hpQ hdimA
end DiagonalTorAndPositivity
end OMA.H2Proof
namespace OMA.H2Proof
section PBasis
variable (k:Type) [Field k] (p : ℕ) [hp:Fact p.Prime] [CharP k p]
def z150 (s:Set k) (n : ℕ) : Type :=
 { e:s →₀ ℕ // ∀ b:s,e b < p ^ n }
def z151 {s:Set k} {n : ℕ} (e:z150 k p s n) : k:=e.1.prod (fun b m=>(b:k) ^ m)
def z152 (s:Set k) : Prop :=
 ∀ f:z150 k p s 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=0→f=0
lemma z153 :
    ∃ B:Set k,z152 k p B ∧
      ∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x:=by
  classical
  have q40:∃ B:Set k,Maximal (z152 k p) B:=by
    refine zorn_subset { s:Set k | z152 k p s } fun c hc hchain => ?_
    refine ⟨⋃₀ c,?_,fun s hs=>Set.subset_sUnion_of_mem hs⟩
    intro f hf
    rcases Set.eq_empty_or_nonempty c with rfl | ⟨s0,hs0⟩
    · ext e
      have he0:e.1=0:=by
        ext u;exact False.elim (by simpa using u.2)
      have q43:∀ e':z150 k p (⋃₀ (∅ : Set (Set k))) 1,e'=e:=fun e'=>by
        apply Subtype.ext;ext u;exact False.elim (by simpa using u.2)
      have q58:f.sum (fun e' c=>c ^ p*z151 k p e')=f e ^ p:=by
        by_cases hfe:f e=0
        · have hf0:f=0:=by
            ext e';rw [q43 e',hfe];rfl
          simp [hf0,hp.out.ne_zero]
        · have q50:f.support = {e}:=by
            ext e';simp [q43 e',hfe]
          rw [Finsupp.sum,q50,Finset.sum_singleton]
          have hmv:z151 k p e=1:=by
            simp [z151,he0]
          rw [hmv,mul_one]
      rw [q58] at hf;exact eq_zero_of_pow_eq_zero hf
    · let U:Finset (↥(⋃₀ c)):=f.support.biUnion fun e=>e.1.support
      have hU':∃ s∈c,∀ u∈U,(u:k)∈s:=by
        refine Finset.induction_on U ⟨s0,hs0,by simp⟩ ?_
        intro u U' _ ⟨s1,hs1,hU1⟩;obtain ⟨s2,hs2,hus2⟩:=Set.mem_sUnion.mp u.2
        rcases hchain.total hs1 hs2 with h12 | h21
        · refine ⟨s2,hs2,fun v hv => ?_⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact hus2
          · exact h12 (hU1 v hv')
        · refine ⟨s1,hs1,fun v hv => ?_⟩
          rcases Finset.mem_insert.mp hv with rfl | hv'
          · exact h21 hus2
          · exact hU1 v hv'
      obtain ⟨s,hsc,hsU⟩:=hU'
      let emb:z150 k p s 1→z150 k p (⋃₀ c) 1:=fun e =>
        ⟨e.1.mapDomain (Set.inclusion (Set.subset_sUnion_of_mem hsc)),fun u=>by
          by_cases hu:∃ v:s,(v:k)=(u:k)
          · obtain ⟨v,hv⟩:=hu
            have q47:u=Set.inclusion (Set.subset_sUnion_of_mem hsc) v:=Subtype.ext hv.symm;rw [q47,Finsupp.mapDomain_apply (Set.inclusion_injective _)];exact e.2 v
          · have q45:(e.1.mapDomain (Set.inclusion (Set.subset_sUnion_of_mem hsc))) u=0:=by
              rw [Finsupp.mapDomain_of_notMem_range];rintro ⟨v,hv⟩;exact hu ⟨v,congrArg Subtype.val hv⟩
            rw [q45]
            exact pow_pos hp.out.pos 1⟩
      have q10:Injective emb:=by
        intro e1 e2 heq;apply Subtype.ext;have q56:=congrArg Subtype.val heq;exact Finsupp.mapDomain_injective (Set.inclusion_injective _) q56
      have q14:∀ e:z150 k p s 1,z151 k p (emb e)=z151 k p e:=fun e=>by
        simp only [z151,emb];rw [Finsupp.prod_mapDomain_index_inj (Set.inclusion_injective _)]
      have q11:∀ e∈f.support,∃ e':z150 k p s 1,emb e'=e:=by
        intro e he
        let e':s →₀ ℕ := e.1.comapDomain (Set.inclusion (Set.subset_sUnion_of_mem hsc))
          (Set.inclusion_injective _).injOn
        have q27:∀ v:s,e' v < p ^ 1:=fun v=>by
          simp only [e',Finsupp.comapDomain_apply];exact e.2 _
        refine ⟨⟨e',q27⟩,?_⟩
        apply Subtype.ext;ext u
        by_cases hu:u∈e.1.support
        · have hus:(u:k)∈s:=hsU u (Finset.mem_biUnion.mpr ⟨e,he,hu⟩)
          have q47:u=Set.inclusion (Set.subset_sUnion_of_mem hsc) ⟨u.1,hus⟩:=rfl
          conv_lhs=>rw [q47]
          rw [Finsupp.mapDomain_apply (Set.inclusion_injective _)];simp [e']
        · have hu0:e.1 u=0:=Finsupp.notMem_support_iff.mp hu
          rw [hu0]
          by_cases hus:(u:k)∈s
          · have q47:u=Set.inclusion (Set.subset_sUnion_of_mem hsc) ⟨u.1,hus⟩:=rfl
            conv_lhs=>rw [q47]
            rw [Finsupp.mapDomain_apply (Set.inclusion_injective _)];simp [e',hu0]
          · rw [Finsupp.mapDomain_of_notMem_range]
            rintro ⟨v,hv⟩;exact hus (congrArg Subtype.val hv▸v.2)
      let g:z150 k p s 1 →₀ k:=f.comapDomain emb q10.injOn
      have q36:g.sum (fun e c=>c ^ p*z151 k p e)=f.sum (fun e c=>c ^ p*z151 k p e):=by
        rw [Finsupp.sum,Finsupp.sum]
        refine Finset.sum_bij (fun e _=>emb e) ?_ ?_ ?_ ?_
        · intro e he
          rw [Finsupp.mem_support_iff] at he ⊢;simpa [g] using he
        · intro e1 _ e2 _ h
          exact q10 h
        · intro e he
          obtain ⟨e',rfl⟩:=q11 e he
          refine ⟨e',?_,rfl⟩
          rw [Finsupp.mem_support_iff] at he ⊢;simpa [g] using he
        · intro e _
          simp [g,q14]
      have hg0:g=0:=hc hsc g (q36.trans hf);ext e
      by_cases he:e∈f.support
      · obtain ⟨e',rfl⟩:=q11 e he
        have : g e'=0:=by simp [hg0]
        simpa [g] using this
      · exact Finsupp.notMem_support_iff.mp he
  obtain ⟨B,hBmax⟩:=q40;have q24:z152 k p B:=hBmax.prop
  let Lset:Set k:={ x:k | ∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x }
  have q22:(0:k)∈Lset:=⟨0,by simp⟩
  have q28:(1:k)∈Lset:=by
    let e0:z150 k p B 1:=⟨0,fun _=>pow_pos hp.out.pos 1⟩
    refine ⟨Finsupp.single e0 1,?_⟩
    rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])];simp [e0,z151]
  have q31:∀ x y,x∈Lset→y∈Lset→x+y∈Lset:=by
    rintro x y ⟨fx,rfl⟩ ⟨fy,rfl⟩
    refine ⟨fx+fy,?_⟩
    rw [Finsupp.sum_add_index']
    · intro e;simp [zero_pow hp.out.ne_zero]
    · intro e a b
      rw [add_pow_char a b,add_mul]
  have q26:∀ x,x∈Lset → -x∈Lset:=by
    rintro x ⟨fx,rfl⟩
    refine ⟨-fx,?_⟩
    have q58:(-fx).sum (fun e c=>c ^ p*z151 k p e)+fx.sum (fun e c=>c ^ p*z151 k p e)=0:=by
      rw [← Finsupp.sum_add_index']
      · simp
      · intro e;simp [zero_pow hp.out.ne_zero]
      · intro e a b;rw [add_pow_char a b,add_mul]
    exact eq_neg_of_add_eq_zero_left q58
  have q1:∀ (c1 c2:k) (e1 e2:z150 k p B 1),(c1 ^ p*z151 k p e1)*(c2 ^ p*z151 k p e2)∈Lset:=by
    intro c1 c2 e1 e2;let e:B →₀ ℕ := e1.1+e2.1;let q:B →₀ ℕ := e.mapRange (· / p) (Nat.zero_div p);let r:B →₀ ℕ := e.mapRange (· % p) (Nat.zero_mod p)
    have q49:∀ b:B,r b < p ^ 1:=fun b=>by
      simp only [r,Finsupp.mapRange_apply,pow_one];exact Nat.mod_lt _ hp.out.pos
    have q41:e=p•q+r:=by
      ext b;simp only [q,r,Finsupp.add_apply,Finsupp.smul_apply,Finsupp.mapRange_apply,smul_eq_mul];exact (Nat.div_add_mod (e b) p).symm
    let rM:z150 k p B 1:=⟨r,q49⟩
    let q52:k:=q.prod (fun b m=>(b:k) ^ m)
    have q12:z151 k p e1*z151 k p e2=q52 ^ p*z151 k p rM:=by
      have h1:z151 k p e1*z151 k p e2=e.prod (fun b m=>(b:k) ^ m):=by
        simp only [z151,e]
        rw [Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)]
      rw [h1,q41,Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)]
      congr 1;simp only [q52,Finsupp.prod]
      have q50:(p•q).support=q.support:=by
        ext b;simp [hp.out.ne_zero]
      rw [q50,← Finset.prod_pow]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Finsupp.smul_apply,smul_eq_mul];rw [mul_comm,pow_mul]
    refine ⟨Finsupp.single rM (c1*c2*q52),?_⟩
    rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])]
    calc (c1*c2*q52) ^ p*z151 k p rM
        = c1 ^ p*c2 ^ p*(q52 ^ p*z151 k p rM):=by ring
      _=c1 ^ p*c2 ^ p*(z151 k p e1*z151 k p e2):=by rw [q12]
      _=(c1 ^ p*z151 k p e1)*(c2 ^ p*z151 k p e2):=by ring
  have q15:∀ {ι : Type} (s:Finset ι) (g : ι → k),(∀ i∈s,g i∈Lset) → ∑ i∈s,g i∈Lset:=by
    intro ι s g
    refine Finset.induction_on s (fun _=>q22) ?_
    intro a s' ha ih hg;rw [Finset.sum_insert ha]
    exact q31 _ _ (hg a (Finset.mem_insert_self a s'))
      (ih fun i hi=>hg i (Finset.mem_insert_of_mem hi))
  have q35:∀ x y,x∈Lset→y∈Lset→x*y∈Lset:=by
    rintro x y ⟨fx,rfl⟩ ⟨fy,rfl⟩;rw [Finsupp.sum,Finsupp.sum,Finset.sum_mul]
    refine q15 fx.support _ fun e1 _ => ?_
    rw [Finset.mul_sum]
    exact q15 fy.support _ fun e2 _=>q1 _ _ e1 e2
  have q7:∀ (c:k) {x:k},x∈Lset→c ^ p*x∈Lset:=by
    rintro c x ⟨fx,rfl⟩
    refine ⟨c•fx,?_⟩
    rw [Finsupp.sum,Finsupp.sum,Finset.mul_sum]
    by_cases hc:c=0
    · simp [hc,zero_pow hp.out.ne_zero]
    · have q50:(c•fx).support=fx.support:=by
        ext e;simp [hc]
      rw [q50]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp [mul_pow,mul_assoc]
  have q25:∀ {x:k},x∈Lset→∀ m : ℕ,x ^ m∈Lset:=by
    intro x hx m
    induction m with
    | zero=>simpa using q28
    | succ m ih=>rw [pow_succ];exact q35 _ _ ih hx
  have q38:∀ x,x∈Lset→x⁻¹ ∈ Lset:=by
    intro x hx
    by_cases hx0:x=0
    · simp [hx0,q22]
    · have heq:(x⁻¹) ^ p*x ^ (p - 1)=x⁻¹ := by
        have hp1:1 ≤ p:=hp.out.one_le
        calc (x⁻¹) ^ p*x ^ (p - 1)
            = x⁻¹ * (x⁻¹) ^ (p - 1)*x ^ (p - 1):=by
              rw [← pow_succ',Nat.sub_add_cancel hp1]
          _=x⁻¹ * ((x⁻¹ * x) ^ (p - 1)):=by rw [mul_assoc,← mul_pow]
          _=x⁻¹ := by rw [inv_mul_cancel₀ hx0,one_pow,mul_one]
      rw [← heq];exact q7 x⁻¹ (q25 hx (p - 1))
  let L:Subfield k :=
    { carrier:=Lset
      zero_mem':=q22
      one_mem':=q28
      add_mem':=fun hx hy=>q31 _ _ hx hy
      neg_mem':=fun hx=>q26 _ hx
      mul_mem':=fun hx hy=>q35 _ _ hx hy
      inv_mem':=fun {_} hx=>q38 _ hx }
  refine ⟨B,q24,fun a => ?_⟩
  by_contra ha_not
  have q17:a∉L:=ha_not
  have q20:a∉B:=by
    intro haB;apply q17
    let e:z150 k p B 1:=⟨Finsupp.single ⟨a,haB⟩ 1,fun b=>by
      by_cases h:b=⟨a,haB⟩
      · subst h;simp [hp.out.one_lt]
      · simp [Finsupp.single_eq_of_ne h,hp.out.pos]⟩
    refine ⟨Finsupp.single e 1,?_⟩
    rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])];simp [e,z151,Finsupp.prod_single_index]
  have q8:a ^ p∈L:=by
    show a ^ p∈Lset
    have : a ^ p*(1:k)∈Lset:=q7 a q28;simpa using this
  have q34:∀ g:Fin p→L,(∑ i:Fin p,(g i:k)*a ^ (i : ℕ))=0→∀ i,g i=0:=by
    intro g hg
    by_contra hne
    push Not at hne
    let P:Polynomial L := ∑ i:Fin p,Polynomial.C (g i)*Polynomial.X ^ (i : ℕ)
    have q13:∀ i:Fin p,P.coeff (i : ℕ)=g i:=fun i=>by
      simp only [P,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow];rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have : (i : ℕ)≠(j : ℕ):=fun h=>hji (Fin.ext h.symm)
        simp [this]
      · intro hi;exact absurd (Finset.mem_univ i) hi
    have q42:P≠0:=by
      obtain ⟨i,hi⟩:=hne;intro h0;have:=q13 i;rw [h0,Polynomial.coeff_zero] at this;exact hi this.symm
    have q32:P.natDegree < p:=by
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
      change Finset.univ.sup (fun i:Fin p=>(Polynomial.C (g i)*Polynomial.X ^ (i : ℕ)).natDegree) < p
      rw [Finset.sup_lt_iff hp.out.pos];intro i _;exact lt_of_le_of_lt (Polynomial.natDegree_C_mul_X_pow_le _ _) i.2
    have q18:Polynomial.aeval a P=0:=by
      simp only [P,map_sum,map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X];exact hg
    have q29:IsIntegral L a:=by
      refine ⟨Polynomial.X ^ p - Polynomial.C ⟨a ^ p,q8⟩,?_,?_⟩
      · exact Polynomial.monic_X_pow_sub_C _ hp.out.ne_zero
      · rw [Polynomial.eval₂_sub,Polynomial.eval₂_X_pow,Polynomial.eval₂_C]
        exact sub_self (a ^ p)
    let μ : Polynomial L:=minpoly L a;have hμ_monic : μ.Monic:=minpoly.monic q29;have hμ_dvd_P : μ ∣ P:=minpoly.dvd L a q18;have hμ_deg_lt : μ.natDegree < p:=lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hμ_dvd_P q42) q32
    have hμ_dvd_Xp : μ ∣ Polynomial.X ^ p - Polynomial.C ⟨a ^ p,q8⟩ :=
      minpoly.dvd L a (by
        rw [map_sub,map_pow,Polynomial.aeval_X,Polynomial.aeval_C]
        exact sub_self (a ^ p))
    have hμ_map_dvd : μ.map (algebraMap L k)∣(Polynomial.X - Polynomial.C a) ^ p:=by
      have h1:=Polynomial.map_dvd (algebraMap L k) hμ_dvd_Xp
      have h2:(Polynomial.X ^ p - Polynomial.C ⟨a ^ p,q8⟩ : Polynomial L).map
          (algebraMap L k)=(Polynomial.X - Polynomial.C a) ^ p:=by
        rw [Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C];change Polynomial.X ^ p - Polynomial.C (a ^ p)=(Polynomial.X - Polynomial.C a) ^ p;rw [sub_pow_char,map_pow]
      exact h2▸h1
    have hμ_deg_pos:0 < μ.natDegree:=minpoly.natDegree_pos q29;have q0:Prime (Polynomial.X - Polynomial.C a:Polynomial k):=(Polynomial.irreducible_X_sub_C a).prime;obtain ⟨m,hm_le,hassoc⟩:=(dvd_prime_pow q0 p).mp hμ_map_dvd;have hμ_map_monic:(μ.map (algebraMap L k)).Monic:=hμ_monic.map _
    have q6:((Polynomial.X - Polynomial.C a:Polynomial k) ^ m).Monic:=(Polynomial.monic_X_sub_C a).pow m;have hμ_map_eq : μ.map (algebraMap L k)=(Polynomial.X - Polynomial.C a) ^ m:=Polynomial.eq_of_monic_of_associated hμ_map_monic q6 hassoc
    have q39:m = μ.natDegree:=by
      have q60:=congrArg Polynomial.natDegree hμ_map_eq;rw [hμ_monic.natDegree_map,Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at q60;exact q60.symm
    have q30:0 < m:=q39▸hμ_deg_pos;have hm_lt:m < p:=q39▸hμ_deg_lt
    have q37:((Polynomial.X - Polynomial.C a:Polynomial k) ^ m).coeff (m - 1) = -(m:k)*a:=by
      rw [sub_eq_add_neg,add_pow,Polynomial.finsetSum_coeff];rw [Finset.sum_eq_single (m - 1)]
      · have h1:m - (m - 1)=1:=by omega
        rw [h1,pow_one,← Polynomial.C_neg,Polynomial.coeff_mul_natCast,Polynomial.coeff_mul_C,Polynomial.coeff_X_pow_self]
        have q23:m.choose (m - 1)=m:=by
          rw [← Nat.choose_symm (by omega),h1,Nat.choose_one_right]
        rw [q23];ring
      · intro j hj hne_j
        rw [Finset.mem_range] at hj;rw [← Polynomial.C_neg,← map_pow,Polynomial.coeff_mul_natCast,Polynomial.coeff_mul_C,Polynomial.coeff_X_pow,if_neg (Ne.symm hne_j)];simp
      · intro q54
        exact absurd (Finset.mem_range.mpr (by omega)) q54
    have q16:(μ.coeff (m - 1) : k) = -(m:k)*a:=by
      rw [← q37,← hμ_map_eq,Polynomial.coeff_map];rfl
    have q33:(m:k)≠0:=by
      intro h0;have q55:p∣m:=(CharP.cast_eq_zero_iff k p m).mp h0;have hle:p ≤ m:=Nat.le_of_dvd q30 q55;omega
    have q44:a = -((m:k)⁻¹ * (μ.coeff (m - 1) : k)):=by
      rw [q16]
      field_simp [q33]
    have haL:a∈L:=by
      rw [q44];exact L.neg_mem (L.mul_mem (L.inv_mem (natCast_mem L m)) (μ.coeff (m - 1)).2)
    exact q17 haL
  have q59:z152 k p (insert a B):=by
    intro f hf;let q57 : ↥(insert a B):=⟨a,Set.mem_insert a B⟩
    let q46:z150 k p (insert a B) 1→Fin p×z150 k p B 1:=fun e =>
      (⟨e.1 q57,by simpa using e.2 q57⟩,
       ⟨e.1.comapDomain (Set.inclusion (Set.subset_insert a B)) (Set.inclusion_injective _).injOn,
        fun b=>by
          simp only [Finsupp.comapDomain_apply]
          exact e.2 _⟩)
    have q5:Injective q46:=by
      intro e1 e2 h
      have h1:e1.1 q57=e2.1 q57:=congrArg (fun x=>x.1.1) h
      have h2:∀ b:B,e1.1 ⟨b.1,Set.mem_insert_of_mem a b.2⟩=e2.1 ⟨b.1,Set.mem_insert_of_mem a b.2⟩:=fun b=>by
        have:=congrArg (fun x=>x.2.1 b) h
        simpa [q46] using this
      apply Subtype.ext;ext u
      rcases Set.mem_insert_iff.mp u.2 with hu | hu
      · have : u=q57:=Subtype.ext hu
        rw [this,h1]
      · exact h2 ⟨u.1,hu⟩
    have q3:∀ e:z150 k p (insert a B) 1,z151 k p e=z151 k p (q46 e).2*a ^ ((q46 e).1 : ℕ):=fun e=>by
      simp only [z151,q46]
      have q50:(e.1.comapDomain (Set.inclusion (Set.subset_insert a B))
          (Set.inclusion_injective _).injOn).prod (fun b m=>(b:k) ^ m)*a ^ e.1 q57 =
          e.1.prod (fun u m=>(u:k) ^ m):=by
        rw [Finsupp.prod,Finsupp.prod]
        by_cases ha0:e.1 q57=0
        · rw [ha0,pow_zero,mul_one]
          refine Finset.prod_bij (fun b _=>Set.inclusion (Set.subset_insert a B) b) ?_ ?_ ?_ ?_
          · intro b hb
            rw [Finsupp.mem_support_iff] at hb ⊢;simpa using hb
          · intro b1 _ b2 _ h
            exact Set.inclusion_injective _ h
          · intro u hu
            have hne:u≠q57:=fun h=>by
              rw [Finsupp.mem_support_iff,h] at hu;exact hu ha0
            have huB:u.1∈B:=(Set.mem_insert_iff.mp u.2).resolve_left fun h=>hne (Subtype.ext h)
            refine ⟨⟨u.1,huB⟩,?_,rfl⟩
            rw [Finsupp.mem_support_iff] at hu ⊢;simpa using hu
          · intro b _;rfl
        · have q53:q57∈e.1.support:=Finsupp.mem_support_iff.mpr ha0
          rw [← Finset.prod_erase_mul e.1.support _ q53];congr 1
          refine Finset.prod_bij (fun b _=>Set.inclusion (Set.subset_insert a B) b) ?_ ?_ ?_ ?_
          · intro b hb
            rw [Finset.mem_erase,Finsupp.mem_support_iff]
            refine ⟨fun h=>q20 (by
              have hv:b.1=a:=congrArg Subtype.val h
              exact hv▸b.2),?_⟩
            rw [Finsupp.mem_support_iff] at hb;simpa using hb
          · intro b1 _ b2 _ h
            exact Set.inclusion_injective _ h
          · intro u hu
            rw [Finset.mem_erase,Finsupp.mem_support_iff] at hu
            have huB:u.1∈B:=(Set.mem_insert_iff.mp u.2).resolve_left fun h=>hu.1 (Subtype.ext h)
            refine ⟨⟨u.1,huB⟩,?_,rfl⟩
            rw [Finsupp.mem_support_iff];simpa using hu.2
          · intro b _;rfl
      exact q50.symm
    let q48:Fin p→z150 k p B 1 →₀ k:=fun i =>
      f.sum fun e c=>if (q46 e).1=i then Finsupp.single (q46 e).2 c else 0
    have q4:∀ i:Fin p,(q48 i).sum (fun e' c=>c ^ p*z151 k p e')=f.sum (fun e c=>if (q46 e).1=i then c ^ p*z151 k p (q46 e).2 else 0):=by
      intro i;dsimp only [q48];rw [Finsupp.sum_sum_index]
      · refine Finsupp.sum_congr fun e _ => ?_
        split_ifs
        · rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])]
        · simp
      · intro e';simp [zero_pow hp.out.ne_zero]
      · intro e' c1 c2;rw [add_pow_char c1 c2,add_mul]
    have q19 : ∑ i:Fin p,((q48 i).sum (fun e' c=>c ^ p*z151 k p e'))*a ^ (i : ℕ)=f.sum (fun e c=>c ^ p*z151 k p e):=by
      simp_rw [q4,Finsupp.sum,Finset.sum_mul];rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_eq_single (q46 e).1]
      · simp [q3 e,mul_assoc]
      · intro i _ hi
        simp [Ne.symm hi]
      · intro hi;exact absurd (Finset.mem_univ _) hi
    let gL:Fin p→L:=fun i=>⟨(q48 i).sum (fun e' c=>c ^ p*z151 k p e'),⟨q48 i,rfl⟩⟩
    have q21 : ∑ i:Fin p,(gL i:k)*a ^ (i : ℕ)=0:=q19.trans hf;have q9:∀ i:Fin p,gL i=0:=q34 gL q21
    have q2:∀ i:Fin p,q48 i=0:=fun i =>
      q24 (q48 i) (congrArg Subtype.val (q9 i))
    ext e
    have hfe:q48 (q46 e).1 (q46 e).2=f e:=by
      dsimp only [q48];rw [Finsupp.sum_apply,Finsupp.sum]
      by_cases q53:e∈f.support
      · rw [Finset.sum_eq_single e]
        · simp
        · intro e' _ hne
          split_ifs with h1
          · rw [Finsupp.single_apply,if_neg]
            intro h2;exact hne (q5 (Prod.ext h1 h2))
          · rfl
        · intro h;exact absurd q53 h
      · have hf0:f e=0:=Finsupp.notMem_support_iff.mp q53
        rw [hf0]
        refine Finset.sum_eq_zero fun e' he' => ?_
        have hne:e'≠e:=fun h=>q53 (h▸he')
        split_ifs with h1
        · rw [Finsupp.single_apply,if_neg]
          intro h2;exact hne (q5 (Prod.ext h1 h2))
        · rfl
    rw [← hfe,q2];rfl
  have q51:insert a B⊆B:=hBmax.le_of_ge q59 (Set.subset_insert a B);exact q20 (q51 (Set.mem_insert a B))
lemma z154 {B:Set k} (q5:z152 k p B)
    (q8:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x) :
    ∀ n : ℕ,
      (∀ f:z150 k p B n →₀ k,f.sum (fun e c=>c ^ (p ^ n)*z151 k p e)=0→f=0) ∧
      (∀ x:k,∃ f:z150 k p B n →₀ k,f.sum (fun e c=>c ^ (p ^ n)*z151 k p e)=x):=by
  classical
  intro n
  induction n with
  | zero =>
    constructor
    · intro f hf
      ext e
      have he0:e.1=0:=by
        ext b;have:=e.2 b;simp at this;exact this
      have q13:∀ e':z150 k p B 0,e'=e:=fun e'=>by
        apply Subtype.ext;ext b;have h1:=e'.2 b;have h2:=e.2 b;simp at h1 h2;omega
      have q14:f.sum (fun e' c=>c ^ (p ^ 0)*z151 k p e')=f e:=by
        by_cases hfe:f e=0
        · have hf0:f=0:=by ext e';rw [q13 e',hfe];rfl
          simp [hf0]
        · have q12:f.support = {e}:=by ext e';simp [q13 e',hfe]
          rw [Finsupp.sum,q12,Finset.sum_singleton];simp [z151,he0]
      exact q14.symm.trans hf
    · intro x
      let e0:z150 k p B 0:=⟨0,fun _=>by simp⟩
      refine ⟨Finsupp.single e0 x,?_⟩
      rw [Finsupp.sum_single_index (by simp)];simp [e0,z151]
  | succ n ih =>
    let q7:z150 k p B (n+1)→z150 k p B 1×z150 k p B n:=fun e =>
      (⟨e.1.mapRange (· % p) (Nat.zero_mod p),fun b=>by
          simp only [Finsupp.mapRange_apply,pow_one]
          exact Nat.mod_lt _ hp.out.pos⟩,
       ⟨e.1.mapRange (· / p) (Nat.zero_div p),fun b=>by
          simp only [Finsupp.mapRange_apply]
          exact Nat.div_lt_of_lt_mul (by simpa [pow_succ'] using e.2 b)⟩)
    let q6:z150 k p B 1×z150 k p B n→z150 k p B (n+1):=fun ⟨r,q⟩ =>
      ⟨r.1+p•q.1,fun b=>by
        simp only [Finsupp.add_apply,Finsupp.smul_apply,smul_eq_mul]
        have hr:r.1 b < p:=by simpa using r.2 b
        have hq:q.1 b < p ^ n:=q.2 b
        calc r.1 b+p*q.1 b
            < p+p*q.1 b:=Nat.add_lt_add_right hr _
          _=p*(q.1 b+1):=by ring
          _ ≤ p*p ^ n:=Nat.mul_le_mul_left p hq
          _=p ^ (n+1):=(pow_succ' p n).symm⟩
    have hlr:∀ e,q6 (q7 e)=e:=fun e=>by
      apply Subtype.ext;ext b;simp only [q7,q6,Finsupp.add_apply,Finsupp.smul_apply,Finsupp.mapRange_apply,smul_eq_mul];rw [add_comm];exact Nat.div_add_mod (e.1 b) p
    have q0:∀ r q,z151 k p (q6 (r,q))=z151 k p r*(z151 k p q) ^ p:=fun r q=>by
      simp only [z151,q6]
      rw [Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)]
      congr 1;simp only [Finsupp.prod]
      have q12:(p•q.1).support=q.1.support:=by
        ext b;simp [hp.out.ne_zero]
      rw [q12,← Finset.prod_pow]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Finsupp.smul_apply,smul_eq_mul];rw [mul_comm,pow_mul]
    constructor
    · intro f hf
      let q9:z150 k p B 1→z150 k p B n →₀ k:=fun r =>
        f.sum fun e c=>if (q7 e).1=r then Finsupp.single (q7 e).2 c else 0
      let q11:z150 k p B 1 →₀ k:=f.sum fun e c=>Finsupp.single (q7 e).1 (c ^ (p ^ n)*z151 k p (q7 e).2)
      have q2:∀ r:z150 k p B 1,q11 r=(q9 r).sum (fun q c=>c ^ (p ^ n)*z151 k p q):=fun r=>by
        dsimp only [q11,q9];rw [Finsupp.sum_apply,Finsupp.sum_sum_index]
        · refine Finsupp.sum_congr fun e _ => ?_
          split_ifs with h
          · subst h
            rw [Finsupp.single_eq_same,Finsupp.sum_single_index (by simp [zero_pow (pow_ne_zero n hp.out.ne_zero)])]
          · rw [Finsupp.single_eq_of_ne (Ne.symm h),Finsupp.sum_zero_index]
        · intro q;simp [zero_pow (pow_ne_zero n hp.out.ne_zero)]
        · intro q c1 c2;rw [add_pow_char_pow c1 c2,add_mul]
      have q1:q11.sum (fun r c=>c ^ p*z151 k p r)=f.sum (fun e c=>c ^ (p ^ (n+1))*z151 k p e):=by
        dsimp only [q11];rw [Finsupp.sum_sum_index]
        · refine Finsupp.sum_congr fun e _ => ?_
          rw [Finsupp.sum_single_index (by simp [zero_pow hp.out.ne_zero])]
          have hmv:z151 k p e=z151 k p (q7 e).1*(z151 k p (q7 e).2) ^ p:=by
            conv_lhs=>rw [← hlr e]
            exact q0 _ _
          rw [hmv,mul_pow,← pow_mul,← pow_succ];ring
        · intro r;simp [zero_pow hp.out.ne_zero]
        · intro r c1 c2;rw [add_pow_char c1 c2,add_mul]
      have q3:q11=0:=q5 q11 (q1.trans hf)
      have q4:∀ r,q9 r=0:=fun r=>by
        refine ih.1 (q9 r) ?_
        rw [← q2 r,q3];rfl
      ext e
      have hfe:q9 (q7 e).1 (q7 e).2=f e:=by
        dsimp only [q9];rw [Finsupp.sum_apply,Finsupp.sum]
        by_cases hmem:e∈f.support
        · rw [Finset.sum_eq_single e]
          · simp
          · intro e' _ hne
            split_ifs with h1
            · rw [Finsupp.single_apply,if_neg]
              intro h2;exact hne (by rw [← hlr e',← hlr e,Prod.ext h1 h2])
            · rfl
          · intro h;exact absurd hmem h
        · have hf0:f e=0:=Finsupp.notMem_support_iff.mp hmem
          rw [hf0]
          refine Finset.sum_eq_zero fun e' he' => ?_
          have hne:e'≠e:=fun h=>hmem (h▸he')
          split_ifs with h1
          · rw [Finsupp.single_apply,if_neg]
            intro h2;exact hne (by rw [← hlr e',← hlr e,Prod.ext h1 h2])
          · rfl
      rw [← hfe,q4];rfl
    · intro x
      obtain ⟨g,hg⟩:=q8 x
      let h:z150 k p B 1→z150 k p B n →₀ k:=fun r=>(ih.2 (g r)).choose
      have hh:∀ r,(h r).sum (fun q c=>c ^ (p ^ n)*z151 k p q)=g r:=fun r=>(ih.2 (g r)).choose_spec
      let f:z150 k p B (n+1) →₀ k:=g.sum fun r _=>(h r).sum fun q c=>Finsupp.single (q6 (r,q)) c
      refine ⟨f,?_⟩
      dsimp only [f];rw [Finsupp.sum_sum_index]
      · have q10:∀ r∈g.support,
            ((h r).sum fun q c=>Finsupp.single (q6 (r,q)) c).sum
              (fun e c=>c ^ (p ^ (n+1))*z151 k p e) =
            (g r) ^ p*z151 k p r:=fun r _=>by
          rw [Finsupp.sum_sum_index]
          · calc (h r).sum (fun q c =>
                  (Finsupp.single (q6 (r,q)) c).sum
                    (fun e c'=>c' ^ (p ^ (n+1))*z151 k p e))
                = (h r).sum (fun q c =>
                    (c ^ (p ^ n)*z151 k p q) ^ p*z151 k p r):=by
                  refine Finsupp.sum_congr fun q _ => ?_
                  rw [Finsupp.sum_single_index (by simp [zero_pow (pow_ne_zero (n+1) hp.out.ne_zero)])];rw [q0 r q,mul_pow,← pow_mul,← pow_succ];ring
              _=((h r).sum (fun q c=>c ^ (p ^ n)*z151 k p q)) ^ p*z151 k p r:=by
                  rw [Finsupp.sum,Finsupp.sum,← Finset.sum_mul];congr 1;exact (map_sum (frobenius k p) _ _).symm
              _=(g r) ^ p*z151 k p r:=by rw [hh r]
          · intro e;simp [zero_pow (pow_ne_zero (n+1) hp.out.ne_zero)]
          · intro e c1 c2;rw [add_pow_char_pow c1 c2,add_mul]
        rw [Finsupp.sum,Finset.sum_congr rfl q10];exact hg
      · intro e;simp [zero_pow (pow_ne_zero (n+1) hp.out.ne_zero)]
      · intro e c1 c2;rw [add_pow_char_pow c1 c2,add_mul]
end PBasis
section CohenRingConstruction
variable (k:Type) [Field k] (p : ℕ) [hp:Fact p.Prime] [CharP k p]
variable (B:Set k)
abbrev z155:Type:=PerfectClosure k p
abbrev z156:Type:=WittVector p (z155 k p)
def z157:k →+* z155 k p:=PerfectClosure.of k p
lemma z158:Injective (z157 k p):=RingHom.injective (z157 k p)
noncomputable def z159 : ℕ → z156 k p →+* z156 k p
 | 0=>RingHom.id _
 | n+1=>WittVector.frobenius.comp (z159 n)
lemma z160 (n : ℕ) (w:z156 k p) (i : ℕ) :
  (z159 k p n w).coeff i=(w.coeff i) ^ (p ^ n):=by
 induction n with
 | zero=>simp [z159]
 | succ n ih =>
  simp only [z159,RingHom.comp_apply,WittVector.coeff_frobenius_charP,ih,← pow_mul,← pow_succ]
noncomputable def z161 (n : ℕ) : WittVector p k →+* z156 k p:=(z159 k p n).comp (WittVector.map (z157 k p))
lemma z162 (n : ℕ) (z:WittVector p k) (i : ℕ) :
  (z161 k p n z).coeff i=z157 k p ((z.coeff i) ^ (p ^ n)):=by
 simp only [z161,RingHom.comp_apply,z160,WittVector.map_coeff,map_pow]
lemma z163 (n : ℕ) (z:WittVector p k) :
  z161 k p (n+1) z=z161 k p n (WittVector.frobenius z):=by
 ext i;rw [z162,z162,WittVector.coeff_frobenius_charP,← pow_mul,← pow_succ']
lemma z164 (n : ℕ) (z:WittVector p k) :
    z161 k p (n+1) (WittVector.verschiebung z)=(p:z156 k p)*z161 k p n z:=by
  have h1:WittVector.frobenius (WittVector.map (z157 k p) (WittVector.verschiebung z))=(p:z156 k p)*WittVector.map (z157 k p) z:=by
    rw [WittVector.map_verschiebung,WittVector.frobenius_verschiebung,mul_comm]
  have q0:∀ m (w:z156 k p),z159 k p (m+1) w=z159 k p m (WittVector.frobenius w):=by
    intro m
    induction m with
    | zero=>intro w;rfl
    | succ m ih =>
      intro w;change WittVector.frobenius (z159 k p (m+1) w)=WittVector.frobenius (z159 k p m (WittVector.frobenius w));rw [ih w]
  calc z161 k p (n+1) (WittVector.verschiebung z)
      = z159 k p n (WittVector.frobenius (WittVector.map (z157 k p) (WittVector.verschiebung z))):=q0 n _
    _=z159 k p n ((p:z156 k p)*WittVector.map (z157 k p) z):=by rw [h1]
    _=(p:z156 k p)*z161 k p n z:=by
        rw [map_mul,map_natCast];rfl
noncomputable def z165 (b:B) : z156 k p:=WittVector.teichmuller p (z157 k p b.1)
noncomputable def z166 (e:B →₀ ℕ) : z156 k p:=e.prod (fun b m=>z165 k p B b ^ m)
lemma z167:z166 k p B 0=1:=by
 simp [z166]
lemma z168 (e1 e2:B →₀ ℕ) :
  z166 k p B (e1+e2)=z166 k p B e1*z166 k p B e2:=by
 simp only [z166]
 exact Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)
lemma z169 (e:B →₀ ℕ) :
  (z166 k p B e).coeff 0=z157 k p (e.prod (fun b m=>(b:k) ^ m)):=by
 change WittVector.constantCoeff (z166 k p B e)=_;simp only [z166,Finsupp.prod,map_prod,map_pow]
 refine Finset.prod_congr rfl fun b _ => ?_
 rfl
lemma z170 (n : ℕ) (q:B →₀ ℕ) :
  z166 k p B ((p ^ n)•q)=z161 k p n (q.prod (fun b m=>WittVector.teichmuller p (b:k) ^ m)):=by
 classical
 have h1:z166 k p B ((p ^ n)•q)=(z166 k p B q) ^ (p ^ n):=by
  simp only [z166,Finsupp.prod]
  have q1:((p ^ n)•q).support=q.support:=by
   ext b;simp only [Finsupp.mem_support_iff,Finsupp.smul_apply,smul_eq_mul,ne_eq,mul_eq_zero,pow_ne_zero n hp.out.ne_zero,false_or]
  rw [q1,← Finset.prod_pow]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [Finsupp.smul_apply,smul_eq_mul];rw [mul_comm,pow_mul]
 rw [h1]
 have q0:∀ a:k,z161 k p n (WittVector.teichmuller p a)=WittVector.teichmuller p (z157 k p a) ^ (p ^ n):=fun a=>by
  ext i;rw [z162,← map_pow (WittVector.teichmuller p)]
  cases i with
  | zero =>
   rw [WittVector.teichmuller_coeff_zero,WittVector.teichmuller_coeff_zero,map_pow]
  | succ i =>
   rw [WittVector.teichmuller_coeff_pos p a (i+1) (Nat.succ_pos i),zero_pow (pow_ne_zero n hp.out.ne_zero),map_zero,WittVector.teichmuller_coeff_pos p _ (i+1) (Nat.succ_pos i)]
 simp only [z166,Finsupp.prod,map_prod,map_pow,← Finset.prod_pow]
 refine Finset.prod_congr rfl fun b _ => ?_
 rw [q0 b.1,← pow_mul,mul_comm,pow_mul];rfl
noncomputable def z171 (n : ℕ) : Subring (z156 k p):=Subring.closure (Set.range (z165 k p B) ∪ Set.range (z161 k p n))
lemma z172:Antitone (z171 k p B):=by
 refine antitone_nat_of_succ_le fun n => ?_
 rw [z171,Subring.closure_le];rintro x (⟨b,rfl⟩ | ⟨z,rfl⟩)
 · exact Subring.subset_closure (Or.inl ⟨b,rfl⟩)
 ·
  rw [z163];exact Subring.subset_closure (Or.inr ⟨WittVector.frobenius z,rfl⟩)
lemma z173 (n : ℕ) (x:z156 k p) :
    x∈z171 k p B n ↔
      ∃ f:z150 k p B n →₀ WittVector p k,x=f.sum (fun e z=>z161 k p n z*z166 k p B e.1):=by
  classical
  constructor
  · intro hx
    let T:Subring (z156 k p) :=
      { carrier:={ y | ∃ f:z150 k p B n →₀ WittVector p k,y=f.sum (fun e z=>z161 k p n z*z166 k p B e.1) }
        zero_mem':=⟨0,by simp⟩
        one_mem':=by
          let e0:z150 k p B n:=⟨0,fun _=>pow_pos hp.out.pos n⟩
          refine ⟨Finsupp.single e0 1,?_⟩
          rw [Finsupp.sum_single_index (by simp)];simp [e0,z167]
        add_mem':=by
          rintro _ _ ⟨f1,rfl⟩ ⟨f2,rfl⟩
          refine ⟨f1+f2,?_⟩
          rw [Finsupp.sum_add_index' (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
        neg_mem':=by
          rintro _ ⟨f,rfl⟩
          refine ⟨-f,?_⟩
          have q5:(-f).sum (fun e z=>z161 k p n z*z166 k p B e.1)+f.sum (fun e z=>z161 k p n z*z166 k p B e.1)=0:=by
            rw [← Finsupp.sum_add_index' (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
            simp
          exact eq_neg_of_add_eq_zero_left q5 |>.symm
        mul_mem':=by
          have q2:∀ (z1 z2:WittVector p k) (e1 e2:z150 k p B n),
              ∃ f:z150 k p B n →₀ WittVector p k,(z161 k p n z1*z166 k p B e1.1)*(z161 k p n z2*z166 k p B e2.1)=f.sum (fun e z=>z161 k p n z*z166 k p B e.1):=by
            intro z1 z2 e1 e2;let e:B →₀ ℕ := e1.1+e2.1;let q:B →₀ ℕ := e.mapRange (· / p ^ n) (Nat.zero_div _);let r:B →₀ ℕ := e.mapRange (· % p ^ n) (Nat.zero_mod _)
            have q3:∀ b:B,r b < p ^ n:=fun b=>by
              simp only [r,Finsupp.mapRange_apply];exact Nat.mod_lt _ (pow_pos hp.out.pos n)
            have q4:e1.1+e2.1=(p ^ n)•q+r:=by
              ext b;simp only [e,q,r,Finsupp.add_apply,Finsupp.smul_apply,Finsupp.mapRange_apply,smul_eq_mul];exact (Nat.div_add_mod (e1.1 b+e2.1 b) (p ^ n)).symm
            let rM:z150 k p B n:=⟨r,q3⟩
            let qW:WittVector p k:=q.prod (fun b m=>WittVector.teichmuller p (b:k) ^ m)
            refine ⟨Finsupp.single rM (z1*z2*qW),?_⟩
            rw [Finsupp.sum_single_index (by simp)]
            have ht:z166 k p B e1.1*z166 k p B e2.1=z161 k p n qW*z166 k p B r:=by
              rw [← z168,q4,z168,z170]
            calc (z161 k p n z1*z166 k p B e1.1)*(z161 k p n z2*z166 k p B e2.1)
                = z161 k p n z1*z161 k p n z2*(z166 k p B e1.1*z166 k p B e2.1):=by ring
              _=z161 k p n z1*z161 k p n z2*(z161 k p n qW*z166 k p B r):=by rw [ht]
              _=z161 k p n (z1*z2*qW)*z166 k p B rM.1:=by
                  simp only [map_mul,rM];ring
          have q1:∀ {y1 y2:z156 k p},(∃ f:z150 k p B n →₀ WittVector p k,y1=f.sum (fun e z=>z161 k p n z*z166 k p B e.1))→(∃ f:z150 k p B n →₀ WittVector p k,y2=f.sum (fun e z=>z161 k p n z*z166 k p B e.1))→∃ f:z150 k p B n →₀ WittVector p k,y1+y2=f.sum (fun e z=>z161 k p n z*z166 k p B e.1):=by
            rintro _ _ ⟨f1,rfl⟩ ⟨f2,rfl⟩
            exact ⟨f1+f2,(Finsupp.sum_add_index' (fun _=>by simp)
              (fun _ _ _=>by rw [map_add,add_mul])).symm⟩
          have q0:∀ {ι : Type} (s:Finset ι) (g : ι → z156 k p),
              (∀ i∈s,∃ f:z150 k p B n →₀ WittVector p k,g i=f.sum (fun e z=>z161 k p n z*z166 k p B e.1)) →
              ∃ f:z150 k p B n →₀ WittVector p k,∑ i∈s,g i=f.sum (fun e z=>z161 k p n z*z166 k p B e.1):=by
            intro ι s g
            refine Finset.induction_on s (fun _=>⟨0,by simp⟩) ?_
            intro a s' ha ih hg;rw [Finset.sum_insert ha]
            exact q1 (hg a (Finset.mem_insert_self a s'))
              (ih fun i hi=>hg i (Finset.mem_insert_of_mem hi))
          rintro _ _ ⟨f1,rfl⟩ ⟨f2,rfl⟩;rw [Finsupp.sum,Finsupp.sum,Finset.sum_mul]
          refine q0 f1.support _ fun e1 _ => ?_
          rw [Finset.mul_sum]
          exact q0 f2.support _ fun e2 _=>q2 _ _ e1 e2 }
    have hle:z171 k p B n ≤ T:=by
      rw [z171,Subring.closure_le];rintro y (⟨b,rfl⟩ | ⟨z,rfl⟩)
      · cases n with
        | zero =>
          let e0:z150 k p B 0:=⟨0,fun _=>by simp⟩
          refine ⟨Finsupp.single e0 (WittVector.teichmuller p b.1),?_⟩
          rw [Finsupp.sum_single_index (by simp),z167,mul_one];simp [z161,z159,z165]
        | succ m =>
          let eb:z150 k p B (m+1):=⟨Finsupp.single b 1,fun b'=>by
            by_cases h:b'=b
            · subst h
              rw [Finsupp.single_eq_same];exact one_lt_pow₀ hp.out.one_lt (Nat.succ_ne_zero m)
            · rw [Finsupp.single_eq_of_ne h]
              exact pow_pos hp.out.pos _⟩
          refine ⟨Finsupp.single eb 1,?_⟩
          rw [Finsupp.sum_single_index (by simp),map_one,one_mul];simp [eb,z166,Finsupp.prod_single_index]
      · let e0:z150 k p B n:=⟨0,fun _=>pow_pos hp.out.pos n⟩
        refine ⟨Finsupp.single e0 z,?_⟩
        rw [Finsupp.sum_single_index (by simp),z167,mul_one]
    exact hle hx
  · rintro ⟨f,rfl⟩
    rw [Finsupp.sum]
    refine Subring.sum_mem _ fun e _=>Subring.mul_mem _ ?_ ?_
    · exact Subring.subset_closure (Or.inr ⟨f e,rfl⟩)
    · simp only [z166,Finsupp.prod]
      exact (z171 k p B n).prod_mem fun b _=>(z171 k p B n).pow_mem
        (Subring.subset_closure (Or.inl ⟨b,rfl⟩)) _
lemma z174 (q3:z152 k p B)
  (q5:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x)
  (n : ℕ) {x:z156 k p} (hx:x∈z171 k p B (n+1))
  (hxp:x∈span {(p:z156 k p)}) :
  ∃ y∈z171 k p B n,x=(p:z156 k p)*y:=by
 classical
 obtain ⟨f,rfl⟩:=(z173 k p B (n+1) x).mp hx
 have hx0:(f.sum (fun e z=>z161 k p (n+1) z*z166 k p B e.1)).coeff 0=0:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp hxp
 let f0:z150 k p B (n+1) →₀ k:=f.mapRange (fun z=>z.coeff 0) (WittVector.zero_coeff p k 0)
 have q2:f0.sum (fun e c=>c ^ (p ^ (n+1))*z151 k p e)=0:=by
  apply z158 k p;rw [map_zero,← hx0]
  change z157 k p (f0.sum (fun e c=>c ^ (p ^ (n+1))*z151 k p e))=WittVector.constantCoeff (f.sum (fun e z=>z161 k p (n+1) z*z166 k p B e.1))
  rw [Finsupp.sum_mapRange_index (fun _=>by simp [zero_pow (pow_ne_zero (n+1) hp.out.ne_zero)])]
  rw [Finsupp.sum,Finsupp.sum,map_sum,map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul,map_mul];congr 1
  · exact (z162 k p (n+1) (f e) 0).symm
  · exact (z169 k p B e.1).symm
 have q0:f0=0:=(z154 k p q3 q5 (n+1)).1 f0 q2
 have q1:∀ e:z150 k p B (n+1),(f e).coeff 0=0:=fun e=>by
  have:=congrArg (fun g:z150 k p B (n+1) →₀ k=>g e) q0
  simpa [f0] using this
 have q4:∀ e:z150 k p B (n+1),f e=WittVector.verschiebung ((f e).shift 1):=fun e=>by
  have h1:=WittVector.eq_iterate_verschiebung (x:=f e) (n:=1) (fun i hi=>by
   have : i=0:=by omega
   subst this
   exact q1 e)
  simpa using h1
 let y:z156 k p:=f.sum (fun e z=>z161 k p n (z.shift 1)*z166 k p B e.1)
 have q6:y∈z171 k p B n:=by
  dsimp only [y];rw [Finsupp.sum]
  refine Subring.sum_mem _ fun e _=>Subring.mul_mem _ ?_ ?_
  · exact Subring.subset_closure (Or.inr ⟨(f e).shift 1,rfl⟩)
  ·
   simp only [z166,Finsupp.prod]
   exact (z171 k p B n).prod_mem fun b _=>(z171 k p B n).pow_mem
    (Subring.subset_closure (Or.inl ⟨b,rfl⟩)) _
 refine ⟨y,q6,?_⟩
 dsimp only [y];rw [Finsupp.sum,Finsupp.sum,Finset.mul_sum]
 refine Finset.sum_congr rfl fun e _ => ?_
 conv_lhs=>rw [q4 e,z164]
 ring
lemma z175 (n : ℕ) {x:z156 k p} (hx:x∈z171 k p B n) :
  ∃ a:k,x.coeff 0=z157 k p a:=by
 obtain ⟨f,rfl⟩:=(z173 k p B n x).mp hx
 refine ⟨f.sum (fun e z=>(z.coeff 0) ^ (p ^ n)*z151 k p e),?_⟩
 change WittVector.constantCoeff (f.sum (fun e z=>z161 k p n z*z166 k p B e.1))=_
 rw [Finsupp.sum,Finsupp.sum,map_sum,map_sum]
 refine Finset.sum_congr rfl fun e _ => ?_
 rw [map_mul,map_mul];congr 1
 · exact z162 k p n (f e) 0
 · exact z169 k p B e.1
lemma z176 (q0:z152 k p B)
  (q1:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x)
  (n : ℕ) (a:k) :
  ∃ x∈z171 k p B n,x.coeff 0=z157 k p a:=by
 classical
 obtain ⟨f,hf⟩:=(z154 k p q0 q1 n).2 a
 let fW:z150 k p B n →₀ WittVector p k:=f.mapRange (fun c=>WittVector.teichmuller p c) (WittVector.teichmuller_zero p)
 let x:z156 k p:=fW.sum (fun e z=>z161 k p n z*z166 k p B e.1)
 refine ⟨x,(z173 k p B n x).mpr ⟨fW,rfl⟩,?_⟩
 change WittVector.constantCoeff x=z157 k p a;rw [← hf];dsimp only [x,fW]
 rw [Finsupp.sum_mapRange_index (fun _=>by simp)]
 rw [Finsupp.sum,Finsupp.sum,map_sum,map_sum]
 refine Finset.sum_congr rfl fun e _ => ?_
 rw [map_mul,map_mul];congr 1
 · exact z162 k p n (WittVector.teichmuller p (f e)) 0
 · exact z169 k p B e.1
lemma z177 (q1:z152 k p B)
  (q2:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x) :
  ∀ n m : ℕ,1 ≤ n→n ≤ m→∀ x∈z171 k p B n,∃ y∈z171 k p B m,x - y∈span {(p:z156 k p) ^ n}:=by
 intro n
 induction n with
 | zero=>intro m h0;omega
 | succ n ih =>
  intro m _ hnm x hx
  cases n with
  | zero =>
   obtain ⟨a,ha⟩:=z175 k p B 1 hx;obtain ⟨y,hy,hy0⟩:=z176 k p B q1 q2 m a
   refine ⟨y,hy,?_⟩
   rw [pow_one,WittVector.mem_span_p_iff_coeff_zero_eq_zero];rw [← WittVector.constantCoeff_apply,map_sub];change x.coeff 0 - y.coeff 0=0;rw [ha,hy0,sub_self]
  | succ n' =>
   obtain ⟨a,ha⟩:=z175 k p B (n'+2) hx;obtain ⟨y0,hy0_mem,hy0_coeff⟩:=z176 k p B q1 q2 m a;have q3:y0∈z171 k p B (n'+2):=z172 k p B hnm hy0_mem
   have q0:x - y0∈span {(p:z156 k p)}:=by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero,← WittVector.constantCoeff_apply,map_sub];change x.coeff 0 - y0.coeff 0=0;rw [ha,hy0_coeff,sub_self]
   obtain ⟨u,hu_mem,hxu⟩:=z174 k p B q1 q2 (n'+1)
    ((z171 k p B (n'+2)).sub_mem hx q3) q0
   obtain ⟨v,hv_mem,huv⟩:=ih m (Nat.succ_le_succ (Nat.zero_le _)) (by omega) u hu_mem
   refine ⟨y0+(p:z156 k p)*v,(z171 k p B m).add_mem hy0_mem
    ((z171 k p B m).mul_mem (natCast_mem _ p) hv_mem),?_⟩
   obtain ⟨w,hw⟩:=mem_span_singleton.mp huv;rw [mem_span_singleton]
   refine ⟨w,?_⟩
   have h1:x - (y0+(p:z156 k p)*v)=(p:z156 k p)*(u - v):=by
    linear_combination hxu
   rw [h1,hw];ring
noncomputable def z178 (n : ℕ) : Subring (z156 k p) where
 carrier:={ x:z156 k p | ∃ s∈z171 k p B n,x - s∈span {(p:z156 k p) ^ n} }
 zero_mem':=⟨0,(z171 k p B n).zero_mem,by simp⟩
 one_mem':=⟨1,(z171 k p B n).one_mem,by simp⟩
 add_mem':=by
  rintro x y ⟨sx,hsx,hx⟩ ⟨sy,hsy,hy⟩
  refine ⟨sx+sy,(z171 k p B n).add_mem hsx hsy,?_⟩
  have : x+y - (sx+sy)=(x - sx)+(y - sy):=by ring
  rw [this];exact Ideal.add_mem _ hx hy
 neg_mem':=by
  rintro x ⟨sx,hsx,hx⟩
  refine ⟨-sx,(z171 k p B n).neg_mem hsx,?_⟩
  have : -x - -sx = -(x - sx):=by ring
  rw [this];exact Submodule.neg_mem _ hx
 mul_mem':=by
  rintro x y ⟨sx,hsx,hx⟩ ⟨sy,hsy,hy⟩
  refine ⟨sx*sy,(z171 k p B n).mul_mem hsx hsy,?_⟩
  have : x*y - sx*sy=(x - sx)*y+sx*(y - sy):=by ring
  rw [this];exact Ideal.add_mem _ (Ideal.mul_mem_right y _ hx) (Ideal.mul_mem_left _ sx hy)
lemma z179:Antitone (z178 k p B):=by
 refine antitone_nat_of_succ_le fun n x ⟨s,hs,hxs⟩ => ?_
 refine ⟨s,z172 k p B (Nat.le_succ n) hs,?_⟩
 have hle:span {(p:z156 k p) ^ (n+1)} ≤ span {(p:z156 k p) ^ n}:=by
  rw [Ideal.span_singleton_le_span_singleton];exact pow_dvd_pow _ (Nat.le_succ n)
 exact hle hxs
noncomputable def z180:Subring (z156 k p) := ⨅ n : ℕ,z178 k p B (n+1)
abbrev z181:Type:=z180 k p B
lemma z182 (x:z156 k p) :
  x∈z180 k p B↔∀ n : ℕ,1 ≤ n→x∈z178 k p B n:=by
 simp only [z180,Subring.mem_iInf];constructor
 ·
  intro h n hn;obtain ⟨m,rfl⟩:=Nat.exists_eq_add_of_le' hn;exact h m
 ·
  intro h n;exact h (n+1) (Nat.succ_le_succ (Nat.zero_le n))
lemma z183 (q4:z152 k p B)
  (q7:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x)
  (n : ℕ) (hn:1 ≤ n) {s:z156 k p} (hs:s∈z171 k p B n) :
  ∃ c:z181 k p B,(c:z156 k p) - s∈span {(p:z156 k p) ^ n}:=by
 classical
 have q8:∀ k0 : ℕ,∀ x∈z171 k p B (n+k0),∃ y∈z171 k p B (n+k0+1),x - y∈span {(p:z156 k p) ^ (n+k0)} :=
  fun k0 x hx=>z177 k p B q4 q7 (n+k0) (n+k0+1)
   (by omega) (Nat.le_succ _) x hx
 let seq:(j : ℕ)→{ x:z156 k p // x∈z171 k p B (n+j) } :=
  Nat.rec ⟨s,hs⟩ fun j prev =>
   ⟨(q8 j prev.1 prev.2).choose,(q8 j prev.1 prev.2).choose_spec.1⟩
 have q0:∀ j : ℕ,(seq j).1 - (seq (j+1)).1∈span {(p:z156 k p) ^ (n+j)}:=fun j=>(q8 j (seq j).1 (seq j).2).choose_spec.2
 have q1:∀ {i j : ℕ},i ≤ j→(seq i).1 - (seq j).1∈span {(p:z156 k p) ^ (n+i)}:=by
  intro i j hij
  induction j,hij using Nat.le_induction with
  | base=>simp
  | succ j hij ih =>
   have h1:(seq i).1 - (seq (j+1)).1=((seq i).1 - (seq j).1)+((seq j).1 - (seq (j+1)).1):=by
    ring
   rw [h1]
   refine Ideal.add_mem _ ih ?_
   have hle:span {(p:z156 k p) ^ (n+j)} ≤ span {(p:z156 k p) ^ (n+i)}:=by
    rw [Ideal.span_singleton_le_span_singleton];exact pow_dvd_pow _ (Nat.add_le_add_left hij n)
   exact hle (q0 j)
 let q5 : ℕ → z156 k p:=fun m=>(seq m).1
 have q2:∀ {a b : ℕ},a ≤ b→q5 a ≡ q5 b [SMOD (span {(p:z156 k p)} ^ a•(⊤ : Submodule (z156 k p) (z156 k p)))]:=by
  intro a b hab;rw [SModEq.sub_mem,span_singleton_pow,smul_eq_mul,mul_top]
  have hle:span {(p:z156 k p) ^ (n+a)} ≤ span {(p:z156 k p) ^ a}:=by
   rw [Ideal.span_singleton_le_span_singleton];exact pow_dvd_pow _ (Nat.le_add_left a n)
  exact hle (q1 hab)
 obtain ⟨L,hL⟩:=IsPrecomplete.prec' (I:=span {(p:z156 k p)}) (M:=z156 k p) q5 q2
 have q3:∀ j : ℕ,L - (seq j).1∈span {(p:z156 k p) ^ (n+j)}:=by
  intro j;have h1:=hL (n+j);rw [SModEq.sub_mem,span_singleton_pow,smul_eq_mul,mul_top] at h1
  have h1':L - (seq (n+j)).1∈span {(p:z156 k p) ^ (n+j)}:=by
   simpa [q5,neg_sub] using Submodule.neg_mem _ h1
  have h2:(seq (n+j)).1 - (seq j).1∈span {(p:z156 k p) ^ (n+j)}:=by
   have q9:=Submodule.neg_mem _ (q1 (Nat.le_add_left j n));simpa [neg_sub] using q9
  have h3:L - (seq j).1=(L - (seq (n+j)).1)+((seq (n+j)).1 - (seq j).1):=by ring
  rw [h3];exact Ideal.add_mem _ h1' h2
 have q6:L∈z180 k p B:=by
  rw [z182];intro m hm
  by_cases hmn:m ≤ n
  ·
   refine z179 k p B hmn ⟨s,hs,?_⟩
   simpa [seq] using q3 0
  ·
   obtain ⟨j,rfl⟩ : ∃ j,m=n+j:=⟨m - n,by omega⟩;exact ⟨(seq j).1,(seq j).2,q3 j⟩
 refine ⟨⟨L,q6⟩,?_⟩
 simpa [seq] using q3 0
lemma z184 (q0:z152 k p B)
    (q1:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x)
    (c:z181 k p B) (hcp:(c:z156 k p)∈span {(p:z156 k p)}) :
    ∃ c':z181 k p B,c=(p:z181 k p B)*c':=by
  obtain ⟨y,hy⟩:=mem_span_singleton.mp hcp
  have q3:y∈z180 k p B:=by
    rw [z182];intro n hn;have q2:(c:z156 k p)∈z178 k p B (n+1):=(z182 k p B _).mp c.2 (n+1) (by omega);obtain ⟨s,hs,hcs⟩:=q2;obtain ⟨w,hw⟩:=mem_span_singleton.mp hcs
    have hsp:s∈span {(p:z156 k p)}:=by
      rw [mem_span_singleton]
      refine ⟨y - (p:z156 k p) ^ n*w,?_⟩
      calc s=(c:z156 k p) - ((c:z156 k p) - s):=by ring
        _=(p:z156 k p)*y - (p:z156 k p) ^ (n+1)*w:=by rw [hw,hy]
        _=(p:z156 k p)*(y - (p:z156 k p) ^ n*w):=by rw [pow_succ'];ring
    obtain ⟨t,ht,hst⟩:=z174 k p B q0 q1 n hs hsp
    refine ⟨t,ht,?_⟩
    rw [mem_span_singleton]
    refine ⟨w,?_⟩
    have q5:(p:z156 k p)*(y - t)=(p:z156 k p)*((p:z156 k p) ^ n*w):=by
      calc (p:z156 k p)*(y - t)
          = (c:z156 k p) - s:=by rw [hy,hst];ring
        _=(p:z156 k p) ^ (n+1)*w:=hw
        _=(p:z156 k p)*((p:z156 k p) ^ n*w):=by rw [pow_succ'];ring
    have q4:(y - t - (p:z156 k p) ^ n*w)*(p:z156 k p)=0:=by
      linear_combination q5
    exact sub_eq_zero.mp (WittVector.eq_zero_of_p_mul_eq_zero _ q4)
  refine ⟨⟨y,q3⟩,Subtype.ext ?_⟩
  simpa using hy
lemma z185 (q0:z152 k p B)
  (q1:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x)
  (n : ℕ) (c:z181 k p B) :
  (c:z156 k p)∈span {(p:z156 k p) ^ n}↔c∈span {(p:z181 k p B) ^ n}:=by
 induction n generalizing c with
 | zero=>simp
 | succ n ih =>
  constructor
  ·
   intro hc
   have hcp:(c:z156 k p)∈span {(p:z156 k p)}:=by
    have hle:span {(p:z156 k p) ^ (n+1)} ≤ span {(p:z156 k p)}:=by
     rw [Ideal.span_singleton_le_span_singleton];exact dvd_pow_self _ (Nat.succ_ne_zero n)
    exact hle hc
   obtain ⟨c',rfl⟩:=z184 k p B q0 q1 c hcp
   have hc':(c':z156 k p)∈span {(p:z156 k p) ^ n}:=by
    obtain ⟨w,hw⟩:=mem_span_singleton.mp hc;rw [mem_span_singleton]
    refine ⟨w,?_⟩
    have q2:((c':z156 k p) - (p:z156 k p) ^ n*w)*(p:z156 k p)=0:=by
     have : (p:z156 k p)*(c':z156 k p)=(p:z156 k p) ^ (n+1)*w:=by
      simpa using hw
     rw [pow_succ'] at this
     linear_combination this
    exact sub_eq_zero.mp (WittVector.eq_zero_of_p_mul_eq_zero _ q2)
   obtain ⟨d,hd⟩:=mem_span_singleton.mp ((ih c').mp hc');rw [mem_span_singleton]
   refine ⟨d,?_⟩
   rw [hd,pow_succ'];ring
  ·
   intro hc;obtain ⟨d,hd⟩:=mem_span_singleton.mp hc;rw [mem_span_singleton];exact ⟨(d:z156 k p),by simpa using congrArg Subtype.val hd⟩
lemma z186 (q6:z152 k p B)
    (q8:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x)
    (c:z181 k p B) (hc:(c:z156 k p).coeff 0≠0) : IsUnit c:=by
  have huW:IsUnit (c:z156 k p):=WittVector.isUnit_of_coeff_zero_ne_zero _ hc;let uW:(z156 k p)ˣ := huW.unit;let q12:z156 k p:=(uW⁻¹ : (z156 k p)ˣ);have q2:q12*(c:z156 k p)=1:=uW.inv_mul;have q1:(c:z156 k p)*q12=1:=uW.mul_inv
  have q4:q12∈z180 k p B:=by
    rw [z182];intro n hn;have hc1:(c:z156 k p)∈z178 k p B 1:=(z182 k p B _).mp c.2 1 le_rfl;obtain ⟨s1,hs1,hcs1⟩:=hc1;obtain ⟨a0,ha0⟩:=z175 k p B 1 hs1
    have q15:(c:z156 k p).coeff 0=z157 k p a0:=by
      have h0:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp (by simpa using hcs1);rw [← WittVector.constantCoeff_apply,map_sub,sub_eq_zero] at h0;exact h0.trans ha0
    have q7:a0≠0:=fun h0=>hc (by rw [q15,h0,map_zero])
    obtain ⟨b0,hb0_mem,hb0_coeff⟩:=z176 k p B q6 q8 n a0⁻¹
    have q10:1 - (c:z156 k p)*b0∈span {(p:z156 k p)}:=by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero,← WittVector.constantCoeff_apply,
        map_sub,map_one,map_mul]
      change 1 - (c:z156 k p).coeff 0*b0.coeff 0=0;rw [q15,hb0_coeff,← map_mul,mul_inv_cancel₀ q7,map_one,sub_self]
    let d:z156 k p:=1 - (c:z156 k p)*b0
    have q9:d∈z178 k p B n :=
      (z178 k p B n).sub_mem (z178 k p B n).one_mem
        ((z178 k p B n).mul_mem ((z182 k p B _).mp c.2 n hn) ⟨b0,hb0_mem,by simp⟩)
    let q3:z156 k p:=b0 * ∑ i∈Finset.range n,d ^ i
    have q0:q3∈z178 k p B n :=
      (z178 k p B n).mul_mem ⟨b0,hb0_mem,by simp⟩
        ((z178 k p B n).sum_mem fun i _=>(z178 k p B n).pow_mem q9 i)
    have q5:(c:z156 k p)*q3=1 - d ^ n:=by
      have q11:(1 - d) * ∑ i∈Finset.range n,d ^ i=1 - d ^ n:=by
        have:=geom_sum_mul d n
        linear_combination -this
      have h1d:(c:z156 k p)*b0=1 - d:=by dsimp only [d];ring
      calc (c:z156 k p)*q3
          = ((c:z156 k p)*b0) * ∑ i∈Finset.range n,d ^ i:=by dsimp only [q3];ring
        _=(1 - d) * ∑ i∈Finset.range n,d ^ i:=by rw [h1d]
        _=1 - d ^ n:=q11
    have hdn:d ^ n∈span {(p:z156 k p) ^ n}:=by
      rw [← span_singleton_pow];exact Ideal.pow_mem_pow q10 n
    have q14:q12 - q3∈span {(p:z156 k p) ^ n}:=by
      have q13:q12 - q3=q12*d ^ n:=by
        calc q12 - q3
            = q12 - q12*((c:z156 k p)*q3):=by
              rw [← mul_assoc,q2,one_mul]
          _=q12*(1 - (c:z156 k p)*q3):=by ring
          _=q12*d ^ n:=by rw [q5];ring
      rw [q13];exact Ideal.mul_mem_left _ _ hdn
    obtain ⟨s,hs,hinv_s⟩:=q0
    refine ⟨s,hs,?_⟩
    have : q12 - s=(q12 - q3)+(q3 - s):=by ring
    rw [this];exact Ideal.add_mem _ q14 hinv_s
  refine ⟨⟨c,⟨q12,q4⟩,?_,?_⟩,rfl⟩
  · exact Subtype.ext q1
  · exact Subtype.ext q2
lemma z187 (q3:z152 k p B)
  (q6:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x) :
  IsDiscreteValuationRing (z181 k p B):=by
 have q0 : ¬ IsUnit (p:z181 k p B):=by
  intro hu
  have huW:IsUnit (p:z156 k p):=by
   have:=hu.map (z180 k p B).subtype;simpa using this
  exact (WittVector.irreducible p (k:=z155 k p)).not_isUnit huW
 have q1:Irreducible (p:z181 k p B):=by
  refine ⟨q0,fun a b hab => ?_⟩
  have q8:(p:z156 k p)=(a:z156 k p)*(b:z156 k p):=by
   simpa using congrArg Subtype.val hab
  rcases (WittVector.irreducible p (k:=z155 k p)).isUnit_or_isUnit q8 with ha | hb
  ·
   left
   have ha0:(a:z156 k p).coeff 0≠0:=by
    intro h0;have q7:(a:z156 k p)∈span {(p:z156 k p)}:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr h0;obtain ⟨w,hw⟩:=mem_span_singleton.mp q7
    exact (WittVector.irreducible p (k:=z155 k p)).not_isUnit (isUnit_of_mul_isUnit_left (hw▸ha))
   exact z186 k p B q3 q6 a ha0
  ·
   right
   have hb0:(b:z156 k p).coeff 0≠0:=by
    intro h0;have q7:(b:z156 k p)∈span {(p:z156 k p)}:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr h0;obtain ⟨w,hw⟩:=mem_span_singleton.mp q7
    exact (WittVector.irreducible p (k:=z155 k p)).not_isUnit (isUnit_of_mul_isUnit_left (hw▸hb))
   exact z186 k p B q3 q6 b hb0
 refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨p,q1,fun {x} hx => ?_⟩
 have hxW:(x:z156 k p)≠0:=fun h0=>hx (Subtype.ext h0)
 obtain ⟨m,uW,hxu⟩:=WittVector.exists_eq_pow_p_mul' (x:z156 k p) hxW
 have q4:x∈span {(p:z181 k p B) ^ m}:=by
  rw [← z185 k p B q3 q6 m x,mem_span_singleton];exact ⟨(uW:z156 k p),hxu⟩
 obtain ⟨u,hu⟩:=mem_span_singleton.mp q4
 have q5:(u:z156 k p)=(uW:z156 k p):=by
  have q9:(p:z156 k p) ^ m*(u:z156 k p)=(p:z156 k p) ^ m*(uW:z156 k p):=by
   have:=congrArg Subtype.val hu;simpa [hxu] using this.symm
  exact mul_left_cancel₀ (pow_ne_zero m (WittVector.p_nonzero p (z155 k p))) q9
 have hu0:(u:z156 k p).coeff 0≠0:=by
  rw [q5];intro h0;have q7:(uW:z156 k p)∈span {(p:z156 k p)}:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr h0;obtain ⟨w,hw⟩:=mem_span_singleton.mp q7
  exact (WittVector.irreducible p (k:=z155 k p)).not_isUnit (isUnit_of_mul_isUnit_left (hw▸uW.isUnit))
 have q2:IsUnit u:=z186 k p B q3 q6 u hu0
 refine ⟨m,q2.unit,?_⟩
 rw [q2.unit_spec];exact hu.symm
lemma z188 (q0:z152 k p B)
  (q1:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x)
  [IsDiscreteValuationRing (z181 k p B)] :
  maximalIdeal (z181 k p B)=span {(p:z181 k p B)}:=by
 refine le_antisymm ?_ ?_
 ·
  intro c hc
  have hc0:(c:z156 k p).coeff 0=0:=by
   by_contra hne
   exact hc (z186 k p B q0 q1 c hne)
  have hcp:(c:z156 k p)∈span {(p:z156 k p)}:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr hc0;obtain ⟨c',rfl⟩:=z184 k p B q0 q1 c hcp;exact mem_span_singleton.mpr ⟨c',rfl⟩
 ·
  rw [span_singleton_le_iff_mem];intro hu
  exact (WittVector.irreducible p (k:=z155 k p)).not_isUnit
   (by simpa using hu.map (z180 k p B).subtype)
lemma z189 (q0:z152 k p B)
  (q2:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x)
  [IsDiscreteValuationRing (z181 k p B)] :
  IsAdicComplete (maximalIdeal (z181 k p B)) (z181 k p B):=by
 rw [z188 k p B q0 q2]
 refine { haus' := ?_,prec' := ?_ }
 ·
  intro c hc;apply Subtype.ext
  refine IsHausdorff.haus' (I:=span {(p:z156 k p)}) (M:=z156 k p) (c:z156 k p) fun n => ?_
  have hcn:=hc n;rw [SModEq.zero,span_singleton_pow,smul_eq_mul,mul_top] at hcn ⊢;exact (z185 k p B q0 q2 n c).mpr hcn
 ·
  intro f hf
  have hfW:∀ {m n : ℕ},m ≤ n →
    (f m:z156 k p) ≡ (f n:z156 k p)
     [SMOD (span {(p:z156 k p)} ^ m•(⊤ : Submodule (z156 k p) (z156 k p)))]:=by
   intro m n hmn;have h:=hf hmn;rw [SModEq.sub_mem,span_singleton_pow,smul_eq_mul,mul_top] at h ⊢;exact (z185 k p B q0 q2 m (f m - f n)).mpr h
  obtain ⟨L,hL⟩:=IsPrecomplete.prec' (I:=span {(p:z156 k p)}) (M:=z156 k p)
   (fun m=>(f m:z156 k p)) hfW
  have q1:L∈z180 k p B:=by
   rw [z182];intro n hn;have hLn:=hL n;rw [SModEq.sub_mem,span_singleton_pow,smul_eq_mul,mul_top] at hLn
   have hLn':L - (f n:z156 k p)∈span {(p:z156 k p) ^ n}:=by
    simpa [neg_sub] using Submodule.neg_mem _ hLn
   obtain ⟨s,hs,hfs⟩:=(z182 k p B _).mp (f n).2 n hn
   refine ⟨s,hs,?_⟩
   have : L - s=(L - (f n:z156 k p))+((f n:z156 k p) - s):=by ring
   rw [this];exact Ideal.add_mem _ hLn' hfs
  refine ⟨⟨L,q1⟩,fun n => ?_⟩
  rw [SModEq.sub_mem,span_singleton_pow,smul_eq_mul,mul_top];rw [← z185 k p B q0 q2 n];have hLn:=hL n;rw [SModEq.sub_mem,span_singleton_pow,smul_eq_mul,mul_top] at hLn;simpa using hLn
lemma z190 (c:z181 k p B) :
  ∃ a:k,(c:z156 k p).coeff 0=z157 k p a:=by
 obtain ⟨s,hs,hcs⟩:=(z182 k p B _).mp c.2 1 le_rfl;obtain ⟨a,ha⟩:=z175 k p B 1 hs
 refine ⟨a,?_⟩
 have q0:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp (by simpa using hcs);rw [← WittVector.constantCoeff_apply,map_sub,sub_eq_zero] at q0;simp only [WittVector.constantCoeff_apply] at q0;exact q0.trans ha
noncomputable def z191:z181 k p B →+* k :=
 {
  toFun:=fun c=>(z190 k p B c).choose
  map_one':=by
   apply z158 k p;rw [← (z190 k p B 1).choose_spec,map_one]
   exact WittVector.one_coeff_zero (p:=p) (R:=z155 k p)
  map_mul':=fun x y=>by
   apply z158 k p;rw [map_mul,← (z190 k p B _).choose_spec,← (z190 k p B x).choose_spec,← (z190 k p B y).choose_spec];exact WittVector.mul_coeff_zero _ _
  map_zero':=by
   apply z158 k p;rw [← (z190 k p B 0).choose_spec,map_zero];exact WittVector.zero_coeff p (z155 k p) 0
  map_add':=fun x y=>by
   apply z158 k p;rw [map_add,← (z190 k p B _).choose_spec,← (z190 k p B x).choose_spec,← (z190 k p B y).choose_spec]
   exact WittVector.add_coeff_zero _ _ }
lemma z192 (c:z181 k p B) :
  z157 k p (z191 k p B c)=(c:z156 k p).coeff 0 :=
 (z190 k p B c).choose_spec.symm
lemma z193 (q0:z152 k p B)
  (q1:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x) :
  Surjective (z191 k p B):=by
 intro a;obtain ⟨s,hs,hs0⟩:=z176 k p B q0 q1 1 a;obtain ⟨c,hc⟩:=z183 k p B q0 q1 1 le_rfl hs
 refine ⟨c,z158 k p ?_⟩
 rw [z192,← hs0];have q2:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp (by simpa using hc);rw [← WittVector.constantCoeff_apply,map_sub,sub_eq_zero] at q2;exact q2
lemma z194 (q0:z152 k p B)
  (q1:∀ x:k,∃ f:z150 k p B 1 →₀ k,f.sum (fun e c=>c ^ p*z151 k p e)=x)
  [IsDiscreteValuationRing (z181 k p B)] :
  RingHom.ker (z191 k p B)=maximalIdeal (z181 k p B):=by
 rw [z188 k p B q0 q1];ext c;rw [RingHom.mem_ker,← (z158 k p).eq_iff,map_zero,z192,← WittVector.mem_span_p_iff_coeff_zero_eq_zero];simpa using z185 k p B q0 q1 1 c
end CohenRingConstruction
section CohenRingMap
variable (R:Type) [CommRing R] [IsLocalRing R]
variable (p : ℕ) [hp:Fact p.Prime] [CharP (ResidueField R) p]
lemma z195 {A B:Type*} [CommRing A] [CommRing B] (f:A →+* B)
  (w:WittVector p A) (n : ℕ) :
  f (WittVector.ghostComponent n w)=WittVector.ghostComponent n (WittVector.map f w):=by
 rw [WittVector.ghostComponent_apply,WittVector.ghostComponent_apply,aeval_wittPolynomial,aeval_wittPolynomial,map_sum]
 refine Finset.sum_congr rfl fun i _ => ?_
 rw [map_mul,map_pow,map_pow,map_natCast,WittVector.map_coeff]
omit [IsLocalRing R] [CharP (ResidueField R) p] in
lemma z196 {I:Ideal R} (hpI:(p:R)∈I) :
    ∀ (j : ℕ) {x y:R},x - y∈I→x ^ (p ^ j) - y ^ (p ^ j)∈I ^ (j+1):=by
  intro j
  induction j with
  | zero =>
    intro x y hxy;simpa using hxy
  | succ j ih =>
    intro x y hxy;let u:R:=x ^ (p ^ j);let v:R:=y ^ (p ^ j);have hδ : u - v∈I ^ (j+1):=ih hxy;let δ : R:=u - v
    have hu:u=v + δ := by dsimp only [δ];ring
    have q6:x ^ (p ^ (j+1)) - y ^ (p ^ (j+1))=(v + δ) ^ p - v ^ p:=by
      rw [pow_succ,pow_mul,pow_mul];change u ^ p - v ^ p=(v + δ) ^ p - v ^ p;rw [hu]
    rw [q6,add_pow,Finset.sum_range_succ]
    have q1:v ^ p * δ ^ (p - p)*(p.choose p:R)=v ^ p:=by simp
    rw [q1,add_sub_cancel_right]
    refine Ideal.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hi0:i=0
    · subst hi0
      simp only [pow_zero,one_mul,tsub_zero,Nat.choose_zero_right,Nat.cast_one,mul_one];have q2 : δ ^ p∈(I ^ (j+1)) ^ p:=Ideal.pow_mem_pow hδ p;rw [← pow_mul] at q2
      have hge:j+2 ≤ (j+1)*p:=by
        have hp2:2 ≤ p:=hp.out.two_le
        calc j+2 ≤ (j+1)*2:=by omega
          _ ≤ (j+1)*p:=Nat.mul_le_mul_left (j+1) hp2
      exact pow_le_pow_right hge q2
    · have q4:p∣p.choose i:=hp.out.dvd_choose_self hi0 hi
      obtain ⟨c,hc⟩:=q4
      have q0:(p.choose i:R)∈I:=by
        rw [hc,Nat.cast_mul];exact I.mul_mem_right (c:R) hpI
      have hδ_pow : δ ^ (p - i)∈I ^ (j+1):=by
        have q3:1 ≤ p - i:=by omega
        obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' q3
        have hm1 : δ ^ (p - i) = δ ^ m * δ := by rw [hm,pow_succ]
        rw [hm1];exact (I ^ (j+1)).mul_mem_left (δ ^ m) hδ
      have q5:(p.choose i:R) * δ ^ (p - i)∈I ^ (j+2):=by
        have : I ^ (j+2)=I*I ^ (j+1):=by rw [pow_succ']
        rw [this];exact mul_mem_mul q0 hδ_pow
      have heq:v ^ i * δ ^ (p - i)*(p.choose i:R)=v ^ i*((p.choose i:R) * δ ^ (p - i)):=by ring
      rw [heq];exact (I ^ (j+2)).mul_mem_left (v ^ i) q5
noncomputable def z197:ResidueField R→R:=fun a=>(residue_surjective a).choose
lemma z198 (a:ResidueField R) : residue R (z197 R a)=a:=(residue_surjective a).choose_spec
noncomputable def z199 (n : ℕ) (hn:1 ≤ n) :
  R⧸maximalIdeal R ^ n →+* ResidueField R :=
 Ideal.Quotient.lift (maximalIdeal R ^ n) (residue R) fun r hr=>by
  rw [residue_eq_zero_iff];exact pow_le_self (by omega) hr
lemma z200 (n : ℕ) (hn:1 ≤ n) (r:R) :
  z199 R n hn (Ideal.Quotient.mk (maximalIdeal R ^ n) r)=residue R r :=
 rfl
omit [CharP (ResidueField R) p] in
lemma z201 (q0:(p:R)∈maximalIdeal R)
  (n : ℕ) (hn:1 ≤ n) (w1 w2:WittVector p (R⧸maximalIdeal R ^ n))
  (h:∀ i ≤ n,z199 R n hn (w1.coeff i)=z199 R n hn (w2.coeff i)) :
  WittVector.ghostComponent n w1=WittVector.ghostComponent n w2:=by
 rw [WittVector.ghostComponent_apply,WittVector.ghostComponent_apply,aeval_wittPolynomial,aeval_wittPolynomial]
 refine Finset.sum_congr rfl fun i hi => ?_
 rw [Finset.mem_range] at hi
 by_cases hin:i=n
 ·
  rw [hin]
  have hp0:((p:R⧸maximalIdeal R ^ n) ^ n)=0:=by
   have : (p:R⧸maximalIdeal R ^ n) ^ n=Ideal.Quotient.mk (maximalIdeal R ^ n) ((p:R) ^ n):=by simp
   rw [this,Ideal.Quotient.eq_zero_iff_mem];exact Ideal.pow_mem_pow q0 n
  simp [hp0]
 ·
  have hilt:i < n:=by omega
  obtain ⟨a1,ha1⟩:=Ideal.Quotient.mk_surjective (w1.coeff i);obtain ⟨a2,ha2⟩:=Ideal.Quotient.mk_surjective (w2.coeff i)
  have q3:residue R a1=residue R a2:=by
   have h1:=h i (by omega);rw [← ha1,← ha2,z200,z200] at h1;exact h1
  have q2:a1 - a2∈maximalIdeal R:=by
   rw [← residue_eq_zero_iff,map_sub,q3,sub_self]
  have q6:=z196 R p q0 (n - i) q2
  have q1:(p:R) ^ i*(a1 ^ (p ^ (n - i)) - a2 ^ (p ^ (n - i)))∈maximalIdeal R ^ n:=by
   have hpi:(p:R) ^ i∈maximalIdeal R ^ i:=Ideal.pow_mem_pow q0 i;have q5:=mul_mem_mul hpi q6;rw [← pow_add] at q5
   have hge:n ≤ i+(n - i+1):=by omega
   exact pow_le_pow_right hge q5
  rw [← ha1,← ha2,← sub_eq_zero]
  have q4:(p:R⧸maximalIdeal R ^ n) ^ i*(Ideal.Quotient.mk (maximalIdeal R ^ n) a1) ^ (p ^ (n - i)) -
    (p:R⧸maximalIdeal R ^ n) ^ i *
    (Ideal.Quotient.mk (maximalIdeal R ^ n) a2) ^ (p ^ (n - i)) =
    Ideal.Quotient.mk (maximalIdeal R ^ n)
     ((p:R) ^ i*(a1 ^ (p ^ (n - i)) - a2 ^ (p ^ (n - i)))):=by
   simp [map_mul,map_sub,map_pow,mul_sub]
  rw [q4,Ideal.Quotient.eq_zero_iff_mem];exact q1
noncomputable def z202 (n : ℕ) (z:WittVector p (ResidueField R)) :
  WittVector p (R⧸maximalIdeal R ^ n) :=
 WittVector.mk p fun i=>Ideal.Quotient.mk (maximalIdeal R ^ n) (z197 R (z.coeff i))
omit [CharP (ResidueField R) p] in
lemma z203 (n : ℕ) (hn:1 ≤ n) (z:WittVector p (ResidueField R)) :
  WittVector.map (z199 R n hn) (z202 R p n z)=z:=by
 ext i;simp [z202,z200,z198]
noncomputable def z204 (q0:(p:R)∈maximalIdeal R) (n : ℕ) :
  WittVector p (ResidueField R) →+* R⧸maximalIdeal R ^ n :=
 if hn:1 ≤ n then
  {
   toFun:=fun z=>WittVector.ghostComponent n (z202 R p n z)
   map_one':=by
    have h1:WittVector.ghostComponent n (z202 R p n 1)=WittVector.ghostComponent n (1:WittVector p (R⧸maximalIdeal R ^ n)):=by
     refine z201 R p q0 n hn _ _ fun i _ => ?_
     rw [← WittVector.map_coeff,← WittVector.map_coeff,z203,map_one]
    rw [h1,map_one]
   map_mul':=fun z1 z2=>by
    have q1:WittVector.ghostComponent n (z202 R p n (z1*z2))=WittVector.ghostComponent n (z202 R p n z1*z202 R p n z2):=by
     refine z201 R p q0 n hn _ _ fun i _ => ?_
     rw [← WittVector.map_coeff,← WittVector.map_coeff,z203,
      map_mul,z203,z203]
    rw [q1,map_mul]
   map_zero':=by
    have h0:WittVector.ghostComponent n (z202 R p n 0)=WittVector.ghostComponent n (0:WittVector p (R⧸maximalIdeal R ^ n)):=by
     refine z201 R p q0 n hn _ _ fun i _ => ?_
     rw [← WittVector.map_coeff,← WittVector.map_coeff,z203,map_zero]
    rw [h0,map_zero]
   map_add':=fun z1 z2=>by
    have q2:WittVector.ghostComponent n (z202 R p n (z1+z2))=WittVector.ghostComponent n (z202 R p n z1+z202 R p n z2):=by
     refine z201 R p q0 n hn _ _ fun i _ => ?_
     rw [← WittVector.map_coeff,← WittVector.map_coeff,z203,
      map_add,z203,z203]
    rw [q2,map_add] }
 else
  have hn0:n=0:=by omega
  have : Subsingleton (R⧸maximalIdeal R ^ n):=by
   rw [hn0,pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
  {
   toFun:=fun _=>0
   map_one':=Subsingleton.elim _ _
   map_mul':=fun _ _=>Subsingleton.elim _ _
   map_zero':=rfl
   map_add':=fun _ _=>Subsingleton.elim _ _ }
omit [CharP (ResidueField R) p] in
lemma z205 (q0:(p:R)∈maximalIdeal R)
  (n : ℕ) (hn:1 ≤ n) (z:WittVector p (ResidueField R))
  (w:WittVector p (R⧸maximalIdeal R ^ n))
  (hw:WittVector.map (z199 R n hn) w=z) :
  z204 R p q0 n z=WittVector.ghostComponent n w:=by
 simp only [z204,dif_pos hn,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk]
 refine z201 R p q0 n hn _ _ fun i _ => ?_
 rw [← WittVector.map_coeff,← WittVector.map_coeff,z203,hw]
omit [CharP (ResidueField R) p] in
lemma z206 (q0:(p:R)∈maximalIdeal R) (n : ℕ)
  (a:ResidueField R) :
  z204 R p q0 n (WittVector.teichmuller p a)=(Ideal.Quotient.mk (maximalIdeal R ^ n) (z197 R a)) ^ (p ^ n):=by
 by_cases hn:1 ≤ n
 ·
  rw [z205 R p q0 n hn _
   (WittVector.teichmuller p (Ideal.Quotient.mk (maximalIdeal R ^ n) (z197 R a)))]
  · exact WittVector.ghostComponent_teichmuller p _ n
  · rw [WittVector.map_teichmuller,z200,z198]
 ·
  have hn0:n=0:=by omega
  have : Subsingleton (R⧸maximalIdeal R ^ n):=by
   rw [hn0,pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
  exact Subsingleton.elim _ _
omit [CharP (ResidueField R) p] in
lemma z207 (q2:(p:R)∈maximalIdeal R) (n : ℕ)
  (z:WittVector p (ResidueField R)) :
  Ideal.Quotient.factor (pow_le_pow_right n.le_succ) (z204 R p q2 (n+1) z)=z204 R p q2 n (WittVector.frobenius z):=by
 by_cases hn:1 ≤ n
 ·
  let fac:R⧸maximalIdeal R ^ (n+1) →+* R⧸maximalIdeal R ^ n:=Ideal.Quotient.factor (pow_le_pow_right n.le_succ)
  have h1:z204 R p q2 (n+1) z=WittVector.ghostComponent (n+1) (z202 R p (n+1) z):=by
   simp [z204]
  rw [h1,z195,← WittVector.ghostComponent_frobenius]
  symm
  refine z205 R p q2 n hn _ _ ?_
  have q4:(z199 R n hn).comp fac=z199 R (n+1) (Nat.succ_le_succ (Nat.zero_le n)):=by
   ext r;rfl
  have q0:WittVector.map (z199 R n hn)
    (WittVector.frobenius (WittVector.map fac (z202 R p (n+1) z))) =
    WittVector.frobenius (WittVector.map (z199 R n hn) (WittVector.map fac (z202 R p (n+1) z))):=by
   ext i;simp only [WittVector.map_coeff,WittVector.coeff_frobenius];let u:=WittVector.map fac (z202 R p (n+1) z)
   have q3:∀ P:MvPolynomial ℕ ℤ,z199 R n hn (MvPolynomial.aeval u.coeff P)=MvPolynomial.aeval (fun j=>z199 R n hn (u.coeff j)) P:=by
    intro P
    refine MvPolynomial.induction_on (motive:=fun P =>
     z199 R n hn (MvPolynomial.aeval u.coeff P) =
     MvPolynomial.aeval (fun j=>z199 R n hn (u.coeff j)) P) P ?_ ?_ ?_
    · intro c;simp
    · intro P1 P2 h1 h2;simp [h1,h2]
    · intro P1 m ih;simp [ih]
   exact q3 (WittVector.frobeniusPoly p i)
  have q1:WittVector.map (z199 R n hn) (WittVector.map fac (z202 R p (n+1) z))=WittVector.map (z199 R (n+1) (Nat.succ_le_succ (Nat.zero_le n))) (z202 R p (n+1) z):=by
   ext i;simp only [WittVector.map_coeff];simpa only [RingHom.comp_apply] using RingHom.congr_fun q4 ((z202 R p (n+1) z).coeff i)
  change WittVector.map (z199 R n hn)
    (WittVector.frobenius (WittVector.map fac (z202 R p (n+1) z)))=WittVector.frobenius z
  rw [q0,q1,z203]
 ·
  have hn0:n=0:=by omega
  have : Subsingleton (R⧸maximalIdeal R ^ n):=by
   rw [hn0,pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
  exact Subsingleton.elim _ _
omit [CharP (ResidueField R) p] in
lemma z208 (q4:(p:R)∈maximalIdeal R) (n : ℕ)
  (z:WittVector p (ResidueField R)) (y:R)
  (hy:Ideal.Quotient.mk (maximalIdeal R ^ n) y=z204 R p q4 n z) :
  Ideal.Quotient.mk (maximalIdeal R ^ (n+1)) ((p:R)*y)=z204 R p q4 (n+1) (WittVector.verschiebung z):=by
 by_cases hn:1 ≤ n
 ·
  let w:WittVector p (R⧸maximalIdeal R ^ (n+1)):=z202 R p (n+1) z
  have hV:z204 R p q4 (n+1) (WittVector.verschiebung z)=WittVector.ghostComponent (n+1) (WittVector.verschiebung w):=by
   refine z205 R p q4 (n+1) (Nat.succ_le_succ (Nat.zero_le n)) _ _ ?_
   rw [WittVector.map_verschiebung,z203]
  rw [hV,WittVector.ghostComponent_verschiebung];obtain ⟨y0,hy0⟩:=Ideal.Quotient.mk_surjective (WittVector.ghostComponent n w)
  have q2:Ideal.Quotient.mk (maximalIdeal R ^ n) y0=z204 R p q4 n z:=by
   let fac:R⧸maximalIdeal R ^ (n+1) →+* R⧸maximalIdeal R ^ n:=Ideal.Quotient.factor (pow_le_pow_right n.le_succ);have q6:fac (Ideal.Quotient.mk (maximalIdeal R ^ (n+1)) y0)=Ideal.Quotient.mk (maximalIdeal R ^ n) y0:=rfl;rw [← q6,hy0,z195]
   symm
   refine z205 R p q4 n hn z (WittVector.map fac w) ?_
   have q5:(z199 R n hn).comp fac=z199 R (n+1) (Nat.succ_le_succ (Nat.zero_le n)):=by
    ext r;rfl
   have q0:WittVector.map (z199 R n hn) (WittVector.map fac w)=WittVector.map (z199 R (n+1) (Nat.succ_le_succ (Nat.zero_le n))) w:=by
    ext i;simp only [WittVector.map_coeff];simpa only [RingHom.comp_apply] using RingHom.congr_fun q5 (w.coeff i)
   rw [q0,z203]
  have q1:y - y0∈maximalIdeal R ^ n:=by
   rw [← Ideal.Quotient.eq_zero_iff_mem,map_sub,hy,q2,sub_self]
  have q3:(p:R)*(y - y0)∈maximalIdeal R ^ (n+1):=by
   rw [pow_succ'];exact mul_mem_mul q4 q1
  rw [← hy0,← map_natCast (Ideal.Quotient.mk (maximalIdeal R ^ (n+1))) p,← map_mul,← sub_eq_zero,← map_sub,Ideal.Quotient.eq_zero_iff_mem];simpa [mul_sub] using q3
 ·
  have hn0:n=0:=by omega
  subst hn0
  have h1:Ideal.Quotient.mk (maximalIdeal R ^ 1) ((p:R)*y)=0:=by
   rw [pow_one,Ideal.Quotient.eq_zero_iff_mem];exact (maximalIdeal R).mul_mem_right y q4
  have h2:z204 R p q4 1 (WittVector.verschiebung z)=0:=by
   have hV:z204 R p q4 1 (WittVector.verschiebung z)=WittVector.ghostComponent 1 (WittVector.verschiebung (z202 R p 1 z)):=by
    refine z205 R p q4 1 le_rfl _ _ ?_
    rw [WittVector.map_verschiebung,z203]
   rw [hV,WittVector.ghostComponent_verschiebung]
   have hp0:(p:R⧸maximalIdeal R ^ 1)=0:=by
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal R ^ 1)) p,Ideal.Quotient.eq_zero_iff_mem,pow_one];exact q4
   rw [hp0,zero_mul]
  rw [h1,h2]
noncomputable def z209 (B:Set (ResidueField R)) (n : ℕ) (e:B →₀ ℕ) :
  R⧸maximalIdeal R ^ n :=
 e.prod fun b m=>(Ideal.Quotient.mk (maximalIdeal R ^ n) (z197 R b.1)) ^ m
lemma z210 (B:Set (ResidueField R)) (n : ℕ) : z209 R B n 0=1:=by
 simp [z209]
lemma z211 (B:Set (ResidueField R)) (n : ℕ) (e1 e2:B →₀ ℕ) :
  z209 R B n (e1+e2)=z209 R B n e1*z209 R B n e2:=by
 simp only [z209]
 exact Finsupp.prod_add_index' (fun _=>pow_zero _) (fun _ _ _=>pow_add _ _ _)
omit [CharP (ResidueField R) p] in
lemma z212 (q0:(p:R)∈maximalIdeal R) (B:Set (ResidueField R))
  (n : ℕ) (q:B →₀ ℕ) :
  z209 R B n ((p ^ n)•q)=z204 R p q0 n (q.prod fun b m=>WittVector.teichmuller p (b:ResidueField R) ^ m):=by
 classical
 have h1:z209 R B n ((p ^ n)•q)=(z209 R B n q) ^ (p ^ n):=by
  simp only [z209,Finsupp.prod]
  have q1:((p ^ n)•q).support=q.support:=by
   ext b;simp only [Finsupp.mem_support_iff,Finsupp.smul_apply,smul_eq_mul,ne_eq,mul_eq_zero,pow_ne_zero n hp.out.ne_zero,false_or]
  rw [q1,← Finset.prod_pow]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [Finsupp.smul_apply,smul_eq_mul];rw [mul_comm,pow_mul]
 rw [h1];simp only [z209,Finsupp.prod,map_prod,map_pow,← Finset.prod_pow]
 refine Finset.prod_congr rfl fun b _ => ?_
 rw [z206,← pow_mul,mul_comm,pow_mul]
lemma z213 (q11:(p:R)∈maximalIdeal R)
  (B:Set (ResidueField R)) (q8:z152 (ResidueField R) p B)
  (q10:∀ x:ResidueField R,∃ f:z150 (ResidueField R) p B 1 →₀ ResidueField R,f.sum (fun e c=>c ^ p*z151 (ResidueField R) p e)=x) :
  ∀ (n : ℕ) (f:z150 (ResidueField R) p B n →₀ WittVector p (ResidueField R)),
   f.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1) ∈
    span {(p:z156 (ResidueField R) p) ^ n} →
   f.sum (fun e z=>z204 R p q11 n z*z209 R B n e.1)=0:=by
 classical
 intro n
 induction n with
 | zero =>
  intro f _
  have : Subsingleton (R⧸maximalIdeal R ^ 0):=by
   rw [pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
  exact Subsingleton.elim _ _
 | succ n ih =>
  intro f hf;let k:=ResidueField R
  have hfp:f.sum (fun e z=>z161 k p (n+1) z*z166 k p B e.1) ∈
    span {(p:z156 k p)}:=by
   have hle:span {(p:z156 k p) ^ (n+1)} ≤ span {(p:z156 k p)}:=by
    rw [Ideal.span_singleton_le_span_singleton];exact dvd_pow_self _ (Nat.succ_ne_zero n)
   exact hle hf
  have hx0:(f.sum (fun e z=>z161 k p (n+1) z*z166 k p B e.1)).coeff 0=0:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp hfp
  let f0:z150 k p B (n+1) →₀ k:=f.mapRange (fun z=>z.coeff 0) (WittVector.zero_coeff p k 0)
  have q6:f0.sum (fun e c=>c ^ (p ^ (n+1))*z151 k p e)=0:=by
   apply z158 k p;rw [map_zero,← hx0]
   change z157 k p (f0.sum (fun e c=>c ^ (p ^ (n+1))*z151 k p e))=WittVector.constantCoeff (f.sum (fun e z=>z161 k p (n+1) z*z166 k p B e.1))
   rw [Finsupp.sum_mapRange_index (fun _=>by simp [zero_pow (pow_ne_zero (n+1) hp.out.ne_zero)])]
   rw [Finsupp.sum,Finsupp.sum,map_sum,map_sum]
   refine Finset.sum_congr rfl fun e _ => ?_
   rw [map_mul,map_mul];congr 1
   · exact (z162 k p (n+1) (f e) 0).symm
   · exact (z169 k p B e.1).symm
  have q2:f0=0:=(z154 k p q8 q10 (n+1)).1 f0 q6
  have q5:∀ e:z150 k p B (n+1),(f e).coeff 0=0:=fun e=>by
   have:=congrArg (fun g:z150 k p B (n+1) →₀ k=>g e) q2
   simpa [f0] using this
  have q9:∀ e:z150 k p B (n+1),f e=WittVector.verschiebung ((f e).shift 1):=fun e=>by
   have h1:=WittVector.eq_iterate_verschiebung (x:=f e) (n:=1) (fun i hi=>by
    have : i=0:=by omega
    subst this
    exact q5 e)
   simpa using h1
  let x':z156 k p:=f.sum (fun e z=>z161 k p n (z.shift 1)*z166 k p B e.1)
  have q15:f.sum (fun e z=>z161 k p (n+1) z*z166 k p B e.1)=(p:z156 k p)*x':=by
   dsimp only [x'];rw [Finsupp.sum,Finsupp.sum,Finset.mul_sum]
   refine Finset.sum_congr rfl fun e _ => ?_
   conv_lhs=>rw [q9 e,z164]
   ring
  have q7:x'∈span {(p:z156 k p) ^ n}:=by
   rw [q15] at hf;obtain ⟨w,hw⟩:=mem_span_singleton.mp hf;rw [mem_span_singleton]
   refine ⟨w,?_⟩
   have q13:(x' - (p:z156 k p) ^ n*w)*(p:z156 k p)=0:=by
    rw [pow_succ'] at hw
    linear_combination hw
   exact sub_eq_zero.mp (WittVector.eq_zero_of_p_mul_eq_zero _ q13)
  let qOf:z150 k p B (n+1)→(B →₀ ℕ):=fun e=>e.1.mapRange (· / p ^ n) (Nat.zero_div _)
  let rOf:z150 k p B (n+1)→z150 k p B n:=fun e =>
   ⟨e.1.mapRange (· % p ^ n) (Nat.zero_mod _),fun b=>by
    simp only [Finsupp.mapRange_apply]
    exact Nat.mod_lt _ (pow_pos hp.out.pos n)⟩
  have q1:∀ e:z150 k p B (n+1),e.1=(p ^ n)•qOf e+(rOf e).1:=fun e=>by
   ext b;simp only [qOf,rOf,Finsupp.add_apply,Finsupp.smul_apply,Finsupp.mapRange_apply,smul_eq_mul];exact (Nat.div_add_mod (e.1 b) (p ^ n)).symm
  let qW:z150 k p B (n+1)→WittVector p k:=fun e =>
   (qOf e).prod fun b m=>WittVector.teichmuller p (b:k) ^ m
  let g:z150 k p B n →₀ WittVector p k:=f.sum fun e z=>Finsupp.single (rOf e) (z.shift 1*qW e)
  have q18:g.sum (fun r z=>z161 k p n z*z166 k p B r.1)=x':=by
   dsimp only [g,x']
   rw [Finsupp.sum_sum_index (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
   refine Finsupp.sum_congr fun e _ => ?_
   rw [Finsupp.sum_single_index (by simp),map_mul,mul_assoc];congr 1;rw [q1 e,z168,z170]
  have q17:g.sum (fun r z=>z204 R p q11 n z*z209 R B n r.1)=f.sum (fun e z=>z204 R p q11 n (z.shift 1)*z209 R B n e.1):=by
   dsimp only [g]
   rw [Finsupp.sum_sum_index (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
   refine Finsupp.sum_congr fun e _ => ?_
   rw [Finsupp.sum_single_index (by simp),map_mul,mul_assoc];congr 1;rw [q1 e,z211,z212]
  have hIH:f.sum (fun e z=>z204 R p q11 n (z.shift 1)*z209 R B n e.1)=0:=by
   rw [← q17];exact ih g (q18.symm▸q7)
  have q14:∀ e:z150 k p B (n+1),∃ y:R,Ideal.Quotient.mk (maximalIdeal R ^ n) y=z204 R p q11 n ((f e).shift 1):=fun e=>Ideal.Quotient.mk_surjective _
  let y:z150 k p B (n+1)→R:=fun e=>(q14 e).choose
  have hy:∀ e,Ideal.Quotient.mk (maximalIdeal R ^ n) (y e)=z204 R p q11 n ((f e).shift 1):=fun e=>(q14 e).choose_spec
  let q16:(B →₀ ℕ)→R:=fun e=>e.prod fun b m=>z197 R b.1 ^ m
  have q4:∀ m (e:B →₀ ℕ),Ideal.Quotient.mk (maximalIdeal R ^ m) (q16 e)=z209 R B m e:=fun m e=>by
   simp only [q16,z209,Finsupp.prod,map_prod,map_pow]
  have q3 : ∑ e∈f.support,y e*q16 e.1∈maximalIdeal R ^ n:=by
   rw [← Ideal.Quotient.eq_zero_iff_mem,map_sum]
   have heq : ∑ e∈f.support,Ideal.Quotient.mk (maximalIdeal R ^ n) (y e*q16 e.1)=f.sum (fun e z=>z204 R p q11 n (z.shift 1)*z209 R B n e.1):=by
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul,hy e,q4]
   rw [heq,hIH]
  have q0:(p:R) * ∑ e∈f.support,y e*q16 e.1∈maximalIdeal R ^ (n+1):=by
   rw [pow_succ'];exact mul_mem_mul q11 q3
  have q12:Ideal.Quotient.mk (maximalIdeal R ^ (n+1)) ((p:R) * ∑ e∈f.support,y e*q16 e.1)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr q0;rw [Finset.mul_sum,map_sum] at q12;rw [← q12,Finsupp.sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← mul_assoc,map_mul,q4,q9 e,z208 R p q11 n ((f e).shift 1) (y e) (hy e)]
lemma z214 (q2:(p:R)∈maximalIdeal R)
  (B:Set (ResidueField R)) (q0:z152 (ResidueField R) p B)
  (q1:∀ x:ResidueField R,∃ f:z150 (ResidueField R) p B 1 →₀ ResidueField R,f.sum (fun e c=>c ^ p*z151 (ResidueField R) p e)=x)
  (n : ℕ) (f1 f2:z150 (ResidueField R) p B n →₀ WittVector p (ResidueField R))
  (q6:f1.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1) -
   f2.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1) ∈
   span {(p:z156 (ResidueField R) p) ^ n}) :
  f1.sum (fun e z=>z204 R p q2 n z*z209 R B n e.1)=f2.sum (fun e z=>z204 R p q2 n z*z209 R B n e.1):=by
 classical
 have q4:(f1 - f2).sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1)=f1.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1) -
   f2.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1):=by
  rw [sub_eq_add_neg,Finsupp.sum_add_index' (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
  have q7:(-f2).sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1)+f2.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1)=0:=by
   rw [← Finsupp.sum_add_index' (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
   simp
  rw [eq_neg_of_add_eq_zero_left q7,sub_eq_add_neg]
 have q5:(f1 - f2).sum (fun e z=>z204 R p q2 n z*z209 R B n e.1)=f1.sum (fun e z=>z204 R p q2 n z*z209 R B n e.1) -
   f2.sum (fun e z=>z204 R p q2 n z*z209 R B n e.1):=by
  rw [sub_eq_add_neg,Finsupp.sum_add_index' (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
  have q7:(-f2).sum (fun e z=>z204 R p q2 n z*z209 R B n e.1)+f2.sum (fun e z=>z204 R p q2 n z*z209 R B n e.1)=0:=by
   rw [← Finsupp.sum_add_index' (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
   simp
  rw [eq_neg_of_add_eq_zero_left q7,sub_eq_add_neg]
 have q3:=z213 R p q2 B q0 q1 n (f1 - f2) (q4.symm▸q6);rw [q5,sub_eq_zero] at q3;exact q3
lemma z215 (B:Set (ResidueField R)) (n : ℕ) (hn:1 ≤ n)
  (c:z181 (ResidueField R) p B) :
  ∃ f:z150 (ResidueField R) p B n →₀ WittVector p (ResidueField R),
   (c:z156 (ResidueField R) p) -
    f.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1) ∈
    span {(p:z156 (ResidueField R) p) ^ n}:=by
 obtain ⟨s,hs,hcs⟩:=(z182 (ResidueField R) p B _).mp c.2 n hn;obtain ⟨f,rfl⟩:=(z173 (ResidueField R) p B n s).mp hs;exact ⟨f,hcs⟩
noncomputable def z216 (q6:(p:R)∈maximalIdeal R)
    (B:Set (ResidueField R)) (q2:z152 (ResidueField R) p B)
    (q5:∀ x:ResidueField R,∃ f:z150 (ResidueField R) p B 1 →₀ ResidueField R,f.sum (fun e c=>c ^ p*z151 (ResidueField R) p e)=x)
    (n : ℕ) : z181 (ResidueField R) p B →+* R⧸maximalIdeal R ^ n :=
  if hn:1 ≤ n then
    let q0:(z150 (ResidueField R) p B n →₀ WittVector p (ResidueField R))→R⧸maximalIdeal R ^ n:=fun f=>f.sum (fun e z=>z204 R p q6 n z*z209 R B n e.1)
    let q7:(z150 (ResidueField R) p B n →₀ WittVector p (ResidueField R))→z156 (ResidueField R) p:=fun f=>f.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1)
    let toF:z181 (ResidueField R) p B→R⧸maximalIdeal R ^ n:=fun c=>q0 (z215 R p B n hn c).choose
    have q9:∀ (c:z181 (ResidueField R) p B)
        (f:z150 (ResidueField R) p B n →₀ WittVector p (ResidueField R)),
        (c:z156 (ResidueField R) p) - q7 f∈span {(p:z156 (ResidueField R) p) ^ n} →
        toF c=q0 f:=fun c f hf=>by
      refine z214 R p q6 B q2 q5 n _ f ?_
      have hch:=(z215 R p B n hn c).choose_spec
      have : q7 (z215 R p B n hn c).choose - q7 f=((c:z156 (ResidueField R) p) - q7 f) -
          ((c:z156 (ResidueField R) p) - q7 (z215 R p B n hn c).choose):=by ring
      rw [this];exact Ideal.sub_mem _ hf hch
    { toFun:=toF
      map_one':=by
        let e0:z150 (ResidueField R) p B n:=⟨0,fun _=>pow_pos hp.out.pos n⟩
        have h1:toF 1=q0 (Finsupp.single e0 1):=by
          refine q9 1 (Finsupp.single e0 1) ?_
          dsimp only [q7];rw [Finsupp.sum_single_index (by simp),map_one,one_mul,z167];simp
        rw [h1];dsimp only [q0];rw [Finsupp.sum_single_index (by simp),map_one,one_mul,z210]
      map_zero':=by
        have h0:toF 0=q0 0:=by
          refine q9 0 0 ?_
          simp [q7]
        rw [h0];simp [q0]
      map_add':=fun c1 c2=>by
        classical
        let f1:=(z215 R p B n hn c1).choose;let f2:=(z215 R p B n hn c2).choose;have hf1:=(z215 R p B n hn c1).choose_spec;have hf2:=(z215 R p B n hn c2).choose_spec
        have q11:toF (c1+c2)=q0 (f1+f2):=by
          refine q9 (c1+c2) (f1+f2) ?_
          have hW:q7 (f1+f2)=q7 f1+q7 f2:=Finsupp.sum_add_index' (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])
          rw [hW]
          have : ((c1+c2:z181 (ResidueField R) p B) : z156 (ResidueField R) p) -
              (q7 f1+q7 f2)=((c1:z156 (ResidueField R) p) - q7 f1) +
              ((c2:z156 (ResidueField R) p) - q7 f2):=by
            push_cast;ring
          rw [this];exact Ideal.add_mem _ hf1 hf2
        rw [q11]
        exact Finsupp.sum_add_index' (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])
      map_mul':=fun c1 c2=>by
        classical
        let f1:=(z215 R p B n hn c1).choose;let f2:=(z215 R p B n hn c2).choose;have hf1:=(z215 R p B n hn c1).choose_spec;have hf2:=(z215 R p B n hn c2).choose_spec
        let qOf:z150 (ResidueField R) p B n→z150 (ResidueField R) p B n→(B →₀ ℕ):=fun e1 e2=>(e1.1+e2.1).mapRange (· / p ^ n) (Nat.zero_div _)
        let rOf:z150 (ResidueField R) p B n→z150 (ResidueField R) p B n→z150 (ResidueField R) p B n :=
          fun e1 e2=>⟨(e1.1+e2.1).mapRange (· % p ^ n) (Nat.zero_mod _),fun b=>by
            simp only [Finsupp.mapRange_apply]
            exact Nat.mod_lt _ (pow_pos hp.out.pos n)⟩
        have q4:∀ e1 e2,e1.1+e2.1=(p ^ n)•qOf e1 e2+(rOf e1 e2).1:=fun e1 e2=>by
          ext b;simp only [qOf,rOf,Finsupp.add_apply,Finsupp.smul_apply,Finsupp.mapRange_apply,smul_eq_mul];exact (Nat.div_add_mod (e1.1 b+e2.1 b) (p ^ n)).symm
        let qW:z150 (ResidueField R) p B n→z150 (ResidueField R) p B n→WittVector p (ResidueField R):=fun e1 e2=>(qOf e1 e2).prod fun b m=>WittVector.teichmuller p (b:ResidueField R) ^ m
        let q8:z150 (ResidueField R) p B n →₀ WittVector p (ResidueField R):=f1.sum fun e1 z1=>f2.sum fun e2 z2=>Finsupp.single (rOf e1 e2) (z1*z2*qW e1 e2)
        have q3:q7 q8=q7 f1*q7 f2:=by
          dsimp only [q7,q8]
          rw [Finsupp.sum_sum_index (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
          rw [Finsupp.sum,Finsupp.sum,Finset.sum_mul]
          refine Finset.sum_congr rfl fun e1 _ => ?_
          rw [Finsupp.sum_sum_index (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
          rw [Finsupp.sum]
          conv_rhs=>rw [Finsupp.sum,Finset.mul_sum]
          refine Finset.sum_congr rfl fun e2 _ => ?_
          rw [Finsupp.sum_single_index (by simp)]
          have ht:z166 (ResidueField R) p B e1.1*z166 (ResidueField R) p B e2.1=z161 (ResidueField R) p n (qW e1 e2)*z166 (ResidueField R) p B (rOf e1 e2).1:=by
            rw [← z168,q4 e1 e2,z168,z170]
          calc z161 (ResidueField R) p n (f1 e1*f2 e2*qW e1 e2)*z166 (ResidueField R) p B (rOf e1 e2).1
              = z161 (ResidueField R) p n (f1 e1)*z161 (ResidueField R) p n (f2 e2) *
                (z161 (ResidueField R) p n (qW e1 e2)*z166 (ResidueField R) p B (rOf e1 e2).1):=by
                  simp only [map_mul];ring
            _=z161 (ResidueField R) p n (f1 e1)*z161 (ResidueField R) p n (f2 e2)*(z166 (ResidueField R) p B e1.1*z166 (ResidueField R) p B e2.1):=by rw [ht]
            _=(z161 (ResidueField R) p n (f1 e1)*z166 (ResidueField R) p B e1.1)*(z161 (ResidueField R) p n (f2 e2)*z166 (ResidueField R) p B e2.1):=by ring
        have q1:q0 q8=q0 f1*q0 f2:=by
          dsimp only [q0,q8]
          rw [Finsupp.sum_sum_index (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
          rw [Finsupp.sum,Finsupp.sum,Finset.sum_mul]
          refine Finset.sum_congr rfl fun e1 _ => ?_
          rw [Finsupp.sum_sum_index (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
          rw [Finsupp.sum]
          conv_rhs=>rw [Finsupp.sum,Finset.mul_sum]
          refine Finset.sum_congr rfl fun e2 _ => ?_
          rw [Finsupp.sum_single_index (by simp)]
          have hr:z209 R B n e1.1*z209 R B n e2.1=z204 R p q6 n (qW e1 e2)*z209 R B n (rOf e1 e2).1:=by
            rw [← z211,q4 e1 e2,z211,z212]
          calc z204 R p q6 n (f1 e1*f2 e2*qW e1 e2)*z209 R B n (rOf e1 e2).1
              = z204 R p q6 n (f1 e1)*z204 R p q6 n (f2 e2) *
                (z204 R p q6 n (qW e1 e2)*z209 R B n (rOf e1 e2).1):=by
                  simp only [map_mul];ring
            _=z204 R p q6 n (f1 e1)*z204 R p q6 n (f2 e2)*(z209 R B n e1.1*z209 R B n e2.1):=by rw [hr]
            _=(z204 R p q6 n (f1 e1)*z209 R B n e1.1)*(z204 R p q6 n (f2 e2)*z209 R B n e2.1):=by ring
        have q10:toF (c1*c2)=q0 q8:=by
          refine q9 (c1*c2) q8 ?_
          rw [q3]
          have : ((c1*c2:z181 (ResidueField R) p B) : z156 (ResidueField R) p) -
              q7 f1*q7 f2 =
              ((c1:z156 (ResidueField R) p) - q7 f1)*(c2:z156 (ResidueField R) p) +
              q7 f1*((c2:z156 (ResidueField R) p) - q7 f2):=by
            push_cast;ring
          rw [this];exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hf1) (Ideal.mul_mem_left _ _ hf2)
        rw [q10,q1] }
  else
    have hn0:n=0:=by omega
    have : Subsingleton (R⧸maximalIdeal R ^ n):=by
      rw [hn0,pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
    { toFun:=fun _=>0
      map_one':=Subsingleton.elim _ _
      map_mul':=fun _ _=>Subsingleton.elim _ _
      map_zero':=rfl
      map_add':=fun _ _=>Subsingleton.elim _ _ }
lemma z217 (q1:(p:R)∈maximalIdeal R)
  (B:Set (ResidueField R)) (q0:z152 (ResidueField R) p B)
  (q2:∀ x:ResidueField R,∃ f:z150 (ResidueField R) p B 1 →₀ ResidueField R,f.sum (fun e c=>c ^ p*z151 (ResidueField R) p e)=x)
  (n : ℕ) (hn:1 ≤ n) (c:z181 (ResidueField R) p B)
  (f:z150 (ResidueField R) p B n →₀ WittVector p (ResidueField R))
  (hf:(c:z156 (ResidueField R) p) -
   f.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1) ∈
   span {(p:z156 (ResidueField R) p) ^ n}) :
  z216 R p q1 B q0 q2 n c=f.sum (fun e z=>z204 R p q1 n z*z209 R B n e.1):=by
 simp only [z216,dif_pos hn,RingHom.coe_mk,MonoidHom.coe_mk,OneHom.coe_mk]
 refine z214 R p q1 B q0 q2 n _ f ?_
 have hch:=(z215 R p B n hn c).choose_spec
 have q3:(z215 R p B n hn c).choose.sum
    (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1) -
   f.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1) =
   ((c:z156 (ResidueField R) p) -
    f.sum (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1)) -
   ((c:z156 (ResidueField R) p) -
    (z215 R p B n hn c).choose.sum
     (fun e z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B e.1)):=by ring
 rw [q3];exact Ideal.sub_mem _ hf hch
lemma z218 (q3:(p:R)∈maximalIdeal R)
  (B:Set (ResidueField R)) (q0:z152 (ResidueField R) p B)
  (q1:∀ x:ResidueField R,∃ f:z150 (ResidueField R) p B 1 →₀ ResidueField R,f.sum (fun e c=>c ^ p*z151 (ResidueField R) p e)=x)
  (n : ℕ) (c:z181 (ResidueField R) p B) :
  Ideal.Quotient.factor (pow_le_pow_right n.le_succ)
    (z216 R p q3 B q0 q1 (n+1) c) =
   z216 R p q3 B q0 q1 n c:=by
 classical
 by_cases hn:1 ≤ n
 ·
  obtain ⟨f,hf⟩:=z215 R p B (n+1) (by omega) c;have h1:=z217 R p q3 B q0 q1 (n+1) (by omega) c f hf
  let qOf:z150 (ResidueField R) p B (n+1)→(B →₀ ℕ):=fun e=>e.1.mapRange (· / p ^ n) (Nat.zero_div _)
  let rOf:z150 (ResidueField R) p B (n+1)→z150 (ResidueField R) p B n:=fun e =>
   ⟨e.1.mapRange (· % p ^ n) (Nat.zero_mod _),fun b=>by
    simp only [Finsupp.mapRange_apply]
    exact Nat.mod_lt _ (pow_pos hp.out.pos n)⟩
  have q2:∀ e:z150 (ResidueField R) p B (n+1),e.1=(p ^ n)•qOf e+(rOf e).1:=fun e=>by
   ext b;simp only [qOf,rOf,Finsupp.add_apply,Finsupp.smul_apply,Finsupp.mapRange_apply,smul_eq_mul];exact (Nat.div_add_mod (e.1 b) (p ^ n)).symm
  let qW:z150 (ResidueField R) p B (n+1)→WittVector p (ResidueField R):=fun e =>
   (qOf e).prod fun b m=>WittVector.teichmuller p (b:ResidueField R) ^ m
  let g:z150 (ResidueField R) p B n →₀ WittVector p (ResidueField R):=f.sum fun e z=>Finsupp.single (rOf e) (WittVector.frobenius z*qW e)
  have q5:g.sum (fun r z=>z161 (ResidueField R) p n z*z166 (ResidueField R) p B r.1)=f.sum (fun e z=>z161 (ResidueField R) p (n+1) z*z166 (ResidueField R) p B e.1):=by
   dsimp only [g]
   rw [Finsupp.sum_sum_index (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
   refine Finsupp.sum_congr fun e _ => ?_
   rw [Finsupp.sum_single_index (by simp),map_mul,mul_assoc,← z163];congr 1;rw [q2 e,z168,z170]
  have hle:span {(p:z156 (ResidueField R) p) ^ (n+1)} ≤ span {(p:z156 (ResidueField R) p) ^ n}:=by
   rw [Ideal.span_singleton_le_span_singleton];exact pow_dvd_pow _ n.le_succ
  have h2:=z217 R p q3 B q0 q1 n hn c g (q5.symm▸hle hf);rw [h1,h2];dsimp only [g]
  rw [Finsupp.sum_sum_index (fun _=>by simp) (fun _ _ _=>by rw [map_add,add_mul])]
  rw [Finsupp.sum,Finsupp.sum,map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finsupp.sum_single_index (by simp),map_mul,z207,map_mul,mul_assoc];congr 1
  have q4:Ideal.Quotient.factor (pow_le_pow_right n.le_succ) (z209 R B (n+1) e.1)=z209 R B n e.1:=by
   simp only [z209,Finsupp.prod,map_prod,map_pow];rfl
  rw [q4,q2 e,z211,z212]
 ·
  have hn0:n=0:=by omega
  have : Subsingleton (R⧸maximalIdeal R ^ n):=by
   rw [hn0,pow_zero];exact Ideal.Quotient.subsingleton_iff.mpr Ideal.one_eq_top
  exact Subsingleton.elim _ _
lemma z219 (q2:(p:R)∈maximalIdeal R)
  (B:Set (ResidueField R)) (q0:z152 (ResidueField R) p B)
  (q1:∀ x:ResidueField R,∃ f:z150 (ResidueField R) p B 1 →₀ ResidueField R,f.sum (fun e c=>c ^ p*z151 (ResidueField R) p e)=x)
  (c:z181 (ResidueField R) p B) :
  z199 R 1 le_rfl (z216 R p q2 B q0 q1 1 c)=z191 (ResidueField R) p B c:=by
 obtain ⟨f,hf⟩:=z215 R p B 1 le_rfl c;rw [z217 R p q2 B q0 q1 1 le_rfl c f hf];apply z158 (ResidueField R) p;rw [z192];have q3:=(WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp (by simpa using hf);rw [← WittVector.constantCoeff_apply,map_sub,sub_eq_zero] at q3;simp only [WittVector.constantCoeff_apply] at q3;rw [q3]
 change z157 (ResidueField R) p (z199 R 1 le_rfl _)=WittVector.constantCoeff (f.sum (fun e z=>z161 (ResidueField R) p 1 z*z166 (ResidueField R) p B e.1))
 rw [Finsupp.sum,Finsupp.sum,map_sum,map_sum,map_sum]
 refine Finset.sum_congr rfl fun e _ => ?_
 rw [map_mul,map_mul,map_mul];congr 1
 ·
  have q4:z199 R 1 le_rfl (z204 R p q2 1 (f e))=((f e).coeff 0) ^ p:=by
   have h1:z204 R p q2 1 (f e)=WittVector.ghostComponent 1 (z202 R p 1 (f e)):=by
    simp [z204]
   rw [h1,WittVector.ghostComponent_apply,aeval_wittPolynomial];simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,one_mul,tsub_zero,pow_one,tsub_self];rw [map_add,map_mul,map_pow,map_natCast];have hp0:(p:ResidueField R)=0:=CharP.cast_eq_zero (ResidueField R) p;rw [hp0,zero_mul,add_zero];simp [z202,z200,z198]
  rw [q4,WittVector.constantCoeff_apply,z162,pow_one]
 ·
  have hr1:z199 R 1 le_rfl (z209 R B 1 e.1)=z151 (ResidueField R) p e:=by
   simp only [z209,z151,Finsupp.prod,map_prod,map_pow]
   refine Finset.prod_congr rfl fun b _ => ?_
   rw [z200,z198]
  rw [hr1,WittVector.constantCoeff_apply,z169];rfl
lemma z220 [IsAdicComplete (maximalIdeal R) R]
  (q6:(p:R)∈maximalIdeal R)
  (B:Set (ResidueField R)) (q4:z152 (ResidueField R) p B)
  (q5:∀ x:ResidueField R,∃ f:z150 (ResidueField R) p B 1 →₀ ResidueField R,f.sum (fun e c=>c ^ p*z151 (ResidueField R) p e)=x) :
  ∃ phi:z181 (ResidueField R) p B →+* R,∀ c,residue R (phi c)=z191 (ResidueField R) p B c:=by
 let q3:z181 (ResidueField R) p B → ℕ → R:=fun c n=>(Ideal.Quotient.mk_surjective (z216 R p q6 B q4 q5 n c)).choose
 have q1:∀ c n,Ideal.Quotient.mk (maximalIdeal R ^ n) (q3 c n)=z216 R p q6 B q4 q5 n c:=fun c n=>(Ideal.Quotient.mk_surjective (z216 R p q6 B q4 q5 n c)).choose_spec
 have q2:∀ c {m n : ℕ},m ≤ n→q3 c m ≡ q3 c n [SMOD (maximalIdeal R ^ m•(⊤ : Submodule R R))]:=by
  intro c m n hmn;rw [SModEq.sub_mem,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,sub_eq_zero,q1 c m]
  have q8:∀ {a b : ℕ} (hab:a ≤ b),
    Ideal.Quotient.factor (pow_le_pow_right hab)
     (z216 R p q6 B q4 q5 b c) =
    z216 R p q6 B q4 q5 a c:=by
   intro a b hab
   induction b,hab using Nat.le_induction with
   | base=>simp
   | succ b hab ih =>
    rw [← Ideal.Quotient.factor_comp_apply (pow_le_pow_right b.le_succ)
     (pow_le_pow_right hab),z218,ih]
  rw [← q8 hmn,← q1 c n];rfl
 let toF:z181 (ResidueField R) p B→R:=fun c=>(IsPrecomplete.prec' (I:=maximalIdeal R) (M:=R) (q3 c) (q2 c)).choose
 have q0:∀ c n,Ideal.Quotient.mk (maximalIdeal R ^ n) (toF c)=z216 R p q6 B q4 q5 n c:=by
  intro c n;have hL:=(IsPrecomplete.prec' (I:=maximalIdeal R) (M:=R) (q3 c) (q2 c)).choose_spec n;rw [SModEq.sub_mem,smul_eq_mul,mul_top] at hL;have q7:Ideal.Quotient.mk (maximalIdeal R ^ n) (q3 c n - toF c)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr hL;rw [map_sub,sub_eq_zero,q1 c n] at q7;exact q7.symm
 let phi:z181 (ResidueField R) p B →+* R :=
  {
   toFun:=toF
   map_one':=by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (toF 1 - 1) fun n => ?_)
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,q0,map_one,map_one,sub_self]
   map_zero':=by
    refine IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (toF 0) fun n => ?_
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,q0,map_zero]
   map_add':=fun x y=>by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (toF (x+y) - (toF x+toF y)) fun n => ?_)
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,map_add,q0,q0,q0,map_add,sub_self]
   map_mul':=fun x y=>by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (toF (x*y) - toF x*toF y) fun n => ?_)
    rw [SModEq.zero,smul_eq_mul,mul_top,← Ideal.Quotient.eq_zero_iff_mem,map_sub,map_mul,q0,q0,q0,map_mul,sub_self] }
 refine ⟨phi,fun c => ?_⟩
 rw [← z200 R 1 le_rfl];change z199 R 1 le_rfl (Ideal.Quotient.mk (maximalIdeal R ^ 1) (toF c))=_;rw [q0 c 1];exact z219 R p q6 B q4 q5 c
end CohenRingMap
lemma z221 {S R:Type*} [CommRing S] [IsLocalRing S]
  [IsAdicComplete (maximalIdeal S) S]
  [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  (f:S →+* R) (q11:∀ u∈maximalIdeal S,f u∈maximalIdeal R)
  (q10:Surjective ((residue R).comp f))
  {d : ℕ} (xs:Fin d→R) (q1:maximalIdeal R=span (Set.range xs))
  (q7:∀ i:Fin d,∃ s∈maximalIdeal S,f s=xs i) :
  Surjective f:=by
 have q6:∀ k (u:S),u∈maximalIdeal S ^ k→f u∈maximalIdeal R ^ k:=by
  intro k u hu
  have hle:(maximalIdeal S).map f ≤ maximalIdeal R:=by
   rw [map_le_iff_le_comap];exact q11
  have q15:=z7 hle k;rw [← Ideal.map_pow] at q15;exact q15 (mem_map_of_mem f hu)
 have q5:∀ k : ℕ,∀ y∈maximalIdeal R ^ k,∃ s∈maximalIdeal S ^ k,y - f s∈maximalIdeal R ^ (k+1):=by
  intro k
  induction k with
  | zero =>
   intro y _;obtain ⟨s,hs⟩:=q10 (residue R y)
   refine ⟨s,by simp,?_⟩
   rw [pow_one,← residue_eq_zero_iff,map_sub];change residue R y - ((residue R).comp f) s=0;rw [hs,sub_self]
  | succ k ih =>
   intro y hy;rw [pow_succ] at hy
   refine Submodule.mul_induction_on hy ?_ ?_
   ·
    intro a ha b hb;rw [q1,Submodule.mem_span_range_iff_exists_fun] at hb;obtain ⟨r,hr⟩:=hb
    have q13:∀ i:Fin d,∃ s∈maximalIdeal S ^ k,a*r i - f s∈maximalIdeal R ^ (k+1):=fun i =>
     ih (a*r i) ((maximalIdeal R ^ k).mul_mem_right (r i) ha)
    let s:Fin d→S:=fun i=>(q13 i).choose
    have q8:∀ i,s i∈maximalIdeal S ^ k:=fun i=>(q13 i).choose_spec.1
    have q2:∀ i,a*r i - f (s i)∈maximalIdeal R ^ (k+1):=fun i=>(q13 i).choose_spec.2
    let t:Fin d→S:=fun i=>(q7 i).choose
    have q9:∀ i,t i∈maximalIdeal S:=fun i=>(q7 i).choose_spec.1
    have q12:∀ i,f (t i)=xs i:=fun i=>(q7 i).choose_spec.2
    refine ⟨∑ i:Fin d,s i*t i,?_,?_⟩
    ·
     refine Ideal.sum_mem _ fun i _ => ?_
     rw [pow_succ];exact mul_mem_mul (q8 i) (q9 i)
    ·
     have hab:a*b = ∑ i:Fin d,(a*r i)*xs i:=by
      rw [← hr,Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [smul_eq_mul,mul_assoc]
     rw [hab,map_sum,← Finset.sum_sub_distrib]
     refine Ideal.sum_mem _ fun i _ => ?_
     rw [map_mul,q12 i,← sub_mul,pow_succ];have q4:xs i∈maximalIdeal R:=q1▸subset_span ⟨i,rfl⟩;exact mul_mem_mul (q2 i) q4
   ·
    intro a b ⟨sa,hsa_mem,hsa_diff⟩ ⟨sb,hsb_mem,hsb_diff⟩
    refine ⟨sa+sb,Ideal.add_mem _ hsa_mem hsb_mem,?_⟩
    rw [map_add]
    have : a+b - (f sa+f sb)=(a - f sa)+(b - f sb):=by ring
    rw [this];exact Ideal.add_mem _ hsa_diff hsb_diff
 intro y
 let step:(k : ℕ)→{ p:S // y - f p∈maximalIdeal R ^ k } →
   { p:S // y - f p∈maximalIdeal R ^ (k+1) }:=fun k prev =>
  let s:=(q5 k (y - f prev.1) prev.2).choose
  ⟨prev.1+s,by
   have q14:=(q5 k (y - f prev.1) prev.2).choose_spec.2;rw [map_add]
   have : y - (f prev.1+f s)=(y - f prev.1) - f s:=by ring
   rw [this]
   exact q14⟩
 let seq:(k : ℕ)→{ p:S // y - f p∈maximalIdeal R ^ k }:=Nat.rec ⟨0,by simp⟩ step
 have q0:∀ k : ℕ,(seq (k+1)).1 - (seq k).1∈maximalIdeal S ^ k:=fun k=>by
  change ((seq k).1+(q5 k (y - f (seq k).1) (seq k).2).choose) - (seq k).1∈maximalIdeal S ^ k;rw [add_sub_cancel_left];exact (q5 k (y - f (seq k).1) (seq k).2).choose_spec.1
 have q3:∀ {a b : ℕ},a ≤ b→(seq a).1 ≡ (seq b).1 [SMOD (maximalIdeal S ^ a•(⊤ : Submodule S S))]:=by
  intro a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top]
  induction b,hab using Nat.le_induction with
  | base=>simp
  | succ b hab ih =>
   have h1:(seq a).1 - (seq (b+1)).1=((seq a).1 - (seq b).1) - ((seq (b+1)).1 - (seq b).1):=by
    ring
   rw [h1];exact Ideal.sub_mem _ ih (pow_le_pow_right hab (q0 b))
 obtain ⟨T,hT⟩:=IsPrecomplete.prec' (I:=maximalIdeal S) (M:=S) (fun k=>(seq k).1) q3
 refine ⟨T,?_⟩
 refine sub_eq_zero.mp (IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (f T - y) fun k => ?_)
 rw [SModEq.zero,smul_eq_mul,mul_top];have hTk:=hT k;rw [SModEq.sub_mem,smul_eq_mul,mul_top] at hTk;have h1:f ((seq k).1 - T)∈maximalIdeal R ^ k:=q6 k _ hTk;have h2:y - f (seq k).1∈maximalIdeal R ^ k:=(seq k).2
 have h3:f T - y = -(f ((seq k).1 - T)+(y - f (seq k).1)):=by
  rw [map_sub];ring
 rw [h3];exact Submodule.neg_mem _ (Ideal.add_mem _ h1 h2)
end OMA.H2Proof
namespace OMA.H2Proof
section CohenStructureAndMain
private lemma z222 {R:Type*} [CommRing R] (n : ℕ) (a h:R) :
  ∃ q:R,(a+h) ^ n=a ^ n+(n:R)*a ^ (n - 1)*h+h ^ 2*q:=by
 induction n with
 | zero=>exact ⟨0,by simp⟩
 | succ n ih =>
  cases n with
  | zero=>exact ⟨0,by ring⟩
  | succ m =>
   obtain ⟨q,hq⟩:=ih
   refine ⟨((m+1 : ℕ) : R)*a ^ m+(a+h)*q,?_⟩
   rw [pow_succ',hq];push_cast;ring
private lemma z223 {R:Type*} [CommRing R] (p:Polynomial R) (a h:R) :
  ∃ q:R,p.eval (a+h)=p.eval a+(Polynomial.derivative p).eval a*h+h ^ 2*q:=by
 induction p using Polynomial.induction_on' with
 | add p₁ p₂ ih₁ ih₂ =>
  obtain ⟨q₁,hq₁⟩:=ih₁;obtain ⟨q₂,hq₂⟩:=ih₂
  refine ⟨q₁ + q₂,?_⟩
  simp only [Polynomial.eval_add,Polynomial.derivative_add,hq₁,hq₂];ring
 | monomial n c =>
  cases n with
  | zero =>
   refine ⟨0,?_⟩
   simp only [Polynomial.monomial_zero_left,Polynomial.eval_C,Polynomial.derivative_C,Polynomial.eval_zero];ring
  | succ m =>
   obtain ⟨q,hq⟩:=z222 (m+1) a h
   refine ⟨c*q,?_⟩
   simp only [Polynomial.eval_monomial,Polynomial.derivative_monomial,hq,Nat.add_sub_cancel];push_cast;ring
private lemma z224 (R:Type) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (q41:ringChar (ResidueField R)=0) :
    ∃ ψ : ResidueField R →+* R,∀ c:ResidueField R,residue R (ψ c)=c:=by
  classical
  have q1:∀ n : ℕ,n≠0→(n:ResidueField R)≠0:=by
    intro n hn h0;have q49:ringChar (ResidueField R)∣n:=ringChar.dvd h0;rw [q41,zero_dvd_iff] at q49;exact hn q49
  have q6:∀ n : ℕ,n≠0→IsUnit (n:R):=by
    intro n hn
    by_contra hnu
    have q48:(n:R)∈maximalIdeal R:=(mem_maximalIdeal (n:R)).mpr hnu;have hr:residue R (n:R)=0:=(residue_eq_zero_iff (n:R)).mpr q48;rw [map_natCast] at hr;exact q1 n hn hr
  have q10:∀ z : ℤ,z≠0→IsUnit (z:R):=by
    intro z hz;have hna:z.natAbs≠0:=Int.natAbs_ne_zero.mpr hz
    rcases Int.natAbs_eq z with h | h
    · have hz':(z:R)=((z.natAbs : ℕ) : R):=by
        rw [← Int.cast_natCast];exact congrArg Int.cast h
      rw [hz'];exact q6 z.natAbs hna
    · have hz':(z:R) = -((z.natAbs : ℕ) : R):=by
        rw [← Int.cast_natCast,← Int.cast_neg];exact congrArg Int.cast h
      rw [hz'];exact (q6 z.natAbs hna).neg
  let q47 : ℚ →+* R :=
    IsLocalization.lift (M:=nonZeroDivisors ℤ) (g:=Int.castRingHom R)
      (fun y=>q10 y.1 (nonZeroDivisors.ne_zero y.2))
  let IsSubfield:Subring R→Prop:=fun S=>∀ x∈S,x≠0→∃ y∈S,x*y=1
  have q30:IsSubfield q47.range:=by
    rintro _ ⟨q,rfl⟩ hne
    have hq0:q≠0:=fun h=>hne (by rw [h,map_zero])
    exact ⟨q47 q⁻¹,⟨q⁻¹,rfl⟩,by rw [← map_mul,mul_inv_cancel₀ hq0,map_one]⟩
  have q39:∃ K:Subring R,Maximal IsSubfield K:=by
    refine zorn_le₀ { S:Subring R | IsSubfield S } fun c hc hchain => ?_
    rcases Set.eq_empty_or_nonempty c with rfl | ⟨S₀,hS₀⟩
    · exact ⟨q47.range,q30,fun _ h=>False.elim h⟩
    · have q56:DirectedOn (· ≤ ·) c:=hchain.directedOn
      let U:Subring R :=
        { carrier := ⋃ S∈c,(S:Set R)
          mul_mem':=by
            rintro a b ⟨_,⟨S₁,rfl⟩,⟨_,⟨hS₁,rfl⟩,ha⟩⟩ ⟨_,⟨S₂,rfl⟩,⟨_,⟨hS₂,rfl⟩,hb⟩⟩;obtain ⟨S₃,hS₃,h13,h23⟩:=q56 S₁ hS₁ S₂ hS₂;exact Set.mem_biUnion hS₃ (S₃.mul_mem (h13 ha) (h23 hb))
          one_mem':=Set.mem_biUnion hS₀ S₀.one_mem
          add_mem':=by
            rintro a b ⟨_,⟨S₁,rfl⟩,⟨_,⟨hS₁,rfl⟩,ha⟩⟩ ⟨_,⟨S₂,rfl⟩,⟨_,⟨hS₂,rfl⟩,hb⟩⟩;obtain ⟨S₃,hS₃,h13,h23⟩:=q56 S₁ hS₁ S₂ hS₂;exact Set.mem_biUnion hS₃ (S₃.add_mem (h13 ha) (h23 hb))
          zero_mem':=Set.mem_biUnion hS₀ S₀.zero_mem
          neg_mem':=by
            rintro a ⟨_,⟨S₁,rfl⟩,⟨_,⟨hS₁,rfl⟩,ha⟩⟩
            exact Set.mem_biUnion hS₁ (S₁.neg_mem ha) }
      have q22:IsSubfield U:=by
        rintro x ⟨_,⟨S₁,rfl⟩,⟨_,⟨hS₁,rfl⟩,hx⟩⟩ hx0;obtain ⟨y,hy,hxy⟩:=hc hS₁ x hx hx0;exact ⟨y,Set.mem_biUnion hS₁ hy,hxy⟩
      refine ⟨U,q22,fun S hS x hx=>Set.mem_biUnion hS hx⟩
  obtain ⟨K,hK_max⟩:=q39;have q26:IsSubfield K:=hK_max.prop
  have q2:IsField K :=
    { exists_pair_ne:=⟨0,1,fun h=>zero_ne_one (congrArg Subtype.val h)⟩
      mul_comm:=mul_comm
      mul_inv_cancel:=fun {x} hx=>by
        obtain ⟨y,hy,hxy⟩:=q26 x.1 x.2 (fun h=>hx (Subtype.ext h))
        exact ⟨⟨y,hy⟩,Subtype.ext hxy⟩ }
  letI : Field K:=q2.toField
  haveI : CharZero K:=by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra hne
    have h0:((n:K) : R)=0:=congrArg Subtype.val hn
    have h0':(n:R)=0:=by simpa using h0
    have hr:residue R (n:R)=0:=by rw [h0',map_zero]
    rw [map_natCast] at hr;exact q1 n hne hr
  let ιK:K →+* ResidueField R:=(residue R).comp K.subtype
  have hιK_surj:Surjective ιK:=by
    by_contra hnot_surj
    simp only [Surjective,not_forall,not_exists] at hnot_surj;obtain ⟨α,hα⟩:=hnot_surj
    by_cases halg:∃ f:Polynomial K,f≠0∧Polynomial.eval₂ ιK α f=0
    · let P_deg : ℕ → Prop:=fun d =>
        ∃ f:Polynomial K,f≠0∧Polynomial.eval₂ ιK α f=0∧f.natDegree=d
      have q21:∃ d,P_deg d:=by
        obtain ⟨f,hf0,hfr⟩:=halg;exact ⟨f.natDegree,f,hf0,hfr,rfl⟩
      let d₀ := Nat.find q21;obtain ⟨f,hf_ne,hf_root,hf_deg⟩:=Nat.find_spec q21
      have q3:0 < f.natDegree:=by
        by_contra hle
        have h0:f.natDegree=0:=by omega
        have hfC:f=Polynomial.C (f.coeff 0):=Polynomial.eq_C_of_natDegree_eq_zero h0
        have hc0:f.coeff 0≠0:=fun h=>hf_ne (by rw [hfC,h,map_zero])
        rw [hfC,Polynomial.eval₂_C] at hf_root;exact hc0 (ιK.injective (by rw [hf_root,map_zero]))
      have q16:Irreducible f:=by
        refine ⟨fun hu => ?_,fun g h hgh => ?_⟩
        · have h0:=Polynomial.natDegree_eq_zero_of_isUnit hu
          omega
        · have q44:g≠0:=fun h0=>hf_ne (by rw [hgh,h0,zero_mul])
          have q46:h≠0:=fun h0=>hf_ne (by rw [hgh,h0,mul_zero])
          have q42:Polynomial.eval₂ ιK α g*Polynomial.eval₂ ιK α h=0:=by
            rw [← Polynomial.eval₂_mul,← hgh,hf_root]
          have q13:f.natDegree=g.natDegree+h.natDegree:=by
            rw [hgh,Polynomial.natDegree_mul q44 q46]
          rcases mul_eq_zero.mp q42 with hg0 | hh0
          · have hge:d₀ ≤ g.natDegree:=Nat.find_min' q21 ⟨g,q44,hg0,rfl⟩
            have q28:h.natDegree=0:=by omega
            right;rw [Polynomial.eq_C_of_natDegree_eq_zero q28]
            have hc0:h.coeff 0≠0:=fun h0 =>
              q46 (by rw [Polynomial.eq_C_of_natDegree_eq_zero q28,h0,map_zero])
            exact (isUnit_iff_ne_zero.mpr hc0).map Polynomial.C
          · have hge:d₀ ≤ h.natDegree:=Nat.find_min' q21 ⟨h,q46,hh0,rfl⟩
            have q32:g.natDegree=0:=by omega
            left;rw [Polynomial.eq_C_of_natDegree_eq_zero q32]
            have hc0:g.coeff 0≠0:=fun h0 =>
              q44 (by rw [Polynomial.eq_C_of_natDegree_eq_zero q32,h0,map_zero])
            exact (isUnit_iff_ne_zero.mpr hc0).map Polynomial.C
      have q25:Polynomial.derivative f≠0:=by
        intro h0
        have q36:=congrArg (fun p:Polynomial K=>p.coeff (f.natDegree - 1)) h0
        rw [Polynomial.coeff_derivative,Polynomial.coeff_zero,Nat.sub_add_cancel q3] at q36
        have q40:((f.natDegree - 1 : ℕ) : K)+1=(f.natDegree:K):=by
          exact_mod_cast Nat.sub_add_cancel q3
        rw [q40] at q36;have hlc:f.coeff f.natDegree≠0:=Polynomial.leadingCoeff_ne_zero.mpr hf_ne;have q54:((f.natDegree : ℕ) : K)≠0:=Nat.cast_ne_zero.mpr (by omega);exact mul_ne_zero hlc q54 q36
      have q20:(Polynomial.derivative f).natDegree < d₀ := by
        rw [Polynomial.natDegree_derivative];omega
      have q11:Polynomial.eval₂ ιK α (Polynomial.derivative f)≠0:=fun h0 =>
        Nat.find_min q21 q20 ⟨Polynomial.derivative f,q25,h0,rfl⟩
      let g:Polynomial R:=f.map K.subtype;let g':Polynomial R:=Polynomial.derivative g;have q24:g'=(Polynomial.derivative f).map K.subtype:=Polynomial.derivative_map f K.subtype;obtain ⟨x₀,hx₀⟩:=residue_surjective α
      have q8:∀ (p:Polynomial K) (y:R),
          residue R ((p.map K.subtype).eval y)=Polynomial.eval₂ ιK (residue R y) p:=by
        intro p y;rw [Polynomial.eval_map,Polynomial.hom_eval₂]
      have hg0:g.eval x₀ ∈ maximalIdeal R:=by
        rw [← residue_eq_zero_iff,q8 f x₀,hx₀,hf_root]
      have q4:IsUnit (g'.eval x₀):=by
        by_contra hnu
        have q48:g'.eval x₀ ∈ maximalIdeal R:=(mem_maximalIdeal _).mpr hnu;have hr:residue R (g'.eval x₀)=0:=(residue_eq_zero_iff _).mpr q48;rw [q24,q8 (Polynomial.derivative f) x₀,hx₀] at hr;exact q11 hr
      let q58:R:=((q4.unit⁻¹ : Rˣ) : R)
      have q7:g'.eval x₀ * q58=1:=by
        have h:=Units.mul_inv q4.unit
        simpa [q58] using congrArg (fun u:Rˣ=>(u:R)) h
      let step:(n : ℕ)→{ y:R // g.eval y∈maximalIdeal R ^ (n+1)∧y - x₀ ∈ maximalIdeal R } →
          { y:R // g.eval y∈maximalIdeal R ^ (n+2)∧y - x₀ ∈ maximalIdeal R }:=fun n prev =>
        let y:=prev.1;let h := -(q58*g.eval y)
        ⟨y+h,by
          have q34:h∈maximalIdeal R ^ (n+1):=Submodule.neg_mem _ ((maximalIdeal R ^ (n+1)).mul_mem_left q58 prev.2.1);have q52:h∈maximalIdeal R:=pow_le_self (Nat.succ_ne_zero n) q34
          refine ⟨?_,?_⟩
          · obtain ⟨q,hq⟩:=z223 g y h
            rw [hq]
            have q53:g.eval y+g'.eval y*h=g.eval y*((g'.eval x₀ - g'.eval y)*q58):=by
              dsimp only [h]
              calc g.eval y+g'.eval y * -(q58*g.eval y)
                  = g.eval y*(1 - g'.eval y*q58):=by ring
                _=g.eval y*(g'.eval x₀ * q58 - g'.eval y*q58):=by rw [q7]
                _=g.eval y*((g'.eval x₀ - g'.eval y)*q58):=by ring
            have hdiff_g':g'.eval x₀ - g'.eval y∈maximalIdeal R:=by
              obtain ⟨c,hc⟩:=Polynomial.sub_dvd_eval_sub x₀ y g';rw [hc]
              have hxy:x₀ - y∈maximalIdeal R:=by
                have : x₀ - y = -(y - x₀):=by ring
                rw [this];exact Submodule.neg_mem _ prev.2.2
              exact (maximalIdeal R).mul_mem_right c hxy
            have q27:g.eval y+g'.eval y*h∈maximalIdeal R ^ (n+2):=by
              rw [q53,pow_succ];exact mul_mem_mul prev.2.1 ((maximalIdeal R).mul_mem_right q58 hdiff_g')
            have q31:h ^ 2*q∈maximalIdeal R ^ (n+2):=by
              have hsq:h ^ 2∈maximalIdeal R ^ (n+2):=by
                have h2:h*h∈maximalIdeal R ^ (n+1)*maximalIdeal R ^ (n+1) :=
                  mul_mem_mul q34 q34
                rw [← pow_two,← pow_two,← pow_mul] at h2;exact pow_le_pow_right (by omega) h2
              exact (maximalIdeal R ^ (n+2)).mul_mem_right q hsq
            exact Ideal.add_mem _ q27 q31
          · have : y+h - x₀ = (y - x₀)+h:=by ring
            rw [this]
            exact Ideal.add_mem _ prev.2.2 q52⟩
      let seq:(n : ℕ)→{ y:R // g.eval y∈maximalIdeal R ^ (n+1)∧y - x₀ ∈ maximalIdeal R }:=Nat.rec ⟨x₀,by simpa using hg0,by simp⟩ step
      have q5:∀ n : ℕ,(seq (n+1)).1 - (seq n).1∈maximalIdeal R ^ (n+1):=fun n=>by
        change ((seq n).1 + -(q58*g.eval (seq n).1)) - (seq n).1∈maximalIdeal R ^ (n+1);rw [add_sub_cancel_left];exact Submodule.neg_mem _ ((maximalIdeal R ^ (n+1)).mul_mem_left q58 (seq n).2.1)
      have q19:∀ {a b : ℕ},a ≤ b→(seq a).1 ≡ (seq b).1 [SMOD (maximalIdeal R ^ a•(⊤ : Submodule R R))]:=by
        intro a b hab;rw [SModEq.sub_mem,smul_eq_mul,mul_top]
        induction b,hab using Nat.le_induction with
        | base=>simp
        | succ b hab ih =>
          have h1:(seq a).1 - (seq (b+1)).1=((seq a).1 - (seq b).1) - ((seq (b+1)).1 - (seq b).1):=by ring
          rw [h1];exact Ideal.sub_mem _ ih (pow_le_pow_right (by omega) (q5 b))
      obtain ⟨r,hr⟩:=IsPrecomplete.prec' (I:=maximalIdeal R) (M:=R) (fun n=>(seq n).1) q19
      have q23:residue R r = α := by
        have h1:=hr 1;rw [SModEq.sub_mem,smul_eq_mul,mul_top,pow_one] at h1
        have hrx₀ : r - x₀ ∈ maximalIdeal R:=by
          have : r - x₀ = ((seq 1).1 - x₀) - ((seq 1).1 - r):=by ring
          rw [this];exact Ideal.sub_mem _ (seq 1).2.2 h1
        have h0:=(residue_eq_zero_iff _).mpr hrx₀;rw [map_sub,sub_eq_zero] at h0;exact h0.trans hx₀
      have q15:g.eval r=0:=by
        refine IsHausdorff.haus' (I:=maximalIdeal R) (M:=R) (g.eval r) fun k => ?_
        rw [SModEq.zero,smul_eq_mul,mul_top];have hk:=hr k;rw [SModEq.sub_mem,smul_eq_mul,mul_top] at hk;obtain ⟨c,hc⟩:=Polynomial.sub_dvd_eval_sub (seq k).1 r g
        have q45:g.eval (seq k).1 - g.eval r∈maximalIdeal R ^ k:=by
          rw [hc];exact (maximalIdeal R ^ k).mul_mem_right c hk
        have hsk:g.eval (seq k).1∈maximalIdeal R ^ k:=pow_le_pow_right (Nat.le_succ k) (seq k).2.1
        have heq:g.eval r=g.eval (seq k).1 - (g.eval (seq k).1 - g.eval r):=by ring
        rw [heq];exact Ideal.sub_mem _ hsk q45
      let ev:Polynomial K →+* R:=Polynomial.eval₂RingHom K.subtype r
      have q14:span {f} ≤ RingHom.ker ev:=by
        rw [span_singleton_le_iff_mem,RingHom.mem_ker];change Polynomial.eval₂ K.subtype r f=0;rw [← Polynomial.eval_map];exact q15
      have q9:(span {f}).IsMaximal:=PrincipalIdealRing.isMaximal_of_irreducible q16
      have q0:RingHom.ker ev ≠ ⊤ := by
        intro q51;have h1:(1:Polynomial K)∈RingHom.ker ev:=q51.symm▸Submodule.mem_top;rw [RingHom.mem_ker,map_one] at h1;exact one_ne_zero h1
      have q18:RingHom.ker ev=span {f}:=(q9.eq_of_le q0 q14).symm
      haveI : (RingHom.ker ev).IsMaximal:=q18▸q9
      letI : Field (Polynomial K⧸RingHom.ker ev):=Ideal.Quotient.field (RingHom.ker ev)
      let q33:(Polynomial K⧸RingHom.ker ev) ≃+* ev.range:=RingHom.quotientKerEquivRange ev
      have q17:IsSubfield ev.range:=by
        intro x hx hx0;let u:Polynomial K⧸RingHom.ker ev:=q33.symm ⟨x,hx⟩
        have hu0:u≠0:=fun h=>hx0 (by
          have h1:(⟨x,hx⟩ : ev.range)=0:=by
            rw [← q33.apply_symm_apply ⟨x,hx⟩];change q33 u=0;rw [h,map_zero]
          exact congrArg Subtype.val h1)
        refine ⟨(q33 u⁻¹ : R),(q33 u⁻¹).2,?_⟩
        have q57:q33 u*q33 u⁻¹ = 1:=by rw [← map_mul,mul_inv_cancel₀ hu0,map_one]
        have q55:=congrArg Subtype.val q57;have hux:(q33 u:R)=x:=congrArg Subtype.val (q33.apply_symm_apply ⟨x,hx⟩);simpa [hux] using q55
      have q38:K ≤ ev.range:=by
        intro a ha;exact ⟨Polynomial.C ⟨a,ha⟩,by simp [ev]⟩
      have q43:K=ev.range:=hK_max.eq_of_le q17 q38;have q29:r∈K:=q43▸⟨Polynomial.X,by simp [ev]⟩;exact hα ⟨r,q29⟩ q23
    · push Not at halg
      obtain ⟨x,hx⟩:=residue_surjective α;let ev:Polynomial K →+* R:=Polynomial.eval₂RingHom K.subtype x
      have q12:∀ y:nonZeroDivisors (Polynomial K),IsUnit (ev y.1):=by
        intro y;have hy0:y.1≠0:=nonZeroDivisors.ne_zero y.2
        by_contra hnu
        have q48:ev y.1∈maximalIdeal R:=(mem_maximalIdeal _).mpr hnu;have hr:residue R (ev y.1)=0:=(residue_eq_zero_iff _).mpr q48
        have q50:residue R (ev y.1)=Polynomial.eval₂ ιK α y.1:=by
          change residue R (Polynomial.eval₂ K.subtype x y.1)=_;rw [Polynomial.hom_eval₂,hx]
        rw [q50] at hr;exact halg y.1 hy0 hr
      let F:FractionRing (Polynomial K) →+* R:=IsLocalization.lift (M:=nonZeroDivisors (Polynomial K)) (g:=ev) q12
      have q37:IsSubfield F.range:=by
        rintro _ ⟨q,rfl⟩ hne
        have hq0:q≠0:=fun h=>hne (by rw [h,map_zero])
        exact ⟨F q⁻¹,⟨q⁻¹,rfl⟩,by rw [← map_mul,mul_inv_cancel₀ hq0,map_one]⟩
      have q38:K ≤ F.range:=by
        intro a ha
        refine ⟨algebraMap (Polynomial K) (FractionRing (Polynomial K)) (Polynomial.C ⟨a,ha⟩),?_⟩
        rw [IsLocalization.lift_eq];simp [ev]
      have q43:K=F.range:=hK_max.eq_of_le q37 q38
      have q35:x∈K:=by
        rw [q43]
        refine ⟨algebraMap (Polynomial K) (FractionRing (Polynomial K)) Polynomial.X,?_⟩
        rw [IsLocalization.lift_eq];simp [ev]
      exact hα ⟨x,q35⟩ hx
  let eK:K ≃+* ResidueField R:=RingEquiv.ofBijective ιK ⟨ιK.injective,hιK_surj⟩
  refine ⟨K.subtype.comp eK.symm.toRingHom,fun c => ?_⟩
  change ιK (eK.symm c)=c;exact eK.apply_symm_apply c
private lemma z225 (R:Type) [CommRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] (q0:ringChar (ResidueField R)≠0)
  (hpR:(ringChar (ResidueField R) : R)=0) :
  ∃ ψ : ResidueField R →+* R,∀ c:ResidueField R,residue R (ψ c)=c:=by
 let k:=ResidueField R;let p : ℕ := ringChar k;have q1:p.Prime:=(CharP.char_is_prime_or_zero k p).resolve_right q0;have : Fact p.Prime:=⟨q1⟩;have : CharP k p:=ringChar.charP k
 have q4:(p:R)∈maximalIdeal R:=by
  rw [hpR];exact (maximalIdeal R).zero_mem
 obtain ⟨B,hBindep,hBspan⟩:=z153 k p;let C:Type:=z181 k p B;have : IsDiscreteValuationRing C:=z187 k p B hBindep hBspan;obtain ⟨phi,hphi_res⟩:=z220 R p q4 B hBindep hBspan
 have q2:RingHom.ker (z191 k p B) ≤ RingHom.ker phi:=by
  rw [z194 k p B hBindep hBspan,z188 k p B hBindep hBspan,span_singleton_le_iff_mem,RingHom.mem_ker,map_natCast];exact hpR
 let eC:(C⧸RingHom.ker (z191 k p B)) ≃+* k:=RingHom.quotientKerEquivOfSurjective (z193 k p B hBindep hBspan)
 let q3:(C⧸RingHom.ker (z191 k p B)) →+* R:=Ideal.Quotient.lift (RingHom.ker (z191 k p B)) phi (fun c hc=>q2 hc)
 refine ⟨q3.comp eC.symm.toRingHom,fun a => ?_⟩
 obtain ⟨c,rfl⟩:=z193 k p B hBindep hBspan a;have heq:eC.symm (z191 k p B c)=Ideal.Quotient.mk (RingHom.ker (z191 k p B)) c:=eC.symm_apply_eq.mpr rfl;change residue R (q3 (eC.symm (z191 k p B c)))=z191 k p B c;rw [heq];exact hphi_res c
private lemma z226 (R:Type) [CommRing R] [IsRegularLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] (hp0:(ringChar (ResidueField R) : R)=0) :
  ∃ d : ℕ,Nonempty (z0 (ResidueField R) d ≃+* R):=by
 let k:=ResidueField R
 have q6:∃ ψ : k →+* R,∀ c:k,residue R (ψ c)=c:=by
  by_cases h0:ringChar k=0
  · exact z224 R h0
  · exact z225 R h0 hp0
 obtain ⟨ψ,hψ⟩:=q6
 have hψ_loc:∀ c∈maximalIdeal k,ψ c∈maximalIdeal R:=by
  intro c hc
  have hc0:c=0:=by
   rw [maximalIdeal_eq_bot (R:=k),Ideal.mem_bot] at hc
   exact hc
  rw [hc0,map_zero];exact (maximalIdeal R).zero_mem
 let d : ℕ := (maximalIdeal R).spanFinrank;have q11:ringKrullDim R=(d:WithBot ℕ∞):=((isRegularLocalRing_iff R).mp ‹IsRegularLocalRing R›).symm;have q13:(maximalIdeal R).FG:=(maximalIdeal R).fg_of_isNoetherianRing;have q10:((maximalIdeal R).generators:Set R).Finite:=Submodule.FG.finite_generators q13;have : Finite (maximalIdeal R).generators:=q10.to_subtype
 have q1:Nat.card (maximalIdeal R).generators=d:=by
  rw [Nat.card_coe_set_eq];exact Submodule.FG.generators_ncard q13
 let q12:Fin d ≃ (maximalIdeal R).generators:=(Finite.equivFinOfCardEq q1).symm
 let xs:Fin d→R:=fun i=>(q12 i:R)
 have q4:∀ i:Fin d,xs i∈maximalIdeal R:=fun i =>
  ((maximalIdeal R).span_generators).le (subset_span (q12 i).2)
 have q2:maximalIdeal R=span (Set.range xs):=by
  rw [← (maximalIdeal R).span_generators];congr 1;ext r;constructor
  · intro hr;exact ⟨q12.symm ⟨r,hr⟩,by simp [xs]⟩
  · rintro ⟨i,rfl⟩;exact (q12 i).2
 obtain ⟨f,hf_C,hf_var,hf_loc⟩:=z24 ψ hψ_loc d xs q4
 have q7:Surjective ((residue R).comp f):=fun a =>
  ⟨z13 k d a,by simp only [RingHom.comp_apply,hf_C,hψ]⟩
 have q9:∀ i:Fin d,∃ s∈maximalIdeal (z0 k d),f s=xs i:=fun i =>
  ⟨z14 k i,by
   rw [z34 d]
   exact mem_sup_right (subset_span ⟨i,rfl⟩),hf_var i⟩
 have q5:Surjective f:=z221 f hf_loc q7 xs q2 q9
 have q8:ringKrullDim (z0 k d)=(d:WithBot ℕ∞):=by
  rw [z11 k d,ringKrullDim_eq_zero_of_isField (Field.toIsField k),zero_add]
 have q3:RingHom.ker f = ⊥ := by
  by_contra hne
  have q0:RingHom.ker f ≠ ⊤ := fun htop =>
   one_ne_zero (by
    have h1:(1:_)∈RingHom.ker f:=htop.symm▸Submodule.mem_top
    rwa [RingHom.mem_ker,map_one] at h1)
  have hlt:=z38 (I:=RingHom.ker f) hne q0;have heq:=ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective q5);rw [heq,q11,q8] at hlt;exact lt_irrefl _ hlt
 exact ⟨d,⟨RingEquiv.ofBijective f ⟨(RingHom.injective_iff_ker_eq_bot f).mpr q3,q5⟩⟩⟩
private lemma z227 (R:Type) [CommRing R] [IsRegularLocalRing R]
  [IsAdicComplete (maximalIdeal R) R]
  (q23:(ringChar (ResidueField R) : R)≠0)
  (q3:(ringChar (ResidueField R) : R)∉maximalIdeal R ^ 2) :
  ∃ (V:Type) (_:CommRing V) (_:IsDomain V) (_:IsDiscreteValuationRing V)
   (_:IsAdicComplete (maximalIdeal V) V) (pV:V) (n : ℕ),
   maximalIdeal V=span {pV}∧Nonempty (z0 V n ≃+* R):=by
 classical
 let k:=ResidueField R;let p : ℕ := ringChar k
 have q1:p≠0:=fun h0=>q23 (by change (p:R)=0;rw [h0,Nat.cast_zero])
 have q7:p.Prime:=(CharP.char_is_prime_or_zero k p).resolve_right q1;have : Fact p.Prime:=⟨q7⟩;have : CharP k p:=ringChar.charP k
 have q12:(p:R)∈maximalIdeal R:=by
  rw [← residue_eq_zero_iff,map_natCast];exact CharP.cast_eq_zero k p
 obtain ⟨B,hBindep,hBspan⟩:=z153 k p;let C:Type:=z181 k p B;have : IsDiscreteValuationRing C:=z187 k p B hBindep hBspan;have : IsAdicComplete (maximalIdeal C) C:=z189 k p B hBindep hBspan;have q17:maximalIdeal C=span {(p:C)}:=z188 k p B hBindep hBspan;obtain ⟨phi,hphi_res_eq⟩:=z220 R p q12 B hBindep hBspan
 have q4:∀ c∈maximalIdeal C,phi c∈maximalIdeal R:=by
  intro c hc;rw [← residue_eq_zero_iff,hphi_res_eq c,← RingHom.mem_ker,z194 k p B hBindep hBspan];exact hc
 let m:=maximalIdeal R;let V:=CotangentSpace R;let v:V:=m.toCotangent ⟨(p:R),q12⟩
 have q28:v≠0:=fun h=>q3 ((m.toCotangent_eq_zero ⟨(p:R),q12⟩).mp h)
 let W:Submodule k V:=Submodule.span k {v}
 have hfinV:Module.Finite k V:=by
  have : Module.Finite R V:=Module.Finite.of_surjective m.toCotangent m.toCotangent_surjective;exact Module.Finite.of_restrictScalars_finite R k V
 have q16:Module.finrank k W=1:=finrank_span_singleton q28
 have hrank:Module.finrank k (V⧸W)+1=Module.finrank k V:=by
  rw [← q16];exact Submodule.finrank_quotient_add_finrank W
 have q9:Module.finrank k V=m.spanFinrank:=(spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm;let n : ℕ := Module.finrank k (V⧸W);let b:=Module.finBasis k (V⧸W)
 have q24:∀ i:Fin n,∃ y:m,W.mkQ (m.toCotangent y)=b i:=fun i=>by
  obtain ⟨u,hu⟩:=Submodule.mkQ_surjective W (b i);obtain ⟨y,hy⟩:=m.toCotangent_surjective u;exact ⟨y,by rw [hy,hu]⟩
 let y:Fin n→m:=fun i=>(q24 i).choose
 have q8:∀ i:Fin n,W.mkQ (m.toCotangent (y i))=b i:=fun i=>(q24 i).choose_spec
 let ys:Fin n→R:=fun i=>(y i:R)
 let J:Ideal R:=span (insert (p:R) (Set.range ys))
 have hJm:J ≤ m:=by
  rw [span_le];rintro z (rfl | ⟨i,rfl⟩)
  · exact q12
  · exact (y i).2
 have q18:m ≤ J⊔m ^ 2:=by
  intro a ha;let u:V:=m.toCotangent ⟨a,ha⟩;have q11:W.mkQ u = ∑ i:Fin n,b.repr (W.mkQ u) i•b i:=(b.sum_repr (W.mkQ u)).symm
  let r:Fin n→R:=fun i=>(residue_surjective (b.repr (W.mkQ u) i)).choose
  have hr:∀ i:Fin n,residue R (r i)=b.repr (W.mkQ u) i:=fun i=>(residue_surjective (b.repr (W.mkQ u) i)).choose_spec
  have q27:u - ∑ i:Fin n,r i•m.toCotangent (y i)∈W:=by
   rw [← Submodule.ker_mkQ W,LinearMap.mem_ker,map_sub,map_sum,sub_eq_zero,q11]
   refine Finset.sum_congr rfl fun i _ => ?_
   rw [← q8 i,← hr i];have q30:(residue R (r i))•m.toCotangent (y i)=r i•m.toCotangent (y i):=algebraMap_smul k (r i) (m.toCotangent (y i));rw [← q30,LinearMap.map_smul]
  obtain ⟨c,hc⟩:=Submodule.mem_span_singleton.mp q27;obtain ⟨r0,hr0⟩:=residue_surjective c
  have q29:m.toCotangent (⟨a,ha⟩ - (r0•⟨(p:R),q12⟩ + ∑ i:Fin n,r i•y i))=0:=by
   rw [map_sub,map_add,map_sum,map_smul]
   have q13:c•v=r0•v:=by rw [← hr0];exact algebraMap_smul k r0 v
   have q32 : ∑ i:Fin n,m.toCotangent (r i•y i) = ∑ i:Fin n,r i•m.toCotangent (y i):=Finset.sum_congr rfl fun i _=>map_smul _ _ _
   rw [q32,← q13,hc];abel
  have q21:a - (r0*(p:R) + ∑ i:Fin n,r i*ys i)∈m ^ 2:=by
   have:=(m.toCotangent_eq_zero _).mp q29;simpa [ys,Submodule.coe_sum,smul_eq_mul] using this
  have q19:r0*(p:R) + ∑ i:Fin n,r i*ys i∈J:=by
   refine J.add_mem (J.mul_mem_left r0 (subset_span (Set.mem_insert _ _))) ?_
   exact J.sum_mem fun i _=>J.mul_mem_left (r i)
    (subset_span (Set.mem_insert_of_mem (p:R) ⟨i,rfl⟩))
  have q20:a=(r0*(p:R) + ∑ i:Fin n,r i*ys i)+(a - (r0*(p:R) + ∑ i:Fin n,r i*ys i)):=by ring
  rw [q20];exact Submodule.add_mem_sup q19 q21
 have q15:m=J:=by
  have q2:m ≤ J⊔m•m:=by simpa [pow_two,smul_eq_mul] using q18
  exact le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot m.fg_of_isNoetherianRing
   (maximalIdeal_le_jacobson ⊥) q2) hJm
 let xs:Fin (n+1)→R:=Fin.cons (p:R) ys
 have q6:maximalIdeal R=span (Set.range xs):=by
  change m=_;rw [q15];dsimp only [J];congr 1;ext z;constructor
  ·
   rintro (rfl | ⟨i,rfl⟩)
   · exact ⟨0,rfl⟩
   · exact ⟨i.succ,rfl⟩
  ·
   rintro ⟨i,rfl⟩
   refine Fin.cases ?_ ?_ i
   · exact Set.mem_insert _ _
   · intro j;exact Set.mem_insert_of_mem _ ⟨j,rfl⟩
 obtain ⟨f,hf_C,hf_var,hf_loc⟩:=z24 phi q4 n ys (fun i=>(y i).2)
 have q14:Surjective ((residue R).comp f):=fun a=>by
  obtain ⟨c,hc⟩:=z193 k p B hBindep hBspan a
  refine ⟨z13 C n c,?_⟩
  dsimp only [RingHom.comp_apply];rw [hf_C c,hphi_res_eq c,hc]
 have q26:∀ i:Fin (n+1),∃ s∈maximalIdeal (z0 C n),f s=xs i:=by
  intro i
  refine Fin.cases ?_ ?_ i
  ·
   refine ⟨z13 C n (p:C),?_,?_⟩
   ·
    rw [z34 n]
    refine mem_sup_left (mem_map_of_mem _ ?_)
    rw [q17];exact subset_span rfl
   ·
    rw [hf_C,map_natCast];rfl
  ·
   intro j
   refine ⟨z14 C j,?_,hf_var j⟩
   rw [z34 n];exact mem_sup_right (subset_span ⟨j,rfl⟩)
 have q10:Surjective f:=z221 f hf_loc q14 xs q6 q26;have q25:ringKrullDim C=1:=IsDiscreteValuationRing.ringKrullDim_eq_one C
 have q22:ringKrullDim (z0 C n)=((n+1 : ℕ) : WithBot ℕ∞):=by
  rw [z11 C n,q25];push_cast;rw [add_comm]
 have q31:ringKrullDim R=((n+1 : ℕ) : WithBot ℕ∞):=by
  rw [((isRegularLocalRing_iff R).mp ‹IsRegularLocalRing R›).symm]
  have hd:m.spanFinrank=n+1:=by omega
  rw [show (maximalIdeal R).spanFinrank=n+1 from hd]
 have q5:RingHom.ker f = ⊥ := by
  by_contra hne
  have q0:RingHom.ker f ≠ ⊤ := fun htop =>
   one_ne_zero (by
    have h1:(1:_)∈RingHom.ker f:=htop.symm▸Submodule.mem_top
    rwa [RingHom.mem_ker,map_one] at h1)
  have hlt:=z38 (I:=RingHom.ker f) hne q0;have heq:=ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective q10);rw [heq,q31,q22] at hlt;exact lt_irrefl _ hlt
 exact ⟨C,inferInstance,inferInstance,‹IsDiscreteValuationRing C›,‹IsAdicComplete (maximalIdeal C) C›,(p:C),n,q17,⟨RingEquiv.ofBijective f ⟨(RingHom.injective_iff_ker_eq_bot f).mpr q5,q10⟩⟩⟩
private lemma z228 {R' R M' M:Type}
  [CommRing R'] [CommRing R] [AddCommGroup M'] [Module R' M'] [AddCommGroup M] [Module R M]
  (e:R' ≃+* R) (f:M' ≃+ M) (q0:∀ (r:R') (x:M'),f (r•x)=e r•f x) :
  Module.length R' M'=Module.length R M:=by
 letI : Algebra R' R:=e.toRingHom.toAlgebra
 letI : Module R' M:=Module.restrictScalars R' R M
 haveI : IsScalarTower R' R M:=IsScalarTower.restrictScalars R' R M
 let fL:M' ≃ₗ[R'] M :=
  {
   toFun:=f
   invFun:=f.symm
   left_inv:=f.left_inv
   right_inv:=f.right_inv
   map_add':=f.map_add
   map_smul':=fun r x=>q0 r x }
 rw [fL.length_eq]
 exact Module.length_eq_of_surjective (S:=R') (R:=R) (M:=M) e.surjective
private lemma z229 {R' R:Type}
  [CommRing R'] [IsNoetherianRing R'] [CommRing R]
  (e:R' ≃+* R) (P Q:Ideal R) :
  intersectionMultiplicity R' (R'⧸P.comap e.toRingHom) (R'⧸Q.comap e.toRingHom) =
  intersectionMultiplicity R (R⧸P) (R⧸Q):=by
 let P':Ideal R':=P.comap e.toRingHom;let Q':Ideal R':=Q.comap e.toRingHom
 letI : Algebra R' R:=e.toRingHom.toAlgebra
 let q6:R' ≃ₗ[R'] R :=
  {
   toFun:=e
   invFun:=e.symm
   left_inv:=e.left_inv
   right_inv:=e.right_inv
   map_add':=e.map_add
   map_smul':=fun r x=>by
    change e (r*x)=e r*e x
    rw [map_mul] }
 haveI : Module.Flat R' R:=Module.Flat.of_linearEquiv q6.symm
 have q2:∀ q : ℕ,Subsingleton (z56 R R (R⧸Q) (q+1)):=fun q=>z67 (R:=R) (M:=R) (N:=R⧸Q) q
 have hQ_eq:Q'=Q.comap e.toRingHom:=rfl;let q1:(R'⧸Q') ≃+* (R⧸Q):=Ideal.quotientEquiv Q' Q e (Ideal.map_comap_of_surjective e.toRingHom e.surjective Q).symm
 let e₀_aux:RestrictScalars R' R (R⧸Q) ≃ₗ[R'] (R'⧸Q') :=
  {
   toFun:=fun x=>q1.symm (RestrictScalars.addEquiv R' R (R⧸Q) x)
   invFun:=fun y=>(RestrictScalars.addEquiv R' R (R⧸Q)).symm (q1 y)
   left_inv:=fun x=>by
    apply (RestrictScalars.addEquiv R' R (R⧸Q)).injective;simp
   right_inv:=fun y=>by simp
   map_add':=fun x₁ x₂=>by simp
   map_smul':=fun r x=>by
    have h1:∀ y:R⧸Q,q1.symm (e r•y)=r•q1.symm y:=fun y=>by
     obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective y;apply q1.injective;rw [q1.apply_symm_apply];change Ideal.Quotient.mk Q (e r)*Ideal.Quotient.mk Q a=q1 (Ideal.Quotient.mk Q' r*q1.symm (Ideal.Quotient.mk Q a));rw [map_mul,q1.apply_symm_apply];rfl
    exact h1 (RestrictScalars.addEquiv R' R (R⧸Q) x) }
 let e₀ : RestrictScalars R' R (R ⊗[R] (R⧸Q)) ≃ₗ[R'] (R'⧸Q'):=(z136 R' R (TensorProduct.lid R (R⧸Q))).trans e₀_aux
 haveI : Module.Finite R' (R'⧸P'):=Module.Finite.of_surjective (Ideal.Quotient.mkₐ R' P').toLinearMap Ideal.Quotient.mk_surjective
 let q0:(R'⧸P') ≃+* (R⧸P):=Ideal.quotientEquiv P' P e (Ideal.map_comap_of_surjective e.toRingHom e.surjective P).symm
 let eP_fwdR':(R ⊗[R'] (R'⧸P')) →ₗ[R'] (R⧸P) :=
  TensorProduct.lift
   {
    toFun:=fun r =>
     {
      toFun:=fun u=>Ideal.Quotient.mk P r*q0 u
      map_add':=fun u₁ u₂=>by rw [map_add,mul_add]
      map_smul':=fun a u=>by
       change Ideal.Quotient.mk P r*q0 (Ideal.Quotient.mk P' a*u)=Ideal.Quotient.mk P (e a)*(Ideal.Quotient.mk P r*q0 u);rw [map_mul];change Ideal.Quotient.mk P r*(Ideal.Quotient.mk P (e a)*q0 u)=_
       ring }
    map_add':=fun r₁ r₂=>by apply LinearMap.ext;intro u;simp [map_add,add_mul]
    map_smul':=fun a r=>by
     apply LinearMap.ext;intro u;change Ideal.Quotient.mk P (e a*r)*q0 u=Ideal.Quotient.mk P (e a)*(Ideal.Quotient.mk P r*q0 u)
     rw [map_mul,mul_assoc] }
 let q3:(R ⊗[R'] (R'⧸P')) →ₗ[R] (R⧸P) :=
  {
   toFun:=eP_fwdR'
   map_add':=eP_fwdR'.map_add
   map_smul':=fun r x=>by
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul s u =>
     change Ideal.Quotient.mk P (r*s)*q0 u=Ideal.Quotient.mk P r*(Ideal.Quotient.mk P s*q0 u);rw [map_mul,mul_assoc]
    | add x₁ x₂ ih₁ ih₂=>simp only [smul_add,map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂] }
 let q4:(R⧸P) →ₗ[R] (R ⊗[R'] (R'⧸P')) :=
  Submodule.liftQ P
   {
    toFun:=fun r=>r ⊗ₜ[R'] (1:R'⧸P')
    map_add':=fun r₁ r₂=>add_tmul r₁ r₂ 1
    map_smul':=fun r₁ r₂=>by
     change (r₁ * r₂) ⊗ₜ[R'] (1:R'⧸P')=r₁ • (r₂ ⊗ₜ[R'] (1:R'⧸P'))
     rw [smul_tmul'];rfl }
   (fun r hr=>by
    rw [LinearMap.mem_ker];change r ⊗ₜ[R'] (1:R'⧸P')=0
    have hr':e.symm r∈P':=by
     change e (e.symm r)∈P;rwa [e.apply_symm_apply]
    have h1:r=e.symm r•(1:R):=by
     change r=e (e.symm r)*1;rw [mul_one,e.apply_symm_apply]
    rw [h1,smul_tmul]
    have h2:e.symm r•(1:R'⧸P')=0:=by
     change Ideal.Quotient.mk P' (e.symm r)*1=0;rw [mul_one,Ideal.Quotient.eq_zero_iff_mem];exact hr'
    rw [h2,tmul_zero])
 let eP:(R ⊗[R'] (R'⧸P')) ≃ₗ[R] (R⧸P) :=
  LinearEquiv.ofLinearMap q3 q4
   (by
    apply LinearMap.ext;intro y;obtain ⟨r,rfl⟩:=Ideal.Quotient.mk_surjective y;change Ideal.Quotient.mk P r*q0 1=Ideal.Quotient.mk P r
    rw [map_one,mul_one])
   (by
    apply LinearMap.ext;intro x
    induction x using TensorProduct.induction_on with
    | zero=>simp
    | tmul r u =>
     obtain ⟨a,rfl⟩:=Ideal.Quotient.mk_surjective u;change (r*e a) ⊗ₜ[R'] (1:R'⧸P')=r ⊗ₜ[R'] Ideal.Quotient.mk P' a
     have h1:r*e a=a•r:=by change r*e a=e a*r;ring
     rw [h1,smul_tmul];congr 1;change Ideal.Quotient.mk P' a*1=Ideal.Quotient.mk P' a;rw [mul_one]
    | add x₁ x₂ ih₁ ih₂=>simp only [map_add] at ih₁ ih₂ ⊢;rw [ih₁,ih₂])
 have q7:∀ i : ℕ,Module.length R' (z56 R' (R'⧸P') (R'⧸Q') i)=Module.length R (z56 R (R⧸P) (R⧸Q) i):=fun i=>by
  obtain ⟨e1⟩:=z145 (R:=R') (T:=R) (S:=R) (N:=R⧸Q) (B:=R'⧸Q')
   q2 e₀ i (R'⧸P')
  obtain ⟨e2⟩:=z144 (T:=R) (N:=R⧸Q) eP i;let q5:z56 R' (R'⧸P') (R'⧸Q') i ≃+ z56 R (R⧸P) (R⧸Q) i:=(e1.toAddEquiv.trans (RestrictScalars.addEquiv R' R _)).trans e2.toAddEquiv
  refine z228 e q5 fun r x => ?_
  change e2 (RestrictScalars.addEquiv R' R _ (e1 (r•x)))=e r•e2 (RestrictScalars.addEquiv R' R _ (e1 x));rw [e1.map_smul];change e2 (e r•RestrictScalars.addEquiv R' R _ (e1 x))=_;exact e2.map_smul (e r) _
 unfold intersectionMultiplicity
 refine finsum_congr fun i => ?_
 rw [q7 i]
end CohenStructureAndMain
end OMA.H2Proof
theorem OMA.solution :
  OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.H2 := by
 intro R _ _ _ hcase P Q _ _ hPQ
 have htransport : ∀ {R' : Type} [CommRing R'] [IsLocalRing R'] (e : R' ≃+* R),
   let P' : Ideal R' := P.comap e.toRingHom;let Q' : Ideal R' := Q.comap e.toRingHom
   P'.IsPrime ∧ Q'.IsPrime ∧ (P' ⊔ Q').radical = maximalIdeal R' ∧
   ringKrullDim (R' ⧸ P') = ringKrullDim (R ⧸ P) ∧
   ringKrullDim (R' ⧸ Q') = ringKrullDim (R ⧸ Q) ∧
   ringKrullDim R' = ringKrullDim R := by
  intro R' _ _ e;dsimp only;let P' : Ideal R' := P.comap e.toRingHom;let Q' : Ideal R' := Q.comap e.toRingHom;have hP' : P'.IsPrime := Ideal.IsPrime.comap e.toRingHom;have hQ' : Q'.IsPrime := Ideal.IsPrime.comap e.toRingHom
  have hmax_comap : (maximalIdeal R).comap e.toRingHom = maximalIdeal R' := by
   have hmax : ((maximalIdeal R).comap e.toRingHom).IsMaximal := Ideal.comap_isMaximal_of_surjective e.toRingHom e.surjective;exact IsLocalRing.eq_maximalIdeal hmax
  have hPQ' : (P' ⊔ Q').radical = maximalIdeal R' := by
   have hsup : P' ⊔ Q' = (P ⊔ Q).comap e.toRingHom := by
    ext x;simp only [Ideal.mem_comap, Submodule.mem_sup, P', Q'];constructor
    ·
     rintro ⟨a, ha, b, hb, rfl⟩;exact ⟨e a, ha, e b, hb, (map_add e a b).symm⟩
    ·
     rintro ⟨a, ha, b, hb, hab⟩
     refine ⟨e.symm a, by simpa using ha, e.symm b, by simpa using hb, ?_⟩
     apply e.injective;rw [map_add, e.apply_symm_apply, e.apply_symm_apply, hab];rfl
   rw [hsup, ← Ideal.comap_radical, hPQ, hmax_comap]
  have hmapP : P'.map e.toRingHom = P := by
   ext r;simp only [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective, P', Ideal.mem_comap]
   exact ⟨fun ⟨x, hx, hxr⟩ => hxr ▸ hx, fun hr => ⟨e.symm r, by simpa using hr, e.apply_symm_apply r⟩⟩
  have hmapQ : Q'.map e.toRingHom = Q := by
   ext r;simp only [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective, Q', Ideal.mem_comap]
   exact ⟨fun ⟨x, hx, hxr⟩ => hxr ▸ hx, fun hr => ⟨e.symm r, by simpa using hr, e.apply_symm_apply r⟩⟩
  refine ⟨hP', hQ', hPQ',
   ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P' P e hmapP.symm),
   ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Q' Q e hmapQ.symm),
   ringKrullDim_eq_of_ringEquiv e⟩
 by_cases hp0 : (ringChar (ResidueField R) : R) = 0
 ·
  obtain ⟨d, ⟨e⟩⟩ := OMA.H2Proof.z226 R hp0;obtain ⟨hP', hQ', hPQ', hdP, hdQ, hdR⟩ := htransport e
  have hdim := (OMA.H2Proof.z54 d (P.comap e.toRingHom)
   (Q.comap e.toRingHom) hPQ').2
  rw [hdP, hdQ, hdR] at hdim
  exact ⟨hdim, fun hne => False.elim (hne hp0)⟩
 ·
  have hp_unram : (ringChar (ResidueField R) : R) ∉ maximalIdeal R ^ 2 := hcase.resolve_left hp0;obtain ⟨V, _, _, _, _, pV, n, hpV, ⟨e⟩⟩ := OMA.H2Proof.z227 R hp0 hp_unram;obtain ⟨hP', hQ', hPQ', hdP, hdQ, hdR⟩ := htransport e
  have hres := OMA.H2Proof.z149 pV hpV n
   (P.comap e.toRingHom) (Q.comap e.toRingHom) hPQ'
  rw [hdP, hdQ, hdR] at hres
  refine ⟨hres.1, fun _ heq => ?_⟩
  rw [← OMA.H2Proof.z229 e P Q];exact hres.2 heq
