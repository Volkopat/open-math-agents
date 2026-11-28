import OMAReductions.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_unramified_R1
import Mathlib

/-!
Cohen structure theorem for complete unramified mixed-characteristic regular local rings.
-/

open IsLocalRing Module Ideal TensorProduct CategoryTheory Limits MonoidalCategory Pointwise Function

namespace SerreCohenStructure


lemma exists_ltSeries_of_krullDim_eq_natCast {α : Type*} [Preorder α] {n : ℕ}
    (h : Order.krullDim α = (n : WithBot ℕ∞)) :
    ∃ c : LTSeries α, c.length = n := by
  have hne : Nonempty α := by
    rw [← Order.krullDim_ne_bot_iff, h]
    exact WithBot.coe_ne_bot
  cases n with
  | zero =>
    obtain ⟨a⟩ := hne
    exact ⟨RelSeries.singleton _ a, rfl⟩
  | succ k =>
    by_contra hno
    push Not at hno
    have hle : Order.krullDim α ≤ (k : WithBot ℕ∞) := by
      rw [Order.krullDim_eq_iSup_length]
      apply WithBot.coe_le_coe.mpr
      refine iSup_le fun c => ?_
      have hc_le : (c.length : WithBot ℕ∞) ≤ ((k + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h, Order.krullDim_eq_iSup_length]
        exact WithBot.coe_le_coe.mpr (le_iSup (fun s : LTSeries α => (s.length : ℕ∞)) c)
      have hc_nat : c.length ≤ k + 1 := by exact_mod_cast hc_le
      have hc_lt : c.length < k + 1 := lt_of_le_of_ne hc_nat (hno c)
      exact Nat.cast_le.mpr (Nat.lt_succ_iff.mp hc_lt)
    rw [h] at hle
    have : k + 1 ≤ k := by exact_mod_cast hle
    omega

lemma ringKrullDim_quotient_eq_natCast {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ∃ n : ℕ, ringKrullDim (R ⧸ I) = (n : WithBot ℕ∞) := by
  have hle : ringKrullDim (R ⧸ I) ≤ ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    (ringKrullDim_quotient_le I).trans (ringKrullDim_le_spanFinrank_maximalIdeal R)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have hne_bot : ringKrullDim (R ⧸ I) ≠ ⊥ := by
    intro hbot
    have hnn := ringKrullDim_nonneg_of_nontrivial (R := R ⧸ I)
    rw [hbot] at hnn
    exact absurd hnn (by decide)
  cases h : ringKrullDim (R ⧸ I) with
  | bot => exact absurd h hne_bot
  | coe e =>
    cases e with
    | top =>
      rw [h] at hle
      have htop : (⊤ : ℕ∞) ≤ ((maximalIdeal R).spanFinrank : ℕ∞) := WithBot.coe_le_coe.mp hle
      exact absurd (top_le_iff.mp htop) (ENat.natCast_ne_top _)
    | coe n =>
      exact ⟨n, rfl⟩

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

lemma z36 {S:Type*} [CommRing S] [IsLocalRing S]
  (I:Ideal S) [Nontrivial (S⧸I)] : IsLocalRing (S⧸I) :=
 IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
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
  exists_ltSeries_of_krullDim_eq_natCast
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

private lemma z227 (R:Type) [CommRing R] [IsRegularLocalRing R]
  [IsAdicComplete (maximalIdeal R) R]
  (q23:(ringChar (ResidueField R) : R)≠0)
  (q3:(ringChar (ResidueField R) : R)∉maximalIdeal R ^ 2) :
  ∃ (V:Type) (_:CommRing V) (_:IsDomain V) (_:IsDiscreteValuationRing V)
   (_:IsAdicComplete (maximalIdeal V) V) (n : ℕ),
   maximalIdeal V=span {(ringChar (ResidueField R) : V)}∧Nonempty (z0 V n ≃+* R):=by
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
 exact ⟨C,inferInstance,inferInstance,‹IsDiscreteValuationRing C›,‹IsAdicComplete (maximalIdeal C) C›,n,q17,⟨RingEquiv.ofBijective f ⟨(RingHom.injective_iff_ker_eq_bot f).mpr q5,q10⟩⟩⟩


noncomputable def powerSeriesMapEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    PowerSeries A ≃+* PowerSeries B where
  toFun := PowerSeries.map e.toRingHom
  invFun := PowerSeries.map e.symm.toRingHom
  left_inv f := by ext k; simp
  right_inv g := by ext k; simp
  map_mul' := map_mul _
  map_add' := map_add _

noncomputable def mvPowerSeriesIterEquiv (V : Type) [CommRing V] :
    ∀ n : ℕ, MvPowerSeries (Fin n) V ≃+* z0 V n
  | 0 => (MvPowerSeries.isEmptyEquiv (Fin 0) V).toRingEquiv
  | n + 1 =>
    (MvPowerSeries.finSuccEquiv V n).toRingEquiv.trans
      (powerSeriesMapEquiv (mvPowerSeriesIterEquiv V n))

theorem serre_h3_main :
    OMA.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_unramified_R1.H3 := by
  intro S _ _ _ p _ hp
  have hp_eq : ringChar (ResidueField S) = p := ringChar.eq (ResidueField S) p
  have hne0 : (ringChar (ResidueField S) : S) ≠ 0 := by
    rw [hp_eq]
    intro h0
    exact hp (h0 ▸ (maximalIdeal S ^ 2).zero_mem)
  have hnot2 : (ringChar (ResidueField S) : S) ∉ maximalIdeal S ^ 2 := by
    rwa [hp_eq]
  obtain ⟨V, instCR, instDom, instDVR, instComp, n, hmaxV, ⟨e0⟩⟩ := z227 S hne0 hnot2
  let _ : CommRing V := instCR
  rw [hp_eq] at hmaxV
  exact ⟨V, instCR, instDom, instDVR, instComp, n, hmaxV,
    ⟨(mvPowerSeriesIterEquiv V n).trans e0⟩⟩

end SerreCohenStructure

theorem OMA.solution :
    OMA.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_unramified_R1.H3 :=
  SerreCohenStructure.serre_h3_main
