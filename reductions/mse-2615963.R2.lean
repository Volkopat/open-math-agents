import OMAStatements.S_mse_2615963
import Mathlib

namespace ChebyshevTest
open Finset
open PowerSeries
variable {R : Type*} [CommRing R]

lemma chebSeries_mul (x : R) :
    (mk fun n => (Polynomial.Chebyshev.C R (n:ℤ)).eval x)*(1-C x*X+X^2)=C (2:R)-C x*X := by
  rw [mul_add,mul_sub,mul_one,←mul_assoc]
  ext n
  simp only [map_add,map_sub]
  cases n with
  | zero => simp [coeff_mk,coeff_zero_eq_constantCoeff]
  | succ n =>
    cases n with
    | zero => simp [coeff_mk,coeff_mul_X_pow',coeff_mul_C,coeff_C] <;> ring
    | succ n =>
      rw [show n+1+1=n+2 by omega]
      simp [coeff_mk,coeff_mul_X_pow',coeff_C,Polynomial.Chebyshev.C_add_two]
      <;> ring

lemma indicator_mul {r : ℕ} (hr : 0<r) : (mk (fun n => if r ∣ n then 1 else 0) : PowerSeries R)*(1-X^r)=1 := by
  rw [mul_sub,mul_one]
  ext n
  simp only [map_sub,coeff_mul_X_pow',coeff_mk,coeff_one]
  by_cases zero : n=0
  · subst n; simp [show ¬r≤0 by omega]
  · rw [if_neg zero]
    by_cases h : r≤n
    · obtain ⟨a,e⟩ : ∃ a, n=a+r := ⟨n-r,by omega⟩
      simp [h,e]
    · simp [h,show ¬ r ∣ n from fun dv => h (Nat.le_of_dvd (Nat.pos_of_ne_zero zero) dv)]

end ChebyshevTest

namespace ChebyshevTest
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]

lemma split_field : (∏ x : (ZMod p), (X-C x)) = X^p-X := by
  have hp := (Fact.out : Nat.Prime p).one_lt
  have hm : (X^p-X : (ZMod p)[X]).Monic := monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hp)
  have roots : (X^p-X : (ZMod p)[X]).roots=univ.val := by simpa using FiniteField.roots_X_pow_card_sub_X (ZMod p)
  have card : (X^p-X : (ZMod p)[X]).roots.card=(X^p-X : (ZMod p)[X]).natDegree := by
    rw [roots,FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp]; simp
  have e := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm card
  rw [roots] at e
  exact e

lemma log_deriv {K : Type*} [Field K] [Algebra (ZMod p) K] (y : K)
    (hn : y^p-y≠0) : (∑ x : (ZMod p), (y-algebraMap (ZMod p) K x)⁻¹)*(y^p-y)= -1 := by
  classical
  let ev := eval₂RingHom (algebraMap (ZMod p) K) y
  have subst (x : (ZMod p)) : ev (X-C x)=y-algebraMap (ZMod p) K x := by simp [ev]
  have evX : ev X=y := by simp [ev]
  have prod : (∏ x : (ZMod p), (y-algebraMap (ZMod p) K x))=y^p-y := by
    simpa only [map_prod,subst,map_sub,map_pow,evX] using congrArg ev (split_field (p:=p))
  have der := congrArg Polynomial.derivative (split_field (p:=p))
  simp only [derivative_prod_finset,derivative_sub,derivative_X,derivative_C,sub_zero,mul_one,
    derivative_X_pow,ZMod.natCast_self,Polynomial.C_0,zero_mul,zero_sub] at der
  have sum : (∑ x : (ZMod p), ∏ t ∈ univ.erase x, (y-algebraMap (ZMod p) K t))= -1 := by
    simpa only [map_sum,map_prod,subst,map_neg,map_one] using congrArg ev der
  rw [Finset.sum_mul,←sum]
  apply sum_congr rfl
  intro x _
  have e := Finset.mul_prod_erase univ (fun t : (ZMod p) => y-algebraMap (ZMod p) K t) (mem_univ x)
  rw [prod] at e
  have ne : y-algebraMap (ZMod p) K x ≠ 0 := by intro h; rw [h,zero_mul] at e; exact hn e.symm
  rw [←e,inv_mul_cancel_left₀ ne]
end ChebyshevTest

namespace ChebyshevTest
open Finset
variable {p : ℕ} [Fact p.Prime]

lemma rational_identity {K : Type*} [Field K] [Algebra (ZMod p) K] [CharP K p]
    (z : K) (hz : z≠0) (u : 1-z^(p-1)≠0) (v : 1-z^(p+1)≠0)
    (s : (ZMod p) → K) (eqn : ∀ x, s x*(1-algebraMap (ZMod p) K x*z+z^2)=2-algebraMap (ZMod p) K x*z) :
    (∑ x, s x)=(1-z^(p+1))⁻¹-(1-z^(p-1))⁻¹ := by
  let t := z^(p-1)
  have hp := (Fact.out : p.Prime).pos
  have powp : z^p=t*z := by dsimp [t]; rw [←pow_succ, Nat.sub_add_cancel hp]
  have powp1 : z^(p+1)=t*z*z := by rw [pow_succ,powp]
  let y := z+z⁻¹
  let D := y^p-y
  have form : D*(t*z)=(1-t)*(1-t*z*z) := by
    dsimp [D,y]
    rw [add_pow_char,inv_pow,powp]
    have nt : t≠0 := pow_ne_zero _ hz
    field_simp; ring
  rw [powp1] at v ⊢
  change 1-t≠0 at u
  change _ = _-(1-t)⁻¹
  have nd : D≠0 := fun bad => (mul_ne_zero u v) (by rw [←form,bad,zero_mul])
  have deriv := log_deriv (p:=p) y nd
  have pm (x : (ZMod p)) : y-algebraMap (ZMod p) K x≠0 := by
    intro bad
    have xy := sub_eq_zero.mp bad
    have fix : (algebraMap (ZMod p) K x)^p=algebraMap (ZMod p) K x := by
      rw [←map_pow,ZMod.pow_card]
    apply nd
    dsimp [D]; rw [xy,fix,sub_self]
  have each (x : (ZMod p)) : s x=1+((1-z^2)/z)*(y-algebraMap (ZMod p) K x)⁻¹ := by
    have e := eqn x
    have nz := pm x
    field_simp [nz,hz]
    dsimp [y] at *
    field_simp [hz] at *
    linear_combination e
  simp_rw [each]
  rw [sum_add_distrib,←mul_sum]
  simp only [sum_const,card_univ,ZMod.card,nsmul_eq_mul,CharP.cast_eq_zero,zero_mul,zero_add]
  change (∑ x : (ZMod p), (y-algebraMap (ZMod p) K x)⁻¹)*D= -1 at deriv
  have iso : (∑ x : (ZMod p), (y-algebraMap (ZMod p) K x)⁻¹)= -1/D := (eq_div_iff nd).mpr deriv
  rw [iso]
  have finish (a b d w q : K) (ha : a≠0) (hb : b≠0) (hd : d≠0) (hw : w≠0)
      (hprod : d*(q*w)=a*b) (hdiff : a-b= -(1-w^2)*q) :
      (1-w^2)/w*(-1/d)=b⁻¹-a⁻¹ := by
    rw [←one_div,←one_div,div_sub_div _ _ hb ha,div_mul_div_comm]
    apply (div_eq_div_iff (mul_ne_zero hw hd) (mul_ne_zero hb ha)).mpr
    rw [one_mul,mul_one,hdiff,mul_comm b a,←hprod]
    ring
  exact finish _ _ _ _ _ u v nd hz form (by ring)
end ChebyshevTest

namespace ChebyshevTest
open Finset PowerSeries
variable {p : ℕ} [Fact p.Prime]

lemma sum_series : (∑ x : (ZMod p), (PowerSeries.mk fun n => (Polynomial.Chebyshev.C (ZMod p) (n:ℤ)).eval x))= (mk (fun n => if (p+1) ∣ n then 1 else 0) : PowerSeries (ZMod p))-(mk (fun n => if (p-1) ∣ n then 1 else 0) : PowerSeries (ZMod p)) := by
  let chebSeries (x : (ZMod p)) : (PowerSeries (ZMod p)) := mk fun n => (Polynomial.Chebyshev.C (ZMod p) (n:ℤ)).eval x
  let indicatorSeries (r : ℕ) : (PowerSeries (ZMod p)) := mk fun n => if r ∣ n then 1 else 0
  change (∑ x : (ZMod p), chebSeries x)=indicatorSeries (p+1)-indicatorSeries (p-1)
  let emb := algebraMap (PowerSeries (ZMod p)) (FractionRing (PowerSeries (ZMod p)))
  let incl : (ZMod p) →+* (FractionRing (PowerSeries (ZMod p))) := emb.comp PowerSeries.C
  letI : Algebra (ZMod p) (FractionRing (PowerSeries (ZMod p))) := incl.toAlgebra
  letI : CharP (FractionRing (PowerSeries (ZMod p))) p := charP_of_injective_algebraMap (algebraMap (ZMod p) (FractionRing (PowerSeries (ZMod p)))).injective p
  let z := emb (PowerSeries.X : (PowerSeries (ZMod p)))
  have inj : Function.Injective emb := IsFractionRing.injective _ _
  have nz : z≠0 := fun h => PowerSeries.X_ne_zero (R:=(ZMod p)) (inj (by simpa [z] using h))
  have invG (r : ℕ) (hr : 0<r) : emb (indicatorSeries r)*(1-z^r)=1 := by
    simpa only [map_mul,map_sub,map_one,map_pow,z] using congrArg emb (indicator_mul (R:=(ZMod p)) hr)
  have invE (r : ℕ) (hr : 0<r) : emb (indicatorSeries r)=(1-z^r)⁻¹ :=
    eq_inv_of_mul_eq_one_left (invG r hr)
  have nd (r : ℕ) (hr : 0<r) : 1-z^r≠0 := by
    intro h
    have eqn := invG r hr
    rw [h,mul_zero] at eqn
    exact zero_ne_one eqn
  have hp := (Fact.out : p.Prime).one_lt
  apply inj
  rw [map_sum,map_sub,invE _ (by omega),invE _ (by omega)]
  apply rational_identity z nz (nd _ (by omega)) (nd _ (by omega))
  intro x
  change emb (chebSeries x)*(1-emb (C x)*z+z^2)=2-emb (C x)*z
  simpa only [map_sub,map_mul,map_add,map_one,map_pow,map_ofNat,z] using congrArg emb (chebSeries_mul x)

theorem local_sum (m : ℕ) :
    (∑ x : (ZMod p), (Polynomial.Chebyshev.C (ZMod p) (m:ℤ)).eval x)=
    (if p+1 ∣ m then 1 else 0)-(if p-1 ∣ m then 1 else 0) := by
  simpa [coeff_mk] using congrArg (coeff m) (sum_series (p:=p))
end ChebyshevTest

namespace ChebyshevTest
open Finset Polynomial
lemma block_sum (p : ℕ) [NeZero p] (f : ZMod p → ZMod p) (q : ℕ) :
    (∑ k ∈ range (p*q), f (k:ZMod p))=q*∑ x, f x := by
  have one : (∑ k ∈ range p, f (k:ZMod p))=∑ x, f x := by
    rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => f (k:ZMod p))]
    have eqn (i : Fin p) : (i.val:ZMod p)=ZMod.finEquiv p i := by
      cases p with
      | zero => exact (Fin.elim0 i)
      | succ p => exact ZMod.natCast_zmod_val (n:=p+1) i
    simp_rw [eqn]
    exact (ZMod.finEquiv p).toEquiv.sum_comp f
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ,sum_range_add,ih]
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add,one,Nat.cast_succ]
    ring

lemma cast_raw {n m p : ℕ} [NeZero p] (dv : p ∣ n) : (((∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((m:ℕ):ℤ)).eval (k:ℤ)) : ℤ) : ZMod p)=
    ((n/p:ℕ):ZMod p)*∑ x : ZMod p, (Polynomial.Chebyshev.C (ZMod p) (m:ℤ)).eval x := by
  have point (k : ℕ) : (((Polynomial.Chebyshev.C ℤ (m:ℤ)).eval (k:ℤ):ℤ):ZMod p)=
      (Polynomial.Chebyshev.C (ZMod p) (m:ℤ)).eval (k:ZMod p) := by
    rw [←Polynomial.Chebyshev.map_C (Int.castRingHom (ZMod p)),Polynomial.eval_map]
    simpa using (Polynomial.map_aeval_eq_aeval_map ..)
  push_cast
  simp_rw [point]
  nth_rw 1 [←Nat.mul_div_cancel' dv]
  exact block_sum p (fun x => (Polynomial.Chebyshev.C (ZMod p) (m:ℤ)).eval x) (n/p)

lemma squarefree_dvd_int {n : ℕ} (sn : Squarefree n) (z : ℤ)
    (localdv : ∀ p : ℕ, p.Prime → p ∣ n → (p:ℤ) ∣ z) : (n:ℤ) ∣ z := by
  by_cases zero : z=0
  · simp [zero]
  have abspos : z.natAbs≠0 := by simpa using zero
  rw [←Int.dvd_natAbs,Int.natCast_dvd_natCast,←Nat.prod_primeFactors_of_squarefree sn]
  apply (Nat.prod_primeFactors_dvd_iff abspos).mpr
  intro p hp
  have ⟨pp,pn,_⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨pp,Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (localdv p pp pn)),abspos⟩
end ChebyshevTest

namespace ChebyshevTest
open Finset
lemma cast_sum {p n m : ℕ} (hp : p.Prime) (dv : p ∣ n) :
    (((∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((m:ℕ):ℤ)).eval (k:ℤ)) : ℤ) : ZMod p)=((n/p:ℕ):ZMod p)*(((if p+1 ∣ m then 1 else 0)-(if p-1 ∣ m then 1 else 0) : ℤ):ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [cast_raw dv,local_sum]
  split_ifs <;> norm_num

theorem criterion (n : ℕ) : (Int.ModEq (n:ℤ) ((∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n-1:ℕ):ℤ)).eval (k:ℤ)) : ℤ) (-1)) ↔
    ∀ p : ℕ, p.Prime → p ∣ n → Int.ModEq p ((n/p:ℕ)*((if p+1 ∣ n-1 then 1 else 0)-(if p-1 ∣ n-1 then 1 else 0) : ℤ)) (-1) := by
  have local_iff (p : ℕ) (hp : p.Prime) (dv : p ∣ n) :
      Int.ModEq p (((∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n-1:ℕ):ℤ)).eval (k:ℤ)) : ℤ)) (-1) ↔ Int.ModEq p ((n/p:ℕ)*((if p+1 ∣ n-1 then 1 else 0)-(if p-1 ∣ n-1 then 1 else 0) : ℤ)) (-1) := by
    rw [←ZMod.intCast_eq_intCast_iff,←ZMod.intCast_eq_intCast_iff]
    simp only [Int.cast_mul,Int.cast_natCast,Int.cast_neg,Int.cast_one]
    rw [cast_sum hp dv]
  constructor
  · intro h p hp dv
    exact (local_iff p hp dv).mp (Int.ModEq.of_dvd (by exact_mod_cast dv) h)
  · intro allp
    have sqf : Squarefree n := by
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro p hp sq
      obtain ⟨k,eqn⟩ := sq
      have dv : p ∣ n := ⟨p*k,by rw [eqn,mul_assoc]⟩
      have h := allp p hp dv
      rw [←ZMod.intCast_eq_intCast_iff] at h
      have reduce : n/p=p*k := by rw [eqn,mul_assoc,Nat.mul_div_cancel_left _ hp.pos]
      letI : Fact p.Prime := ⟨hp⟩
      simp [reduce] at h
    apply Int.modEq_iff_dvd.mpr
    exact squarefree_dvd_int sqf _ (fun p hp dv => Int.modEq_iff_dvd.mp ((local_iff p hp dv).mpr (allp p hp dv)))

lemma prime_pass {p : ℕ} (hp : p.Prime) : (Int.ModEq (p:ℤ) ((∑ k ∈ Finset.range p, (Polynomial.Chebyshev.C ℤ ((p-1:ℕ):ℤ)).eval (k:ℤ)) : ℤ) (-1)) := by
  apply (criterion _).mpr
  intro q hq dv
  obtain eqn := (Nat.dvd_prime hp).mp dv
  have e : q=p := eqn.resolve_left hq.ne_one
  subst q
  have pos := hp.one_lt
  have nd : ¬p+1 ∣ p-1 := by intro dv; have := Nat.le_of_dvd (by omega) dv; omega
  simp [nd,Nat.div_self hp.pos]
end ChebyshevTest

namespace ChebyshevTest
lemma sign_branches {p n : ℕ} (hp : p.Prime) (dv : p ∣ n) (h : (Int.ModEq (n:ℤ) ((∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n-1:ℕ):ℤ)).eval (k:ℤ)) : ℤ) (-1))) :
    (p-1 ∣ n-1 ∧ ¬p+1 ∣ n-1 ∧ (p:ℤ) ∣ (n/p:ℕ)-1) ∨
    (p+1 ∣ n-1 ∧ ¬p-1 ∣ n-1 ∧ (p:ℤ) ∣ (n/p:ℕ)+1) := by
  have c := (criterion n).mp h p hp dv
  have notone : ¬ (p:ℤ) ∣ 1 := by exact_mod_cast hp.not_dvd_one
  rw [Int.modEq_iff_dvd] at c
  by_cases a : p+1 ∣ n-1 <;> by_cases b : p-1 ∣ n-1
  · simp [a,b] at c
    exact False.elim (notone (by simpa using c))
  · right
    refine ⟨a,b,?_⟩
    have eqn : (-(1:ℤ))-(n/p:ℕ)*((if p+1 ∣ n-1 then 1 else 0)-(if p-1 ∣ n-1 then 1 else 0) : ℤ) = -(((n/p:ℕ):ℤ)+1) := by simp [a,b]; ring
    rw [eqn,dvd_neg] at c
    exact c
  · left
    refine ⟨b,a,?_⟩
    convert c using 1
    simp [a,b]; ring
  · simp [a,b] at c
    exact False.elim (notone (by simpa using c))

lemma cofactor_constraint {p n : ℕ} (hp : p.Prime) (dv : p ∣ n) (hn : 1<n) (h : (Int.ModEq (n:ℤ) ((∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n-1:ℕ):ℤ)).eval (k:ℤ)) : ℤ) (-1))) :
    (p:ℤ)*((p:ℤ)-1) ∣ ((n/p:ℕ):ℤ)-1 ∨ (p:ℤ)*((p:ℤ)+1) ∣ ((n/p:ℕ):ℤ)+1 := by
  let q : ℤ := (n/p:ℕ)
  have eqn : (n:ℤ)=p*q := by dsimp only [q]; exact_mod_cast (Nat.mul_div_cancel' dv).symm
  have pp := hp.one_lt
  rcases sign_branches hp dv h with ⟨d,_,dd⟩|⟨d,_,dd⟩
  · left
    have dj : (p:ℤ)-1 ∣ (n:ℤ)-1 := by
      have ie := Int.natCast_dvd_natCast.mpr d
      simpa only [Int.natCast_sub (show 1≤p by omega),Int.natCast_sub (show 1≤n by omega),Int.natCast_one] using ie
    apply IsCoprime.mul_dvd (show IsCoprime (p:ℤ) (p-1) from ⟨1,-1,by ring⟩) dd
    obtain ⟨k,ek⟩ := dj
    exact ⟨k-q,by change q-1=_; rw [eqn] at ek; linarith only [ek]⟩
  · right
    have dj : (p:ℤ)+1 ∣ (n:ℤ)-1 := by
      have ie := Int.natCast_dvd_natCast.mpr d
      simpa only [Int.natCast_add,Int.natCast_sub (show 1≤n by omega),Int.natCast_one] using ie
    apply IsCoprime.mul_dvd (show IsCoprime (p:ℤ) (p+1) from ⟨-1,1,by ring⟩) dd
    obtain ⟨k,ek⟩ := dj
    exact ⟨q-k,by change q+1=_; rw [eqn] at ek; linarith only [ek]⟩

lemma even_pass {n : ℕ} (hn : 1<n) (he : Even n) (h : (Int.ModEq (n:ℤ) ((∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n-1:ℕ):ℤ)).eval (k:ℤ)) : ℤ) (-1))) : n=2 := by
  obtain ⟨k,rfl⟩ := he
  have two : 2 ∣ k+k := ⟨k,by omega⟩
  have hs := (criterion _).mp h 2 Nat.prime_two two
  have oddk : ¬2 ∣ k := by
    intro dv
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have zz : (k:ZMod 2)=0 := (ZMod.natCast_eq_zero_iff k 2).mpr dv
    rw [←ZMod.intCast_eq_intCast_iff] at hs
    rw [show (k+k)/2=k by omega] at hs
    simp only [Int.cast_mul,Int.cast_natCast,zz,zero_mul,Int.cast_neg,Int.cast_one] at hs
    exact one_ne_zero (neg_eq_zero.mp hs.symm)
  by_contra ne
  have kp : k.minFac.Prime := Nat.minFac_prime (by omega)
  have dv := Nat.minFac_dvd k
  have kd : k.minFac ∣ k+k := dvd_add dv dv
  have neq : k.minFac ≠ 2 := fun bad => oddk (bad ▸ dv)
  have odd := kp.odd_of_ne_two neq
  obtain ⟨t,ht⟩ := odd
  have bad (r : ℕ) (er : r%2=0) : ¬r ∣ k+k-1 := by
    intro d
    have div2 : 2 ∣ r := by omega
    have := div2.trans d
    omega
  rcases sign_branches kp kd h with ⟨d,_,_⟩|⟨d,_,_⟩
  · exact bad _ (by omega) d
  · exact bad _ (by omega) d
end ChebyshevTest

namespace ChebyshevTest
lemma cofactor_large {p n : ℕ} (hp : p.Prime) (dv : p ∣ n) (hn : 1<n) (nc : ¬n.Prime)
    (h : (Int.ModEq (n:ℤ) ((∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n-1:ℕ):ℤ)).eval (k:ℤ)) : ℤ) (-1))) : p*(p-1)+1 ≤ n/p := by
  have qpos : 1 < n/p := by
    have eqn := Nat.mul_div_cancel' dv
    generalize n/p=q at eqn ⊢
    cases q with
    | zero => simp at eqn; omega
    | succ q =>
      cases q with
      | zero => simp at eqn; exact (nc (eqn ▸ hp)).elim
      | succ q => omega
  have pp := hp.one_lt
  have bound : (p:ℤ)*((p:ℤ)-1)+1 ≤ ((n/p:ℕ):ℤ) := by
    rcases cofactor_constraint hp dv hn h with low|high
    · have := Int.le_of_dvd (by omega : 0<((n/p:ℕ):ℤ)-1) low
      omega
    · have := Int.le_of_dvd (by positivity : 0<((n/p:ℕ):ℤ)+1) high
      nlinarith
  have casted : ((p*(p-1)+1:ℕ):ℤ) ≤ ((n/p:ℕ):ℤ) := by
    simpa only [Int.natCast_add,Int.natCast_mul,Int.natCast_sub (show 1≤p by omega),Int.natCast_one] using bound
  exact_mod_cast casted
end ChebyshevTest

namespace OMA.R_mse_2615963_R2
/-- The branch where every cofactor is 1 modulo p(p−1). -/
def H1 : Prop := ∀ n : ℕ, 1<n → Odd n → ¬n.Prime →
    (∀ p : ℕ, p.Prime → p ∣ n → (p:ℤ)*((p:ℤ)-1) ∣ ((n/p:ℕ):ℤ)-1) →
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p-1 ∣ n-1 ∧ p+1 ∣ n-1

/-- The remaining branch, where at least one prime factor can use only
the negative cofactor progression. -/
def H2 : Prop := ∀ n : ℕ, 1<n → Odd n → ¬n.Prime →
    (∃ r : ℕ, r.Prime ∧ r ∣ n ∧ ¬(r:ℤ)*((r:ℤ)-1) ∣ ((n/r:ℕ):ℤ)-1) →
    (∀ p : ℕ, p.Prime → p ∣ n →
      (p:ℤ)*((p:ℤ)-1) ∣ ((n/p:ℕ):ℤ)-1 ∨ (p:ℤ)*((p:ℤ)+1) ∣ ((n/p:ℕ):ℤ)+1) →
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p-1 ∣ n-1 ∧ p+1 ∣ n-1

theorem main : H1 → H2 → type_of% @OMA.S_mse_2615963.main := by
  classical
  intro onlyPlus mixed n hn
  have cast : (n:ℤ)-1=((n-1:ℕ):ℤ) := by rw [Int.natCast_sub (by omega),Int.natCast_one]
  rw [cast]
  change n.Prime ↔ (Int.ModEq (n:ℤ) ((∑ k ∈ Finset.range n, (Polynomial.Chebyshev.C ℤ ((n-1:ℕ):ℤ)).eval (k:ℤ)) : ℤ) (-1))
  refine ⟨ChebyshevTest.prime_pass,?_⟩
  intro test
  by_contra nc
  have odd : Odd n := by
    rw [←Nat.not_even_iff_odd]
    exact fun he => nc ((ChebyshevTest.even_pass hn he test) ▸ Nat.prime_two)
  have conflict : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p-1 ∣ n-1 ∧ p+1 ∣ n-1 := by
    by_cases allplus : ∀ p : ℕ, p.Prime → p ∣ n → (p:ℤ)*((p:ℤ)-1) ∣ ((n/p:ℕ):ℤ)-1
    · exact onlyPlus n hn odd nc allplus
    · push_neg at allplus
      exact mixed n hn odd nc allplus (fun p hp dv => ChebyshevTest.cofactor_constraint hp dv hn test)
  obtain ⟨p,pp,dv,minus,plus⟩ := conflict
  rcases ChebyshevTest.sign_branches pp dv test with a|b
  · exact a.2.1 plus
  · exact b.2.1 minus
end OMA.R_mse_2615963_R2
