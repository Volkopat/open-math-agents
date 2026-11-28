import OMAReductions.R_OeisA245212_conjecture_R1_H2_R2_H2_R1_H2_R1

/-! Recover the dyadic index and reduced numerator from the denominator alone. -/
namespace OMA.MersenneDenominator245212

def Q (t : ℕ) := (2^t-1)/Nat.gcd (2^t-1) t

private theorem twice_le_pow {b : ℕ} (hb : 0 < b) : 2*b ≤ 2^b := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ (2:ℕ) (j+1)]
    omega

theorem bound {t : ℕ} (ht : 2 ≤ t) : 2^(t/2)-1 < Q t := by
  let a := t/2
  let b := t-a
  have hp : 0 < b := by dsimp [a,b]; omega
  have cover : a+b=t := by dsimp [a,b]; omega
  have tcap : t ≤ 2^b := (show t≤2*b by dsimp [a,b]; omega).trans (twice_le_pow hp)
  have pa := Nat.two_pow_pos a
  have pb : 1 < 2^b := Nat.one_lt_two_pow hp.ne'
  have det : t*(2^a-1)<2^t-1 := by
    have h := Nat.mul_le_mul_right (2^a-1) tcap
    have z := congrArg (fun x : ℕ => 2^b*x) (Nat.sub_add_cancel (by omega : 1≤2^a))
    have prod : 2^t=2^a*2^b := by rw [←pow_add,cover]
    rw [prod]
    have s : 2^b*(2^a-1)+2^b=2^a*2^b := by nlinarith only [z]
    omega
  have gd := Nat.gcd_dvd_left (2^t-1) t
  have small : (2^t-1).gcd t ≤ t := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  have mul : Q t * ((2^t-1).gcd t)=2^t-1 := Nat.div_mul_cancel gd
  by_contra! h
  have le := Nat.mul_le_mul h small
  change Q t * _ ≤ (2^a-1)*t at le
  rw [mul,mul_comm (2^a-1)] at le
  omega

private theorem pow_test (t m : ℕ) :
    (2 : ZMod (Q t))^m=1 ↔ Q t ∣ 2^m-1 := by
  have h := Nat.modEq_iff_dvd' (show 1≤(2:ℕ)^m from Nat.one_le_pow _ _ (by decide)) (n:=Q t)
  rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] at h
  exact eq_comm.trans h

theorem order {t : ℕ} (ht : 2≤t) : orderOf (2 : ZMod (Q t))=t := by
  have gd := Nat.gcd_dvd_left (2^t-1) t
  have mul : Q t * ((2^t-1).gcd t)=2^t-1 := Nat.div_mul_cancel gd
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega) ((pow_test t t).mpr ⟨_,mul.symm⟩)
  intro p pp pt eq
  have pos : 0<t/p := Nat.div_pos (Nat.le_of_dvd (by omega) pt) pp.pos
  have cap : t/p≤t/2 := Nat.div_le_div_left pp.two_le (by decide)
  have le := Nat.pow_le_pow_right (by decide : 0 < 2) cap
  have mid := bound ht
  have d := Nat.le_of_dvd (by have := Nat.one_lt_two_pow pos.ne'; omega : 0<2^(t/p)-1)
    ((pow_test t _).mp eq)
  omega

end OMA.MersenneDenominator245212

namespace OMA.MersenneOrderSupport245212
open OMA.MersenneDenominator245212 Finset

noncomputable def ord (p : ℕ) := orderOf (2 : ZMod p)

private theorem test (p m : ℕ) :
    (2 : ZMod p)^m=1 ↔ p∣2^m-1 := by
  have h:=Nat.modEq_iff_dvd' (show 1≤(2:ℕ)^m from Nat.one_le_pow _ _ (by decide)) (n:=p)
  rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] at h
  exact eq_comm.trans h

theorem primeOrder {p : ℕ} (hp : p.Prime) (odd : p≠2) : ord p∣p-1 := by
  let _ : Fact p.Prime:=⟨hp⟩
  have nz : (2:ZMod p)≠0 := by
    change ((2:ℕ):ZMod p)≠0
    rw [Ne,ZMod.natCast_eq_zero_iff]
    exact fun d=>odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp d)
  exact ZMod.orderOf_dvd_card_sub_one nz

private theorem oddOrder {p : ℕ} (hp : p.Prime) (odd : p≠2) :
    0<ord p ∧ ¬p∣ord p := by
  have div:=primeOrder hp odd
  have sub : 0<p-1 := by have:= hp.one_lt;omega
  refine ⟨Nat.pos_of_dvd_of_pos div sub,?_⟩
  exact fun d=>by have:=Nat.le_of_dvd sub (d.trans div);omega

private theorem order_test (p m : ℕ) : ord p ∣ m ↔ p∣2^m-1 :=
  (orderOf_dvd_iff_pow_eq_one).trans (test p m)

private theorem qdiv (t : ℕ) : Q t∣2^t-1 := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

private theorem qpos {t : ℕ} (ht : 0<t) : 0<Q t := by
  have z : 0<2^t-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow ht.ne')
  apply Nat.div_pos (Nat.le_of_dvd z (Nat.gcd_dvd_left _ _))
  exact Nat.gcd_pos_of_pos_left _ z

private theorem indexLTE {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) (div : ord p∣t) :
    (2^t-1).factorization p=(2^(ord p)-1).factorization p+t.factorization p := by
  obtain ⟨k,eq⟩:=div
  have kp : k≠0 := fun h=>by simp [eq,h] at ht
  have dp:=oddOrder hp odd
  have sub := (order_test p (ord p)).mp dvd_rfl
  have nd : ¬ p∣2^(ord p) := fun h=>odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow h))
  let _ : Fact p.Prime:=⟨hp⟩
  have h:=padicValNat.pow_sub_pow (hp.odd_of_ne_two odd) (x:=2^ord p) (y:=1)
    (Nat.one_lt_two_pow dp.1.ne') sub nd kp
  rw [one_pow,←pow_mul,←eq,←Nat.factorization_def _ hp,
    ←Nat.factorization_def _ hp,←Nat.factorization_def _ hp] at h
  rw [eq,Nat.factorization_mul dp.1.ne' kp,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd dp.2,
    zero_add,←eq]
  exact h

/-- Removing gcd(2^t−1,t) cancels precisely the index's contribution in LTE. -/
theorem valuation {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) (div : ord p∣t) :
    (Q t).factorization p=(2^(ord p)-1).factorization p := by
  have mn := (Nat.sub_pos_of_lt (Nat.one_lt_two_pow ht.ne')).ne'
  have h:=indexLTE hp odd ht div
  rw [Q,Nat.factorization_div (Nat.gcd_dvd_left _ _),Finsupp.tsub_apply,
    Nat.factorization_gcd mn ht.ne',Finsupp.inf_apply]
  omega

/-- Which primes survive the reduction: all the Mersenne number's prime factors
survive, with no extra primes, even if they also divide the index. -/
theorem support {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) :
    p∣Q t ↔ ord p∣t := by
  constructor
  · exact fun h=>(order_test p t).mpr (h.trans (qdiv t))
  · intro dv
    have h:=hp.factorization_pos_of_dvd (Nat.sub_pos_of_lt
      (Nat.one_lt_two_pow (oddOrder hp odd).1.ne')).ne' ((order_test p (ord p)).mp dvd_rfl)
    rw [←valuation hp odd ht dv] at h
    exact (dvd_pow_self p h.ne').trans (Nat.ordProj_dvd _ _)

private theorem not_two {t : ℕ} (ht : 0<t) : ¬2∣Q t := by
  have ev : 2∣2^t := dvd_pow_self _ ht.ne'
  intro d; have h:=d.trans (qdiv t); have:=Nat.two_pow_pos t;omega

/-- The index is the lcm of the orders modulo DISTINCT primes of Q(t);
no prime-power order or factorization exponent is needed. -/
theorem index {t : ℕ} (ht : 2≤t) : (Q t).primeFactors.lcm ord=t := by
  let L:=(Q t).primeFactors.lcm ord
  have tpos : 0<t := by omega
  have qnz:=(qpos tpos).ne'
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd fun p mem=>?_
    obtain ⟨hp,pd,_⟩:=Nat.mem_primeFactors.mp mem
    exact (order_test p t).mpr (pd.trans (qdiv t))
  · suffices all : Q t∣2^L-1 by
      simpa only [OMA.MersenneDenominator245212.order ht] using orderOf_dvd_of_pow_eq_one ((test _ L).mpr all)
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p j hp jd
    by_cases z : j=0
    · simp [z]
    have pd: p∣Q t := (dvd_pow_self p z).trans jd
    have odd : p≠2 := fun eq=>not_two tpos (eq ▸ pd)
    have dv:ord p∣L := Finset.dvd_lcm (f:=ord) (Nat.mem_primeFactors.mpr ⟨hp,pd,qnz⟩)
    have ordp:=(oddOrder hp odd).1
    have pk:= (hp.pow_dvd_iff_le_factorization qnz).mp jd
    rw [valuation hp odd tpos ((support hp odd tpos).mp pd)] at pk
    have jm:= (hp.pow_dvd_iff_le_factorization (Nat.sub_pos_of_lt (Nat.one_lt_two_pow ordp.ne')).ne').mpr pk
    obtain ⟨a,ha⟩:=dv
    exact jm.trans (by rw [ha,pow_mul]; simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2^ord p) 1 a)

theorem index_of_pos {t : ℕ} (ht : 0<t) : (Q t).primeFactors.lcm ord=t := by
  by_cases ht' : 2≤t
  · exact index ht'
  · have eq : t=1 := by omega
    simp [eq,Q]

/-- Cancelling the gcd with the index preserves the full prime support. -/
theorem q_primes {t : ℕ} (ht : 0<t) : (Q t).primeFactors=(2^t-1).primeFactors := by
  have mp := Nat.sub_pos_of_lt (Nat.one_lt_two_pow ht.ne')
  ext p
  constructor
  · intro mem
    obtain ⟨hp,d,_⟩:=Nat.mem_primeFactors.mp mem
    exact Nat.mem_primeFactors.mpr ⟨hp,d.trans (qdiv t),mp.ne'⟩
  · intro mem
    obtain ⟨hp,d,_⟩:=Nat.mem_primeFactors.mp mem
    have odd : p≠2 := by
      rintro rfl
      have ev : 2∣2^t:=dvd_pow_self _ ht.ne'
      omega
    exact Nat.mem_primeFactors.mpr ⟨hp,(support hp odd ht).2 ((order_test p t).2 d),(qpos ht).ne'⟩

end OMA.MersenneOrderSupport245212

namespace OMA.MersenneFractionInverse245212
open Nat Finset OMA.MersenneDenominator245212 OMA.MersenneOrderSupport245212

noncomputable def idx (z : ℕ) := z.primeFactors.lcm ord
def part (t z : ℕ) := (t.divisors.filter (fun d=>d.Coprime z)).sup id

theorem coprimePart {t : ℕ} (ht : 0<t) :
    part t (Q t)=t/((2^t-1).gcd t) := by
  let D:=2^t-1
  let G:=D.gcd t
  let P:=t/G
  have dp : 0<D:=Nat.sub_pos_of_lt (Nat.one_lt_two_pow ht.ne')
  have gp : 0<G:=Nat.gcd_pos_of_pos_left _ dp
  have prod : P*G=t:=Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have pos : 0<P:=Nat.div_pos (Nat.le_of_dvd ht (Nat.gcd_dvd_right _ _)) gp
  have cp : P.Coprime (Q t):=(Nat.coprime_div_gcd_div_gcd gp).symm
  change _=P
  apply le_antisymm
  · apply Finset.sup_le
    intro d mem
    obtain ⟨dv,free⟩:=Finset.mem_filter.mp mem
    have co : d.Coprime G:=by
      by_contra h
      obtain ⟨p,pr,dd,dg⟩:=Nat.Prime.not_coprime_iff_dvd.mp h
      have md : p∈D.primeFactors:=Nat.mem_primeFactors.mpr
        ⟨pr,dg.trans (Nat.gcd_dvd_left _ _),dp.ne'⟩
      change p∈(2^t-1).primeFactors at md
      rw [←q_primes ht] at md
      exact (pr.coprime_iff_not_dvd.mp (free.of_dvd_left dd)) (Nat.dvd_of_mem_primeFactors md)
    have dvd : d∣P*G:=prod.symm ▸ (Nat.dvd_of_mem_divisors dv)
    exact Nat.le_of_dvd pos (co.dvd_of_dvd_mul_left (by simpa only [mul_comm G P] using dvd))
  · exact Finset.le_sup (f:=id) (Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨⟨G,prod.symm⟩,ht.ne'⟩,cp⟩)

theorem recover {t : ℕ} (ht : 0<t) :
    idx (Q t)=t ∧ part (idx (Q t)) (Q t)=t/((2^t-1).gcd t) := by
  have ix : idx (Q t)=t:=index_of_pos ht
  exact ⟨ix,by rw [ix];exact coprimePart ht⟩

end OMA.MersenneFractionInverse245212

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H2_R2_H2_R1_H2_R1.H1 := by
  intro t ht
  exact OMA.MersenneFractionInverse245212.recover (by omega : 0<t)
