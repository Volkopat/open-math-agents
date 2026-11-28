import OMAReductions.R_OeisA245212_conjecture_R1_H2_R2_H1_R1

/-! A245212 fourth roots: four linear tests or a unique index recovered from prime support. -/

/- The multiplicative order of two recovers the index of a reduced
Mersenne denominator. This applies even when the denominator is composite. -/
namespace OMA.MersenneDenominator245212


private theorem twice_le_pow {b : ℕ} (hb : 0 < b) : 2*b ≤ 2^b := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ (2:ℕ) (j+1)]
    omega

theorem bound {t : ℕ} (ht : 2 ≤ t) : 2^(t/2)-1 < ((2^t-1)/Nat.gcd (2^t-1) t) := by
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
  have mul : ((2^t-1)/Nat.gcd (2^t-1) t) * ((2^t-1).gcd t)=2^t-1 := Nat.div_mul_cancel gd
  by_contra! h
  have le := Nat.mul_le_mul h small
  change ((2^t-1)/Nat.gcd (2^t-1) t) * _ ≤ (2^a-1)*t at le
  rw [mul,mul_comm (2^a-1)] at le
  omega

private theorem pow_test (t m : ℕ) :
    (2 : ZMod (((2^t-1)/Nat.gcd (2^t-1) t)))^m=1 ↔ ((2^t-1)/Nat.gcd (2^t-1) t) ∣ 2^m-1 := by
  have h := Nat.modEq_iff_dvd' (show 1≤(2:ℕ)^m from Nat.one_le_pow _ _ (by decide)) (n:=((2^t-1)/Nat.gcd (2^t-1) t))
  rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] at h
  exact eq_comm.trans h

theorem order {t : ℕ} (ht : 2≤t) : orderOf (2 : ZMod (((2^t-1)/Nat.gcd (2^t-1) t)))=t := by
  have gd := Nat.gcd_dvd_left (2^t-1) t
  have mul : ((2^t-1)/Nat.gcd (2^t-1) t) * ((2^t-1).gcd t)=2^t-1 := Nat.div_mul_cancel gd
  apply orderOf_eq_of_pow_and_pow_div_prime (by omega) ((pow_test t t).mpr ⟨_,mul.symm⟩)
  intro p pp pt eq
  have pos : 0<t/p := Nat.div_pos (Nat.le_of_dvd (by omega) pt) pp.pos
  have cap : t/p≤t/2 := Nat.div_le_div_left pp.two_le (by decide)
  have le := Nat.pow_le_pow_right (by decide : 0 < 2) cap
  have mid := bound ht
  have d := Nat.le_of_dvd (by have := Nat.one_lt_two_pow pos.ne'; omega : 0<2^(t/p)-1)
    ((pow_test t _).mp eq)
  omega

theorem injective_on_indices {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) (eq : ((2^s-1)/Nat.gcd (2^s-1) s)=((2^t-1)/Nat.gcd (2^t-1) t)) : s=t := by
  rw [←order hs,←order ht,eq]

/-- A positive solution of the residual equation has reduced denominator Q(k+1). -/
theorem reduced {x y k : ℕ} (hy : 0 < y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) : y/(x.gcd y)=((2^(k+1)-1)/Nat.gcd (2^(k+1)-1) (k+1)) := by
  let t := k+1
  let D := 2^t-1
  let g := D.gcd t
  let P := t/g
  let q := ((2^t-1)/Nat.gcd (2^t-1) t)
  let u := x%y
  have qq : u+k*y=x := by simpa only [u,quot,mul_comm] using Nat.mod_add_div x y
  have rem : x-k*y=u := by omega
  change 2^t*(x-k*y)=x+y at sol
  rw [rem] at sol
  have pos : 1<2^t := Nat.one_lt_two_pow (by dsimp [t]; omega)
  have ds : D+1=2^t := by dsimp only [D]; omega
  have ratio : D*u=t*y := by
    change D*u=(k+1)*y
    nlinarith only [sol,qq,congrArg (fun n : ℕ => n*u) ds]
  have dp : 0 < D := by omega
  have gp : 0 < g := Nat.gcd_pos_of_pos_left _ dp
  have qp : 0 < q := Nat.div_pos (Nat.le_of_dvd dp (Nat.gcd_dvd_left D t)) gp
  have af : q*g=D := Nat.div_mul_cancel (Nat.gcd_dvd_left D t)
  have bf : P*g=t := Nat.div_mul_cancel (Nat.gcd_dvd_right D t)
  have red : q*u=P*y := by
    apply Nat.eq_of_mul_eq_mul_right gp
    calc
      q*u*g = q*g*u := by ring
      _ = D*u := by rw [af]
      _ = t*y := ratio
      _ = P*y*g := by rw [←bf]; ring
  have cp : q.Coprime P := Nat.coprime_div_gcd_div_gcd gp
  have d : q∣y := cp.dvd_of_dvd_mul_left (red ▸ dvd_mul_right q u)
  let z := y/q
  have yz : y=q*z := (Nat.mul_div_cancel' d).symm
  have uz : u=P*z := by
    apply Nat.eq_of_mul_eq_mul_left qp
    calc
      q*u = P*y := red
      _ = P*(q*z) := congrArg (P*·) yz
      _ = q*(P*z) := by ring
  have gz : x.gcd y=z := by
    calc
      _ = u.gcd y := by rw [←qq,Nat.gcd_add_mul_right_left]
      _ = (P*z).gcd (q*z) := congrArg₂ Nat.gcd uz yz
      _ = z := by rw [Nat.gcd_mul_right,cp.symm.gcd_eq_one]; simp
  change y/(x.gcd y)=q
  rw [gz]
  have zp : 0 < z := Nat.div_pos (Nat.le_of_dvd hy d) qp
  exact (Nat.div_eq_iff_eq_mul_left zp (by exact ⟨q,yz.trans (Nat.mul_comm q z)⟩)).mpr yz

/-- The denominator alone recovers k+1, without needing the numerator. -/
theorem residual_order {x y k : ℕ} (hy : 0 < y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) : orderOf (2 : ZMod (y/(x.gcd y)))=k+1 := by
  rw [reduced hy hk quot sol]
  exact order (by omega)

end OMA.MersenneDenominator245212


/- The reduced Mersenne denominator is determined by its distinct
prime divisors. Each such prime occurs to its base-two Wieferich
valuation, independently of the index. -/
namespace OMA.MersenneOrderSupport245212
open OMA.MersenneDenominator245212 Finset


private theorem test (p m : ℕ) :
    (2 : ZMod p)^m=1 ↔ p∣2^m-1 := by
  have h:=Nat.modEq_iff_dvd' (show 1≤(2:ℕ)^m from Nat.one_le_pow _ _ (by decide)) (n:=p)
  rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] at h
  exact eq_comm.trans h

theorem primeOrder {p : ℕ} (hp : p.Prime) (odd : p≠2) : orderOf (2 : ZMod p)∣p-1 := by
  let _ : Fact p.Prime:=⟨hp⟩
  have nz : (2:ZMod p)≠0 := by
    change ((2:ℕ):ZMod p)≠0
    rw [Ne,ZMod.natCast_eq_zero_iff]
    exact fun d=>odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp d)
  exact ZMod.orderOf_dvd_card_sub_one nz

private theorem oddOrder {p : ℕ} (hp : p.Prime) (odd : p≠2) :
    0<orderOf (2 : ZMod p) ∧ ¬p∣orderOf (2 : ZMod p) := by
  have div:=primeOrder hp odd
  have sub : 0<p-1 := by have:= hp.one_lt;omega
  refine ⟨Nat.pos_of_dvd_of_pos div sub,?_⟩
  exact fun d=>by have:=Nat.le_of_dvd sub (d.trans div);omega

private theorem order_test (p m : ℕ) : orderOf (2 : ZMod p) ∣ m ↔ p∣2^m-1 :=
  (orderOf_dvd_iff_pow_eq_one).trans (test p m)

private theorem qdiv (t : ℕ) : ((2^t-1)/Nat.gcd (2^t-1) t)∣2^t-1 := Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

private theorem qpos {t : ℕ} (ht : 0<t) : 0<((2^t-1)/Nat.gcd (2^t-1) t) := by
  have z : 0<2^t-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow ht.ne')
  apply Nat.div_pos (Nat.le_of_dvd z (Nat.gcd_dvd_left _ _))
  exact Nat.gcd_pos_of_pos_left _ z

private theorem indexLTE {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) (div : orderOf (2 : ZMod p)∣t) :
    (2^t-1).factorization p=(2^(orderOf (2 : ZMod p))-1).factorization p+t.factorization p := by
  obtain ⟨k,eq⟩:=div
  have kp : k≠0 := fun h=>by simp [eq,h] at ht
  have dp:=oddOrder hp odd
  have sub := (order_test p (orderOf (2 : ZMod p))).mp dvd_rfl
  have nd : ¬ p∣2^(orderOf (2 : ZMod p)) := fun h=>odd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
    (hp.dvd_of_dvd_pow h))
  let _ : Fact p.Prime:=⟨hp⟩
  have h:=padicValNat.pow_sub_pow (hp.odd_of_ne_two odd) (x:=2^orderOf (2 : ZMod p)) (y:=1)
    (Nat.one_lt_two_pow dp.1.ne') sub nd kp
  rw [one_pow,←pow_mul,←eq,←Nat.factorization_def _ hp,
    ←Nat.factorization_def _ hp,←Nat.factorization_def _ hp] at h
  rw [eq,Nat.factorization_mul dp.1.ne' kp,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd dp.2,
    zero_add,←eq]
  exact h

/-- Removing gcd(2^t−1,t) cancels precisely the index's contribution in LTE. -/
theorem valuation {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) (div : orderOf (2 : ZMod p)∣t) :
    (((2^t-1)/Nat.gcd (2^t-1) t)).factorization p=(2^(orderOf (2 : ZMod p))-1).factorization p := by
  have mn := (Nat.sub_pos_of_lt (Nat.one_lt_two_pow ht.ne')).ne'
  have h:=indexLTE hp odd ht div
  rw [Nat.factorization_div (Nat.gcd_dvd_left _ _),Finsupp.tsub_apply,
    Nat.factorization_gcd mn ht.ne',Finsupp.inf_apply]
  omega

/-- Which primes survive the reduction: all the Mersenne number's prime factors
survive, with no extra primes, even if they also divide the index. -/
theorem support {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) :
    p∣((2^t-1)/Nat.gcd (2^t-1) t) ↔ orderOf (2 : ZMod p)∣t := by
  constructor
  · exact fun h=>(order_test p t).mpr (h.trans (qdiv t))
  · intro dv
    have h:=hp.factorization_pos_of_dvd (Nat.sub_pos_of_lt
      (Nat.one_lt_two_pow (oddOrder hp odd).1.ne')).ne' ((order_test p (orderOf (2 : ZMod p))).mp dvd_rfl)
    rw [←valuation hp odd ht dv] at h
    exact (dvd_pow_self p h.ne').trans (Nat.ordProj_dvd _ _)

theorem wieferich {p t : ℕ} (hp : p.Prime) (odd : p≠2) (ht : 0<t) (div : p∣((2^t-1)/Nat.gcd (2^t-1) t)) :
    (((2^t-1)/Nat.gcd (2^t-1) t)).factorization p=(2^(p-1)-1).factorization p := by
  rw [valuation hp odd ht ((support hp odd ht).mp div)]
  have sp : 0<p-1 := by have:=hp.one_lt;omega
  have h:=indexLTE hp odd sp (primeOrder hp odd)
  rw [Nat.factorization_eq_zero_of_not_dvd (p:=p) (n:=p-1)
    (fun h=>by have:=Nat.le_of_dvd sp h;omega),add_zero] at h
  exact h.symm

private theorem not_two {t : ℕ} (ht : 0<t) : ¬2∣((2^t-1)/Nat.gcd (2^t-1) t) := by
  have ev : 2∣2^t := dvd_pow_self _ ht.ne'
  intro d; have h:=d.trans (qdiv t); have:=Nat.two_pow_pos t;omega

/-- The index is the lcm of the orders modulo DISTINCT primes of Q(t);
no prime-power order or factorization exponent is needed. -/
theorem index {t : ℕ} (ht : 2≤t) : (((2^t-1)/Nat.gcd (2^t-1) t)).primeFactors.lcm (fun p : ℕ => orderOf (2 : ZMod p))=t := by
  let L:=(((2^t-1)/Nat.gcd (2^t-1) t)).primeFactors.lcm (fun p : ℕ => orderOf (2 : ZMod p))
  have tpos : 0<t := by omega
  have qnz:=(qpos tpos).ne'
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd fun p mem=>?_
    obtain ⟨hp,pd,_⟩:=Nat.mem_primeFactors.mp mem
    exact (order_test p t).mpr (pd.trans (qdiv t))
  · suffices all : ((2^t-1)/Nat.gcd (2^t-1) t)∣2^L-1 by
      simpa only [OMA.MersenneDenominator245212.order ht] using orderOf_dvd_of_pow_eq_one ((test _ L).mpr all)
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p j hp jd
    by_cases z : j=0
    · simp [z]
    have pd: p∣((2^t-1)/Nat.gcd (2^t-1) t) := (dvd_pow_self p z).trans jd
    have odd : p≠2 := fun eq=>not_two tpos (eq ▸ pd)
    have dv:orderOf (2 : ZMod p)∣L := Finset.dvd_lcm (f:=(fun p : ℕ => orderOf (2 : ZMod p))) (Nat.mem_primeFactors.mpr ⟨hp,pd,qnz⟩)
    have ordp:=(oddOrder hp odd).1
    have pk:= (hp.pow_dvd_iff_le_factorization qnz).mp jd
    rw [valuation hp odd tpos ((support hp odd tpos).mp pd)] at pk
    have jm:= (hp.pow_dvd_iff_le_factorization (Nat.sub_pos_of_lt (Nat.one_lt_two_pow ordp.ne')).ne').mpr pk
    obtain ⟨a,ha⟩:=dv
    exact jm.trans (by rw [ha,pow_mul]; simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2^orderOf (2 : ZMod p)) 1 a)

theorem support_injective {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) (eq : (((2^s-1)/Nat.gcd (2^s-1) s)).primeFactors=(((2^t-1)/Nat.gcd (2^t-1) t)).primeFactors) :
    s=t := by rw [←index hs,←index ht,eq]

theorem index_dvd {t y : ℕ} (ht : 2≤t) (hy : y≠0) (div : ((2^t-1)/Nat.gcd (2^t-1) t)∣y) :
    t∣(y.primeFactors.filter (·≠2)).lcm (fun p=>p-1) := by
  rw [←index ht]
  refine Finset.lcm_dvd fun p mem=>?_
  obtain ⟨hp,pd,_⟩:=Nat.mem_primeFactors.mp mem
  have odd : p≠2 := fun eq=>not_two (by omega) (eq ▸ pd)
  exact (primeOrder hp odd).trans (Finset.dvd_lcm (Finset.mem_filter.mpr
    ⟨Nat.mem_primeFactors.mpr ⟨hp,pd.trans div,hy⟩,odd⟩))

end OMA.MersenneOrderSupport245212


/- Four linear ratios cover every solution whose reduced denominator divides 105. -/
namespace OMA.MersenneDenominator245212

theorem four_lines {x y k : ℕ} (hy : 0 < y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) (small : y/(x.gcd y) ∣ 105) : (3*x=5*y ∨ 7*x=17*y ∨ 15*x=49*y ∨ 21*x=107*y) := by
  let t := k+1
  have ht : 2≤t := by dsimp [t]; omega
  have qd : ((2^t-1)/Nat.gcd (2^t-1) t)∣105 := (reduced hy hk quot sol) ▸ small
  have div : ((2^t-1)/Nat.gcd (2^t-1) t)∣2^12-1 := qd.trans (by decide : 105∣(2:ℕ)^12-1)
  have m := (Nat.modEq_iff_dvd' (by decide : 1≤(2:ℕ)^12) (n:=((2^t-1)/Nat.gcd (2^t-1) t))).mpr div
  rw [←ZMod.natCast_eq_natCast_iff] at m
  have pow : (2:ZMod (((2^t-1)/Nat.gcd (2^t-1) t)))^12=1 := by simpa only [Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using m.symm
  have dt := orderOf_dvd_of_pow_eq_one pow
  rw [order ht] at dt
  have up := Nat.le_of_dvd (by decide : 0<12) dt
  have can : t=2 ∨ t=3 ∨ t=4 ∨ t=6 := by
    revert qd dt
    clear_value t
    interval_cases t <;> decide +kernel
  have le : k*y≤x := by rw [quot]; exact Nat.div_mul_le_self _ _
  rcases can with a|a|a|a <;> dsimp [t] at a
  · left; have kk : k=1 := by omega
    rw [kk] at sol le; omega
  · right; left; have kk : k=2 := by omega
    rw [kk] at sol le; omega
  · right; right; left; have kk : k=3 := by omega
    rw [kk] at sol le; omega
  · right; right; right; have kk : k=5 := by omega
    rw [kk] at sol le; omega


theorem smooth_lines {x y k : ℕ} (hy : 0<y) (hk : 1≤k) (quot : k=x/y)
    (sol : 2^(k+1)*(x-k*y)=x+y) (sm : ¬(∃ p∈(y/(x.gcd y)).primeFactors, 7<p)) : (3*x=5*y ∨ 7*x=17*y ∨ 15*x=49*y ∨ 21*x=107*y) := by
  let t := k+1
  have ht : 2≤t := by dsimp [t]; omega
  have den : y/(x.gcd y)=((2^t-1)/Nat.gcd (2^t-1) t) := reduced hy hk quot sol
  rw [den] at sm
  have qnz : ((2^t-1)/Nat.gcd (2^t-1) t)≠0 := by have h := bound ht; omega
  have dt0 := OMA.MersenneOrderSupport245212.index_dvd ht qnz (dvd_refl (((2^t-1)/Nat.gcd (2^t-1) t)))
  have dt : t∣12 := dt0.trans (Finset.lcm_dvd (fun p mem => by
    obtain ⟨pf,odd⟩ := Finset.mem_filter.mp mem
    have prime := (Nat.mem_primeFactors.mp pf).1
    have le : p≤7 := by by_contra! bad; exact sm ⟨p,pf,bad⟩
    interval_cases p <;> norm_num at *))
  have top := Nat.le_of_dvd (by decide : 0<12) dt
  have good : ((2^t-1)/Nat.gcd (2^t-1) t)∣105 := by
    revert dt sm
    clear_value t
    interval_cases t <;> decide +kernel
  exact four_lines hy hk quot sol (den ▸ good)

end OMA.MersenneDenominator245212


/- The small-prime case uses four explicit linear equations. In the other
case, the distinct primes of the reduced denominator fix the exponent. -/
namespace OMA.R_OeisA245212_conjecture_R1_H2_R2_H1_R1_H2_R1
open Finset ArithmeticFunction OMA.MersenneDenominator245212 OMA.MersenneOrderSupport245212
open scoped ArithmeticFunction.sigma


/-- Four fixed linear tests for an unrestricted fourth root whose reduced
denominator has prime factors at most seven. -/
def H1 : Prop :=
  ∀ v : ℕ, (Odd v ∧ 1 < v ∧ ¬Squarefree v ∧
    (∀ s : ℕ, (∀ p : ℕ, p.Prime → p∣v^2 → p ≡ 1 [MOD 2^s]) → (v^2).divisors.card ≡ 1 [MOD 2^s]) ∧
    (v^2).divisors.card ≡ (if v%8=3 ∨ v%8=5 then 9 else 1) [MOD 16]) → let m := v^4
    let A := m*m.divisors.card; let x := A-σ 1 m
    let y := (∑ d∈m.divisors,d*d.divisors.card)-A
    0<y → ¬(∃ p∈(y/(x.gcd y)).primeFactors, 7<p) → ¬(3*x=5*y ∨ 7*x=17*y ∨ 15*x=49*y ∨ 21*x=107*y)

/-- A prime of at least eleven remains. The set of prime divisors,
ignoring multiplicity, fixes the candidate index. -/
def H2 : Prop :=
  ∀ v : ℕ, (Odd v ∧ 1 < v ∧ ¬Squarefree v ∧
    (∀ s : ℕ, (∀ p : ℕ, p.Prime → p∣v^2 → p ≡ 1 [MOD 2^s]) → (v^2).divisors.card ≡ 1 [MOD 2^s]) ∧
    (v^2).divisors.card ≡ (if v%8=3 ∨ v%8=5 then 9 else 1) [MOD 16]) → let m := v^4
    let A := m*m.divisors.card; let x := A-σ 1 m
    let y := (∑ d∈m.divisors,d*d.divisors.card)-A
    let z := y/(x.gcd y); let t := z.primeFactors.lcm (fun p : ℕ => orderOf (2 : ZMod p))
    0<y → (∃ p∈z.primeFactors, 7<p) → 2≤t → z=((2^t-1)/Nat.gcd (2^t-1) t) → x ≠ (t-1)*y+t*y/(2^t-1)

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1_H2_R2_H1_R1.H2 := by
  intro low high v vo vb rep mod1 mod2 m A F x y k hk sol
  have av : (Odd v ∧ 1 < v ∧ ¬Squarefree v ∧
    (∀ s : ℕ, (∀ p : ℕ, p.Prime → p∣v^2 → p ≡ 1 [MOD 2^s]) → (v^2).divisors.card ≡ 1 [MOD 2^s]) ∧
    (v^2).divisors.card ≡ (if v%8=3 ∨ v%8=5 then 9 else 1) [MOD 16]) := ⟨vo,vb,rep,mod1,mod2⟩
  have hy : 0<y := by
    by_contra! z
    have zero : y=0 := by omega
    change 1≤x/y at hk
    simp [zero] at hk
  have den : y/(x.gcd y)=((2^(k+1)-1)/Nat.gcd (2^(k+1)-1) (k+1)) := reduced hy hk rfl sol
  by_cases big : (∃ p∈(y/(x.gcd y)).primeFactors, 7<p)
  · have t2 : 2≤k+1 := by omega
    have ind : (y/(x.gcd y)).primeFactors.lcm (fun p : ℕ => orderOf (2 : ZMod p))=k+1 := by rw [den,index t2]
    have no := high v av
    change 0<y → (∃ p∈(y/(x.gcd y)).primeFactors, 7<p) → 2≤(y/(x.gcd y)).primeFactors.lcm (fun p : ℕ => orderOf (2 : ZMod p)) → _ at no
    rw [ind] at no
    apply no hy big t2 den
    have xy : k*y≤x := Nat.div_mul_le_self x y
    have alg : (x-k*y)*(2^(k+1)-1)=(k+1)*y := by
      have one := Nat.sub_add_cancel (Nat.one_le_pow (k+1) 2 (by decide))
      nlinarith only [sol,congrArg (fun z : ℕ=>z*(x-k*y)) one,Nat.sub_add_cancel xy]
    have pos : 0<2^(k+1)-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
    have quotient : (k+1)*y/(2^(k+1)-1)=x-k*y :=
      Nat.div_eq_of_eq_mul_left pos alg.symm
    change x=(k+1-1)*y+(k+1)*y/(2^(k+1)-1)
    rw [quotient,Nat.add_sub_cancel]
    omega
  · exact low v av hy big (smooth_lines hy hk rfl sol big)

end OMA.R_OeisA245212_conjecture_R1_H2_R2_H1_R1_H2_R1
