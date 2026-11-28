import OMAStatements.S_oeis_a284760
import Mathlib

/-! Prime-factor descent for Meštrović's quartic power-sum conjecture.
The Bernoulli criterion uses von Staudt–Clausen and Faulhaber; compare
Kellner, Proposition 8.5, for the even-power step. H1 is an order-two
Kummer congruence. There is no squarefree assumption on n. -/
namespace OMA.PowerSum284760
open Finset Nat

private theorem taylor {R : Type*} [CommRing R] (x y:R) (hy:y^2=0) (e:ℕ) :
    (x+y)^e=x^e+e*x^(e-1)*y := by
  cases e with
  | zero => simp
  | succ e =>
    induction e with
    | zero=>simp
    | succ e ih =>
      rw [pow_succ (x+y),ih]
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,pow_succ]
      linear_combination ((e:R)+1)*x^e*hy

private theorem blocks {R : Type*} [AddCommMonoid R] (f : ℕ→R) (m k : ℕ) :
    (∑i∈range (m*k),f i)=∑j∈range k,∑i∈range m,f (m*j+i) := by
  induction k with
  | zero=>simp
  | succ k ih=>rw [Nat.mul_succ,sum_range_succ,sum_range_add,ih]

private theorem blocks_cast (m k e : ℕ) :
    (∑i∈range (m*k), (i:ZMod m)^e)=(k:ZMod m)*∑i∈range m,(i:ZMod m)^e := by
  rw [blocks];simp

private theorem lift_pow_sum {p m : ℕ} (odd : Odd p) (pm : p∣m) (e : ℕ) :
    (∑i∈range (m*p),(i:ZMod (p*m))^e)=(p:ZMod (p*m))*∑i∈range m,(i:ZMod (p*m))^e := by
  have mm : (m:ZMod (p*m))^2=0 := by
    rw [←Nat.cast_pow,ZMod.natCast_eq_zero_iff,pow_two]
    exact Nat.mul_dvd_mul_right pm m
  have sum_div : p ∣ ∑j∈range p,j := by
    obtain ⟨u,h⟩:=odd
    use u
    have s:=sum_range_id_mul_two p
    rw [show p-1=2*u by omega] at s
    nlinarith only [s]
  have vanish : (m:ZMod (p*m))*(∑j∈range p,(j:ZMod (p*m)))=0 := by
    rw [←Nat.cast_sum,←Nat.cast_mul,ZMod.natCast_eq_zero_iff,Nat.mul_comm p m]
    exact Nat.mul_dvd_mul_left m sum_div
  rw [blocks,sum_comm,mul_sum]
  apply sum_congr rfl
  intro i _
  calc
    _=∑j∈range p, ((i:ZMod (p*m))^e + ((e:ZMod (p*m))*i^(e-1)*m)*j) := by
      apply sum_congr rfl;intro j _
      push_cast
      rw [add_comm,taylor (i:ZMod (p*m)) (_*_) (by rw [mul_pow,mm,zero_mul])]
      ring
    _ = _ := by
      rw [sum_add_distrib,←mul_sum,mul_assoc _ (m:ZMod (p*m)),vanish,mul_zero,add_zero,sum_const,card_range,nsmul_eq_mul]

private theorem base_nonzero {p e : ℕ} (hp:p.Prime) (ep:0<e) (he:p-1∣e) :
    (∑ i∈range p,(i:ZMod p)^e)≠0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h1:=sum_range_add_sum_Ico (fun i:ℕ=>(i:ZMod p)^e) hp.one_le
  rw [←h1]
  have same (i) (hi:i∈Ico 1 p) : (i:ZMod p)^e=1 := by
    have nz : (i:ZMod p)≠0 := by
      intro h
      have := Nat.le_of_dvd (mem_Ico.mp hi).1 ((ZMod.natCast_eq_zero_iff ..).mp h)
      exact (mem_Ico.mp hi).2.not_ge this
    obtain ⟨a,ha⟩:=he
    rw [ha,pow_mul,ZMod.pow_card_sub_one_eq_one nz,one_pow]
  simp only [sum_congr rfl same,sum_const,Nat.card_Ico,nsmul_eq_mul,mul_one]
  simp [zero_pow ep.ne',Nat.cast_sub hp.one_le]

/-- For a positive exponent divisible by p−1, the complete sum is not a
multiple of n whenever n is an odd multiple of p. -/
private theorem obstruction {p e : ℕ} (hp : p.Prime) (odd : Odd p) (ep:0<e)
    (he:p-1∣e) (n:ℕ) (np:0<n) (div:p∣n) : ¬n∣∑i∈range n,i^e := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m,rfl⟩:=div
    have mp : 0 < m := Nat.pos_of_mul_pos_left np
    by_cases pm : p∣m
    · intro hz
      have hzero: (∑i∈range (m*p),(i:ZMod (p*m))^e)=0 := by
        simpa only [mul_comm m p,←Nat.cast_pow,←Nat.cast_sum,ZMod.natCast_eq_zero_iff] using hz
      rw [lift_pow_sum odd pm e] at hzero
      simp only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul,ZMod.natCast_eq_zero_iff] at hzero
      exact ih m (by nlinarith only [hp.one_lt,mp]) mp pm (Nat.dvd_of_mul_dvd_mul_left hp.pos hzero)
    · intro hz
      have hzero : (∑i∈range (p*m),(i:ZMod p)^e)=0 := by
        simpa only [←Nat.cast_pow,←Nat.cast_sum,ZMod.natCast_eq_zero_iff] using
          (show p∣∑i∈range (p*m),i^e from (dvd_mul_right p m).trans hz)
      rw [blocks_cast] at hzero
      let _ : Fact p.Prime:=⟨hp⟩
      exact (mul_ne_zero (fun hm=>(pm ((ZMod.natCast_eq_zero_iff ..).mp hm))) (base_nonzero hp ep he)) hzero

private theorem reflect {n e : ℕ} (he : Odd e) :
    2*(∑i∈Ico 1 n,(i:ZMod (n^2))^e)=
      (n:ZMod (n^2))*e*(∑i∈Ico 1 n,(i:ZMod (n^2))^(e-1)) := by
  let R:= ZMod (n^2)
  have sq : (n:R)^2=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have mirror : (∑i∈Ico 1 n,((n-i:ℕ):R)^e)=∑i∈Ico 1 n,(i:R)^e := by
    apply sum_bij' (fun i _=>n-i) (fun i _=>n-i)
    all_goals intro i hi;obtain ⟨low,high⟩:=mem_Ico.mp hi
    all_goals first | exact mem_Ico.mpr ⟨by omega,by omega⟩ | omega | rfl
  have ev : Even (e-1) := by obtain ⟨b,hb⟩:=he;exact ⟨b,by omega⟩
  rw [two_mul]
  nth_rw 1 [←mirror]
  rw [←sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [Nat.cast_sub (mem_Ico.mp hi).2.le,sub_eq_neg_add,taylor _ _ sq,he.neg_pow,ev.neg_pow]
  ring

/-- A prime with p−1 ∣ n−3 already obstructs divisibility by n². -/
theorem local_obstruction {n p:ℕ} (odd:Odd n) (hp:p.Prime) (pn:p∣n) (he:p-1∣n-3) :
    ¬ n^2∣∑i∈Ico 1 n,i^(n-2) := by
  have pos:=odd.pos
  have hn:=Nat.le_of_dvd pos pn
  have po : Odd p := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr odd).of_dvd_right pn)
  have big : 3≤n := by have :=hp.two_le;obtain ⟨b,h⟩:=odd;omega
  by_cases eq : n=3
  · subst n;decide
  have exp : 0<n-3 := by omega
  have eodd : Odd (n-2) := by obtain ⟨b,h⟩:=odd;exact ⟨b-1,by omega⟩
  intro zz
  have val := reflect (n:=n) eodd
  have left : (∑i∈Ico 1 n,(i:ZMod (n^2))^(n-2))=0 := by
    simpa only [←Nat.cast_pow,←Nat.cast_sum,ZMod.natCast_eq_zero_iff] using zz
  rw [left,mul_zero,show n-2-1=n-3 by omega] at val
  have sqdiv : n^2∣n*(n-2)*(∑i∈Ico 1 n,i^(n-3)) := by
    simpa only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul,ZMod.natCast_eq_zero_iff] using val.symm
  rw [pow_two,mul_assoc n] at sqdiv
  have cut:=Nat.dvd_of_mul_dvd_mul_left pos sqdiv
  have cop : n.Coprime (n-2) :=
    (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_two_right.mpr odd)
  have dvd:=cop.dvd_of_dvd_mul_left cut
  have id := sum_range_add_sum_Ico (fun i:ℕ=>i^(n-3)) (show 1≤n by omega)
  have conv : (∑i∈Ico 1 n,i^(n-3))=∑i∈range n,i^(n-3) := by
    simpa [zero_pow exp.ne'] using id
  exact obstruction hp po exp he n pos pn (conv ▸ dvd)

end OMA.PowerSum284760

/-! A second-order local test for odd A284760 counterexamples, including primes
where the first complete power-sum obstruction vanishes. -/
namespace OMA.PowerSumRegular284760
open Finset Nat

private theorem quad {R : Type*} [CommRing R] (x y:R) (hy:y^3=0) (e:ℕ) :
    (x+y)^e=x^e+e*x^(e-1)*y+(e.choose 2:R)*x^(e-2)*y^2 := by
  cases e with
  | zero=>simp
  | succ e=>
    cases e with
    | zero=>simp
    | succ a=>
      induction a with
      | zero=>norm_num [pow_two];ring
      | succ a ih=>
        rw [pow_succ (x+y),ih,Nat.choose_succ_succ (a+2) 1]
        simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one,Nat.succ_sub_succ_eq_sub,
          Nat.sub_zero,Nat.cast_ofNat,pow_succ]
        linear_combination ((a+2).choose 2:R)*x^a*hy

private theorem mirror {R : Type*} [AddCommMonoid R] (n:ℕ) (f:ℕ→R) :
    (∑i∈Ico 1 n,f (n-i))=∑i∈Ico 1 n,f i := by
  apply sum_bij' (fun i _=>n-i) (fun i _=>n-i)
  all_goals intro i hi;obtain ⟨lo,hi⟩:=mem_Ico.mp hi
  all_goals first | exact mem_Ico.mpr ⟨by omega,by omega⟩ | omega | rfl

private theorem ico_range {f:ℕ→ℕ} {n:ℕ} (np:0<n) (z:f 0=0) :
    (∑i∈Ico 1 n,f i)=∑i∈range n,f i := by
  simpa [z] using sum_range_add_sum_Ico f np

private theorem odd_sum {n e:ℕ} (on:Odd n) (oe:Odd e) : n∣∑i∈Ico 1 n,i^e := by
  have ref:=mirror n (fun i:ℕ=>(i:ZMod n)^e)
  have rev (i) (hi:i∈Ico 1 n) : ((n-i:ℕ):ZMod n)^e = -(i:ZMod n)^e := by
    rw [Nat.cast_sub (mem_Ico.mp hi).2.le,ZMod.natCast_self,zero_sub,oe.neg_pow]
  rw [sum_congr rfl rev,sum_neg_distrib] at ref
  have two : 2*(∑i∈Ico 1 n,(i:ZMod n)^e)=0 := by linear_combination -ref
  apply (Nat.coprime_two_right.mpr on).dvd_of_dvd_mul_left
  exact (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact two)

private theorem reflect3 {n e : ℕ} (on:Odd n) (oe:Odd e) (big:3≤e) :
    2*(∑i∈Ico 1 n,(i:ZMod (n^3))^e)=
      (n:ZMod (n^3))*e*(∑i∈Ico 1 n,(i:ZMod (n^3))^(e-1)) := by
  let R:=ZMod (n^3)
  have z : (n:R)^3=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have ev : Even (e-1) := by obtain ⟨b,hb⟩:=oe;exact ⟨b,by omega⟩
  have od : Odd (e-2) := by obtain ⟨b,hb⟩:=oe;exact ⟨b-1,by omega⟩
  have vanish : (n:R)^2*(∑i∈Ico 1 n,(i:R)^(e-2))=0 := by
    simp only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul]
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    rw [show (3:ℕ)=2+1 by decide,pow_succ]
    exact Nat.mul_dvd_mul_left _ (odd_sum on od)
  rw [two_mul]
  nth_rw 1 [←mirror n (fun i=>(i:R)^e)]
  rw [←sum_add_distrib]
  calc
    _=∑i∈Ico 1 n, ((n:R)*e*(i:R)^(e-1) - (e.choose 2:R)*n^2*(i:R)^(e-2)) := by
      apply sum_congr rfl;intro i hi
      rw [Nat.cast_sub (mem_Ico.mp hi).2.le,sub_eq_neg_add,quad _ _ z,
        oe.neg_pow,ev.neg_pow,od.neg_pow];ring
    _=_ := by rw [sum_sub_distrib,←mul_sum,←mul_sum,mul_assoc _ ((n:R)^2),vanish,mul_zero,sub_zero]

private theorem div_linear {p:ℕ} (odd:Odd p) : p∣∑j∈range p,j := by
  obtain ⟨u,h⟩:=odd
  refine ⟨u,?_⟩
  have s:=sum_range_id_mul_two p
  rw [show p-1=2*u by omega] at s
  nlinarith only [s]

private theorem div_square {p:ℕ} (hp:p.Prime) (big:5≤p) : p∣∑j∈range p,j^2 := by
  have formula (b:ℕ) : 6*(∑j∈range b,j^2)+3*b^2=2*b^3+b := by
    induction b with
    | zero=>simp
    | succ b ih=>rw [sum_range_succ];nlinarith only [ih]
  have h : p∣6*(∑j∈range p,j^2) := by
    apply (Nat.dvd_add_left (show p∣3*p^2 from dvd_mul_of_dvd_right (dvd_pow_self p (by decide : 2≠0)) _)).mp
    rw [formula];exact dvd_add (dvd_mul_of_dvd_right (dvd_pow_self p (by decide : 3≠0)) _) (dvd_refl p)
  apply (hp.dvd_mul.mp h).resolve_left
  intro hd
  change p ∣ 2*3 at hd
  rcases hp.dvd_mul.mp hd with a|a
  · have :=Nat.le_of_dvd (by decide : 0<2) a;omega
  · have :=Nat.le_of_dvd (by decide : 0<3) a;omega

/-- Sum the second-order expansion over a rectangle of complete blocks. -/
private theorem moments {R:Type*} [CommRing R] (m k e:ℕ) (zero:(m:R)^3=0) :
    (∑i∈range (m*k),(i:R)^e)=
    k*(∑i∈range m,(i:R)^e) +
    (e:R)*(m:R)*(∑j∈range k,(j:R))*(∑i∈range m,(i:R)^(e-1))+
    (e.choose 2:R)*(m:R)^2*(∑j∈range k,(j:R)^2)*(∑i∈range m,(i:R)^(e-2)) := by
  rw [OMA.PowerSum284760.blocks,sum_comm]
  calc
    _ = ∑i∈range m, ∑j∈range k, ((i:R)^e +
          ((e:R)*m*(i:R)^(e-1))*j + ((e.choose 2:R)*(m:R)^2*(i:R)^(e-2))*j^2) := by
      apply sum_congr rfl;intro i _
      apply sum_congr rfl;intro j _
      push_cast
      rw [add_comm,quad (i:R) (_*_) (by rw [mul_pow,zero,zero_mul])]
      ring
    _ = ∑i∈range m, ((k:R)*(i:R)^e +
         ((e:R)*m*(∑j∈range k,(j:R)))*(i:R)^(e-1)+
         ((e.choose 2:R)*(m:R)^2*(∑j∈range k,(j:R)^2))*(i:R)^(e-2)) := by
      apply sum_congr rfl;intro i _
      simp only [sum_add_distrib,←mul_sum,sum_const,card_range,nsmul_eq_mul]
      ring
    _ = _ := by simp only [sum_add_distrib,←mul_sum]

private theorem odd_range {n e:ℕ} (on:Odd n) (oe:Odd e) : n∣∑i∈range n,i^e := by
  rw [←ico_range on.pos (by exact zero_pow oe.pos.ne')]
  exact odd_sum on oe

private theorem lift_two {p m e : ℕ} (hp:p.Prime) (big:5≤p) (pm:p∣m)
    (om:Odd m) (odd:Odd (e-1)) :
    (∑i∈range (m*p),(i:ZMod (p^2*m))^e)=
      (p:ZMod (p^2*m))*∑i∈range m,(i:ZMod (p^2*m))^e := by
  let R:=ZMod (p^2*m)
  have vanish (a:ℕ) (h:p^2*m∣a) : (a:R)=0 := (ZMod.natCast_eq_zero_iff ..).mpr h
  have cube : (m:R)^3=0 := by
    rw [←Nat.cast_pow]; apply vanish;rw [pow_succ];exact Nat.mul_dvd_mul_right (pow_dvd_pow_of_dvd pm 2) m
  have lin : (m:R)*(∑j∈range p,(j:R))*(∑i∈range m,(i:R)^(e-1))=0 := by
    have h : p^2*m ∣ m*(∑j∈range p,j)*(∑i∈range m,i^(e-1)) := by
      obtain ⟨u,hu⟩:=div_linear (hp.odd_of_ne_two (by omega))
      obtain ⟨v,hv⟩:=pm.trans (odd_range om odd)
      use u*v;rw [hu,hv];ring
    simpa only [R,Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using vanish _ h
  have sq : (m:R)^2*(∑j∈range p,(j:R)^2)=0 := by
    simp only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul];apply vanish
    obtain ⟨u,hu⟩:=pm;obtain ⟨v,hv⟩:=div_square hp big
    use u*v;rw [hu,hv];ring
  rw [moments (R:=R) m p e cube]
  linear_combination (e:R)*lin + (e.choose 2:R)*(∑i∈range m,(i:R)^(e-2))*sq

private theorem first_block {p m e : ℕ} (op:Odd p) (od:Odd (e-1)) :
    (∑i∈range (p*m),(i:ZMod (p^2))^e)=(m:ZMod (p^2))*∑i∈range p,(i:ZMod (p^2))^e := by
  let R:=ZMod (p^2)
  have sq : (p:R)^2=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have lin : (p:R)*(∑i∈range p,(i:R)^(e-1))=0 := by
    have h : p^2 ∣ p*(∑i∈range p,i^(e-1)) := by
      rw [pow_two];exact Nat.mul_dvd_mul_left _ (odd_range op od)
    simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr h
  rw [moments (R:=R) p m e (by rw [pow_succ,sq,zero_mul]),sq];simp only [mul_zero,zero_mul,add_zero]
  linear_combination (e:R)*(∑j∈range m,(j:R))*lin

private theorem shrink {p e : ℕ} (hp : p.Prime) (big:5≤p) (od:Odd (e-1))
    (n:ℕ) (on:Odd n) (pn:p∣n) (hs:p*n∣∑i∈range n,i^e) : p^2∣∑i∈range p,i^e := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m,rfl⟩:=pn
    have mp:=Nat.pos_of_mul_pos_left on.pos
    have op := hp.odd_of_ne_two (by omega)
    have om : Odd m := (Nat.odd_mul.mp on).2
    rw [←mul_assoc,pow_two p|>.symm] at hs
    by_cases pm:p∣m
    · have hzero : (∑i∈range (m*p),(i:ZMod (p^2*m))^e)=0 := by
        simpa only [mul_comm m p,Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr hs
      rw [lift_two hp big pm om od] at hzero
      have hz : p^2*m∣p*(∑i∈range m,i^e) := (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact hzero)
      rw [pow_two,mul_assoc] at hz
      exact ih m (by nlinarith only [hp.one_lt,mp]) om pm (Nat.dvd_of_mul_dvd_mul_left hp.pos hz)
    · have hzero : (∑i∈range (p*m),(i:ZMod (p^2))^e)=0 := by
        simpa only [Nat.cast_sum,Nat.cast_pow] using
          (ZMod.natCast_eq_zero_iff _ _).mpr ((dvd_mul_right (p^2) m).trans hs)
      rw [first_block op od] at hzero
      apply ((hp.coprime_iff_not_dvd.mpr pm).pow_left 2).dvd_of_dvd_mul_left
      exact (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact hzero)

/-- Every prime divisor of an odd counterexample must already pass this
complete residue test modulo its square, regardless of its multiplicity. -/
theorem prime_test {n p:ℕ} (on:Odd n) (hp:p.Prime) (big:5≤p) (pn:p∣n)
    (hz:n^4∣∑i∈Ico 1 n,i^(n-2)) : p^2∣∑i∈Ico 1 p,i^(n-3) := by
  have np:=on.pos
  have nn:=Nat.le_of_dvd np pn
  have od : Odd (n-2) := by obtain ⟨k,h⟩:=on;exact ⟨k-1,by omega⟩
  have od' : Odd (n-3-1) := by obtain ⟨k,h⟩:=on;exact ⟨k-2,by omega⟩
  have val := reflect3 on od (by omega)
  have zeros : (∑i∈Ico 1 n,(i:ZMod (n^3))^(n-2))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr
      ((pow_dvd_pow n (by decide : 3≤4)).trans hz)
  rw [zeros,mul_zero,show n-2-1=n-3 by omega] at val
  have dv : n^3∣n*((n-2)*(∑i∈Ico 1 n,i^(n-3))) :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;rw [←mul_assoc];exact val.symm)
  have cop : n.Coprime (n-2) :=
    (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_two_right.mpr on)
  rw [pow_succ'] at dv
  have sq := (cop.pow_left 2).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left np dv)
  rw [ico_range np (by exact zero_pow (by omega : n-3≠0))] at sq
  rw [ico_range hp.pos (by exact zero_pow (by omega : n-3≠0))]
  exact shrink hp big od' n on pn ((show p*n∣n^2 by rw [pow_two];exact Nat.mul_dvd_mul_right pn n).trans sq)

end OMA.PowerSumRegular284760

/-! Faulhaber at the actual exponent n−2.  Since its denominator n−1
is a unit at every prime dividing n, all but one of the top terms can be
controlled directly with von Staudt–Clausen. -/
namespace OMA.BernoulliScreen284760
open Finset Nat
open private Bernoulli.not_dvd_den_bernoulli_add_indicator Bernoulli.vonStaudtIndicator from Mathlib.NumberTheory.Bernoulli


private theorem integral_iff {p:ℕ} [Fact p.Prime] (x:ℚ) :
    x∈(Rat.padicValuation p).integer ↔ ¬p∣x.den := Rat.padicValuation_le_one_iff

private theorem bernoulli_integral {p i:ℕ} [Fact p.Prime] (ip : 0 < i)
    (ei:Even i) (nd:¬p-1∣i) : bernoulli i∈(Rat.padicValuation p).integer := by
  obtain ⟨k,h⟩:=ei
  have hh:i=2*k:=by omega
  clear h
  subst i
  have x:=Bernoulli.not_dvd_den_bernoulli_add_indicator (p:=p) (k:=k) (by omega)
  apply (integral_iff _).mpr
  simpa [Bernoulli.vonStaudtIndicator,nd] using x

private theorem p_bernoulli {p:ℕ} [Fact p.Prime] (hp:5≤p) (i:ℕ) :
    (p:ℚ)*bernoulli i∈(Rat.padicValuation p).integer := by
  by_cases iz:i=0
  · subst i;simp
  by_cases io:i=1
  · subst i;apply ((Rat.padicValuation p).integer).mul_mem (natCast_mem ((Rat.padicValuation p).integer) _) ((integral_iff _).mpr ?_)
    norm_num [bernoulli_one];intro d;have :=Nat.le_of_dvd (by decide : 0<2) d;omega
  rcases Nat.even_or_odd i with ev|od
  · obtain ⟨k,h⟩:=ev;have hh:i=2*k:=by omega
    clear h
    subst i
    have z:=(integral_iff _).mpr (Bernoulli.not_dvd_den_bernoulli_add_indicator (p:=p) (k:=k) (by omega))
    have mult:=((Rat.padicValuation p).integer).mul_mem (natCast_mem ((Rat.padicValuation p).integer) p) z
    by_cases d:p-1∣2*k
    · have nz:(p:ℚ)≠0:=by exact_mod_cast (Fact.out : p.Prime).ne_zero
      have ident:(p:ℚ)*bernoulli (2*k)=p*(bernoulli (2*k)+1/p)-1:=by field_simp;ring
      rw [ident]
      apply ((Rat.padicValuation p).integer).sub_mem _ ((Rat.padicValuation p).integer).one_mem
      simpa [Bernoulli.vonStaudtIndicator,d] using mult
    · simpa [Bernoulli.vonStaudtIndicator,d] using mult
  · rw [bernoulli_eq_zero_of_odd od (by omega),mul_zero];exact ((Rat.padicValuation p).integer).zero_mem

private theorem scaled_terms {p n b:ℕ} [Fact p.Prime] (hp:5≤p)
    (nn:0<n) (pn:p∣n) (i:ℕ) (lt:i<b) :
    bernoulli i*((b+4).choose i:ℚ)*(n:ℚ)^(b+4-i)/(n:ℚ)^4 ∈(Rat.padicValuation p).integer := by
  obtain ⟨u,hu⟩:=pn
  have hpow : b+4-i=(b-i-1)+1+4:=by omega
  have nz:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  have hm:(n:ℚ)=(p:ℚ)*u:=by exact_mod_cast hu
  have id : bernoulli i*((b+4).choose i:ℚ)*(n:ℚ)^(b+4-i)/(n:ℚ)^4 =
      (p*bernoulli i)*u*((b+4).choose i:ℚ)*(n:ℚ)^(b-i-1) := by
    rw [hpow,pow_add _ _ 4,pow_succ];field_simp;rw [hm];ring
  rw [id]
  exact ((Rat.padicValuation p).integer).mul_mem (((Rat.padicValuation p).integer).mul_mem (((Rat.padicValuation p).integer).mul_mem (p_bernoulli hp i)
    (natCast_mem ((Rat.padicValuation p).integer) u)) (natCast_mem ((Rat.padicValuation p).integer) _))
    (((Rat.padicValuation p).integer).pow_mem (natCast_mem ((Rat.padicValuation p).integer) _) _)

private theorem principal {n p b:ℕ} [Fact p.Prime] (hp:7≤p) (nform:n=b+5)
    (eb:Even b) (pn:p∣n) (nd:¬p-1∣b) (sq:n^4∣∑i∈range n,i^(b+3)) :
    bernoulli (b+2)*((b+4).choose (b+2):ℚ)/(n:ℚ)^2 ∈(Rat.padicValuation p).integer := by
  have nn:0<n:=by omega
  have bpos:0<b:=by have :=Nat.le_of_dvd nn pn;omega
  have nz:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  let f (i:ℕ) := bernoulli i*((b+4).choose i:ℚ)*(n:ℚ)^(b+4-i)/(n:ℚ)^4
  have integral : (∑i∈range (b+4),f i)∈(Rat.padicValuation p).integer := by
    obtain ⟨c,hc⟩:=sq
    have faul:=sum_range_pow n (b+3)
    have scast : (∑i∈range n,(i:ℚ)^(b+3))=(n:ℚ)^4*c:=by exact_mod_cast hc
    rw [scast,←Finset.sum_div] at faul
    have den:(b+3+1:ℚ)≠0:=by positivity
    have alg: (∑i∈range (b+4),f i)= (b+3+1:ℚ)*c := by
      unfold f;rw [←Finset.sum_div]
      rw [div_eq_iff (pow_ne_zero 4 nz)]
      push_cast at faul
      have v:=(eq_div_iff den).mp faul
      linear_combination -v
    rw [alg];exact ((Rat.padicValuation p).integer).mul_mem (by exact_mod_cast natCast_mem ((Rat.padicValuation p).integer) (b+3+1)) (natCast_mem ((Rat.padicValuation p).integer) c)
  have early : (∑i∈range b,f i)∈(Rat.padicValuation p).integer :=
    ((Rat.padicValuation p).integer).sum_mem (fun i hi=>scaled_terms (by omega : 5≤p) nn pn i (mem_range.mp hi))
  have fb : f b∈(Rat.padicValuation p).integer := by
    have nb:=bernoulli_integral bpos eb nd
    have eq:f b=bernoulli b*((b+4).choose b:ℚ):=by dsimp [f];rw [show b+4-b=4 by omega];field_simp
    rw [eq];exact ((Rat.padicValuation p).integer).mul_mem nb (natCast_mem ((Rat.padicValuation p).integer) _)
  have odd1:Odd (b+1):=by obtain ⟨t,ht⟩:=eb;exact ⟨t,by omega⟩
  have odd3:Odd (b+3):=by obtain ⟨t,ht⟩:=eb;exact ⟨t+1,by omega⟩
  have z1:f (b+1)=0:=by simp [f,bernoulli_eq_zero_of_odd odd1 (by omega)]
  have z3:f (b+3)=0:=by simp [f,bernoulli_eq_zero_of_odd odd3 (by omega)]
  rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,z1,z3,add_zero,add_zero] at integral
  have last:= ((Rat.padicValuation p).integer).sub_mem integral (((Rat.padicValuation p).integer).add_mem early fb)
  rw [add_sub_cancel_left] at last
  have eq:f (b+2)=bernoulli (b+2)*((b+4).choose (b+2):ℚ)/(n:ℚ)^2:=by
    dsimp [f];rw [show b+4-(b+2)=2 by omega];field_simp
  simpa only [eq] using last

private theorem numerator_of_scaled_integral {p n a c:ℕ} [Fact p.Prime] (q:ℚ)
    (nn:0<n) (pn:p^a∣n) (pc:p.Coprime c)
    (mem:q*c/(n:ℚ)^2∈(Rat.padicValuation p).integer) : p^(2*a)∣q.num.natAbs := by
  let x:=q*c/(n:ℚ)^2
  have dx:¬p∣x.den:=(integral_iff _).mp mem
  have nz:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  have alg : (x.num:ℚ)*q.den*(n:ℚ)^2=q.num*c*x.den := by
    have h : (x.num:ℚ)/x.den=((q.num:ℚ)/q.den)*c/(n:ℚ)^2 := by
      rw [Rat.num_div_den,Rat.num_div_den]
    have xd:(x.den:ℚ)≠0:=by exact_mod_cast x.den_ne_zero
    have qd:(q.den:ℚ)≠0:=by exact_mod_cast q.den_ne_zero
    field_simp at h;linear_combination h
  have ints : x.num*(q.den:ℤ)*(n:ℤ)^2=q.num*c*x.den := by exact_mod_cast alg
  have natid:=congrArg Int.natAbs ints
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast] at natid
  have left:p^(2*a)∣n^2 := by
    rw [mul_comm 2 a,pow_mul];exact pow_dvd_pow_of_dvd pn 2
  have prod := dvd_mul_of_dvd_right left (x.num.natAbs*q.den)
  rw [natid,mul_assoc] at prod
  exact ((pc.mul_right ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr dx)).pow_left (2*a)).dvd_of_dvd_mul_right prod

/-- If p−1 does not divide n−5, a counterexample forces the full square of
each p-power divisor of n to divide the Bernoulli numerator at n−3. -/
theorem square_bernoulli {n p a:ℕ} (hp:p.Prime) (large:7≤p) (on:Odd n)
    (pos:0<a) (dvd:p^a∣n) (nonres:¬p-1∣n-5)
    (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) : p^(2*a)∣(bernoulli (n-3)).num.natAbs := by
  let _ : Fact p.Prime:=⟨hp⟩
  have pn:= (dvd_pow_self _ pos.ne').trans dvd
  have lg:=Nat.le_of_dvd on.pos pn
  let b:=n-5
  have nf:n=b+5:=by dsimp [b];omega
  have ev:Even b:=by obtain ⟨j,hj⟩:=on;exact ⟨j-2,by dsimp [b];omega⟩
  have exp:n-2=b+3:=by omega
  have exp':n-3=b+2:=by omega
  have cd:p.Coprime ((b+4).choose (b+2)) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have id:2*((b+4).choose (b+2))=(b+4)*(b+3) := by
      rw [Nat.choose_symm_of_eq_add (show b+4=(b+2)+2 by omega),Nat.choose_two_right]
      have even:2∣(b+4)*(b+3):=dvd_mul_of_dvd_left (show 2∣b+4 from ev.add (by decide : Even 4) |>.two_dvd) _
      rw [show b+4-1=b+3 by omega,Nat.mul_div_cancel' even]
    have d:=(dvd_mul_of_dvd_right h 2);rw [id] at d
    rcases hp.dvd_mul.mp d with d|d
    · have dd:p∣1:=by apply (Nat.dvd_add_left d).mp;simpa only [nf,show b+4+1=b+5 by omega,add_comm 1 (b+4)] using pn
      exact hp.not_dvd_one dd
    · have dd:p∣2:=by apply (Nat.dvd_add_left d).mp;simpa only [nf,show b+3+2=b+5 by omega,add_comm 2 (b+3)] using pn
      have :=Nat.le_of_dvd (by decide : 0<2) dd;omega
  rw [exp] at bad
  have split:=sum_range_add_sum_Ico (fun i:ℕ=>i^(b+3)) on.pos
  have same:(∑i∈Ico 1 n,i^(b+3))=∑i∈range n,i^(b+3):=by simpa using split
  rw [same] at bad
  rw [exp']
  exact numerator_of_scaled_integral _ on.pos dvd cd (principal large nf ev pn nonres bad)

end OMA.BernoulliScreen284760

namespace OMA.DoubleBernoulli284760
open Nat Finset

private theorem perm {R:Type*} [AddCommMonoid R] (p:ℕ) (odd:Odd p) (f:ℕ→R):
    (∑i∈range p,f ((2*i)%p))=∑i∈range p,f i := by
  let u:=(p+1)/2
  have id:2*u=p+1:=by dsimp [u];obtain ⟨t,h⟩:=odd;omega
  have inv (i:ℕ) (hi:i<p) : (2*u*i)%p=i := by
    rw [id,add_mul,one_mul,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hi]
  apply sum_bij' (fun i _=>(2*i)%p) (fun i _=>(u*i)%p)
  · intro i _;exact mem_range.mpr (Nat.mod_lt _ odd.pos)
  · intro i _;exact mem_range.mpr (Nat.mod_lt _ odd.pos)
  · intro i hi;rw [Nat.mul_mod_mod,←mul_assoc,mul_comm u 2];exact inv _ (mem_range.mp hi)
  · intro i hi;rw [Nat.mul_mod_mod,←mul_assoc];exact inv _ (mem_range.mp hi)
  · intro _ _;rfl

private theorem weight (h:ℕ) :
    (∑i∈range (2*h+1), ((2*i)/(2*h+1))*((2*i)%(2*h+1)))=h^2 := by
  conv_lhs => arg 1;rw [show 2*h+1=(h+1)+h by omega]
  rw [sum_range_add]
  have first (i:ℕ) (hi:i∈range (h+1)) : ((2*i)/(2*h+1))*((2*i)%(2*h+1))=0:=by
    have :=mem_range.mp hi;rw [Nat.div_eq_of_lt (by omega),zero_mul]
  have last (i:ℕ) (hi:i∈range h) :
      ((2*(h+1+i))/(2*h+1))*((2*(h+1+i))%(2*h+1))=2*i+1:=by
    have ih:=mem_range.mp hi
    rw [show 2*(h+1+i)=(2*i+1)+(2*h+1) by omega,Nat.add_div_right _ (by omega),
        Nat.div_eq_of_lt (by omega),Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)];simp
  rw [sum_congr rfl first,sum_congr rfl last,sum_const_zero,zero_add,sum_add_distrib,
    ←mul_sum,sum_const,card_range,nsmul_eq_mul,mul_one]
  cases h with
  | zero=>simp
  | succ h=>
    have id:=sum_range_id_mul_two (h+1)
    rw [Nat.add_sub_cancel] at id;nlinarith only [id]

/-- Under the square-local test, doubling the representatives forces one
weighted half-residue sum to vanish modulo p. -/
private theorem weight_zero {e p:ℕ} (hp:p.Prime) (odd:Odd p)
    (de:¬p∣e) (he:p^2∣∑i∈range p,i^e) :
    p∣∑i∈range p, (2*i/p)*((2*i)%p)^(e-1) := by
  let R:=ZMod (p^2)
  have sq:(p:R)^2=0:=by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have base : (∑i∈range p,(i:R)^e)=0 := by
    simpa only [Nat.cast_pow,Nat.cast_sum] using (ZMod.natCast_eq_zero_iff _ _).mpr he
  have eq (i:ℕ) : ((2*i:ℕ):R)^e = (((2*i)%p:ℕ):R)^e+
      ((p:R)*e)*((2*i/p:ℕ):R)*(((2*i)%p:ℕ):R)^(e-1) := by
    calc
      _ = ((((2*i)%p:ℕ):R)+(p:R)*((2*i/p:ℕ):R))^e := by
        congr 1
        simpa only [R,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun a:ℕ=>(a:ZMod (p^2))) (Nat.mod_add_div (2*i) p).symm
      _ = _ := by rw [OMA.PowerSum284760.taylor _ _ (by rw [mul_pow,sq,zero_mul])];ring
  have tot := sum_congr (s₁:=range p) rfl (fun i _=>eq i)
  rw [sum_add_distrib,perm p odd (fun i=>(i:R)^e)] at tot
  have lm : (∑i∈range p,((2*i:ℕ):R)^e)=0 := by
    change (∑i∈range p,((2*i:ℕ):ZMod (p^2))^e)=0
    simp only [Nat.cast_mul,Nat.cast_ofNat,mul_pow,←mul_sum];rw [base,mul_zero]
  rw [lm,base,zero_add] at tot
  have val : (p:R)*((e:R)*(∑i∈range p, ((2*i/p:ℕ):R)*(((2*i)%p:ℕ):R)^(e-1)))=0 := by
    rw [mul_sum,mul_sum];simpa only [mul_assoc] using tot.symm
  have dv:p^2∣p*(e*(∑i∈range p, (2*i/p)*((2*i)%p)^(e-1))) :=
    (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact val)
  rw [pow_two] at dv
  exact (hp.coprime_iff_not_dvd.mpr de).dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hp.pos dv)

/-- The missing second Bernoulli index is impossible for an actual odd
counterexample: its half-residue sum would be a nonzero triangular number. -/
theorem not_two_of_test {n p:ℕ} (hp:p.Prime) (big:5≤p) (on:Odd n) (pn:p∣n)
    (h:p^2∣∑i∈range p,i^(n-3)) : ¬p-1∣n-5 := by
  have nn:=Nat.le_of_dvd on.pos pn
  have op:=hp.odd_of_ne_two (by omega)
  have de:¬p∣n-3 := by
    intro dv
    have dd:p∣3 := (Nat.dvd_add_left dv).mp (by rwa [Nat.add_sub_cancel' (by omega : 3≤n)])
    have := Nat.le_of_dvd (by decide : 0<3) dd;omega
  have half:=weight_zero hp op de h
  intro twice
  obtain ⟨q,hq⟩:=twice
  have exp:n-3-1=1+(p-1)*q:=by omega
  let _ : Fact p.Prime:=⟨hp⟩
  have same (a:ℕ) : ((a%p:ℕ):ZMod p)^(n-3-1)=((a%p:ℕ):ZMod p) := by
    by_cases z:((a%p:ℕ):ZMod p)=0
    · rw [z,zero_pow (by omega : n-3-1≠0)]
    · rw [exp,pow_add,pow_mul,ZMod.pow_card_sub_one_eq_one z,one_pow,pow_one,mul_one]
  have z1 : (∑i∈range p,((2*i/p:ℕ):ZMod p)*(((2*i)%p:ℕ):ZMod p)^(n-3-1))=0 := by
    simpa only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr half
  simp_rw [same] at z1
  have dw : p∣∑i∈range p,(2*i/p)*((2*i)%p) := (ZMod.natCast_eq_zero_iff _ _).mp (by
    simpa only [Nat.cast_sum,Nat.cast_mul] using z1)
  obtain ⟨b,hb⟩:=op
  rw [hb,weight] at dw
  have pb:(2*b+1).Prime:=hb ▸ hp
  have small: 2*b+1 ≤ b := Nat.le_of_dvd (by omega) (pb.dvd_of_dvd_pow dw)
  omega

theorem not_two {n p:ℕ} (hp:p.Prime) (big:5≤p) (on:Odd n) (pn:p∣n)
    (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) : ¬p-1∣n-5 := by
  have nn:=Nat.le_of_dvd on.pos pn
  have h:=OMA.PowerSumRegular284760.prime_test on hp big pn bad
  rw [OMA.PowerSumRegular284760.ico_range hp.pos (by exact zero_pow (by omega : n-3≠0))] at h
  exact not_two_of_test hp big on pn h

/-- All prime divisors p≥7 of a counterexample, without an index exception,
must divide the Bernoulli numerator to twice their multiplicity in n. -/
theorem square_bernoulli {n p a:ℕ} (hp:p.Prime) (large:7≤p) (on:Odd n)
    (pos:0<a) (dvd:p^a∣n) (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) :
    p^(2*a)∣(bernoulli (n-3)).num.natAbs :=
  OMA.BernoulliScreen284760.square_bernoulli hp large on pos dvd
    (not_two hp (by omega) on ((dvd_pow_self _ pos.ne').trans dvd) bad) bad

/-- Meštrović's quartic divisibility at any odd n forces the entire square
of n to divide the reduced numerator of the single Bernoulli number B_(n−3). -/
theorem whole_square {n:ℕ} (on:Odd n) (bad:n^4∣∑i∈Ico 1 n,i^(n-2)) :
    n^2∣(bernoulli (n-3)).num.natAbs := by
  by_cases z:(bernoulli (n-3)).num.natAbs=0
  · rw [z];exact dvd_zero _
  apply (Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ on.pos.ne') z).mp
  intro p hp
  simp only [Nat.factorization_pow,Finsupp.nsmul_apply,smul_eq_mul]
  by_cases a:n.factorization p=0
  · simp [a]
  have pd:= (hp.dvd_iff_one_le_factorization on.pos.ne').mpr (by omega)
  have nr : ¬p-1∣n-3 := fun h => OMA.PowerSum284760.local_obstruction on hp pd h
    ((pow_dvd_pow n (by decide : 2≤4)).trans bad)
  have large:7≤p := by
    by_contra! small
    have op:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr on).of_dvd_right pd)
    obtain ⟨j,hj⟩:=op
    have :=hp.two_le
    have :=Nat.le_of_dvd on.pos pd
    obtain ⟨t,ht⟩:=on
    have cases:p=3 ∨ p=5 := by omega
    rcases cases with rfl|rfl
    · omega
    · have nt:=not_two hp (by decide) (show Odd n from ⟨t,ht⟩) pd bad
      omega
  apply (hp.pow_dvd_iff_le_factorization z).mp
  exact square_bernoulli hp large on (by omega) ((hp.pow_dvd_iff_le_factorization on.pos.ne').mpr le_rfl) bad

end OMA.DoubleBernoulli284760

namespace OMA.ThirdOrder284760
open Finset Nat
open OMA.BernoulliScreen284760


private theorem inv_mem {p d:ℕ} [Fact p.Prime] (pos:0<d) (good:¬p∣d):
    (d:ℚ)⁻¹∈(Rat.padicValuation p).integer := by
  apply (OMA.BernoulliScreen284760.integral_iff _).mpr
  rwa [Rat.inv_natCast_den_of_pos pos]

end OMA.ThirdOrder284760

namespace OMA.QuarticIff284760
open Nat Finset
open private Bernoulli.not_dvd_den_bernoulli_add_indicator Bernoulli.vonStaudtIndicator from Mathlib.NumberTheory.Bernoulli

private theorem nat_of_local {n s t:ℕ} (nn:0<n)
    (h:∀ p:ℕ, ∀ hp:p.Prime, p∣n → (s:ℚ)/(n:ℚ)^t∈(@Rat.padicValuation p ⟨hp⟩).integer) : n^t∣s := by
  let x:ℚ:=(s:ℚ)/(n:ℚ)^t
  have co:n.Coprime x.den:=Nat.coprime_of_dvd (fun p hp pn=>by
    let _ : Fact p.Prime:=⟨hp⟩
    exact (OMA.BernoulliScreen284760.integral_iff x).mp (h p hp pn))
  have zn:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  have id:(x.num:ℚ)/x.den=(s:ℚ)/(n:ℚ)^t:=Rat.num_div_den _
  have dn:(x.den:ℚ)≠0:=by exact_mod_cast x.den_ne_zero
  field_simp at id
  have eq:x.num*(n:ℤ)^t=(s:ℤ)*x.den:=by rw [mul_comm (s:ℤ)];exact_mod_cast id
  have val:=congrArg Int.natAbs eq
  simp only [Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_pow] at val
  have d:=dvd_mul_left (n^t) x.num.natAbs
  rw [val] at d;exact (co.pow_left _).dvd_of_dvd_mul_right d

private theorem quotient {p d:ℕ} [Fact p.Prime] (x:ℚ) (pos:0<d) (pd:p∣d)
    (dv:d∣x.num.natAbs) : x/(d:ℚ)∈(Rat.padicValuation p).integer := by
  have dn:(d:ℚ)≠0:=by exact_mod_cast pos.ne'
  have cp:¬p∣x.den := (Fact.out : p.Prime).coprime_iff_not_dvd.mp (x.reduced.of_dvd_left (pd.trans dv))
  obtain ⟨z,hz⟩:=Int.natCast_dvd.mpr dv
  have num:(x.num:ℚ)=(d:ℚ)*z:=by exact_mod_cast hz
  have id:x/(d:ℚ)=(z:ℚ)*(x.den:ℚ)⁻¹:=by nth_rw 1 [←Rat.num_div_den x];rw [num];field_simp
  rw [id];exact ((Rat.padicValuation p).integer).mul_mem (intCast_mem _ _) (OMA.ThirdOrder284760.inv_mem x.den_pos cp)

private theorem not_regular_den {p t:ℕ} [Fact p.Prime] (pos:0<t)
    (ev:Even t) (hd:p∣(bernoulli t).num.natAbs): ¬p-1∣t := by
  intro reg
  have hp:=Fact.out (p:=p.Prime)
  have be:bernoulli t∈(Rat.padicValuation p).integer:=(OMA.BernoulliScreen284760.integral_iff _).mpr
    (hp.coprime_iff_not_dvd.mp ((bernoulli t).reduced.of_dvd_left hd))
  obtain ⟨k,hk⟩:=ev
  have tform:t=2*k:=by omega
  have v:=Bernoulli.not_dvd_den_bernoulli_add_indicator (p:=p) (k:=k) (by omega)
  have add:bernoulli t+(p:ℚ)⁻¹∈(Rat.padicValuation p).integer:=by
    apply (OMA.BernoulliScreen284760.integral_iff _).mpr
    simpa [←tform,Bernoulli.vonStaudtIndicator,reg] using v
  have inv:=((Rat.padicValuation p).integer).sub_mem add be
  rw [add_sub_cancel_left] at inv
  have contra:=(OMA.BernoulliScreen284760.integral_iff _).mp inv
  rw [Rat.inv_natCast_den_of_pos hp.pos] at contra
  exact contra (dvd_refl _)

private theorem local_square {p b:ℕ} [Fact p.Prime] (big:5≤p) (ev:Even b) (bp:0<b)
    (unit:¬p∣b+3) (num:p^2∣(bernoulli (b+2)).num.natAbs) :
    p^2∣∑i∈range p,i^(b+2) := by
  have hp:=Fact.out (p:=p.Prime)
  have nz:(p:ℚ)≠0:=by exact_mod_cast hp.ne_zero
  let f (i:ℕ):=bernoulli i*((b+3).choose i:ℚ)*(p:ℚ)^(b+3-i)/(p:ℚ)^2
  have early :(∑i∈range (b+1),f i)∈(Rat.padicValuation p).integer := by
    apply ((Rat.padicValuation p).integer).sum_mem;intro i hi;have lt:=mem_range.mp hi
    have id:f i=(p*bernoulli i)*((b+3).choose i:ℚ)*(p:ℚ)^(b-i) := by
      dsimp [f];rw [show b+3-i=(b-i)+1+2 by omega,pow_add _ _ 2,pow_succ];field_simp
    rw [id];exact ((Rat.padicValuation p).integer).mul_mem (((Rat.padicValuation p).integer).mul_mem
      (OMA.BernoulliScreen284760.p_bernoulli big i) (natCast_mem _ _)) (((Rat.padicValuation p).integer).pow_mem (natCast_mem _ p) _)
  have ob:Odd (b+1):=by obtain ⟨j,hj⟩:=ev;exact ⟨j,by omega⟩
  have z1:f (b+1)=0:=by simp [f,bernoulli_eq_zero_of_odd ob (by omega)]
  have top:f (b+2)∈(Rat.padicValuation p).integer := by
    have id:f (b+2)=bernoulli (b+2)/(p^2:ℕ)*(((b+3).choose (b+2):ℚ)*p) := by
      dsimp [f];rw [show b+3-(b+2)=1 by omega,pow_one];push_cast;field_simp
    rw [id];exact ((Rat.padicValuation p).integer).mul_mem (quotient _ (pow_pos hp.pos _) (dvd_pow_self p (by decide)) num)
      (((Rat.padicValuation p).integer).mul_mem (natCast_mem _ _) (natCast_mem _ _))
  have all:(∑i∈range (b+3),f i)∈(Rat.padicValuation p).integer := by
    rw [sum_range_succ,sum_range_succ,z1,add_zero];exact ((Rat.padicValuation p).integer).add_mem early top
  have mem:((∑i∈range p,i^(b+2):ℕ):ℚ)/(p:ℚ)^2∈(Rat.padicValuation p).integer := by
    have id:((∑i∈range p,i^(b+2):ℕ):ℚ)/(p:ℚ)^2 =
        (∑i∈range (b+3),f i)*((b+3:ℕ):ℚ)⁻¹ := by
      push_cast;rw [sum_range_pow,←Finset.sum_div];unfold f;rw [←Finset.sum_div];push_cast;ring
    rw [id];exact ((Rat.padicValuation p).integer).mul_mem all (OMA.ThirdOrder284760.inv_mem (by omega) unit)
  apply nat_of_local hp.pos
  intro q hq dq
  obtain rfl:=(Nat.prime_dvd_prime_iff_eq hq hp).mp dq;exact mem

private theorem quartic_local {p n b:ℕ} [Fact p.Prime] (big:5≤p) (pn:p∣n)
    (nf:n=b+5) (bp:0<b) (ev:Even b) (good:¬p-1∣b)
    (num:n^2∣(bernoulli (b+2)).num.natAbs) :
    ((∑i∈range n,i^(b+3):ℕ):ℚ)/(n:ℚ)^4∈(Rat.padicValuation p).integer := by
  have nn:0<n:=by omega
  have nz:(n:ℚ)≠0:=by exact_mod_cast nn.ne'
  let f (i:ℕ):=bernoulli i*((b+4).choose i:ℚ)*(n:ℚ)^(b+4-i)/(n:ℚ)^4
  have early:(∑i∈range b,f i)∈(Rat.padicValuation p).integer := ((Rat.padicValuation p).integer).sum_mem fun i hi=>
    OMA.BernoulliScreen284760.scaled_terms big nn pn i (mem_range.mp hi)
  have term0:f b∈(Rat.padicValuation p).integer := by
    have id:f b=bernoulli b*((b+4).choose b:ℚ):=by dsimp [f];rw [show b+4-b=4 by omega];field_simp
    rw [id];exact ((Rat.padicValuation p).integer).mul_mem (OMA.BernoulliScreen284760.bernoulli_integral bp ev good) (natCast_mem _ _)
  have term2:f (b+2)∈(Rat.padicValuation p).integer := by
    have id:f (b+2)=bernoulli (b+2)/(n^2:ℕ)*((b+4).choose (b+2):ℚ):=by
      dsimp [f];rw [show b+4-(b+2)=2 by omega];push_cast;field_simp
    rw [id];exact ((Rat.padicValuation p).integer).mul_mem
      (quotient _ (pow_pos nn _) (pn.trans (dvd_pow_self _ (by decide))) num) (natCast_mem _ _)
  have ob:Odd (b+1):=by obtain ⟨j,hj⟩:=ev;exact ⟨j,by omega⟩
  have oc:Odd (b+3):=by obtain ⟨j,hj⟩:=ev;exact ⟨j+1,by omega⟩
  have z1:f (b+1)=0:=by simp [f,bernoulli_eq_zero_of_odd ob (by omega)]
  have z3:f (b+3)=0:=by simp [f,bernoulli_eq_zero_of_odd oc (by omega)]
  have all:(∑i∈range (b+4),f i)∈(Rat.padicValuation p).integer := by
    rw [sum_range_succ,sum_range_succ,sum_range_succ,sum_range_succ,z3,z1,add_zero,add_zero]
    exact ((Rat.padicValuation p).integer).add_mem (((Rat.padicValuation p).integer).add_mem early term0) term2
  have unit:¬p∣b+4:=by
    intro d
    exact (Fact.out : p.Prime).not_dvd_one <| (Nat.dvd_add_left d).mp (by rwa [show 1+(b+4)=n by omega])
  have id:((∑i∈range n,i^(b+3):ℕ):ℚ)/(n:ℚ)^4 =
      (∑i∈range (b+4),f i)*((b+4:ℕ):ℚ)⁻¹ := by
    push_cast;rw [sum_range_pow,←Finset.sum_div];unfold f;rw [←Finset.sum_div];push_cast;ring
  rw [id];exact ((Rat.padicValuation p).integer).mul_mem all (OMA.ThirdOrder284760.inv_mem (by omega) unit)

/-- Exact composite-and-prime Bernoulli characterization of the original
quartic power-sum congruence for every positive odd n. -/
theorem original_iff {n:ℕ} (on:Odd n) :
    n^4∣∑i∈Ico 1 n,i^(n-2) ↔ n^2∣(bernoulli (n-3)).num.natAbs := by
  refine ⟨OMA.DoubleBernoulli284760.whole_square on,?_⟩
  intro sq
  by_cases nn:7≤n
  · let b:=n-5
    have nf:n=b+5:=by dsimp [b];omega
    have bp:0<b:=by omega
    have ev:Even b:=by obtain ⟨j,hj⟩:=on;exact ⟨j-2,by omega⟩
    have exp:n-3=b+2:=by omega
    rw [exp] at sq
    rw [show n-2=b+3 by omega]
    have split:=sum_range_add_sum_Ico (fun i:ℕ=>i^(b+3)) on.pos
    have same:(∑i∈Ico 1 n,i^(b+3))=∑i∈range n,i^(b+3):=by simpa using split
    rw [same]
    apply nat_of_local on.pos
    intro p hp pn
    let _ : Fact p.Prime:=⟨hp⟩
    have q2:p^2∣(bernoulli (b+2)).num.natAbs := (pow_dvd_pow_of_dvd pn 2).trans sq
    have nr:=not_regular_den (by omega : 0<b+2) (ev.add (by decide : Even 2))
      ((dvd_pow_self _ (by decide : 2≠0)).trans q2)
    have oddp:=Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr on).of_dvd_right pn)
    have big:5≤p := by
      obtain ⟨j,hj⟩:=oddp
      obtain ⟨t,ht⟩:=ev
      have :=hp.two_le
      by_contra! small
      have h3:p=3:=by omega
      rw [h3] at nr;omega
    have unit:¬p∣b+3:=by
      intro d
      have d2:p∣2:=(Nat.dvd_add_left d).mp (by rwa [show 2+(b+3)=n by omega])
      have :=Nat.le_of_dvd (by decide : 0<2) d2;omega
    have loc:=local_square big ev bp unit q2
    rw [←exp] at loc
    exact quartic_local big pn nf bp ev (OMA.DoubleBernoulli284760.not_two_of_test hp big on pn loc) sq
  · obtain ⟨j,hj⟩:=on
    have cases:n=1∨n=3∨n=5:=by omega
    rcases cases with rfl|rfl|rfl
    · simp
    · norm_num [bernoulli_zero] at sq
    · norm_num [bernoulli_two] at sq

end OMA.QuarticIff284760

namespace OMA.QuarticAll284760
open Nat Finset

/-- For n even and e positive even, already n itself fails to divide the
complete power sum. Halving the number of terms preserves the obstruction. -/
theorem even_obstruction {n e:ℕ} (nn:0<n) (en:Even n) (ep:0<e) (ee:Even e) :
    ¬n∣∑i∈range n,i^e := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨m,hm⟩:=en
    have nf:n=2*m:=by omega
    have mp:0 < m :=by omega
    intro hz
    rw [nf] at hz
    rcases Nat.even_or_odd m with em|om
    · let R:=ZMod (2*m)
      have sq:(m:R)^2=0:=by
        rw [←Nat.cast_pow,ZMod.natCast_eq_zero_iff,pow_two]
        exact Nat.mul_dvd_mul_right em.two_dvd _
      have emul:(m:R)*e=0:=by
        rw [←Nat.cast_mul,ZMod.natCast_eq_zero_iff,mul_comm 2 m]
        exact Nat.mul_dvd_mul_left _ ee.two_dvd
      have term (i:ℕ) : ((m+i:ℕ):R)^e=(i:R)^e := by
        rw [Nat.cast_add,add_comm,OMA.PowerSum284760.taylor _ _ sq e]
        linear_combination (i:R)^(e-1)*emul
      have val:(∑i∈range (2*m),(i:R)^e)=0:=by
        simpa only [Nat.cast_pow,Nat.cast_sum] using (ZMod.natCast_eq_zero_iff _ _).mpr hz
      conv at val => lhs;arg 1;rw [two_mul m]
      rw [sum_range_add,sum_congr rfl (fun i _=>term i),←two_mul] at val
      have div:2*m∣2*(∑i∈range m,i^e):=(ZMod.natCast_eq_zero_iff _ _).mp (by push_cast;exact val)
      exact ih m (by omega) mp em ((Nat.dvd_of_mul_dvd_mul_left (by decide : 0<2)) div)
    · have span:=OMA.PowerSum284760.blocks_cast 2 m e
      have zero:(∑i∈range (2*m),(i:ZMod 2)^e)=0:=by
        simpa only [Nat.cast_sum,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff _ _).mpr
          ((dvd_mul_right 2 m).trans hz)
      rw [zero] at span
      have base:(∑i∈range 2,(i:ZMod 2)^e)=1:=by
        rw [sum_range_succ,sum_range_succ];simp [zero_pow ep.ne']
      rw [base,mul_one] at span
      exact om.not_two_dvd_nat ((ZMod.natCast_eq_zero_iff ..).mp span.symm)

/-- Complete characterization for the original positive integer n. -/
theorem all_iff {n:ℕ} (pos:0<n) :
    n^4∣∑i∈Ico 1 n,i^(n-2) ↔ Odd n ∧ n^2∣(bernoulli (n-3)).num.natAbs := by
  rcases Nat.even_or_odd n with en|on
  · by_cases nt:n=2
    · subst n;decide
    have lo:4≤n:=by obtain ⟨j,hj⟩:=en;omega
    have ev:Even (n-2):=by obtain ⟨j,hj⟩:=en;exact ⟨j-1,by omega⟩
    have fail:=even_obstruction pos en (by omega : 0<n-2) ev
    rw [←OMA.PowerSumRegular284760.ico_range pos (by exact zero_pow (by omega : n-2≠0))] at fail
    constructor
    · intro d;exact False.elim (fail ((dvd_pow_self n (by decide : 4≠0)).trans d))
    · intro h;obtain ⟨u,hu⟩:=h.1;obtain ⟨t,ht⟩:=en;omega
  · simpa [on] using OMA.QuarticIff284760.original_iff on

end OMA.QuarticAll284760

namespace OMA.R_oeis_a284760_R2
open Nat Finset

/-- Kummer transfer of a Bernoulli numerator zero along one nonzero
branch modulo p−1, at the order required by a repeated prime divisor. -/
def H1 : Prop := ∀ {p v e t : ℕ}, p.Prime → 7 ≤ p → 0 < v → 2 < e → 2 < t →
  v < e → v < t → Even e → Even t → ¬ p ∣ e → ¬ p ∣ e+1 → ¬ p ∣ t+1 → ¬ p-1 ∣ t →
  e ≡ t [MOD (p^v).totient] → p^v ∣ (bernoulli e).num.natAbs →
  p^v ∣ (bernoulli t).num.natAbs

/-- Only odd inputs having no proper nontrivial divisor with all local
indices aligned remain. For a squarefree divisor d this asks only whether
n and d agree modulo p−1 at each prime p dividing d. Prime n are included. -/
def H2 : Prop := ∀ n : ℕ, 1 < n → Odd n →
  (∀ d : ℕ, 1 < d → d ∣ n → d < n →
    ¬ ∀ p : ℕ, p.Prime → p ∣ d → n ≡ d [MOD (p^(2*d.factorization p)).totient]) →
  ¬ n^2 ∣ (bernoulli (n-3)).num.natAbs

end OMA.R_oeis_a284760_R2

namespace OMA.R_oeis_a284760_R2
open Nat Finset
private theorem room {p a : ℕ} (large : 7 ≤ p) (positive : 0 < a) :
    2 * a + 4 ≤ p^a := by
  induction a with
  | zero => omega
  | succ a ih =>
    by_cases az : a=0
    · subst a; simpa using (show 6≤p by omega)
    have bound := ih (by omega)
    rw [pow_succ]
    have step := Nat.mul_le_mul bound large
    omega

/-- The order used in the transfer is twice the multiplicity in the smaller
divisor. Therefore even a divisor with repeated factors can sometimes be used. -/
private theorem descend_using (changeIndex : H1)
    {n h : ℕ} (hh : 1<h) (hn : h∣n) (nn : 1<n)
    (compat : ∀ p : ℕ, p.Prime → p∣h → n≡h [MOD (p^(2*h.factorization p)).totient])
    (bad : n^4∣∑i∈Ico 1 n,i^(n-2)) : h^4∣∑i∈Ico 1 h,i^(h-2) := by
  obtain ⟨on,num⟩ := (OMA.QuarticAll284760.all_iff (by omega)).mp bad
  have oh := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr on).of_dvd_right hn)
  have order := Nat.le_of_dvd on.pos hn
  apply (OMA.QuarticAll284760.all_iff (by omega)).mpr
  refine ⟨oh,?_⟩
  by_cases numzero : (bernoulli (h-3)).num.natAbs=0
  · rw [numzero]; exact dvd_zero _
  apply (Nat.factorization_prime_le_iff_dvd (pow_ne_zero _ (by omega)) numzero).mp
  intro p hp
  simp only [Nat.factorization_pow,Finsupp.nsmul_apply,smul_eq_mul]
  by_cases az : h.factorization p=0
  · simp [az]
  have ph := (hp.dvd_iff_one_le_factorization (by omega : h≠0)).mpr (by omega)
  have pn := ph.trans hn
  have nr : ¬p-1∣n-3 := fun r => OMA.PowerSum284760.local_obstruction on hp pn r
    ((pow_dvd_pow n (by decide : 2≤4)).trans bad)
  have large : 7≤p := by
    by_contra! small
    have op := Nat.coprime_two_left.mp ((Nat.coprime_two_left.mpr on).of_dvd_right pn)
    obtain ⟨j,hj⟩ := op
    obtain ⟨k,hk⟩ := on
    have := hp.two_le
    have cases : p=3 ∨ p=5 := by omega
    rcases cases with rfl|rfl
    · omega
    · have other := OMA.DoubleBernoulli284760.not_two hp (by decide) (show Odd n from ⟨k,hk⟩) pn bad
      omega
  have ap : 0<h.factorization p := by omega
  have pd := (hp.pow_dvd_iff_le_factorization (by omega : h≠0)).mpr (le_rfl : h.factorization p≤_)
  have big := (room large ap).trans (Nat.le_of_dvd (by omega : 0<h) pd)
  have ev (x : ℕ) (ox : Odd x) (xl : 3≤x) : Even (x-3) := by
    obtain ⟨j,hj⟩ := ox
    exact ⟨j-1,by omega⟩
  have nondiv (x j : ℕ) (px : p∣x) (pos : 0<j) (lt : j<p) (bound : j≤x) : ¬p∣x-j := by
    intro d
    have z : p∣j := (Nat.dvd_add_left d).mp (by rwa [Nat.add_sub_of_le bound])
    exact (not_le.mpr lt) (Nat.le_of_dvd pos z)
  have eqn := Nat.ModEq.sub_right (by omega : 3≤n) (by omega : 3≤h) (compat p hp ph)
  have smallmod : p-1∣(p^(2*h.factorization p)).totient := by
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : 2*h.factorization p≠0)
    rw [hj,Nat.totient_prime_pow_succ hp]
    exact dvd_mul_left ..
  have nt : ¬p-1∣h-3 := by
    intro d
    apply nr
    exact Nat.modEq_zero_iff_dvd.mp ((eqn.of_dvd smallmod).trans (Nat.modEq_zero_iff_dvd.mpr d))
  have sq : p^(2*h.factorization p)∣(bernoulli (n-3)).num.natAbs := by
    rw [mul_comm 2, pow_mul]
    exact (pow_dvd_pow_of_dvd (pd.trans hn) 2).trans num
  apply (hp.pow_dvd_iff_le_factorization numzero).mp
  apply changeIndex hp large (by omega) (by omega) (by omega) (by omega) (by omega)
    (ev n on (by omega)) (ev h oh (by omega)) (nondiv n 3 pn (by decide) (by omega) (by omega)) _ _ nt eqn sq
  · rw [show n-3+1=n-2 by omega]
    exact nondiv n 2 pn (by decide) (by omega) (by omega)
  · rw [show h-3+1=h-2 by omega]
    exact nondiv h 2 ph (by decide) (by omega) (by omega)


theorem main : H1 → H2 → type_of% @OMA.S_oeis_a284760.main := by
  intro changeIndex core n
  induction n using Nat.strong_induction_on with
  | h n smaller =>
    intro big zero
    have bad := Nat.dvd_of_mod_eq_zero zero
    obtain ⟨odd, square⟩ := (OMA.QuarticAll284760.all_iff (by omega)).mp bad
    apply core n big odd _ square
    intro d largerThanOne divides lt compat
    have inherited := descend_using changeIndex largerThanOne divides big compat bad
    exact smaller d lt largerThanOne (Nat.mod_eq_zero_of_dvd inherited)

end OMA.R_oeis_a284760_R2
