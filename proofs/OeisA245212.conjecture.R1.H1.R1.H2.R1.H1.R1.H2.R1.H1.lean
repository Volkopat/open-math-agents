import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R1_H2_R1
import Mathlib

/-! The distinct odd prime divisors of (b^t-1) recover the index (t\ge3),
even for odd bases. No existence theorem for primitive prime divisors is needed. -/
namespace OMA.RepunitOrder245212

private def geom (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => geom x k+x^k

private theorem telescope (x k : ℕ) (hx : 1≤x) : geom x k*(x-1)+1=x^k := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
    have h : x-1+1=x := by omega
    simp only [geom,pow_succ]
    nlinarith only [ih, congrArg (fun j : ℕ => x^k*j) h]

private theorem geom_gt {x : ℕ} (hx : 2≤x) (k : ℕ) : k+2<geom x (k+2) := by
  induction k with
  | zero => simpa [geom] using (by omega : 2<1+x)
  | succ k ih =>
    have h:=Nat.one_lt_pow (a:=x) (by omega : k+2≠0) (by omega)
    change k+1+2<geom x (k+2)+x^(k+2)
    omega

private theorem geom_mod_two {x k : ℕ} (hk : Odd k) : ¬2∣geom x k := by
  by_cases ev : 2∣x
  · obtain ⟨a,rfl⟩:=ev
    suffices h : ∀ j, ¬2∣geom (2*a) (j+1) by
      cases k with
      | zero => simp at hk
      | succ k => exact h k
    intro j
    induction j with
    | zero => simp [geom]
    | succ j ih =>
      have d : 2∣(2*a)^(j+1) := (dvd_mul_right 2 a).trans (dvd_pow_self _ (by omega))
      change ¬2∣geom (2*a) (j+1)+(2*a)^(j+1)
      omega
  · have xodd:=Nat.odd_iff.mpr (by omega : x%2=1)
    have h : ∀ j, geom x j%2=j%2 := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        have o:=Nat.odd_iff.mp (xodd.pow (n:=j))
        change (geom x j+x^j)%2=(j+1)%2
        omega
    have := h k
    have := Nat.odd_iff.mp hk
    omega

private theorem odd_step {x q : ℕ} (hx : 2≤x) (hq : 2≤q) (odd : Odd q) :
    ∃ p : ℕ, p.Prime ∧ p≠2 ∧ p∣x^q-1 ∧ ¬p∣x-1 := by
  let G:=geom x q
  have lower : q<G := by
    have e : q=q-2+2 := by omega
    simpa only [G,←e] using geom_gt hx (q-2)
  have xq : G*(x-1)=x^q-1 := by have := telescope x q (by omega); dsimp only [G];omega
  by_contra! none
  suffices G∣q from (Nat.not_le_of_lt lower) (Nat.le_of_dvd (by omega) this)
  apply (Nat.factorization_le_iff_dvd (by omega) (by omega)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases dv : p∣G
    · have po : p≠2 := fun eq=>geom_mod_two odd (eq ▸ dv)
      have pg : p∣x^q-1 := xq ▸ (dv.trans (dvd_mul_right G (x-1)))
      have px:=none p hp po pg
      have nn : ¬p∣x := by
        intro hh
        have h1 : p∣1 := (show x-(x-1)=1 by omega) ▸ Nat.dvd_sub hh px
        have := Nat.le_of_dvd (by decide : 0<1) h1
        have:=hp.two_le;omega
      let _ : Fact p.Prime:=⟨hp⟩
      have h:=padicValNat.pow_sub_pow (hp.odd_of_ne_two po) (x:=x) (y:=1) (by omega) px nn (by omega : q≠0)
      rw [one_pow,←Nat.factorization_def _ hp,←Nat.factorization_def _ hp,←Nat.factorization_def _ hp,
        ←xq,Nat.factorization_mul (by omega) (by omega),Finsupp.add_apply] at h
      omega
    · simp [Nat.factorization_eq_zero_of_not_dvd dv]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem odd_factor {z : ℕ} (hz : 1<z) (zo : ¬2∣z) :
    ∃ p, p.Prime ∧ p≠2 ∧ p∣z := by
  let p:=z.minFac
  have d : p∣z := z.minFac_dvd
  exact ⟨p,Nat.minFac_prime (by omega),fun eq=>zo (eq ▸ d),d⟩

private theorem square_plus {z : ℕ} (hz : 1<z) :
    ∃ p, p.Prime ∧ p≠2 ∧ p∣z^2+1 := by
  rcases Nat.even_or_odd z with ⟨w,hw⟩|⟨w,hw⟩
  · have h : z^2+1=2*(2*w^2)+1 := by rw [hw];ring
    exact odd_factor (by nlinarith) (by rw [h];omega)
  · have wpos : 0<w := by omega
    have fac : z^2+1=2*(2*(w*(w+1))+1) := by rw [hw];ring
    obtain ⟨p,prime,odd,d⟩:=odd_factor (z:=2*(w*(w+1))+1)
      (by have h : 0<w*(w+1) := by positivity
          omega) (by omega)
    exact ⟨p,prime,odd,fac ▸ d.trans (dvd_mul_left _ _)⟩

private theorem power_plus {b u : ℕ} (hb : 2≤b) (hu : 2≤u) :
    ∃ p, p.Prime ∧ p≠2 ∧ p∣b^u+1 := by
  rcases Nat.even_or_odd u with ⟨v,hv⟩|⟨v,hv⟩
  · have vp : 0<v := by omega
    have h : b^u=(b^v)^2 := by rw [←pow_mul];congr 1;omega
    rw [h];exact square_plus (Nat.one_lt_pow vp.ne' (by omega))
  · have vp : 0<v := by omega
    let G := geom (b^2) v
    have tel := telescope (b^2) v (Nat.one_le_pow _ _ (by omega))
    have pb : 1<(b^2)^v := Nat.one_lt_pow vp.ne' (by nlinarith)
    change G*(b^2-1)+1=(b^2)^v at tel
    have Gp : 0<G := by by_contra! nz;rw [show G=0 by omega] at tel;omega
    have bsub : b-1+1=b := by omega
    have bsub2 := Nat.sub_add_cancel (Nat.one_le_pow 2 b (by omega))
    have bz : b^2-1=(b-1)*(b+1) := by nlinarith [congrArg (fun j : ℕ=>j*(b+1)) bsub]
    rw [bz] at tel
    have shift : b^u=(b^2)^v*b := by rw [←pow_mul,←pow_succ,hv]
    let R := 1+b*(b-1)*G
    have fact : b^u+1=R*(b+1) := by rw [shift,←tel];dsimp only [R];ring
    have dv : 2∣b*(b-1) := by
      by_cases ev : 2∣b
      · exact ev.trans (dvd_mul_right _ _)
      · exact (by omega : 2∣b-1).trans (dvd_mul_left _ _)
    have no : ¬2∣R := by have := dv.trans (dvd_mul_right (b*(b-1)) G);dsimp only [R];omega
    have rb : 1<R := by
      dsimp only [R]
      have dpos : 0<b-1:=by omega
      have bpos : 0<b:=by omega
      have prod : 0<b*(b-1)*G:=by positivity
      omega
    obtain ⟨p,prime,odd,d⟩:=odd_factor rb no
    exact ⟨p,prime,odd,fact ▸ d.trans (dvd_mul_right _ _)⟩

noncomputable def ord (b p : ℕ) := orderOf (b : ZMod p)

private theorem order_test {b p m : ℕ} (hb : 0<b) :
    ord b p ∣ m ↔ p∣b^m-1 := by
  rw [ord,orderOf_dvd_iff_pow_eq_one]
  have h:=Nat.modEq_iff_dvd' (show 1≤b^m from Nat.one_le_pow _ _ hb) (n:=p)
  rw [←ZMod.natCast_eq_natCast_iff,Nat.cast_one,Nat.cast_pow] at h
  exact eq_comm.trans h

noncomputable def oddOrders (b t : ℕ) :=
  ((b^t-1).primeFactors.filter (·≠2)).lcm (ord b)

/-- All distinct odd prime divisors together recover the exponent for every
integer base at least two and every exponent at least three. -/
theorem recover {b t : ℕ} (hb : 2≤b) (ht : 3≤t) : oddOrders b t=t := by
  let L:=oddOrders b t
  have based : ∀ {p : ℕ}, p.Prime → p≠2 → p∣b^t-1 → ord b p∣L := by
    intro p hp po d
    apply Finset.dvd_lcm
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,d,
      (Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by omega))).ne'⟩,po⟩
  have Lt : L∣t := by
    apply Finset.lcm_dvd
    exact fun p h=>(order_test (by omega : 0<b)).2
      (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp h).1)
  change L=t
  by_contra different
  obtain ⟨c,tc⟩:=Lt
  have cp : 1<c := by
    by_contra! small
    interval_cases c <;> simp_all
  let q:=c.minFac
  have qp : q.Prime:=Nat.minFac_prime (by omega)
  obtain ⟨j,cj⟩:=c.minFac_dvd
  let u:=L*j
  have expn : t=u*q := by dsimp only [u];rw [tc,cj];ring
  have up : 0<u := by by_contra! z;rw [show u=0 by omega] at expn;omega
  have all : ∀ {p:ℕ}, p.Prime → p≠2 → p∣b^t-1 → p∣b^u-1 := fun hp po d=>
    (order_test (by omega : 0<b)).1 ((based hp po d).trans (dvd_mul_right L j))
  by_cases two : q=2
  · have t2 : t=u*2 := by rwa [two] at expn
    have u2 : 2≤u := by omega
    obtain ⟨p,hp,po,d⟩:=power_plus hb u2
    have z : 1<b^u:=Nat.one_lt_pow up.ne' (by omega)
    have fac : b^t-1=(b^u+1)*(b^u-1) := by
      rw [t2,pow_mul]
      have h : b^u-1+1=b^u := by omega
      have pos : 0<(b^u)^2 := by positivity
      have h2 : (b^u)^2-1+1=(b^u)^2 := by omega
      nlinarith [congrArg (fun j : ℕ=>j*(b^u+1)) h]
    have prev:=all hp po (fac ▸ d.trans (dvd_mul_right _ _))
    have dp : p∣2 := (show b^u+1-(b^u-1)=2 by omega) ▸ Nat.dvd_sub d prev
    exact po ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 dp)
  · obtain ⟨p,hp,po,d,no⟩:=odd_step (x:=b^u) (Nat.one_lt_pow up.ne' (by omega)) qp.two_le
      (qp.odd_of_ne_two two)
    exact no (all hp po (by simpa only [expn,pow_mul] using d))

/-- The reduced denominator of t/(b^t-1). -/
def Q (b t : ℕ) := (b^t-1)/Nat.gcd (b^t-1) t

theorem odd_primes {b t : ℕ} (hb : 2≤b) (ht : 0<t) :
    ((Q b t).primeFactors.filter (·≠2))=((b^t-1).primeFactors.filter (·≠2)) := by
  have mn : 0<b^t-1:=Nat.sub_pos_of_lt (Nat.one_lt_pow ht.ne' (by omega))
  have gd:=Nat.gcd_dvd_left (b^t-1) t
  have qd : Q b t ∣ b^t-1:=Nat.div_dvd_of_dvd gd
  have qpos := Nat.pos_of_dvd_of_pos qd mn
  ext p
  simp only [Finset.mem_filter]
  refine and_congr_left fun odd=>?_ 
  constructor
  · intro mem
    obtain ⟨hp,d,_⟩:=Nat.mem_primeFactors.mp mem
    exact Nat.mem_primeFactors.mpr ⟨hp,d.trans qd,mn.ne'⟩
  · intro mem
    obtain ⟨hp,d,_⟩:=Nat.mem_primeFactors.mp mem
    let _ : Fact p.Prime:=⟨hp⟩
    have pb : ¬p∣b := by
      intro h
      have h' := h.trans (dvd_pow_self b ht.ne')
      have d1 : p∣1 := (show b^t-(b^t-1)=1 by omega) ▸ Nat.dvd_sub h' d
      have:=Nat.le_of_dvd (by decide : 0<1) d1
      have:=hp.two_le;omega
    have dn : ord b p∣p-1 := ZMod.orderOf_dvd_card_sub_one (fun eq=>pb (ZMod.natCast_eq_zero_iff b p|>.mp eq))
    have dp : 0<ord b p := Nat.pos_of_dvd_of_pos dn (by have:=hp.two_le;omega)
    have dn' : ¬p∣ord b p := by
      intro d'
      have := Nat.le_of_dvd (by have:=hp.two_le;omega : 0<p-1) (d'.trans dn)
      have:=hp.two_le
      omega
    obtain ⟨k,eq⟩:=(order_test (by omega : 0<b)).2 d
    have kp : k≠0 := fun h=>by simp [eq,h] at ht
    have test:= (order_test (by omega : 0<b) (p:=p) (m:=ord b p)).1 dvd_rfl
    have posD : 0<b^(ord b p)-1:=Nat.sub_pos_of_lt (Nat.one_lt_pow dp.ne' (by omega))
    have vp:=hp.factorization_pos_of_dvd posD.ne' test
    have h:=padicValNat.pow_sub_pow (hp.odd_of_ne_two odd) (x:=b^ord b p) (y:=1)
      (by omega) test (fun dd=>pb (hp.dvd_of_dvd_pow dd)) kp
    rw [one_pow,←pow_mul,←eq,←Nat.factorization_def _ hp,←Nat.factorization_def _ hp,←Nat.factorization_def _ hp] at h
    have vpT : t.factorization p=k.factorization p := by
      rw [eq,Nat.factorization_mul dp.ne' kp,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd dn',zero_add]
    have posQ : 0<(Q b t).factorization p := by
      rw [Q,Nat.factorization_div gd,Finsupp.tsub_apply,Nat.factorization_gcd mn.ne' ht.ne',Finsupp.inf_apply]
      omega
    exact Nat.mem_primeFactors.mpr ⟨hp,(dvd_pow_self p posQ.ne').trans (Nat.ordProj_dvd _ _),qpos.ne'⟩

theorem reduced_recover {b t : ℕ} (hb : 2≤b) (ht : 3≤t) :
    ((Q b t).primeFactors.filter (·≠2)).lcm (ord b)=t := by
  rw [odd_primes hb (by omega)]
  exact recover hb ht

theorem denominator {b t : ℕ} (hb : 2≤b) (ht : 0<t) :
    ((t:ℚ)+(t:ℚ)/((b:ℚ)^t-1)).den=Q b t := by
  have mn : 0<b^t-1 := Nat.sub_pos_of_lt (Nat.one_lt_pow ht.ne' (by omega))
  have bpos : 0<b:=by omega
  have castD : (((b^t-1:ℕ):ℤ):ℚ)=(b:ℚ)^t-1 := by
    push_cast [Nat.one_le_pow t b bpos]
    rfl
  rw [Rat.natCast_add_den,←castD,←Int.cast_natCast (R:=ℚ) t,←Rat.divInt_eq_div,Rat.den_divInt,
    if_neg (Int.ofNat_ne_zero.mpr mn.ne')]
  rfl

end OMA.RepunitOrder245212

theorem OMA.solution : OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro p t hp ht
  dsimp only
  rw [OMA.RepunitOrder245212.denominator hp.two_le (by omega)]
  exact OMA.RepunitOrder245212.reduced_recover hp.two_le ht
