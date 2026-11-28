import OMAReductions.R_BealConjecture_beal_conjecture_R3
import Mathlib.Tactic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.Multiplicity

/-! A positive gap index gives a finite exponent window in the unramified diagonal equation. In degree seven the residual subproblem also carries three distinct prime witnesses. -/

-- Credit: @Deldor14
-- uses note #142486
namespace OMA.R_BealConjecture_beal_conjecture_R3_H3_R1

/-- Outside degree seven, enumerate the cyclotomic root by its positive gap index. -/
def H1 : Prop :=
  ∀ a b k r s j : ℕ, 0<a → 0<b → a.Coprime b → k.Prime → Odd k → k≠7 →
    (r=4 ∨ (r.Prime ∧ Odd r)) → ¬k ∣ a+b → a+b=s^r → 0<j →
    let t := s^(k-1)-k*j
    1<t → (∀ l : ℕ, l.Prime → l ∣ t → 2*k ∣ l-1) →
    r*(k*j) ≤ (2^(k-1)-1)*t →
    (k≤r → (k*j)*s^(r-k+1) < min a b) →
    (a^k+b^k)/(a+b) ≠ t^r

/-- In degree seven the gap index is accompanied by three distinct prime witnesses
for prime output exponents at least eleven. -/
def H2 : Prop :=
  ∀ a b r s j : ℕ, 0<a → 0<b → a.Coprime b →
    (r=4 ∨ (r.Prime ∧ Odd r)) → ¬7 ∣ a+b → a+b=s^r → 0<j →
    let t := s^6-7*j
    1<t → (∀ l : ℕ, l.Prime → l ∣ t → 14 ∣ l-1) →
    r*(7*j) ≤ 63*t →
    (7≤r → (7*j)*s^(r-7+1) < min a b) →
    (11≤r → ∃ l m q : ℕ, l.Prime ∧ m.Prime ∧ q.Prime ∧ l ∣ a ∧ m ∣ b ∧
      q ∣ a^2+a*b+b^2 ∧ l≠m ∧ l≠q ∧ m≠q ∧ r∣l-1 ∧ r∣m-1 ∧ 6*r∣q-1) →
    (a^7+b^7)/(a+b) ≠ t^r


theorem seventh_identity (a b : ℕ) :
    (a+b)^7 = a^7+b^7+(a+b)*(7*a*b*(a^2+a*b+b^2)^2) := by ring

theorem split_identity {a b u v p : ℕ} (hs : a+b=u^p) (hspos : 0<a+b)
    (he : a^7+b^7=(a+b)*v^p) :
    (u^6)^p = v^p+7*a*b*(a^2+a*b+b^2)^2 := by
  apply Nat.eq_of_mul_eq_mul_left hspos
  calc
    (a+b)*(u^6)^p = (a+b)^7 := by
      rw [hs, ← pow_mul, Nat.mul_comm 6 p, pow_mul]; ring
    _ = (a+b)*(v^p+7*a*b*(a^2+a*b+b^2)^2) := by
      rw [seventh_identity, he]; ring

theorem gap {a b u v t : ℕ} (hb : 0<b)
    (hs : a+b=u^(7+t)) (he : a^7+b^7=(u*v)^(7+t)) :
    (u^6-v)*u^(t+1) < b := by
  have hp : 7+t ≠ 0 := by omega
  have hpow : a^(7+t) < (v*u^(t+1))^(7+t) := by
    calc
      a^(7+t) = a^7*a^t := pow_add _ _ _
      _ ≤ a^7*(a+b)^t := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) t)
      _ < (a^7+b^7)*(a+b)^t := by
        apply Nat.mul_lt_mul_of_pos_right (Nat.lt_add_of_pos_right (pow_pos hb 7))
        exact pow_pos (by omega) t
      _ = (v*u^(t+1))^(7+t) := by
        rw [he,hs,mul_pow,mul_pow,pow_succ u t,mul_pow,← pow_mul,← pow_mul]
        rw [Nat.mul_comm (7+t) t]; ring
  have hn := (Nat.pow_lt_pow_iff_left hp).mp hpow
  have hprod : u^6*u^(t+1) = a+b := by
    rw [←pow_add,hs]; congr 1; omega
  rw [Nat.sub_mul,hprod]
  omega

theorem equal_or_split {q p : ℕ} [Fact q.Prime] (hp : p.Prime)
    {x y : ZMod q} (hy : y ≠ 0) (he : x^p=y^p) : x=y ∨ p ∣ q-1 := by
  have hx : x ≠ 0 := by
    intro h; rw [h,zero_pow hp.ne_zero] at he; exact pow_ne_zero _ hy he.symm
  have h1 : (x/y)^p=1 := by rw [div_pow,he,div_self (pow_ne_zero _ hy)]
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one h1) with h|h
  · left
    have hh := pow_orderOf_eq_one (x/y)
    rw [h,pow_one] at hh
    exact (div_eq_one_iff_eq hy).mp hh
  · right
    simpa [h] using ZMod.orderOf_dvd_card_sub_one (div_ne_zero hx hy)

theorem odd_local_valuation {q p X Y : ℕ} [Fact q.Prime]
    (hq : Odd q) (hYX : Y<X) (hdiv : q ∣ X-Y) (hunit : ¬ q ∣ X) (hp : p ≠ 0) :
    padicValNat q (X^p - Y^p) = padicValNat q (X-Y) + padicValNat q p :=
  padicValNat.pow_sub_pow hq hYX hdiv hunit hp


/-- Every divisor supported on primes not 1 mod p fits into p*(X-Y). -/
theorem nonsplit_dvd {p X Y A : ℕ} (hp : p.Prime) (hod : Odd p)
    (hYX : Y<X) (hc : X.Coprime Y) (hA : A ∣ X^p-Y^p)
    (hs : ∀ q : ℕ, q.Prime → q ∣ A → ¬p ∣ q-1) : A ∣ p*(X-Y) := by
  have hlt := Nat.pow_lt_pow_left hYX hp.ne_zero
  have hd := Nat.sub_ne_zero_of_lt hYX
  have hM := Nat.sub_ne_zero_of_lt hlt
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro q e hq ha
  by_cases e0 : e=0
  · simp [e0]
  have hqa : q ∣ A := dvd_trans (dvd_pow_self q e0) ha
  have : Fact q.Prime := ⟨hq⟩
  have hm := (Nat.modEq_iff_dvd' hlt.le).mpr (dvd_trans hqa hA)
  have he : (X:ZMod q)^p=(Y:ZMod q)^p := by
    simpa using ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hm).symm
  have hy : (Y:ZMod q)≠0 := by
    intro hz
    rw [hz,zero_pow hp.ne_zero] at he
    have hzero : (X:ZMod q)=0 := by
      by_contra hn; exact (pow_ne_zero p hn) he
    have hx := (ZMod.natCast_eq_zero_iff X q).mp hzero
    have hgy := Nat.dvd_gcd hx ((ZMod.natCast_eq_zero_iff Y q).mp hz)
    rw [hc.gcd_eq_one] at hgy
    exact hq.ne_one (Nat.eq_one_of_dvd_one hgy)
  have hcast := (equal_or_split hp hy he).resolve_right (hs q hq hqa)
  have hdiv := (Nat.modEq_iff_dvd' hYX.le).mp ((ZMod.natCast_eq_natCast_iff _ _ _).mp hcast.symm)
  have hunit : ¬q ∣ X := fun h => hy (hcast ▸ (ZMod.natCast_eq_zero_iff X q).mpr h)
  have hval := (padicValNat_dvd_iff_le (p:=q) hM).mp (dvd_trans ha hA)
  apply (padicValNat_dvd_iff_le (p:=q) (mul_ne_zero hp.ne_zero hd)).mpr
  rw [padicValNat.mul hp.ne_zero hd]
  by_cases heq : q=p
  · subst q
    rw [padicValNat.pow_sub_pow hod hYX hdiv hunit hp.ne_zero] at hval
    omega
  · have hn : ¬q ∣ p := by
      intro h
      exact ((Nat.dvd_prime hp).mp h).elim hq.ne_one heq
    have heZ : emultiplicity (q:ℤ) ((X:ℤ)^p-(Y:ℤ)^p) =
        emultiplicity (q:ℤ) ((X:ℤ)-(Y:ℤ)) := by
      apply emultiplicity_pow_sub_pow_of_prime (Nat.prime_iff_prime_int.mp hq)
      · rw [←Int.natCast_sub hYX.le]; exact_mod_cast hdiv
      · exact_mod_cast hunit
      · exact_mod_cast hn
    have hsame : padicValNat q (X^p-Y^p)=padicValNat q (X-Y) := by
      rw [←ENat.natCast_inj,padicValNat_eq_emultiplicity hM,padicValNat_eq_emultiplicity hd,
          ←Int.natCast_emultiplicity,←Int.natCast_emultiplicity q (X-Y),
          Int.natCast_sub hlt.le,Int.natCast_sub hYX.le]
      push_cast
      exact heZ
    omega

theorem exists_split {p X Y A : ℕ} (hp : p.Prime) (hod : Odd p)
    (hYX : Y<X) (hc : X.Coprime Y) (hA : A ∣ X^p-Y^p)
    (hsize : p*(X-Y)<A) : ∃ q : ℕ, q.Prime ∧ q ∣ A ∧ p ∣ q-1 := by
  by_contra! h
  have hdiv := nonsplit_dvd hp hod hYX hc hA h
  have hpos : 0<p*(X-Y) := Nat.mul_pos hp.pos (Nat.sub_pos_of_lt hYX)
  exact (not_lt_of_ge (Nat.le_of_dvd hpos hdiv)) hsize

theorem split_of_primitive {a b c p : ℕ} (ha : 0<a) (hb : 0<b)
    (hc : a.Coprime b) (h7 : ¬7 ∣ a+b) (hp : p≠0) (he : a^7+b^7=c^p) :
    ∃ u v : ℕ, a+b=u^p ∧ c=u*v ∧ u.Coprime v := by
  obtain ⟨Q,hQ⟩ := (by decide : Odd 7).nat_add_dvd_pow_add_pow (x:=a) (y:=b)
  have hDQ : (a+b)^6=Q+7*a*b*(a^2+a*b+b^2)^2 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0<a+b by omega)
    calc
      (a+b)*(a+b)^6 = (a+b)^7 := by ring
      _ = _ := by rw [seventh_identity,hQ]; ring
  have hcop : (a+b).Coprime Q := by
    by_contra bad
    obtain ⟨q,hq,h1,h2⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
    have : Fact q.Prime := ⟨hq⟩
    have hz := (ZMod.natCast_eq_zero_iff _ q).mpr h1
    push_cast at hz
    have hQz := (ZMod.natCast_eq_zero_iff _ q).mpr h2
    have hb0 : (b:ZMod q)≠0 := by
      intro z
      rw [z,add_zero] at hz
      have d := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff _ q).mp hz)
        ((ZMod.natCast_eq_zero_iff _ q).mp z)
      rw [hc.gcd_eq_one] at d
      exact hq.ne_one (Nat.eq_one_of_dvd_one d)
    have ha0 : (a:ZMod q) = -b := eq_neg_of_add_eq_zero_left hz
    have hf := congrArg (fun t : ℕ => (t:ZMod q)) hDQ
    push_cast at hf
    rw [hz,hQz] at hf
    have hH : (a:ZMod q)^2+a*b+b^2=b^2 := by rw [ha0]; ring
    rw [hH,ha0] at hf
    have hseven : (7:ZMod q)=0 := by
      by_contra h
      have hne : (7:ZMod q)*(-b)*b*(b^2)^2≠0 := by
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero h (neg_ne_zero.mpr hb0)) hb0) (pow_ne_zero _ (pow_ne_zero _ hb0))
      exact hne (by simpa using hf.symm)
    have hd : q ∣ 7 := (ZMod.natCast_eq_zero_iff 7 q).mp hseven
    rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with e|e
    · exact hq.ne_one e
    · exact h7 (e ▸ h1)
  have hprod : (a+b)*Q=c^p := hQ.symm.trans he
  obtain ⟨u,hu⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.gcd_eq_one) hprod
  obtain ⟨v,hv⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop.symm.gcd_eq_one)
    ((Nat.mul_comm Q (a+b)).trans hprod)
  refine ⟨u,v,hu,?_,?_⟩
  · apply (Nat.pow_left_inj hp).mp
    rw [mul_pow,←hu,←hv,hprod]
  · rw [hu,hv] at hcop
    exact (hcop.coprime_dvd_left (dvd_pow_self u hp)).coprime_dvd_right (dvd_pow_self v hp)

private theorem domination (n : ℕ) : 11+n ≤ 2^(5+n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (11+n)+1≤2^((5+n)+1)
    rw [pow_succ]
    omega

/-- The three prime witnesses, directly from the primitive unramified equation. -/
theorem primitive_witnesses {a b c p : ℕ} (ha : 0<a) (hb : 0<b)
    (hc : a.Coprime b) (h7 : ¬7 ∣ a+b) (hp : p.Prime) (hp11 : 11≤p)
    (he : a^7+b^7=c^p) :
    ∀ A ∈ [a,b,a^2+a*b+b^2], ∃ q : ℕ, q.Prime ∧ q ∣ A ∧ p ∣ q-1 := by
  obtain ⟨u,v,hs,huv,hcop⟩ := split_of_primitive ha hb hc h7 hp.ne_zero he
  have hu : 2≤u := by
    by_contra! small
    interval_cases u <;> simp [hp.ne_zero] at hs <;> omega
  rw [huv] at he
  have hv : a^7+b^7=(a+b)*v^p := by rw [he,mul_pow,←hs]
  have hI := split_identity hs (by omega) hv
  let H := a^2+a*b+b^2
  change (u^6)^p=v^p+7*a*b*H^2 at hI
  have hHa : a ≤ H := by
    dsimp [H]; nlinarith [Nat.mul_le_mul_left a (show 1≤b by omega)]
  have hH : 0<H := by omega
  have hP : 0<7*a*b*H^2 := by positivity
  have hYX : v<u^6 := (Nat.pow_lt_pow_iff_left hp.ne_zero).mp (by omega)
  let d := u^6-v
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hp11
  have ham : d*u^(5+n)<a := by
    simpa [d, Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (gap (t:=4+n) (a:=b) ha (by rw [add_comm]; convert hs using 1; ring) (by rw [add_comm]; convert he using 1; ring))
  have hbm : d*u^(5+n)<b := by
    simpa [d,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (gap (t:=4+n) hb (by convert hs using 1; ring) (by convert he using 1; ring))
  have hpd := (domination n).trans (Nat.pow_le_pow_left hu (5+n))
  have hdd : (11+n)*d ≤ d*u^(5+n) := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hpd
  have ht : (u^6)^(11+n)-v^(11+n) = 7*a*b*H^2 := by omega
  have pa : a ∣ 7*a*b*H^2 := by exact ⟨7*b*H^2,by ring⟩
  have pb : b ∣ 7*a*b*H^2 := by exact ⟨7*a*H^2,by ring⟩
  have ph : H ∣ 7*a*b*H^2 := by exact ⟨7*a*b*H,by ring⟩
  intro A hA
  change A ∈ [a,b,H] at hA
  apply exists_split hp (hp.odd_of_ne_two (by omega)) hYX (hcop.pow_left 6)
  · rw [ht]; simp at hA
    rcases hA with rfl|rfl|rfl <;> assumption
  · change (11+n)*d<A
    simp at hA
    rcases hA with rfl|rfl|rfl <;> omega

private theorem coprime_H {a b : ℕ} (hc : a.Coprime b) :
    a.Coprime (a^2+a*b+b^2) := by
  by_contra h
  obtain ⟨q,hq,ha,hH⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have : Fact q.Prime := ⟨hq⟩
  have hz := (ZMod.natCast_eq_zero_iff _ q).mpr ha
  have hf := (ZMod.natCast_eq_zero_iff _ q).mpr hH
  push_cast at hf
  rw [hz] at hf
  have hb : (b:ZMod q)=0 := by
    by_contra hn
    have : (b:ZMod q)^2=0 := by simpa using hf
    exact pow_ne_zero 2 hn this
  have hd := Nat.dvd_gcd ha ((ZMod.natCast_eq_zero_iff _ q).mp hb)
  rw [hc.gcd_eq_one] at hd
  exact hq.ne_one (Nat.eq_one_of_dvd_one hd)

theorem three_distinct {a b c p : ℕ} (ha : 0<a) (hb : 0<b)
    (hc : a.Coprime b) (h7 : ¬7 ∣ a+b) (hp : p.Prime) (hp11 : 11≤p)
    (he : a^7+b^7=c^p) :
    ∃ r s q : ℕ, r.Prime ∧ s.Prime ∧ q.Prime ∧ r ∣ a ∧ s ∣ b ∧
      q ∣ a^2+a*b+b^2 ∧ r≠s ∧ r≠q ∧ s≠q ∧ p∣r-1 ∧ p∣s-1 ∧ 6*p∣q-1 := by
  let H := a^2+a*b+b^2
  have hw := primitive_witnesses ha hb hc h7 hp hp11 he
  obtain ⟨r,hr,hrA,hrp⟩ := hw a (by simp)
  obtain ⟨s,hs,hsB,hsp⟩ := hw b (by simp)
  obtain ⟨q,hq,hqH,hqp⟩ := hw H (by simp [H])
  have hAH : a.Coprime H := coprime_H hc
  have hBH : b.Coprime H := by
    have h := coprime_H hc.symm
    convert h using 1; dsimp [H]; ring
  have avoid {B C l : ℕ} (h : B.Coprime C) (hl : l.Prime) (hB : l ∣ B) : ¬l ∣ C := by
    intro hC
    have g := Nat.dvd_gcd hB hC
    rw [h.gcd_eq_one] at g
    exact hl.ne_one (Nat.eq_one_of_dvd_one g)
  refine ⟨r,s,q,hr,hs,hq,hrA,hsB,hqH,?_,?_,?_,hrp,hsp,?_⟩
  · intro e; exact avoid hc hr hrA (e ▸ hsB)
  · intro e; exact avoid hAH hr hrA (e ▸ hqH)
  · intro e; exact avoid hBH hs hsB (e ▸ hqH)
  · have : Fact q.Prime := ⟨hq⟩
    have qb := Nat.le_of_dvd (show 0<q-1 by have := hq.two_le; omega) hqp
    have hmod := (ZMod.natCast_eq_zero_iff _ q).mpr hqH
    dsimp [H] at hmod
    push_cast at hmod
    have hbq : (b:ZMod q)≠0 := by
      intro hz
      exact avoid hBH hq ((ZMod.natCast_eq_zero_iff _ q).mp hz) hqH
    have cubic : (a:ZMod q)^3=(b:ZMod q)^3 := by linear_combination ((a:ZMod q)-b)*hmod
    have hne : (a:ZMod q)≠(b:ZMod q) := by
      intro e
      rw [e] at hmod
      have h3b : (3:ZMod q)*((b:ZMod q)^2)=0 := by linear_combination hmod
      have hd := (ZMod.natCast_eq_zero_iff 3 q).mp ((mul_eq_zero.mp h3b).resolve_right (pow_ne_zero 2 hbq))
      have := Nat.le_of_dvd (by decide : 0<3) hd
      omega
    have h3 := (equal_or_split (by decide : Nat.Prime 3) hbq cubic).resolve_left hne
    have h2 : 2 ∣ q-1 := by obtain ⟨k,hk⟩ := hq.odd_of_ne_two (by omega); exact ⟨k,by omega⟩
    have h6 : 6 ∣ q-1 := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
    have hp6 : p.Coprime 6 := hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by decide : 0<6) h; omega)
    exact hp6.symm.mul_dvd_of_dvd_of_dvd h6 hqp


theorem general_gap {a b u v k t : ℕ} (hb : 0<b) (hk : 0<k)
    (hs : a+b=u^(k+t)) (he : a^k+b^k=(u*v)^(k+t)) :
    (u^(k-1)-v)*u^(t+1)<b := by
  have hp : k+t ≠ 0 := by omega
  have hpow : a^(k+t)<(v*u^(t+1))^(k+t) := by
    calc
      a^(k+t) = a^k*a^t := pow_add _ _ _
      _ ≤ a^k*(a+b)^t := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) t)
      _ < (a^k+b^k)*(a+b)^t := by
        apply Nat.mul_lt_mul_of_pos_right (Nat.lt_add_of_pos_right (pow_pos hb k))
        exact pow_pos (by omega) t
      _ = (v*u^(t+1))^(k+t) := by
        rw [he,hs,mul_pow,mul_pow,pow_succ u t,mul_pow,←pow_mul,←pow_mul]
        rw [Nat.mul_comm (k+t) t]; ring
  have hn := (Nat.pow_lt_pow_iff_left hp).mp hpow
  have hprod : u^(k-1)*u^(t+1)=a+b := by
    rw [←pow_add,hs]; congr 1; omega
  rw [Nat.sub_mul,hprod]
  omega

theorem support_residue {k : ℕ} : ∀ t : ℕ, t ≠ 0 →
    (∀ q : ℕ, q.Prime → q ∣ t → 2*k ∣ q-1) → (t : ZMod k) = 1 := by
  apply Nat.recOnMul
  · simp
  · simp
  · intro q hq _ hs
    have h := dvd_trans (show k ∣ 2*k by simp) (hs q hq (dvd_refl q))
    have z := (ZMod.natCast_eq_zero_iff (q-1) k).mpr h
    rw [Nat.cast_sub (by have := hq.two_le; omega)] at z
    simpa using sub_eq_zero.mp z
  · intro a b ha hb hn hs
    have hn' := mul_ne_zero_iff.mp hn
    rw [Nat.cast_mul, ha hn'.1 (fun q h d => hs q h (dvd_mul_of_dvd_left d _)),
       hb hn'.2 (fun q h d => hs q h (dvd_mul_of_dvd_right d _)),one_mul]

theorem strict_sum {a b n : ℕ} (ha : 0<a) (hb : 0<b) (hn : 1<n) :
    a^n+b^n<(a+b)^n := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (show 2≤n by omega)
  have h := pow_add_pow_le (x:=a) (y:=b) (by omega) (by omega) (n:=1+j) (by omega)
  have h' := Nat.mul_le_mul_right (a+b) h
  have hpos : 0<a^(1+j)*b := Nat.mul_pos (pow_pos ha _) hb
  have ha' : 2+j=(1+j)+1 := by omega
  rw [ha',pow_succ,pow_succ,pow_succ]
  apply lt_of_lt_of_le _ h'
  nlinarith only [hpos, Nat.zero_le (b^(1+j)*a)]

theorem height_window {a b k r s t : ℕ} (ha : 0<a) (hb : 0<b)
    (hk : k.Prime) (ho : Odd k) (hr : 0<r) (hu : ¬k ∣ a+b)
    (hs : a+b=s^r) (ht : 1<t)
    (hsupp : ∀ q : ℕ, q.Prime → q ∣ t → 2*k ∣ q-1)
    (he : (a^k+b^k)/(a+b)=t^r) :
    k ≤ s^(k-1)-t ∧ k ∣ s^(k-1)-t ∧ r*(s^(k-1)-t) ≤ (2^(k-1)-1)*t ∧
    (k≤r → (s^(k-1)-t)*s^(r-k+1) < min a b) := by
  let X := s^(k-1)
  have hD : 0<a+b := by omega
  have hk1 := hk.two_le
  have hquot : a^k+b^k=(a+b)*t^r := by
    rw [←he,mul_comm,Nat.div_mul_cancel (ho.nat_add_dvd_pow_add_pow (x:=a) (y:=b))]
  have hsX : (a+b)*X^r=(a+b)^k := by
    dsimp [X]
    rw [←pow_mul,Nat.mul_comm (k-1) r,pow_mul,←hs,←pow_succ']
    congr 1; omega
  have hYX : t<X := by
    apply (Nat.pow_lt_pow_iff_left (by omega : r≠0)).mp
    apply Nat.lt_of_mul_lt_mul_left (a:=a+b)
    rw [hsX,←hquot]
    exact strict_sum ha hb (by omega)
  have hspos : ¬k ∣ s := by
    intro d; exact hu (hs ▸ dvd_trans d (dvd_pow_self s (by omega)))
  have : Fact k.Prime := ⟨hk⟩
  have hsK : (s:ZMod k)≠0 := fun h => hspos ((ZMod.natCast_eq_zero_iff s k).mp h)
  have hX : (X:ZMod k)=1 := by simpa [X] using ZMod.pow_card_sub_one_eq_one hsK
  have htK := support_residue t (by omega) hsupp
  have hdiv : k ∣ X-t := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub hYX.le,hX,htK,sub_self]
  have hd : k≤X-t := Nat.le_of_dvd (by omega) hdiv
  have hpow : X^r≤2^(k-1)*t^r := by
    apply Nat.le_of_mul_le_mul_left _ hD
    calc
      (a+b)*X^r = (a+b)^k := hsX
      _ ≤ 2^(k-1)*(a^k+b^k) := add_pow_le (Nat.zero_le a) (Nat.zero_le b) k
      _ = (a+b)*(2^(k-1)*t^r) := by rw [hquot]; ring
  obtain ⟨e,heq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  have hber := pow_add_mul_le_add_pow (a:=t) (b:=X-t) (Nat.zero_le _) (Nat.zero_le _) r
  rw [Nat.add_sub_of_le hYX.le] at hber
  have hbnd : r*(X-t)≤(2^(k-1)-1)*t := by
    rw [heq,pow_succ t] at hpow hber
    simp only [Nat.cast_id,Nat.succ_sub_one] at hber
    have hcomp : (t+(e+1)*(X-t))*t^e≤(2^(k-1)*t)*t^e := by
      calc
        _ = t^e*t+(e+1)*t^e*(X-t) := by ring
        _ ≤ X^(e+1) := hber
        _ ≤ 2^(k-1)*(t^e*t) := hpow
        _ = _ := by ring
    have hcancel := Nat.le_of_mul_le_mul_right hcomp (pow_pos (by omega : 0<t) e)
    rw [Nat.sub_mul,one_mul]
    rw [heq]
    change (e+1)*(X-t) ≤ _
    omega
  refine ⟨hd,hdiv,hbnd,?_⟩
  intro hkr
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hkr
  have full : a^k+b^k=(s*t)^(k+j) := by rw [hquot,mul_pow,←hs]
  have g1 := general_gap hb hk.pos hs full
  have g2 := general_gap (a:=b) (b:=a) ha hk.pos (by rwa [add_comm]) (by rwa [add_comm])
  exact lt_min (by simpa using g2) (by simpa using g1)

theorem main : H1 → H2 → OMA.R_BealConjecture_beal_conjecture_R3.H3 := by
  intro h1 h2 a b k r s t ha hb hc hk ho hr hu hs ht hsupp he
  have hrp : 0<r := hr.elim (fun e => by omega) (fun v => v.1.pos)
  obtain ⟨hkbound,hdiv,hrbound,hsmall⟩ :=
    height_window ha hb hk ho hrp hu hs ht hsupp he
  obtain ⟨j,hj⟩ := hdiv
  have hjpos : 0<j := by
    have hkmin := hk.two_le
    by_contra! h
    have jzero : j=0 := by omega
    rw [jzero,mul_zero] at hj
    omega
  have hrecover : s^(k-1)-k*j=t := by
    have hkpos := hk.pos
    omega
  rw [hj] at hrbound hsmall
  by_cases hseven : k=7
  · subst k
    have hw (h : 11≤r) := three_distinct (c:=s*t) ha hb hc hu
      (hr.resolve_left (by omega)).1 h (by
        rw [mul_pow,←hs,←he,mul_comm,Nat.div_mul_cancel (ho.nat_add_dvd_pow_add_pow (x:=a) (y:=b))])
    have h := h2 a b r s j ha hb hc hr hu hs hjpos
    dsimp only at h
    change s^6-7*j=t at hrecover
    rw [hrecover] at h
    exact h ht hsupp hrbound hsmall hw he
  · have h := h1 a b k r s j ha hb hc hk ho hseven hr hu hs hjpos
    dsimp only at h
    rw [hrecover] at h
    exact h ht hsupp hrbound hsmall he

end OMA.R_BealConjecture_beal_conjecture_R3_H3_R1
