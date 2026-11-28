import OMAReductions.R_oeis_a397683_R1
import Mathlib

-- Reduction oeis-a397683.R1.H1.R2 of step oeis-a397683.R1.H1
-- Credit: @PanPapag

-- Continues Ciphore’s reduction. Reuses PanPapag’s reciprocal witnesses, finite
-- certificates, and simultaneous lifts from the A397683 desk notes.
namespace OMA.R_oeis_a397683_R1_H1_R2

namespace QuarterPair

theorem pair {p : ℕ} (hp : p.Prime) (hr : p % 4 = 1) :
    ∃ x : ZMod p, x ≠ 0 ∧ x+1 ≠ 0 ∧ 4 ∣ orderOf x ∧ orderOf x = orderOf (x+1) := by
  letI : Fact p.Prime := ⟨hp⟩
  have ht : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (CharP.cast_eq_zero_iff (ZMod p) p 2).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by have := hp.two_le; omega))
  have hm : (-1 : ZMod p) ≠ 1 := by intro h; apply ht; linear_combination -h
  by_cases hd : 4 ∣ orderOf (2 : ZMod p)
  · let v : ZMod p := 2⁻¹
    have hv : -v+1 = v := by dsimp [v]; field_simp; ring
    refine ⟨-v, neg_ne_zero.mpr (inv_ne_zero ht), by rw [hv]; exact inv_ne_zero ht, ?_⟩
    rw [hv]
    have hvd : 4 ∣ orderOf v := by
      let u := Units.mk0 (2 : ZMod p) ht
      change 4 ∣ orderOf (↑u⁻¹ : ZMod p)
      rw [orderOf_units, orderOf_inv, ← orderOf_units]
      exact hd
    have hdiv : orderOf v ∣ 2 * orderOf (-v) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, show v^2 = (-v)^2 by ring, ← pow_mul, Nat.mul_comm, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have h := hvd.trans hdiv
    have e : Even (orderOf (-v)) := ⟨orderOf (-v)/2, by omega⟩
    have e' : Even (orderOf v) := ⟨orderOf v/2, by omega⟩
    have eq : orderOf (-v) = orderOf v := by
      apply Nat.dvd_antisymm
      · apply orderOf_dvd_of_pow_eq_one
        rw [e'.neg_pow, pow_orderOf_eq_one]
      · apply orderOf_dvd_of_pow_eq_one
        simpa only [e.neg_pow] using pow_orderOf_eq_one (-v)
    exact ⟨by rwa [eq], eq⟩
  obtain ⟨i,hi⟩ := (ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3))
  have hi' : i^2 = -1 := by simpa [pow_two] using hi.symm
  let x := (i-1)/2
  let y := (i+1)/2
  have he : x+1 = y := by dsimp [x,y]; field_simp; ring
  have fourth (z : ZMod p) (hz : z = x ∨ z = y) : z^4*4 = -1 := by
    rcases hz with rfl|rfl
    · dsimp [x]; field_simp; linear_combination (4*i^2-16*i+20)*hi'
    · dsimp [y]; field_simp; linear_combination (4*i^2+16*i+20)*hi'
  let d := orderOf (2 : ZMod p)
  obtain ⟨k,hk,hdk⟩ : ∃ k : ℕ, Odd k ∧ d ∣ 2*k := by
    change ¬4 ∣ d at hd
    by_cases hh : 2 ∣ d
    · exact ⟨d/2, ⟨d/4, by omega⟩, by simpa only [Nat.mul_div_cancel' hh] using (dvd_refl d)⟩
    · exact ⟨d, ⟨d/2, by omega⟩, dvd_mul_left _ _⟩
  have h4 : (4 : ZMod p)^k = 1 := by
    rw [show (4 : ZMod p) = 2^2 by norm_num, ← pow_mul]
    exact orderOf_dvd_iff_pow_eq_one.mp hdk
  have ord (z : ZMod p) (hz : z = x ∨ z = y) : 4 ∣ orderOf z := by
    have hh := congrArg (fun v : ZMod p => v^k) (fourth z hz)
    simp only [mul_pow, h4, mul_one, hk.neg_one_pow] at hh
    rw [← pow_mul, Nat.mul_comm, pow_mul] at hh
    have eight : orderOf (z^k) = 2^(2+1) := by
      apply orderOf_eq_prime_pow (p := 2) (n := 2)
      · change (z^k)^4 ≠ 1; rw [hh]; exact hm
      · change (z^k)^8 = 1
        rw [show 8 = 4*2 by decide, pow_mul, hh]; norm_num
    exact (show 4 ∣ 8 by decide).trans (by rw [← show orderOf (z^k) = 8 from eight]; exact orderOf_pow_dvd k)
  have nx (z : ZMod p) (hz : z = x ∨ z = y) : z ≠ 0 := by
    intro h
    simpa [h] using fourth z hz
  refine ⟨x,nx x (.inl rfl), by rw [he]; exact nx y (.inr rfl), ord x (.inl rfl), ?_⟩
  rw [he]
  have hxy : x^4 = y^4 := by
    apply mul_right_cancel₀ (show (4 : ZMod p) ≠ 0 by convert mul_ne_zero ht ht using 1 <;> norm_num)
    rw [fourth x (.inl rfl), fourth y (.inr rfl)]
  have eq := congrArg orderOf hxy
  rw [orderOf_pow_of_dvd (by decide) (ord x (.inl rfl)), orderOf_pow_of_dvd (by decide) (ord y (.inr rfl))] at eq
  have := ord x (.inl rfl)
  have := ord y (.inr rfl)
  omega
end QuarterPair

namespace SimultaneousDigit

theorem expansion (x p k n : ℕ) : ∃ r : ℕ,
    (x+p*k)^(n+1) = x^(n+1) + p*((n+1)*x^n*k+p*r) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r,hr⟩ := ih
    refine ⟨(n+1)*x^n*k^2+r*(x+p*k), ?_⟩
    rw [pow_succ (x+p*k), hr]
    ring

theorem goodDigit {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (a b s t : ZMod p) (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃ k : ZMod p, a+s*k ≠ 0 ∧ b+t*k ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (CharP.cast_eq_zero_iff (ZMod p) p 2).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hp)
  by_contra! h
  have h0 := h 0
  have h1 := h 1
  have hh := h 2
  simp only [mul_zero,add_zero,mul_one] at h0 h1
  by_cases ha : a = 0
  · subst a
    simp [hs] at h1
    have h' := hh (by simpa using mul_ne_zero hs h2)
    apply ht
    linear_combination h' - h1
  · have hb := h0 ha
    subst b
    have ha1 : a+s=0 := by by_contra hn; exact ht (by simpa using h1 hn)
    have ha2 : a+s*2=0 := by by_contra hn; exact mul_ne_zero ht h2 (by simpa using hh hn)
    apply hs
    linear_combination ha2 - ha1
end SimultaneousDigit

namespace SimultaneousDigit
theorem simultaneous {p x d : ℕ} (hp : p.Prime) (ho : Odd p) (hx : 1 ≤ x)
    (hxp : x+1 < p) (hd : d ≠ 0)
    (h₀ : orderOf (x : ZMod p) = d) (h₁ : orderOf ((x+1 : ℕ) : ZMod p) = d) :
    ∃ y t u : ℕ, 1 ≤ y ∧ y < p^2 ∧ y ≡ x [MOD p] ∧
    y^d = 1+p*t ∧ (y+1)^d = 1+p*u ∧ ¬ (p : ℤ) ∣ (t : ℤ) ∧ ¬ (p : ℤ) ∣ (u : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have nz (z : ℕ) (hz : 0 < z) (hzp : z < p) : (z : ZMod p) ≠ 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p z).not.mpr (Nat.not_dvd_of_pos_of_lt hz hzp)
  have hdiv := orderOf_dvd_iff_pow_eq_one.mpr (ZMod.pow_card_sub_one_eq_one (nz x hx (by omega)))
  rw [h₀] at hdiv
  have hn := Nat.le_of_dvd (by omega : 0 < p-1) hdiv
  have base (z : ℕ) (hz : 0 < z) (hord : orderOf (z : ZMod p) = n+1) :
      ∃ a : ℕ, z^(n+1) = 1+p*a := by
    have hh : (1 : ℕ) ≡ z^(n+1) [MOD p] := by
      apply (ZMod.natCast_eq_natCast_iff ..).mp
      simp [← hord, pow_orderOf_eq_one]
    obtain ⟨a,ha⟩ := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hz)).mp hh
    exact ⟨a, by have := Nat.one_le_pow (n+1) z hz; omega⟩
  obtain ⟨a,ha⟩ := base x hx h₀
  obtain ⟨b,hb⟩ := base (x+1) (by omega) h₁
  have slope (z : ℕ) (hz : 0 < z) (hzp : z < p) :
      (((n+1)*z^n : ℕ) : ZMod p) ≠ 0 := by
    rw [Nat.cast_mul, Nat.cast_pow]
    exact mul_ne_zero (nz _ (by omega) (by omega)) (pow_ne_zero _ (nz z hz hzp))
  obtain ⟨k,hk,hk'⟩ := goodDigit (by omega : 2 < p) (a : ZMod p) b _ _
    (slope x hx (by omega)) (slope (x+1) (by omega) hxp)
  have lift (z c : ℕ) (hc : z^(n+1) = 1+p*c)
      (hnz : (c : ZMod p)+(((n+1)*z^n : ℕ) : ZMod p)*k ≠ 0) :
      ∃ t : ℕ, (z+p*k.val)^(n+1) = 1+p*t ∧ ¬ (p : ℤ) ∣ (t : ℤ) := by
    obtain ⟨r,hr⟩ := expansion z p k.val n
    refine ⟨c+(n+1)*z^n*k.val+p*r, ?_, ?_⟩
    · rw [hr,hc]; ring
    · intro bad
      have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr bad
      apply hnz
      simpa using hh
  obtain ⟨t,ht,hpt⟩ := lift x a ha hk
  obtain ⟨u,hu,hpu⟩ := lift (x+1) b hb hk'
  refine ⟨x+p*k.val,t,u,by omega,?_,?_,ht,?_,hpt,hpu⟩
  · have hv := k.val_lt
    have := Nat.mul_le_mul_left p (show k.val+1 ≤ p by omega)
    nlinarith
  · change (x+p*k.val)%p = x%p
    simp
  · simpa only [show x+p*k.val+1 = x+1+p*k.val by omega] using hu
end SimultaneousDigit

namespace EvenLift
theorem primePowerOrderLift {p x d t : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hd : d ≠ 0) (hbase : orderOf (x : ZMod p) = d)
    (hpow : x ^ d = 1 + p * t) (ht : ¬ (p : ℤ) ∣ (t : ℤ)) (n : ℕ) :
    orderOf (x : ZMod (p ^ (n+1))) = d * p ^ n := by
  let hmap := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)
  have hdiv := orderOf_map_dvd hmap.toMonoidHom (x : ZMod (p^(n+1)))
  have hdiv' : d ∣ orderOf (x : ZMod (p^(n+1))) := by
    simpa [hmap, hbase] using hdiv
  have h := ZMod.orderOf_one_add_mul_prime hp ho (t : ℤ) ht n
  have he : (x : ZMod (p^(n+1)))^d = 1 + (p : ℕ) * (t : ℤ) := by
    exact_mod_cast congrArg (fun z : ℕ => (z : ZMod (p^(n+1)))) hpow
  rw [← he, orderOf_pow_of_dvd hd hdiv'] at h
  rw [← h, Nat.mul_div_cancel' hdiv']


theorem lift {p n : ℕ} (hp : p.Prime) (ho : Odd p) (hn : 1 ≤ n)
    (given : ∃ v : ZMod p, IsUnit v ∧ IsUnit (v+1) ∧
      orderOf v = orderOf (v+1) ∧ 2 ∣ orderOf v) :
    ∃ v : ZMod (p^n), IsUnit v ∧ IsUnit (v+1) ∧
      orderOf v = orderOf (v+1) ∧ 2 ∣ orderOf v := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨v,hv,hw,he,h2⟩ := given
  have hx : 1 ≤ v.val := Nat.pos_of_ne_zero (fun h => hv.ne_zero (v.val_eq_zero.mp h))
  have hxp : v.val+1 < p := by
    have hl := v.val_lt
    by_contra! bad
    have h : v.val+1 = p := by omega
    apply hw.ne_zero
    simpa using congrArg (fun z : ℕ => (z : ZMod p)) h
  obtain ⟨y,t,u,hy,_,hc,ht,hu,hpt,hpu⟩ := SimultaneousDigit.simultaneous hp ho hx hxp
    (isOfFinOrder_iff_isUnit.mpr hv).orderOf_pos.ne' (by simp) (by simpa using he.symm)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hp2 : p ≠ 2 := by obtain ⟨j,hj⟩ := ho; omega
  have hc' := (ZMod.natCast_eq_natCast_iff ..).mpr hc
  have hc1 := (ZMod.natCast_eq_natCast_iff ..).mpr (hc.add_right 1)
  have a := primePowerOrderLift hp hp2 (isOfFinOrder_iff_isUnit.mpr hv).orderOf_pos.ne'
    (by simpa using congrArg orderOf hc') ht hpt k
  have b := primePowerOrderLift hp hp2 (isOfFinOrder_iff_isUnit.mpr hv).orderOf_pos.ne'
    (by simpa using (congrArg orderOf hc1).trans (by simpa using he.symm)) hu hpu k
  have pos : 0 < orderOf v * p^k := Nat.mul_pos (isOfFinOrder_iff_isUnit.mpr hv).orderOf_pos (pow_pos hp.pos _)
  refine ⟨y, isOfFinOrder_iff_isUnit.mp (orderOf_pos_iff.mp (a ▸ pos)), ?_, ?_, a ▸ dvd_mul_of_dvd_left h2 _⟩
  · apply isOfFinOrder_iff_isUnit.mp
    apply orderOf_pos_iff.mp
    simpa only [Nat.cast_add_one] using (b.symm ▸ pos : 0 < orderOf ((y+1 : ℕ) : ZMod (p^(k+1))))
  · simpa using a.trans b.symm
end EvenLift

theorem QuarterPair.primePowers {p a : ℕ} (hp : p.Prime) (hr : p % 4 = 1)
    (ha : 1 ≤ a) : OMA.S_oeis_a397683.f (p^a) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx,hy,hd,he⟩ := QuarterPair.pair hp hr
  obtain ⟨v,hv,hw,he',_⟩ := EvenLift.lift hp (show Odd p from ⟨p/2,by omega⟩) ha
    ⟨x, isUnit_iff_ne_zero.mpr hx, isUnit_iff_ne_zero.mpr hy, he, (by decide : 2 ∣ 4).trans hd⟩
  have hm := one_lt_pow₀ hp.one_lt (by omega : a ≠ 0)
  haveI : NeZero (p^a) := ⟨by omega⟩
  haveI : Fact (1 < p^a) := ⟨hm⟩
  rw [OMA.S_oeis_a397683.f, if_neg hm.ne']
  apply Nat.ne_of_gt
  refine Finset.card_pos.mpr ⟨v.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_,v.val_lt⟩,?_⟩⟩
  · exact Nat.pos_of_ne_zero (fun h => hv.ne_zero (v.val_eq_zero.mp h))
  · rw [← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime]
    simpa using (show IsUnit v ∧ IsUnit (v+1) ∧ orderOf v = orderOf (v+1) from ⟨hv,hw,he'⟩)
namespace SmallPrimePairs
private def witness : ℕ → ℕ × ℕ
  | 5 => (2, 4)
  | 11 => (3, 5)
  | 13 => (6, 12)
  | 17 => (8, 8)
  | 19 => (4, 9)
  | 23 => (2, 11)
  | 29 => (23, 7)
  | 31 => (9, 15)
  | 37 => (33, 9)
  | 41 => (20, 20)
  | 43 => (9, 21)
  | 47 => (2, 23)
  | 53 => (15, 13)
  | 59 => (3, 29)
  | 61 => (15, 15)
  | 67 => (14, 11)
  | 71 => (2, 35)
  | 73 => (13, 72)
  | 79 => (21, 13)
  | 83 => (3, 41)
  | 89 => (9, 44)
  | 97 => (19, 32)
  | 101 => (24, 25)
  | 103 => (8, 17)
  | 107 => (3, 53)
  | 109 => (21, 27)
  | 113 => (56, 28)
  | 127 => (17, 63)
  | 131 => (62, 13)
  | 137 => (59, 17)
  | 139 => (44, 23)
  | 149 => (5, 37)
  | 151 => (123, 25)
  | 157 => (7, 52)
  | 163 => (21, 27)
  | 167 => (2, 83)
  | _ => (0, 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem cert : ∀ i : Fin 170, i.val.Prime → i.val ≠ 2 → i.val ≠ 3 → i.val ≠ 7 →
    let (x,d) := witness i.val
    1 ≤ x ∧ x+1 < i.val ∧ 0 < d ∧
    ((x : ZMod i.val)^d = 1 ∧ ∀ j : Fin d, 0 < j.val → (x : ZMod i.val)^j.val ≠ 1) ∧
    (((x+1 : ℕ) : ZMod i.val)^d = 1 ∧ ∀ j : Fin d, 0 < j.val → ((x+1 : ℕ) : ZMod i.val)^j.val ≠ 1) := by
  decide

theorem small {p : ℕ} (hp : p.Prime) (hb : p < 170) (h2 : p ≠ 2) (h3 : p ≠ 3) (h7 : p ≠ 7) :
    ∃ x d : ℕ, 1 ≤ x ∧ x+1 < p ∧ d ≠ 0 ∧ orderOf (x : ZMod p) = d ∧
      orderOf ((x+1 : ℕ) : ZMod p) = d := by
  have h := cert ⟨p,hb⟩ hp h2 h3 h7
  generalize he : witness p = w
  obtain ⟨x,d⟩ := w
  simp only at h
  rw [he] at h
  obtain ⟨hx,hp',hd,⟨ha,ha'⟩,hb',hb''⟩ := h
  exact ⟨x,d,hx,hp',hd.ne', (orderOf_eq_iff hd).mpr ⟨ha,fun m hm => ha' ⟨m,hm⟩⟩,
    (orderOf_eq_iff hd).mpr ⟨hb',fun m hm => hb'' ⟨m,hm⟩⟩⟩
end SmallPrimePairs

open OMA.S_oeis_a397683

theorem inversePairWitness {m : ℕ} (hm : 1 < m) (x : ZMod m) (h : x * (x+1) = 1) :
    f m ≠ 0 := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨hm⟩
  let u : (ZMod m)ˣ := ⟨x,x+1,h,by rwa [mul_comm]⟩
  have hx : x ≠ 0 := by intro hz; simp [hz] at h
  have he : orderOf x = orderOf (x+1) := by
    change orderOf (u : ZMod m) = orderOf ((u⁻¹ : (ZMod m)ˣ) : ZMod m)
    rw [orderOf_units, orderOf_units, orderOf_inv]
  simp only [f, if_neg (by omega : m ≠ 1), ne_eq, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, x.val_lt⟩, ?_⟩⟩
  · exact Nat.pos_of_ne_zero (fun hz => hx (x.val_eq_zero.mp hz))
  · rw [← ZMod.isUnit_iff_coprime, ← ZMod.isUnit_iff_coprime]
    simpa using (show IsUnit x ∧ IsUnit (x+1) ∧ orderOf x = orderOf (x+1) from
      ⟨u.isUnit, u⁻¹.isUnit, he⟩)

theorem reciprocalRootPrime {p : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hr : p % 5 = 1 ∨ p % 5 = 4) : ∃ x : ZMod p, x*(x+1)=1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h5 : IsSquare (p : ZMod 5) := by
    rw [← ZMod.natCast_mod p 5]
    rcases hr with h | h <;> rw [h]
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  obtain ⟨s, hs⟩ := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by decide) ho).mp h5
  have h2 : (2 : ZMod p) ≠ 0 := by
    exact_mod_cast (CharP.cast_eq_zero_iff (ZMod p) p 2).not.mpr (fun h => ho ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h))
  refine ⟨(s-1)/2, ?_⟩
  field_simp
  push_cast at hs
  linear_combination -hs


theorem liftInversePair {p : ℕ} [Fact p.Prime] (x : ℤ)
    (h : (p : ℤ) ∣ x*(x+1)-1) (hn : (2*(x : ZMod p)+1) ≠ 0) (n : ℕ) :
    ∃ y : ℤ, (p : ℤ)^(n+1) ∣ y*(y+1)-1 ∧ (y : ZMod p) = x := by
  induction n with
  | zero => exact ⟨x, by simpa using h, rfl⟩
  | succ n ih =>
    obtain ⟨y, ⟨t, ht⟩, hy⟩ := ih
    let k : ℤ := ((-(t : ZMod p) / (2*(x : ZMod p)+1)).val : ℕ)
    have hk : (k : ZMod p) = -(t : ZMod p) / (2*(x : ZMod p)+1) := by simp [k]
    have hz : (p : ℤ) ∣ t + (2*y+1)*k := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      push_cast
      rw [hy, hk]
      field_simp
      ring
    obtain ⟨v, hv⟩ := hz
    refine ⟨y+(p:ℤ)^(n+1)*k, ⟨v+(p:ℤ)^n*k^2, ?_⟩, ?_⟩
    · calc
        _ = (y*(y+1)-1) + (p:ℤ)^(n+1)*((2*y+1)*k + (p:ℤ)^(n+1)*k^2) := by ring
        _ = (p:ℤ)^(n+1)*(t+(2*y+1)*k+(p:ℤ)^(n+1)*k^2) := by rw [ht]; ring
        _ = _ := by rw [hv]; ring
    · push_cast
      simp [hy]


theorem reciprocalPrimePowers {p : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hr : p % 5 = 1 ∨ p % 5 = 4) (n : ℕ) : f (p^(n+1)) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := reciprocalRootPrime hp ho hr
  have h5 : (5 : ZMod p) ≠ 0 := by
    have hp5 : p ≠ 5 := by rintro rfl; norm_num at hr
    exact_mod_cast (CharP.cast_eq_zero_iff (ZMod p) p 5).not.mpr (fun h => hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h))
  have hn : 2*x+1 ≠ 0 := by
    intro hh
    apply h5
    linear_combination  (2*x+1)*hh - 4*hx
  let z : ℤ := x.val
  have hz : (z : ZMod p) = x := by simp [z]
  have hd : (p : ℤ) ∣ z*(z+1)-1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    rw [hz, hx, sub_self]
  obtain ⟨y, hy, _⟩ := liftInversePair z hd (by rwa [hz]) n
  apply inversePairWitness (one_lt_pow₀ hp.one_lt (by omega)) (y : ZMod (p^(n+1)))
  apply sub_eq_zero.mp
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd (y*(y+1)-1) (p^(n+1))).mpr (by exact_mod_cast hy)
  simpa using hh

def H1 : Prop := ∀ p : ℕ, p.Prime → 170 ≤ p → p % 20 = 3 →
  ∃ x d : ℕ, 1 ≤ x ∧ x+1 < p ∧ d ≠ 0 ∧
    orderOf (x : ZMod p) = d ∧ orderOf ((x+1 : ℕ) : ZMod p) = d

def H2 : Prop := ∀ p : ℕ, p.Prime → 170 ≤ p → p % 20 = 7 →
  ∃ x d : ℕ, 1 ≤ x ∧ x+1 < p ∧ d ≠ 0 ∧
    orderOf (x : ZMod p) = d ∧ orderOf ((x+1 : ℕ) : ZMod p) = d

theorem main : H1 → H2 → OMA.R_oeis_a397683_R1.H1 := by
  intro h₁ h₂ p a hp ho hp3 hp7 ha
  have hodd := ho
  obtain ⟨j,hj⟩ := hodd
  have hn : p ≠ 2 := by omega
  by_cases h4 : p%4 = 1
  · exact QuarterPair.primePowers hp h4 ha
  by_cases h5 : p%5 = 1 ∨ p%5 = 4
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    exact reciprocalPrimePowers hp hn h5 k
  have h50 : p%5 ≠ 0 := by
    intro h
    have e := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  have w : ∃ x d : ℕ, 1 ≤ x ∧ x+1 < p ∧ d ≠ 0 ∧
      orderOf (x : ZMod p) = d ∧ orderOf ((x+1 : ℕ) : ZMod p) = d := by
    by_cases hb : p < 170
    · exact SmallPrimePairs.small hp hb hn hp3 hp7
    have cases : p%20 = 3 ∨ p%20 = 7 := by
      have hmod (k : ℕ) (hk : k ∣ 20) : (p%20)%k = p%k := Nat.mod_mod_of_dvd p hk
      have h₄ := hmod 4 (by decide)
      have h₅ := hmod 5 (by decide)
      have h₂ := hmod 2 (by decide)
      have hb' := Nat.mod_lt p (by decide : 0 < 20)
      generalize p%20 = r at *
      interval_cases r <;> norm_num at * <;> omega
    exact cases.elim (h₁ p hp (by omega)) (h₂ p hp (by omega))
  obtain ⟨x,d,hx,hxp,hd,h₀,h₁'⟩ := w
  obtain ⟨y,t,u,hy,hyp,hyx,ht,hu,hpt,hpu⟩ := SimultaneousDigit.simultaneous hp ho hx hxp hd h₀ h₁'
  have certify (z : ℕ) (hz : 1 ≤ z) (hzp : z < p^a) (hc : z.Coprime p)
      (hc' : (z+1).Coprime p)
      (he : orderOf (z : ZMod (p^a)) = orderOf ((z+1 : ℕ) : ZMod (p^a))) :
      OMA.S_oeis_a397683.f (p^a) ≠ 0 := by
    have hg := one_lt_pow₀ hp.one_lt (by omega : a ≠ 0)
    rw [OMA.S_oeis_a397683.f, if_neg hg.ne']
    exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hz,hzp⟩, hc.pow_right a, hc'.pow_right a, he⟩⟩)
  have cop (z : ℕ) (hz : 0 < z) (hzp : z < p) : z.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (fun h => (Nat.le_of_dvd hz h).not_gt hzp)).symm
  by_cases h : a = 1
  · apply certify x hx (by simpa [h] using (by omega : x < p)) (cop x hx (by omega))
      (cop _ (by omega) hxp)
    rw [h, pow_one]; exact h₀.trans h₁'.symm
  · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    have hcast := (ZMod.natCast_eq_natCast_iff ..).mpr hyx
    have hsucc := (ZMod.natCast_eq_natCast_iff ..).mpr (hyx.add_right 1)
    have hcop (z w : ℕ) (e : z ≡ w [MOD p]) (hw : w.Coprime p) : z.Coprime p := by
      exact e.gcd_eq.trans hw
    apply certify y hy (hyp.trans_le (Nat.pow_le_pow_right hp.pos (by omega)))
      (hcop _ _ hyx (cop _ hx (by omega))) (hcop _ _ (hyx.add_right 1) (cop _ (by omega) hxp))
    exact (EvenLift.primePowerOrderLift hp (by rintro rfl; obtain ⟨k,hk⟩ := ho; omega)
      hd (congrArg orderOf hcast |>.trans h₀) ht hpt n).trans
      (EvenLift.primePowerOrderLift hp (by rintro rfl; obtain ⟨k,hk⟩ := ho; omega)
      hd (congrArg orderOf hsucc |>.trans h₁') hu hpu n).symm

end OMA.R_oeis_a397683_R1_H1_R2
