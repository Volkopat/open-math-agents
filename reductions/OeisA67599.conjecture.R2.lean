import FormalConjectures.OEIS.«67599»

/-!
Three distinct prime factors in the decimal factorization fixed-point problem.
The two subgoals are a prime occurrence and the exact three-prime encoding criterion.
The arithmetic of the progression, including its exact period, is proved below.
-/

-- Credit: @SHIN09-git
namespace OMA.R_OeisA67599_conjecture_R2

-- The terms with indices zero and one have proper divisors 17 and 7187.
def H1 : Prop :=
  ∃ t : ℕ, 2 ≤ t ∧ Nat.Prime ((35730 * 10^(12460 + 83338*t) + 1) / 83339)

-- The general criterion, including the necessity that the greatest prime occurs once.
def H2 : Prop :=
  ∀ p q r a b c : ℕ, p.Prime → q.Prime → r.Prime → p < q → q < r →
    0 < a → 0 < b → 0 < c →
    (OeisA67599.a (p^a*q^b*r^c) = p^a*q^b*r^c ↔
      c = 1 ∧ (p^a*q^b-10)*r =
        10 * OeisA67599.concatenateNats
          (OeisA67599.concatenateNats (OeisA67599.concatenateNats p a) q) b *
          10^(Nat.digits 10 r).length + 1)

theorem decimal_power {s v : ℕ} (h : 10^s % 83339 = v % 83339) :
    (10 : ZMod 83339)^s = (v : ZMod 83339) := by
  have he := (ZMod.natCast_eq_natCast_iff' (10^s) v 83339).mpr h
  push_cast at he
  exact he

theorem decimal_order : orderOf (10 : ZMod 83339) = 83338 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide) (decimal_power (v:=1) (by decide +kernel))
  intro p hp hd
  have hh : p ∣ 2*41669 := hd
  rcases hp.dvd_mul.mp hh with h | h
  · have := (Nat.dvd_prime_two_le Nat.prime_two hp.two_le).mp h
    subst p
    rw [decimal_power (s:=83338/2) (v:=83338) (by decide +kernel)]
    decide +kernel
  · have := (Nat.dvd_prime_two_le (show Nat.Prime 41669 by norm_num1) hp.two_le).mp h
    subst p
    rw [decimal_power (s:=83338/41669) (v:=100) (by decide +kernel)]
    decide +kernel

theorem admissible_lengths (d : ℕ) :
    83339 ∣ 35730*10^d+1 ↔ d%83338 = 12460 := by
  have base : (35730 : ZMod 83339)*10^12460+1 = 0 := by
    rw [decimal_power (s:=12460) (v:=23299) (by decide +kernel)]
    decide +kernel
  have fin : IsOfFinOrder (10 : ZMod 83339) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨83338, by decide, decimal_power (v:=1) (by decide +kernel)⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  have poweq : (10 : ZMod 83339)^d = 10^12460 ↔ d%83338 = 12460 := by
    rw [fin.pow_inj_mod,decimal_order]
  rw [←poweq]
  constructor
  · intro h
    have same : (35730 : ZMod 83339)*10^d = 35730*10^12460 := add_right_cancel (h.trans base.symm)
    have inv : (60040 : ZMod 83339)*35730 = 1 := by decide +kernel
    simpa only [←mul_assoc,inv,one_mul] using congrArg ((60040 : ZMod 83339)*·) same
  · intro h
    exact (congrArg (fun x : ZMod 83339 => 35730*x+1) h).trans base

theorem ratio_width {r v : ℕ} (h : 83339*r = 357300*10^v+1) (hv : 1 ≤ v) :
    (Nat.digits 10 r).length = v+1 ∧ 7 < r := by
  have hb : 10 ≤ 10^v := (show 10^1 ≤ 10^v from Nat.pow_le_pow_right (by decide) hv)
  have hl : 10^v ≤ r := by omega
  have hu : r < 10^v*10 := by omega
  have := (Nat.lt_digits_length_iff (by decide : 1<10) r).2 hl
  have := (Nat.digits_length_le_iff (by decide : 1<10) r).2
    (show r < 10^(v+1) by simpa only [pow_succ] using hu)
  omega

theorem candidate_value (t : ℕ) :
    let d := 12460+83338*t
    let r := (35730*10^d+1)/83339
    83339*r = 35730*10^d+1 ∧ (Nat.digits 10 r).length = d ∧ 7 < r := by
  let v := 12459+83338*t
  let r := (35730*10^(12460+83338*t)+1)/83339
  have dv : 12460+83338*t = v+1 := by dsimp [v]; omega
  have hd := (admissible_lengths (12460+83338*t)).mpr (by omega)
  have hm : 83339*r = 35730*10^(12460+83338*t)+1 := Nat.mul_div_cancel' hd
  have h : 83339*r = 357300*10^v+1 := by
    simpa only [dv,pow_succ,show ∀ x : ℕ, 35730*(x*10) = 357300*x by intro x; omega] using hm
  obtain ⟨hw,hgt⟩ := ratio_width h (by dsimp [v]; omega)
  exact ⟨hm,hw.trans dv.symm,hgt⟩

theorem first_two_composite :
    ¬ Nat.Prime ((35730*10^12460+1)/83339) ∧
    ¬ Nat.Prime ((35730*10^95798+1)/83339) := by
  constructor
  · intro hp
    have h := (Nat.dvd_prime_two_le hp (by decide : 2 ≤ 17)).mp (by decide +kernel)
    exact (show 17 ≠ (35730*10^12460+1)/83339 by decide +kernel) h
  · intro hp
    have h := (Nat.dvd_prime_two_le hp (by decide : 2 ≤ 7187)).mp (by decide +kernel)
    exact (show 7187 ≠ (35730*10^95798+1)/83339 by decide +kernel) h

theorem family_iff (hthree : H2) {r : ℕ} (hr : r.Prime) (hlt : 7 < r) :
    OeisA67599.a (83349*r) = 83349*r ↔
      ∃ t : ℕ, r = (35730*10^(12460+83338*t)+1)/83339 := by
  have eqn := hthree 3 7 r 5 3 1 (by decide) (by decide) hr (by decide) hlt
    (by decide) (by decide) (by decide)
  simp only [pow_one] at eqn
  change (OeisA67599.a (83349*r) = 83349*r ↔
    True ∧ 83339*r = 35730*10^(Nat.digits 10 r).length+1) at eqn
  constructor
  · intro h
    have hm := (eqn.mp h).2
    let d := (Nat.digits 10 r).length
    change 83339*r = 35730*10^d+1 at hm
    have hd := (admissible_lengths d).mp ⟨r,hm.symm⟩
    have := Nat.mod_add_div d 83338
    have hv : d = 12460+83338*(d/83338) := by omega
    refine ⟨d/83338,?_⟩
    rw [←hv,←hm,Nat.mul_div_cancel_left _ (by decide)]
  · rintro ⟨t,h⟩
    obtain ⟨hm,hw,_⟩ := candidate_value t
    rw [←h] at hm hw
    exact eqn.mpr ⟨True.intro, by rwa [hw]⟩

theorem main : H1 → H2 → type_of% @OeisA67599.conjecture := by
  rintro ⟨t,_,hr⟩ hthree
  let r := (35730*10^(12460+83338*t)+1)/83339
  have hgt : 7 < r := (candidate_value t).2.2
  refine ⟨83349*r, by omega, (family_iff hthree hr hgt).mpr ⟨t,rfl⟩⟩

end OMA.R_OeisA67599_conjecture_R2
