import OMAStatements.S_oeis_a359842
import Mathlib

/-!
Divide each binomial term by the prime power after removing the common prime
factors from the numerator and denominator of each falling-factorial term.
The odd-prime residues cancel in pairs. At powers of three there are two
further corrections modulo nine, which cancel each other.
-/

namespace OMA.S_oeis_a359842

open Finset
open scoped Nat

private theorem exponent_lt {p k i : ℕ} (hp : p.Prime) (hi : 0 < i) (h : i < p ^ k) :
    i.factorization p < k := by
  exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp ((Nat.ordProj_le p hi.ne').trans_lt h)

private theorem pow_dvd_of_le_exponent {p i s : ℕ} (h : s ≤ i.factorization p) :
    p ^ s ∣ i :=
  (pow_dvd_pow p h).trans (Nat.ordProj_dvd i p)

private theorem exponent_mul_unit {p m s : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    (p ^ s * m).factorization p = s := by
  have hm' : m ≠ 0 := fun hz => hm (hz ▸ dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm', Finsupp.add_apply,
    Nat.factorization_pow_self hp, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

private theorem pow_mul_div_of_le {p s r j : ℕ} (hp : p.Prime) (hsr : s ≤ r) :
    p ^ r * j / p ^ s = p ^ (r - s) * j := by
  apply Nat.div_eq_of_eq_mul_left (pow_pos hp.pos _)
  calc
    p ^ r * j = (p ^ (r - s) * p ^ s) * j := by rw [← pow_add, Nat.sub_add_cancel hsr]
    _ = (p ^ (r - s) * j) * p ^ s := by ac_rfl

/-- Reduce the numerator and denominator of the falling factorial term by the same power of p. -/
def normalizedFactor (p modulus A i : ℕ) : ZMod modulus :=
  1 - ((A / ordProj[p] i : ℕ) : ZMod modulus) * (ordCompl[p] i : ZMod modulus)⁻¹

/-- Binomial coefficient after removing the p-parts of each factor in its product formula. -/
theorem cast_choose_product {p modulus A B : ℕ} (hp : p.Prime)
    (hmod : ∃ precision : ℕ, 0 < precision ∧ modulus = p ^ precision)
    (hBA : B ≤ A) (hdiv : ∀ i ∈ Icc 1 B, ordProj[p] i ∣ A) :
    ((A - 1).choose B : ZMod modulus) = (-1) ^ B *
      ∏ i ∈ Icc 1 B, normalizedFactor p modulus A i := by
  obtain ⟨precision, hs, rfl⟩ := hmod
  let I := Icc 1 B
  let t (i : ℕ) := ordProj[p] i
  let d (i : ℕ) := ordCompl[p] i
  let c (i : ℕ) := A / t i
  have hi (i : ℕ) (hi : i ∈ I) : 0 < i ∧ i ≤ A := by
    obtain ⟨h1, h2⟩ := mem_Icc.mp hi
    exact ⟨h1, h2.trans hBA⟩
  have hfactorial : B.factorial = ∏ i ∈ I, i := by
    rw [Nat.factorial_eq_prod_range_add_one]
    unfold I
    rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
    simp [Nat.add_comm]
  have hdesc : (A - 1).descFactorial B = ∏ i ∈ I, (A - i) := by
    rw [Nat.descFactorial_eq_prod_range]
    unfold I
    rw [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel, Nat.sub_sub, Nat.add_comm 1]
  have hstrip (i : ℕ) (hi' : i ∈ I) : t i * (c i - d i) = A - i := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_div_cancel' (hdiv i hi'), Nat.ordProj_mul_ordCompl_eq_self]
  have hfactored : (∏ i ∈ I, d i) * (A - 1).choose B = ∏ i ∈ I, (c i - d i) := by
    apply Nat.mul_left_cancel (show 0 < ∏ i ∈ I, t i from prod_pos (fun i _ => Nat.ordProj_pos i p))
    rw [← mul_assoc, ← prod_mul_distrib, ← prod_mul_distrib]
    simp_rw [show ∀ i, t i * d i = i from fun i => Nat.ordProj_mul_ordCompl_eq_self i p]
    rw [← hfactorial, ← Nat.descFactorial_eq_factorial_mul_choose, hdesc]
    exact prod_congr rfl (fun i hi' => (hstrip i hi').symm)
  let R := ZMod (p ^ precision)
  have hunit (i : ℕ) (hi' : i ∈ I) : IsUnit (d i : R) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hs).2 (Nat.not_dvd_ordCompl hp (hi i hi').1.ne')
  have hcle (i : ℕ) (hi' : i ∈ I) : d i ≤ c i := Nat.div_le_div_right (hi i hi').2
  have hcast : (∏ i ∈ I, (d i : R)) * ((A - 1).choose B : R) =
      ∏ i ∈ I, ((c i : R) - (d i : R)) := by
    rw [← Nat.cast_prod, ← Nat.cast_mul, hfactored, Nat.cast_prod]
    exact prod_congr rfl (fun i hi' => Nat.cast_sub (hcle i hi'))
  change ((A - 1).choose B : R) = (-1)^B * ∏ i ∈ I, normalizedFactor p (p ^ precision) A i
  have hu : IsUnit (∏ i ∈ I, (d i : R)) := IsUnit.prod_iff.mpr hunit
  have hcard : I.card = B := by simp [I, Nat.card_Icc]
  apply hu.isRegular.left
  calc
    _ = ∏ i ∈ I, ((c i : R) - (d i : R)) := hcast
    _ = ∏ i ∈ I, (-1) * ((d i : R) * normalizedFactor p (p ^ precision) A i) := by
      apply prod_congr rfl
      intro i hi'
      have huv := ZMod.mul_inv_of_unit (d i : R) (hunit i hi')
      change ((c i : R) - (d i : R)) = -1 * ((d i : R) * (1 - (c i : R) * (d i : R)⁻¹))
      have heq : (d i : R) * ((c i : R) * (d i : R)⁻¹) = (c i : R) := by
        rw [mul_left_comm, huv, mul_one]
      rw [mul_sub, mul_one, heq]
      ring
    _ = _ := by simp only [prod_mul_distrib, prod_const, hcard]; ring

/-- Consecutive binomial coefficients with the common p-part removed. -/
theorem scaled_choose_identity {p r j : ℕ} (hp : p.Prime) (hj : 0 < j) (hle : j ≤ p ^ r) :
    let N := p ^ r
    let e := p ^ (r - j.factorization p)
    let d := ordCompl[p] j
    (e + d) * (N * j).choose (N + j) = N * d * (N * j - 1).choose (N + j - 1) := by
  dsimp
  let N := p ^ r
  let t := ordProj[p] j
  let e := p ^ (r - j.factorization p)
  let d := ordCompl[p] j
  change (e + d) * (N * j).choose (N + j) = N * d * (N * j - 1).choose (N + j - 1)
  have hrt : j.factorization p ≤ r := Nat.factorization_le_of_le_pow hle
  have htjd : t * d = j := Nat.ordProj_mul_ordCompl_eq_self j p
  have htN : t * e = N := by dsimp [t, e, N]; rw [← pow_add, Nat.add_sub_of_le hrt]
  have hNj : 0 < N * j := Nat.mul_pos (pow_pos hp.pos _) hj
  have heq := Nat.add_one_mul_choose_eq (N * j - 1) (N + j - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ N * j), Nat.sub_add_cancel (by omega : 1 ≤ N + j)] at heq
  apply Nat.mul_left_cancel (show 0 < t from Nat.ordProj_pos j p)
  calc
    t * ((e + d) * (N * j).choose (N + j)) = (N * j).choose (N + j) * (N + j) := by
      rw [← mul_assoc, mul_add, htN, htjd, mul_comm]
    _ = N * j * (N * j - 1).choose (N + j - 1) := heq.symm
    _ = t * (N * d * (N * j - 1).choose (N + j - 1)) := by rw [← htjd]; ac_rfl

theorem interior_dvd {p r j : ℕ} (hp : p.Prime) (hj : 0 < j) (hlt : j < p ^ r) :
    p ^ r ∣ (p ^ r * j).choose (p ^ r + j) := by
  have hs := exponent_lt hp hj hlt
  have hde : p ∣ p ^ (r - j.factorization p) := dvd_pow_self _ (by omega)
  have hnp : ¬ p ∣ p ^ (r - j.factorization p) + ordCompl[p] j := by
    intro h
    exact Nat.not_dvd_ordCompl hp hj.ne' ((Nat.dvd_add_iff_right hde).2 h)
  have hcop := (hp.coprime_iff_not_dvd.2 hnp).pow_left r
  apply (hcop.dvd_mul_left).mp
  rw [scaled_choose_identity hp hj hlt.le]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

theorem end_choose_identity {p r : ℕ} (hp : p.Prime) :
    2 * (p ^ r * p ^ r).choose (p ^ r + p ^ r) =
      p ^ r * (p ^ r * p ^ r - 1).choose (p ^ r + p ^ r - 1) := by
  have h := scaled_choose_identity (r := r) hp (pow_pos hp.pos r : 0 < p ^ r) le_rfl
  dsimp only at h
  simpa only [Nat.factorization_pow_self hp, Nat.sub_self, Nat.div_self (pow_pos hp.pos r),
    pow_zero, one_mul, mul_one, one_add_one_eq_two] using h

theorem end_dvd_odd {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ^ r ∣ (p ^ r * p ^ r).choose (p ^ r + p ^ r) := by
  have hcop : p.Coprime 2 := hp.coprime_iff_not_dvd.2 (fun h => hp2 ((Nat.dvd_prime Nat.prime_two).1 h |>.resolve_left hp.ne_one))
  apply ((hcop.pow_left r).dvd_mul_left).mp
  rw [end_choose_identity hp]
  exact dvd_mul_right _ _

theorem end_dvd_two {r : ℕ} (hr : 0 < r) :
    2 ^ (r - 1) ∣ (2 ^ r * 2 ^ r).choose (2 ^ r + 2 ^ r) := by
  have heq := end_choose_identity (r := r) Nat.prime_two
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  have heq' : 2 * _ = 2 * (2 ^ (r - 1) * (2 ^ r * 2 ^ r - 1).choose (2 ^ r + 2 ^ r - 1)) :=
    heq.trans (by rw [← mul_assoc, ← hpow])
  exact ⟨_, Nat.mul_left_cancel (by decide : 0 < 2) heq'⟩

/-- The natural-number quotient of a summand by the prime power. -/
def normalizedChoose (p r j : ℕ) : ℕ := (p ^ r * j).choose (p ^ r + j) / p ^ r

private theorem unit_at_modulus {p modulus d : ℕ} (hp : p.Prime)
    (hmod : ∃ precision : ℕ, 0 < precision ∧ modulus = p ^ precision) (hd : ¬ p ∣ d) :
    IsUnit (d : ZMod modulus) := by
  obtain ⟨s, hs, rfl⟩ := hmod
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hs).2 hd

theorem interior_scaled_eq {p modulus r j : ℕ} (hp : p.Prime)
    (hmod : ∃ precision : ℕ, 0 < precision ∧ modulus = p ^ precision)
    (hj : 0 < j) (hlt : j < p ^ r)
    (hsquare : (p ^ (r - j.factorization p) : ZMod modulus) ^ 2 = 0) :
    (normalizedChoose p r j : ZMod modulus) =
      (1 - (p ^ (r - j.factorization p) : ZMod modulus) *
        (ordCompl[p] j : ZMod modulus)⁻¹) * ((p ^ r * j - 1).choose (p ^ r + j - 1) : ZMod modulus) := by
  let N := p ^ r
  let e := p ^ (r - j.factorization p)
  let d := ordCompl[p] j
  let Q := normalizedChoose p r j
  let B := (N * j - 1).choose (N + j - 1)
  have hpos : 0 < N := pow_pos hp.pos _
  have hchoose : N * Q = (N * j).choose (N + j) := Nat.mul_div_cancel' (interior_dvd hp hj hlt)
  have hrel : (e + d) * Q = d * B := by
    apply Nat.mul_left_cancel hpos
    calc
      N * ((e + d) * Q) = (e + d) * (N * Q) := by ac_rfl
      _ = N * d * B := by rw [hchoose, scaled_choose_identity hp hj hlt.le]
      _ = N * (d * B) := mul_assoc _ _ _
  let R := ZMod modulus
  have hcast : ((e : R) + (d : R)) * (Q : R) = (d : R) * (B : R) := by
    let f : ℕ →+* R := Nat.castRingHom R
    have hh : f ((e + d) * Q) = f (d * B) := congrArg f hrel
    rw [map_mul, map_add, map_mul] at hh
    exact hh
  have he : p ∣ e := dvd_pow_self _ (by have := exponent_lt hp hj hlt; dsimp [e]; omega)
  have hd : ¬ p ∣ d := Nat.not_dvd_ordCompl hp hj.ne'
  have hedu := unit_at_modulus hp hmod (d := e + d) (fun h => hd ((Nat.dvd_add_iff_right he).2 h))
  have hdu := ZMod.mul_inv_of_unit (d : R) (unit_at_modulus hp hmod hd)
  have hsquare' : (e : R) ^ 2 = 0 := by simpa only [e, Nat.cast_pow] using hsquare
  rw [← Nat.cast_pow]
  change (Q : R) = (1 - (e : R) * (d : R)⁻¹) * (B : R)
  apply show IsLeftRegular ((e : R) + (d : R)) from by simpa only [Nat.cast_add] using hedu.isRegular.left
  have hprod : ((e : R) + (d : R)) * (1 - (e : R) * (d : R)⁻¹) = (d : R) := by
    calc
      _ = (d : R) + (e : R) * (1 - (d : R) * (d : R)⁻¹) - (e : R) ^ 2 * (d : R)⁻¹ := by ring
      _ = _ := by rw [hdu, hsquare']; ring
  change ((e : R) + (d : R)) * (Q : R) = ((e : R) + (d : R)) * ((1 - (e : R) * (d : R)⁻¹) * (B : R))
  rw [hcast, ← mul_assoc, hprod]

theorem end_scaled_eq {p modulus r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : ∃ precision : ℕ, 0 < precision ∧ modulus = p ^ precision) :
    (normalizedChoose p r (p ^ r) : ZMod modulus) =
      (2 : ZMod modulus)⁻¹ * ((p ^ r * p ^ r - 1).choose (p ^ r + p ^ r - 1) : ZMod modulus) := by
  let N := p ^ r
  let Q := normalizedChoose p r N
  let B := (N * N - 1).choose (N + N - 1)
  have hchoose : N * Q = (N * N).choose (N + N) := Nat.mul_div_cancel' (end_dvd_odd hp hp2)
  have hrel : 2 * Q = B := by
    apply Nat.mul_left_cancel (show 0 < N from pow_pos hp.pos _)
    rw [mul_left_comm, hchoose, end_choose_identity hp]
  let R := ZMod modulus
  have hcast : (2 : R) * (Q : R) = (B : R) := by
    let f : ℕ →+* R := Nat.castRingHom R
    have hh : f (2 * Q) = f B := congrArg f hrel
    rw [map_mul, map_ofNat] at hh
    exact hh
  have hunit := unit_at_modulus hp hmod (d := 2)
    (fun h => hp2 ((Nat.dvd_prime Nat.prime_two).1 h |>.resolve_left hp.ne_one))
  have hunit' : IsUnit (2 : R) := by simpa using hunit
  change (Q : R) = (2 : R)⁻¹ * (B : R)
  apply hunit'.isRegular.left
  change (2 : R) * (Q : R) = 2 * ((2 : R)⁻¹ * (B : R))
  rw [hcast, ← mul_assoc, ZMod.mul_inv_of_unit _ hunit', one_mul]

private theorem choose_span_le {N j : ℕ} (hN : 0 < N) (hj : 0 < j) : N + j - 1 ≤ N * j := by
  have hm := Nat.mul_le_mul_right (j - 1) (show 1 ≤ N from hN)
  rw [one_mul, Nat.mul_sub, mul_one] at hm
  have hm' : N ≤ N * j := by simpa using Nat.mul_le_mul_left N hj
  omega

private theorem nearby_exponent_le {p r i : ℕ} (hp : p.Prime) (hi : 0 < i) (hlt : i < 2 * p ^ r) :
    i.factorization p ≤ r := by
  have h' : i < p ^ (r + 1) := hlt.trans_le (by rw [pow_succ']; exact Nat.mul_le_mul_right _ hp.two_le)
  exact Nat.lt_succ_iff.mp (exponent_lt hp hi h')

private theorem nearby_exponent_lt {p r i : ℕ} (hp : p.Prime) (hi : 0 < i)
    (hlt : i < 2 * p ^ r) (hne : i ≠ p ^ r) : i.factorization p < r := by
  have he := nearby_exponent_le hp hi hlt
  by_contra! hbad
  obtain ⟨t, ht⟩ := pow_dvd_of_le_exponent hbad
  have ht₁ : 0 < t := by by_contra! ht₁; interval_cases t; simp_all
  have ht₂ : t < 2 := by
    by_contra! ht₂
    have hmul := Nat.mul_le_mul_left (p ^ r) ht₂
    rw [mul_comm _ 2, ← ht] at hmul
    omega
  have : t = 1 := by omega
  exact hne (by simpa [this] using ht)

private theorem normalized_factor_pow {p modulus r j i : ℕ} (hp : p.Prime)
    (hi : i.factorization p ≤ r) :
    normalizedFactor p modulus (p ^ r * j) i =
      1 - (p ^ (r - i.factorization p) : ZMod modulus) * (j : ZMod modulus) *
        (ordCompl[p] i : ZMod modulus)⁻¹ := by
  rw [normalizedFactor, pow_mul_div_of_le hp hi, Nat.cast_mul, Nat.cast_pow]

theorem normalized_factor_at_power {p modulus r j : ℕ} (hp : p.Prime) :
    normalizedFactor p modulus (p ^ r * j) (p ^ r) = 1 - (j : ZMod modulus) := by
  rw [normalizedFactor, Nat.factorization_pow_self hp, Nat.div_self (pow_pos hp.pos r),
    Nat.mul_div_cancel_left _ (pow_pos hp.pos r)]
  simp

private theorem cast_choose_prime_modulus {p r j : ℕ} (hp : p.Prime) (hj : 0 < j)
    (hle : j ≤ p ^ r) :
    ((p ^ r * j - 1).choose (p ^ r + j - 1) : ZMod p) =
      (-1) ^ (p ^ r + j - 1) * (1 - (j : ZMod p)) := by
  let N := p ^ r
  have hN : 0 < N := pow_pos hp.pos _
  have hmod : ∃ s : ℕ, 0 < s ∧ p = p ^ s := ⟨1, by decide, (pow_one p).symm⟩
  rw [cast_choose_product hp hmod (choose_span_le hN hj)]
  · rw [prod_eq_single_of_mem N (mem_Icc.mpr (by omega)), normalized_factor_at_power hp]
    intro i hi hne
    have hb : i < 2 * N := by have := (mem_Icc.mp hi).2; omega
    have he := nearby_exponent_lt hp (mem_Icc.mp hi).1 hb hne
    have hz : (p : ZMod p) ^ (r - i.factorization p) = 0 :=
      pow_eq_zero_of_le (show 1 ≤ r - i.factorization p by omega) (by simp)
    rw [normalized_factor_pow hp he.le, hz, zero_mul, zero_mul, sub_zero]
  · intro i hi
    have hb : i < 2 * N := by have := (mem_Icc.mp hi).2; omega
    exact dvd_mul_of_dvd_left (pow_dvd_pow p (nearby_exponent_le hp (mem_Icc.mp hi).1 hb)) _

theorem interior_normalized_prime {p r j : ℕ} (hp : p.Prime) (hodd : Odd (p ^ r))
    (hj : 0 < j) (hlt : j < p ^ r) :
    (normalizedChoose p r j : ZMod p) = (-1) ^ j * (1 - (j : ZMod p)) := by
  have hmod : ∃ s : ℕ, 0 < s ∧ p = p ^ s := ⟨1, by decide, (pow_one p).symm⟩
  have he := exponent_lt hp hj hlt
  have hz : (p : ZMod p) ^ (r - j.factorization p) = 0 :=
    pow_eq_zero_of_le (show 1 ≤ r - j.factorization p by omega) (by simp)
  rw [interior_scaled_eq hp hmod hj hlt (by rw [hz]; simp), hz, zero_mul, sub_zero, one_mul,
    cast_choose_prime_modulus hp hj hlt.le]
  obtain ⟨a, ha⟩ := hodd
  have hindex : p ^ r + j - 1 = 2 * a + j := by omega
  rw [hindex, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

theorem end_normalized_prime {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 0 < r) (hodd : Odd (p ^ r)) :
    (normalizedChoose p r (p ^ r) : ZMod p) = -(2 : ZMod p)⁻¹ := by
  have hmod : ∃ s : ℕ, 0 < s ∧ p = p ^ s := ⟨1, by decide, (pow_one p).symm⟩
  have hzero : ((p ^ r : ℕ) : ZMod p) = 0 := by rw [Nat.cast_pow, ZMod.natCast_self, zero_pow hr.ne']
  rw [end_scaled_eq hp hp2 hmod, cast_choose_prime_modulus hp (pow_pos hp.pos _) le_rfl,
    hzero]
  obtain ⟨a, ha⟩ := hodd
  have hindex : p ^ r + p ^ r - 1 = 2 * (2 * a) + 1 := by omega
  rw [hindex, pow_add, pow_mul, neg_one_sq]
  simp

private theorem three_pow_zero {e : ℕ} (he : 2 ≤ e) : (3 : ZMod 9) ^ e = 0 :=
  pow_eq_zero_of_le he (by decide)

theorem inverse_two_nine : (2 : ZMod 9)⁻¹ = 5 := ZMod.inv_eq_of_mul_eq_one 9 2 5 (by decide)

private theorem inverse_four_nine : (4 : ZMod 9)⁻¹ = 7 := ZMod.inv_eq_of_mul_eq_one 9 4 7 (by decide)

private theorem inverse_five_nine : (5 : ZMod 9)⁻¹ = 2 := ZMod.inv_eq_of_mul_eq_one 9 5 2 (by decide)

private theorem ternary_factor_mul {s d j : ℕ} (hd : ¬ 3 ∣ d) :
    normalizedFactor 3 9 (3 ^ (s + 1) * j) (3 ^ s * d) =
      1 - 3 * (j : ZMod 9) * (d : ZMod 9)⁻¹ := by
  have he := exponent_mul_unit Nat.prime_three (s := s) hd
  rw [normalized_factor_pow Nat.prime_three (by omega : (3 ^ s * d).factorization 3 ≤ s + 1),
    he, Nat.add_sub_cancel_left, pow_one, Nat.mul_div_cancel_left _ (pow_pos (by decide : 0 < 3) s),
    Nat.cast_ofNat]

private theorem odd_middle_pairs (x : ZMod 9) : (1 - 3 * x) * (1 - 6 * x) = 1 := by
  calc
    _ = 1 - (9 : ZMod 9) * x + (18 : ZMod 9) * x ^ 2 := by ring
    _ = _ := by rw [show (9 : ZMod 9) = 0 by decide, show (18 : ZMod 9) = 0 by decide]; ring

private theorem product_divisible_indices {M B : ℕ} (hM : 0 < M) (f : ℕ → ZMod 9)
    (hone : ∀ i ∈ Icc 1 B, ¬ M ∣ i → f i = 1) :
    ∏ i ∈ Icc 1 B, f i = ∏ d ∈ Icc 1 (B / M), f (M * d) := by
  let I := Icc 1 B
  have hindices : I.filter (fun i => M ∣ i) = (Icc 1 (B / M)).image (fun d => M * d) := by
    ext i
    rw [mem_filter, mem_image]
    constructor
    · rintro ⟨hi, d, rfl⟩
      obtain ⟨hpos, hle⟩ := mem_Icc.mp hi
      have hdpos : 0 < d := by by_contra! hd; interval_cases d; simp at hpos
      exact ⟨d, mem_Icc.mpr ⟨hdpos, (Nat.le_div_iff_mul_le hM).2 (by simpa [mul_comm] using hle)⟩, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨hdpos, hdle⟩ := mem_Icc.mp hd
      exact ⟨mem_Icc.mpr ⟨Nat.mul_pos hM hdpos, by simpa [mul_comm] using (Nat.le_div_iff_mul_le hM).1 hdle⟩,
        dvd_mul_right _ _⟩
  calc
    _ = ∏ i ∈ I.filter (fun i => M ∣ i), f i := (prod_subset (filter_subset _ _) (fun i hi hj =>
      hone i hi (fun h => hj (mem_filter.mpr ⟨hi, h⟩)))).symm
    _ = _ := by rw [hindices, prod_image (fun a _ b _ h => Nat.mul_left_cancel hM h)]

private theorem cast_choose_nine {s j : ℕ} (hj : 0 < j) (hle : j ≤ 3 ^ (s + 1)) :
    ((3 ^ (s + 1) * j - 1).choose (3 ^ (s + 1) + j - 1) : ZMod 9) =
      (-1) ^ (3 ^ (s + 1) + j - 1) *
        ((1 - (j : ZMod 9)) * (1 - if 3 ^ s < j ∧ j ≤ 2 * 3 ^ s then 3 * (j : ZMod 9) else 0)) := by
  let N := 3 ^ (s + 1)
  let M := 3 ^ s
  let B := N + j - 1
  have hM : 0 < M := pow_pos (by decide) _
  have hN : 0 < N := pow_pos (by decide) _
  have hNM : N = 3 * M := pow_succ' 3 s
  have hmod : ∃ s : ℕ, 0 < s ∧ 9 = 3 ^ s := ⟨2, by decide, by decide⟩
  change ((N * j - 1).choose B : ZMod 9) = (-1)^B * ((1 - (j : ZMod 9)) *
    (1 - if M < j ∧ j ≤ 2 * M then 3 * (j : ZMod 9) else 0))
  rw [cast_choose_product Nat.prime_three hmod (choose_span_le hN hj)]
  · congr 1
    rw [product_divisible_indices hM]
    · have h3 : 3 ≤ B / M := (Nat.le_div_iff_mul_le hM).2 (by dsimp [B]; omega)
      have h6 : B / M < 6 := (Nat.div_lt_iff_lt_mul hM).2 (by dsimp [B]; omega)
      have h4 : 4 ≤ B / M ↔ M < j := by rw [Nat.le_div_iff_mul_le hM]; dsimp [B]; omega
      have h5 : 5 ≤ B / M ↔ 2 * M < j := by rw [Nat.le_div_iff_mul_le hM]; dsimp [B]; omega
      have f1 : normalizedFactor 3 9 (N * j) M = 1 - 3 * (j : ZMod 9) := by
        simpa only [mul_one, Nat.cast_one, ZMod.inv_one] using
          (ternary_factor_mul (s := s) (j := j) (by decide : ¬3 ∣ 1))
      have f2 : normalizedFactor 3 9 (N * j) (M * 2) = 1 - 6 * (j : ZMod 9) := by
        rw [ternary_factor_mul (by decide : ¬3 ∣ 2), Nat.cast_ofNat, inverse_two_nine,
          mul_right_comm (3 : ZMod 9), show (3 : ZMod 9) * 5 = 6 by decide]
      have f3 : normalizedFactor 3 9 (N * j) (M * 3) = 1 - (j : ZMod 9) := by
        rw [show M * 3 = N by omega, normalized_factor_at_power Nat.prime_three]
      have f4 : normalizedFactor 3 9 (N * j) (M * 4) = 1 - 3 * (j : ZMod 9) := by
        rw [ternary_factor_mul (by decide : ¬3 ∣ 4), Nat.cast_ofNat, inverse_four_nine,
          mul_right_comm (3 : ZMod 9), show (3 : ZMod 9) * 7 = 3 by decide]
      have f5 : normalizedFactor 3 9 (N * j) (M * 5) = 1 - 6 * (j : ZMod 9) := by
        rw [ternary_factor_mul (by decide : ¬3 ∣ 5), Nat.cast_ofNat, inverse_five_nine,
          mul_right_comm (3 : ZMod 9), show (3 : ZMod 9) * 2 = 6 by decide]
      have hc3 : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
      have hc4 : Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
      have hc5 : Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) := by decide
      have hpair := odd_middle_pairs (j : ZMod 9)
      interval_cases h : (B / M)
      · have hn : ¬ (M < j ∧ j ≤ 2 * M) := by omega
        simp only [hc3, hn, ↓reduceIte, sub_zero, mul_one]
        simp [Finset.prod_insert, f1, f2, f3, ← mul_assoc, hpair]
      · have hm : M < j ∧ j ≤ 2 * M := by omega
        simp only [hc4, if_pos hm]
        simp [Finset.prod_insert, f1, f2, f3, f4, ← mul_assoc, hpair]
      · have hn : ¬ (M < j ∧ j ≤ 2 * M) := by omega
        simp only [hc5, hn, ↓reduceIte, sub_zero, mul_one]
        simp [Finset.prod_insert, f1, f2, f3, f4, f5, ← mul_assoc, hpair]
    · intro i hi hndi
      have hs : i.factorization 3 < s := by
        by_contra! h
        exact hndi (pow_dvd_of_le_exponent h)
      rw [normalized_factor_pow Nat.prime_three (by omega : i.factorization 3 ≤ s + 1),
        Nat.cast_ofNat, three_pow_zero (by omega : 2 ≤ s + 1 - i.factorization 3), zero_mul, zero_mul, sub_zero]
  · intro i hi
    have hb : i < 2 * N := by have := (mem_Icc.mp hi).2; omega
    exact dvd_mul_of_dvd_left (pow_dvd_pow 3 (nearby_exponent_le Nat.prime_three (mem_Icc.mp hi).1 hb)) _

private theorem ternary_prefactor {s j : ℕ} (hj : 0 < j) (hlt : j < 3 ^ (s + 1)) :
    (3 : ZMod 9) ^ (s + 1 - j.factorization 3) * ((ordCompl[3] j : ℕ) : ZMod 9)⁻¹ =
      if j = 3 ^ s then 3 else if j = 2 * 3 ^ s then 3 * ((2 : ZMod 9)⁻¹) else 0 := by
  let M := 3 ^ s
  have hM : 0 < M := pow_pos (by decide) _
  have hlt' : j < 3 * M := by simpa only [pow_succ'] using hlt
  by_cases hd : M ∣ j
  · obtain ⟨d, rfl⟩ := hd
    have hpos : 0 < d := by by_contra! h; interval_cases d; simp at hj
    have hsmall : d < 3 := by
      apply Nat.lt_of_mul_lt_mul_left (a := M)
      simpa only [mul_comm 3 M] using hlt'
    interval_cases d
    · have h := exponent_mul_unit Nat.prime_three (s := s) (m := 1) (by decide)
      rw [h, Nat.add_sub_cancel_left, pow_one, show M * 1 / 3 ^ s = 1 from Nat.mul_div_cancel_left _ hM]
      simp [M]
    · have h := exponent_mul_unit Nat.prime_three (s := s) (m := 2) (by decide)
      rw [h, Nat.add_sub_cancel_left, pow_one, show M * 2 / 3 ^ s = 2 from Nat.mul_div_cancel_left _ hM]
      have hne : M * 2 ≠ 3 ^ s := by change M * 2 ≠ M; omega
      rw [if_neg hne, if_pos (show M * 2 = 2 * 3 ^ s from mul_comm M 2), Nat.cast_ofNat]
  · have hs : j.factorization 3 < s := by
      by_contra! h
      exact hd (pow_dvd_of_le_exponent h)
    have hne₁ : j ≠ 3 ^ s := fun h => hd (h ▸ dvd_refl M)
    have hne₂ : j ≠ 2 * 3 ^ s := fun h => hd (h ▸ dvd_mul_left M 2)
    rw [three_pow_zero (by omega : 2 ≤ s + 1 - j.factorization 3), zero_mul, if_neg hne₁, if_neg hne₂]

theorem interior_normalized_nine {s j : ℕ} (hj : 0 < j) (hlt : j < 3 ^ (s + 1)) :
    (normalizedChoose 3 (s + 1) j : ZMod 9) = (-1)^j * (1 - (j : ZMod 9)) *
      (1 - if 3 ^ s < j ∧ j ≤ 2 * 3 ^ s then 3 * (j : ZMod 9) else 0) *
      (1 - if j = 3 ^ s then 3 else if j = 2 * 3 ^ s then 3 * ((2 : ZMod 9)⁻¹) else 0) := by
  have hm : ∃ s : ℕ, 0 < s ∧ 9 = 3 ^ s := ⟨2, by decide, by decide⟩
  have hs := exponent_lt Nat.prime_three hj hlt
  have hz : ((3 : ZMod 9) ^ (s + 1 - j.factorization 3)) ^ 2 = 0 := by
    rw [← pow_mul]
    exact three_pow_zero (by omega)
  have hodd : Odd (3 ^ (s + 1)) := (by decide : Odd (3 : ℕ)).pow
  obtain ⟨a, ha⟩ := hodd
  have hindex : 3 ^ (s + 1) + j - 1 = 2 * a + j := by omega
  rw [interior_scaled_eq Nat.prime_three hm hj hlt hz, Nat.cast_ofNat, ternary_prefactor hj hlt,
    cast_choose_nine hj hlt.le, hindex, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]
  ring

theorem end_normalized_nine {s : ℕ} (hs : 0 < s) :
    (normalizedChoose 3 (s + 1) (3 ^ (s + 1)) : ZMod 9) = -(2 : ZMod 9)⁻¹ := by
  have hm : ∃ s : ℕ, 0 < s ∧ 9 = 3 ^ s := ⟨2, by decide, by decide⟩
  have hN : 0 < 3 ^ (s + 1) := pow_pos (by decide) _
  have hM : 0 < 3 ^ s := pow_pos (by decide) _
  have hNM : 3 ^ (s + 1) = 3 * 3 ^ s := pow_succ' 3 s
  have hn : ¬ (3 ^ s < 3 ^ (s + 1) ∧ 3 ^ (s + 1) ≤ 2 * 3 ^ s) := by omega
  have hzero : ((3 ^ (s + 1) : ℕ) : ZMod 9) = 0 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact three_pow_zero (by omega)
  have hodd : Odd (3 ^ (s + 1)) := (by decide : Odd (3 : ℕ)).pow
  obtain ⟨a, ha⟩ := hodd
  have hindex : 3 ^ (s + 1) + 3 ^ (s + 1) - 1 = 2 * (2 * a) + 1 := by omega
  rw [end_scaled_eq Nat.prime_three (by decide : 3 ≠ 2) hm, cast_choose_nine hN le_rfl, if_neg hn,
    hzero, hindex, pow_add, pow_mul, neg_one_sq]
  simp

private def sumBaseline {R : Type*} [Ring R] (j : ℕ) : R :=
  (-1) ^ j * (1 - (j : R))

private lemma baselinePair {R : Type*} [CommRing R] (m : ℕ) :
    sumBaseline (R := R) (2 * m + 1) + sumBaseline (R := R) (2 * m + 2) = -1 := by
  simp only [sumBaseline, pow_add, pow_mul, pow_one, neg_one_sq,
    one_pow, one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  ring

private lemma baselineSum {R : Type*} [CommRing R] (m : ℕ) :
    (∑ j ∈ Ico 1 (2 * m + 1), sumBaseline (R := R) j) = -(m : R) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h₀ : 2 * (m + 1) + 1 = 2 * m + 2 + 1 := by omega
    have h₁ : 2 * m + 2 = (2 * m + 1) + 1 := by omega
    calc
      _ = (∑ j ∈ Ico 1 (2 * m + 1), sumBaseline (R := R) j) +
          (sumBaseline (R := R) (2 * m + 1) + sumBaseline (R := R) (2 * m + 2)) := by
        rw [h₀, sum_Ico_succ_top (by omega : 1 ≤ 2 * m + 2),
          h₁, sum_Ico_succ_top (by omega : 1 ≤ 2 * m + 1)]
        ac_rfl
      _ = _ := by rw [ih, baselinePair, Nat.cast_succ]; ring

private theorem oddPrimeSum (p r : ℕ) (hp : p.Prime) (hp₂ : 2 < p) (hr : 1 ≤ r) :
    (∑ j ∈ Ico 1 (p ^ r), (-1 : ZMod p) ^ j * (1 - (j : ZMod p))) -
      (2 : ZMod p)⁻¹ = 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (hp.odd_of_ne_two (by omega)).pow (n := r)
  have hn : p ^ r = 2 * m + 1 := by omega
  have hz : ((p ^ r : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_pow, ZMod.natCast_self, zero_pow (by omega : r ≠ 0)]
  have hc : (2 : ZMod p) * (m : ZMod p) + 1 = 0 := by
    rw [hn] at hz
    simpa using hz
  have h₂ : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact (not_le_of_gt hp₂) (Nat.le_of_dvd (by decide) hd)
  have hi := mul_inv_cancel₀ h₂
  change (∑ j ∈ Ico 1 (p ^ r), sumBaseline (R := ZMod p) j) - _ = _
  rw [hn, baselineSum]
  calc
    _ = (2 : ZMod p)⁻¹ * (-(2 * (m : ZMod p) + 1)) := by
      linear_combination (m : ZMod p) * hi
    _ = 0 := by rw [hc]; simp

private def ternaryRaw (j : ℕ) : ZMod 9 :=
  sumBaseline (R := ZMod 9) j * (3 * (j : ZMod 9))

private lemma rawResidue (t s : ℕ) :
    ternaryRaw (3 * t + s) =
      (-1 : ZMod 9) ^ (3 * t + s) * (3 * (s : ZMod 9) * (1 - (s : ZMod 9))) := by
  unfold ternaryRaw sumBaseline
  push_cast
  have h₉ : (9 : ZMod 9) = 0 := by decide
  linear_combination ((-1 : ZMod 9) ^ (3 * t + s) * (t : ZMod 9) *
    (1 - 3 * (t : ZMod 9) - 2 * (s : ZMod 9))) * h₉

private lemma rawBlock (t : ℕ) :
    ternaryRaw (3 * t + 1) + ternaryRaw (3 * t + 2) + ternaryRaw (3 * t + 3) =
      (3 : ZMod 9) * (-1) ^ t := by
  rw [rawResidue, rawResidue, rawResidue]
  have h₁ : (3 : ZMod 9) * ((1 : ℕ) : ZMod 9) * (1 - ((1 : ℕ) : ZMod 9)) = 0 :=
    by decide
  have h₂ : (3 : ZMod 9) * ((2 : ℕ) : ZMod 9) * (1 - ((2 : ℕ) : ZMod 9)) = 3 :=
    by decide
  have h₃ : (3 : ZMod 9) * ((3 : ℕ) : ZMod 9) * (1 - ((3 : ℕ) : ZMod 9)) = 0 :=
    by decide
  have h₂pow : (-1 : ZMod 9) ^ 2 = 1 := by decide
  have h₃pow : (-1 : ZMod 9) ^ 3 = -1 := by decide
  simp only [h₁, h₂, h₃, mul_zero, zero_add, add_zero, pow_add, pow_mul,
    h₂pow, h₃pow, mul_one]
  ring

private lemma middleBlocks (s k : ℕ) :
    (∑ j ∈ Ico (3 * s + 1) (3 * s + 3 * k + 1), ternaryRaw j) =
      3 * (-1 : ZMod 9) ^ s * ∑ i ∈ range k, (-1 : ZMod 9) ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    let t := s + k
    have ht : 3 * s + 3 * k + 1 = 3 * t + 1 := by dsimp [t]; omega
    have ht₃ : 3 * s + 3 * (k + 1) + 1 = (3 * t + 3) + 1 := by dsimp [t]; omega
    have h₃ : 3 * t + 3 = (3 * t + 2) + 1 := rfl
    have h₂ : 3 * t + 2 = (3 * t + 1) + 1 := rfl
    have hb : 3 * s + 1 ≤ 3 * t + 1 := by dsimp [t]; omega
    calc
      _ = (∑ j ∈ Ico (3 * s + 1) (3 * s + 3 * k + 1), ternaryRaw j) +
          (ternaryRaw (3 * t + 1) + ternaryRaw (3 * t + 2) + ternaryRaw (3 * t + 3)) := by
        rw [ht₃, sum_Ico_succ_top (by omega : 3 * s + 1 ≤ 3 * t + 3),
          h₃, sum_Ico_succ_top (by omega : 3 * s + 1 ≤ 3 * t + 2),
          h₂, sum_Ico_succ_top hb, ht]
        ac_rfl
      _ = _ := by
        rw [ih, rawBlock, sum_range_succ, show t = s + k from rfl, pow_add]
        ring

private lemma rawMiddle (m : ℕ) (hodd : Odd m) :
    (∑ j ∈ Ico (3 * m + 1) (2 * (3 * m) + 1), ternaryRaw j) = -3 := by
  rw [show 2 * (3 * m) + 1 = 3 * m + 3 * m + 1 by omega, middleBlocks]
  have hsum : (∑ i ∈ range m, (-1 : ZMod 9) ^ i) = 1 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [Fin.sum_neg_one_pow, Nat.not_even_iff_odd.mpr hodd]
  rw [hsum, hodd.neg_pow]
  ring

private theorem ternarySum (r : ℕ) (hr : 2 ≤ r) :
    let N : ℕ := 3 ^ r
    let M : ℕ := 3 ^ (r - 1)
    (∑ j ∈ Ico 1 N, (-1 : ZMod 9) ^ j * (1 - (j : ZMod 9)) *
      (1 - if M < j ∧ j ≤ 2 * M then 3 * (j : ZMod 9) else 0) *
      (1 - if j = M then 3 else if j = 2 * M then 3 * (2 : ZMod 9)⁻¹ else 0)) -
      (2 : ZMod 9)⁻¹ = 0 := by
  let m : ℕ := 3 ^ (r - 2)
  let M : ℕ := 3 * m
  let N : ℕ := 3 * M
  have hM : 3 ^ (r - 1) = M := by
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ, mul_comm]
  have hN : 3 ^ r = N := by
    rw [show r = (r - 1) + 1 by omega, pow_succ, hM, mul_comm]
  change (∑ j ∈ Ico 1 (3 ^ r), sumBaseline (R := ZMod 9) j *
    (1 - if 3 ^ (r - 1) < j ∧ j ≤ 2 * 3 ^ (r - 1) then 3 * (j : ZMod 9) else 0) *
    (1 - if j = 3 ^ (r - 1) then 3 else if j = 2 * 3 ^ (r - 1) then
      3 * (2 : ZMod 9)⁻¹ else 0)) - (2 : ZMod 9)⁻¹ = 0
  rw [hN, hM]
  have hm : 0 < m := by dsimp [m]; positivity
  have hMp : 0 < M := by dsimp [M]; omega
  have hNm : N = 3 * M := rfl
  have hoddm : Odd m := (by decide : Odd (3 : ℕ)).pow
  have hoddM : Odd M := (by decide : Odd (3 : ℕ)).mul hoddm
  have hoddN : Odd N := (by decide : Odd (3 : ℕ)).mul hoddM
  have h₉ : (9 : ZMod 9) = 0 := by decide
  have h25 : (5 : ZMod 9) * 2 = 1 := by decide
  have hi : (2 : ZMod 9) * (2 : ZMod 9)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ ⟨⟨2, 5, by decide, h25⟩, rfl⟩
  have hinv : (2 : ZMod 9)⁻¹ = 5 := by
    calc
      _ = (5 * 2) * (2 : ZMod 9)⁻¹ := by rw [h25, one_mul]
      _ = 5 * (2 * (2 : ZMod 9)⁻¹) := by ring
      _ = 5 := by rw [hi, mul_one]
  have hNzero : (N : ZMod 9) = 0 := by
    change ((3 * (3 * m) : ℕ) : ZMod 9) = 0
    push_cast
    linear_combination (m : ZMod 9) * h₉
  have hMzero : (3 : ZMod 9) * (M : ZMod 9) = 0 := by
    change (3 : ZMod 9) * ((3 * m : ℕ) : ZMod 9) = 0
    push_cast
    linear_combination (m : ZMod 9) * h₉
  let A : ℕ → ZMod 9 := fun j => if M < j ∧ j ≤ 2 * M then j else 0
  let C : ℕ → ZMod 9 := fun j => if j = M then 1 else if j = 2 * M then 2⁻¹ else 0
  have hexpand (j : ℕ) :
      sumBaseline (R := ZMod 9) j * (1 - 3 * A j) * (1 - 3 * C j) =
        sumBaseline (R := ZMod 9) j - sumBaseline (R := ZMod 9) j * (3 * A j) -
          sumBaseline (R := ZMod 9) j * (3 * C j) := by
    linear_combination (sumBaseline (R := ZMod 9) j * A j * C j) * h₉
  have hfactor (j : ℕ) :
      sumBaseline (R := ZMod 9) j *
        (1 - if M < j ∧ j ≤ 2 * M then 3 * (j : ZMod 9) else 0) *
        (1 - if j = M then 3 else if j = 2 * M then 3 * (2 : ZMod 9)⁻¹ else 0) =
      sumBaseline (R := ZMod 9) j * (1 - 3 * A j) * (1 - 3 * C j) := by
    simp only [A, C, mul_ite, mul_one, mul_zero]
  have hmidSet : (Ico 1 N).filter (fun j => M < j ∧ j ≤ 2 * M) =
      Ico (M + 1) (2 * M + 1) := by
    ext j
    simp only [mem_filter, mem_Ico]
    omega
  have hmid : (∑ j ∈ Ico 1 N, sumBaseline (R := ZMod 9) j * (3 * A j)) = -3 := by
    simp only [A, mul_ite, mul_zero]
    change (∑ j ∈ Ico 1 N, if M < j ∧ j ≤ 2 * M then ternaryRaw j else 0) = -3
    rw [← Finset.sum_filter, hmidSet]
    exact rawMiddle m hoddm
  have hmMem : M ∈ Ico 1 N := by rw [mem_Ico]; omega
  have h2mMem : 2 * M ∈ Ico 1 N := by rw [mem_Ico]; omega
  have hneq : M ≠ 2 * M := by omega
  have hpair (j : ℕ) : sumBaseline (R := ZMod 9) j * (3 * C j) =
      (if j = M then sumBaseline (R := ZMod 9) M * 3 else 0) +
      (if j = 2 * M then sumBaseline (R := ZMod 9) (2 * M) * (3 * (2 : ZMod 9)⁻¹) else 0) := by
    by_cases h₁ : j = M
    · subst j
      simp [C, hneq]
    · by_cases h₂ : j = 2 * M
      · subst j
        simp [C, h₁]
      · simp [C, h₁, h₂]
  have hvalue₁ : sumBaseline (R := ZMod 9) M * 3 = -3 := by
    rw [sumBaseline, hoddM.neg_pow]
    linear_combination hMzero
  have hvalue₂ : sumBaseline (R := ZMod 9) (2 * M) * (3 * (2 : ZMod 9)⁻¹) =
      3 * (2 : ZMod 9)⁻¹ := by
    simp only [sumBaseline, pow_mul, neg_one_sq, one_pow, one_mul, Nat.cast_mul, Nat.cast_ofNat]
    linear_combination (-2 * (2 : ZMod 9)⁻¹) * hMzero
  have hexcept : (∑ j ∈ Ico 1 N, sumBaseline (R := ZMod 9) j * (3 * C j)) = 3 := by
    simp_rw [hpair]
    rw [sum_add_distrib]
    simp [hmMem, h2mMem]
    rw [hvalue₁, hvalue₂, hinv]
    decide
  have hbase : (∑ j ∈ Ico 1 N, sumBaseline (R := ZMod 9) j) - (2 : ZMod 9)⁻¹ = 0 := by
    obtain ⟨s, hs⟩ := hoddN
    have hn : N = 2 * s + 1 := by omega
    have hc : (2 : ZMod 9) * (s : ZMod 9) + 1 = 0 := by
      rw [hn] at hNzero
      simpa using hNzero
    rw [hn, baselineSum]
    calc
      _ = (2 : ZMod 9)⁻¹ * (-(2 * (s : ZMod 9) + 1)) := by
        linear_combination (s : ZMod 9) * hi
      _ = 0 := by rw [hc]; simp
  simp_rw [hfactor, hexpand]
  rw [sum_sub_distrib, sum_sub_distrib, hmid, hexcept]
  linear_combination hbase

/-! The three divisibility claims obtained by summing the normalized terms. -/

private theorem a_split {N : ℕ} (hN : 0 < N) :
    a N = (∑ j ∈ Ico 1 N, (N * j).choose (N + j)) + (N * N).choose (N + N) := by
  unfold a
  rw [sum_range_succ, sum_range_eq_add_Ico _ hN]
  simp [Nat.choose_eq_zero_of_lt hN]

private theorem a_normalized {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    a (p ^ r) = p ^ r * ((∑ j ∈ Ico 1 (p ^ r), normalizedChoose p r j) + normalizedChoose p r (p ^ r)) := by
  rw [a_split (pow_pos hp.pos r), mul_add, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjlt⟩ := mem_Ico.mp hj
    exact (Nat.mul_div_cancel' (interior_dvd hp hj0 hjlt)).symm
  · exact (Nat.mul_div_cancel' (end_dvd_odd hp hp2)).symm

private theorem binary_congruence (r : ℕ) (hr : 2 ≤ r) :
    a (2 ^ r) ≡ 0 [MOD 2 ^ (r - 1)] := by
  apply Nat.modEq_zero_iff_dvd.mpr
  rw [a_split (pow_pos (by decide : 0 < 2) r)]
  refine dvd_add (Finset.dvd_sum fun j hj => ?_) (end_dvd_two (show 0 < r by omega))
  obtain ⟨hj0, hjlt⟩ := mem_Ico.mp hj
  exact (pow_dvd_pow 2 (Nat.sub_le r 1)).trans (interior_dvd Nat.prime_two hj0 hjlt)

private theorem odd_prime_congruence (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    a (p ^ r) ≡ 0 [MOD p ^ (r + 1)] := by
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd (p ^ r) := (hp.odd_of_ne_two hp2).pow
  apply Nat.modEq_zero_iff_dvd.mpr
  rw [a_normalized hp hp2, pow_succ]
  apply Nat.mul_dvd_mul_left
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_add, Nat.cast_sum, end_normalized_prime hp hp2 hr hodd, ← sub_eq_add_neg]
  convert oddPrimeSum p r hp (by omega) hr using 2
  apply sum_congr rfl
  intro j hj
  obtain ⟨hj0, hjlt⟩ := mem_Ico.mp hj
  exact interior_normalized_prime hp hodd hj0 hjlt

private theorem ternary_congruence (r : ℕ) (hr : 2 ≤ r) :
    a (3 ^ r) ≡ 0 [MOD 3 ^ (r + 2)] := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  apply Nat.modEq_zero_iff_dvd.mpr
  rw [a_normalized Nat.prime_three (by decide : 3 ≠ 2), pow_add]
  apply Nat.mul_dvd_mul_left
  change 9 ∣ _
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  rw [Nat.cast_add, Nat.cast_sum, end_normalized_nine (by omega : 0 < s), ← sub_eq_add_neg]
  have hsum :
      (∑ j ∈ Ico 1 (3 ^ (s + 1)), (normalizedChoose 3 (s + 1) j : ZMod 9)) =
        ∑ j ∈ Ico (1 : ℕ) (3 ^ (s + 1)), (-1 : ZMod 9) ^ j * (1 - (j : ZMod 9)) *
          (1 - if 3 ^ s < j ∧ j ≤ 2 * 3 ^ s then 3 * (j : ZMod 9) else 0) *
          (1 - if j = 3 ^ s then 3 else if j = 2 * 3 ^ s then 3 * (2 : ZMod 9)⁻¹ else 0) := by
    apply sum_congr rfl
    intro j hj
    obtain ⟨hj0, hjlt⟩ := mem_Ico.mp hj
    exact interior_normalized_nine hj0 hjlt
  rw [hsum]
  simpa only [Nat.add_sub_cancel] using ternarySum (s + 1) (by omega)

end OMA.S_oeis_a359842

theorem OMA.solution : type_of% @OMA.S_oeis_a359842.main := by
  exact ⟨OMA.S_oeis_a359842.binary_congruence, OMA.S_oeis_a359842.ternary_congruence,
    OMA.S_oeis_a359842.odd_prime_congruence⟩
