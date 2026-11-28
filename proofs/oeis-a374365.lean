import OMAStatements.S_oeis_a374365

/-!
# Vanishing Möbius sums at a fifth root of unity

Original proof by @agchua (PR #19316). The Möbius involution and reduction
modulo five are retained. The coefficient relation now uses Mathlib's
prime-order root-of-unity theorem directly.
-/

namespace A374365aux

theorem prim : IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 5)) 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have e : 2 * (Real.pi : ℂ) * Complex.I / ((5 : ℕ) : ℂ) = 2 * (Real.pi : ℂ) * Complex.I / 5 := by
    norm_num
  rw [e] at h
  exact h

theorem pow_mod5 (z : ℂ) (hz : z ^ 5 = 1) (n : ℕ) : z ^ n = z ^ (n % 5) := by
  conv_lhs => rw [← Nat.mod_add_div n 5]
  rw [pow_add, pow_mul, hz, one_pow, mul_one]

theorem cpow_eq (k : ℕ) :
    (-1 : ℂ) ^ ((2 * (k : ℂ)) / 5) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 5) ^ k := by
  rw [Complex.cpow_def_of_ne_zero (show (-1 : ℂ) ≠ 0 by norm_num), Complex.log_neg_one,
    ← Complex.exp_nat_mul]
  congr 1
  ring

theorem S_eq (m : ℕ) (hm : 1 ≤ m) :
    OMA.S_oeis_a374365.S m =
      ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 5) ^ d := by
  unfold OMA.S_oeis_a374365.S
  have hdiv : m.divisors = (Finset.Icc 1 m).filter (fun k => k ∣ m) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, _⟩
      have h1 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      have h2 : d ≤ m := Nat.le_of_dvd (by omega) hd
      exact ⟨⟨by omega, h2⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
  rw [hdiv, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  show (if k ∣ m then (1 : ℂ) else 0) * ((ArithmeticFunction.moebius k : ℤ) : ℂ) *
      (-1 : ℂ) ^ ((2 * (k : ℂ)) / 5) =
    if k ∣ m then ((ArithmeticFunction.moebius k : ℤ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 5) ^ k else 0
  rw [cpow_eq]
  split_ifs <;> simp

theorem li (z : ℂ) (hz : IsPrimitiveRoot z 5) (a b c d e : ℤ)
    (h : (a : ℂ) + b * z + c * z ^ 2 + d * z ^ 3 + e * z ^ 4 = 0) :
    a = e ∧ b = e ∧ c = e ∧ d = e := by
  have hc := (IsPrimitiveRoot.sum_eq_zero_iff_forall_eq_int (by decide) hz ![a,b,c,d,e]).mp
    (by simpa [Fin.sum_univ_succ, add_assoc] using h)
  exact ⟨hc 0 4, hc 1 4, hc 2 4, hc 3 4⟩

theorem regroup {R : Type*} [CommRing R] (s : Finset ℕ) (G : ℕ → R) :
    ∑ d ∈ s, ((ArithmeticFunction.moebius d : ℤ) : R) * G (d % 5) =
      ∑ r ∈ Finset.range 5,
        ((∑ d ∈ s with d % 5 = r, ArithmeticFunction.moebius d : ℤ) : R) * G r := by
  have h := Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.range 5)
    (g := fun d => d % 5) (fun d _ => Finset.mem_range.mpr (Nat.mod_lt d (by norm_num)))
    (fun d => ((ArithmeticFunction.moebius d : ℤ) : R) * G (d % 5))
  refine h.symm.trans ?_
  apply Finset.sum_congr rfl
  intro r _
  show ∑ i ∈ s with i % 5 = r, ((ArithmeticFunction.moebius i : ℤ) : R) * G (i % 5) =
    ((∑ d ∈ s with d % 5 = r, ArithmeticFunction.moebius d : ℤ) : R) * G r
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mem_filter] at hd
  rw [hd.2]

theorem sqf_rad (m : ℕ) : Squarefree (∏ p ∈ m.primeFactors, p) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro x hxp hxx
  have hx : _root_.Prime x := hxp.prime
  have hx1 : x ∣ ∏ p ∈ m.primeFactors, p := (dvd_mul_right x x).trans hxx
  obtain ⟨q, hq, hxq⟩ := (Prime.dvd_finsetProd_iff hx _).mp hx1
  have hqx : x = q := (Nat.prime_dvd_prime_iff_eq hxp (Nat.prime_of_mem_primeFactors hq)).mp hxq
  rw [← hqx] at hq
  rw [← Finset.mul_prod_erase _ _ hq] at hxx
  have hx2 : x ∣ ∏ p ∈ m.primeFactors.erase x, p := Nat.dvd_of_mul_dvd_mul_left hxp.pos hxx
  obtain ⟨q2, hq2, hxq2⟩ := (Prime.dvd_finsetProd_iff hx _).mp hx2
  have hq2' := Finset.mem_erase.mp hq2
  have hqx2 : x = q2 :=
    (Nat.prime_dvd_prime_iff_eq hxp (Nat.prime_of_mem_primeFactors hq2'.2)).mp hxq2
  exact hq2'.1 hqx2.symm

theorem rad_sum {R : Type*} [CommRing R] (m : ℕ) (hm : m ≠ 0) (F : ℕ → R) :
    ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : R) * F d =
      ∑ d ∈ (∏ p ∈ m.primeFactors, p).divisors,
        ((ArithmeticFunction.moebius d : ℤ) : R) * F d := by
  have hn0 : (∏ p ∈ m.primeFactors, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hnm : (∏ p ∈ m.primeFactors, p) ∣ m := Nat.prod_primeFactors_dvd m
  have hsq : ∀ s : Finset ℕ,
      ∑ d ∈ s with Squarefree d, ((ArithmeticFunction.moebius d : ℤ) : R) * F d =
        ∑ d ∈ s, ((ArithmeticFunction.moebius d : ℤ) : R) * F d := by
    intro s
    apply Finset.sum_filter_of_ne
    intro x _ hx
    apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
    intro h0
    apply hx
    rw [h0]
    simp
  rw [← hsq m.divisors, ← hsq (∏ p ∈ m.primeFactors, p).divisors]
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdm, _⟩, hd⟩
    refine ⟨⟨?_, hn0⟩, hd⟩
    rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.prod_primeFactors_dvd_iff hn0,
      Nat.primeFactors_prod_primeFactors]
    exact Nat.primeFactors_mono hdm hm
  · rintro ⟨⟨hdn, _⟩, hd⟩
    exact ⟨⟨hdn.trans hnm, hm⟩, hd⟩

theorem key (z : ℂ) (hz : z ^ 5 = 1) (p e : ℕ) (hp : p.Prime) (hp5 : p % 5 = 1)
    (he : ¬ p ∣ e) :
    ((ArithmeticFunction.moebius (p * e) : ℤ) : ℂ) * z ^ (p * e) =
      -(((ArithmeticFunction.moebius e : ℤ) : ℂ) * z ^ e) := by
  have hcop : Nat.Coprime p e := (Nat.Prime.coprime_iff_not_dvd hp).mpr he
  have hmod : p * e % 5 = e % 5 := by
    rw [Nat.mul_mod, hp5, one_mul, Nat.mod_mod]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp, pow_mod5 z hz (p * e), pow_mod5 z hz e, hmod]
  push_cast
  ring

theorem p5_of_p10 (p : ℕ) (hp : p.Prime) (h10 : p % 10 ≠ 1) : p % 5 ≠ 1 := by
  intro h5
  have h2 : 2 ∣ p := by omega
  have h22 : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
  omega

theorem one_sub_ne (p : ℕ) (h5 : p % 5 ≠ 1) : (1 : ZMod 5) - (p : ZMod 5) ≠ 0 := by
  intro h
  have h1 : ((p : ℕ) : ZMod 5) = ((1 : ℕ) : ZMod 5) := by
    rw [Nat.cast_one]
    exact (sub_eq_zero.mp h).symm
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  omega

end A374365aux

open OMA.S_oeis_a374365 A374365aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a374365.main := by
  intro m hm
  unfold InSeq
  rw [norm_eq_zero, S_eq m hm]
  generalize hz : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 5) = z
  have hzp : IsPrimitiveRoot z 5 := by
    rw [← hz]
    exact prim
  have hz5 : z ^ 5 = 1 := hzp.pow_eq_one
  have hm0 : m ≠ 0 := by omega
  constructor
  · intro h0
    by_contra hno'
    have hno : ∀ p : ℕ, p.Prime → p ∣ m → p % 10 ≠ 1 :=
      fun p hp hpm h10 => hno' ⟨p, hp, hpm, h10⟩
    have h0a : ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) * z ^ (d % 5) = 0 :=
      (Finset.sum_congr rfl (fun d _ => by rw [← pow_mod5 z hz5 d])).trans h0
    have h0b := (regroup m.divisors (fun r => z ^ r)).symm.trans h0a
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
      pow_one] at h0b
    obtain ⟨h04, h14, h24, h34⟩ := li z hzp
      (∑ d ∈ m.divisors with d % 5 = 0, ArithmeticFunction.moebius d)
      (∑ d ∈ m.divisors with d % 5 = 1, ArithmeticFunction.moebius d)
      (∑ d ∈ m.divisors with d % 5 = 2, ArithmeticFunction.moebius d)
      (∑ d ∈ m.divisors with d % 5 = 3, ArithmeticFunction.moebius d)
      (∑ d ∈ m.divisors with d % 5 = 4, ArithmeticFunction.moebius d)
      (by linear_combination h0b)
    have h10 : (10 : ZMod 5) = 0 := by decide
    have hchi0 : ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ZMod 5) *
        (((d % 5 : ℕ)) : ZMod 5) = 0 := by
      rw [regroup m.divisors (fun r => ((r : ℕ) : ZMod 5))]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [h04, h14, h24, h34]
      simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
      linear_combination
        ((∑ d ∈ m.divisors with d % 5 = 4, ArithmeticFunction.moebius d : ℤ) : ZMod 5) * h10
    have hz2 : ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ZMod 5) *
        ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction (ZMod 5)) d = 0 := by
      refine Eq.trans (Finset.sum_congr rfl ?_) hchi0
      intro d _
      exact congrArg (fun x => ((ArithmeticFunction.moebius d : ℤ) : ZMod 5) * x)
        (ZMod.natCast_mod d 5).symm
    have hprod := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction (ZMod 5))
      ArithmeticFunction.isMultiplicative_id.natCast (sqf_rad m)
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hne : ∏ p ∈ (∏ q ∈ m.primeFactors, q).primeFactors,
        (1 - ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction (ZMod 5)) p)
          ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro p hp
      rw [Nat.primeFactors_prod_primeFactors] at hp
      have hp' := Nat.mem_primeFactors.mp hp
      have h5 := p5_of_p10 p hp'.1 (hno p hp'.1 hp'.2.1)
      exact one_sub_ne p h5
    exact hne (hprod.trans ((rad_sum m hm0 _).symm.trans hz2))
  · rintro ⟨p, hp, hpm, hp10⟩
    have hp5 : p % 5 = 1 := by omega
    have hp2 : 2 ≤ p := hp.two_le
    have hpp : ∀ d : ℕ, Squarefree d → ¬ p * p ∣ d := by
      intro d hsq h
      have hu := hsq p h
      rw [Nat.isUnit_iff] at hu
      omega
    refine Finset.sum_involution
      (fun d _ => if p * p ∣ d then d else if p ∣ d then d / p else d * p) ?_ ?_ ?_ ?_
    · intro d hd
      by_cases h2 : p * p ∣ d
      · have hmu : ArithmeticFunction.moebius d = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun hsq => hpp d hsq h2)
        simp only [if_pos h2, hmu]
        simp
      · by_cases h1 : p ∣ d
        · obtain ⟨e, rfl⟩ := h1
          have he : ¬ p ∣ e := fun h => h2 (Nat.mul_dvd_mul_left p h)
          simp only [if_neg h2, if_pos (Nat.dvd_mul_right p e), Nat.mul_div_cancel_left e hp.pos]
          rw [key z hz5 p e hp hp5 he]
          ring
        · simp only [if_neg h2, if_neg h1]
          rw [Nat.mul_comm d p, key z hz5 p d hp hp5 h1]
          ring
    · intro d hd hf
      have hsq : Squarefree d := by
        apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
        intro h0
        apply hf
        rw [h0]
        simp
      have h2 := hpp d hsq
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      simp only [if_neg h2]
      split_ifs with h1
      · obtain ⟨e, rfl⟩ := h1
        rw [Nat.mul_div_cancel_left e hp.pos]
        have he0 : 0 < e := Nat.pos_of_ne_zero (fun h => by simp [h] at hd0)
        intro h
        nlinarith
      · intro h
        nlinarith
    · intro d hd
      show (if p * p ∣ d then d else if p ∣ d then d / p else d * p) ∈ m.divisors
      rw [Nat.mem_divisors] at hd ⊢
      split_ifs with h2 h1
      · exact hd
      · exact ⟨(Nat.div_dvd_of_dvd h1).trans hd.1, hd.2⟩
      · have hcop : Nat.Coprime d p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm
        exact ⟨hcop.mul_dvd_of_dvd_of_dvd hd.1 hpm, hd.2⟩
    · intro d hd
      by_cases h2 : p * p ∣ d
      · simp only [if_pos h2]
      · by_cases h1 : p ∣ d
        · obtain ⟨e, rfl⟩ := h1
          have he : ¬ p ∣ e := fun h => h2 (Nat.mul_dvd_mul_left p h)
          have he2 : ¬ p * p ∣ e := fun h => he ((Nat.dvd_mul_right p p).trans h)
          simp only [if_neg h2, if_pos (Nat.dvd_mul_right p e), Nat.mul_div_cancel_left e hp.pos,
            if_neg he2, if_neg he]
          ring
        · have hdp2 : ¬ p * p ∣ d * p := fun h => h1 (Nat.dvd_of_mul_dvd_mul_right hp.pos h)
          simp only [if_neg h2, if_neg h1, if_neg hdp2, if_pos (Nat.dvd_mul_left p d),
            Nat.mul_div_cancel d hp.pos]
