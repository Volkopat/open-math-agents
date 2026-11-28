import OMAStatements.S_oeis_a344200
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a344200

open Polynomial OMA.S_oeis_a344200

private lemma zmod2_add_self {R : Type*} [Ring R] [Algebra (ZMod 2) R] (x : R) : x + x = 0 := by
  have h2 : (2 : R) = 0 := by
    have h : algebraMap (ZMod 2) R (2 : ZMod 2) = 0 := by
      rw [show (2 : ZMod 2) = 0 by decide, map_zero]
    rw [map_ofNat] at h
    exact h
  calc x + x = (2 : R) * x := (two_mul x).symm
    _ = 0 * x := by rw [h2]
    _ = 0 := zero_mul x

private lemma zmod2_sub_eq_add {R : Type*} [Ring R] [Algebra (ZMod 2) R] (x y : R) :
    x - y = x + y := by
  have hy : -y = y := by
    have h := zmod2_add_self y
    calc -y = -y + (y + y) := by rw [h, add_zero]
      _ = (-y + y) + y := by rw [add_assoc]
      _ = y := by rw [neg_add_cancel, zero_add]
  rw [sub_eq_add_neg, hy]

private lemma zmod2_eq_of_add_eq_zero {R : Type*} [Ring R] [Algebra (ZMod 2) R] {x y : R}
    (h : x + y = 0) : x = y := by
  calc x = x + (y + y) := by rw [zmod2_add_self, add_zero]
    _ = (x + y) + y := by rw [add_assoc]
    _ = y := by rw [h, zero_add]


private lemma coeff_comp_X_pow (P : Polynomial (ZMod 2)) {p : ℕ} (hp : 0 < p) (n : ℕ) :
    (P.comp (X ^ p)).coeff n = if p ∣ n then P.coeff (n / p) else 0 := by
  induction P using Polynomial.induction_on' with
  | add f g hf hg =>
    rw [add_comp, coeff_add, hf, hg, coeff_add]
    split_ifs <;> simp
  | monomial i a =>
    rw [monomial_comp, coeff_C_mul, ← pow_mul, coeff_X_pow, coeff_monomial]
    by_cases h : n = p * i
    · rw [if_pos h, mul_one, if_pos ⟨i, h⟩, if_pos (by rw [h, Nat.mul_div_cancel_left i hp])]
    · rw [if_neg h, mul_zero]
      split_ifs with hd hi
      · obtain ⟨q, hq⟩ := hd
        rw [hq, Nat.mul_div_cancel_left q hp] at hi
        exact absurd (hi ▸ hq) h
      · rfl
      · rfl

private lemma natDegree_polyA {e r k m : ℕ} (hr : Odd r) (hk : Odd k) (hm : 2 ^ e * r * k < m) :
    (PolyA e r k m).natDegree = m ∧ (PolyA e r k m).Monic := by
  unfold PolyA
  have hq_pos : 0 < 2 ^ e * r := by
    obtain ⟨r', rfl⟩ := hr
    exact Nat.mul_pos (pow_pos (by decide) e) (by omega)
  have hk_pos : 0 < k := by
    obtain ⟨k', rfl⟩ := hk; omega
  have hdeg_tail : ((X ^ k + 1 : Polynomial (ZMod 2)) ^ (2 ^ e * r)).natDegree < m := by
    have h1 : (X ^ k + 1 : Polynomial (ZMod 2)).natDegree ≤ k := by
      refine le_trans (natDegree_add_le _ _) ?_
      simp
    calc ((X ^ k + 1 : Polynomial (ZMod 2)) ^ (2 ^ e * r)).natDegree
        ≤ (2 ^ e * r) * (X ^ k + 1 : Polynomial (ZMod 2)).natDegree := natDegree_pow_le
      _ ≤ (2 ^ e * r) * k := Nat.mul_le_mul_left _ h1
      _ < m := hm
  have hdeg_lt : ((X ^ k + 1 : Polynomial (ZMod 2)) ^ (2 ^ e * r)).natDegree <
      (X ^ m : Polynomial (ZMod 2)).natDegree := by
    rwa [natDegree_X_pow]
  refine ⟨?_, ?_⟩
  · rw [natDegree_add_eq_left_of_natDegree_lt hdeg_lt, natDegree_X_pow]
  · exact (monic_X_pow m).add_of_left (degree_lt_degree hdeg_lt)

private lemma natDegree_polyB {e r k m : ℕ} (hr : Odd r) (hk : Odd k) (hm : 2 ^ e * r * k < m) :
    (PolyB e r k m).natDegree = m ∧ (PolyB e r k m).Monic := by
  unfold PolyB
  have hq_pos : 0 < 2 ^ e * r * k := by
    obtain ⟨r', rfl⟩ := hr
    obtain ⟨k', rfl⟩ := hk
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by decide) e) (by omega)) (by omega)
  have hdeg_tail : (X ^ (2 ^ e * r * k) + 1 : Polynomial (ZMod 2)).natDegree < m := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
    simp only [natDegree_X_pow, natDegree_one]
    omega
  have hdeg_lt : (X ^ (2 ^ e * r * k) + 1 : Polynomial (ZMod 2)).natDegree <
      (X ^ m : Polynomial (ZMod 2)).natDegree := by
    rwa [natDegree_X_pow]
  rw [add_assoc]
  refine ⟨?_, ?_⟩
  · rw [natDegree_add_eq_left_of_natDegree_lt hdeg_lt, natDegree_X_pow]
  · exact (monic_X_pow m).add_of_left (degree_lt_degree hdeg_lt)

private lemma exists_irred_factor_lt_deg {P : Polynomial (ZMod 2)} (hdeg : 2 ≤ P.natDegree)
    (hred : ¬ Irreducible P) :
    ∃ f : Polynomial (ZMod 2), Irreducible f ∧ f ∣ P ∧ 1 ≤ f.natDegree ∧ f.natDegree < P.natDegree := by
  have hP0 : P ≠ 0 := by intro h; rw [h, natDegree_zero] at hdeg; omega
  have hPnunit : ¬ IsUnit P := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  rw [irreducible_iff] at hred
  push Not at hred
  obtain ⟨a, b, hPab, ha_nu, hb_nu⟩ := hred hPnunit
  have ha0 : a ≠ 0 := fun h => hP0 (by rw [hPab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hP0 (by rw [hPab, h, mul_zero])
  have ha_deg : 1 ≤ a.natDegree := by
    by_contra h0
    have ha_eq0 : a.natDegree = 0 := by omega
    have haC := Polynomial.eq_C_of_natDegree_eq_zero ha_eq0
    have hc0 : a.coeff 0 ≠ 0 := fun h => ha0 (by rw [haC, h, map_zero])
    exact ha_nu (haC ▸ isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
  have hb_deg : 1 ≤ b.natDegree := by
    by_contra h0
    have hb_eq0 : b.natDegree = 0 := by omega
    have hbC := Polynomial.eq_C_of_natDegree_eq_zero hb_eq0
    have hc0 : b.coeff 0 ≠ 0 := fun h => hb0 (by rw [hbC, h, map_zero])
    exact hb_nu (hbC ▸ isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
  have hdeg_sum : P.natDegree = a.natDegree + b.natDegree := by
    rw [hPab, natDegree_mul ha0 hb0]
  obtain ⟨f, hf_irred, hfa⟩ := WfDvdMonoid.exists_irreducible_factor ha_nu ha0
  have hf_deg1 : 1 ≤ f.natDegree := by
    by_contra h0
    have hf_eq0 : f.natDegree = 0 := by omega
    have hfC := Polynomial.eq_C_of_natDegree_eq_zero hf_eq0
    have hc0 : f.coeff 0 ≠ 0 := fun h => hf_irred.ne_zero (by rw [hfC, h, map_zero])
    exact hf_irred.not_isUnit (hfC ▸ isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
  have hf_le_a : f.natDegree ≤ a.natDegree := Polynomial.natDegree_le_of_dvd hfa ha0
  refine ⟨f, hf_irred, dvd_trans hfa ⟨b, hPab⟩, hf_deg1, by omega⟩

private lemma poly_dvd_of_aeval_zero {L : Type*} [Field L] [Algebra (ZMod 2) L]
    {A P : Polynomial (ZMod 2)} (hA : Irreducible A) {z : L}
    (hzA : aeval z A = 0) (hzP : aeval z P = 0) : A ∣ P := by
  obtain ⟨g, hg⟩ : ∃ g, g = EuclideanDomain.gcd P A := ⟨_, rfl⟩
  have hgA : g ∣ A := hg ▸ EuclideanDomain.gcd_dvd_right P A
  have hgP : g ∣ P := hg ▸ EuclideanDomain.gcd_dvd_left P A
  obtain ⟨q, hq⟩ := hgA
  rcases hA.isUnit_or_isUnit hq with hgu | hqu
  · exfalso
    have hbez : g = P * EuclideanDomain.gcdA P A + A * EuclideanDomain.gcdB P A :=
      hg.trans (EuclideanDomain.gcd_eq_gcd_ab P A)
    have hev := congrArg (aeval z) hbez
    rw [map_add, map_mul, map_mul, hzP, hzA, zero_mul, zero_mul, add_zero] at hev
    obtain ⟨u, hu⟩ := hgu
    have h1 := congrArg (aeval z)
      (show (u : Polynomial (ZMod 2)) * (u⁻¹ : (Polynomial (ZMod 2))ˣ) = 1 from u.mul_inv)
    rw [map_mul, map_one, hu, hev, zero_mul] at h1
    exact zero_ne_one h1
  · obtain ⟨u, hu⟩ := hqu
    have hAg : A ∣ g := ⟨((u⁻¹ : (Polynomial (ZMod 2))ˣ) : Polynomial (ZMod 2)), by
      calc g = g * ((u : Polynomial (ZMod 2)) * ((u⁻¹ : (Polynomial (ZMod 2))ˣ) : Polynomial (ZMod 2))) := by
              rw [Units.mul_inv, mul_one]
        _ = (g * q) * ((u⁻¹ : (Polynomial (ZMod 2))ˣ) : Polynomial (ZMod 2)) := by rw [hu]; ring
        _ = A * ((u⁻¹ : (Polynomial (ZMod 2))ˣ) : Polynomial (ZMod 2)) := by rw [← hq]⟩
    exact dvd_trans hAg hgP

private lemma card_adjoinRoot_zmod2 {f : Polynomial (ZMod 2)} (hf : Irreducible f) :
    have : Fact (Irreducible f) := ⟨hf⟩
    Nat.card (AdjoinRoot f) = 2 ^ f.natDegree := by
  have : Fact (Irreducible f) := ⟨hf⟩
  have hfin : Module.finrank (ZMod 2) (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis hf.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have : Module.Finite (ZMod 2) (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis hf.ne_zero).finite
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := AdjoinRoot f)
  rw [hfin, Nat.card_zmod] at hcard
  exact hcard

private lemma part_i {e r k m : ℕ} (hr : Odd r) (hk : Odd k) (hm : 2 ^ e * r * k < m)
    (hA : Irreducible (PolyA e r k m)) : Irreducible (PolyB e r k m) := by
  have ⟨hdegA, _⟩ := natDegree_polyA hr hk hm
  have ⟨hdegB, _⟩ := natDegree_polyB hr hk hm
  have hq_pos : 0 < 2 ^ e * r * k := by
    obtain ⟨r', rfl⟩ := hr; obtain ⟨k', rfl⟩ := hk
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by decide) e) (by omega)) (by omega)
  by_contra hBred
  obtain ⟨f, hf_irred, hfB, hf_deg1, hf_lt⟩ := exists_irred_factor_lt_deg (by omega : 2 ≤ (PolyB e r k m).natDegree) hBred
  have : Fact (Irreducible f) := ⟨hf_irred⟩
  let L := AdjoinRoot f
  let y : L := AdjoinRoot.root f
  have hyf : aeval y f = 0 := AdjoinRoot.aeval_eq f ▸ AdjoinRoot.mk_self
  have hyB : aeval y (PolyB e r k m) = 0 := by
    obtain ⟨g, hg⟩ := hfB
    rw [hg, map_mul, hyf, zero_mul]
  have hy_eq : y ^ m = y ^ (2 ^ e * r * k) + 1 := by
    have h0 : y ^ m + (y ^ (2 ^ e * r * k) + 1) = 0 := by
      simpa [PolyB, add_assoc] using hyB
    exact zmod2_eq_of_add_eq_zero h0
  let q := 2 ^ e * r
  let z : L := y ^ q
  have hzA : aeval z (PolyA e r k m) = 0 := by
    have hz_eq : z ^ m = (z ^ k + 1) ^ q := by
      calc z ^ m = (y ^ q) ^ m := rfl
        _ = (y ^ m) ^ q := by rw [← pow_mul, mul_comm, pow_mul]
        _ = (y ^ (q * k) + 1) ^ q := by rw [hy_eq]
        _ = (z ^ k + 1) ^ q := by simp only [z, pow_mul]
    simp only [PolyA, map_add, map_pow, aeval_X, map_one]
    rw [hz_eq]
    exact zmod2_add_self _
  -- Pigeonhole: maps (Fin m → ZMod 2) → L has domain size 2^m > 2^(f.natDegree) = card L
  have hcardL : Nat.card L = 2 ^ f.natDegree := card_adjoinRoot_zmod2 hf_irred
  have : Module.Finite (ZMod 2) L := (AdjoinRoot.powerBasis hf_irred.ne_zero).finite
  have : Finite L := Module.finite_of_finite (ZMod 2)
  let evalVec : (Fin m → ZMod 2) → L := fun c => ∑ i : Fin m, algebraMap (ZMod 2) L (c i) * z ^ i.1
  have hnot_inj : ¬ Function.Injective evalVec := by
    intro hinj
    have hle := Nat.card_le_card_of_injective evalVec hinj
    rw [hcardL, Nat.card_pi] at hle
    simp only [Nat.card_zmod, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hle
    have hlt : 2 ^ f.natDegree < 2 ^ m := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  rw [Function.Injective] at hnot_inj
  push Not at hnot_inj
  obtain ⟨c₁, c₂, heq, hne⟩ := hnot_inj
  let P : Polynomial (ZMod 2) := ∑ i : Fin m, C (c₁ i - c₂ i) * X ^ i.1
  have hP_coeff : ∀ j : ℕ, P.coeff j = if hj : j < m then c₁ ⟨j, hj⟩ - c₂ ⟨j, hj⟩ else 0 := by
    intro j
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    by_cases hj : j < m
    · rw [dif_pos hj, Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro i _ hij
        have : j ≠ i.1 := fun h => hij (Fin.ext h.symm)
        simp [this]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    · rw [dif_neg hj]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : j ≠ i.1 := by omega
      simp [this]
  have hP_ne0 : P ≠ 0 := by
    intro h0
    apply hne
    funext i
    have hc := congrArg (fun Q : Polynomial (ZMod 2) => Q.coeff i.1) h0
    rw [hP_coeff i.1, dif_pos i.2, coeff_zero] at hc
    exact sub_eq_zero.mp hc
  have hP_deg : P.natDegree < m := by
    by_contra hge
    have hlc : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hP_ne0
    rw [hP_coeff P.natDegree, dif_neg (by omega)] at hlc
    exact hlc rfl
  have hP_eval : aeval z P = 0 := by
    simp only [P, map_sum, map_mul, map_pow, aeval_C, aeval_X, map_sub]
    have heq' : (∑ i : Fin m, (algebraMap (ZMod 2) L (c₁ i) - algebraMap (ZMod 2) L (c₂ i)) * z ^ i.1) =
        evalVec c₁ - evalVec c₂ := by
      simp only [evalVec, sub_mul, Finset.sum_sub_distrib]
    rw [heq', heq, sub_self]
  have hAdvdP : PolyA e r k m ∣ P := poly_dvd_of_aeval_zero hA hzA hP_eval
  have hle_deg := Polynomial.natDegree_le_of_dvd hAdvdP hP_ne0
  omega

private lemma part_ii_c {e r k m : ℕ} (hr : Odd r) (hk : Odd k) (hm : 2 ^ e * r * k < m)
    (hB : Irreducible (PolyB e r k m)) (he : 0 < e) : Odd m := by
  by_contra hnotodd
  rw [Nat.not_odd_iff_even] at hnotodd
  obtain ⟨m', hm'⟩ := hnotodd
  have hm2 : m = 2 * m' := by omega
  have h2qk : 2 ∣ 2 ^ e * r * k := by
    have h2e : 2 ∣ 2 ^ e := dvd_pow_self 2 (by omega)
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h2e r) k
  obtain ⟨s, hs⟩ := h2qk
  have hBsq : PolyB e r k m = (X ^ m' + X ^ s + 1) ^ 2 := by
    have hadd2 : ∀ u v : Polynomial (ZMod 2), (u + v) ^ 2 = u ^ 2 + v ^ 2 := by
      intro u v
      calc (u + v) ^ 2 = u ^ 2 + (u * v + u * v) + v ^ 2 := by ring
        _ = u ^ 2 + 0 + v ^ 2 := by rw [zmod2_add_self]
        _ = u ^ 2 + v ^ 2 := by rw [add_zero]
    unfold PolyB
    rw [hadd2, hadd2, one_pow, ← pow_mul, ← pow_mul, mul_comm m' 2, mul_comm s 2, ← hm2, ← hs]
  have hq_pos : 0 < 2 ^ e * r * k := by
    obtain ⟨r', rfl⟩ := hr; obtain ⟨k', rfl⟩ := hk
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by decide) e) (by omega)) (by omega)
  have hm'_gt_s : s < m' := by omega
  have hf_deg : (X ^ m' + X ^ s + 1 : Polynomial (ZMod 2)).natDegree = m' := by
    rw [add_assoc, natDegree_add_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow m'
    · rw [natDegree_X_pow]
      refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
      simp only [natDegree_X_pow, natDegree_one]
      omega
  have hf_nu : ¬ IsUnit (X ^ m' + X ^ s + 1 : Polynomial (ZMod 2)) := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  rw [sq] at hBsq
  rcases hB.isUnit_or_isUnit hBsq with hu | hu <;> exact hf_nu hu

private lemma part_ii_a {e r k m : ℕ} (hr : Odd r) (hk : Odd k) (hm : 2 ^ e * r * k < m)
    (hB : Irreducible (PolyB e r k m)) (hAn : ¬ Irreducible (PolyA e r k m)) :
    1 < Nat.gcd m r := by
  have ⟨hdegA, hmonA⟩ := natDegree_polyA hr hk hm
  have ⟨hdegB, hmonB⟩ := natDegree_polyB hr hk hm
  have hq_pos : 0 < 2 ^ e * r * k := by
    obtain ⟨r', rfl⟩ := hr; obtain ⟨k', rfl⟩ := hk
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by decide) e) (by omega)) (by omega)
  by_contra hle1
  have hr_pos : 0 < r := by obtain ⟨r', rfl⟩ := hr; omega
  have hgcd_r : Nat.gcd m r = 1 := by
    have hpos : 0 < Nat.gcd m r := Nat.gcd_pos_of_pos_right m hr_pos
    omega
  set q := 2 ^ e * r
  have hgcd_q : Nat.gcd m q = 1 := by
    by_cases he : e = 0
    · simpa [q, he] using hgcd_r
    · have hmodd : Odd m := part_ii_c hr hk hm hB (by omega)
      have hcop2 : Nat.Coprime m (2 ^ e) := by
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_comm, (by decide : Nat.Prime 2).coprime_iff_not_dvd]
        obtain ⟨t, rfl⟩ := hmodd; omega
      exact hcop2.mul_right hgcd_r
  -- Work in L = AdjoinRoot B (field of cardinality 2^m)
  have : Fact (Irreducible (PolyB e r k m)) := ⟨hB⟩
  let L := AdjoinRoot (PolyB e r k m)
  let y : L := AdjoinRoot.root (PolyB e r k m)
  have hyB : aeval y (PolyB e r k m) = 0 := AdjoinRoot.aeval_eq (PolyB e r k m) ▸ AdjoinRoot.mk_self
  have hy_eq : y ^ m = y ^ (q * k) + 1 := by
    have h0 : y ^ m + (y ^ (q * k) + 1) = 0 := by simpa [PolyB, q, add_assoc] using hyB
    exact zmod2_eq_of_add_eq_zero h0
  have hy_ne0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : m ≠ 0), zero_pow (by omega : q * k ≠ 0), zero_add] at hy_eq
    exact zero_ne_one hy_eq
  let z : L := y ^ q
  have hzA : aeval z (PolyA e r k m) = 0 := by
    have hz_eq : z ^ m = (z ^ k + 1) ^ q := by
      calc z ^ m = (y ^ q) ^ m := rfl
        _ = (y ^ m) ^ q := by rw [← pow_mul, mul_comm, pow_mul]
        _ = (y ^ (q * k) + 1) ^ q := by rw [hy_eq]
        _ = (z ^ k + 1) ^ q := by simp only [z, pow_mul]
    simp only [PolyA, map_add, map_pow, aeval_X, map_one]
    rw [hz_eq]
    exact zmod2_add_self _
  -- Express y as a polynomial in z over ZMod 2!
  have htot_pos : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega)
  let a := q ^ (Nat.totient m - 1)
  have haq_mod : a * q ≡ 1 [MOD m] := by
    have hpow : a * q = q ^ Nat.totient m := by
      simp only [a]
      conv_rhs => rw [show Nat.totient m = (Nat.totient m - 1) + 1 by omega, pow_succ]
    rw [hpow]
    exact Nat.ModEq.pow_totient (Nat.coprime_comm.mp hgcd_q)
  have haq_eq : a * q = m * (a * q / m) + 1 := by
    have hdiv := Nat.div_add_mod (a * q) m
    have hmod1 : a * q % m = 1 := Eq.trans haq_mod (Nat.mod_eq_of_lt (by omega))
    omega
  set b := a * q / m
  have : Module.Finite (ZMod 2) L := (AdjoinRoot.powerBasis hB.ne_zero).finite
  have : Finite L := Module.finite_of_finite (ZMod 2)
  let : Fintype L := Fintype.ofFinite L
  have hcardL : Fintype.card L = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card, card_adjoinRoot_zmod2 hB, hdegB]
  have hzk1_ne0 : z ^ k + 1 ≠ 0 := by
    have hzk : z ^ k + 1 = y ^ m := by simpa [z, pow_mul] using hy_eq.symm
    rw [hzk]
    exact pow_ne_zero m hy_ne0
  have hpow_ne0 : (z ^ k + 1) ^ b ≠ 0 := pow_ne_zero b hzk1_ne0
  have hinv_eq : ((z ^ k + 1) ^ b) ^ (2 ^ m - 2) * (z ^ k + 1) ^ b = 1 := by
    have h2m : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← pow_succ, show 2 ^ m - 2 + 1 = Fintype.card L - 1 by omega]
    exact FiniteField.pow_card_sub_one_eq_one _ hpow_ne0
  let R : Polynomial (ZMod 2) := X ^ a * ((X ^ k + 1) ^ b) ^ (2 ^ m - 2)
  have hy_poly : y = aeval z R := by
    have hza : z ^ a = (z ^ k + 1) ^ b * y := by
      calc z ^ a = y ^ (a * q) := by simp only [z, ← pow_mul, mul_comm q a]
        _ = y ^ (m * b + 1) := by rw [haq_eq]
        _ = (y ^ m) ^ b * y := by rw [pow_add, pow_one, pow_mul]
        _ = (z ^ k + 1) ^ b * y := by
            have hzk : y ^ m = z ^ k + 1 := by simpa [z, pow_mul] using hy_eq
            rw [hzk]
    simp only [R, map_mul, map_pow, map_add, aeval_X, map_one]
    rw [hza]
    calc y = 1 * y := (one_mul y).symm
      _ = (((z ^ k + 1) ^ b) ^ (2 ^ m - 2) * (z ^ k + 1) ^ b) * y := by rw [hinv_eq]
      _ = (z ^ k + 1) ^ b * y * ((z ^ k + 1) ^ b) ^ (2 ^ m - 2) := by ring
  -- Since A is reducible of degree m, it factors as A = g1 * g2 with 1 ≤ deg g1, deg g2 < m
  have hAnu : ¬ IsUnit (PolyA e r k m) := by
    intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
  rw [irreducible_iff] at hAn
  push Not at hAn
  obtain ⟨g₁, g₂, hAg, hg1_nu, hg2_nu⟩ := hAn hAnu
  have hg1_0 : g₁ ≠ 0 := fun h => hmonA.ne_zero (by rw [hAg, h, zero_mul])
  have hg2_0 : g₂ ≠ 0 := fun h => hmonA.ne_zero (by rw [hAg, h, mul_zero])
  have hdeg_g1 : 1 ≤ g₁.natDegree := by
    by_contra h0
    have hC := Polynomial.eq_C_of_natDegree_eq_zero (by omega : g₁.natDegree = 0)
    have hc0 : g₁.coeff 0 ≠ 0 := fun h => hg1_0 (by rw [hC, h, map_zero])
    exact hg1_nu (hC ▸ isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
  have hdeg_g2 : 1 ≤ g₂.natDegree := by
    by_contra h0
    have hC := Polynomial.eq_C_of_natDegree_eq_zero (by omega : g₂.natDegree = 0)
    have hc0 : g₂.coeff 0 ≠ 0 := fun h => hg2_0 (by rw [hC, h, map_zero])
    exact hg2_nu (hC ▸ isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
  have hsum_deg : g₁.natDegree + g₂.natDegree = m := by
    rw [← natDegree_mul hg1_0 hg2_0, ← hAg, hdegA]
  have hprod0 : aeval z g₁ * aeval z g₂ = 0 := by
    rw [← map_mul, ← hAg, hzA]
  obtain ⟨g, hgz, hg0, hg_lt⟩ : ∃ g : Polynomial (ZMod 2), aeval z g = 0 ∧ g ≠ 0 ∧ g.natDegree < m := by
    rcases mul_eq_zero.mp hprod0 with h1 | h2
    · exact ⟨g₁, h1, hg1_0, by omega⟩
    · exact ⟨g₂, h2, hg2_0, by omega⟩
  -- Every element of L is aeval z Q for some Q with deg Q < g.natDegree!
  -- Normalize g to be monic (over ZMod 2, every nonzero polynomial is ALREADY monic!)
  have hg_monic : g.Monic := by
    have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have h1 : g.leadingCoeff = 1 := by
      have h01 : g.leadingCoeff = 0 ∨ g.leadingCoeff = 1 := by
        generalize g.leadingCoeff = c
        fin_cases c
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases h01 with h | h
      · exact absurd h hlc
      · exact h
    exact h1
  let evalLow : (Fin g.natDegree → ZMod 2) → L := fun c => ∑ i : Fin g.natDegree, algebraMap (ZMod 2) L (c i) * z ^ i.1
  have hsurj : Function.Surjective evalLow := by
    intro w
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective w
    let Q := (P.comp R) %ₘ g
    have hQ_eval : aeval z Q = AdjoinRoot.mk (PolyB e r k m) P := by
      have hdiv := Polynomial.modByMonic_add_div (P.comp R) g
      have hev := congrArg (aeval z) hdiv
      rw [map_add, map_mul, hgz, zero_mul, add_zero] at hev
      rw [hev, aeval_comp, ← hy_poly]
      exact AdjoinRoot.aeval_eq P
    have hQ_deg : ∀ j : ℕ, g.natDegree ≤ j → Q.coeff j = 0 := by
      intro j hj
      by_cases hQ0 : Q = 0
      · simp [hQ0]
      · have hlt : Q.natDegree < g.natDegree := by
          have := Polynomial.degree_modByMonic_lt (P.comp R) hg_monic
          rwa [Polynomial.degree_eq_natDegree hQ0, Polynomial.degree_eq_natDegree hg0,
            Nat.cast_lt] at this
        exact coeff_eq_zero_of_natDegree_lt (by omega)
    refine ⟨fun i => Q.coeff i.1, ?_⟩
    rw [← hQ_eval]
    have hQ_sum : Q = ∑ i : Fin g.natDegree, C (Q.coeff i.1) * X ^ i.1 := by
      ext j
      rw [finsetSum_coeff]
      simp only [coeff_C_mul, coeff_X_pow]
      by_cases hj : j < g.natDegree
      · rw [Finset.sum_eq_single ⟨j, hj⟩]
        · simp
        · intro i _ hij; have : j ≠ i.1 := fun h => hij (Fin.ext h.symm); simp [this]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      · rw [hQ_deg j (by omega)]
        symm
        refine Finset.sum_eq_zero fun i _ => ?_
        have : j ≠ i.1 := by omega
        simp [this]
    conv_rhs => rw [hQ_sum]
    simp [evalLow, map_sum, map_mul, map_pow]
  have hcard_le := Fintype.card_le_of_surjective evalLow hsurj
  rw [hcardL, Fintype.card_pi] at hcard_le
  simp only [ZMod.card, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard_le
  have hlt : 2 ^ g.natDegree < 2 ^ m := Nat.pow_lt_pow_right (by decide) hg_lt
  omega

private lemma part_ii_b {e r k m p : ℕ} (hr : Odd r) (hk : Odd k) (hm : 2 ^ e * r * k < m)
    (hB : Irreducible (PolyB e r k m)) (hp : p.Prime) (hpdvd : p ∣ Nat.gcd m (r * k)) :
    p * orderOf (2 : ZMod p) ∣ m := by
  have ⟨hdegB, _⟩ := natDegree_polyB hr hk hm
  have hpm : p ∣ m := dvd_trans hpdvd (Nat.gcd_dvd_left m (r * k))
  have hprk : p ∣ r * k := dvd_trans hpdvd (Nat.gcd_dvd_right m (r * k))
  have hp_odd : p ≠ 2 := by
    intro h2
    rw [h2] at hprk
    obtain ⟨t, ht⟩ := hr.mul hk
    have h0 : (r * k) % 2 = 0 := Nat.mod_eq_zero_of_dvd hprk
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨d, hd_eq⟩ := hpm
  have hpqk : p ∣ 2 ^ e * r * k := by
    rw [mul_assoc]; exact dvd_mul_of_dvd_right hprk (2 ^ e)
  obtain ⟨s, hs_eq⟩ := hpqk
  have hs_pos : 0 < s := by
    have hq_pos : 0 < 2 ^ e * r * k := by
      obtain ⟨r', rfl⟩ := hr; obtain ⟨k', rfl⟩ := hk
      exact Nat.mul_pos (Nat.mul_pos (pow_pos (by decide) e) (by omega)) (by omega)
    nlinarith
  have hd_gt_s : s < d := by nlinarith
  have hd_pos : 1 ≤ d := by omega
  -- B(X) = C(X^p) where C(T) = T^d + T^s + 1
  let Cpoly : Polynomial (ZMod 2) := X ^ d + X ^ s + 1
  have hC_deg : Cpoly.natDegree = d ∧ Cpoly.Monic := by
    unfold Cpoly
    have hlt : (X ^ s + 1 : Polynomial (ZMod 2)).natDegree < (X ^ d : Polynomial (ZMod 2)).natDegree := by
      rw [natDegree_X_pow]
      refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
      simp only [natDegree_X_pow, natDegree_one]; omega
    rw [add_assoc]
    exact ⟨by rw [natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow],
      (monic_X_pow d).add_of_left (degree_lt_degree hlt)⟩
  have hB_comp : PolyB e r k m = Cpoly.comp (X ^ p) := by
    unfold PolyB Cpoly
    simp only [add_comp, pow_comp, X_comp, one_comp, ← pow_mul, ← hd_eq, ← hs_eq]
  have hC_irred : Irreducible Cpoly := by
    have hCnu : ¬ IsUnit Cpoly := by
      intro hu; have := Polynomial.natDegree_eq_zero_of_isUnit hu; omega
    refine ⟨hCnu, fun a b hab => ?_⟩
    have hBfac : PolyB e r k m = a.comp (X ^ p) * b.comp (X ^ p) := by
      rw [hB_comp, hab, mul_comp]
    rcases hB.isUnit_or_isUnit hBfac with hua | hub
    · left
      have ha0 : a ≠ 0 := fun h => hC_deg.2.ne_zero (by rw [hab, h, zero_mul])
      have hdeg0 : (a.comp (X ^ p)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hua
      rw [natDegree_comp, natDegree_X_pow] at hdeg0
      have ha_deg0 : a.natDegree = 0 := by
        rcases mul_eq_zero.mp hdeg0 with h | h <;> omega
      have haC := Polynomial.eq_C_of_natDegree_eq_zero ha_deg0
      have hc0 : a.coeff 0 ≠ 0 := fun h => ha0 (by rw [haC, h, map_zero])
      exact haC ▸ isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
    · right
      have hb0 : b ≠ 0 := fun h => hC_deg.2.ne_zero (by rw [hab, h, mul_zero])
      have hdeg0 : (b.comp (X ^ p)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hub
      rw [natDegree_comp, natDegree_X_pow] at hdeg0
      have hb_deg0 : b.natDegree = 0 := by
        rcases mul_eq_zero.mp hdeg0 with h | h <;> omega
      have hbC := Polynomial.eq_C_of_natDegree_eq_zero hb_deg0
      have hc0 : b.coeff 0 ≠ 0 := fun h => hb0 (by rw [hbC, h, map_zero])
      exact hbC ▸ isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
  -- Suffices to show orderOf (2 : ZMod p) ∣ d
  suffices hord : orderOf (2 : ZMod p) ∣ d by
    rw [hd_eq]; exact mul_dvd_mul_left p hord
  rw [orderOf_dvd_iff_pow_eq_one]
  by_contra hpow_ne1
  have hndvd : ¬ p ∣ 2 ^ d - 1 := by
    intro hdvd
    apply hpow_ne1
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
    have hmod : 2 ^ d ≡ 1 [MOD p] := ((Nat.modEq_iff_dvd' h1).mpr hdvd).symm
    have hz := (ZMod.natCast_eq_natCast_iff (2 ^ d) 1 p).mpr hmod
    simpa [Nat.cast_pow] using hz
  have hcop : Nat.Coprime p (2 ^ d - 1) := hp.coprime_iff_not_dvd.mpr hndvd
  -- Work in K = AdjoinRoot Cpoly (cardinality 2^d)
  have : Fact (Irreducible Cpoly) := ⟨hC_irred⟩
  let K := AdjoinRoot Cpoly
  have : Module.Finite (ZMod 2) K := (AdjoinRoot.powerBasis hC_irred.ne_zero).finite
  have : Finite K := Module.finite_of_finite (ZMod 2)
  let : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 2 ^ d := by
    rw [← Nat.card_eq_fintype_card, card_adjoinRoot_zmod2 hC_irred, hC_deg.1]
  let α₀ : K := AdjoinRoot.root Cpoly
  have hα₀_ne0 : α₀ ≠ 0 := by
    intro h0
    have hev : aeval α₀ Cpoly = 0 := AdjoinRoot.aeval_eq Cpoly ▸ AdjoinRoot.mk_self
    simp only [Cpoly, map_add, map_pow, aeval_X, map_one, h0,
      zero_pow (by omega : d ≠ 0), zero_pow (by omega : s ≠ 0), zero_add] at hev
    exact one_ne_zero hev
  have hα₀_pow : α₀ ^ (2 ^ d - 1) = 1 := by
    rw [← hcardK]
    exact FiniteField.pow_card_sub_one_eq_one α₀ hα₀_ne0
  have h2d_ge2 : 2 ≤ 2 ^ d := by
    calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by decide) hd_pos
  -- Find w with p * w = 1 + (2^d - 1) * t
  have hex_w : ∃ w t : ℕ, p * w = 1 + (2 ^ d - 1) * t := by
    by_cases h2d2 : 2 ^ d - 1 = 1
    · exact ⟨1, p - 1, by rw [h2d2]; omega⟩
    · have hM_gt1 : 1 < 2 ^ d - 1 := by omega
      have htot_pos : 0 < Nat.totient (2 ^ d - 1) := Nat.totient_pos.mpr (by omega)
      let w := p ^ (Nat.totient (2 ^ d - 1) - 1)
      have hpw : p * w ≡ 1 [MOD (2 ^ d - 1)] := by
        have h1 : p * w = p ^ Nat.totient (2 ^ d - 1) := by
          simp only [w]
          conv_rhs => rw [show Nat.totient (2 ^ d - 1) = (Nat.totient (2 ^ d - 1) - 1) + 1 by omega, pow_succ']
        rw [h1]
        exact Nat.ModEq.pow_totient hcop
      have hmod1 : p * w % (2 ^ d - 1) = 1 := Eq.trans hpw (Nat.mod_eq_of_lt hM_gt1)
      have hdiv := Nat.div_add_mod (p * w) (2 ^ d - 1)
      exact ⟨w, p * w / (2 ^ d - 1), by omega⟩
  obtain ⟨w, t, hpw⟩ := hex_w
  let γ₀ : K := α₀ ^ w
  have hγ₀_p : γ₀ ^ p = α₀ := by
    calc γ₀ ^ p = α₀ ^ (p * w) := by simp only [γ₀, ← pow_mul, mul_comm w p]
      _ = α₀ ^ (1 + (2 ^ d - 1) * t) := by rw [hpw]
      _ = α₀ * (α₀ ^ (2 ^ d - 1)) ^ t := by rw [pow_add, pow_one, pow_mul]
      _ = α₀ := by rw [hα₀_pow, one_pow, mul_one]
  -- Pick representative polynomial G of degree < d for γ₀
  obtain ⟨G0, hG0⟩ := AdjoinRoot.mk_surjective γ₀
  let G : Polynomial (ZMod 2) := G0 %ₘ Cpoly
  have hG_mk : AdjoinRoot.mk Cpoly G = γ₀ := by
    have hdiv := Polynomial.modByMonic_add_div G0 Cpoly
    have hmk := congrArg (AdjoinRoot.mk Cpoly) hdiv
    rw [map_add, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero, hG0] at hmk
    exact hmk
  have hG_deg_lt : G = 0 ∨ G.natDegree < d := by
    by_cases hG_zero : G = 0
    · exact Or.inl hG_zero
    · right
      have hlt := Polynomial.degree_modByMonic_lt G0 hC_deg.2
      rwa [Polynomial.degree_eq_natDegree hG_zero, Polynomial.degree_eq_natDegree hC_deg.2.ne_zero,
        hC_deg.1, Nat.cast_lt] at hlt
  have hC_dvd_Gp : Cpoly ∣ G ^ p + X := by
    have hmk0 : AdjoinRoot.mk Cpoly (G ^ p + X) = 0 := by
      rw [map_add, map_pow, hG_mk, hγ₀_p]
      exact zmod2_add_self α₀
    exact AdjoinRoot.mk_eq_zero.mp hmk0
  -- Work in L = AdjoinRoot B: let y = root B, γ = aeval (y^p) G, then γ^p = y^p!
  have : Fact (Irreducible (PolyB e r k m)) := ⟨hB⟩
  let L := AdjoinRoot (PolyB e r k m)
  let y : L := AdjoinRoot.root (PolyB e r k m)
  have hyB : aeval y (PolyB e r k m) = 0 := AdjoinRoot.aeval_eq (PolyB e r k m) ▸ AdjoinRoot.mk_self
  have hyC : aeval (y ^ p) Cpoly = 0 := by
    have h1 := congrArg (aeval y) hB_comp
    rw [hyB, aeval_comp] at h1
    simpa using h1.symm
  let γ : L := aeval (y ^ p) G
  have hγ_p : γ ^ p = y ^ p := by
    obtain ⟨U, hU⟩ := hC_dvd_Gp
    have hev := congrArg (aeval (y ^ p)) hU
    rw [map_add, map_pow, aeval_X, map_mul, hyC, zero_mul] at hev
    exact zmod2_eq_of_add_eq_zero hev
  -- Define Q j = (G ^ (p - 1 - j)) %ₘ Cpoly (deg < d) and R = ∑ j < p, (Q j).comp (X^p) * X^j
  let Q : ℕ → Polynomial (ZMod 2) := fun j => (G ^ (p - 1 - j)) %ₘ Cpoly
  let R : Polynomial (ZMod 2) := ∑ j ∈ Finset.range p, (Q j).comp (X ^ p) * X ^ j
  have hQ_eval : ∀ j : ℕ, aeval (y ^ p) (Q j) = γ ^ (p - 1 - j) := by
    intro j
    have hdiv := Polynomial.modByMonic_add_div (G ^ (p - 1 - j)) Cpoly
    have hev := congrArg (aeval (y ^ p)) hdiv
    rw [map_add, map_mul, hyC, zero_mul, add_zero] at hev
    simpa [γ, Q, map_pow] using hev
  have hR_eval : aeval y R = ∑ j ∈ Finset.range p, γ ^ (p - 1 - j) * y ^ j := by
    simp only [R, map_sum, map_mul, map_pow, aeval_comp, aeval_X]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hQ_eval j]
  have hprod_zero : (y - γ) * aeval y R = 0 := by
    rw [hR_eval]
    have hgeom : (y - γ) * ∑ j ∈ Finset.range p, γ ^ (p - 1 - j) * y ^ j = y ^ p - γ ^ p := by
      have hcomm : ∑ j ∈ Finset.range p, γ ^ (p - 1 - j) * y ^ j =
          ∑ j ∈ Finset.range p, y ^ j * γ ^ (p - 1 - j) :=
        Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hcomm]
      exact (geom_sum₂_mul y γ p).symm ▸ by ring
    rw [hgeom, hγ_p, sub_self]
  rcases mul_eq_zero.mp hprod_zero with hlin | hR0
  · -- Case y = γ: then aeval y (G.comp (X^p) + X) = 0 with 0 < deg < m!
    let S : Polynomial (ZMod 2) := G.comp (X ^ p) + X
    have hS_eval : aeval y S = 0 := by
      have hyγ : y = γ := sub_eq_zero.mp hlin
      simp only [S, map_add, aeval_comp, map_pow, aeval_X]
      rw [show aeval (y ^ p) G = γ from rfl, hyγ]
      exact zmod2_add_self γ
    have hS_coeff1 : S.coeff 1 = 1 := by
      have hcomp_coeff : (G.comp (X ^ p)).coeff 1 = 0 := by
        rw [coeff_comp_X_pow G hp.pos 1, if_neg hp.not_dvd_one]
      simp [S, hcomp_coeff]
    have hS_ne0 : S ≠ 0 := fun h0 => by rw [h0, coeff_zero] at hS_coeff1; exact zero_ne_one hS_coeff1
    have hS_deg : S.natDegree < m := by
      have hGcomp_deg : (G.comp (X ^ p)).natDegree < m := by
        rcases hG_deg_lt with hG0 | hGlt
        · rw [hG0, zero_comp, natDegree_zero]; omega
        · rw [natDegree_comp, natDegree_X_pow]
          have h1 : G.natDegree * p ≤ (d - 1) * p := Nat.mul_le_mul_right p (by omega)
          have h2 : (d - 1) * p < d * p := Nat.mul_lt_mul_of_pos_right (by omega) hp.pos
          have h3 : d * p = m := by rw [hd_eq, mul_comm]
          omega
      refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
      rw [natDegree_X]
      have hm_gt1 : 1 < m := by
        rw [hd_eq]
        exact lt_of_lt_of_le (by omega : 1 < p) (Nat.le_mul_of_pos_right p hd_pos)
      omega
    have hBdvdS : PolyB e r k m ∣ S := poly_dvd_of_aeval_zero hB hyB hS_eval
    have hle := Polynomial.natDegree_le_of_dvd hBdvdS hS_ne0
    omega
  · -- Case aeval y R = 0: coeff (p - 1) of R is 1 (so R ≠ 0), and deg R < p * d = m!
    have hR_coeff : R.coeff (p - 1) = 1 := by
      simp only [R, finsetSum_coeff]
      rw [Finset.sum_eq_single (p - 1)]
      · have hQp1 : Q (p - 1) = 1 := by
          simp only [Q, Nat.sub_self, pow_zero]
          exact Polynomial.modByMonic_eq_self_iff hC_deg.2 |>.mpr (by
            rw [Polynomial.degree_one, Polynomial.degree_eq_natDegree hC_deg.2.ne_zero, hC_deg.1]
            exact_mod_cast (by omega : 0 < d))
        rw [hQp1, one_comp, one_mul, coeff_X_pow]
        simp
      · intro j hj hjne
        rw [Finset.mem_range] at hj
        rw [coeff_mul_X_pow', if_pos (by omega : j ≤ p - 1), coeff_comp_X_pow (Q j) hp.pos]
        have hndvd : ¬ p ∣ p - 1 - j := by
          intro hdvd
          have hle := Nat.le_of_dvd (by omega) hdvd
          omega
        rw [if_neg hndvd]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    have hR_ne0 : R ≠ 0 := fun h0 => by rw [h0, coeff_zero] at hR_coeff; exact zero_ne_one hR_coeff
    have hR_deg : R.natDegree < m := by
      have hterm_lt : ∀ j ∈ Finset.range p, ((Q j).comp (X ^ p) * X ^ j).natDegree < m := by
        intro j hj
        rw [Finset.mem_range] at hj
        by_cases hQj0 : Q j = 0
        · rw [hQj0, zero_comp, zero_mul, natDegree_zero]; omega
        · have hQlt : (Q j).natDegree < d := by
            have := Polynomial.degree_modByMonic_lt (G ^ (p - 1 - j)) hC_deg.2
            rwa [Polynomial.degree_eq_natDegree hQj0, Polynomial.degree_eq_natDegree hC_deg.2.ne_zero,
              hC_deg.1, Nat.cast_lt] at this
          have h1 : (Q j).natDegree * p ≤ (d - 1) * p := Nat.mul_le_mul_right p (by omega)
          have h2 : (d - 1) * p + p = d * p := by
            rw [← add_one_mul, show d - 1 + 1 = d by omega]
          have h3 : d * p = m := by rw [hd_eq, mul_comm]
          have h4 : ((Q j).comp (X ^ p) * X ^ j).natDegree ≤ (Q j).natDegree * p + j := by
            calc ((Q j).comp (X ^ p) * X ^ j).natDegree
                ≤ ((Q j).comp (X ^ p)).natDegree + (X ^ j).natDegree := natDegree_mul_le
              _ = (Q j).natDegree * p + j := by rw [natDegree_comp, natDegree_X_pow, natDegree_X_pow]
          omega
      have hR_coeff_hi : ∀ t : ℕ, m ≤ t → R.coeff t = 0 := by
        intro t ht
        simp only [R, finsetSum_coeff]
        refine Finset.sum_eq_zero fun j hj => ?_
        exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hterm_lt j hj) ht)
      by_contra hge
      have hlc : R.coeff R.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hR_ne0
      exact hlc (hR_coeff_hi R.natDegree (by omega))
    have hBdvdR : PolyB e r k m ∣ R := poly_dvd_of_aeval_zero hB hyB hR0
    have hle := Polynomial.natDegree_le_of_dvd hBdvdR hR_ne0
    omega

private lemma part_ii_converse {e r k m : ℕ} (hr : Odd r) (hk : Odd k) (hm : 2 ^ e * r * k < m)
    (hgcd : 1 < Nat.gcd m r) : ¬ Irreducible (PolyA e r k m) := by
  have ⟨hdegA, hmonA⟩ := natDegree_polyA hr hk hm
  set g := Nat.gcd m r
  have hgm : g ∣ m := Nat.gcd_dvd_left m r
  have hgr : g ∣ r := Nat.gcd_dvd_right m r
  obtain ⟨m', hm'⟩ := hgm
  obtain ⟨r', hr'⟩ := hgr
  set q' := 2 ^ e * r'
  have hq_eq : 2 ^ e * r = g * q' := by simp only [q', hr']; ring
  let u : Polynomial (ZMod 2) := X ^ m'
  let v : Polynomial (ZMod 2) := (X ^ k + 1) ^ q'
  have hA_eq : PolyA e r k m = u ^ g + v ^ g := by
    unfold PolyA
    simp only [u, v, ← pow_mul, mul_comm m' g, mul_comm q' g, ← hm', ← hq_eq]
  have hdvd : u + v ∣ PolyA e r k m := by
    rw [hA_eq, ← zmod2_sub_eq_add u v, ← zmod2_sub_eq_add (u ^ g) (v ^ g)]
    exact sub_dvd_pow_sub_pow u v g
  have hq'_pos : 0 < q' := by
    have hr'_pos : 0 < r' := by
      obtain ⟨t, ht⟩ := hr
      rcases Nat.eq_zero_or_pos r' with rfl | hpos
      · omega
      · exact hpos
    exact Nat.mul_pos (pow_pos (by decide) e) hr'_pos
  have hk_pos : 0 < k := by obtain ⟨t, rfl⟩ := hk; omega
  have hm'_gt : q' * k < m' := by
    have : g * (q' * k) < g * m' := by
      calc g * (q' * k) = 2 ^ e * r * k := by rw [hq_eq]; ring
        _ < m := hm
        _ = g * m' := hm'
    exact Nat.lt_of_mul_lt_mul_left this
  have hdeg_v : v.natDegree < m' := by
    have h1 : (X ^ k + 1 : Polynomial (ZMod 2)).natDegree ≤ k := by
      refine le_trans (natDegree_add_le _ _) ?_; simp
    calc v.natDegree ≤ q' * (X ^ k + 1 : Polynomial (ZMod 2)).natDegree := natDegree_pow_le
      _ ≤ q' * k := Nat.mul_le_mul_left q' h1
      _ < m' := hm'_gt
  have hdeg_uv : (u + v).natDegree = m' := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by rwa [natDegree_X_pow]), natDegree_X_pow]
  have hm'_ge2 : 2 ≤ m' := by nlinarith
  have hm'_lt_m : m' < m := by nlinarith
  obtain ⟨W, hW⟩ := hdvd
  intro hAirred
  rcases hAirred.isUnit_or_isUnit hW with huv | hWu
  · have := Polynomial.natDegree_eq_zero_of_isUnit huv
    omega
  · have hW0 : W ≠ 0 := hWu.ne_zero
    have huv0 : u + v ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg_uv; omega
    have hWdeg := Polynomial.natDegree_eq_zero_of_isUnit hWu
    have hsum : (PolyA e r k m).natDegree = (u + v).natDegree + W.natDegree := by
      rw [hW, natDegree_mul huv0 hW0]
    omega

private lemma general_conjecture :
    ∀ e r k m : ℕ, Odd r → Odd k → 2 ^ e * r * k < m →
      (Irreducible (PolyA e r k m) → Irreducible (PolyB e r k m)) ∧
      (Irreducible (PolyB e r k m) →
        (¬ Irreducible (PolyA e r k m) ↔
          1 < Nat.gcd m r ∧
          (∀ p : ℕ, p.Prime → p ∣ Nat.gcd m (r * k) → p * orderOf (2 : ZMod p) ∣ m) ∧
          (0 < e → Odd m))) := by
  intro e r k m hr hk hm
  refine ⟨part_i hr hk hm, fun hB => ⟨fun hAn => ?_, fun ⟨hgcd, _, _⟩ => part_ii_converse hr hk hm hgcd⟩⟩
  exact ⟨part_ii_a hr hk hm hB hAn, fun p hp hp_dvd => part_ii_b hr hk hm hB hp hp_dvd,
    part_ii_c hr hk hm hB⟩

private theorem prove_main : type_of% @OMA.S_oeis_a344200.main := by
  refine ⟨general_conjecture, fun m hm => ?_⟩
  have hgen := general_conjecture 0 5 3 m (by decide) (by decide) (by simpa using hm)
  have hord5 : orderOf (2 : ZMod 5) = 4 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 4) (by decide)
    intro q hq hqdvd
    have hq2 : q = 2 := by
      have h1 : q ∣ 2 ^ 2 := hqdvd
      exact (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 2)).mp (hq.dvd_of_dvd_pow h1)
    subst hq2; decide
  constructor
  · intro ⟨hB, hAn⟩
    refine ⟨hB, ?_⟩
    obtain ⟨hgcd, hord, _⟩ := (hgen.2 hB).mp hAn
    have h5m : 5 ∣ m := by
      have hdvd5 : Nat.gcd m 5 ∣ 5 := Nat.gcd_dvd_right m 5
      have hge : Nat.gcd m 5 = 5 := by
        rcases (by decide : Nat.Prime 5).eq_one_or_self_of_dvd _ hdvd5 with h1 | h5
        · omega
        · exact h5
      rw [← hge]; exact Nat.gcd_dvd_left m 5
    have h5g : 5 ∣ Nat.gcd m (5 * 3) := Nat.dvd_gcd h5m (by decide)
    have h20 := hord 5 (by decide) h5g
    rwa [hord5] at h20
  · intro ⟨hB, h20⟩
    refine ⟨hB, ?_⟩
    have h5m : 5 ∣ m := dvd_trans (by decide : 5 ∣ 20) h20
    have hgcd : 1 < Nat.gcd m 5 := by
      have : 5 ∣ Nat.gcd m 5 := Nat.dvd_gcd h5m (dvd_refl 5)
      have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right m (by decide)) this
      omega
    exact part_ii_converse (by decide) (by decide) (by simpa using hm) hgcd

end OMA.P_oeis_a344200

theorem OMA.solution : type_of% @OMA.S_oeis_a344200.main :=
  OMA.P_oeis_a344200.prove_main
