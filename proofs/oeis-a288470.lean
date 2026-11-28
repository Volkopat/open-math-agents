import OMAStatements.S_oeis_a288470
import Mathlib

/-!
Peter Bala formulated the conjecture in OEIS A288470. Rohan Bajaj previously
proved it using binomial valuations and adjacent Jacobsthal scaling
(https://github.com/rbajaj5/a183068-supercongruence/blob/main/related-results/A288470OddPrimeTower.md).
This formalization pairs the unit factors at `i` and `j - i` to obtain the
quadratic scaling estimate needed for the same split of the sum.
-/

namespace A288470

open Finset
open OMA.S_oeis_a288470 (a)

private def unitIndices (p j : ℕ) : Finset ℕ := (Icc 1 j).filter (fun i => ¬ p ∣ i)

private def unitDenominator (p j : ℕ) : ℕ := ∏ i ∈ unitIndices p j, i

private def unitNumerator (p d j : ℕ) : ℕ := ∏ i ∈ unitIndices p j, (d + i)

private theorem unit_denominator_not_dvd {p j : ℕ} (hp : p.Prime) : ¬ p ∣ unitDenominator p j := by
  exact hp.prime.not_dvd_finsetProd fun i hi => (mem_filter.mp hi).2

private theorem split_scaled_product {p j : ℕ} (hp : 0 < p) (f : ℕ → ℕ) :
    (∏ i ∈ Icc 1 (p * j), f i) = (∏ k ∈ Icc 1 j, f (p * k)) * ∏ i ∈ unitIndices p (p * j), f i := by
  have hindices : (Icc 1 (p * j)).filter (fun i => p ∣ i) = (Icc 1 j).image (fun k => p * k) := by
    ext i
    rw [mem_filter, mem_image]
    constructor
    · rintro ⟨hi, k, rfl⟩
      obtain ⟨hpos, hle⟩ := mem_Icc.mp hi
      have hk : 0 < k := by
        by_contra! he
        have hk' : k = 0 := by omega
        simp [hk'] at hpos
      exact ⟨k, mem_Icc.mpr ⟨hk, (Nat.mul_le_mul_left_iff hp).mp hle⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨hpos, hle⟩ := mem_Icc.mp hk
      exact ⟨mem_Icc.mpr ⟨Nat.mul_pos hp hpos, Nat.mul_le_mul_left p hle⟩, dvd_mul_right _ _⟩
  rw [← prod_filter_mul_prod_filter_not _ (fun i => p ∣ i), hindices,
    prod_image (fun _ _ _ _ h => Nat.mul_left_cancel hp h)]
  rfl

private theorem choose_product (d j : ℕ) :
    (∏ i ∈ Icc 1 j, i) * (d + j).choose j = ∏ i ∈ Icc 1 j, (d + i) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose d j
  rw [Nat.ascFactorial_eq_prod_range, Nat.factorial_eq_prod_range_add_one] at h
  simpa [← Ico_add_one_right_eq_Icc, prod_Ico_eq_prod_range, add_assoc, add_comm 1] using h.symm

/-- Cancel the factors at multiples of `p` in the two binomial products. -/
private theorem choose_cross_product {p : ℕ} (hp : 0 < p) (d j : ℕ) :
    (p * (d + j)).choose (p * j) * unitDenominator p (p * j) =
      (d + j).choose j * unitNumerator p (p * d) (p * j) := by
  let C := (p * (d + j)).choose (p * j)
  let C' := (d + j).choose j
  let D := unitDenominator p (p * j)
  let U := unitNumerator p (p * d) (p * j)
  let E := ∏ i ∈ Icc 1 j, i
  let G := ∏ i ∈ Icc 1 j, (d + i)
  have hcard : (Icc (1 : ℕ) j).card = j := by simp [Nat.card_Icc]
  have hden : (∏ i ∈ Icc 1 (p * j), i) = (p ^ j * E) * D := by
    rw [split_scaled_product hp, prod_mul_distrib, prod_const, hcard]
    rfl
  have hnum : (∏ i ∈ Icc 1 (p * j), (p * d + i)) = (p ^ j * G) * U := by
    rw [split_scaled_product hp]
    simp_rw [← mul_add]
    rw [prod_mul_distrib, prod_const, hcard]
    rfl
  have hbig : (p ^ j * E) * D * C = (p ^ j * G) * U := by
    have hh := choose_product (p * d) (p * j)
    rwa [← mul_add, hden, hnum] at hh
  have hsmall : E * C' = G := choose_product d j
  have hpos : 0 < p ^ j * E := Nat.mul_pos (pow_pos hp _) (prod_pos (fun _ hi => (mem_Icc.mp hi).1))
  change C * D = C' * U
  apply Nat.mul_left_cancel hpos
  calc
    _ = (p ^ j * E) * D * C := by ac_rfl
    _ = (p ^ j * G) * U := hbig
    _ = _ := by rw [← hsmall]; ac_rfl

private theorem unit_indices_reflect {p j i : ℕ} (hj : p ∣ j) (hi : i ∈ unitIndices p j) :
    j - i ∈ unitIndices p j := by
  obtain ⟨his, hin⟩ := mem_filter.mp hi
  obtain ⟨hip, hile⟩ := mem_Icc.mp his
  have hinj : i ≠ j := fun h => hin (h.symm ▸ hj)
  exact mem_filter.mpr ⟨mem_Icc.mpr (by omega), fun h => hin (by
    simpa only [show j - (j - i) = i by omega] using Nat.dvd_sub hj h)⟩

private theorem unit_product_reflect {p j : ℕ} (hj : p ∣ j) (f : ℕ → ℕ) :
    (∏ i ∈ unitIndices p j, f (j - i)) = ∏ i ∈ unitIndices p j, f i := by
  apply prod_bij' (fun i _ => j - i) (fun i _ => j - i)
    (fun _ hi => unit_indices_reflect hj hi) (fun _ hi => unit_indices_reflect hj hi)
  · intro i hi
    have := (mem_Icc.mp (mem_filter.mp hi).1).2
    omega
  · intro i hi
    have := (mem_Icc.mp (mem_filter.mp hi).1).2
    omega
  · intro i hi
    rfl

/-- A unit numerator product is congruent to the unit denominator product. -/
private theorem unit_product_congruence {p d j e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 0 < e)
    (hd : p ^ e ∣ d) (hj : p ^ e ∣ j) :
    unitNumerator p d j ≡ unitDenominator p j [MOD p ^ (2 * e)] := by
  let U := unitNumerator p d j
  let D := unitDenominator p j
  let m := p ^ (2 * e)
  have hpDe : p ∣ d := (dvd_pow_self p he.ne').trans hd
  have hpJe : p ∣ j := (dvd_pow_self p he.ne').trans hj
  have hpair : ∀ i ∈ unitIndices p j,
      (d + i) * (d + (j - i)) ≡ i * (j - i) [MOD m] := by
    intro i hi
    have hle := (mem_Icc.mp (mem_filter.mp hi).1).2
    have hmul : m ∣ d * (d + j) := by
      dsimp only [m]
      rw [two_mul, pow_add]
      exact mul_dvd_mul hd (dvd_add hd hj)
    have hfactor : (d + i) * (d + (j - i)) = i * (j - i) + d * (d + j) := by
      calc
        _ = i * (j - i) + d * (d + (i + (j - i))) := by ring
        _ = _ := by rw [Nat.add_sub_of_le hle]
    rw [hfactor]
    exact Nat.add_modEq_left_iff.mpr hmul
  have hsquared : U * U ≡ D * D [MOD m] := by
    have h := Nat.ModEq.prod hpair
    have href := unit_product_reflect hpJe (fun i : ℕ => i)
    rw [prod_mul_distrib, prod_mul_distrib,
      unit_product_reflect hpJe (fun i => d + i), href] at h
    exact h
  have hbase : U ≡ D [MOD p] := by
    change (∏ i ∈ unitIndices p j, (d + i)) ≡ ∏ i ∈ unitIndices p j, i [MOD p]
    apply Nat.ModEq.prod
    intro i _
    simpa only [zero_add] using (Nat.modEq_zero_iff_dvd.mpr hpDe).add_right i
  have htwo : ¬ p ∣ 2 := fun h => hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hnot : ¬ p ∣ U + D := by
    intro h
    have heq : U + D ≡ 2 * D [MOD p] := by rw [two_mul]; exact hbase.add_right D
    have hmul := (heq.dvd_iff dvd_rfl).mp h
    exact unit_denominator_not_dvd hp ((hp.dvd_mul.mp hmul).resolve_left htwo)
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow (d := 2 * e) hp (by omega)).mpr hnot
  rw [← ZMod.natCast_eq_natCast_iff] at hsquared ⊢
  change (U : ZMod m) = (D : ZMod m)
  apply hu.isRegular.left
  change ((U + D : ℕ) : ZMod m) * (U : ZMod m) = ((U + D : ℕ) : ZMod m) * (D : ZMod m)
  simp only [Nat.cast_add, Nat.cast_mul] at hsquared ⊢
  linear_combination hsquared

private theorem choose_divisibility {p r N j : ℕ} (hp : p.Prime) (hN : p ^ r ∣ N) (hj : 0 < j) :
    p ^ (r - j.factorization p) ∣ N.choose j := by
  by_cases hn : N = 0
  · simp [hn, Nat.choose_eq_zero_of_lt hj]
  by_cases hsmall : r ≤ j.factorization p
  · simp [Nat.sub_eq_zero_of_le hsmall]
  let t := ordProj[p] j
  let u := ordCompl[p] j
  let q := p ^ (r - j.factorization p)
  have htu : t * u = j := Nat.ordProj_mul_ordCompl_eq_self j p
  have htq : t * q = p ^ r := by
    dsimp [t, q]
    rw [← pow_add, Nat.add_sub_of_le (by omega)]
  have hz := Nat.add_one_mul_choose_eq (N - 1) (j - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ N), Nat.sub_add_cancel hj] at hz
  have hmul : t * q ∣ t * (u * N.choose j) := by
    rw [htq, ← mul_assoc, htu, mul_comm j, ← hz]
    exact dvd_mul_of_dvd_left hN _
  have hDiv := (Nat.mul_dvd_mul_iff_left (Nat.ordProj_pos j p)).mp hmul
  have hCoprime := (Nat.coprime_ordCompl hp hj.ne').pow_left (r - j.factorization p)
  exact (hCoprime.dvd_mul_left).mp hDiv

private def summand (N j : ℕ) : ℕ := N.choose j * (2 * N).choose (2 * j)

private theorem summand_divisibility {p r N j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : p ^ r ∣ N) (hj : 0 < j) : p ^ (2 * (r - j.factorization p)) ∣ summand N j := by
  have hn2 : ¬p ∣ 2 := fun h => hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hexp : (2 * j).factorization p = j.factorization p := by
    rw [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) hj.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hn2, zero_add]
  have htwo := choose_divisibility hp (dvd_mul_of_dvd_right hN 2) (Nat.mul_pos (by decide : 0 < 2) hj)
  rw [hexp] at htwo
  simpa only [summand, two_mul (r - j.factorization p), pow_add] using
    mul_dvd_mul (choose_divisibility hp hN hj) htwo

private theorem summand_cross_product {p : ℕ} (hp : 0 < p) (d j : ℕ) :
    summand (p * (d + j)) (p * j) * (unitDenominator p (p * j) * unitDenominator p (p * (2 * j))) =
      summand (d + j) j * (unitNumerator p (p * d) (p * j) * unitNumerator p (p * (2 * d)) (p * (2 * j))) := by
  have h₁ := choose_cross_product hp d j
  have h₂ := choose_cross_product hp (2 * d) (2 * j)
  simp_rw [← mul_add] at h₂
  simp only [summand, mul_left_comm 2 p]
  rw [mul_mul_mul_comm, h₁, h₂, mul_mul_mul_comm]

private theorem cancel_unit_right {p e C D U : ℕ} (hp : p.Prime) (he : 0 < e) (hU : ¬ p ∣ U)
    (h : C * U ≡ D * U [MOD p ^ e]) : C ≡ D [MOD p ^ e] := by
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow hp he).mpr hU
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_mul] at h
  rw [← ZMod.natCast_eq_natCast_iff]
  exact hu.isRegular.right h

/-- Transfer the summand at index `p * j` to index `j` at the preceding scale. -/
private theorem summand_rescale {p A j r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hA : p ^ r ∣ A) (hj : j ≤ A) :
    summand (p * A) (p * j) ≡ summand A j [MOD p ^ (2 * (r + 1))] := by
  by_cases hj0 : j = 0
  · simp [hj0, summand, Nat.ModEq.refl]
  let t := min r (j.factorization p)
  let e := t + 1
  let d := A - j
  let D := unitDenominator p (p * j) * unitDenominator p (p * (2 * j))
  let U := unitNumerator p (p * d) (p * j) * unitNumerator p (p * (2 * d)) (p * (2 * j))
  have htA : p ^ t ∣ A := (pow_dvd_pow p (min_le_left _ _)).trans hA
  have htj : p ^ t ∣ j := (pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd j p)
  have htd : p ^ t ∣ d := Nat.dvd_sub htA htj
  have hpj : p ^ e ∣ p * j := by
    rw [show e = t + 1 by rfl, pow_succ']
    exact Nat.mul_dvd_mul_left p htj
  have hpd : p ^ e ∣ p * d := by
    rw [show e = t + 1 by rfl, pow_succ']
    exact Nat.mul_dvd_mul_left p htd
  have hpj2 : p ^ e ∣ p * (2 * j) := by rw [mul_left_comm p 2 j]; exact dvd_mul_of_dvd_right hpj 2
  have hpd2 : p ^ e ∣ p * (2 * d) := by rw [mul_left_comm p 2 d]; exact dvd_mul_of_dvd_right hpd 2
  have he : 0 < e := Nat.succ_pos t
  have hcong : U ≡ D [MOD p ^ (2 * e)] :=
    (unit_product_congruence hp hp2 he hpd hpj).mul (unit_product_congruence hp hp2 he hpd2 hpj2)
  obtain ⟨v, hv⟩ := summand_divisibility hp hp2 hA (Nat.pos_of_ne_zero hj0)
  have hexp : 2 * (r - j.factorization p) + 2 * e = 2 * (r + 1) := by
    dsimp [e, t]
    omega
  have hlarge : summand A j * U ≡ summand A j * D [MOD p ^ (2 * (r + 1))] := by
    rw [hv, ← hexp, pow_add, mul_assoc, mul_assoc]
    exact (hcong.mul_left v).mul_left' _
  have hcross := summand_cross_product hp.pos d j
  change summand (p * (d + j)) (p * j) * D = summand (d + j) j * U at hcross
  rw [show d + j = A from Nat.sub_add_cancel hj] at hcross
  rw [← hcross] at hlarge
  apply cancel_unit_right hp (by omega) _ hlarge
  exact fun h => (hp.dvd_mul.mp h).elim (unit_denominator_not_dvd hp) (unit_denominator_not_dvd hp)

theorem supercongruence (p n k : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (_hn : 0 < n) (hk : 0 < k) :
    a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [MOD p ^ (2 * k)] := by
  let r := k - 1
  let A := n * p ^ r
  have hkr : r + 1 = k := Nat.sub_add_cancel hk
  have hA : p ^ r ∣ A := dvd_mul_left _ _
  have hTop : n * p ^ k = p * A := by rw [← hkr, pow_succ']; dsimp only [A]; ac_rfl
  have hTopDvd : p ^ k ∣ p * A := by rw [← hTop]; exact dvd_mul_left _ _
  rw [hTop]
  change (∑ j ∈ range (p * A + 1), summand (p * A) j) ≡
    ∑ j ∈ range (A + 1), summand A j [MOD p ^ (2 * k)]
  rw [← sum_filter_add_sum_filter_not (range (p * A + 1)) (fun j => p ∣ j)]
  have hzero : (∑ j ∈ (range (p * A + 1)).filter (fun j => ¬ p ∣ j), summand (p * A) j) ≡
      0 [MOD p ^ (2 * k)] := by
    apply Nat.ModEq.sum_zero
    intro j hj
    have hnd := (mem_filter.mp hj).2
    have hjpos : 0 < j := Nat.pos_of_ne_zero (fun hz => hnd (hz ▸ dvd_zero p))
    apply Nat.modEq_zero_iff_dvd.mpr
    simpa only [Nat.factorization_eq_zero_of_not_dvd hnd, Nat.sub_zero] using
      summand_divisibility hp hp2 hTopDvd hjpos
  have hindices : (range (p * A + 1)).filter (fun j => p ∣ j) = (range (A + 1)).image (fun j => p * j) := by
    ext j
    rw [mem_filter, mem_image]
    constructor
    · rintro ⟨hj, x, rfl⟩
      exact ⟨x, mem_range.mpr (Nat.lt_succ_iff.mpr ((Nat.mul_le_mul_left_iff hp.pos).mp
        (Nat.lt_succ_iff.mp (mem_range.mp hj)))), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.mul_le_mul_left p (Nat.lt_succ_iff.mp
        (mem_range.mp hx)))), dvd_mul_right p x⟩
  have hdiv : (∑ j ∈ (range (p * A + 1)).filter (fun j => p ∣ j), summand (p * A) j) ≡
      ∑ j ∈ range (A + 1), summand A j [MOD p ^ (2 * k)] := by
    rw [hindices, sum_image (fun _ _ _ _ h => Nat.mul_left_cancel hp.pos h)]
    apply Nat.ModEq.sum
    intro j hj
    simpa only [hkr] using summand_rescale hp hp2 hA (Nat.lt_succ_iff.mp (mem_range.mp hj))
  simpa only [add_zero] using hdiv.add hzero

end A288470

theorem OMA.solution : type_of% @OMA.S_oeis_a288470.main := by
  intro p n k hp h5 hn hk
  exact A288470.supercongruence p n k hp (by omega) hn hk
