import OMAStatements.S_oeis_a061002
import Mathlib

/-!
The exact Wolstenholme quotient in A061002. The common denominator proof pairs
`k` and `p-k`, then applies the vanishing inverse-square sum modulo `p`.
-/

section HarmonicCrossSection

/- The inverse-square permutation and the square sum below are reused from
@ivillar's merged proof for A007406, https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6590. -/

open Finset

namespace OMA.A061002

private lemma sum_sq_six (m : ℕ) : 6 * ∑ k ∈ Icc 1 m, k ^ 2 = m * (m + 1) * (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

private lemma natCast_ne_zero_of_mem {p : ℕ} {k : ℕ} (hk : k ∈ Icc 1 (p - 1)) :
    (k : ZMod p) ≠ 0 := by
  rw [mem_Icc] at hk
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  omega

private lemma inv_sq_sum (p : ℕ) [hp : Fact p.Prime] :
    ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ 2 = ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)) ^ 2 := by
  have hp1 := hp.out.one_lt
  have hmaps : ∀ k ∈ Icc 1 (p - 1), ((k : ZMod p)⁻¹).val ∈ Icc 1 (p - 1) := by
    intro k hk
    have h0 := natCast_ne_zero_of_mem hk
    rw [mem_Icc]
    constructor
    · rw [Nat.one_le_iff_ne_zero, Ne, ZMod.val_eq_zero]
      exact inv_ne_zero h0
    · have := ZMod.val_lt ((k : ZMod p)⁻¹)
      omega
  have hinv : ∀ k ∈ Icc 1 (p - 1), ((((k : ZMod p)⁻¹).val : ZMod p)⁻¹).val = k := by
    intro k hk
    rw [ZMod.natCast_zmod_val, inv_inv, ZMod.val_natCast, Nat.mod_eq_of_lt]
    rw [mem_Icc] at hk
    omega
  refine Finset.sum_nbij' (fun k : ℕ => ((k : ZMod p)⁻¹).val) (fun k : ℕ => ((k : ZMod p)⁻¹).val)
    hmaps hmaps hinv hinv ?_
  intro k hk
  rw [ZMod.natCast_zmod_val]

private theorem sum_sq_mod_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) [Fact p.Prime] :
    (∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ 2) = 0 := by
  have hp1 : p - 1 + 1 = p := by omega
  have h6mul :=
    congrArg (fun x : ℕ => (x : ZMod p)) (sum_sq_six (p - 1))
  rw [hp1] at h6mul
  push_cast at h6mul
  have h6 : (6 : ZMod p) ≠ 0 := by
    change ((6 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have hd' : p ∣ 2 * 3 := hd
    rcases hp.dvd_mul.mp hd' with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h
      omega
  have hzero : (6 : ZMod p) * ∑ k ∈ Icc 1 (p - 1), (k : ZMod p) ^ 2 = 0 := by
    simpa only [ZMod.natCast_self, mul_zero, zero_mul] using h6mul
  exact (mul_eq_zero.mp hzero).resolve_left h6

/-- The factorial-scaled reflected products sum to zero modulo p. -/
theorem cross_sum_dvd {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    p ∣ ∑ k ∈ Icc 1 (p - 1), ((p - 1).factorial / k) * ((p - 1).factorial / (p - k)) := by
  let : Fact p.Prime := ⟨hp⟩
  let F := (p - 1).factorial
  have hfactor (k : ℕ) (hk : k ∈ Icc 1 (p - 1)) :
      ((F / k : ℕ) : ZMod p) = (F : ZMod p) * (k : ZMod p)⁻¹ := by
    have hdvd : k ∣ F := Nat.dvd_factorial (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
    have hz := natCast_ne_zero_of_mem hk
    apply mul_right_cancel₀ hz
    rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
    rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  have hterm (k : ℕ) (hk : k ∈ Icc 1 (p - 1)) :
      ((F / k : ℕ) : ZMod p) * ((F / (p - k) : ℕ) : ZMod p) =
        - (F : ZMod p) ^ 2 * ((k : ZMod p)⁻¹) ^ 2 := by
    have hkm := mem_Icc.mp hk
    have hkp : p - k ∈ Icc 1 (p - 1) := mem_Icc.mpr ⟨by omega, by omega⟩
    have hcast : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [hfactor k hk, hfactor (p - k) hkp, hcast, inv_neg]
    ring
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simp only [Nat.cast_sum, Nat.cast_mul]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, inv_sq_sum, sum_sq_mod_prime hp h3, mul_zero]

end OMA.A061002

end HarmonicCrossSection

section WolstenholmePairingSection

/-
The common-denominator proof of Wolstenholme's congruence.
Reflecting k to p-k is also used by @Genbox in the project's merged proof of
the harmonic characterization of Wolstenholme primes.
-/

namespace OMA.A061002Wolstenholme

open Finset
open OMA.S_oeis_a061002

private theorem reflect_harmonic_numerator (p F : ℕ) (hp : 0 < p) :
    ∑ k ∈ Icc 1 (p - 1), F / (p - k) = ∑ k ∈ Icc 1 (p - 1), F / k := by
  have hI : Icc 1 (p - 1) = Ico 1 p := by ext k; simp only [mem_Icc, mem_Ico]; omega
  rw [hI]
  simpa only [show p + 1 - p = 1 by omega, show p + 1 - 1 = p by omega] using
    sum_Ico_reflect (fun k => F / k) 1 (m := p) (n := p) (by omega)

private theorem paired_common_denominator (p : ℕ) (hp : 0 < p) :
    let F := (p - 1).factorial
    let R := ∑ k ∈ Icc 1 (p - 1), F / k
    2 * R * F = p * ∑ k ∈ Icc 1 (p - 1), (F / k) * (F / (p - k)) := by
  dsimp only
  let F := (p - 1).factorial
  let S := Icc 1 (p - 1)
  let R := ∑ k ∈ S, F / k
  have hkF (k : ℕ) (hk : k ∈ S) : F / k * k = F :=
    Nat.div_mul_cancel (Nat.dvd_factorial (by have h := mem_Icc.mp hk; omega) (mem_Icc.mp hk).2)
  have hPair (k : ℕ) (hk : k ∈ S) :
      (F / k + F / (p - k)) * F = p * ((F / k) * (F / (p - k))) := by
    have h := mem_Icc.mp hk
    have hk' : p - k ∈ S := mem_Icc.mpr ⟨by omega, by omega⟩
    calc
      _ = (F / k) * ((F / (p - k)) * (p - k)) + (F / (p - k)) * ((F / k) * k) := by
        rw [hkF (p-k) hk', hkF k hk, add_mul]
      _ = (k + (p - k)) * ((F / k) * (F / (p - k))) := by ring
      _ = _ := by rw [Nat.add_sub_of_le (by omega : k ≤ p)]
  calc
    2 * R * F = ∑ k ∈ S, (F / k + F / (p - k)) * F := by
      rw [← sum_mul, sum_add_distrib, reflect_harmonic_numerator p F hp]
      change 2 * R * F = (R + R) * F
      ring
    _ = ∑ k ∈ S, p * ((F / k) * (F / (p - k))) := sum_congr rfl hPair
    _ = p * ∑ k ∈ S, (F / k) * (F / (p - k)) := (mul_sum _ _ _).symm

/-- The mod-p cross-product congruence implies the exact p² numerator
divisibility, and p does not divide the reduced denominator. -/
theorem harmonic_num_dvd_and_den_of_cross {p : ℕ} (hp : p.Prime) (h3 : 3 < p)
    (hCross : p ∣ ∑ k ∈ Icc 1 (p - 1), ((p - 1).factorial / k) * ((p - 1).factorial / (p - k))) :
    (p : ℤ)^2 ∣ (H (p - 1)).num ∧ ¬ p ∣ (H (p - 1)).den := by
  let F := (p - 1).factorial
  let R := ∑ k ∈ Icc 1 (p - 1), F / k
  let q := H (p - 1)
  have hFcop : p.Coprime F := hp.coprime_iff_not_dvd.mpr
    (fun h => by have hh := (hp.dvd_factorial.mp h); omega)
  have hTwo : p.Coprime 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have hC : (p^2).Coprime (2*F) := (hTwo.mul_right hFcop).pow_left 2
  obtain ⟨m, hm⟩ := hCross
  have hp2 : p^2 ∣ 2 * R * F := by
    refine ⟨m, ?_⟩
    have h := paired_common_denominator p hp.pos
    dsimp only at h
    rw [hm] at h
    exact h.trans (by ring)
  have hRdiv : p^2 ∣ R := hC.dvd_of_dvd_mul_right
    (show p^2 ∣ R * (2 * F) from (show 2 * R * F = R * (2 * F) by ring) ▸ hp2)
  have hf0 : (F : ℚ) ≠ 0 := by positivity
  have hq : q = (R : ℚ) / (F : ℚ) := by
    change (∑ k ∈ Icc 1 (p - 1), (1 : ℚ) / (k : ℚ)) = _
    dsimp only [R]
    rw [Nat.cast_sum, sum_div]
    apply sum_congr rfl
    intro k hk
    have h := mem_Icc.mp hk
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hkF : k ∣ F := Nat.dvd_factorial (by omega) h.2
    rw [Nat.cast_div hkF hk0]
    field_simp [hk0, hf0]
  have hKey : q.num * (F : ℤ) = (R : ℤ) * (q.den : ℤ) := by
    have hmul := (eq_div_iff hf0).mp hq
    have h : (q.num : ℚ) * (F : ℚ) = (R : ℚ) * (q.den : ℚ) := by
      rw [← Rat.mul_den_eq_num q, mul_right_comm, hmul]
    exact_mod_cast h
  have hcopZ : IsCoprime (p : ℤ) (F : ℤ) := Nat.isCoprime_iff_coprime.mpr hFcop
  constructor
  · apply hcopZ.pow_left.dvd_of_dvd_mul_right
    rw [hKey]
    exact dvd_mul_of_dvd_left (by exact_mod_cast hRdiv) _
  · intro hpden
    have hdenZ : (q.den : ℤ) ∣ (F : ℤ) := by
      rw [hq]
      simpa only [Rat.divInt_eq_div, Int.cast_natCast] using Rat.den_dvd (R : ℤ) (F : ℤ)
    have hpF : p ∣ F := Int.natCast_dvd_natCast.mp
      ((Int.natCast_dvd_natCast.mpr hpden).trans hdenZ)
    exact (hp.coprime_iff_not_dvd.mp hFcop) hpF

end OMA.A061002Wolstenholme

end WolstenholmePairingSection

section A061002RationalSection

/- The two reduced rational forms used by the harmonic quotient. -/

namespace OMA.A061002Rational

/-- If `p²` divides the numerator of a positive fraction and `p` is coprime
to its denominator, the normalized numerator and denominator give the identity. -/
theorem ratio_of_divisibility {q : ℚ} (hq : 0 < q) {p : ℕ} (hp : 0 < p)
    (hC : p.Coprime q.den) (hD : (p : ℤ) ^ 2 ∣ q.num) :
    (((q + 1 / (p : ℚ)) / q).den : ℤ) = (p : ℤ) ^ 3 * (q / (p : ℚ) ^ 2).num := by
  let a := q.num.natAbs
  let b := q.den
  have haInt : (a : ℤ) = q.num := Int.natAbs_of_nonneg (Rat.num_pos.mpr hq).le
  have ha : 0 < a := by exact_mod_cast (haInt.symm ▸ Rat.num_pos.mpr hq)
  have hb : 0 < b := q.den_pos
  have hfrac : (a : ℚ) / (b : ℚ) = q := by
    have hc : (a : ℚ) = (q.num : ℚ) := by exact_mod_cast haInt
    rw [hc, Rat.num_div_den]
  obtain ⟨v, hv⟩ := hD
  have hvD : v.natAbs ∣ a := by
    change v.natAbs ∣ q.num.natAbs
    rw [hv, Int.natAbs_mul]
    exact dvd_mul_left _ _
  have hV : Nat.Coprime v.natAbs b := q.reduced.coprime_dvd_left hvD
  have hVfrac : q / (p : ℚ) ^ 2 = (v : ℚ) / (b : ℚ) := by
    have haV : (a : ℚ) = (p : ℚ)^2 * (v : ℚ) := by
      exact_mod_cast (haInt.trans hv)
    rw [← hfrac, haV]
    field_simp
  have hNum : (q / (p : ℚ) ^ 2).num = v := by
    rw [hVfrac]
    exact Rat.num_div_eq_of_coprime (show 0 < (b : ℤ) by exact_mod_cast hb)
      (by simpa only [Int.natAbs_natCast] using hV)
  have hPQ : (p * a + b).Coprime (p * a) :=
    Nat.coprime_self_add_left.mpr (Nat.Coprime.mul_left hC q.reduced).symm
  have hQfrac : (q + 1 / (p : ℚ)) / q = ((p * a + b : ℕ) : ℚ) / ((p * a : ℕ) : ℚ) := by
    rw [← hfrac]
    push_cast
    field_simp
  have hDen : (((q + 1 / (p : ℚ)) / q).den : ℤ) = (p * a : ℕ) := by
    rw [hQfrac]
    exact Rat.den_div_eq_of_coprime (show 0 < ((p * a : ℕ) : ℤ) by exact_mod_cast Nat.mul_pos hp ha)
      (by simpa only [Int.natAbs_natCast] using hPQ)
  rw [hDen, hNum]
  push_cast
  rw [haInt, hv]
  ring

open OMA.S_oeis_a061002

/-- The harmonic quotient follows from the numerator and denominator conditions. -/
theorem harmonic_identity_of_divisibility {p : ℕ} (hp : 3 < p)
    (hC : p.Coprime (H (p - 1)).den) (hD : (p : ℤ) ^ 2 ∣ (H (p - 1)).num) :
    ((H p / H (p - 1)).den : ℤ) = (p : ℤ) ^ 3 * (H (p - 1) / (p : ℚ) ^ 2).num := by
  have h1 : 1 ≤ p - 1 := by omega
  have hH : 0 < H (p - 1) := by
    have hmem : 1 ∈ Finset.Icc 1 (p - 1) := Finset.mem_Icc.mpr ⟨le_rfl, h1⟩
    apply (show (0 : ℚ) < 1 / (1 : ℕ) by norm_num).trans_le
    exact Finset.single_le_sum (f := fun k : ℕ => (1 : ℚ) / k) (fun k _ => by positivity) hmem
  have hAdd : H p = H (p - 1) + 1 / (p : ℚ) := by
    unfold H
    have he := Finset.sum_Icc_succ_top (a := 1) (b := p - 1)
      (by omega) (fun k : ℕ => (1 : ℚ) / k)
    simpa only [Nat.sub_add_cancel (show 1 ≤ p by omega)] using he
  rw [hAdd]
  exact ratio_of_divisibility hH (by omega) hC hD

end OMA.A061002Rational

end A061002RationalSection

theorem OMA.solution : type_of% @OMA.S_oeis_a061002.main := by
  intro p hp h3
  obtain ⟨hNum, hDen⟩ := OMA.A061002Wolstenholme.harmonic_num_dvd_and_den_of_cross hp h3
    (OMA.A061002.cross_sum_dvd hp h3)
  exact OMA.A061002Rational.harmonic_identity_of_divisibility h3
    (hp.coprime_iff_not_dvd.mpr hDen) hNum
