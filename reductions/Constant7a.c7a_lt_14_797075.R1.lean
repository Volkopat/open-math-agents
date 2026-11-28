import FormalConjectures.OptimizationConstants.«7a»
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- The final integral in Rhin and Viola, Acta Arithmetica 77 (1996), Theorem 5.1.
-- Index n = floor(log_32768 b). The two bounds leave slack in each exponential rate.
open Real Filter
open scoped Topology

namespace OMA.R_Constant7a_c7a_lt_14_797075_R1

def H1 : Prop := ∀ᶠ b : ℕ in atTop,
  let I : ℝ := ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      ((x ^ 12 * (1 - x) ^ 12 * y ^ 14 * (1 - y) ^ 14) / (1 - x * y) ^ 13) ^
        (Nat.log 32768 b) / (1 - x * y)
  ∃ d p q : ℤ, (b : ℝ) ^ 2 ≤ 2 * d ∧ (d : ℝ) ≤ (b : ℝ) ^ 2 ∧
    |(q : ℝ)| ≤ (b : ℝ) ^ 5 ∧ (d : ℝ) * I = p + q * (π ^ 2 / 6)

def H2 : Prop := ∀ᶠ b : ℕ in atTop,
  let I : ℝ := ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      ((x ^ 12 * (1 - x) ^ 12 * y ^ 14 * (1 - y) ^ 14) / (1 - x * y) ^ 13) ^
        (Nat.log 32768 b) / (1 - x * y)
  2 ≤ I * (b : ℝ) ^ 4 ∧ 2 * I * (b : ℝ) ^ 3 ≤ 1

lemma liouvilleWith_sq_div_six_of_pi {p : ℝ} (hp : 0 ≤ p) (h : LiouvilleWith p π) :
    LiouvilleWith (p / 2) (π ^ 2 / 6) := by
  have hsq : LiouvilleWith (p / 2) (π ^ 2) := by
    obtain ⟨C, hC0, hfreq⟩ := h.exists_pos
    refine ⟨(2 * π + C) * C, ?_⟩
    have hsq_tendsto : Tendsto (fun n : ℕ => n ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num)
    refine hsq_tendsto.frequently (hfreq.mono ?_)
    rintro n ⟨hn1, m, hne, hlt⟩
    refine ⟨m ^ 2, ?_, ?_⟩
    · intro heq
      have h1 : (π - (m : ℝ) / n) * (π + (m : ℝ) / n) = 0 := by
        push_cast at heq
        have : ((m : ℝ) / n) ^ 2 = (m : ℝ) ^ 2 / (n : ℝ) ^ 2 := div_pow _ _ 2
        linarith
      rcases mul_eq_zero.1 h1 with hsub | hadd
      · exact hne (sub_eq_zero.1 hsub)
      · exact irrational_pi ⟨((-m : ℤ) : ℚ) / (n : ℚ), by
          push_cast
          have : (-(m : ℝ)) / (n : ℝ) = -((m : ℝ) / (n : ℝ)) := neg_div _ _
          linarith⟩
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn1
      have hnpow1 : (1 : ℝ) ≤ (n : ℝ) ^ p :=
        Real.one_le_rpow (by exact_mod_cast hn1) hp
      have hdiffC : |π - (m : ℝ) / n| < C := by
        calc |π - (m : ℝ) / n| < C / (n : ℝ) ^ p := hlt
          _ ≤ C / 1 := div_le_div_of_nonneg_left hC0.le zero_lt_one hnpow1
          _ = C := div_one C
      have hsum_bd : |π + (m : ℝ) / n| ≤ 2 * π + C := by
        have hrew : π + (m : ℝ) / n = 2 * π - (π - (m : ℝ) / n) := by ring
        rw [hrew]
        calc |2 * π - (π - (m : ℝ) / n)|
            ≤ |2 * π| + |π - (m : ℝ) / n| := abs_sub _ _
          _ = 2 * π + |π - (m : ℝ) / n| := by rw [abs_of_pos (by positivity)]
          _ ≤ 2 * π + C := by linarith
      have hdiff_sq : π ^ 2 - ((m ^ 2 : ℤ) : ℝ) / ((n ^ 2 : ℕ) : ℝ) =
          (π + (m : ℝ) / n) * (π - (m : ℝ) / n) := by
        push_cast; field_simp [hnpos.ne']; ring
      rw [hdiff_sq, abs_mul]
      have hden_eq : (((n ^ 2 : ℕ) : ℝ)) ^ (p / 2) = (n : ℝ) ^ p := by
        push_cast
        rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul hnpos.le]
        congr 1; ring
      rw [hden_eq, mul_div_assoc]
      calc |π + (m : ℝ) / n| * |π - (m : ℝ) / n|
          ≤ (2 * π + C) * |π - (m : ℝ) / n| :=
            mul_le_mul_of_nonneg_right hsum_bd (abs_nonneg _)
        _ < (2 * π + C) * (C / (n : ℝ) ^ p) :=
            mul_lt_mul_of_pos_left hlt (by positivity)
  have hmul := hsq.mul_rat (r := (1 / 6 : ℚ)) (by norm_num)
  simpa [div_eq_mul_inv] using hmul


lemma separation {b : ℕ} (hb : 2 ≤ b) {a d p q : ℤ} {x I : ℝ}
    (D₁ : (b : ℝ) ^ 2 ≤ 2 * d) (D₂ : (d : ℝ) ≤ (b : ℝ) ^ 2)
    (Q : |(q : ℝ)| ≤ (b : ℝ) ^ 5) (L : (d : ℝ) * I = p + q * x)
    (I₁ : 2 ≤ I * (b : ℝ) ^ 4) (I₂ : 2 * I * (b : ℝ) ^ 3 ≤ 1)
    (small : |x - a / (b : ℝ)| < 1 / (b : ℝ) ^ 7) : False := by
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  have hI : 0 ≤ I := by
    by_contra! h
    have := mul_neg_of_neg_of_pos h (pow_pos hb0 4)
    linarith
  have lower : 1 ≤ d * I * (b : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right D₁ (mul_nonneg hI (sq_nonneg (b : ℝ)))]
  have upper : 2 * (d : ℝ) * I * b ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_right D₂ (mul_nonneg hI hb0.le)]
  let e : ℝ := q * (x - a / (b : ℝ))
  have small' : |e| < 1 / (b : ℝ) ^ 2 := by
    calc |e| = |(q : ℝ)| * |x - a / (b : ℝ)| := abs_mul _ _
      _ ≤ (b : ℝ) ^ 5 * |x - a / (b : ℝ)| := mul_le_mul_of_nonneg_right Q (abs_nonneg _)
      _ < (b : ℝ) ^ 5 * (1 / (b : ℝ) ^ 7) := mul_lt_mul_of_pos_left small (pow_pos hb0 5)
      _ = _ := by field_simp
  have err := abs_lt.mp small'
  let z : ℤ := p * b + q * a
  have identity : (z : ℝ) = ((d : ℝ) * I - e) * b := by
    dsimp [z, e]
    push_cast
    rw [L]
    field_simp
    ring
  have zpos : 0 < (z : ℝ) := by
    rw [identity]
    exact mul_pos (sub_pos.mpr (err.2.trans_le ((div_le_iff₀ (pow_pos hb0 2)).2 lower))) hb0
  have zlt : (z : ℝ) < 1 := by
    have inv : 1 / (b : ℝ) ^ 2 ≤ 1 / (2 * b) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith [mul_nonneg hb0.le (sub_nonneg.mpr hb')]
    have half : -(1 / (2 * (b : ℝ))) < e := lt_of_le_of_lt (neg_le_neg inv) err.1
    have aux := (neg_lt_iff_pos_add).1 half
    have aux' := mul_pos aux (show 0 < 2 * (b : ℝ) by positivity)
    rw [add_mul, one_div_mul_cancel (by positivity)] at aux'
    rw [identity]
    nlinarith
  have zpos' : (0 : ℤ) < z := by exact_mod_cast zpos
  have zlt' : z < (1 : ℤ) := by exact_mod_cast zlt
  omega

theorem main : H1 → H2 → type_of% @Constant7a.c7a_lt_14_797075 := by
  intro h₁ h₂
  have bound : Constant7a.C7a ≤ 14 := by
    unfold Constant7a.C7a Constant7a.irrationalityExponent
    rw [sSup_le_iff]
    rintro _ ⟨p, hp, rfl⟩
    by_contra! hg
    have hg' : (14 : ℝ) < (p : ℝ) := by
      have h : (14 : NNReal) < p := by exact_mod_cast hg
      exact_mod_cast h
    have hz := liouvilleWith_sq_div_six_of_pi p.coe_nonneg hp
    have freq := hz.frequently_lt_rpow_neg (show (7 : ℝ) < p / 2 by linarith)
    obtain ⟨b, ⟨⟨hb, ha⟩, hc⟩, a, _, hs⟩ :=
      ((((eventually_ge_atTop 2).and h₁).and h₂).and_frequently freq).exists
    obtain ⟨d, u, v, hd, hd', hv, eq⟩ := ha
    obtain ⟨lo, hi⟩ := hc
    apply separation hb hd hd' hv eq lo hi (a := a)
    simpa [Real.rpow_neg (Nat.cast_nonneg b), one_div] using hs
  apply lt_of_le_of_lt bound
  change ((14 : NNReal) : ENNReal) < ((14.797075 : NNReal) : ENNReal)
  apply ENNReal.coe_lt_coe.mpr
  norm_num

end OMA.R_Constant7a_c7a_lt_14_797075_R1
