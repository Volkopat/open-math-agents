import OMAStatements.S_oeis_a383377
import Mathlib

namespace A383377Aux
open PowerSeries

lemma neg2 : ∀ a : ZMod 2, -a = a := by decide

lemma abs_cast (x : ℤ) : ((|x| : ℤ) : ZMod 2) = (x : ZMod 2) := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, Int.cast_neg, neg2]

noncomputable def red : PowerSeries ℤ →+* PowerSeries (ZMod 2) :=
  PowerSeries.map (Int.castRingHom (ZMod 2))

lemma coeff_red (n : ℕ) (F : PowerSeries ℤ) :
    coeff n (red F) = ((coeff n F : ℤ) : ZMod 2) := by
  unfold red
  rw [coeff_map]
  rfl

lemma coeff_mul_congr (P F G : PowerSeries (ZMod 2)) (n : ℕ)
    (h : ∀ m, m ≤ n → coeff m F = coeff m G) : coeff n (P * F) = coeff n (P * G) := by
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [h p.2 (by omega)]

lemma key (B C : PowerSeries (ZMod 2)) (hBC : C * B = 1)
    (h : ∀ n, coeff n B = ∑ j ∈ Finset.range (n + 1), coeff (n - j) (C ^ j)) : B = 1 + X := by
  have hG : ∀ n m, m ≤ n →
      coeff m B = coeff m (∑ j ∈ Finset.range (n + 1), (X * C) ^ j) := by
    intro n m hm
    have h1 : coeff m (∑ j ∈ Finset.range (n + 1), (X * C) ^ j) =
        ∑ j ∈ Finset.range (n + 1), coeff m ((X * C) ^ j) := map_sum _ _ _
    have h2 : ∑ j ∈ Finset.range (m + 1), coeff m ((X * C) ^ j) =
        ∑ j ∈ Finset.range (n + 1), coeff m ((X * C) ^ j) := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro j _ hj
      rw [mul_pow, coeff_X_pow_mul', if_neg]
      intro hjm
      exact hj (Finset.mem_range.mpr (by omega))
    rw [h m, h1, ← h2]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.mem_range.mp hj
    rw [mul_pow, coeff_X_pow_mul', if_pos (by omega)]
  have hmain : ∀ n, coeff n ((1 - X * C) * B) = coeff n (1 : PowerSeries (ZMod 2)) := by
    intro n
    rw [coeff_mul_congr _ _ _ n (hG n), mul_neg_geom_sum, map_sub, mul_pow, coeff_X_pow_mul',
      if_neg (by omega), sub_zero]
  have e : (1 - X * C) * B = B - X := by
    have e' : (1 - X * C) * B = B - X * (C * B) := by ring
    rw [e', hBC, mul_one]
  rw [e] at hmain
  have hBX : B - X = 1 := PowerSeries.ext hmain
  rw [← hBX]; ring
end A383377Aux

open A383377Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a383377.main := by
  intro A hA n hn
  have hBC : red (↑A⁻¹ : PowerSeries ℤ) * red (A : PowerSeries ℤ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h : ∀ n, PowerSeries.coeff n (red (A : PowerSeries ℤ)) =
      ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff (n - j) ((red (↑A⁻¹ : PowerSeries ℤ)) ^ j) := by
    intro n
    rw [coeff_red, hA n, Int.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← map_pow, coeff_red]
    exact abs_cast _
  have hB := key _ _ hBC h
  have hc : PowerSeries.coeff n (red (A : PowerSeries ℤ)) = 0 := by
    rw [hB, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X, if_neg (by omega),
      if_neg (by omega), add_zero]
  rw [coeff_red] at hc
  exact ZMod.intCast_eq_zero_iff_even.mp hc
