import OMAStatements.S_oeis_a245658
import Mathlib

namespace OMA.S_oeis_a245658

private lemma coeff_cube_zmod3 (f : PowerSeries (ZMod 3)) (n : ℕ) :
    PowerSeries.coeff (3 * n) (f ^ 3) = PowerSeries.coeff n f := by
  have htrunc : ∀ m : ℕ,
      PowerSeries.coeff m (f ^ 3) =
        PowerSeries.coeff m ((∑ k ∈ Finset.range (m + 1),
          PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k) ^ 3) := by
    intro m
    set P : PowerSeries (ZMod 3) :=
      ∑ k ∈ Finset.range (m + 1), PowerSeries.C (PowerSeries.coeff k f) * PowerSeries.X ^ k
    have hdiff : ∀ k ≤ m, PowerSeries.coeff k (f - P) = 0 := by
      intro k hk
      rw [map_sub, sub_eq_zero]
      simp only [P, map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hjk; rw [if_neg (Ne.symm hjk), mul_zero]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
    have hmul_zero : ∀ (g h : PowerSeries (ZMod 3)),
        (∀ k ≤ m, PowerSeries.coeff k g = 0) →
        PowerSeries.coeff m (g * h) = 0 := by
      intro g h hg
      rw [PowerSeries.coeff_mul]
      refine Finset.sum_eq_zero fun ab hab => ?_
      have hsum : ab.1 + ab.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      rw [hg ab.1 (by omega), zero_mul]
    have hsub : f ^ 3 - P ^ 3 = (f - P) * (f ^ 2 + f * P + P ^ 2) := by ring
    have h0 := hmul_zero (f - P) (f ^ 2 + f * P + P ^ 2) hdiff
    rw [← hsub, map_sub, sub_eq_zero] at h0
    exact h0
  rw [htrunc (3 * n)]
  have hadd3 : ∀ a b : PowerSeries (ZMod 3), (a + b) ^ 3 = a ^ 3 + b ^ 3 := by
    intro a b
    have h3 : (3 : PowerSeries (ZMod 3)) = 0 := by
      have : (3 : ZMod 3) = 0 := by decide
      rw [← map_ofNat PowerSeries.C 3, this, map_zero]
    calc (a + b) ^ 3 = a ^ 3 + 3 * (a ^ 2 * b + a * b ^ 2) + b ^ 3 := by ring
      _ = a ^ 3 + b ^ 3 := by rw [h3, zero_mul, add_zero]
  have hfrob : ∀ (s : Finset ℕ) (g : ℕ → PowerSeries (ZMod 3)),
      (∑ k ∈ s, g k) ^ 3 = ∑ k ∈ s, (g k) ^ 3 := by
    intro s g
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, hadd3, ih]
  rw [hfrob]
  simp only [mul_pow, ← map_pow PowerSeries.C, ← pow_mul, map_sum, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X_pow]
  rw [Finset.sum_eq_single n]
  · simp [mul_comm]
  · intro k _ hkn
    rw [if_neg (by omega), mul_zero]
  · intro hnot
    exact absurd (Finset.mem_range.mpr (by omega)) hnot

private theorem main_proved :
    ∀ (a b : ℕ → ℤ) (A B : PowerSeries ℤ),
      A = PowerSeries.mk a →
      B = PowerSeries.mk b →
      (∀ m : ℕ, (∑ n ∈ Finset.range (m + 1),
        PowerSeries.coeff m (PowerSeries.C (b n) * PowerSeries.X ^ n * polyA247031 n)) =
        if m = 0 then 1 else 0) →
      A ^ 3 = B →
      ∀ n : ℕ, (a n % 3 = 2 ↔ b (3 * n) % 3 = 2) := by
  intro a b A B hA hB _ hcube n
  set φ3 : ℤ →+* ZMod 3 := Int.castRingHom (ZMod 3)
  set Φ3 : PowerSeries ℤ →+* PowerSeries (ZMod 3) := PowerSeries.map φ3
  have hmap : (Φ3 A) ^ 3 = Φ3 B := by
    rw [← map_pow, hcube]
  have hcoeff := congr_arg (PowerSeries.coeff (3 * n)) hmap
  rw [coeff_cube_zmod3, PowerSeries.coeff_map, PowerSeries.coeff_map, hA, hB,
    PowerSeries.coeff_mk, PowerSeries.coeff_mk] at hcoeff
  have hmod : (a n : ZMod 3) = (b (3 * n) : ZMod 3) := hcoeff
  have heq := (ZMod.intCast_eq_intCast_iff (a n) (b (3 * n)) 3).mp hmod
  rw [Int.ModEq] at heq
  norm_num at heq
  rw [heq]

end OMA.S_oeis_a245658

theorem OMA.solution : type_of% @OMA.S_oeis_a245658.main :=
  OMA.S_oeis_a245658.main_proved
