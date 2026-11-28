import OMAStatements.S_oeis_a337950
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA337950Proof

open OMA.S_oeis_a337950

private lemma four_pow_odd_add_one_mod5 (n : ℕ) (hodd : Odd n) :
    ((4 : ZMod 5) ^ n + 1) = 0 := by
  have h4 : (4 : ZMod 5) = -1 := by decide
  rw [h4, hodd.neg_one_pow]
  decide

private lemma coeff_thetaF_mod5_zero_of_not_four_dvd {m : ℕ} (hnd : ¬ (4 ∣ m)) :
    ((PowerSeries.coeff m thetaF : ℤ) : ZMod 5) = 0 := by
  unfold thetaF
  rw [PowerSeries.coeff_mk]
  have hm0 : m ≠ 0 := fun h => hnd (h ▸ dvd_zero 4)
  rw [if_neg hm0]
  split_ifs with hsq
  · set n := Nat.sqrt m
    have hn_odd : Odd n := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      rcases hev with ⟨q, hq⟩
      apply hnd
      refine ⟨q ^ 2, ?_⟩
      rw [← hsq, hq]; ring
    push_cast
    rw [four_pow_odd_add_one_mod5 n hn_odd, mul_zero]
  · simp

private lemma coeff_thetaF_zero : PowerSeries.coeff 0 thetaF = 1 := by
  unfold thetaF; rw [PowerSeries.coeff_mk]; simp

private lemma coeff_A_mod5_zero_of_not_four_dvd {A : PowerSeries ℤ} (hA : IsA337950 A) :
    ∀ m : ℕ, ¬ (4 ∣ m) → ((PowerSeries.coeff m A : ℤ) : ZMod 5) = 0 := by
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 5) := PowerSeries.map (Int.castRingHom (ZMod 5))
  have hF0 : PowerSeries.coeff 0 (phi thetaF) = 1 := by
    simp [phi, coeff_thetaF_zero]
  have hF_zero : ∀ j : ℕ, ¬ (4 ∣ j) → PowerSeries.coeff j (phi thetaF) = 0 := by
    intro j hj
    simp only [phi, PowerSeries.coeff_map, Int.coe_castRingHom]
    exact coeff_thetaF_mod5_zero_of_not_four_dvd hj
  have hRHS_zero : ∀ j : ℕ, ¬ (4 ∣ j) → PowerSeries.coeff j (phi (negXDeriv thetaF)) = 0 := by
    intro j hj
    simp only [phi, PowerSeries.coeff_map, Int.coe_castRingHom, negXDeriv, PowerSeries.coeff_mk,
      Int.cast_mul, Int.cast_neg, Int.cast_natCast]
    rw [coeff_thetaF_mod5_zero_of_not_four_dvd hj, mul_zero]
  have hmul : phi thetaF * phi A = phi (negXDeriv thetaF) := by
    rw [← map_mul, hA.2]
  intro m
  suffices h : ¬ (4 ∣ m) → PowerSeries.coeff m (phi A) = 0 by
    simpa [phi] using h
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hnd
    have hm := congrArg (PowerSeries.coeff m) hmul
    rw [hRHS_zero m hnd, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (phi thetaF) * PowerSeries.coeff j (phi A)),
      Finset.sum_range_succ'] at hm
    simp only [Nat.sub_zero, hF0, one_mul] at hm
    have hpre :
        ∑ k ∈ Finset.range m, PowerSeries.coeff (k + 1) (phi thetaF) * PowerSeries.coeff (m - (k + 1)) (phi A) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      by_cases h4 : 4 ∣ k + 1
      · have hnd' : ¬ (4 ∣ m - (k + 1)) := by
          intro h; apply hnd
          have : (k + 1) + (m - (k + 1)) = m := by omega
          rw [← this]; exact dvd_add h4 h
        rw [ih (m - (k + 1)) (by omega) hnd', mul_zero]
      · rw [hF_zero (k + 1) h4, zero_mul]
    rw [hpre, zero_add] at hm
    exact hm

end OeisA337950Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a337950.main := by
  intro A hA n k hk
  change PowerSeries.coeff (4 * n + k) A ≡ 0 [ZMOD ((5 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_zero]
  have hnd : ¬ (4 ∣ 4 * n + k) := by
    rcases hk with rfl | rfl | rfl <;> omega
  exact OeisA337950Proof.coeff_A_mod5_zero_of_not_four_dvd hA (4 * n + k) hnd
