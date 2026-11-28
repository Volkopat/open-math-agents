import OMAStatements.S_oeis_a295762
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA295762Proof

open Classical
open OMA.S_oeis_a295762

private noncomputable def psComp2 (F G : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

private noncomputable def psSubPow2 (F : PowerSeries (ZMod 2)) (m : ℕ) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if m ∣ n then PowerSeries.coeff (n / m) F else 0

private lemma map_psComp (F G : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (psComp F G) =
      psComp2 (PowerSeries.map (Int.castRingHom (ZMod 2)) F)
              (PowerSeries.map (Int.castRingHom (ZMod 2)) G) := by
  ext n
  simp only [PowerSeries.coeff_map, psComp, psComp2, PowerSeries.coeff_mk, map_sum, map_mul,
    ← map_pow]

private lemma map_psSubPow (F : PowerSeries ℤ) (m : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (psSubPow F m) =
      psSubPow2 (PowerSeries.map (Int.castRingHom (ZMod 2)) F) m := by
  ext n
  simp only [PowerSeries.coeff_map, psSubPow, psSubPow2, PowerSeries.coeff_mk]
  split_ifs <;> simp

private lemma psComp2_X (F : PowerSeries (ZMod 2)) : psComp2 F PowerSeries.X = F := by
  ext n
  unfold psComp2
  rw [PowerSeries.coeff_mk]
  simp_rw [PowerSeries.coeff_X_pow]
  rw [Finset.sum_eq_single n]
  · simp
  · intro k _ hne; simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma two_eq_zero_ps2 : (2 : PowerSeries (ZMod 2)) = 0 := by
  ext k; rw [show (2 : PowerSeries (ZMod 2)) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
  split_ifs <;> simp [show (2 : ZMod 2) = 0 by decide]

private lemma A_eq_X_add_sub2 {A : PowerSeries ℤ} (hA : IsA295762 A) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A =
      PowerSeries.X + psSubPow2 (PowerSeries.map (Int.castRingHom (ZMod 2)) A) 2 := by
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have h := congrArg phi hA.2
  rw [map_psComp, map_sub, map_mul, map_ofNat, two_eq_zero_ps2, zero_mul, sub_zero,
    map_add] at h
  dsimp only [phi] at h
  rw [PowerSeries.map_X, map_psSubPow, psComp2_X] at h
  exact h

private lemma coeff_A_mod2 {A : PowerSeries ℤ} (hA : IsA295762 A) :
    ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.map (Int.castRingHom (ZMod 2)) A) =
      if ∃ k : ℕ, n = 2 ^ k then 1 else 0 := by
  let A2 := PowerSeries.map (Int.castRingHom (ZMod 2)) A
  have hA20 : PowerSeries.coeff 0 A2 = 0 := by simp [A2, hA.1]
  have hA2 : A2 = PowerSeries.X + psSubPow2 A2 2 := A_eq_X_add_sub2 hA
  intro n
  change PowerSeries.coeff n A2 = _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      rw [hA20, if_neg]
      rintro ⟨k, hk⟩
      have := Nat.one_le_pow k 2 (by decide)
      omega
    | 1 =>
      have h := congrArg (PowerSeries.coeff 1) hA2
      simp only [map_add, PowerSeries.coeff_X, psSubPow2, PowerSeries.coeff_mk, ↓reduceIte,
        show ¬ (2 ∣ 1) by decide, add_zero] at h
      rw [h, if_pos ⟨0, rfl⟩]
    | m + 2 =>
      have h := congrArg (PowerSeries.coeff (m + 2)) hA2
      simp only [map_add, PowerSeries.coeff_X, psSubPow2, PowerSeries.coeff_mk,
        show m + 2 ≠ 1 by omega, ↓reduceIte, zero_add] at h
      rw [h]
      by_cases h2 : 2 ∣ m + 2
      · rw [if_pos h2, ih ((m + 2) / 2) (by omega)]
        have hiff : (∃ k : ℕ, (m + 2) / 2 = 2 ^ k) ↔ (∃ k : ℕ, m + 2 = 2 ^ k) := by
          constructor
          · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ']; omega⟩
          · rintro ⟨k, hk⟩
            cases k with
            | zero => norm_num at hk; omega
            | succ k' => rw [pow_succ'] at hk; exact ⟨k', by omega⟩
        by_cases hex : ∃ k : ℕ, (m + 2) / 2 = 2 ^ k
        · rw [if_pos hex, if_pos (hiff.mp hex)]
        · rw [if_neg hex, if_neg (mt hiff.mpr hex)]
      · rw [if_neg h2]
        have hnot : ¬ ∃ k : ℕ, m + 2 = 2 ^ k := by
          rintro ⟨k, hk⟩
          cases k with
          | zero => norm_num at hk; omega
          | succ k' => apply h2; rw [hk, pow_succ']; exact dvd_mul_right 2 _
        rw [if_neg hnot]

end OeisA295762Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a295762.main := by
  intro A hA n
  have hmod : PowerSeries.coeff n A % 2 = 1 ↔ ((PowerSeries.coeff n A : ℤ) : ZMod 2) = 1 := by
    constructor
    · intro h
      have h' : PowerSeries.coeff n A ≡ 1 [ZMOD ((2 : ℕ) : ℤ)] := by rw [Int.ModEq]; omega
      simpa using (ZMod.intCast_eq_intCast_iff _ _ 2).mpr h'
    · intro h
      have h' : PowerSeries.coeff n A ≡ 1 [ZMOD ((2 : ℕ) : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff _ _ 2).mp (by simpa using h)
      rw [Int.ModEq] at h'; omega
  rw [hmod]
  have h := OeisA295762Proof.coeff_A_mod2 hA n
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom] at h
  rw [h]
  split_ifs with hex
  · simp [hex]
  · simp [hex]
