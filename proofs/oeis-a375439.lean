import OMAStatements.S_oeis_a375439
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA375439Proof

open Classical
open OMA.S_oeis_a375439

private noncomputable def psSubPow2 (F : PowerSeries (ZMod 2)) (m : ℕ) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if m ∣ n then PowerSeries.coeff (n / m) F else 0

private lemma map_psSubPow (A : PowerSeries ℤ) (m : ℕ) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (psSubPow A m) =
      psSubPow2 (PowerSeries.map (Int.castRingHom (ZMod 2)) A) m := by
  ext n
  simp only [PowerSeries.coeff_map, psSubPow, psSubPow2, PowerSeries.coeff_mk]
  split_ifs <;> simp

private lemma two_eq_zero_ps2 : (2 : PowerSeries (ZMod 2)) = 0 := by
  ext k; rw [show (2 : PowerSeries (ZMod 2)) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
  split_ifs <;> simp [show (2 : ZMod 2) = 0 by decide]

private lemma three_eq_one_ps2 : (3 : PowerSeries (ZMod 2)) = 1 := by
  ext k; rw [show (3 : PowerSeries (ZMod 2)) = PowerSeries.C 3 from rfl, PowerSeries.coeff_C,
    PowerSeries.coeff_one]
  split_ifs <;> simp [show (3 : ZMod 2) = 1 by decide]

private lemma A_eq_mod2 {A : PowerSeries ℤ} (hA : IsA375439 A) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A =
      PowerSeries.X + PowerSeries.X ^ 2 + psSubPow2 (PowerSeries.map (Int.castRingHom (ZMod 2)) A) 3 := by
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  have h := congrArg phi hA.2
  simp only [map_mul, map_add, map_pow, map_ofNat, three_eq_one_ps2, two_eq_zero_ps2,
    one_mul, zero_mul, add_zero] at h
  dsimp only [phi] at h
  rw [PowerSeries.map_X, map_psSubPow] at h
  exact h

private lemma coeff_A_mod2 {A : PowerSeries ℤ} (hA : IsA375439 A) :
    ∀ n : ℕ, PowerSeries.coeff n (PowerSeries.map (Int.castRingHom (ZMod 2)) A) =
      if ∃ k : ℕ, n = 3 ^ k ∨ n = 2 * 3 ^ k then 1 else 0 := by
  let A2 := PowerSeries.map (Int.castRingHom (ZMod 2)) A
  have hA20 : PowerSeries.coeff 0 A2 = 0 := by simp [A2, hA.1]
  have hA2 : A2 = PowerSeries.X + PowerSeries.X ^ 2 + psSubPow2 A2 3 := A_eq_mod2 hA
  intro n
  change PowerSeries.coeff n A2 = _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      rw [hA20, if_neg]
      rintro ⟨k, h | h⟩ <;> (have := Nat.one_le_pow k 3 (by decide); omega)
    | 1 =>
      have h := congrArg (PowerSeries.coeff 1) hA2
      simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, psSubPow2,
        PowerSeries.coeff_mk] at h
      simp only [↓reduceIte, show (1 : ℕ) ≠ 2 by decide, show ¬ (3 ∣ 1) by decide,
        add_zero] at h
      rw [h, if_pos ⟨0, Or.inl rfl⟩]
    | 2 =>
      have h := congrArg (PowerSeries.coeff 2) hA2
      simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, psSubPow2,
        PowerSeries.coeff_mk] at h
      simp only [show (2 : ℕ) ≠ 1 by decide, ↓reduceIte, show ¬ (3 ∣ 2) by decide,
        zero_add, add_zero] at h
      rw [h, if_pos ⟨0, Or.inr rfl⟩]
    | m + 3 =>
      have h := congrArg (PowerSeries.coeff (m + 3)) hA2
      simp only [map_add, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, psSubPow2,
        PowerSeries.coeff_mk, show m + 3 ≠ 1 by omega, show m + 3 ≠ 2 by omega,
        ↓reduceIte, zero_add] at h
      rw [h]
      by_cases h3 : 3 ∣ m + 3
      · rw [if_pos h3, ih ((m + 3) / 3) (by omega)]
        have hiff : (∃ k : ℕ, (m + 3) / 3 = 3 ^ k ∨ (m + 3) / 3 = 2 * 3 ^ k) ↔
            (∃ k : ℕ, m + 3 = 3 ^ k ∨ m + 3 = 2 * 3 ^ k) := by
          constructor
          · rintro ⟨k, hk | hk⟩
            · exact ⟨k + 1, Or.inl (by rw [pow_succ']; omega)⟩
            · exact ⟨k + 1, Or.inr (by rw [pow_succ']; omega)⟩
          · rintro ⟨k, hk | hk⟩
            · cases k with
              | zero => norm_num at hk; omega
              | succ k' => rw [pow_succ'] at hk; exact ⟨k', Or.inl (by omega)⟩
            · cases k with
              | zero => norm_num at hk; omega
              | succ k' => rw [pow_succ'] at hk; exact ⟨k', Or.inr (by omega)⟩
        by_cases hex : ∃ k : ℕ, (m + 3) / 3 = 3 ^ k ∨ (m + 3) / 3 = 2 * 3 ^ k
        · rw [if_pos hex, if_pos (hiff.mp hex)]
        · rw [if_neg hex, if_neg (mt hiff.mpr hex)]
      · rw [if_neg h3]
        have hnot : ¬ ∃ k : ℕ, m + 3 = 3 ^ k ∨ m + 3 = 2 * 3 ^ k := by
          rintro ⟨k, hk | hk⟩
          · cases k with
            | zero => norm_num at hk; omega
            | succ k' =>
              apply h3; rw [hk, pow_succ']; exact dvd_mul_right 3 _
          · cases k with
            | zero => norm_num at hk; omega
            | succ k' =>
              apply h3; rw [hk, pow_succ', show 2 * (3 * 3 ^ k') = 3 * (2 * 3 ^ k') by ring]
              exact dvd_mul_right 3 _
        rw [if_neg hnot]

end OeisA375439Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a375439.main := by
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
  have h := OeisA375439Proof.coeff_A_mod2 hA n
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom] at h
  rw [h]
  split_ifs with hex
  · simp [hex]
  · simp [hex]
