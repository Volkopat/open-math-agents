import OMAStatements.S_oeis_a389542

open PowerSeries

/-
SPDX-License-Identifier: Apache-2.0

`coeff_square_mod_two` and `quadratic_coeff_one_iff_power_two` are adapted from
dvgyl/oeis-proofs (revision 55ad2bd4804b6bcefeeb6c21eb06eac8b09c45d8, Apache 2.0), as
modified in the A393171 proof for the pinned Mathlib. The rest is new code.
-/

namespace OMA.A389542Proof

theorem coeff_square_mod_two (A : PowerSeries (ZMod 2)) (n : ℕ) :
    coeff n (A^2) = if 2 ∣ n then coeff (n/2) A else 0 := by
  rw [pow_two, coeff_mul_eq_coeff_trunc_mul_trunc A A (Nat.lt_succ_self n)]
  rw [← Polynomial.coe_mul, ← pow_two]
  rw [← Polynomial.map_frobenius_expand 2, Polynomial.coeff_coe, Polynomial.coeff_map,
    frobenius_def, Polynomial.coeff_expand (by decide : 0 < 2)]
  split_ifs with h
  · rw [ZMod.pow_card, coeff_trunc, if_pos (by omega)]
  · simp

theorem quadratic_coeff_one_iff_power_two (A : PowerSeries (ZMod 2))
    (h0 : coeff 0 A = 0) (hquad : A = X + A^2) (n : ℕ) :
    coeff n A = 1 ↔ ∃ k : ℕ, n = 2^k := by
  have h1 : coeff 1 A = 1 := by
    have he := congrArg (coeff 1) hquad
    simpa only [map_add, coeff_X, if_pos rfl, coeff_square_mod_two,
      show ¬ 2 ∣ 1 by decide, if_false, add_zero, ite_true] using he
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hz : n = 0
    · subst n
      rw [h0]
      simp only [zero_ne_one, false_iff]
      rintro ⟨k, hk⟩
      exact (Nat.two_pow_pos k).ne' hk.symm
    by_cases ho : n = 1
    · subst n
      rw [h1]
      simp only [true_iff]
      exact ⟨0, by simp⟩
    have hn : 2 ≤ n := by omega
    have hc := congrArg (coeff n) hquad
    rw [map_add, coeff_square_mod_two, coeff_X, if_neg ho, zero_add] at hc
    by_cases hd : 2 ∣ n
    · rw [if_pos hd] at hc
      rw [hc]
      refine (ih (n/2) (by omega)).trans ?_
      constructor
      · rintro ⟨k, hk⟩
        refine ⟨k+1, ?_⟩
        have he := Nat.mul_div_cancel' hd
        rw [pow_succ]
        omega
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; omega
        | succ k =>
          refine ⟨k, ?_⟩
          rw [hk, pow_succ, Nat.mul_div_left _ (by decide : 0 < 2)]
    · rw [if_neg hd] at hc
      rw [hc]
      simp only [zero_ne_one, false_iff]
      rintro ⟨k, hk⟩
      cases k with
      | zero => simp at hk; omega
      | succ k =>
        apply hd
        rw [hk, pow_succ]
        exact dvd_mul_left _ _

end OMA.A389542Proof

open OMA.A389542Proof
open OMA.S_oeis_a389542

set_option maxHeartbeats 0 in
theorem OMA.solution : type_of% @OMA.S_oeis_a389542.main := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  classical
  intro A h0 h1 heq
  let U : PowerSeries ℤ := PowerSeries.mk (fun m => coeff (m + 1) A)
  have hU0 : constantCoeff U = 1 := by
    simpa only [U, PowerSeries.constantCoeff_mk, zero_add] using h1
  have hA : A = X * U := by
    simpa only [U, h0, map_zero, add_zero] using
      (PowerSeries.eq_X_mul_shift_add_const A)
  let B : PowerSeries ℤ := A ^ 2 - X ^ 2
  have hB0 : constantCoeff B = 0 := by simp [B, h0]
  have hb : PowerSeries.HasSubst B :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hB0
  let S : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ :=
    PowerSeries.substAlgHom hb
  have hS (P : PowerSeries ℤ) : S P = PowerSeries.subst B P := by
    change (PowerSeries.substAlgHom (R := ℤ) hb) P = _
    rw [PowerSeries.coe_substAlgHom]
  have hSX : S X = B := PowerSeries.substAlgHom_X hb
  have hV0 : coeff 0 (S U) = 1 := by
    have hz : constantCoeff (U - 1) = 0 := by simp [hU0]
    have hzero : constantCoeff (PowerSeries.subst B (U - 1)) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hB0 (U - 1) hz
    have hSU : S U = S (U - 1) + 1 := by rw [map_sub, map_one]; ring
    rw [hSU, map_add, PowerSeries.coeff_one, if_pos rfl, hS,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hzero, zero_add]
  have hcomp : B * S U = 4 * A ^ 3 := by
    calc
      B * S U = S A := by rw [hA, map_mul, hSX]
      _ = 4 * A ^ 3 := by
        rw [hS]
        change PowerSeries.subst B A = 4 * A ^ 3 at heq
        exact heq
  let F : PowerSeries ℤ →+* PowerSeries (ZMod 2) :=
    PowerSeries.map (Int.castRingHom (ZMod 2))
  have hFcoeff (P : PowerSeries ℤ) (m : ℕ) :
      coeff m (F P) = ((coeff m P : ℤ) : ZMod 2) := by
    exact PowerSeries.coeff_map (Int.castRingHom (ZMod 2)) m P
  have hFX : F X = X := by exact PowerSeries.map_X _
  have htwo : (2 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (PowerSeries.C (R := ZMod 2))
        (show (2 : ZMod 2) = 0 by decide)
  have hfour : (4 : PowerSeries (ZMod 2)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (PowerSeries.C (R := ZMod 2))
        (show (4 : ZMod 2) = 0 by decide)
  have hVne : F (S U) ≠ 0 := by
    intro hz
    have hh := congrArg (fun P : PowerSeries (ZMod 2) => coeff 0 P) hz
    change coeff 0 (F (S U)) = coeff 0 (0 : PowerSeries (ZMod 2)) at hh
    simpa only [hFcoeff, hV0, Int.cast_one, map_zero, one_ne_zero] using hh
  have hFB : F B = 0 := by
    have hp : F B * F (S U) = 0 := by
      simpa only [map_mul, map_pow, map_ofNat, hfour, zero_mul] using
        (congrArg F hcomp)
    exact (mul_eq_zero.mp hp).resolve_right hVne
  have hFA : F A = X := by
    have hsquare : (F A) ^ 2 - (X : PowerSeries (ZMod 2)) ^ 2 = 0 := by
      simpa only [B, map_sub, map_pow, hFX] using hFB
    have hs : (F A - X) ^ 2 = 0 := by
      calc
        (F A - X) ^ 2 = (F A) ^ 2 - X ^ 2 +
            2 * (X ^ 2 - F A * X) := by ring
        _ = 0 := by rw [hsquare, htwo, zero_mul, add_zero]
    rw [pow_two, mul_eq_zero] at hs
    rcases hs with hs | hs <;> exact sub_eq_zero.mp hs
  have hFU : F U = 1 := by
    apply PowerSeries.X_mul_cancel
    calc
      X * F U = F A := by rw [hA, map_mul, hFX]
      _ = X * 1 := by rw [hFA, mul_one]
  let D : PowerSeries ℤ := PowerSeries.mk (fun m =>
    (coeff m U - coeff m (1 : PowerSeries ℤ)) / 2)
  have hUC : U = 1 + PowerSeries.C (2 : ℤ) * D := by
    apply PowerSeries.ext
    intro m
    have hc : coeff m (F U) = coeff m (F 1) := by rw [hFU, map_one F]
    simp only [hFcoeff] at hc
    have hmod := (ZMod.intCast_eq_intCast_iff'
      (coeff m U) (coeff m (1 : PowerSeries ℤ)) 2).mp hc
    simp only [map_add, PowerSeries.coeff_C_mul, D, PowerSeries.coeff_mk]
    omega
  have hUD : U = 1 + 2 * D := by
    simpa only [map_ofNat] using hUC
  have hD0 : coeff 0 D = 0 := by
    simp [D, PowerSeries.coeff_mk, PowerSeries.coeff_zero_eq_constantCoeff_apply, hU0]
  have hVmod : F (S U) = 1 := by
    simp only [hUD, map_add, map_mul, map_one, map_ofNat,
      htwo, zero_mul, add_zero]
  have hBform : B = (4 : PowerSeries ℤ) * X ^ 2 * (D + D ^ 2) := by
    dsimp only [B]
    rw [hA, hUD]
    ring
  have h4ne : (4 : PowerSeries ℤ) ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.constantCoeff (R := ℤ)) hz
    norm_num [map_ofNat] at hc
  have hfacne : (4 : PowerSeries ℤ) * X ^ 2 ≠ 0 :=
    mul_ne_zero h4ne (pow_ne_zero _ PowerSeries.X_ne_zero)
  have hcancel : (D + D ^ 2) * S U = X * U ^ 3 := by
    apply mul_left_cancel₀ hfacne
    calc
      (4 : PowerSeries ℤ) * X ^ 2 * ((D + D ^ 2) * S U) =
          B * S U := by rw [hBform]; ring
      _ = 4 * A ^ 3 := hcomp
      _ = (4 : PowerSeries ℤ) * X ^ 2 * (X * U ^ 3) := by
        rw [hA]
        ring
  have hD : F D + (F D) ^ 2 = X := by
    simpa only [map_mul, map_add, map_pow, hVmod, hFU, hFX,
      mul_one, one_pow] using (congrArg F hcancel)
  have hd0 : coeff 0 (F D) = 0 := by
    rw [hFcoeff, hD0, Int.cast_zero]
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m ≠ 0 := by omega
  have hcoef : coeff (m + 1) A = 2 * coeff m D := by
    rw [hA, PowerSeries.coeff_succ_X_mul, hUC, map_add,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_one, if_neg hm, zero_add]
  have hs : (∃ k : ℕ, m = 2 ^ k) ↔ specialIndex (m + 1) := by
    unfold specialIndex
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by omega⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by omega⟩
  have hquad : F D = X + (F D) ^ 2 := by
    calc F D = (F D + (F D) ^ 2) - (F D) ^ 2 := by ring
      _ = X - (F D) ^ 2 := by rw [hD]
      _ = X + (F D) ^ 2 - 2 * (F D) ^ 2 := by ring
      _ = X + (F D) ^ 2 := by rw [htwo, zero_mul, sub_zero]
  have hiff := quadratic_coeff_one_iff_power_two (F D) hd0 hquad m
  rw [hFcoeff] at hiff
  by_cases hp : ∃ k : ℕ, m = 2 ^ k
  · have hspecial : specialIndex (m + 1) := hs.mp hp
    have hz : ((coeff m D : ℤ) : ZMod 2) = 1 := hiff.mpr hp
    have hodd : coeff m D % 2 = 1 := by
      have hh := (ZMod.intCast_eq_intCast_iff' (coeff m D) 1 2).mp
        (by simpa using hz)
      omega
    constructor
    · constructor
      · intro _
        exact hspecial
      · intro _
        rw [hcoef]
        change (2 * coeff m D) % 4 = (2 : ℤ) % 4
        omega
    · intro hnot
      exact False.elim (hnot hspecial)
  · have hnot : ¬ specialIndex (m + 1) := fun h => hp (hs.mpr h)
    have hz : ((coeff m D : ℤ) : ZMod 2) = 0 := by
      have hne : ((coeff m D : ℤ) : ZMod 2) ≠ 1 := fun h => hp (hiff.mp h)
      generalize ((coeff m D : ℤ) : ZMod 2) = x at hne ⊢
      revert x
      decide
    have heven : (2 : ℤ) ∣ coeff m D :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff m D) 2).mp hz
    obtain ⟨q, hq⟩ := heven
    have hmul : coeff (m + 1) A = 4 * q := by
      rw [hcoef, hq]
      ring
    constructor
    · constructor
      · intro hmod
        rw [hmul] at hmod
        change (4 * q) % 4 = (2 : ℤ) % 4 at hmod
        omega
      · intro hspecial
        exact False.elim (hnot hspecial)
    · intro _
      exact ⟨q, hmul⟩
