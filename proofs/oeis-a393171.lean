import OMAStatements.S_oeis_a393171

/-
SPDX-License-Identifier: Apache-2.0

The parity lemmas are adapted from dvgyl/oeis-proofs, revision
55ad2bd4804b6bcefeeb6c21eb06eac8b09c45d8, licensed under Apache 2.0.
Original formalization: OpenAI ChatGPT for Dev D. Goyal.
Modified here to use an arbitrary quadratic series and the pinned Mathlib.
The fixed-point uniqueness and direct mod-eight verification are new code.
See the accompanying Apache-2.0-LICENSE.txt.
-/

namespace A393171Proof

open PowerSeries OMA.S_oeis_a393171

lemma fixed_unique {R : Type*} [CommRing R]
    (C H F G : PowerSeries R)
    (hC : constantCoeff C = 0)
    (hF0 : constantCoeff F = 0) (hG0 : constantCoeff G = 0)
    (hF : F = H + (F.subst C) ^ 2)
    (hG : G = H + (G.subst C) ^ 2) : F = G := by
  have hc : HasSubst C := HasSubst.of_constantCoeff_zero hC
  have hx : (X : PowerSeries R) ∣ C := X_dvd_iff.mpr hC
  have hf : constantCoeff (F.subst C) = 0 :=
    constantCoeff_subst_eq_zero hC F hF0
  have hg : constantCoeff (G.subst C) = 0 :=
    constantCoeff_subst_eq_zero hC G hG0
  have hd : F - G = (F.subst C - G.subst C) * (F.subst C + G.subst C) := by
    calc
      F - G = (H + (F.subst C) ^ 2) - (H + (G.subst C) ^ 2) :=
        congrArg₂ (fun a b : PowerSeries R => a - b) hF hG
      _ = _ := by ring
  have hn : ∀ n : ℕ, (X : PowerSeries R) ^ n ∣ F - G := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hsub : (X : PowerSeries R) ^ n ∣ F.subst C - G.subst C := by
        obtain ⟨Q, hQ⟩ := ih
        rw [← subst_sub hc, hQ, subst_mul hc, subst_pow hc, subst_X hc]
        exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hx n) _
      have hsum : (X : PowerSeries R) ∣ F.subst C + G.subst C := by
        apply X_dvd_iff.mpr
        rw [map_add, hf, hg, add_zero]
      rw [hd, pow_succ]
      exact mul_dvd_mul hsub hsum
  ext n
  have hzero := X_pow_dvd_iff.mp (hn (n + 1)) n (Nat.lt_succ_self n)
  simpa only [map_sub, sub_eq_zero] using hzero

theorem candidate_constant (P : PowerSeries (ZMod 8))
    (hP0 : constantCoeff P = 0) :
    constantCoeff (X + X ^ 2 + 4 * (P - X - X * P)) = 0 := by
  simp [hP0]

theorem candidate_fixed (P : PowerSeries (ZMod 8))
    (hP0 : constantCoeff P = 0) (hP : P = X + P ^ 2) :
    X + X ^ 2 + 4 * (P - X - X * P) =
      X + ((X + X ^ 2 + 4 * (P - X - X * P)).subst P) ^ 2 := by
  have hs : HasSubst P := HasSubst.of_constantCoeff_zero' hP0
  have h8 : (8 : PowerSeries (ZMod 8)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (PowerSeries.C (R := ZMod 8)) (by decide : (8 : ZMod 8) = 0)
  rw [← coe_substAlgHom hs]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, substAlgHom_X]
  let Q := (substAlgHom hs) P - P - P * (substAlgHom hs) P
  change X + X ^ 2 + 4 * (P - X - X * P) = X + (P + P ^ 2 + 4 * Q) ^ 2
  have he : (P + P ^ 2 + 4 * Q) ^ 2 = (P + P ^ 2) ^ 2 := by
    calc
      (P + P ^ 2 + 4 * Q) ^ 2 =
          (P + P ^ 2) ^ 2 + 8 * ((P + P ^ 2) * Q + 2 * Q ^ 2) := by ring
      _ = (P + P ^ 2) ^ 2 := by rw [h8, zero_mul, add_zero]
  rw [he]
  linear_combination (P ^ 2 + 3 * P + 4 - X) * hP

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

theorem no_adjacent_powers (n : ℕ) (hn : 2<n) :
    ¬((∃ k : ℕ, n=2^k) ∧ (∃ k : ℕ, n-1=2^k)) := by
  rintro ⟨⟨k,hk⟩,⟨l,hl⟩⟩
  cases k with
  | zero => simp only [pow_zero] at hk; omega
  | succ k =>
    cases l with
    | zero => simp only [pow_zero] at hl; omega
    | succ l =>
      rw [pow_succ] at hk hl
      omega

theorem power_or_next (n : ℕ) (hn : 2<n) :
    ((∃ k : ℕ, n=2^k) ∨ (∃ k : ℕ, n-1=2^k)) ↔
      ∃ k : ℕ, 1≤k ∧ (n=2^k ∨ n=2^k+1) := by
  constructor
  · rintro (⟨k,hk⟩ | ⟨k,hk⟩)
    · refine ⟨k,?_,Or.inl hk⟩
      cases k with
      | zero => simp only [pow_zero] at hk; omega
      | succ k => omega
    · refine ⟨k,?_,Or.inr (by omega)⟩
      cases k with
      | zero => simp only [pow_zero] at hk; omega
      | succ k => omega
  · rintro ⟨k,_,hk | hk⟩
    · exact Or.inl ⟨k,hk⟩
    · exact Or.inr ⟨k,by omega⟩

theorem catalan_adjacent_parity (A : PowerSeries (ZMod 2))
    (h0 : coeff 0 A = 0) (hquad : A = X + A^2) (n : ℕ) (hn : 2<n) :
    coeff n A - coeff (n-1) A = 1 ↔
      ∃ k : ℕ, 1≤k ∧ (n=2^k ∨ n=2^k+1) := by
  have hf : ∀ u v : ZMod 2, (u-v=1 ↔ ((u=1 ∨ v=1) ∧ ¬(u=1 ∧ v=1))) := by decide
  rw [hf, quadratic_coeff_one_iff_power_two A h0 hquad,
    quadratic_coeff_one_iff_power_two A h0 hquad,
    and_iff_left (no_adjacent_powers n hn)]
  exact power_or_next n hn

lemma catalan_zero : constantCoeff catalanGF = 0 := by
  simp [catalanGF]

lemma catalan_equation : catalanGF = X + catalanGF ^ 2 := by
  have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    PowerSeries.catalanSeries_sq_mul_X_add_one
  simp only [map_add, map_mul, map_pow, PowerSeries.map_X, map_one] at h
  dsimp only [catalanGF]
  linear_combination -(X : PowerSeries ℤ) * h

lemma mapped_equation (A : PowerSeries ℤ)
    (he : A = X + (A.subst catalanGF)^2) :
    PowerSeries.map (Int.castRingHom (ZMod 8)) A = X +
      ((PowerSeries.map (Int.castRingHom (ZMod 8)) A).subst
      (PowerSeries.map (Int.castRingHom (ZMod 8)) catalanGF))^2 := by
  have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 8))) he
  have hs : PowerSeries.map (Int.castRingHom (ZMod 8)) (A.subst catalanGF) =
      (PowerSeries.map (Int.castRingHom (ZMod 8)) A).subst
        (PowerSeries.map (Int.castRingHom (ZMod 8)) catalanGF) :=
    PowerSeries.map_subst (HasSubst.of_constantCoeff_zero' catalan_zero) A
  simpa only [map_add, map_pow, PowerSeries.map_X, hs] using h

def reduce : ZMod 8 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)

lemma four_residue (u : ZMod 8) :
    (4 * u = 4 ↔ reduce u = 1) ∧ (4 * u = 0 ↔ reduce u ≠ 1) := by
  exact (by decide : ∀ u : ZMod 8,
    (4 * u = 4 ↔ reduce u = 1) ∧ (4 * u = 0 ↔ reduce u ≠ 1)) u

lemma candidate_coeff (P : PowerSeries (ZMod 8)) (n : ℕ) (hn : 2 < n) :
    coeff n (X + X ^ 2 + 4 * (P - X - X * P)) =
      4 * (coeff n P - coeff (n - 1) P) := by
  have hfour (U : PowerSeries (ZMod 8)) : coeff n (4 * U) = 4 * coeff n U := by
    have he : (4 : PowerSeries (ZMod 8)) * U = U + U + U + U := by ring
    rw [he]
    simp only [map_add]
    ring
  have hx : coeff n (X * P) = coeff (n - 1) P := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using coeff_succ_X_mul (n - 1) P
  simp only [map_add, map_sub, hfour, coeff_X, coeff_X_pow,
    if_neg (by omega : n ≠ 1), if_neg (by omega : n ≠ 2), zero_add, sub_zero, hx]

lemma mod_eight (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (he : A = X + (A.subst catalanGF)^2) :
    PowerSeries.map (Int.castRingHom (ZMod 8)) A =
      X + X^2 + 4 * (PowerSeries.map (Int.castRingHom (ZMod 8)) catalanGF - X -
        X * PowerSeries.map (Int.castRingHom (ZMod 8)) catalanGF) := by
  let P := PowerSeries.map (Int.castRingHom (ZMod 8)) catalanGF
  have hp0 : constantCoeff P = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [P, coeff_map, coeff_zero_eq_constantCoeff, catalan_zero, map_zero]
  have hp : P = X + P^2 := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 8))) catalan_equation
    simpa only [map_add, map_pow, PowerSeries.map_X] using h
  exact fixed_unique P X _ _ hp0 (by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [coeff_map, coeff_zero_eq_constantCoeff, h0, map_zero])
    (candidate_constant P hp0) (mapped_equation A he) (candidate_fixed P hp0 hp)

lemma residue (A : PowerSeries ℤ) (h0 : constantCoeff A = 0)
    (he : A = X + (A.subst catalanGF)^2) (n : ℕ) (hn : 2 < n) :
    (((coeff n A : ℤ) : ZMod 8) = 4 ↔ specialIndex n) ∧
    (((coeff n A : ℤ) : ZMod 8) = 0 ↔ ¬ specialIndex n) := by
  let P := PowerSeries.map (Int.castRingHom (ZMod 8)) catalanGF
  let Q := PowerSeries.map reduce P
  have hp0 : constantCoeff P = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [P, coeff_map, coeff_zero_eq_constantCoeff, catalan_zero, map_zero]
  have hp : P = X + P^2 := by
    have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 8))) catalan_equation
    simpa only [map_add, map_pow, PowerSeries.map_X] using h
  have hq0 : coeff 0 Q = 0 := by
    simp only [Q, coeff_map, coeff_zero_eq_constantCoeff, hp0, map_zero]
  have hq : Q = X + Q^2 := by
    have h := congrArg (PowerSeries.map reduce) hp
    simpa only [map_add, map_pow, PowerSeries.map_X] using h
  have hm := congrArg (coeff n) (mod_eight A h0 he)
  rw [coeff_map, candidate_coeff _ n hn] at hm
  change ((coeff n A : ℤ) : ZMod 8) = 4 * (coeff n P - coeff (n - 1) P) at hm
  rw [hm]
  have hd := four_residue (coeff n P - coeff (n - 1) P)
  have hs := catalan_adjacent_parity Q hq0 hq n hn
  have hr (m : ℕ) : reduce (coeff m P) = coeff m Q := (coeff_map reduce m P).symm
  rw [map_sub, hr n, hr (n - 1)] at hd
  exact ⟨hd.1.trans hs, hd.2.trans (not_congr hs)⟩

end A393171Proof

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a393171.main := by
  intro A h0 he n hn
  have h := A393171Proof.residue A h0 he n hn
  constructor
  · exact (ZMod.intCast_eq_intCast_iff (coeff n A) 4 8).symm.trans (by simpa using h.1)
  · intro hs
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (coeff n A) 8).mp (h.2.mpr hs)
