import OMAStatements.S_oeis_a202943
import Mathlib

open OMA.S_oeis_a202943
open PowerSeries

namespace P202943

abbrev R2 := ZMod 2

theorem two_eq : (2 : R2) = 0 := rfl

theorem h2 : (2 : PowerSeries R2) = 0 := by
  rw [show (2 : PowerSeries R2) = C 2 from (map_ofNat C 2).symm, two_eq, map_zero]

theorem sq_coeff (B : PowerSeries R2) (n : ℕ) :
    coeff n (B ^ 2) = if n % 2 = 0 then coeff (n / 2) B else 0 := by
  rw [sq, coeff_mul]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hmem : (m, m) ∈ Finset.HasAntidiagonal.antidiagonal (2 * m) := by simp; ring
    rw [← Finset.add_sum_erase _ _ hmem]
    have hz : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (2 * m)).erase (m, m), coeff x.1 B * coeff x.2 B = 0 := by
      apply Finset.sum_involution (fun x _ => (x.2, x.1))
      · intro a _
        rw [mul_comm (coeff a.2 B), ← two_mul, two_eq, zero_mul]
      · intro a ha _ heq
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        have e1 := congrArg Prod.fst heq
        have e2 := congrArg Prod.snd heq
        simp only at e1 e2
        apply ha.1
        ext <;> simp <;> omega
      · intro a ha
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at ha ⊢
        refine ⟨fun h => ha.1 (by ext <;> simp <;> omega), by omega⟩
      · intro a _; rfl
    rw [hz, add_zero, show 2 * m / 2 = m by omega]
    have : ∀ x : ZMod 2, x * x = x := by decide
    exact this _
  · apply Finset.sum_involution (fun x _ => (x.2, x.1))
    · intro a _
      rw [mul_comm (coeff a.2 B), ← two_mul, two_eq, zero_mul]
    · intro a ha _ heq
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
      have e1 := congrArg Prod.fst heq
      have e2 := congrArg Prod.snd heq
      simp only at e1 e2
      omega
    · intro a ha
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp only; omega)
    · intro a _; rfl

theorem frob (F : PowerSeries R2) : F ^ 2 = expand 2 (by norm_num) F := by
  ext n
  rw [sq_coeff, coeff_expand]
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem mdb_succ (n : ℕ) : IsMoserDeBruijn n ↔ (n % 4 = 0 ∨ n % 4 = 1) ∧ IsMoserDeBruijn (n / 4) := by
  unfold IsMoserDeBruijn
  constructor
  · intro h
    refine ⟨by have := h 0; simp at this; omega, fun k => ?_⟩
    have := h (k + 1)
    rwa [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by ring, pow_add, ← Nat.div_div_eq_div_mul] at this
  · rintro ⟨h0, h⟩ k
    rcases k with _ | k
    · simp; omega
    · rw [show 2 * (k + 1) + 1 = 2 + (2 * k + 1) by ring, pow_add, ← Nat.div_div_eq_div_mul]; exact h k

open Classical in
noncomputable def M : PowerSeries R2 := mk fun n => if IsMoserDeBruijn n then 1 else 0

theorem M0 : constantCoeff M = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp only [M, coeff_mk]
  rw [if_pos]
  intro k; simp

theorem M_eq : M = (1 + X) * expand 4 (by norm_num) M := by
  ext n
  rw [add_mul, one_mul, map_add]
  rcases n with _ | n
  · simp only [coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul, add_zero,
      constantCoeff_expand, M0]
  · rw [coeff_succ_X_mul, coeff_expand, coeff_expand]
    simp only [M, coeff_mk]
    rw [mdb_succ (n + 1)]
    have key : ∀ (c : Prop) [Decidable c] (P Q : Prop) [Decidable P] [Decidable Q], (P ↔ c ∧ Q) →
        ((if P then (1 : R2) else 0) = if c then (if Q then 1 else 0) else 0) := by
      intro c _ P Q _ _ h
      by_cases hc : c <;> by_cases hq : Q <;> simp_all
    rcases (by omega : (n + 1) % 4 = 0 ∨ (n + 1) % 4 = 1 ∨ (n + 1) % 4 = 2 ∨ (n + 1) % 4 = 3) with h | h | h | h
    · rw [if_pos (show 4 ∣ n + 1 by omega), if_neg (show ¬ 4 ∣ n by omega), add_zero]
      by_cases hD : IsMoserDeBruijn ((n + 1) / 4)
      · rw [if_pos ⟨Or.inl h, hD⟩, if_pos hD]
      · rw [if_neg (fun hh => hD hh.2), if_neg hD]
    · rw [if_neg (show ¬ 4 ∣ n + 1 by omega), if_pos (show 4 ∣ n by omega), zero_add,
        show n / 4 = (n + 1) / 4 by omega]
      by_cases hD : IsMoserDeBruijn ((n + 1) / 4)
      · rw [if_pos ⟨Or.inr h, hD⟩, if_pos hD]
      · rw [if_neg (fun hh => hD hh.2), if_neg hD]
    · rw [if_neg (show ¬ 4 ∣ n + 1 by omega), if_neg (show ¬ 4 ∣ n by omega), add_zero,
        if_neg (fun hh => by omega)]
    · rw [if_neg (show ¬ 4 ∣ n + 1 by omega), if_neg (show ¬ 4 ∣ n by omega), add_zero,
        if_neg (fun hh => by omega)]

theorem N_one : M * expand 2 (by norm_num) M * (1 + X) = 1 := by
  set N := M * expand 2 (by norm_num) M * (1 + X) with hN
  have e4 : ∀ F : PowerSeries R2, expand 2 (by norm_num) (expand 4 (by norm_num) F) =
      expand 8 (by norm_num) F := fun F => (expand_mul 2 (by norm_num) 4 (by norm_num) F).symm
  have e44 : ∀ F : PowerSeries R2, expand 4 (by norm_num) (expand 2 (by norm_num) F) =
      expand 8 (by norm_num) F := fun F => (expand_mul 4 (by norm_num) 2 (by norm_num) F).symm
  have hNs : N = expand 4 (by norm_num) N := by
    have a1 : N = (1 + X) ^ 2 * (1 + X ^ 2) * (expand 4 (by norm_num) M * expand 8 (by norm_num) M) := by
      rw [hN]
      nth_rewrite 1 [M_eq]
      nth_rewrite 2 [M_eq]
      rw [map_mul, map_add, map_one, expand_X, e4]
      ring
    have a2 : expand 4 (by norm_num) N = (1 + X ^ 4) * (expand 4 (by norm_num) M * expand 8 (by norm_num) M) := by
      rw [hN, map_mul, map_mul, map_add, map_one, expand_X, e44]
      ring
    rw [a2, a1]
    linear_combination (expand 4 (by norm_num) M * expand 8 (by norm_num) M * (X + X ^ 2 + X ^ 3)) * h2
  have hN0 : constantCoeff N = 1 := by
    rw [hN, map_mul, map_mul, constantCoeff_expand, M0]; simp
  ext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hN0
    · rw [coeff_one, if_neg (by omega), hNs, coeff_expand]
      by_cases hd : 4 ∣ n
      · rw [if_pos hd]
        have := ih (n / 4) (by omega)
        rw [this, coeff_one, if_neg (by omega)]
      · rw [if_neg hd]

end P202943

theorem OMA.solution : type_of% @OMA.S_oeis_a202943.main := by
  classical
  intro A hA hE
  set φ := Int.castRingHom (ZMod 2)
  set B := A.map φ with hBdef
  have hC : (PowerSeries.mk (fun n =>
      if ∃ m : ℕ, IsMoserDeBruijn m ∧ n = 32 * m then (1 : ZMod 2) else 0)) =
      expand 32 (by norm_num) P202943.M := by
    ext n
    rw [coeff_expand, coeff_mk]
    by_cases hd : 32 ∣ n
    · rw [if_pos hd]
      simp only [P202943.M, coeff_mk]
      by_cases hm : IsMoserDeBruijn (n / 32)
      · rw [if_pos hm, if_pos ⟨n / 32, hm, by omega⟩]
      · rw [if_neg hm, if_neg (by rintro ⟨m, hm', rfl⟩; apply hm; rwa [Nat.mul_div_cancel_left _ (by norm_num)])]
    · rw [if_neg hd, if_neg (by rintro ⟨m, -, rfl⟩; exact hd (dvd_mul_right 32 m))]
  rw [hC]
  set C := (1 + X) * (1 + X ^ 2) * (1 + X ^ 8) * expand 32 (by norm_num) P202943.M with hCdef
  have hF : F202943.map φ = 1 + X := by
    ext n
    rw [coeff_map, F202943, coeff_mk, map_add, coeff_one, coeff_X]
    rcases n with _ | _ | n
    · simp [φ]
    · simp [φ]; rfl
    · rw [if_neg (by omega), if_neg (by omega), add_zero]
      have h1 : 1 ≤ (n + 2) * (n + 2 - 1) := by rw [show n + 2 - 1 = n + 1 by omega]; nlinarith
      have : (2 : ℤ) ∣ 2 ^ ((n + 2) * (n + 2 - 1)) := dvd_pow_self 2 (by omega)
      obtain ⟨c, hc⟩ := this
      rw [hc]
      simp [φ, P202943.two_eq]
  have hB3 : B ^ 3 = 1 + X := by rw [hBdef, ← map_pow, hE, hF]
  have hC3 : C ^ 3 = 1 + X := by
    have e64 : expand 32 (by norm_num) (expand 2 (by norm_num) P202943.M) = expand 64 (by norm_num) P202943.M :=
      (expand_mul 32 (by norm_num) 2 (by norm_num) P202943.M).symm
    have e64' : expand 2 (by norm_num) (expand 32 (by norm_num) P202943.M) = expand 64 (by norm_num) P202943.M :=
      (expand_mul 2 (by norm_num) 32 (by norm_num) P202943.M).symm
    have hN := congrArg (expand 32 (by norm_num)) P202943.N_one
    rw [map_mul, map_mul, map_add, map_one, expand_X, e64] at hN
    have hC2 : C ^ 2 = (1 + X ^ 2) * (1 + X ^ 4) * (1 + X ^ 16) * expand 64 (by norm_num) P202943.M := by
      rw [P202943.frob, hCdef, map_mul, map_mul, map_mul, map_add, map_add, map_add, map_one,
        map_pow, map_pow, expand_X, e64']
      ring
    rw [show C ^ 3 = C * C ^ 2 by ring, hC2, hCdef]
    linear_combination (1 + X) * hN + (expand 32 (by norm_num) P202943.M * expand 64 (by norm_num) P202943.M *
      (X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 + X ^ 8 + X ^ 9 + X ^ 10 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14 + X ^ 15 + X ^ 16 + X ^ 17 + X ^ 18 + X ^ 19 + X ^ 20 + X ^ 21 + X ^ 22 + X ^ 23 + X ^ 24 + X ^ 25 + X ^ 26 + X ^ 27 + X ^ 28 + X ^ 29 + X ^ 30 + X ^ 31)) * P202943.h2
  have hBC : B = C := by
    have : (B - C) * (B ^ 2 + B * C + C ^ 2) = 0 := by
      rw [show (B - C) * (B ^ 2 + B * C + C ^ 2) = B ^ 3 - C ^ 3 by ring, hB3, hC3, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have hB0 : constantCoeff B = 1 := by
        rw [hBdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hA]
        simp
      have hC0 : constantCoeff C = 1 := by
        rw [hCdef]; simp [constantCoeff_expand, P202943.M0]
      have := congrArg constantCoeff h
      rw [map_add, map_add, map_mul, map_pow, map_pow, hB0, hC0] at this
      revert this; decide
  exact hBC
