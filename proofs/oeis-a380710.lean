import OMAStatements.S_oeis_a380710
import Mathlib

open OMA.S_oeis_a380710
open PowerSeries

namespace P380710

open Finset

theorem sym (f : ℕ → ZMod 2) (m : ℕ) :
    ∑ p ∈ antidiagonal m, f p.1 * f p.2 = if Even m then f (m / 2) * f (m / 2) else 0 := by
  have key : ∀ s : Finset (ℕ × ℕ), (∀ p ∈ s, p.1 ≠ p.2) → (∀ p ∈ s, p.swap ∈ s) →
      ∑ p ∈ s, f p.1 * f p.2 = 0 := by
    intro s hne hsw
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun p hp => hsw p hp) ?_
    · intro p _
      simp only [Prod.fst_swap, Prod.snd_swap]
      rw [mul_comm (f p.2)]
      exact CharTwo.add_self_eq_zero _
    · intro p hp _ h
      apply hne p hp
      have := congrArg Prod.fst h
      simpa using this.symm
    · intro p _; simp
  split_ifs with he
  · obtain ⟨k, rfl⟩ := he
    have hk : (k + k) / 2 = k := by omega
    rw [hk]
    have hmem : (k, k) ∈ antidiagonal (k + k) := by simp
    rw [← Finset.add_sum_erase _ _ hmem]
    rw [key, add_zero]
    · intro p hp
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
      intro h
      apply hp.1
      ext <;> simp <;> omega
    · intro p hp
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      refine ⟨?_, by simp; omega⟩
      intro h
      apply hp.1
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp at h1 h2
      ext <;> simp <;> omega
  · apply key
    · intro p hp h
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      apply he
      exact ⟨p.1, by omega⟩
    · intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      simp; omega

abbrev φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)

theorem map_abs (F : PowerSeries ℤ) : map φ (absPS F) = map φ F := by
  ext n
  simp only [coeff_map, absPS, coeff_mk]
  rcases abs_choice (coeff n F) with h | h <;> rw [h]
  simp [ZMod.neg_eq_self_mod_two]

theorem sq_rel (A : PowerSeries ℤ) (h : IsGF A) :
    (map φ A) ^ 2 = map φ A + X := by
  obtain ⟨B, hB, hA⟩ := h
  have h1 : (map φ A) ^ 2 * map φ B = 1 := by rw [← map_pow, ← map_mul, hB, map_one]
  have h2 : map φ A = 1 + X * map φ A * map φ B := by
    conv_lhs => rw [hA]
    rw [map_add, map_mul, map_mul, map_abs, map_one, map_X]
  calc (map φ A) ^ 2 = map φ A * map φ A := by ring
    _ = map φ A * (1 + X * map φ A * map φ B) := by rw [← h2]
    _ = map φ A + X * ((map φ A) ^ 2 * map φ B) := by ring
    _ = map φ A + X := by rw [h1, mul_one]

theorem coeff_zero_eq (A : PowerSeries ℤ) (h : IsGF A) : coeff 0 A = 1 := by
  obtain ⟨B, _, hA⟩ := h
  conv_lhs => rw [hA]
  simp [mul_assoc]

theorem rel (A : PowerSeries ℤ) (h : IsGF A) (n : ℕ) :
    ((coeff n A : ℤ) : ZMod 2) =
      (if Even n then ((coeff (n / 2) A : ℤ) : ZMod 2) else 0) + (if n = 1 then 1 else 0) := by
  have e := congrArg (coeff n) (sq_rel A h)
  rw [pow_two, coeff_mul, map_add, coeff_X] at e
  simp only [coeff_map] at e
  rw [sym (fun i => φ (coeff i A)) n] at e
  have hx : ∀ x : ZMod 2, x * x = x := by decide
  simp only [φ, Int.coe_castRingHom, hx] at e
  have e2 : ((coeff n A : ℤ) : ZMod 2) =
      (if Even n then ((coeff (n / 2) A : ℤ) : ZMod 2) else 0) - (if n = 1 then 1 else 0) := by
    rw [e]; ring
  rw [e2, sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

theorem parity (A : PowerSeries ℤ) (h : IsGF A) :
    ∀ n, 0 < n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [← ZMod.intCast_eq_one_iff_odd, rel A h n]
    obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
    · have hm : 0 < m := by omega
      rw [if_pos (even_two_mul m), if_neg (by omega), add_zero,
        Nat.mul_div_cancel_left _ (by norm_num), ZMod.intCast_eq_one_iff_odd, ih m (by omega) hm]
      constructor
      · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨k, hk⟩
        rcases k with _ | k
        · simp at hk
        · exact ⟨k, by rw [pow_succ] at hk; omega⟩
    · rw [if_neg (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one m), zero_add]
      rcases m with _ | m
      · simp
        exact ⟨0, rfl⟩
      · rw [if_neg (by omega)]
        simp only [zero_ne_one, false_iff]
        rintro ⟨k, hk⟩
        rcases k with _ | k
        · simp at hk
        · rw [pow_succ] at hk; omega

def c : ℕ → ℤ
  | 0 => 1
  | n + 1 => -|∑ i : Fin (n + 1), c i * c (n - i)|
decreasing_by all_goals (have := i.isLt; omega)

theorem D_eq : PowerSeries.mk c = 1 - X * absPS ((PowerSeries.mk c) ^ 2) := by
  ext n
  rcases n with _ | n
  · simp [c]
  · rw [map_sub, coeff_succ_X_mul, absPS, coeff_mk, coeff_mk, pow_two, coeff_mul, c,
      Fin.sum_univ_eq_sum_range (fun i => c i * c (n - i)),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp

theorem exists_gf : ∃ A, IsGF A := by
  have hc : constantCoeff (PowerSeries.mk c) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]; simp [c]
  set A := invOfUnit (PowerSeries.mk c) 1 with hAdef
  have hAD : A * PowerSeries.mk c = 1 := by
    rw [mul_comm]; exact mul_invOfUnit (PowerSeries.mk c) 1 (by rw [hc]; rfl)
  refine ⟨A, (PowerSeries.mk c) ^ 2, ?_, ?_⟩
  · rw [← mul_pow, hAD, one_pow]
  · have := congrArg (A * ·) D_eq
    rw [hAD, mul_sub, mul_one] at this
    linear_combination -this

end P380710

theorem OMA.solution : type_of% @OMA.S_oeis_a380710.main :=
  ⟨P380710.exists_gf, fun A h n hn => P380710.parity A h n hn⟩
