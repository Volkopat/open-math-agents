import OMAStatements.S_oeis_a368633
import Mathlib

open OMA.S_oeis_a368633
open PowerSeries

namespace P368633

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

theorem coeff_rel (A : PowerSeries ℤ) (h : IsGF A) (n : ℕ) :
    coeff (n + 1) A = (2 - (-1) ^ n) * ∑ p ∈ antidiagonal n, coeff p.1 A * coeff p.2 A := by
  conv_lhs => rw [h]
  rw [← map_pow, map_sub, map_add, mul_assoc, coeff_succ_X_mul, coeff_rescale,
    show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp, coeff_C_mul, coeff_succ_X_mul, pow_two, coeff_mul]
  simp
  ring

theorem coeff_zero_eq (A : PowerSeries ℤ) (h : IsGF A) : coeff 0 A = 1 := by
  conv_lhs => rw [h]
  simp [mul_assoc]

theorem parity (A : PowerSeries ℤ) (h : IsGF A) :
    ∀ n, Odd (coeff n A) ↔ ∃ k, n + 1 = 2 ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => exact ⟨fun _ => ⟨0, rfl⟩, fun _ => by rw [coeff_zero_eq A h]; decide⟩
    | succ n =>
      rw [coeff_rel A h n]
      have hodd : Odd ((2 : ℤ) - (-1) ^ n) := by
        rcases neg_one_pow_eq_or ℤ n with h1 | h1 <;> rw [h1] <;> decide
      rw [Int.odd_mul, and_iff_right hodd, ← ZMod.intCast_eq_one_iff_odd]
      push_cast
      rw [sym (fun i => ((coeff i A : ℤ) : ZMod 2)) n]
      split_ifs with he
      · obtain ⟨m, rfl⟩ := he
        have hm : (m + m) / 2 = m := by omega
        rw [hm, ← Int.cast_mul, ZMod.intCast_eq_one_iff_odd, Int.odd_mul, and_self,
          ih m (by omega)]
        constructor
        · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
      · simp only [zero_ne_one, false_iff]
        rintro ⟨k, hk⟩
        apply he
        cases k with
        | zero => simp at hk
        | succ k => exact ⟨2 ^ k - 1, by rw [pow_succ] at hk; have := Nat.one_le_two_pow (n := k); omega⟩

def b : ℕ → ℤ
  | 0 => 1
  | n + 1 => (2 - (-1) ^ n) * ∑ i : Fin (n + 1), b i * b (n - i)
decreasing_by all_goals (have := i.isLt; omega)

theorem exists_gf : ∃ A, IsGF A := by
  refine ⟨mk b, ?_⟩
  unfold IsGF
  ext n
  cases n with
  | zero => simp [mul_assoc, b]
  | succ n =>
    rw [← map_pow, map_sub, map_add, mul_assoc, coeff_succ_X_mul, coeff_rescale,
      show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp, coeff_C_mul, coeff_succ_X_mul, pow_two,
      coeff_mul]
    simp only [coeff_mk, coeff_one, Nat.succ_ne_zero, if_false, zero_add]
    rw [b, Fin.sum_univ_eq_sum_range (fun i => b i * b (n - i)),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    ring

end P368633

theorem OMA.solution : type_of% @OMA.S_oeis_a368633.main := by
  refine ⟨P368633.exists_gf, fun A h n => ?_⟩
  rw [P368633.parity A h n]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by have := Nat.one_le_two_pow (n := k); omega⟩
