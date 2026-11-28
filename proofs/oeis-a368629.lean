import OMAStatements.S_oeis_a368629
import Mathlib

open OMA.S_oeis_a368629
open PowerSeries

namespace P368629

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

theorem c4_eq (A : PowerSeries ℤ) (n : ℕ) :
    coeff n (A ^ 4) = ∑ p ∈ antidiagonal n, coeff p.1 (A ^ 2) * coeff p.2 (A ^ 2) := by
  rw [show A ^ 4 = A ^ 2 * A ^ 2 by ring, coeff_mul]

theorem c2_eq (A : PowerSeries ℤ) (n : ℕ) :
    coeff n (A ^ 2) = ∑ p ∈ antidiagonal n, coeff p.1 A * coeff p.2 A := by
  rw [pow_two, coeff_mul]

theorem coeff_two_mul (A : PowerSeries ℤ) (n : ℕ) : coeff n (2 * A) = 2 * coeff n A := by
  rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp, coeff_C_mul]

theorem coeff_rhs (A : PowerSeries ℤ) (n : ℕ) :
    coeff (n + 1) (2 + X * (A ^ 2 + (rescale (-1 : ℤ) A) ^ 2) + X * (A ^ 4 - (rescale (-1 : ℤ) A) ^ 4))
      = coeff n (A ^ 2) + (-1) ^ n * coeff n (A ^ 2) + (coeff n (A ^ 4) - (-1) ^ n * coeff n (A ^ 4)) := by
  rw [← map_pow, ← map_pow, map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, map_add, map_sub,
    coeff_rescale, coeff_rescale, show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp, coeff_C]
  simp

theorem coeff_rel (A : PowerSeries ℤ) (h : IsGF A) (n : ℕ) :
    coeff (n + 1) A = if Even n then coeff n (A ^ 2) else coeff n (A ^ 4) := by
  have e := congrArg (coeff (n + 1)) h
  rw [coeff_two_mul, coeff_rhs] at e
  split_ifs with he
  · rw [he.neg_one_pow] at e; linarith
  · rw [(Nat.not_even_iff_odd.mp he).neg_one_pow] at e; linarith

theorem coeff_zero_eq (A : PowerSeries ℤ) (h : IsGF A) : coeff 0 A = 1 := by
  have e := congrArg (coeff 0) h
  rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp] at e
  rw [coeff_C_mul, map_add, map_add, coeff_C, coeff_zero_X_mul, coeff_zero_X_mul, if_pos rfl] at e
  linarith

theorem parity (A : PowerSeries ℤ) (h : IsGF A) :
    ∀ n, Odd (coeff n A) ↔ ∃ k, n + 1 = 2 ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => exact ⟨fun _ => ⟨0, rfl⟩, fun _ => by rw [coeff_zero_eq A h]; decide⟩
    | succ n =>
      rw [coeff_rel A h n, ← ZMod.intCast_eq_one_iff_odd]
      split_ifs with he
      · rw [c2_eq]
        push_cast
        rw [sym (fun i => ((coeff i A : ℤ) : ZMod 2)) n, if_pos he]
        obtain ⟨m, rfl⟩ := he
        have hm : (m + m) / 2 = m := by omega
        rw [hm, ← Int.cast_mul, ZMod.intCast_eq_one_iff_odd, Int.odd_mul, and_self,
          ih m (by omega)]
        constructor
        · rintro ⟨k, hk⟩; exact ⟨k + 1, by rw [pow_succ]; omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => simp at hk
          | succ k => exact ⟨k, by rw [pow_succ] at hk; omega⟩
      · rw [c4_eq]
        push_cast
        rw [sym (fun i => ((coeff i (A ^ 2) : ℤ) : ZMod 2)) n, if_neg he]
        simp only [zero_ne_one, false_iff]
        rintro ⟨k, hk⟩
        apply he
        cases k with
        | zero => simp at hk
        | succ k =>
          exact ⟨2 ^ k - 1, by rw [pow_succ] at hk; have := Nat.one_le_two_pow (n := k); omega⟩

def b : ℕ → ℤ
  | 0 => 1
  | n + 1 => if n % 2 = 0 then ∑ i : Fin (n + 1), b i * b (n - i)
      else ∑ i : Fin (n + 1), (∑ j : Fin (i + 1), b j * b (i - j)) *
        (∑ j : Fin (n - i + 1), b j * b (n - i - j))
decreasing_by
  all_goals first
    | (have := i.isLt; have := j.isLt; omega)
    | (have := i.isLt; omega)

theorem fin_sum (f : ℕ → ℤ) (m : ℕ) :
    ∑ p ∈ antidiagonal m, f p.1 * f p.2 = ∑ i : Fin (m + 1), f i * f (m - i) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Fin.sum_univ_eq_sum_range (fun i => f i * f (m - i))]

theorem exists_gf : ∃ A, IsGF A := by
  refine ⟨mk b, ?_⟩
  unfold IsGF
  ext n
  cases n with
  | zero =>
    rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) by simp]
    rw [coeff_C_mul, map_add, map_add, coeff_C, coeff_zero_X_mul, coeff_zero_X_mul, if_pos rfl,
      coeff_mk, b]
    ring
  | succ n =>
    rw [coeff_two_mul]
    rw [coeff_rhs, c4_eq, c2_eq, coeff_mk]
    have hc2 : ∀ m, coeff m (mk b ^ 2) = ∑ i : Fin (m + 1), b i * b (m - i) := by
      intro m; rw [c2_eq]; simp only [coeff_mk]; exact fin_sum b m
    simp only [coeff_mk, hc2]
    rw [fin_sum b n, fin_sum (fun m => ∑ i : Fin (m + 1), b i * b (m - i)) n, b]
    split_ifs with hn
    · rw [(Nat.even_iff.mpr hn).neg_one_pow]; ring
    · rw [(Nat.odd_iff.mpr (by omega)).neg_one_pow]; ring

end P368629

theorem OMA.solution : type_of% @OMA.S_oeis_a368629.main := by
  refine ⟨P368629.exists_gf, fun A h n => ?_⟩
  rw [P368629.parity A h n]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by omega⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by have := Nat.one_le_two_pow (n := k); omega⟩
