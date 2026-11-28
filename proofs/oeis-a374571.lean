import OMAStatements.S_oeis_a374571
import Mathlib

open OMA.S_oeis_a374571
open PowerSeries

namespace P374571

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

theorem coeff_S (A : PowerSeries ℤ) (n : ℕ) :
    coeff n (A.subst ((X : PowerSeries ℤ) ^ 2)) = if 2 ∣ n then coeff (n / 2) A else 0 := by
  rw [coeff_subst_X_pow (by norm_num)]; simp

theorem S_sq (A : PowerSeries ℤ) :
    (A.subst ((X : PowerSeries ℤ) ^ 2)) ^ 2 = (A ^ 2).subst ((X : PowerSeries ℤ) ^ 2) := by
  rw [← expand_apply 2 (by norm_num), ← expand_apply 2 (by norm_num), map_pow]

theorem coeff_even (A : PowerSeries ℤ) (h : IsGF A) (k : ℕ) :
    coeff (2 * k) A = coeff k A := by
  conv_lhs => rw [h.2]
  rw [map_sub, coeff_S, if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ (by norm_num)]
  rcases k with _ | k
  · simp
  · rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, coeff_succ_X_mul, S_sq, coeff_S,
      if_neg (by omega)]
    simp

theorem coeff_odd (A : PowerSeries ℤ) (h : IsGF A) (k : ℕ) :
    coeff (2 * k + 1) A = -∑ p ∈ antidiagonal k, coeff p.1 A * coeff p.2 A := by
  conv_lhs => rw [h.2]
  rw [map_sub, coeff_S, if_neg (by omega), coeff_succ_X_mul, S_sq, coeff_S,
    if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ (by norm_num), pow_two, coeff_mul]
  simp

theorem fib_iff (n : ℕ) : Fibbinary n ↔
    ¬ (n.testBit 0 = true ∧ n.testBit 1 = true) ∧ Fibbinary (n / 2) := by
  unfold Fibbinary
  constructor
  · intro H
    refine ⟨H 0, fun i => ?_⟩
    have := H (i + 1)
    rwa [Nat.testBit_add_one, Nat.testBit_add_one n (i + 1)] at this
  · rintro ⟨H0, H⟩ i
    rcases i with _ | i
    · exact H0
    · rw [Nat.testBit_add_one, Nat.testBit_add_one n (i + 1)]
      exact H i

theorem fib_even (k : ℕ) : Fibbinary (2 * k) ↔ Fibbinary k := by
  rw [fib_iff, Nat.mul_div_cancel_left _ (by norm_num), Nat.testBit_zero]
  simp

theorem fib_odd (k : ℕ) : Fibbinary (2 * k + 1) ↔ Even k ∧ Fibbinary k := by
  rw [fib_iff, show (2 * k + 1) / 2 = k by omega, Nat.testBit_zero, Nat.testBit_add_one,
    show (2 * k + 1) / 2 = k by omega, Nat.testBit_zero]
  simp only [decide_eq_true_eq, Nat.even_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

theorem parity (A : PowerSeries ℤ) (h : IsGF A) :
    ∀ n, Odd (coeff n A) ↔ Fibbinary n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
    · rcases k with _ | k
      · have h0 : coeff 0 A = 1 := by rw [coeff_zero_eq_constantCoeff_apply, h.1]
        rw [h0]
        refine ⟨fun _ => ?_, fun _ => odd_one⟩
        intro i; simp
      · rw [coeff_even A h, fib_even]
        exact ih _ (by omega)
    · rw [coeff_odd A h, fib_odd, odd_neg, ← ZMod.intCast_eq_one_iff_odd]
      push_cast
      rw [sym (fun i => ((coeff i A : ℤ) : ZMod 2)) k]
      split_ifs with he
      · obtain ⟨m, rfl⟩ := he
        have hm : (m + m) / 2 = m := by omega
        rw [hm, ← Int.cast_mul, ZMod.intCast_eq_one_iff_odd, Int.odd_mul, and_self,
          show m + m = 2 * m by ring, ← coeff_even A h m, ih (2 * m) (by omega)]
        exact ⟨fun h => ⟨even_two_mul m, h⟩, fun h => h.2⟩
      · simp only [zero_ne_one, false_iff]
        rintro ⟨he', _⟩
        exact he he'

def b (n : ℕ) : ℤ :=
  if n = 0 then 1
  else if n % 2 = 0 then b (n / 2)
  else -∑ i : Fin (n / 2 + 1), b i * b (n / 2 - i)
termination_by n
decreasing_by all_goals omega

theorem b_even (k : ℕ) (hk : 0 < k) : b (2 * k) = b k := by
  rw [b, if_neg (by omega), if_pos (by omega), Nat.mul_div_cancel_left _ (by norm_num)]

theorem b_odd (k : ℕ) : b (2 * k + 1) = -∑ p ∈ antidiagonal k, b p.1 * b p.2 := by
  rw [b, if_neg (by omega), if_neg (by omega), show (2 * k + 1) / 2 = k by omega,
    Fin.sum_univ_eq_sum_range (fun i => b i * b (k - i)),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem exists_gf : ∃ A, IsGF A := by
  refine ⟨mk b, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, b, if_pos rfl]
  · ext n
    obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
    · rw [map_sub, coeff_S, if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ (by norm_num)]
      rcases k with _ | k
      · simp
      · rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring, coeff_succ_X_mul, S_sq, coeff_S,
          if_neg (by omega), coeff_mk, coeff_mk, ← show 2 * (k + 1) = (2 * k + 1) + 1 by ring,
          b_even _ (by omega)]
        simp
    · rw [map_sub, coeff_S, if_neg (by omega), coeff_succ_X_mul, S_sq, coeff_S,
        if_pos (dvd_mul_right 2 k), Nat.mul_div_cancel_left _ (by norm_num), pow_two, coeff_mul,
        coeff_mk, b_odd]
      simp

end P374571

theorem OMA.solution : type_of% @OMA.S_oeis_a374571.main :=
  ⟨P374571.exists_gf, fun A h n _ => P374571.parity A h n⟩
