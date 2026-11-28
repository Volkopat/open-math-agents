import OMAStatements.S_oeis_a267872
import Mathlib

namespace A267872
open OMA.S_oeis_a267872

lemma rule_false (l c r : Bool) (h : rule l c r = false) :
    (l = false ∧ c = false) ∨ (c = false ∧ r = false) := by
  revert h
  cases l <;> cases c <;> cases r <;> decide

lemma rule_ttt : rule true true true = true := by decide

lemma state1_iff (x : ℤ) : state 1 x = false ↔ (x = 1 ∨ x = -1) := by
  have hs : state 1 x = rule (decide (x - 1 = 0)) (decide (x = 0)) (decide (x + 1 = 0)) := rfl
  rw [hs]
  by_cases h1 : x = 1
  · subst h1
    constructor
    · intro _; left; rfl
    · intro _; decide
  · by_cases h2 : x = -1
    · subst h2
      constructor
      · intro _; right; rfl
      · intro _; decide
    · by_cases h0 : x = 0
      · subst h0
        constructor
        · intro h; exact absurd h (by decide)
        · intro h; omega
      · have e1 : decide (x - 1 = 0) = false := decide_eq_false (by omega)
        have e2 : decide (x = 0) = false := decide_eq_false h0
        have e3 : decide (x + 1 = 0) = false := decide_eq_false (by omega)
        rw [e1, e2, e3]
        constructor
        · intro h; exact absurd h (by decide)
        · intro h; omega

lemma state2 (x : ℤ) : state 2 x = true := by
  have hs : state 2 x = rule (state 1 (x - 1)) (state 1 x) (state 1 (x + 1)) := rfl
  rw [hs]
  by_contra hne
  have hf : rule (state 1 (x - 1)) (state 1 x) (state 1 (x + 1)) = false := by
    simpa using hne
  rcases rule_false _ _ _ hf with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [state1_iff] at h1 h2
    omega
  · rw [state1_iff] at h1 h2
    omega

lemma state_all (n : ℕ) (x : ℤ) : state (n + 2) x = true := by
  induction n generalizing x with
  | zero => exact state2 x
  | succ n ih =>
    have hs : state (n + 1 + 2) x =
        rule (state (n + 2) (x - 1)) (state (n + 2) x) (state (n + 2) (x + 1)) := rfl
    rw [hs, ih, ih, ih]
    exact rule_ttt

lemma a_ge (n : ℕ) : a (n + 2) = 2 * n + 5 := by
  unfold a
  rw [Finset.filter_true_of_mem (fun x _ => state_all n x), Int.card_Icc]
  push_cast
  omega

lemma a_zero : a 0 = 1 := by
  unfold a
  have h : (Finset.Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).filter (fun x => state 0 x = true) = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      push_cast at h1 h2
      omega
    · rintro rfl
      refine ⟨⟨by simp, by simp⟩, ?_⟩
      decide
  rw [h]
  rfl

lemma a_one : a 1 = 1 := by
  unfold a
  have h : (Finset.Icc (-((1 : ℕ) : ℤ)) ((1 : ℕ) : ℤ)).filter (fun x => state 1 x = true) = {0} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      push_cast at h1 h2
      have h4 : ¬ (x = 1 ∨ x = -1) := by
        rw [← state1_iff]
        simp [h3]
      omega
    · rintro rfl
      refine ⟨⟨by simp, by simp⟩, ?_⟩
      decide
  rw [h]
  rfl

lemma coeff_mk_mul_X (k n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ k) =
      if k ≤ n then (a (n - k) : ℤ) else 0 := by
  simp only [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]

lemma coeff_lhs (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 2) =
      (a n : ℤ) - 2 * (if 1 ≤ n then (a (n - 1) : ℤ) else 0)
        + (if 2 ≤ n then (a (n - 2) : ℤ) else 0) := by
  have expand : PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 2 =
      PowerSeries.mk (fun n => (a n : ℤ))
        - PowerSeries.C 2 * (PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 1)
        + PowerSeries.mk (fun n => (a n : ℤ)) * PowerSeries.X ^ 2 := by
    simp only [map_ofNat, pow_one]
    ring
  rw [expand]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_mk_mul_X]
  simp only [PowerSeries.coeff_mk]

lemma coeff_rhs (n : ℕ) :
    PowerSeries.coeff n ((1 : PowerSeries ℤ) - PowerSeries.X + 4 * PowerSeries.X ^ 2
        - 2 * PowerSeries.X ^ 3) =
      (if n = 0 then 1 else 0) - (if n = 1 then 1 else 0) + 4 * (if n = 2 then 1 else 0)
        - 2 * (if n = 3 then 1 else 0) := by
  have expand : ((1 : PowerSeries ℤ) - PowerSeries.X + 4 * PowerSeries.X ^ 2
        - 2 * PowerSeries.X ^ 3) =
      PowerSeries.X ^ 0 - PowerSeries.X ^ 1 + PowerSeries.C 4 * PowerSeries.X ^ 2
        - PowerSeries.C 2 * PowerSeries.X ^ 3 := by
    simp only [map_ofNat, pow_one, pow_zero]
  rw [expand]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]

end A267872

theorem OMA.solution : type_of% @OMA.S_oeis_a267872.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have e1 : m + 4 - 1 = (m + 1) + 2 := by omega
    have e2 : m + 4 - 2 = m + 2 := by omega
    rw [e1, e2, show m + 4 = (m + 2) + 2 by omega, A267872.a_ge, A267872.a_ge, A267872.a_ge]
    push_cast
    ring
  · apply PowerSeries.ext
    intro n
    rw [A267872.coeff_lhs, A267872.coeff_rhs]
    by_cases hn : 4 ≤ n
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have e1 : m + 4 - 1 = (m + 1) + 2 := by omega
      have e2 : m + 4 - 2 = m + 2 := by omega
      have c1 : 1 ≤ m + 4 := by omega
      have c2 : 2 ≤ m + 4 := by omega
      have d0 : ¬ (m + 4 = 0) := by omega
      have d1 : ¬ (m + 4 = 1) := by omega
      have d2 : ¬ (m + 4 = 2) := by omega
      have d3 : ¬ (m + 4 = 3) := by omega
      rw [if_pos c1, if_pos c2, if_neg d0, if_neg d1, if_neg d2, if_neg d3, e1, e2,
        show m + 4 = (m + 2) + 2 by omega, A267872.a_ge, A267872.a_ge, A267872.a_ge]
      push_cast
      ring
    · have hn' : n < 4 := by omega
      have h0 := A267872.a_zero
      have h1 := A267872.a_one
      have h2 := A267872.a_ge 0
      have h3 := A267872.a_ge 1
      interval_cases n <;> norm_num [h0, h1, h2, h3]
