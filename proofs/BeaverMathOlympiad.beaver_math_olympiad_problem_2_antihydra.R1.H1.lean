import OMAReductions.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_R1
import Mathlib

-- Step BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.R1.H1: hypothesis H1 of reduction BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.R1
-- Credit: @ivillar. Kernel computation: run the Antihydra recurrence for 2^17 = 131072 >= 100000 steps (binary-split recursion, decide +kernel) and check that the counter never goes negative; run_spec transfers this to any sequences a, b satisfying the recurrences.

/-! Step BeaverMathOlympiad.beaver_math_olympiad_problem_2_antihydra.R1.H1. -/

namespace P8Antihydra

/-- One step of the Antihydra counter, with the counter kept as a natural number;
`none` signals that the counter would go negative. -/
def step (s : ℕ × ℕ) : Option (ℕ × ℕ) :=
  if s.1 % 2 = 0 then some (3 * s.1 / 2, s.2 + 2)
  else if s.2 = 0 then none else some (3 * s.1 / 2, s.2 - 1)

/-- `run j` performs `2 ^ j` steps (binary splitting keeps the recursion shallow). -/
def run : ℕ → ℕ × ℕ → Option (ℕ × ℕ)
  | 0, s => step s
  | j + 1, s => match run j s with
    | none => none
    | some t => run j t

theorem run_spec (a : ℕ → ℕ) (b : ℕ → ℤ) (ha : ∀ n, a (n + 1) = (3 * a n) / 2)
    (hb : ∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) :
    ∀ j k s, 0 ≤ b k → run j (a k, (b k).toNat) = some s →
      (∀ i ≤ 2 ^ j, 0 ≤ b (k + i)) ∧ s = (a (k + 2 ^ j), (b (k + 2 ^ j)).toNat) := by
  intro j
  induction j with
  | zero =>
    intro k s hk h
    simp only [run, step] at h
    simp only [pow_zero]
    by_cases hpar : a k % 2 = 0
    · rw [if_pos hpar] at h
      have hb1 : b (k + 1) = b k + 2 := by rw [hb, if_pos hpar]
      obtain rfl := Option.some.inj h
      refine ⟨?_, ?_⟩
      · intro i hi
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
        · simpa using hk
        · rw [hb1]
          omega
      · rw [ha, hb1]
        ext
        · rfl
        · simp only
          omega
    · rw [if_neg hpar] at h
      have hb1 : b (k + 1) = b k - 1 := by rw [hb, if_neg hpar]
      by_cases h0 : (b k).toNat = 0
      · rw [if_pos h0] at h
        exact absurd h (by simp)
      · rw [if_neg h0] at h
        obtain rfl := Option.some.inj h
        refine ⟨?_, ?_⟩
        · intro i hi
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
          · simpa using hk
          · rw [hb1]
            omega
        · rw [ha, hb1]
          ext
          · rfl
          · simp only
            omega
  | succ j ih =>
    intro k s hk h
    simp only [run] at h
    cases hr : run j (a k, (b k).toNat) with
    | none =>
      rw [hr] at h
      exact absurd h (by simp)
    | some t =>
      rw [hr] at h
      obtain ⟨h1, rfl⟩ := ih k t hk hr
      have hk' : 0 ≤ b (k + 2 ^ j) := h1 _ le_rfl
      obtain ⟨h2, rfl⟩ := ih (k + 2 ^ j) s hk' h
      have e : k + 2 ^ j + 2 ^ j = k + 2 ^ (j + 1) := by rw [pow_succ]; ring
      refine ⟨?_, by rw [e]⟩
      intro i hi
      by_cases hij : i ≤ 2 ^ j
      · exact h1 i hij
      · have := h2 (i - 2 ^ j) (by rw [pow_succ] at hi; omega)
        rwa [show k + 2 ^ j + (i - 2 ^ j) = k + i by omega] at this

theorem run_ok : (run 17 (8, 0)).isSome = true := by decide +kernel

theorem antihydra_h1 : ∀ (a : ℕ → ℕ) (b : ℕ → ℤ), a 0 = 8 → (∀ n, a (n + 1) = (3 * a n) / 2) →
    b 0 = 0 → (∀ n, b (n + 1) = if a n % 2 = 0 then b n + 2 else b n - 1) →
    ∀ n, n ≤ 100000 → b n ≥ 0 := by
  intro a b ha0 ha hb0 hb n hn
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp run_ok
  have h0 : (a 0, (b 0).toNat) = (8, 0) := by rw [ha0, hb0]; rfl
  have := (run_spec a b ha hb 17 0 s (by rw [hb0]) (by rw [h0]; exact hs)).1 n
    (by norm_num; omega)
  simpa using this

end P8Antihydra

theorem OMA.solution : OMA.R_BeaverMathOlympiad_beaver_math_olympiad_problem_2_antihydra_R1.H1 :=
  P8Antihydra.antihydra_h1
