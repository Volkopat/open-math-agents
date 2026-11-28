import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1
import Mathlib

/-! Every `0 < n < 1000` reaches `1` under the Collatz map, by a kernel-checked search with at
most `200` steps per start (the longest trajectory below `1000`, from `871`, takes `178`). -/

namespace OMA.Step_CollatzConjecture_collatz_conjecture_R1_H2_R1_H1

open CollatzConjecture

/-- The Collatz map with a parity test by remainder. -/
def cs (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

theorem cs_eq (n : ℕ) : cs n = collatzStep n := by
  unfold cs collatzStep
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_pos (Nat.even_iff.mpr h)]
  · rw [if_neg h, if_neg (fun he => h (Nat.even_iff.mp he))]

/-- `n` reaches `1` within `fuel` steps. -/
def reachB : ℕ → ℕ → Bool
  | 0, n => n == 1
  | fuel + 1, n => n == 1 || reachB fuel (cs n)

theorem reachB_spec : ∀ fuel n : ℕ, reachB fuel n = true → ∃ m : ℕ, collatzStep^[m] n = 1 := by
  intro fuel
  induction fuel with
  | zero => intro n h; exact ⟨0, by simpa [reachB] using h⟩
  | succ fuel ih =>
    intro n h
    simp only [reachB, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨m, hm⟩ := ih (cs n) h
      exact ⟨m + 1, by rw [Function.iterate_succ_apply, ← cs_eq]; exact hm⟩

/-- `test x` holds for every `x` in `[s, s + c)`. -/
def checkFrom (test : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => true
  | c + 1, s => test s && checkFrom test c (s + 1)

theorem checkFrom_spec (test : ℕ → Bool) : ∀ c s : ℕ, checkFrom test c s = true →
    ∀ n : ℕ, s ≤ n → n < s + c → test n = true := by
  intro c
  induction c with
  | zero => intro s _ n h1 h2; omega
  | succ c ih =>
    intro s h n h1 h2
    simp only [checkFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact ih (s + 1) h.2 n hlt (by omega)

theorem check_all : checkFrom (reachB 200) 999 1 = true := by decide +kernel

end OMA.Step_CollatzConjecture_collatz_conjecture_R1_H2_R1_H1

open OMA.Step_CollatzConjecture_collatz_conjecture_R1_H2_R1_H1 in
theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H1 :=
  fun n h0 h1 => reachB_spec 200 n (checkFrom_spec (reachB 200) 999 1 check_all n h0 (by omega))
