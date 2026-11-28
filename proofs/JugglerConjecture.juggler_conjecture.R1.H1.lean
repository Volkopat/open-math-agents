import OMAReductions.R_JugglerConjecture_juggler_conjecture_R1
import Mathlib

/-! Every `0 < n ≤ 1000` reaches `1` under the juggler map, by a kernel-checked run. Each
step takes an integer square root by Newton iteration and checks it against `Nat.eq_sqrt`;
the real powers in `jugglerStep` are rewritten to `Nat.sqrt`. -/

namespace OMA.Step_JugglerConjecture_juggler_conjecture_R1_H1

open JugglerConjecture

/-- Newton iteration for the integer square root, with fuel. -/
def newt (x : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | f + 1, g => if (g + x / g) / 2 < g then newt x f ((g + x / g) / 2) else g

/-- A candidate integer square root. -/
def isq (y : ℕ) : ℕ := newt y 100 (1 <<< (Nat.log2 y / 2 + 1))

/-- The radicand of the juggler step: `x` if `x` is even, `x ^ 3` if `x` is odd. -/
def rad (x : ℕ) : ℕ := if x % 2 = 0 then x else x ^ 3

/-- The candidate square root of the radicand is exact. -/
def okB (x : ℕ) : Bool :=
  decide (isq (rad x) * isq (rad x) ≤ rad x) && decide (rad x < (isq (rad x) + 1) * (isq (rad x) + 1))

theorem floor_sqrt_half (x : ℕ) : ⌊(x : ℝ) ^ (1 / 2 : ℝ)⌋₊ = Nat.sqrt x := by
  rw [← Real.sqrt_eq_rpow, Real.nat_floor_real_sqrt_eq_nat_sqrt]

theorem floor_sqrt_three_half (x : ℕ) : ⌊(x : ℝ) ^ (3 / 2 : ℝ)⌋₊ = Nat.sqrt (x ^ 3) := by
  have h : (x : ℝ) ^ (3 / 2 : ℝ) = (((x ^ 3 : ℕ) : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = (3 : ℕ) * (1 / 2 : ℝ) by norm_num,
      Real.rpow_mul (Nat.cast_nonneg x), Real.rpow_natCast]
    push_cast
    rfl
  rw [h, floor_sqrt_half]

theorem jugglerStep_eq (x : ℕ) : jugglerStep x = Nat.sqrt (rad x) := by
  unfold jugglerStep rad
  by_cases h : x % 2 = 0
  · rw [if_pos (Nat.even_iff.mpr h), if_pos h, floor_sqrt_half]
  · rw [if_neg (fun he => h (Nat.even_iff.mp he)), if_neg h, floor_sqrt_three_half]

theorem okB_spec {x : ℕ} (h : okB x = true) : jugglerStep x = isq (rad x) := by
  simp only [okB, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [jugglerStep_eq]
  exact (Nat.eq_sqrt.mpr h).symm

/-- `x` reaches `1` within `fuel` checked juggler steps. -/
def reachB : ℕ → ℕ → Bool
  | 0, x => x == 1
  | f + 1, x => x == 1 || (okB x && reachB f (isq (rad x)))

theorem reachB_spec : ∀ f x : ℕ, reachB f x = true → ∃ m : ℕ, jugglerStep^[m] x = 1 := by
  intro f
  induction f with
  | zero => intro x h; exact ⟨0, by simpa [reachB] using h⟩
  | succ f ih =>
    intro x h
    simp only [reachB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · exact ⟨0, h⟩
    · obtain ⟨m, hm⟩ := ih _ h2
      exact ⟨m + 1, by rw [Function.iterate_succ_apply, okB_spec h1]; exact hm⟩

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

theorem check_all : checkFrom (reachB 100) 1000 1 = true := by decide +kernel

theorem reach (n : ℕ) (h0 : n > 0) (h : n ≤ 1000) : ∃ m, jugglerStep^[m] n = 1 :=
  reachB_spec 100 n (checkFrom_spec (reachB 100) 1000 1 check_all n h0 (by omega))

end OMA.Step_JugglerConjecture_juggler_conjecture_R1_H1

theorem OMA.solution : OMA.R_JugglerConjecture_juggler_conjecture_R1.H1 :=
  OMA.Step_JugglerConjecture_juggler_conjecture_R1_H1.reach
