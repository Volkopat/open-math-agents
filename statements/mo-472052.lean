import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Growth of binary strings avoiding a translated four-position pattern

Source: https://mathoverflow.net/questions/472052

Positions k−t, k−s, k, k+s must never carry 0,0,1,0. The question gives
s=2 and t=3, and the author's comment asks for bounds for arbitrary spacings.
-/
namespace OMA.S_mo_472052

/-- The most recent previously written bit has index zero. -/
def push (b : Bool) (h : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | i+1 => h i

/-- When writing 0 at k+s, it is legal if a required 0 in the past
is 1, or the required 1 at k is 0. Writing 1 is always legal. -/
def allowZero (s t : ℕ) (h : ℕ → Bool) : Bool :=
  h (t+s-1) || h (s+s-1) || !(h (s-1))

/-- Each branch writes one bit. The base case counts the empty continuation. -/
def continuations (s t : ℕ) : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 1
  | n+1, h => continuations s t n (push true h) +
      if allowZero s t h then continuations s t n (push false h) else 0

/-- Past the left end the history is all ones, so a forbidden pattern
can start only at an actual position in the word. -/
def count (s t n : ℕ) : ℕ := continuations s t n (fun _ => true)

theorem main : ∀ s t : ℕ, 0<s → 0<t → ∃ c : ℝ,
    7/4 ≤ c ∧ c < 2 ∧
    (∀ n : ℕ, c^n ≤ (count s t n : ℝ) ∧ (count s t n : ℝ) ≤ c^(n+max t s+s)) ∧
    (s=2 → t=3 →
      1884337/1000000 < c ∧ c < 1884338/1000000 ∧
      c^7-2*c^6+2*c^3-c^2-3*c+1 = 0) := by
  sorry

end OMA.S_mo_472052
