import OMAStatements.S_oeis_a076217
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OMA.S_oeis_a076217

private theorem step_up (n : ℕ) (h : a n < (n : ℤ) + 1) :
    a (n+1) = a n + (n+1 : ℕ) := by
  rw [a]
  push_cast
  rw [Int.sign_eq_one_of_pos (by omega), mul_one]

private theorem step_down (n : ℕ) (h : (n : ℤ) + 1 < a n) :
    a (n+1) = a n - (n+1 : ℕ) := by
  rw [a]
  push_cast
  rw [Int.sign_eq_neg_one_of_neg (by omega)]
  ring

private theorem step_same (n : ℕ) (h : a n = (n : ℤ) + 1) : a (n+1) = a n := by
  rw [a]
  push_cast
  rw [h]
  simp

/-- On the block starting at a fixed point p, the two alternating subsequences
are linear, up to but not including the next fixed point 3p. -/
private theorem block {p : ℕ} (hp : a p = (p : ℤ)) (j : ℕ) (hj : j < p) :
    a (p+2*j) = (p : ℤ) - j ∧ a (p+2*j+1) = 2*(p : ℤ)+j+1 := by
  induction j with
  | zero =>
    simp only [Nat.mul_zero, Nat.cast_zero, sub_zero, add_zero]
    constructor
    · exact hp
    · rw [step_up p (by omega), hp]
      push_cast
      ring
  | succ j ih =>
    obtain ⟨_, ho⟩ := ih (by omega)
    have hs := step_down (p+2*j+1) (by push_cast; omega)
    have he : a (p+2*(j+1)) = (p : ℤ) - (j+1) := by
      rw [show p+2*(j+1) = (p+2*j+1)+1 by omega, hs, ho]
      push_cast
      ring
    have hu := step_up (p+2*(j+1)) (by push_cast; omega)
    constructor
    · simpa using he
    · rw [hu, he]
      push_cast
      ring

private theorem next_fixed {p : ℕ} (hpos : 0 < p) (hp : a p = (p : ℤ)) :
    a (3*p) = (3*p : ℕ) := by
  have hlast := (block hp (p-1) (by omega)).2
  rw [show p+2*(p-1)+1 = 3*p-1 by omega] at hlast
  have hs := step_same (3*p-1) (by omega)
  rw [show 3*p-1+1 = 3*p by omega] at hs
  omega

private theorem fixed (k : ℕ) : a (3^k) = ((3^k : ℕ) : ℤ) := by
  induction k with
  | zero => decide
  | succ k =>
    rw [pow_succ, Nat.mul_comm]
    exact next_fixed (by positivity) ‹_›

private def recurrence (n : ℕ) : Prop := a n = -a (n-1) + a (n-2) + a (n-3)

private theorem inside {p n : ℕ} (hp : a p = (p : ℤ)) (hl : p+3 ≤ n) (hr : n < 3*p) :
    recurrence n := by
  let j := (n-p-3)/2
  have hj : n = p+2*j+3 ∨ n = p+2*j+4 := by dsimp [j]; omega
  have h₀ := block hp j (by omega)
  have h₁ := block hp (j+1) (by omega)
  unfold recurrence
  rcases hj with he | ho
  · rw [show n = p+2*(j+1)+1 by omega, h₁.2,
        show p+2*(j+1)+1-1 = p+2*(j+1) by omega, h₁.1,
        show p+2*(j+1)+1-2 = p+2*j+1 by omega, h₀.2,
        show p+2*(j+1)+1-3 = p+2*j by omega, h₀.1]
    push_cast
    ring
  · have h₂ := (block hp (j+2) (by omega)).1
    rw [show n = p+2*(j+2) by omega, h₂,
        show p+2*(j+2)-1 = p+2*(j+1)+1 by omega, h₁.2,
        show p+2*(j+2)-2 = p+2*(j+1) by omega, h₁.1,
        show p+2*(j+2)-3 = p+2*j+1 by omega, h₀.2]
    push_cast
    ring

private theorem boundary {p n : ℕ} (hp : a p = (p : ℤ)) (hp3 : 3 ≤ p)
    (hl : 3*p ≤ n) (hr : n < 3*p+3) : ¬ recurrence n := by
  have hb := block hp (p-1) (by omega)
  have hc := (block hp (p-2) (by omega)).2
  have hd := next_fixed (by omega : 0 < p) hp
  have he := (block hd 0 (by omega)).2
  have hf := (block hd 1 (by omega)).1
  simp only [Nat.mul_zero, Nat.mul_one, Nat.cast_zero, Nat.cast_one, add_zero] at he hf
  obtain ⟨hb₁, hb₂⟩ := hb
  rw [show p+2*(p-2)+1 = 3*p-3 by omega] at hc
  rw [show p+2*(p-1) = 3*p-2 by omega] at hb₁
  rw [show p+2*(p-1)+1 = 3*p-1 by omega] at hb₂
  unfold recurrence
  rcases (show n = 3*p ∨ n = 3*p+1 ∨ n = 3*p+2 by omega) with h | h | h
  · subst n
    omega
  · subst n
    simp only [show 3*p+1-1 = 3*p by omega, show 3*p+1-2 = 3*p-1 by omega,
      show 3*p+1-3 = 3*p-2 by omega]
    omega
  · subst n
    simp only [show 3*p+2-1 = 3*p+1 by omega, show 3*p+2-2 = 3*p by omega,
      show 3*p+2-3 = 3*p-1 by omega]
    omega

end OMA.S_oeis_a076217

open OMA.S_oeis_a076217 in
theorem OMA.solution : type_of% @OMA.S_oeis_a076217.main := by
  intro n hn
  let k := Nat.log 3 (n-3)
  let p := 3^k
  have hlo : p ≤ n-3 := Nat.pow_log_le_self 3 (by omega)
  have hhi : n-3 < 3*p := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 3) (n-3)
    simpa only [p, k, pow_succ, Nat.mul_comm] using h
  have hk : 1 ≤ k := by
    by_contra! h
    have hz : k = 0 := by omega
    simp [p, hz] at hhi
    omega
  have hp3 : 3 ≤ p := Nat.pow_le_pow_right (by decide : 0 < 3) hk
  have hp : a p = (p : ℤ) := fixed k
  change recurrence n ↔ _
  by_cases hinner : n < 3*p
  · refine ⟨fun _ ⟨r, _, hrl, hrr⟩ => ?_, fun _ => inside hp (by omega) hinner⟩
    by_cases hr : r ≤ k
    · have h : 3^r ≤ p := Nat.pow_le_pow_right (by decide : 0 < 3) hr
      omega
    · have h : 3^(k+1) ≤ 3^r := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega)
      rw [pow_succ, Nat.mul_comm] at h
      change 3*p ≤ _ at h
      omega
  · have hbad := boundary hp hp3 (by omega : 3*p ≤ n) (by omega : n < 3*p+3)
    have hex : ∃ r : ℕ, 2 ≤ r ∧ 3^r ≤ n ∧ n < 3^r+3 := by
      refine ⟨k+1, by omega, ?_⟩
      rw [pow_succ, Nat.mul_comm]
      change 3*p ≤ n ∧ n < 3*p+3
      omega
    exact ⟨fun h => (hbad h).elim, fun h => (h hex).elim⟩
