import OMAStatements.S_oeis_a259458
import Mathlib

open OMA.S_oeis_a259458 PowerSeries

theorem P259458.rf5 (n : ℕ) : rf 5 n = ((n + 4).factorial : ℚ) / 24 := by
  induction n with
  | zero => simp [rf, Nat.factorial]
  | succ k ih =>
    unfold rf at ih ⊢
    rw [Finset.prod_range_succ, ih, show k + 1 + 4 = (k + 4) + 1 by ring, Nat.factorial_succ (k + 4)]
    push_cast
    ring

theorem P259458.rf3 (n : ℕ) : rf 3 n = ((n + 2).factorial : ℚ) / 2 := by
  induction n with
  | zero => simp [rf, Nat.factorial]
  | succ k ih =>
    unfold rf at ih ⊢
    rw [Finset.prod_range_succ, ih, show k + 1 + 2 = (k + 2) + 1 by ring, Nat.factorial_succ (k + 2)]
    push_cast
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a259458.main := by
  congr 1
  funext n
  rw [P259458.rf5, P259458.rf3]
  unfold a
  have h4 : ((n + 4).factorial : ℚ) = (n + 4) * (n + 3) * ((n + 2).factorial : ℚ) := by
    rw [show n + 4 = (n + 3) + 1 by ring, Nat.factorial_succ, show n + 3 = (n + 2) + 1 by ring,
      Nat.factorial_succ]
    push_cast
    ring
  have h2 : ((n + 2).factorial : ℚ) = (n + 2) * (n + 1) * (n.factorial : ℚ) := by
    rw [show n + 2 = (n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [h4, h2]
  field_simp
  ring
