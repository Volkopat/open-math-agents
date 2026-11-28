import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1
import Mathlib

/-! The 40 surviving residues below 1024 each reach `3^o < 2^e` with `e ≤ 10` within 20 steps:
a kernel-checked bounded search. -/

namespace OMA.Step_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1_H1
open CollatzConjecture

def cs (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

theorem cs_eq (n : ℕ) : cs n = collatzStep n := by
  unfold cs collatzStep
  by_cases h : n % 2 = 0
  · rw [if_pos h, if_pos (Nat.even_iff.mpr h)]
  · rw [if_neg h, if_neg (fun he => h (Nat.even_iff.mp he))]

theorem iter_eq (k n : ℕ) : cs^[k] n = collatzStep^[k] n := by
  have : cs = collatzStep := funext cs_eq
  rw [this]

/-- counts of even / odd steps among the first `t` iterates. -/
def ev (r t : ℕ) : ℕ := ((Finset.range t).filter (fun i => cs^[i] r % 2 = 0)).card
def od (r t : ℕ) : ℕ := ((Finset.range t).filter (fun i => cs^[i] r % 2 = 1)).card

def cls (r : ℕ) : Bool :=
  [27, 31, 39, 47, 63, 71, 79, 91, 95, 103, 111, 123, 127].contains (r % 128)

def excl : List ℕ := [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
  239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
  511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
  767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023]

theorem key : ∀ r < 1024, cls r = true → r ∉ excl →
    ∃ t < 20, ev r t ≤ 10 ∧ 3 ^ od r t < 2 ^ ev r t := by
  decide +kernel

theorem H1' : ∀ r : ℕ, r < 1024 →
    (r % 128 = 27 ∨ r % 128 = 31 ∨ r % 128 = 39 ∨ r % 128 = 47 ∨
     r % 128 = 63 ∨ r % 128 = 71 ∨ r % 128 = 79 ∨ r % 128 = 91 ∨
     r % 128 = 95 ∨ r % 128 = 103 ∨ r % 128 = 111 ∨ r % 128 = 123 ∨ r % 128 = 127) →
    r ∉ ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231,
          239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495,
          511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763,
          767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ) →
    ∃ t : ℕ,
      ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card ≤ 10 ∧
      3 ^ ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 1)).card <
      2 ^ ((Finset.range t).filter (fun i => collatzStep^[i] r % 2 = 0)).card := by
  intro r hr hmod hnot
  have hc : cls r = true := by
    unfold cls
    rcases hmod with h|h|h|h|h|h|h|h|h|h|h|h|h <;> simp [h]
  obtain ⟨t, -, h⟩ := key r hr hc hnot
  refine ⟨t, ?_⟩
  simpa only [ev, od, iter_eq] using h

end OMA.Step_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1_H1

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1.H1 :=
  OMA.Step_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1_H1.H1'
