import OMAStatements.S_oeis_a005251
import Mathlib

/-!
# Dement's identity for OEIS A005251

Put `d n = (-1)^n * b n`. By the recurrence of `b`, `d` satisfies the recurrence of `a` and `c`,
so `a (n + 1) + d n = 2 * c (n + 1)` follows from the cases `n = 0, 1, 2`, and the same recurrence
keeps `0 ≤ d n ≤ d (n + 1)`. Hence `|b n| = d n`.
-/

open OMA.S_oeis_a005251

theorem OMA.k : ∀ n, a (n + 1) + (-1) ^ n * b n = 2 * c (n + 1) ∧ 0 ≤ (-1) ^ n * b n ∧
    (-1) ^ n * b n ≤ (-1) ^ (n + 1) * b (n + 1)
  | 0 | 1 | 2 => by decide
  | n + 3 => by
    have h := OMA.k n
    have i := OMA.k (n + 1)
    have j := OMA.k (n + 2)
    have e : b (n + 3) = -2 * b (n + 2) - b (n + 1) - b n := rfl
    have f : b (n + 3 + 1) = -2 * b (n + 3) - b (n + 2) - b (n + 1) := rfl
    have : a (n + 3 + 1) = 2 * a (n + 3) - a (n + 2) + a (n + 1) := rfl
    have : c (n + 3 + 1) = 2 * c (n + 3) - c (n + 2) + c (n + 1) := rfl
    rw [f, e] at *
    ring_nf at *
    refine ⟨by linarith, by linarith, by linarith⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a005251.main := fun n => by
  obtain ⟨h, g, -⟩ := OMA.k n
  rwa [← abs_of_nonneg g, abs_mul, abs_neg_one_pow, one_mul] at h
