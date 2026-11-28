import OMAStatements.S_oeis_a159864
import Mathlib

open OMA.S_oeis_a159864 in
theorem OMA.solution : type_of% @OMA.S_oeis_a159864.main := by
  have hrec : ∀ j i : ℕ, D j (i + 2) = D j (i + 1) + D j i := by
    intro j
    induction j with
    | zero =>
      intro i
      show ((Nat.fib (i + 2) : ℕ) : ℤ) = (Nat.fib (i + 1) : ℤ) + (Nat.fib i : ℤ)
      rw [Nat.fib_add_two]
      push_cast
      ring
    | succ j ih =>
      intro i
      have h1 : D j (i + 3) = D j (i + 2) + D j (i + 1) := ih (i + 1)
      have h2 : D j (i + 2) = D j (i + 1) + D j i := ih i
      show D j (i + 3) - D j (i + 2) = (D j (i + 2) - D j (i + 1)) + (D j (i + 1) - D j i)
      linear_combination h1 - h2
  have shift : ∀ j i : ℕ, D (j + 1) (i + 1) = D j i := by
    intro j i
    have h : D j (i + 1 + 1) = D j (i + 1) + D j i := hrec j i
    show D j (i + 1 + 1) - D j (i + 1) = D j i
    linear_combination h
  have E : ∀ j : ℕ, D j 0 = (-1) ^ (j + 1) * (Nat.fib j : ℤ) ∧
      D (j + 1) 0 = (-1) ^ (j + 2) * (Nat.fib (j + 1) : ℤ) := by
    intro j
    induction j with
    | zero =>
      constructor
      · show ((Nat.fib 0 : ℕ) : ℤ) = (-1) ^ (0 + 1) * (Nat.fib 0 : ℤ)
        norm_num
      · show D 0 (0 + 1) - D 0 0 = (-1) ^ (0 + 2) * (Nat.fib (0 + 1) : ℤ)
        show ((Nat.fib (0 + 1) : ℕ) : ℤ) - ((Nat.fib 0 : ℕ) : ℤ) = (-1) ^ (0 + 2) * (Nat.fib (0 + 1) : ℤ)
        norm_num
    | succ j ih =>
      refine ⟨ih.2, ?_⟩
      have hs : D (j + 1 + 1) 0 = D (j + 1) (0 + 1) - D (j + 1) 0 := rfl
      have h3 : D (j + 1) (0 + 1) = D j 0 := shift j 0
      have hf : (Nat.fib (j + 1 + 1) : ℤ) = (Nat.fib j : ℤ) + (Nat.fib (j + 1) : ℤ) := by
        have h := Nat.fib_add_two (n := j)
        rw [show j + 2 = j + 1 + 1 by ring] at h
        exact_mod_cast h
      rw [hs, h3, ih.1, ih.2, hf]
      ring
  have row : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 3), T (n + 2) k
      = (Nat.fib (n + 2) : ℤ) + ∑ k ∈ Finset.range (n + 1), T n k + D (n + 2) 0 := by
    intro n
    have e1 : ∑ k ∈ Finset.range (n + 3), T (n + 2) k
        = ∑ k ∈ Finset.range (n + 2), T (n + 2) k + T (n + 2) (n + 2) :=
      Finset.sum_range_succ _ _
    have e2 : ∑ k ∈ Finset.range (n + 2), T (n + 2) k
        = ∑ k ∈ Finset.range (n + 1), T (n + 2) (k + 1) + T (n + 2) 0 :=
      Finset.sum_range_succ' _ _
    have hmid : ∑ k ∈ Finset.range (n + 1), T (n + 2) (k + 1)
        = ∑ k ∈ Finset.range (n + 1), T n k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < n + 1 := Finset.mem_range.mp hk
      show D (k + 1) (n + 2 - (k + 1)) = D k (n - k)
      rw [show n + 2 - (k + 1) = (n - k) + 1 by omega]
      exact shift k (n - k)
    have h0 : T (n + 2) 0 = (Nat.fib (n + 2) : ℤ) := rfl
    have hl : T (n + 2) (n + 2) = D (n + 2) 0 := by
      show D (n + 2) (n + 2 - (n + 2)) = D (n + 2) 0
      rw [Nat.sub_self]
    rw [e1, e2, hmid, h0, hl]
    ring
  have ev : ∀ m : ℕ, ∑ k ∈ Finset.range (2 * m + 1), T (2 * m) k = 0 := by
    intro m
    induction m with
    | zero => first | rfl | decide | simp [T, D]
    | succ m ih =>
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) = 2 * m + 2 by ring,
        row (2 * m)]
      have hE : D (2 * m + 2) 0 = -(Nat.fib (2 * m + 2) : ℤ) := by
        rw [(E (2 * m + 2)).1, show 2 * m + 2 + 1 = 2 * (m + 1) + 1 by ring, pow_succ, pow_mul]
        norm_num
      linear_combination ih + hE
  have od : ∀ m : ℕ, ∑ k ∈ Finset.range (2 * m + 2), T (2 * m + 1) k
      = 2 * (Nat.fib (2 * m + 2) : ℤ) := by
    intro m
    induction m with
    | zero =>
      show ∑ k ∈ Finset.range 2, T 1 k = 2 * (Nat.fib 2 : ℤ)
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      show D 0 1 + (D 0 (0 + 1) - D 0 0) = 2 * (Nat.fib 2 : ℤ)
      show ((Nat.fib 1 : ℕ) : ℤ) + (((Nat.fib (0 + 1) : ℕ) : ℤ) - ((Nat.fib 0 : ℕ) : ℤ))
        = 2 * (Nat.fib 2 : ℤ)
      norm_num [Nat.fib_two]
    | succ m ih =>
      rw [show 2 * (m + 1) + 2 = 2 * m + 1 + 3 by ring,
        show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, row (2 * m + 1)]
      have ih' : ∑ k ∈ Finset.range (2 * m + 1 + 1), T (2 * m + 1) k
          = 2 * (Nat.fib (2 * m + 1 + 1) : ℤ) := ih
      have hE : D (2 * m + 1 + 2) 0 = (Nat.fib (2 * m + 1 + 2) : ℤ) := by
        rw [(E (2 * m + 1 + 2)).1, show 2 * m + 1 + 2 + 1 = 2 * (m + 2) by ring, pow_mul]
        norm_num
      have hf : (Nat.fib (2 * m + 1 + 3) : ℤ)
          = (Nat.fib (2 * m + 1 + 1) : ℤ) + (Nat.fib (2 * m + 1 + 2) : ℤ) := by
        have h := Nat.fib_add_two (n := 2 * m + 1 + 1)
        rw [show 2 * m + 1 + 1 + 2 = 2 * m + 1 + 3 by ring,
          show 2 * m + 1 + 1 + 1 = 2 * m + 1 + 2 by ring] at h
        exact_mod_cast h
      linear_combination ih' + hE - 2 * hf
  exact fun n => ⟨ev n, od n⟩
