import OMAStatements.S_oeis_a000392
import Mathlib

open Finset OMA.S_oeis_a000392

namespace OMA.Helpers

theorem inj {i j a b : ℕ} (h : 2 ^ i * 3 ^ j = 2 ^ a * 3 ^ b) : i = a ∧ j = b := by
  have h2 := congrArg (Nat.factorization · 2) h
  have h3 := congrArg (Nat.factorization · 3) h
  simp [Nat.factorization_mul, Nat.prime_two.factorization, Nat.prime_three.factorization] at h2 h3
  exact ⟨h2, h3⟩

theorem memS (n x : ℕ) : x ∈ S (n + 1) ↔ ∃ i j, i + j ≤ n ∧ 2 ^ i * 3 ^ j = x := by
  induction n generalizing x with
  | zero => simp [S, eq_comm]
  | succ n ih =>
    simp only [S, mem_union, mem_image, ih]
    constructor
    · rintro ((⟨i, j, h, rfl⟩ | ⟨_, ⟨i, j, h, rfl⟩, rfl⟩) | ⟨_, ⟨i, j, h, rfl⟩, rfl⟩)
      exacts [⟨i, j, by omega, rfl⟩, ⟨i + 1, j, by omega, by ring⟩, ⟨i, j + 1, by omega, by ring⟩]
    · rintro ⟨_ | i, _ | j, h, rfl⟩
      exacts [.inl (.inl ⟨0, 0, by omega, rfl⟩), .inr ⟨_, ⟨0, j, by omega, rfl⟩, by ring⟩,
        .inl (.inr ⟨_, ⟨i, 0, by omega, rfl⟩, by ring⟩),
        .inl (.inr ⟨_, ⟨i, j + 1, by omega, rfl⟩, by ring⟩)]

theorem sum_S (n : ℕ) : 2 * (∑ x ∈ S (n + 1), x) + 2 ^ (n + 3) = 3 ^ (n + 2) + 1 := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
    let L := (antidiagonal (n + 1)).image (fun p => 2 ^ p.1 * 3 ^ p.2)
    have e : S (n + 2) = S (n + 1) ∪ L := by
      ext x
      simp only [mem_union, memS, L, mem_image, HasAntidiagonal.mem_antidiagonal]
      constructor
      · rintro ⟨i, j, h, rfl⟩
        by_cases h' : i + j ≤ n
        exacts [.inl ⟨i, j, h', rfl⟩, .inr ⟨(i, j), by omega, rfl⟩]
      · rintro (⟨i, j, h, rfl⟩ | ⟨⟨i, j⟩, h, rfl⟩) <;> exact ⟨i, j, by omega, rfl⟩
    have d : Disjoint (S (n + 1)) L := disjoint_left.2 fun x hx hx' => by
      obtain ⟨i, j, h, rfl⟩ := (memS _ _).1 hx
      obtain ⟨⟨a, b⟩, h', e⟩ := mem_image.1 hx'
      have := inj e
      simp at h'
      omega
    have g (m : ℕ) : (∑ p ∈ antidiagonal m, 2 ^ p.1 * 3 ^ p.2) + 2 ^ (m + 1) = 3 ^ (m + 1) := by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Nat.sum_antidiagonal_succ]
        simp only [pow_succ, mul_right_comm _ 2, ← sum_mul] at ih ⊢
        omega
    rw [e, sum_union d, sum_image fun p _ q _ h => Prod.ext_iff.2 (inj h)]
    have := g (n + 1)
    simp only [pow_succ] at ih this ⊢
    omega

theorem stirling (n : ℕ) : Nat.stirlingSecond (n + 2) 2 + 1 = 2 ^ (n + 1) ∧
    2 * Nat.stirlingSecond (n + 3) 3 + 2 ^ (n + 3) = 3 ^ (n + 2) + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have := Nat.stirlingSecond_succ_succ (n + 2) 1
    have := Nat.stirlingSecond_succ_succ (n + 3) 2
    simp only [Nat.stirlingSecond_one_right, add_assoc, Nat.reduceAdd, pow_succ] at *
    omega

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a000392.main := by
  rintro (_ | m) hn
  · omega
  have := OMA.Helpers.stirling m
  have := OMA.Helpers.sum_S m
  show Nat.stirlingSecond (m + 3) 3 = _
  omega
