import OMAStatements.S_oeis_a123329
import Mathlib
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: row i+1 of the double sum equals f(i) = sum_{j<=i} (j-1-i%j), and f(i+1)-f(i) = aliquot(i+1)
-- via (i+1)%j = i%j+1-j[j|i+1]; so a(n-1) = sum A153485; swap sums and use sigma = aliquot + id, sum k(n+1-k) = C(n+2,3).
open OMA.S_oeis_a123329

namespace A123329Proof
open OMA.S_oeis_a123329

theorem mod_succ (N j : ℕ) (hj : 1 ≤ j) :
    (((N + 1) % j : ℕ) : ℤ) = ((N % j : ℕ) : ℤ) + 1 - (if j ∣ N + 1 then (j : ℤ) else 0) := by
  have h1 := Nat.mod_add_div (N + 1) j
  have h2 := Nat.mod_add_div N j
  have h3 : (N + 1) / j = N / j + if j ∣ N + 1 then 1 else 0 := Nat.succ_div
  rw [h3] at h1
  split_ifs at h1 ⊢ with h
  · have : ((N + 1) % j + j * (N / j + 1) : ℤ) = N + 1 := by exact_mod_cast h1
    have h2' : ((N % j : ℕ) + j * (N / j : ℕ) : ℤ) = N := by exact_mod_cast h2
    push_cast at this ⊢
    nlinarith
  · have : ((N + 1) % j + j * (N / j + 0) : ℤ) = N + 1 := by exact_mod_cast h1
    have h2' : ((N % j : ℕ) + j * (N / j : ℕ) : ℤ) = N := by exact_mod_cast h2
    push_cast at this ⊢
    nlinarith

def f (N : ℕ) : ℤ := ∑ j ∈ Finset.Ico 1 (N + 1), ((j : ℤ) - 1 - ((N % j : ℕ) : ℤ))

theorem f_eq (N : ℕ) : f N = ∑ k ∈ Finset.Icc 1 N, (A001065 k : ℤ) := by
  induction N with
  | zero => simp [f]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← ih]
    unfold f
    rw [Finset.sum_Ico_succ_top (by omega)]
    have hal : (A001065 (N + 1) : ℤ) =
        ∑ j ∈ Finset.Ico 1 (N + 1), (if j ∣ N + 1 then (j : ℤ) else 0) := by
      unfold A001065
      rw [Nat.properDivisors]
      push_cast
      rw [Finset.sum_filter]
    rw [hal]
    have : ∀ j ∈ Finset.Ico 1 (N + 1), ((j : ℤ) - 1 - (((N + 1) % j : ℕ) : ℤ)) =
        ((j : ℤ) - 1 - ((N % j : ℕ) : ℤ)) - 1 + (if j ∣ N + 1 then (j : ℤ) else 0) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [mod_succ N j hj.1]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp
    ring

theorem row_eq (N : ℕ) :
    ∑ j ∈ Finset.Ico 1 (N + 1), ((M (N + 1) j : ℤ) - M j (N + 1)) = f N := by
  unfold f
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Ico] at hj
  unfold M
  have : (j - 1) % (N + 1) = j - 1 := Nat.mod_eq_of_lt (by omega)
  rw [this, Nat.add_sub_cancel]
  push_cast
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem a_eq (m : ℕ) : a m = ∑ k ∈ Finset.Icc 1 (m + 1), (A153485 k : ℤ) := by
  unfold a
  induction m with
  | zero =>
    simp only [zero_add, Finset.Icc_self, Finset.sum_singleton]
    rw [show (2:ℕ) = 1 + 1 from rfl, row_eq, f_eq]
    simp [A153485]
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by ring, Finset.sum_Icc_succ_top (show 2 ≤ m + 2 + 1 by omega),
      ih, Finset.sum_Icc_succ_top (show 1 ≤ m + 1 + 1 by omega)]
    congr 1
    rw [row_eq, f_eq]
    unfold A153485
    push_cast
    rfl

theorem conv (n : ℕ) : ∑ k ∈ Finset.Icc 1 n, (A153485 k : ℤ) =
    ∑ k ∈ Finset.Icc 1 n, (A001065 k : ℤ) * ((n + 1 - k : ℕ) : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega)]
    have : ∀ k ∈ Finset.Icc 1 n, (A001065 k : ℤ) * ((n + 1 + 1 - k : ℕ) : ℤ) =
        (A001065 k : ℤ) * ((n + 1 - k : ℕ) : ℤ) + A001065 k := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [show n + 1 + 1 - k = (n + 1 - k) + 1 by omega]
      push_cast
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    unfold A153485
    rw [Finset.sum_Icc_succ_top (by omega)]
    push_cast
    simp
    ring

theorem gauss (n : ℕ) : 2 * ∑ k ∈ Finset.Icc 1 n, k = n * (n + 1) ∧
    6 * ∑ k ∈ Finset.Icc 1 n, k * (n - k + 1) = n * (n + 1) * (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have : ∀ k ∈ Finset.Icc 1 n, k * (n + 1 - k + 1) = k * (n - k + 1) + k := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [show n + 1 - k + 1 = (n - k + 1) + 1 by omega]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
    constructor
    · rw [mul_add, h1]; ring
    · rw [show n + 1 - (n + 1) + 1 = 1 by omega, mul_add, mul_add, h2]
      nlinarith [h1]

theorem third (n : ℕ) : (A175254 n : ℤ) - A000292 n =
    ∑ k ∈ Finset.Icc 1 n, (A001065 k : ℤ) * ((n + 1 - k : ℕ) : ℤ) := by
  have h2 := (gauss n).2
  have hdiv : A000292 n = ∑ k ∈ Finset.Icc 1 n, k * (n - k + 1) := by
    unfold A000292; omega
  rw [hdiv]
  unfold A175254
  have : ∀ k ∈ Finset.Icc 1 n, ArithmeticFunction.sigma 1 k * (n - k + 1) =
      A001065 k * (n + 1 - k) + k * (n - k + 1) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
      show n + 1 - k = n - k + 1 by omega]
    unfold A001065
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  push_cast
  ring

end A123329Proof

open A123329Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a123329.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h1 := A123329Proof.a_eq m
  have h2 := A123329Proof.conv (m + 1)
  have h3 := A123329Proof.third (m + 1)
  refine ⟨?_, h1, ?_⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2, h3]
