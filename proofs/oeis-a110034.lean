import OMAStatements.S_oeis_a110034

-- Problem: A110034: Row sums of a characteristic triangle for the Fibonacci numbers.
-- Upstream: formal-conjectures statements/oeis-a110034.lean:0 (declaration OMA.S_oeis_a110034.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a(n) is the characteristic polynomial of H(n) at x = 1, that is det(1 - H(n)).
-- Since F(i+j+1) = F(i)F(j) + F(i+1)F(j+1), H(n) = U V with U an n X 2 and V a 2 X n matrix,
-- and det(1 - U V) = det(1 - V U) = (1 - S0)(1 - S1) - P^2 with S0 = Sum F(i)^2,
-- S1 = Sum F(i+1)^2, P = Sum F(i)F(i+1) over i < n. With S0 = F(n)F(n+1) - F(n)^2,
-- S1 = F(n)F(n+1), 2P = 2F(n)^2 - 1 + (-1)^n and Cassini's identity, this determinant D(n)
-- satisfies D(n+1) = D(n) - (2F(n)^2 + (-1)^n) = D(n) - A061646(n), and D(1) = 0; the terms
-- A061646(k) = 2F(k)^2 + (-1)^k are positive for k >= 1.

namespace K04A110034

open OMA.S_oeis_a110034

/-- The n X 2 matrix (F(i + c)). -/
def U (n : ℕ) : Matrix (Fin n) (Fin 2) ℤ := Matrix.of fun i c => (Nat.fib ((i : ℕ) + (c : ℕ)) : ℤ)

/-- The 2 X n matrix (F(j + c)). -/
def V (n : ℕ) : Matrix (Fin 2) (Fin n) ℤ := Matrix.of fun c j => (Nat.fib ((j : ℕ) + (c : ℕ)) : ℤ)

theorem a_eval (n : ℕ) : a n = (H n).charpoly.eval 1 := by
  rw [Polynomial.eval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  unfold a T
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [one_pow, mul_one]

theorem charpoly_eval_one (n : ℕ) : (H n).charpoly.eval 1 = (1 - H n).det := by
  rw [Matrix.eval_charpoly, map_one]

theorem H_entry (n : ℕ) (i j : Fin n) : H n i j = U n i 0 * V n 0 j + U n i 1 * V n 1 j := by
  show (Nat.fib ((i : ℕ) + (j : ℕ) + 1) : ℤ) =
    (Nat.fib ((i : ℕ) + 0) : ℤ) * (Nat.fib ((j : ℕ) + 0) : ℤ) +
      (Nat.fib ((i : ℕ) + 1) : ℤ) * (Nat.fib ((j : ℕ) + 1) : ℤ)
  rw [add_zero, add_zero]
  exact_mod_cast Nat.fib_add (i : ℕ) (j : ℕ)

theorem H_eq (n : ℕ) : H n = U n * V n := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, H_entry]

theorem det_eq (n : ℕ) : (1 - H n).det = (1 - V n * U n).det := by
  rw [H_eq, Matrix.det_one_sub_mul_comm]

theorem VU00 (n : ℕ) :
    (V n * U n) 0 0 = ∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib i : ℤ) := by
  rw [Matrix.mul_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => (Nat.fib i : ℤ) * (Nat.fib i : ℤ)) n

theorem VU01 (n : ℕ) :
    (V n * U n) 0 1 = ∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib (i + 1) : ℤ) := by
  rw [Matrix.mul_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => (Nat.fib i : ℤ) * (Nat.fib (i + 1) : ℤ)) n

theorem VU10 (n : ℕ) :
    (V n * U n) 1 0 = ∑ i ∈ Finset.range n, (Nat.fib (i + 1) : ℤ) * (Nat.fib i : ℤ) := by
  rw [Matrix.mul_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => (Nat.fib (i + 1) : ℤ) * (Nat.fib i : ℤ)) n

theorem VU11 (n : ℕ) :
    (V n * U n) 1 1 = ∑ i ∈ Finset.range n, (Nat.fib (i + 1) : ℤ) * (Nat.fib (i + 1) : ℤ) := by
  rw [Matrix.mul_apply]
  exact Fin.sum_univ_eq_sum_range (fun i => (Nat.fib (i + 1) : ℤ) * (Nat.fib (i + 1) : ℤ)) n

theorem det_two (n : ℕ) : (1 - V n * U n).det =
    (1 - ∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib i : ℤ)) *
      (1 - ∑ i ∈ Finset.range n, (Nat.fib (i + 1) : ℤ) * (Nat.fib (i + 1) : ℤ)) -
    (∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib (i + 1) : ℤ)) *
      (∑ i ∈ Finset.range n, (Nat.fib (i + 1) : ℤ) * (Nat.fib i : ℤ)) := by
  rw [Matrix.det_fin_two, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.one_apply_eq, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), VU00, VU01, VU10, VU11]
  ring

theorem fib2 (k : ℕ) : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
  exact_mod_cast Nat.fib_add_two (n := k)

theorem cassini (n : ℕ) : (Nat.fib (n + 1) : ℤ) * Nat.fib (n + 1) - Nat.fib n * Nat.fib (n + 1) -
    Nat.fib n * Nat.fib n = (-1) ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 by ring, fib2 k]
    linear_combination (-1 : ℤ) * ih

theorem S1_closed (n : ℕ) :
    ∑ i ∈ Finset.range n, (Nat.fib (i + 1) : ℤ) * (Nat.fib (i + 1) : ℤ) =
      (Nat.fib n : ℤ) * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show k + 1 + 1 = k + 2 by ring, fib2 k]
    ring

theorem S0_closed (n : ℕ) :
    ∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib i : ℤ) =
      (Nat.fib n : ℤ) * Nat.fib (n + 1) - Nat.fib n * Nat.fib n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, show k + 1 + 1 = k + 2 by ring, fib2 k]
    ring

theorem P_closed (n : ℕ) :
    2 * ∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib (i + 1) : ℤ) =
      2 * (Nat.fib n : ℤ) * Nat.fib n - 1 + (-1) ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ]
    linear_combination ih + (-2 : ℤ) * cassini k

/-- The 2 X 2 determinant det(1 - V U) as a function of n. -/
def Dz (n : ℕ) : ℤ :=
  (1 - ∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib i : ℤ)) *
      (1 - ∑ i ∈ Finset.range n, (Nat.fib (i + 1) : ℤ) * (Nat.fib (i + 1) : ℤ)) -
    (∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib (i + 1) : ℤ)) *
      (∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib (i + 1) : ℤ))

theorem incr (n : ℕ) : Dz (n + 1) = Dz n - (2 * (Nat.fib n : ℤ) * Nat.fib n + (-1) ^ n) := by
  have hS0 := S0_closed n
  have hS1 := S1_closed n
  have hP := P_closed n
  have hC := cassini n
  unfold Dz
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  linear_combination ((Nat.fib (n + 1) : ℤ) ^ 2) * hS0 + ((Nat.fib n : ℤ) ^ 2) * hS1 -
    ((Nat.fib n : ℤ) * Nat.fib (n + 1)) * hP - (1 - (Nat.fib n : ℤ) * Nat.fib (n + 1)) * hC

theorem P10 (n : ℕ) : ∑ i ∈ Finset.range n, (Nat.fib (i + 1) : ℤ) * (Nat.fib i : ℤ) =
    ∑ i ∈ Finset.range n, (Nat.fib i : ℤ) * (Nat.fib (i + 1) : ℤ) := by
  refine Finset.sum_congr rfl ?_
  intro i _
  exact mul_comm _ _

theorem a_eq_D (n : ℕ) : a n = Dz n := by
  rw [a_eval, charpoly_eval_one, det_eq, det_two, P10]
  rfl

theorem B_closed (k : ℕ) :
    B (k + 1) = 2 * (Nat.fib k : ℤ) * Nat.fib k + (-1) ^ k ∧
    B (k + 2) = 2 * (Nat.fib (k + 1) : ℤ) * Nat.fib (k + 1) + (-1) ^ (k + 1) ∧
    B (k + 3) = 2 * (Nat.fib (k + 2) : ℤ) * Nat.fib (k + 2) + (-1) ^ (k + 2) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show B 1 = 2 * (Nat.fib 0 : ℤ) * Nat.fib 0 + (-1) ^ 0
      rw [show B 1 = 1 from rfl, Nat.fib_zero]
      norm_num
    · show B 2 = 2 * (Nat.fib 1 : ℤ) * Nat.fib 1 + (-1) ^ 1
      rw [show B 2 = 1 from rfl, Nat.fib_one]
      norm_num
    · show B 3 = 2 * (Nat.fib 2 : ℤ) * Nat.fib 2 + (-1) ^ 2
      rw [show B 3 = 3 from rfl, Nat.fib_two]
      norm_num
  | succ k ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    show B (k + 4) = 2 * (Nat.fib (k + 3) : ℤ) * Nat.fib (k + 3) + (-1) ^ (k + 3)
    have e : B (k + 4) = 2 * B (k + 3) + 2 * B (k + 2) - B (k + 1) := rfl
    have f3 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      exact_mod_cast Nat.fib_add_two (n := k + 1)
    rw [e, h1, h2, h3, f3, fib2 k]
    ring

theorem a_closed (m : ℕ) : a (m + 1) = -∑ k ∈ Finset.Icc 1 m, B (k + 1) := by
  rw [a_eq_D]
  induction m with
  | zero =>
    rw [incr 0, Finset.Icc_eq_empty_of_lt (show 0 < 1 by norm_num), Finset.sum_empty]
    unfold Dz
    simp
  | succ k ih =>
    rw [incr (k + 1), ih, Finset.sum_Icc_succ_top (show 1 ≤ k + 1 by omega),
      (B_closed (k + 1)).1]
    ring

theorem B_nonneg (k : ℕ) (hk : 1 ≤ k) : 0 ≤ B (k + 1) := by
  rw [(B_closed k).1]
  have h : 0 < Nat.fib k := Nat.fib_pos.mpr (by omega)
  have hf : (1 : ℤ) ≤ Nat.fib k := by omega
  rcases neg_one_pow_eq_or ℤ k with hs | hs
  · rw [hs]
    nlinarith
  · rw [hs]
    nlinarith

theorem Q_nonneg (m : ℕ) : 0 ≤ ∑ k ∈ Finset.Icc 1 m, B (k + 1) := by
  apply Finset.sum_nonneg
  intro k hk
  exact B_nonneg k (Finset.mem_Icc.mp hk).1

end K04A110034

open OMA.S_oeis_a110034 K04A110034 in
theorem OMA.solution : type_of% @OMA.S_oeis_a110034.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_closed m, show m + 1 - 1 = m by omega, abs_neg, abs_of_nonneg (Q_nonneg m)]
