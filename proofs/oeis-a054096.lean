import OMAStatements.S_oeis_a054096

-- Problem: A054096: T(n,2), array T as in A054090.
-- Upstream: formal-conjectures statements/oeis-a054096.lean:0 (declaration OMA.S_oeis_a054096.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with r(h) the row sums, the definition gives T(n,k) + T(n-1,k-1) = r(n-1) for
-- 2 <= k <= n (induction on k; the two r(n-1-k) terms cancel). Summing row n, r(n) = 1 + r(n-1)
-- + Sum_{k=2..n} (r(n-1) - T(n-1,k-1)) = (n-1) r(n-1) + 2. Also T(n,2) = r(n-1) - r(n-2). The
-- differences d(m) = r(m) - r(m-1) then satisfy the recurrence of A006183, d(1) = 1, d(2) = 2.

namespace K02A054096

open OMA.S_oeis_a054096

/-- The row sums r(m) = Sum_{j=0..m} T(m,j). -/
def R (m : ℕ) : ℤ := ∑ j ∈ Finset.range (m + 1), T m j

theorem T_k0 (n : ℕ) : T n 0 = 1 := by
  rw [T]

theorem T_s1 (n : ℕ) : T (n + 1) 1 = R n := by
  show T (n + 1) 1 = ∑ j ∈ Finset.range (n + 1), T n j
  rw [T]

theorem T_s2 (n k : ℕ) (h : k + 2 ≤ n + 1) :
    T (n + 1) (k + 2) = T (n + 1) (k + 1) - (-1) ^ (k + 2) * R (n + 1 - (k + 2)) := by
  show T (n + 1) (k + 2) = T (n + 1) (k + 1) -
    (-1) ^ (k + 2) * ∑ j ∈ Finset.range (n + 1 - (k + 2) + 1), T (n + 1 - (k + 2)) j
  rw [T, if_pos h]

theorem T_rec (N K : ℕ) (h2 : 2 ≤ K) (hK : K ≤ N) :
    T N K = T N (K - 1) - (-1) ^ K * R (N - K) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  rw [show k + 2 - 1 = k + 1 by omega]
  exact T_s2 n k hK

theorem T2 (m : ℕ) : T (m + 2) 2 = R (m + 1) - R m := by
  have h := T_rec (m + 2) 2 (by norm_num) (by omega)
  rw [show (2 : ℕ) - 1 = 1 by norm_num, show m + 2 - 2 = m by omega] at h
  have h1 : T (m + 2) 1 = R (m + 1) := T_s1 (m + 1)
  linear_combination h + h1

theorem key (m : ℕ) : ∀ k, k ≤ m → T (m + 2) (k + 2) + T (m + 1) (k + 1) = R (m + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h1 := T2 m
    have h2 : T (m + 1) 1 = R m := T_s1 m
    show T (m + 2) 2 + T (m + 1) 1 = R (m + 1)
    linear_combination h1 + h2
  | succ k ih =>
    intro hk
    have e1 := T_rec (m + 2) (k + 3) (by omega) (by omega)
    rw [show k + 3 - 1 = k + 2 by omega, show m + 2 - (k + 3) = m - k - 1 by omega] at e1
    have e2 := T_rec (m + 1) (k + 2) (by omega) (by omega)
    rw [show k + 2 - 1 = k + 1 by omega, show m + 1 - (k + 2) = m - k - 1 by omega] at e2
    have h := ih (by omega)
    show T (m + 2) (k + 3) + T (m + 1) (k + 2) = R (m + 1)
    linear_combination e1 + e2 + h

theorem rowrec (m : ℕ) : R (m + 2) = ((m : ℤ) + 1) * R (m + 1) + 2 := by
  have e2 : ∑ i ∈ Finset.range (m + 1), T (m + 2) (i + 1 + 1) =
      ∑ k ∈ Finset.range (m + 1), (R (m + 1) - T (m + 1) (k + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h := key m i (by omega)
    show T (m + 2) (i + 2) = R (m + 1) - T (m + 1) (i + 1)
    linear_combination h
  have s1 : R (m + 2) =
      ∑ k ∈ Finset.range (m + 1), (R (m + 1) - T (m + 1) (k + 1)) + R (m + 1) + 1 := by
    have e0 : T (m + 2) 0 = 1 := T_k0 (m + 2)
    have e1 : T (m + 2) (0 + 1) = R (m + 1) := T_s1 (m + 1)
    show ∑ j ∈ Finset.range (m + 2 + 1), T (m + 2) j = _
    rw [Finset.sum_range_succ' _ (m + 2), Finset.sum_range_succ' _ (m + 1), e2, e0, e1]
  have h3 : R (m + 1) = ∑ k ∈ Finset.range (m + 1), T (m + 1) (k + 1) + 1 := by
    have e0 : T (m + 1) 0 = 1 := T_k0 (m + 1)
    show ∑ j ∈ Finset.range (m + 1 + 1), T (m + 1) j = _
    rw [Finset.sum_range_succ' _ (m + 1), e0]
  rw [s1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  linear_combination h3

theorem R0 : R 0 = 1 := by
  have h : R 0 = T 0 0 := by
    show ∑ j ∈ Finset.range (0 + 1), T 0 j = T 0 0
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linear_combination h + T_k0 0

theorem R1 : R 1 = 2 := by
  have h : R 1 = T 1 0 + T 1 1 := by
    show ∑ j ∈ Finset.range (1 + 1), T 1 j = T 1 0 + T 1 1
    rw [Finset.sum_range_succ, Finset.sum_range_one]
  have h11 : T 1 1 = R 0 := T_s1 0
  linear_combination h + T_k0 1 + h11 + R0

theorem rowrec' (m : ℕ) : R (m + 1) = (m : ℤ) * R m + 2 := by
  cases m with
  | zero =>
    show R 1 = ((0 : ℕ) : ℤ) * R 0 + 2
    rw [Nat.cast_zero]
    linear_combination R1
  | succ m =>
    rw [Nat.cast_succ]
    exact rowrec m

theorem Pm (m : ℕ) :
    R (m + 1) - R m = A006183 (m + 1) ∧ R (m + 2) - R (m + 1) = A006183 (m + 2) := by
  induction m with
  | zero =>
    have c1 : A006183 1 = 1 := rfl
    have c2 : A006183 2 = 2 := rfl
    have h : R 2 = (((0 : ℕ) : ℤ) + 1) * R 1 + 2 := rowrec 0
    rw [Nat.cast_zero] at h
    show R 1 - R 0 = A006183 1 ∧ R 2 - R 1 = A006183 2
    rw [c1, c2]
    exact ⟨by linear_combination R1 - R0, by linear_combination h⟩
  | succ m ih =>
    have hc : A006183 (m + 3) = ((m : ℤ) + 3) * A006183 (m + 2) +
        (3 - ((m : ℤ) + 3)) * A006183 (m + 1) := rfl
    have h2 := rowrec' (m + 2)
    have h1 := rowrec' (m + 1)
    have h0 := rowrec' m
    rw [show m + 2 + 1 = m + 3 by omega] at h2
    rw [show m + 1 + 1 = m + 2 by omega] at h1
    push_cast at h2 h1
    show R (m + 2) - R (m + 1) = A006183 (m + 2) ∧ R (m + 3) - R (m + 2) = A006183 (m + 3)
    refine ⟨ih.2, ?_⟩
    rw [hc]
    linear_combination h2 - 2 * h1 + h0 + ((m : ℤ) + 3) * ih.2 - (m : ℤ) * ih.1

end K02A054096

open OMA.S_oeis_a054096 K02A054096 in
theorem OMA.solution : type_of% @OMA.S_oeis_a054096.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  show T (m + 2) 2 = A006183 (m + 1)
  rw [T2 m]
  exact (Pm m).1
