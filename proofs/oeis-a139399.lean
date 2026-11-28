import OMAStatements.S_oeis_a139399

-- Problem: A139399: Number of steps to reach a cycle in Collatz problem.
-- Upstream: formal-conjectures statements/oeis-a139399.lean:0 (declaration OMA.S_oeis_a139399.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: f(x) = 1 only for x = 2, and f(x) = 2 only for x = 4. Let K = A006577(n), the least k
-- with f^k(n) = 1. As n > 2, K >= 2, so f^(K-1)(n) = 2 and f^(K-2)(n) = 4. If f^j(n) were in
-- {1, 2, 4} for some j < K-2, then f^(j+2)(n) = 1 (as f(1) = 4, f(4) = 2, f(2) = 1) with j+2 < K,
-- against the choice of K. Hence a(n) = K - 2.

namespace N18A139399

open OMA.S_oeis_a139399

theorem f_eq_one (x : ℕ) (h : f x = 1) : x = 2 := by
  unfold f at h
  by_cases hx : x % 2 = 0
  · rw [if_pos hx] at h
    omega
  · rw [if_neg hx] at h
    omega

theorem f_eq_two (x : ℕ) (h : f x = 2) : x = 4 := by
  unfold f at h
  by_cases hx : x % 2 = 0
  · rw [if_pos hx] at h
    omega
  · rw [if_neg hx] at h
    omega

theorem f_two : f 2 = 1 := by decide

theorem f_four : f 4 = 2 := by decide

theorem it_succ (j n : ℕ) : f^[j + 1] n = f (f^[j] n) := Function.iterate_succ_apply' f j n

theorem key (n : ℕ) (hn : 2 < n) (hex : ∃ k : ℕ, f^[k] n = 1) :
    (a n : ℤ) = (A006577 n : ℤ) - 2 := by
  have hne : ({k : ℕ | f^[k] n = 1} : Set ℕ).Nonempty := hex
  have hK : f^[A006577 n] n = 1 := Nat.sInf_mem hne
  have hmin : ∀ j : ℕ, f^[j] n = 1 → A006577 n ≤ j :=
    fun j hj => Nat.sInf_le (s := {k : ℕ | f^[k] n = 1}) hj
  have hK0 : A006577 n ≠ 0 := by
    intro h0
    have e0 : f^[0] n = n := rfl
    rw [h0, e0] at hK
    omega
  have hK1 : A006577 n ≠ 1 := by
    intro h1
    have e1 : f^[1] n = f n := rfl
    rw [h1, e1] at hK
    have h2 := f_eq_one n hK
    omega
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, A006577 n = J + 1 + 1 := ⟨A006577 n - 2, by omega⟩
  rw [hJ, it_succ, it_succ] at hK
  have hJ4 : f^[J] n = 4 := f_eq_two _ (f_eq_one _ hK)
  have hmem : J ∈ {k : ℕ | f^[k] n = 1 ∨ f^[k] n = 2 ∨ f^[k] n = 4} := by
    show f^[J] n = 1 ∨ f^[J] n = 2 ∨ f^[J] n = 4
    exact Or.inr (Or.inr hJ4)
  have hle : a n ≤ J := Nat.sInf_le hmem
  have hne2 : ({k : ℕ | f^[k] n = 1 ∨ f^[k] n = 2 ∨ f^[k] n = 4} : Set ℕ).Nonempty := ⟨J, hmem⟩
  have hS0 := Nat.sInf_mem hne2
  have hS : f^[a n] n = 1 ∨ f^[a n] n = 2 ∨ f^[a n] n = 4 := hS0
  have hge : J ≤ a n := by
    by_contra hlt
    rcases hS with h1 | h2 | h4
    · have h5 := hmin (a n) h1
      omega
    · have e : f^[a n + 1] n = 1 := by
        rw [it_succ, h2, f_two]
      have h5 := hmin (a n + 1) e
      omega
    · have e : f^[a n + 1 + 1] n = 1 := by
        rw [it_succ, it_succ, h4, f_four, f_two]
      have h5 := hmin (a n + 1 + 1) e
      omega
  have hEq : a n = J := le_antisymm hle hge
  omega

end N18A139399

open OMA.S_oeis_a139399 N18A139399 in
theorem OMA.solution : type_of% @OMA.S_oeis_a139399.main := by
  intro n hn hex
  exact key n hn hex
