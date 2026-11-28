import OMAStatements.S_oeis_a008956

-- Problem oeis-a008956: for the triangle entry(n+1, k+1) = (2n+1)^2 entry(n, k) + entry(n, k+1) with
-- entry(n, 0) = 1, the row sums are Prod_{j < n} ((2j+1)^2 + 1).
-- Upstream: statements/oeis-a008956.lean (declaration OMA.S_oeis_a008956.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: entry(n, k) = 0 for k > n and entry(n, 0) = 1. Summing the recurrence over k gives
-- S(n+1) = 1 + (2n+1)^2 S(n) + (S(n) - 1) = ((2n+1)^2 + 1) S(n), and S(0) = 1.

open Finset OMA.S_oeis_a008956

private lemma entry_eq_zero_a008956 : ∀ n k : ℕ, n < k → entry n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  | succ n ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h : entry (n + 1) (k' + 1) = (2 * n + 1) ^ 2 * entry n k' + entry n (k' + 1) := rfl
    have h1 : n < k' := by omega
    have h2 : n < k' + 1 := by omega
    rw [h, ih k' h1, ih (k' + 1) h2, mul_zero, add_zero]

private lemma entry_zero_right_a008956 : ∀ n : ℕ, entry n 0 = 1 := by
  intro n
  cases n <;> rfl

theorem OMA.solution : type_of% @OMA.S_oeis_a008956.main := by
  intro n
  unfold absOddCoefficient
  induction n with
  | zero => simp [entry]
  | succ n ih =>
    have hshift : ∑ k ∈ range (n + 1), entry n (k + 1) + 1 = ∑ k ∈ range (n + 1), entry n k := by
      have h := Finset.sum_range_succ' (fun k => entry n k) (n + 1)
      have h' := Finset.sum_range_succ (fun k => entry n k) (n + 1)
      have hz : entry n (n + 1) = 0 := entry_eq_zero_a008956 n (n + 1) (by omega)
      rw [entry_zero_right_a008956 n] at h
      rw [hz] at h'
      omega
    have hrec : ∀ k, entry (n + 1) (k + 1) = (2 * n + 1) ^ 2 * entry n k + entry n (k + 1) :=
      fun k => rfl
    have h10 : entry (n + 1) 0 = 1 := rfl
    rw [Finset.sum_range_succ', Finset.prod_range_succ, ← ih, h10]
    simp only [hrec, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [add_assoc, hshift]
    ring
