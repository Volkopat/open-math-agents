import OMAStatements.S_oeis_a125792

-- Problem: A125792: Column 2 of table A125790; also equals row sums of matrix power A078121^2.
-- Upstream: formal-conjectures statements/oeis-a125792.lean:0 (declaration OMA.S_oeis_a125792.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: telescoping the recurrence gives T(n+1,k) = Sum_{j=0..k} T(n,2j). Then
-- T(n+1,2k) = N(n,2k+1) for all k, by induction on n: for n = 0 both sides are 2k+1, and
-- N(n+1,2k+1) = Sum_{i=1..2k+1} N(n,2i-1) = Sum_{j=0..2k} N(n,2j+1) = Sum_{j=0..2k} T(n+1,2j)
-- = T(n+2,2k). With k = 1: a(n+1) = T(n+1,2) = N(n,3).

namespace K02A125792

open OMA.S_oeis_a125792

theorem T_zero (k : ℕ) : T 0 k = 1 := by
  rw [T]

theorem T_col0 (n : ℕ) : T n 0 = 1 := by
  cases n with
  | zero => rw [T]
  | succ m => rw [T]

theorem T_ss (n k : ℕ) : T (n + 1) (k + 1) = T (n + 1) k + T n (2 * (k + 1)) := by
  rw [T]

theorem T_sum (n k : ℕ) : T (n + 1) k = ∑ j ∈ Finset.range (k + 1), T n (2 * j) := by
  induction k with
  | zero => simp [T_col0]
  | succ k ih =>
    rw [Finset.sum_range_succ _ (k + 1), T_ss, ih]

theorem Icc_bridge (g : ℕ → ℕ) (m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, g i = ∑ j ∈ Finset.range m, g (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih, Finset.sum_range_succ]

theorem T_N (n : ℕ) : ∀ k : ℕ, T (n + 1) (2 * k) = N n (2 * k + 1) := by
  induction n with
  | zero =>
    intro k
    rw [T_sum]
    simp [T_zero, N]
  | succ n ih =>
    intro k
    rw [T_sum]
    have e : N (n + 1) (2 * k + 1) = ∑ i ∈ Finset.Icc 1 (2 * k + 1), N n (2 * i - 1) := rfl
    rw [e, Icc_bridge]
    apply Finset.sum_congr rfl
    intro j _
    rw [ih j, show 2 * (j + 1) - 1 = 2 * j + 1 by omega]

end K02A125792

open OMA.S_oeis_a125792 K02A125792 in
theorem OMA.solution : type_of% @OMA.S_oeis_a125792.main := by
  intro n _
  have h := T_N n 1
  rw [show 2 * 1 = 2 by norm_num, show 2 + 1 = 3 by norm_num] at h
  exact h
