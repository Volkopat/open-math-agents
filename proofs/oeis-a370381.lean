import OMAStatements.S_oeis_a370381

-- Problem: A370381: Array read by downward antidiagonals: A(n,k) = Sum_{j=0..k+1} binomial(k+2, j+1)*A(n-1,j) with A(0,k) = 1, n >= 0, k >= 0.
-- Upstream: formal-conjectures statements/oeis-a370381.lean:0 (declaration OMA.S_oeis_a370381.main)
-- Credit: @umarsxlim (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.S_oeis_a370381

private lemma binom_pow_sum (r k : ℕ) :
    1 + ∑ j ∈ Finset.range (k + 2), (k + 2).choose (j + 1) * r ^ (j + 1) =
      (r + 1) ^ (k + 2) := by
  rw [add_pow, add_comm 1]
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_id]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma connected_sum_reflect (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), connected (i + 1) * (n + 1 - i).factorial =
      ∑ j ∈ Finset.range (n + 1), (j + 1).factorial * connected (n + 1 - j) := by
  rw [← Finset.sum_range_reflect (fun i => connected (i + 1) * (n + 1 - i).factorial) (n + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have h1 : n + 1 - 1 - j + 1 = n + 1 - j := by omega
  have h2 : n + 1 - (n + 1 - 1 - j) = j + 1 := by omega
  rw [h1, h2, mul_comm]

private lemma step_sum_of_row_bowen (n : ℕ)
    (h0 : entry n 0 +
        ∑ i ∈ Finset.range n, connected (i + 1) * (n - i).factorial * (n - i) ^ 1 =
      (n + 1).factorial * (n + 1) ^ 1)
    (hbowen : connected (n + 1) +
        ∑ i ∈ Finset.range n, connected (i + 1) * (n - i).factorial =
      (n + 1).factorial) :
    entry n 0 +
        ∑ i ∈ Finset.range (n + 1), connected (i + 1) * (n + 1 - i).factorial =
      (n + 2).factorial := by
  simp only [pow_one] at h0
  have hsum :
      (∑ i ∈ Finset.range n, connected (i + 1) * (n - i).factorial * (n - i)) +
        (∑ i ∈ Finset.range n, connected (i + 1) * (n - i).factorial) =
      ∑ i ∈ Finset.range n, connected (i + 1) * (n + 1 - i).factorial := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hsub : n + 1 - i = (n - i) + 1 := by omega
    rw [hsub, Nat.factorial_succ]
    ring
  have hsplit :
      ∑ i ∈ Finset.range (n + 1), connected (i + 1) * (n + 1 - i).factorial =
        (∑ i ∈ Finset.range n, connected (i + 1) * (n + 1 - i).factorial) +
          connected (n + 1) := by
    rw [Finset.sum_range_succ]
    simp
  have hrhs :
      (n + 1).factorial * (n + 1) + (n + 1).factorial = (n + 2).factorial := by
    rw [Nat.factorial_succ (n + 1)]
    ring
  linarith

private lemma entry_and_bowen : ∀ n : ℕ,
    (∀ k : ℕ,
      entry n k +
        ∑ i ∈ Finset.range n,
          connected (i + 1) * (n - i).factorial * (n - i) ^ (k + 1) =
        (n + 1).factorial * (n + 1) ^ (k + 1)) ∧
    (connected (n + 1) +
        ∑ i ∈ Finset.range n, connected (i + 1) * (n - i).factorial =
      (n + 1).factorial)
  | 0 => by
    constructor
    · intro k
      simp [entry]
    · rw [connected]
      simp
  | n + 1 => by
    obtain ⟨hrow, hbowen⟩ := entry_and_bowen n
    have hstep_sum := step_sum_of_row_bowen n (hrow 0) hbowen
    have hentry0 : entry n 0 = connected (n + 2) := by
      rw [connected]
      rw [connected_sum_reflect] at hstep_sum
      change entry n 0 =
        (n + 2).factorial -
          ∑ j ∈ Finset.range (n + 1), (j + 1).factorial * connected (n + 1 - j)
      omega
    refine ⟨?_, ?_⟩
    · intro k
      have hmul :
          ∑ j ∈ Finset.range (k + 2),
              (k + 2).choose (j + 1) *
                (entry n j +
                  ∑ i ∈ Finset.range n,
                    connected (i + 1) * (n - i).factorial * (n - i) ^ (j + 1)) =
            ∑ j ∈ Finset.range (k + 2),
              (k + 2).choose (j + 1) * ((n + 1).factorial * (n + 1) ^ (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hrow j]
      have hlhs_expand :
          ∑ j ∈ Finset.range (k + 2),
              (k + 2).choose (j + 1) *
                (entry n j +
                  ∑ i ∈ Finset.range n,
                    connected (i + 1) * (n - i).factorial * (n - i) ^ (j + 1)) =
            entry (n + 1) k +
              ∑ i ∈ Finset.range n,
                connected (i + 1) * (n - i).factorial *
                  (∑ j ∈ Finset.range (k + 2),
                    (k + 2).choose (j + 1) * (n - i) ^ (j + 1)) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        rw [entry]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hrhs_expand :
          ∑ j ∈ Finset.range (k + 2),
              (k + 2).choose (j + 1) * ((n + 1).factorial * (n + 1) ^ (j + 1)) =
            (n + 1).factorial *
              (∑ j ∈ Finset.range (k + 2),
                (k + 2).choose (j + 1) * (n + 1) ^ (j + 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hlhs_expand, hrhs_expand] at hmul
      have hterm :
          (∑ i ∈ Finset.range n,
              connected (i + 1) * (n - i).factorial *
                (∑ j ∈ Finset.range (k + 2),
                  (k + 2).choose (j + 1) * (n - i) ^ (j + 1))) +
            (∑ i ∈ Finset.range n, connected (i + 1) * (n - i).factorial) =
          ∑ i ∈ Finset.range n,
            connected (i + 1) * (n + 1 - i).factorial * (n + 1 - i) ^ (k + 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have hsub : n + 1 - i = (n - i) + 1 := by omega
        have hbin := binom_pow_sum (n - i) k
        calc
          connected (i + 1) * (n - i).factorial *
              (∑ j ∈ Finset.range (k + 2),
                (k + 2).choose (j + 1) * (n - i) ^ (j + 1)) +
            connected (i + 1) * (n - i).factorial
          _ = connected (i + 1) * (n - i).factorial *
              (1 + ∑ j ∈ Finset.range (k + 2),
                (k + 2).choose (j + 1) * (n - i) ^ (j + 1)) := by ring
          _ = connected (i + 1) * (n - i).factorial * (n - i + 1) ^ (k + 2) := by rw [hbin]
          _ = connected (i + 1) * ((n - i + 1) * (n - i).factorial) *
              (n - i + 1) ^ (k + 1) := by
                rw [pow_succ']
                ring
          _ = connected (i + 1) * (n + 1 - i).factorial * (n + 1 - i) ^ (k + 1) := by
                rw [hsub, Nat.factorial_succ]
      have hsplit :
          ∑ i ∈ Finset.range (n + 1),
              connected (i + 1) * (n + 1 - i).factorial * (n + 1 - i) ^ (k + 1) =
            (∑ i ∈ Finset.range n,
              connected (i + 1) * (n + 1 - i).factorial * (n + 1 - i) ^ (k + 1)) +
            connected (n + 1) := by
        rw [Finset.sum_range_succ]
        simp
      have hrhs_final :
          (n + 1).factorial *
              (∑ j ∈ Finset.range (k + 2),
                (k + 2).choose (j + 1) * (n + 1) ^ (j + 1)) +
            (n + 1).factorial =
          (n + 2).factorial * (n + 2) ^ (k + 1) := by
        have hbin := binom_pow_sum (n + 1) k
        calc
          (n + 1).factorial *
              (∑ j ∈ Finset.range (k + 2),
                (k + 2).choose (j + 1) * (n + 1) ^ (j + 1)) +
            (n + 1).factorial
          _ = (n + 1).factorial *
              (1 + ∑ j ∈ Finset.range (k + 2),
                (k + 2).choose (j + 1) * (n + 1) ^ (j + 1)) := by ring
          _ = (n + 1).factorial * (n + 2) ^ (k + 2) := by rw [hbin]
          _ = ((n + 2) * (n + 1).factorial) * (n + 2) ^ (k + 1) := by
                rw [pow_succ']
                ring
          _ = (n + 2).factorial * (n + 2) ^ (k + 1) := by
                rw [Nat.factorial_succ (n + 1)]
      change entry (n + 1) k +
          ∑ i ∈ Finset.range (n + 1),
            connected (i + 1) * (n + 1 - i).factorial * (n + 1 - i) ^ (k + 1) =
        (n + 2).factorial * (n + 2) ^ (k + 1)
      linarith
    · rw [← hentry0]
      exact hstep_sum

end OMA.S_oeis_a370381

theorem OMA.solution : type_of% @OMA.S_oeis_a370381.main := by
  intro n
  obtain ⟨hrow, hbowen⟩ := OMA.S_oeis_a370381.entry_and_bowen n
  have hstep := OMA.S_oeis_a370381.step_sum_of_row_bowen n (hrow 0) hbowen
  rw [OMA.S_oeis_a370381.connected]
  rw [OMA.S_oeis_a370381.connected_sum_reflect] at hstep
  change OMA.S_oeis_a370381.entry n 0 =
    (n + 2).factorial -
      ∑ j ∈ Finset.range (n + 1), (j + 1).factorial * OMA.S_oeis_a370381.connected (n + 1 - j)
  omega
