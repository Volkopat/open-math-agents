import OMAStatements.S_oeis_a188648

-- Problem: A188648: Binomial sums a(n) = Sum_{k=0..n} (binomial(2n-k,k))^2.
-- Upstream: formal-conjectures statements/oeis-a188648.lean:0 (declaration OMA.S_oeis_a188648.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: term n (k+1) = term n k * (k-n)^2 (n+1+k)^2 / ((1/2+k)^2 (1+k) 16 (k+1)). Hence
-- term n k = binomial(n+k,2k)^2 for k <= n, and term n k = 0 for k > n. Reversing the order of
-- summation, a(n) = Sum_{k=0..n} binomial(n+k,2k)^2, which is the finite sum of the series.

open OMA.S_oeis_a188648 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188648.main := by
  have hR : ∀ n k : ℕ, term n (k + 1) = term n k *
      (((k : ℚ) - n) ^ 2 * ((n : ℚ) + 1 + k) ^ 2 /
        ((1 / 2 + (k : ℚ)) ^ 2 * (1 + (k : ℚ)) * 16 * ((k : ℚ) + 1))) := by
    intro n k
    have hC : (ascPochhammer ℚ k).eval (1 / 2 : ℚ) ≠ 0 :=
      (ascPochhammer_pos k (1 / 2 : ℚ) (by norm_num)).ne'
    have hD : (ascPochhammer ℚ k).eval (1 : ℚ) ≠ 0 :=
      (ascPochhammer_pos k (1 : ℚ) (by norm_num)).ne'
    have hF : (k.factorial : ℚ) ≠ 0 := by positivity
    have h1 : (1 / 2 + (k : ℚ)) ≠ 0 := by positivity
    have h1' : (1 + 2 * (k : ℚ)) ≠ 0 := by positivity
    have h2 : (1 + (k : ℚ)) ≠ 0 := by positivity
    have h3 : ((k : ℚ) + 1) ≠ 0 := by positivity
    unfold term
    rw [Nat.factorial_succ k]
    simp only [ascPochhammer_succ_eval]
    push_cast
    field_simp
    ring
  have hC0 : ∀ n k : ℕ, k ≤ n → term n k = ((Nat.choose (n + k) (2 * k) : ℕ) : ℚ) ^ 2 := by
    intro n k
    induction k with
    | zero =>
      intro _
      simp [term]
    | succ k ih =>
      intro hk
      rw [hR n k, ih (by omega)]
      have e1 := Nat.add_one_mul_choose_eq (n + k) (2 * k + 1)
      rw [show n + k + 1 = n + (k + 1) by ring, show 2 * k + 1 + 1 = 2 * (k + 1) by ring] at e1
      have q1 := congrArg (Nat.cast : ℕ → ℚ) e1
      push_cast at q1
      have e2 := Nat.choose_succ_right_eq (n + k) (2 * k)
      rw [show n + k - 2 * k = n - k by omega] at e2
      have q2 := congrArg (Nat.cast : ℕ → ℚ) e2
      push_cast [Nat.cast_sub (show k ≤ n by omega)] at q2
      have q3 : ((Nat.choose (n + (k + 1)) (2 * (k + 1)) : ℕ) : ℚ) *
          ((2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1)) =
          ((Nat.choose (n + k) (2 * k) : ℕ) : ℚ) * (((n : ℚ) - k) * ((n : ℚ) + k + 1)) := by
        linear_combination (-(2 * (k : ℚ) + 1)) * q1 + ((n : ℚ) + k + 1) * q2
      have hDen : (1 / 2 + (k : ℚ)) ^ 2 * (1 + (k : ℚ)) * 16 * ((k : ℚ) + 1) ≠ 0 := by
        positivity
      rw [← mul_div_assoc, div_eq_iff hDen]
      linear_combination
        (-(((Nat.choose (n + k) (2 * k) : ℕ) : ℚ) * (((n : ℚ) - k) * ((n : ℚ) + k + 1)) +
          ((Nat.choose (n + (k + 1)) (2 * (k + 1)) : ℕ) : ℚ) *
            ((2 * (k : ℚ) + 2) * (2 * (k : ℚ) + 1)))) * q3
  have hT : ∀ n j : ℕ, term n (n + 1 + j) = 0 := by
    intro n j
    induction j with
    | zero =>
      rw [show n + 1 + 0 = n + 1 by ring, hR n n]
      simp
    | succ j ih =>
      rw [show n + 1 + (j + 1) = n + 1 + j + 1 by ring, hR n (n + 1 + j), ih]
      simp
  intro n
  have hA : a n = ∑ k ∈ Finset.range (n + 1), (Nat.choose (n + k) (2 * k)) ^ 2 := by
    unfold a
    rw [← Finset.sum_range_reflect (fun k => (Nat.choose (2 * n - k) k) ^ 2) (n + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    show (Nat.choose (2 * n - (n + 1 - 1 - j)) (n + 1 - 1 - j)) ^ 2 =
      (Nat.choose (n + j) (2 * j)) ^ 2
    rw [show n + 1 - 1 - j = n + j - 2 * j by omega,
      show 2 * n - (n + j - 2 * j) = n + j by omega,
      Nat.choose_symm (by omega : 2 * j ≤ n + j)]
  have hzero : ∀ k ∉ Finset.range (n + 1), term n k = 0 := by
    intro k hk
    rw [Finset.mem_range, not_lt] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = n + 1 + j := ⟨k - (n + 1), by omega⟩
    exact hT n j
  have heq : ∑ k ∈ Finset.range (n + 1), term n k = (a n : ℚ) := by
    rw [hA]
    push_cast
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact hC0 n k (by omega)
  rw [← heq]
  exact hasSum_sum_of_ne_finset_zero (f := fun k => term n k) hzero
