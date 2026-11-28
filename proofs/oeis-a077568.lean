import OMAStatements.S_oeis_a077568

-- Problem: A077568: a(1,n) as defined in A003148.
-- Upstream: formal-conjectures statements/oeis-a077568.lean:0 (declaration OMA.S_oeis_a077568.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: (-n)_k = (-1)^k k! C(n,k) and (3/2)_k (2k+3) = 3 (5/2)_k, so
-- term n k = 3 C(n,k) (-2)^k / (2k+3) and a(n) = (2n+3)!! S(n), S(n) = Sum_k C(n,k) (-2)^k/(2k+3).
-- Termwise (2n+5) C(n+1,k) - 2(n+1) C(n,k) = (2k+3) C(n+1,k); with the binomial theorem this
-- gives (2n+5) S(n+1) = 2(n+1) S(n) + (-1)^(n+1), hence a(n+1) = 2(n+1) a(n) + (-1)^(n+1) (2n+3)!!.
-- Two steps of this first-order recurrence give the conjectured one.

open OMA.S_oeis_a077568 in
theorem OMA.solution : type_of% @OMA.S_oeis_a077568.main := by
  have hP : ∀ k : ℕ, (ascPochhammer ℚ k).eval (3 / 2 : ℚ) * (2 * (k : ℚ) + 3) =
      3 * (ascPochhammer ℚ k).eval (5 / 2 : ℚ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
      push_cast
      linear_combination (5 / 2 + (k : ℚ)) * ih
  have hP5 : ∀ k : ℕ, (ascPochhammer ℚ k).eval (5 / 2 : ℚ) ≠ 0 := fun k =>
    (ascPochhammer_pos k (5 / 2 : ℚ) (by norm_num)).ne'
  have hN : ∀ n k : ℕ, (ascPochhammer ℚ k).eval (-(n : ℚ)) =
      (-1) ^ k * ((k.factorial : ℚ) * (n.choose k : ℚ)) := by
    intro n k
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose]
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ascPochhammer_succ_eval, ih, Nat.descFactorial_succ]
      rcases Nat.lt_or_ge n k with h | h
      · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
        simp
      · push_cast [Nat.cast_sub h]
        ring
  have hT : ∀ n k : ℕ, term n k =
      3 * ((n.choose k : ℚ) * ((-2 : ℚ) ^ k / (2 * (k : ℚ) + 3))) := by
    intro n k
    have hk : (k.factorial : ℚ) ≠ 0 := by positivity
    have hd : (2 * (k : ℚ) + 3) ≠ 0 := by positivity
    have hinv : (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 3)⁻¹ = 1 := mul_inv_cancel₀ hd
    have h2 : (-2 : ℚ) ^ k = (-1) ^ k * 2 ^ k := neg_pow (2 : ℚ) k
    unfold term
    rw [hN n k, div_eq_iff hk, div_mul_eq_mul_div, div_eq_iff (hP5 k)]
    linear_combination
      ((n.choose k : ℚ) * (-2 : ℚ) ^ k * (2 * (k : ℚ) + 3)⁻¹ * (k.factorial : ℚ)) * hP k -
        ((n.choose k : ℚ) * (-2 : ℚ) ^ k * (k.factorial : ℚ) *
          (ascPochhammer ℚ k).eval (3 / 2 : ℚ)) * hinv -
        ((n.choose k : ℚ) * (k.factorial : ℚ) * (ascPochhammer ℚ k).eval (3 / 2 : ℚ)) * h2
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℚ, ∀ n, S n = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) * ((-2 : ℚ) ^ k / (2 * (k : ℚ) + 3)) := ⟨_, fun _ => rfl⟩
  have haS : ∀ n : ℕ, a n = (Nat.doubleFactorial (2 * n + 3) : ℚ) * S n := by
    intro n
    unfold a
    rw [hS n, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hT n k]
    ring
  have hSrec : ∀ n : ℕ,
      (2 * (n : ℚ) + 5) * S (n + 1) = 2 * ((n : ℚ) + 1) * S n + (-1) ^ (n + 1) := by
    intro n
    have hbin : ∑ k ∈ Finset.range (n + 1 + 1), ((n + 1).choose k : ℚ) * (-2 : ℚ) ^ k =
        (-1) ^ (n + 1) := by
      have h := add_pow (-2 : ℚ) 1 (n + 1)
      rw [show (-2 : ℚ) + 1 = -1 by norm_num] at h
      rw [h]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [one_pow, mul_one]
      ring
    have hext : S n = ∑ k ∈ Finset.range (n + 1 + 1),
        (n.choose k : ℚ) * ((-2 : ℚ) ^ k / (2 * (k : ℚ) + 3)) := by
      rw [hS n, Finset.sum_range_succ _ (n + 1),
        Nat.choose_eq_zero_of_lt (show n < n + 1 by omega), Nat.cast_zero, zero_mul, add_zero]
    rw [hS (n + 1), hext, Finset.mul_sum, Finset.mul_sum, ← hbin, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' : k ≤ n + 1 := by
      have := Finset.mem_range.mp hk
      omega
    have e := Nat.choose_mul_succ_eq n k
    have q := congrArg (Nat.cast : ℕ → ℚ) e
    push_cast [Nat.cast_sub hk'] at q
    have hd : (2 * (k : ℚ) + 3) ≠ 0 := by positivity
    have hinv : (2 * (k : ℚ) + 3) * (2 * (k : ℚ) + 3)⁻¹ = 1 := mul_inv_cancel₀ hd
    linear_combination (((n + 1).choose k : ℚ) * (-2 : ℚ) ^ k) * hinv -
      (2 * (-2 : ℚ) ^ k * (2 * (k : ℚ) + 3)⁻¹) * q
  have hdf : ∀ m : ℕ, Nat.doubleFactorial (2 * (m + 1) + 3) =
      (2 * m + 3 + 2) * Nat.doubleFactorial (2 * m + 3) := by
    intro m
    rw [show 2 * (m + 1) + 3 = 2 * m + 3 + 2 by ring]
    exact Nat.doubleFactorial_add_two (2 * m + 3)
  have hrec : ∀ m : ℕ, a (m + 1) = 2 * ((m : ℚ) + 1) * a m +
      (-1) ^ (m + 1) * (Nat.doubleFactorial (2 * m + 3) : ℚ) := by
    intro m
    rw [haS (m + 1), haS m, hdf m]
    push_cast
    linear_combination (Nat.doubleFactorial (2 * m + 3) : ℚ) * hSrec m
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have r1 := hrec (m + 1)
  have r0 := hrec m
  rw [show m + 1 + 1 = m + 2 by omega, hdf m] at r1
  push_cast at r1 ⊢
  linear_combination r1 + (2 * (m : ℚ) + 5) * r0
