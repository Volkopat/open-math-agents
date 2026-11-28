import OMAStatements.S_oeis_a106346

-- Problem: A106346: Inverse of number triangle A106344.
-- Upstream: formal-conjectures statements/oeis-a106346.lean:0 (declaration OMA.S_oeis_a106346.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the block M of A106344 is lower triangular with ones on the diagonal, so det M = 1
-- and M^-1 * M = 1. Let e(j) = 1 if j + 1 is a power of 2, else 0. By Lucas, binomial(2^m - 1, r)
-- is odd for r < 2^m, and T(i, j) = 0 unless j <= i <= 2j; so in row i the only j with e(j) = 1
-- and T(i, j) = 1 is j = 2^m - 1 with 2^m <= i + 1 < 2^(m+1). Hence M e = 1, M^-1 1 = e, and the
-- row sums of the inverse are e.

open OMA.S_oeis_a106346 in
theorem OMA.solution : type_of% @OMA.S_oeis_a106346.main := by
  classical
  have hodd : ∀ m r : ℕ, r ≤ 2 ^ m - 1 → Nat.choose (2 ^ m - 1) r % 2 = 1 := by
    intro m
    induction m with
    | zero =>
      intro r hr
      rw [pow_zero] at hr ⊢
      obtain rfl : r = 0 := by omega
      decide
    | succ m ih =>
      intro r hr
      have h1 : 0 < 2 ^ m := Nat.two_pow_pos m
      have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      have hL : Nat.choose (2 ^ (m + 1) - 1) r % 2 =
          (Nat.choose ((2 ^ (m + 1) - 1) % 2) (r % 2) *
            Nat.choose ((2 ^ (m + 1) - 1) / 2) (r / 2)) % 2 :=
        Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := 2 ^ (m + 1) - 1) (k := r) (p := 2)
      have hn2 : (2 ^ (m + 1) - 1) % 2 = 1 := by omega
      have hn1 : (2 ^ (m + 1) - 1) / 2 = 2 ^ m - 1 := by omega
      have hc1 : Nat.choose 1 (r % 2) = 1 := by
        rcases Nat.mod_two_eq_zero_or_one r with h | h
        · simp [h]
        · simp [h]
      rw [hL, hn2, hn1, hc1, one_mul]
      exact ih (r / 2) (by omega)
  intro n
  obtain ⟨e, he⟩ : ∃ e : Fin (n + 1) → ℚ,
      ∀ j, e j = if ∃ m : ℕ, j.val + 1 = 2 ^ m then 1 else 0 := ⟨_, fun _ => rfl⟩
  have hlow : (block n).IsLowerTriangular := by
    intro i j hij
    have hij' : i.val < j.val := Fin.lt_def.mp (OrderDual.toDual_lt_toDual.mp hij)
    show ((T i.val j.val : ℕ) : ℚ) = 0
    rw [T, if_neg (show ¬ (j.val ≤ i.val) by omega), Nat.cast_zero]
  have hdet : (block n).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular _ hlow]
    apply Finset.prod_eq_one
    intro i _
    show ((T i.val i.val : ℕ) : ℚ) = 1
    simp [T]
  have hinv : (block n)⁻¹ * block n = 1 :=
    Matrix.nonsing_inv_mul (A := block n) (by rw [hdet]; exact isUnit_one)
  have hMe : Matrix.mulVec (block n) e = 1 := by
    funext i
    show ∑ j, block n i j * e j = 1
    obtain ⟨m, hm⟩ : ∃ m, m = Nat.log 2 (i.val + 1) := ⟨_, rfl⟩
    have hm1 : 2 ^ m ≤ i.val + 1 := by
      rw [hm]
      exact Nat.pow_log_le_self 2 (Nat.succ_ne_zero _)
    have hm2 : i.val + 1 < 2 ^ (m + 1) := by
      rw [hm]
      exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have hi : i.val < n + 1 := i.isLt
    have hj0 : 2 ^ m - 1 < n + 1 := by omega
    rw [Fintype.sum_eq_single (⟨2 ^ m - 1, hj0⟩ : Fin (n + 1)) ?_]
    · show block n i ⟨2 ^ m - 1, hj0⟩ * e ⟨2 ^ m - 1, hj0⟩ = 1
      have hT : T i.val (2 ^ m - 1) = 1 := by
        rw [T, if_pos (show 2 ^ m - 1 ≤ i.val by omega)]
        exact hodd m (i.val - (2 ^ m - 1)) (by omega)
      have hB : block n i ⟨2 ^ m - 1, hj0⟩ = 1 := by
        show ((T i.val (2 ^ m - 1) : ℕ) : ℚ) = 1
        rw [hT, Nat.cast_one]
      have hE : e ⟨2 ^ m - 1, hj0⟩ = 1 := by
        rw [he]
        exact if_pos ⟨m, by show 2 ^ m - 1 + 1 = 2 ^ m; omega⟩
      rw [hB, hE, mul_one]
    · intro j hj
      show block n i j * e j = 0
      rw [he]
      by_cases hP : ∃ m' : ℕ, j.val + 1 = 2 ^ m'
      · rw [if_pos hP, mul_one]
        obtain ⟨m', hm'⟩ := hP
        show ((T i.val j.val : ℕ) : ℚ) = 0
        rw [T]
        by_cases hji : j.val ≤ i.val
        · rw [if_pos hji]
          by_cases hc : i.val - j.val ≤ j.val
          · exfalso
            apply hj
            have hlog : Nat.log 2 (i.val + 1) = m' :=
              Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by rw [pow_succ]; omega)
            apply Fin.ext
            show j.val = 2 ^ m - 1
            rw [hm, hlog]
            omega
          · simp only [Nat.choose_eq_zero_of_lt (show j.val < i.val - j.val by omega),
              Nat.zero_mod, Nat.cast_zero]
        · rw [if_neg hji, Nat.cast_zero]
      · rw [if_neg hP, mul_zero]
  have hrow : Matrix.mulVec (block n)⁻¹ (1 : Fin (n + 1) → ℚ) = e := by
    rw [← hMe, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have key : ∑ j, (block n)⁻¹ (Fin.last n) j = e (Fin.last n) := by
    rw [← hrow]
    show ∑ j, (block n)⁻¹ (Fin.last n) j =
      ∑ j, (block n)⁻¹ (Fin.last n) j * (1 : Fin (n + 1) → ℚ) j
    simp only [Pi.one_apply, mul_one]
  have hlast : e (Fin.last n) = (A036987 n : ℚ) := by
    rw [he]
    by_cases hP : ∃ m : ℕ, n + 1 = 2 ^ m
    · rw [if_pos (show ∃ m : ℕ, (Fin.last n).val + 1 = 2 ^ m from hP)]
      unfold A036987
      rw [if_pos hP, Nat.cast_one]
    · rw [if_neg (show ¬ ∃ m : ℕ, (Fin.last n).val + 1 = 2 ^ m from hP)]
      unfold A036987
      rw [if_neg hP, Nat.cast_zero]
  have hS : ∀ j : Fin (n + 1), S n j.val = (block n)⁻¹ (Fin.last n) j := by
    intro j
    exact dif_pos (Nat.lt_succ_iff.mp j.isLt)
  rw [Finset.sum_range]
  simp only [hS]
  rw [key, hlast]
