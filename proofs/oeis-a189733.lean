import OMAStatements.S_oeis_a189733

-- Problem: A189733: Denominator of B(0,n) where B(n,n)=0, B(n-1,n) = (-1)^(n+1)/n, and B(m,n) = B(m+1,n-1) + B(m,n-1), n >= 0, m >= 0, is an array of fractions.
-- Upstream: formal-conjectures statements/oeis-a189733.lean:0 (declaration OMA.S_oeis_a189733.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with S a h = Sum_{j <= a} binomial(a-j, j) h(j), one has
-- U (a+1) m = (-1)^m S a (j -> (-1)^j/(m+j+1)) by the Pascal rule for S. The identity
-- (a+2)/(j+1) binomial(a-j,j) = binomial(a+1-j,j+1) + binomial(a-j,j) gives
-- (a+2) U (a+1) 0 = 1 - f(a+2) + f(a) with f(a) = S a (j -> (-1)^j), and f(a+3) = -f(a).
-- So B(0,n) = c(n)/(n+1) with c = 0,2,3,2,0,-1 repeating, which gives every claim.

open OMA.S_oeis_a189733 in
theorem OMA.solution : type_of% @OMA.S_oeis_a189733.main := by
  have hU0 : ∀ m, U 0 m = 0 := fun _ => rfl
  have hU1 : ∀ m, U 1 m = (-1) ^ (m + 2) / ((m : ℚ) + 1) := fun _ => rfl
  have hU2 : ∀ d m, U (d + 2) m = U (d + 1) m + U d (m + 1) := fun _ _ => rfl
  -- S a h = Sum_{j <= a} binomial(a - j, j) h(j)
  obtain ⟨S, hS⟩ : ∃ S : ℕ → (ℕ → ℚ) → ℚ, ∀ a h,
      S a h = ∑ j ∈ Finset.range (a + 1), ((a - j).choose j : ℚ) * h j := ⟨_, fun _ _ => rfl⟩
  have hS0 : ∀ h, S 0 h = h 0 := by
    intro h
    rw [hS]
    simp
  have hS1 : ∀ h, S 1 h = h 0 := by
    intro h
    rw [hS]
    simp [Finset.sum_range_succ]
  -- the Pascal rule
  have hPas : ∀ (h : ℕ → ℚ) (a : ℕ), S (a + 2) h = S (a + 1) h + S a (fun j => h (j + 1)) := by
    intro h a
    have e1 : S (a + 2) h = ∑ i ∈ Finset.range (a + 1),
        ((a + 2 - (i + 1)).choose (i + 1) : ℚ) * h (i + 1) +
        ((a + 2 - (a + 1 + 1)).choose (a + 1 + 1) : ℚ) * h (a + 1 + 1) +
        ((a + 2 - 0).choose 0 : ℚ) * h 0 := by
      rw [hS, Finset.sum_range_succ', Finset.sum_range_succ]
    have e2 : S (a + 1) h = ∑ i ∈ Finset.range (a + 1),
        ((a + 1 - (i + 1)).choose (i + 1) : ℚ) * h (i + 1) + ((a + 1 - 0).choose 0 : ℚ) * h 0 := by
      rw [hS, Finset.sum_range_succ']
    have e3 : S a (fun j => h (j + 1)) =
        ∑ i ∈ Finset.range (a + 1), ((a - i).choose i : ℚ) * h (i + 1) := by
      rw [hS]
    have key : ∑ i ∈ Finset.range (a + 1), ((a + 2 - (i + 1)).choose (i + 1) : ℚ) * h (i + 1) =
        ∑ i ∈ Finset.range (a + 1), (((a + 1 - (i + 1)).choose (i + 1) : ℚ) * h (i + 1) +
          ((a - i).choose i : ℚ) * h (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≤ a := by
        have := Finset.mem_range.mp hi
        omega
      rw [show a + 2 - (i + 1) = a - i + 1 by omega, show a + 1 - (i + 1) = a - i by omega,
        Nat.choose_succ_succ']
      push_cast
      ring
    rw [e1, e2, e3, key, Finset.sum_add_distrib, show a + 2 - (a + 1 + 1) = 0 by omega,
      Nat.choose_zero_succ, Nat.choose_zero_right, Nat.choose_zero_right]
    simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero]
    ring
  -- U (a+1) m as a sum
  have hL1 : ∀ a : ℕ,
      (∀ m : ℕ, U (a + 1) m = (-1) ^ m * S a (fun j => (-1 : ℚ) ^ j / ((m : ℚ) + j + 1))) ∧
      (∀ m : ℕ, U (a + 2) m = (-1) ^ m * S (a + 1) (fun j => (-1 : ℚ) ^ j / ((m : ℚ) + j + 1))) := by
    intro a
    induction a with
    | zero =>
      have base : ∀ m : ℕ,
          U 1 m = (-1) ^ m * S 0 (fun j => (-1 : ℚ) ^ j / ((m : ℚ) + j + 1)) := by
        intro m
        rw [hU1, hS0, Nat.cast_zero, pow_zero, pow_add]
        ring
      refine ⟨base, fun m => ?_⟩
      rw [hU2 0 m, hU0, add_zero, hS1]
      have hb := base m
      rw [hS0] at hb
      exact hb
    | succ a ih =>
      refine ⟨ih.2, fun m => ?_⟩
      rw [hU2 (a + 1) m]
      have e2 : U (a + 1 + 1) m =
          (-1) ^ m * S (a + 1) (fun j => (-1 : ℚ) ^ j / ((m : ℚ) + j + 1)) := ih.2 m
      have e3 : S (a + 1 + 1) (fun j => (-1 : ℚ) ^ j / ((m : ℚ) + j + 1)) =
          S (a + 1) (fun j => (-1 : ℚ) ^ j / ((m : ℚ) + j + 1)) +
          S a (fun j => (-1 : ℚ) ^ (j + 1) / ((m : ℚ) + ((j + 1 : ℕ) : ℚ) + 1)) := hPas _ a
      have e4 : S a (fun j => (-1 : ℚ) ^ (j + 1) / ((m : ℚ) + ((j + 1 : ℕ) : ℚ) + 1)) =
          -S a (fun j => (-1 : ℚ) ^ j / (((m + 1 : ℕ) : ℚ) + j + 1)) := by
        rw [hS, hS, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        push_cast
        ring
      rw [e2, ih.1 (m + 1), e3, e4]
      ring
  -- (a+2) S a (j -> (-1)^j/(j+1)) = 1 - f(a+2) + f(a)
  have hL2 : ∀ a : ℕ, ((a : ℚ) + 2) * S a (fun j => (-1 : ℚ) ^ j / (((0 : ℕ) : ℚ) + j + 1)) =
      1 - S (a + 2) (fun j => (-1 : ℚ) ^ j) + S a (fun j => (-1 : ℚ) ^ j) := by
    intro a
    have T1 : ((a : ℚ) + 2) * S a (fun j => (-1 : ℚ) ^ j / (((0 : ℕ) : ℚ) + j + 1)) =
        ∑ j ∈ Finset.range (a + 1), ((-1 : ℚ) ^ j * ((a + 1 - j).choose (j + 1) : ℚ) +
          ((a - j).choose j : ℚ) * (-1) ^ j) := by
      rw [hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j ≤ a := by
        have := Finset.mem_range.mp hj
        omega
      have k1 := Nat.add_one_mul_choose_eq (a - j) j
      rw [show a - j + 1 = a + 1 - j by omega] at k1
      have k2 : ((a + 1 - j : ℕ) : ℚ) = (a : ℚ) + 1 - j := by
        rw [Nat.cast_sub (show j ≤ a + 1 by omega), Nat.cast_add, Nat.cast_one]
      have key : ((a : ℚ) + 1 - j) * ((a - j).choose j : ℚ) =
          ((a + 1 - j).choose (j + 1) : ℚ) * ((j : ℚ) + 1) := by
        rw [← k2]
        exact_mod_cast k1
      have hj1 : (j : ℚ) + 1 ≠ 0 := by positivity
      have e : ((a : ℚ) + 2) * ((a - j).choose j : ℚ) / ((j : ℚ) + 1) =
          ((a + 1 - j).choose (j + 1) : ℚ) + ((a - j).choose j : ℚ) := by
        rw [div_eq_iff hj1]
        linear_combination key
      calc ((a : ℚ) + 2) * (((a - j).choose j : ℚ) * ((-1 : ℚ) ^ j / (((0 : ℕ) : ℚ) + j + 1)))
          = (-1) ^ j * (((a : ℚ) + 2) * ((a - j).choose j : ℚ) / ((j : ℚ) + 1)) := by
            rw [Nat.cast_zero]
            ring
        _ = (-1 : ℚ) ^ j * ((a + 1 - j).choose (j + 1) : ℚ) + ((a - j).choose j : ℚ) * (-1) ^ j := by
            rw [e]
            ring
    have f1 : S (a + 2) (fun j => (-1 : ℚ) ^ j) = ∑ i ∈ Finset.range (a + 1),
        ((a + 2 - (i + 1)).choose (i + 1) : ℚ) * (-1) ^ (i + 1) +
        ((a + 2 - (a + 1 + 1)).choose (a + 1 + 1) : ℚ) * (-1) ^ (a + 1 + 1) +
        ((a + 2 - 0).choose 0 : ℚ) * (-1) ^ 0 := by
      rw [hS, Finset.sum_range_succ', Finset.sum_range_succ]
    have f2 : ∑ i ∈ Finset.range (a + 1), ((a + 2 - (i + 1)).choose (i + 1) : ℚ) * (-1) ^ (i + 1) =
        -∑ j ∈ Finset.range (a + 1), (-1 : ℚ) ^ j * ((a + 1 - j).choose (j + 1) : ℚ) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≤ a := by
        have := Finset.mem_range.mp hi
        omega
      rw [show a + 2 - (i + 1) = a + 1 - i by omega, pow_succ]
      ring
    have T2 : ∑ j ∈ Finset.range (a + 1), (-1 : ℚ) ^ j * ((a + 1 - j).choose (j + 1) : ℚ) =
        1 - S (a + 2) (fun j => (-1 : ℚ) ^ j) := by
      rw [f1, f2, show a + 2 - (a + 1 + 1) = 0 by omega, Nat.choose_zero_succ,
        Nat.choose_zero_right]
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, add_zero, pow_zero, mul_one]
      ring
    have T3 : ∑ j ∈ Finset.range (a + 1), ((a - j).choose j : ℚ) * (-1 : ℚ) ^ j =
        S a (fun j => (-1 : ℚ) ^ j) := by
      rw [hS]
    rw [T1, Finset.sum_add_distrib, T2, T3]
  -- f(a) = S a (j -> (-1)^j) is 6-periodic
  have hrec : ∀ a, S (a + 2) (fun j => (-1 : ℚ) ^ j) =
      S (a + 1) (fun j => (-1 : ℚ) ^ j) - S a (fun j => (-1 : ℚ) ^ j) := by
    intro a
    have e : S a (fun j => (-1 : ℚ) ^ (j + 1)) = -S a (fun j => (-1 : ℚ) ^ j) := by
      rw [hS, hS, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hPas, e]
    ring
  have h3 : ∀ a, S (a + 3) (fun j => (-1 : ℚ) ^ j) = -S a (fun j => (-1 : ℚ) ^ j) := by
    intro a
    have e1 := hrec (a + 1)
    have e0 := hrec a
    rw [show a + 1 + 2 = a + 3 by ring, show a + 1 + 1 = a + 2 by ring] at e1
    rw [e1, e0]
    ring
  have h6 : ∀ a, S (a + 6) (fun j => (-1 : ℚ) ^ j) = S a (fun j => (-1 : ℚ) ^ j) := by
    intro a
    have e := h3 (a + 3)
    rw [show a + 3 + 3 = a + 6 by ring] at e
    rw [e, h3]
    ring
  have hk6 : ∀ k r, S (6 * k + r) (fun j => (-1 : ℚ) ^ j) = S r (fun j => (-1 : ℚ) ^ j) := by
    intro k r
    induction k with
    | zero => rw [Nat.mul_zero, Nat.zero_add]
    | succ k ih => rw [show 6 * (k + 1) + r = 6 * k + r + 6 by ring, h6, ih]
  have v0 : S 0 (fun j => (-1 : ℚ) ^ j) = 1 := by rw [hS0, pow_zero]
  have v1 : S 1 (fun j => (-1 : ℚ) ^ j) = 1 := by rw [hS1, pow_zero]
  have e2 : S 2 (fun j => (-1 : ℚ) ^ j) =
      S 1 (fun j => (-1 : ℚ) ^ j) - S 0 (fun j => (-1 : ℚ) ^ j) := hrec 0
  have e3 : S 3 (fun j => (-1 : ℚ) ^ j) = -S 0 (fun j => (-1 : ℚ) ^ j) := h3 0
  have e4 : S 4 (fun j => (-1 : ℚ) ^ j) = -S 1 (fun j => (-1 : ℚ) ^ j) := h3 1
  have e5 : S 5 (fun j => (-1 : ℚ) ^ j) = -S 2 (fun j => (-1 : ℚ) ^ j) := h3 2
  have e6 : S 6 (fun j => (-1 : ℚ) ^ j) = S 0 (fun j => (-1 : ℚ) ^ j) := h6 0
  have e7 : S 7 (fun j => (-1 : ℚ) ^ j) = S 1 (fun j => (-1 : ℚ) ^ j) := h6 1
  have v2 : S 2 (fun j => (-1 : ℚ) ^ j) = 0 := by
    rw [e2, v1, v0]
    ring
  have v3 : S 3 (fun j => (-1 : ℚ) ^ j) = -1 := by rw [e3, v0]
  have v4 : S 4 (fun j => (-1 : ℚ) ^ j) = -1 := by rw [e4, v1]
  have v5 : S 5 (fun j => (-1 : ℚ) ^ j) = 0 := by rw [e5, v2, neg_zero]
  have v6 : S 6 (fun j => (-1 : ℚ) ^ j) = 1 := by rw [e6, v0]
  have v7 : S 7 (fun j => (-1 : ℚ) ^ j) = 1 := by rw [e7, v1]
  -- (a+2) B(0,a+1)
  have hUa : ∀ a : ℕ, ((a : ℚ) + 2) * U (a + 1) 0 =
      1 - S (a + 2) (fun j => (-1 : ℚ) ^ j) + S a (fun j => (-1 : ℚ) ^ j) := by
    intro a
    rw [(hL1 a).1 0, pow_zero, one_mul]
    exact hL2 a
  -- the values of B(0,n)
  have hW : ∀ k : ℕ, U (6 * k + 1) 0 = ((3 * k + 1 : ℕ) : ℚ)⁻¹ ∧
      U (6 * k + 2) 0 = ((2 * k + 1 : ℕ) : ℚ)⁻¹ ∧ U (6 * k + 3) 0 = ((3 * k + 2 : ℕ) : ℚ)⁻¹ ∧
      U (6 * k + 4) 0 = 0 ∧ U (6 * k + 5) 0 = -((6 * k + 6 : ℕ) : ℚ)⁻¹ ∧
      U (6 * k + 6) 0 = 0 := by
    intro k
    have s0 : S (6 * k) (fun j => (-1 : ℚ) ^ j) = 1 := by
      have e := hk6 k 0
      rw [Nat.add_zero] at e
      rw [e, v0]
    have s1 : S (6 * k + 1) (fun j => (-1 : ℚ) ^ j) = 1 := by rw [hk6, v1]
    have s2 : S (6 * k + 2) (fun j => (-1 : ℚ) ^ j) = 0 := by rw [hk6, v2]
    have s3 : S (6 * k + 3) (fun j => (-1 : ℚ) ^ j) = -1 := by rw [hk6, v3]
    have s4 : S (6 * k + 4) (fun j => (-1 : ℚ) ^ j) = -1 := by rw [hk6, v4]
    have s5 : S (6 * k + 5) (fun j => (-1 : ℚ) ^ j) = 0 := by rw [hk6, v5]
    have s6 : S (6 * k + 6) (fun j => (-1 : ℚ) ^ j) = 1 := by rw [hk6, v6]
    have s7 : S (6 * k + 7) (fun j => (-1 : ℚ) ^ j) = 1 := by rw [hk6, v7]
    have u1 := hUa (6 * k)
    rw [s2, s0] at u1
    have u2 := hUa (6 * k + 1)
    rw [show 6 * k + 1 + 1 = 6 * k + 2 by ring, show 6 * k + 1 + 2 = 6 * k + 3 by ring, s3,
      s1] at u2
    have u3 := hUa (6 * k + 2)
    rw [show 6 * k + 2 + 1 = 6 * k + 3 by ring, show 6 * k + 2 + 2 = 6 * k + 4 by ring, s4,
      s2] at u3
    have u4 := hUa (6 * k + 3)
    rw [show 6 * k + 3 + 1 = 6 * k + 4 by ring, show 6 * k + 3 + 2 = 6 * k + 5 by ring, s5,
      s3] at u4
    have u5 := hUa (6 * k + 4)
    rw [show 6 * k + 4 + 1 = 6 * k + 5 by ring, show 6 * k + 4 + 2 = 6 * k + 6 by ring, s6,
      s4] at u5
    have u6 := hUa (6 * k + 5)
    rw [show 6 * k + 5 + 1 = 6 * k + 6 by ring, show 6 * k + 5 + 2 = 6 * k + 7 by ring, s7,
      s5] at u6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply eq_inv_of_mul_eq_one_left
      push_cast at u1 ⊢
      linear_combination u1 / 2
    · apply eq_inv_of_mul_eq_one_left
      push_cast at u2 ⊢
      linear_combination u2 / 3
    · apply eq_inv_of_mul_eq_one_left
      push_cast at u3 ⊢
      linear_combination u3 / 2
    · have hc : ((6 * k + 3 : ℕ) : ℚ) + 2 ≠ 0 := by positivity
      have u4' : (((6 * k + 3 : ℕ) : ℚ) + 2) * U (6 * k + 4) 0 = 0 := by
        rw [u4]
        ring
      exact (mul_eq_zero.mp u4').resolve_left hc
    · rw [neg_inv]
      apply eq_inv_of_mul_eq_one_left
      push_cast at u5 ⊢
      linear_combination -u5
    · have hc : ((6 * k + 5 : ℕ) : ℚ) + 2 ≠ 0 := by positivity
      have u6' : (((6 * k + 5 : ℕ) : ℚ) + 2) * U (6 * k + 6) 0 = 0 := by
        rw [u6]
        ring
      exact (mul_eq_zero.mp u6').resolve_left hc
  have hdinv : ∀ b : ℕ, 0 < b → ((b : ℚ)⁻¹).den = b := by
    intro b hb
    rw [Rat.inv_natCast_den, if_neg (show ¬ (b = 0) by omega)]
  -- the closed forms
  have hA : ∀ n : ℕ, a (6 * n) = 1 ∧ a (1 + 6 * n) = 1 + 3 * n ∧ a (2 + 6 * n) = 1 + 2 * n ∧
      a (3 + 6 * n) = 2 + 3 * n ∧ a (4 + 6 * n) = 1 ∧ a (5 + 6 * n) = 6 + 6 * n := by
    intro n
    obtain ⟨w1, w2, w3, w4, w5, -⟩ := hW n
    unfold a
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [show 6 * 0 = 0 from rfl, hU0, Rat.den_zero]
      · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        obtain ⟨-, -, -, -, -, w6⟩ := hW k
        rw [show 6 * (k + 1) = 6 * k + 6 by ring, w6, Rat.den_zero]
    · rw [add_comm, w1, hdinv (3 * n + 1) (by omega)]
      ring
    · rw [add_comm, w2, hdinv (2 * n + 1) (by omega)]
      ring
    · rw [add_comm, w3, hdinv (3 * n + 2) (by omega)]
      ring
    · rw [add_comm, w4, Rat.den_zero]
    · rw [add_comm, w5, Rat.den_neg_eq_den, hdinv (6 * n + 6) (by omega)]
      ring
  refine ⟨hA, ?_⟩
  -- the recurrence
  intro n hn
  obtain ⟨p, r, hr, rfl⟩ : ∃ p r, r < 6 ∧ n = r + 6 * (p + 2) :=
    ⟨n / 6 - 2, n % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  rw [show r + 6 * (p + 2) - 6 = r + 6 * (p + 1) by omega,
    show r + 6 * (p + 2) - 12 = r + 6 * p by omega]
  obtain rfl | rfl | rfl | rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by
    omega
  · simp only [Nat.zero_add]
    rw [(hA (p + 2)).1, (hA (p + 1)).1, (hA p).1]
    norm_num
  · rw [(hA (p + 2)).2.1, (hA (p + 1)).2.1, (hA p).2.1]
    push_cast
    ring
  · rw [(hA (p + 2)).2.2.1, (hA (p + 1)).2.2.1, (hA p).2.2.1]
    push_cast
    ring
  · rw [(hA (p + 2)).2.2.2.1, (hA (p + 1)).2.2.2.1, (hA p).2.2.2.1]
    push_cast
    ring
  · rw [(hA (p + 2)).2.2.2.2.1, (hA (p + 1)).2.2.2.2.1, (hA p).2.2.2.2.1]
    norm_num
  · rw [(hA (p + 2)).2.2.2.2.2, (hA (p + 1)).2.2.2.2.2, (hA p).2.2.2.2.2]
    push_cast
    ring
