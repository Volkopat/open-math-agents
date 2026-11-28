import OMAStatements.S_oeis_a267235

-- Problem: A267235: Number of length-6 0..n arrays with no following elements greater than or equal to the first repeated value.
-- Upstream: formal-conjectures statements/oeis-a267235.lean:0 (declaration OMA.S_oeis_a267235.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: peel off the first entry. If x1 = x2 the condition says that x3, ..., x6 are less
-- than x2; if x1 /= x2 it is the same condition for the shorter array (x2, ..., x6). So with
-- c_L the count for length L, c_6 = S4 + n c_5, c_5 = S3 + n c_4, c_4 = S2 + n c_3,
-- c_3 = S1 + n (n+1)^2, where S_k is the sum of v^k over v = 0..n. The power sums give
-- 60 a(n) + 2n = 60n^6 + 197n^5 + 180n^4 + 45n^3; the recurrence is the vanishing seventh
-- difference of this sextic, and the g.f. follows by comparing coefficients.

open OMA.S_oeis_a267235 in
theorem OMA.solution : type_of% @OMA.S_oeis_a267235.main := by
  -- a sum over x in 0..n of a function that is p at x = e and q elsewhere
  have Lsplit : ∀ (n e p q : ℕ) (f : ℕ → ℕ), e ≤ n → (∀ x, x ≤ n → x ≠ e → f x = q) →
      f e = p → ∑ x ∈ Finset.range (n + 1), f x = p + n * q := by
    intro n e p q f he h1 h2
    have hm : e ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have e1 : ∑ x ∈ (Finset.range (n + 1)).erase e, f x =
        ∑ _x ∈ (Finset.range (n + 1)).erase e, q := by
      refine Finset.sum_congr rfl (fun x hx => h1 x ?_ (Finset.ne_of_mem_erase hx))
      have hx' := Finset.mem_of_mem_erase hx
      rw [Finset.mem_range] at hx'
      omega
    rw [← Finset.add_sum_erase (Finset.range (n + 1)) f hm, h2, e1, Finset.sum_const,
      Finset.card_erase_of_mem hm, Finset.card_range, smul_eq_mul, Nat.add_sub_cancel]
  -- the number of tuples with all entries below v
  have R1 : ∀ n v : ℕ, v ≤ n + 1 →
      ∑ y ∈ Finset.range (n + 1), (if y < v then 1 else 0) = v := by
    intro n v hv
    rw [← Finset.card_filter]
    have e : (Finset.range (n + 1)).filter (fun y => y < v) = Finset.range v := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [e, Finset.card_range]
  have R2 : ∀ n v : ℕ, v ≤ n + 1 →
      ∑ y ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
        (if y.1 < v ∧ y.2 < v then 1 else 0) = v ^ 2 := by
    intro n v hv
    rw [← Finset.card_filter]
    have e : (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun y : ℕ × ℕ => y.1 < v ∧ y.2 < v) = Finset.range v ×ˢ Finset.range v := by
      ext ⟨b1, b2⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    rw [e, Finset.card_product, Finset.card_range]
    ring
  have R3 : ∀ n v : ℕ, v ≤ n + 1 →
      ∑ y ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
        (if y.1 < v ∧ y.2.1 < v ∧ y.2.2 < v then 1 else 0) = v ^ 3 := by
    intro n v hv
    rw [← Finset.card_filter]
    have e : (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun y : ℕ × ℕ × ℕ => y.1 < v ∧ y.2.1 < v ∧ y.2.2 < v) =
        Finset.range v ×ˢ Finset.range v ×ˢ Finset.range v := by
      ext ⟨b1, b2, b3⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    rw [e, Finset.card_product, Finset.card_product, Finset.card_range]
    ring
  have R4 : ∀ n v : ℕ, v ≤ n + 1 →
      ∑ y ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
        Finset.range (n + 1),
        (if y.1 < v ∧ y.2.1 < v ∧ y.2.2.1 < v ∧ y.2.2.2 < v then 1 else 0) = v ^ 4 := by
    intro n v hv
    rw [← Finset.card_filter]
    have e : (Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
        Finset.range (n + 1)).filter
        (fun y : ℕ × ℕ × ℕ × ℕ => y.1 < v ∧ y.2.1 < v ∧ y.2.2.1 < v ∧ y.2.2.2 < v) =
        Finset.range v ×ˢ Finset.range v ×ˢ Finset.range v ×ˢ Finset.range v := by
      ext ⟨b1, b2, b3, b4⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    rw [e, Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_range]
    ring
  -- the sums of the indicators of the case x1 = x2
  have Q4 : ∀ n, ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      (if r.2.1 < r.1 ∧ r.2.2.1 < r.1 ∧ r.2.2.2.1 < r.1 ∧ r.2.2.2.2 < r.1 then 1 else 0) =
      ∑ v ∈ Finset.range (n + 1), v ^ 4 := by
    intro n
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl (fun v hv => R4 n v (by rw [Finset.mem_range] at hv; omega))
  have Q3 : ∀ n, ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1),
      (if r.2.1 < r.1 ∧ r.2.2.1 < r.1 ∧ r.2.2.2 < r.1 then 1 else 0) =
      ∑ v ∈ Finset.range (n + 1), v ^ 3 := by
    intro n
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl (fun v hv => R3 n v (by rw [Finset.mem_range] at hv; omega))
  have Q2 : ∀ n, ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      (if r.2.1 < r.1 ∧ r.2.2 < r.1 then 1 else 0) = ∑ v ∈ Finset.range (n + 1), v ^ 2 := by
    intro n
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl (fun v hv => R2 n v (by rw [Finset.mem_range] at hv; omega))
  have Q1 : ∀ n, ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      (if r.2 < r.1 then 1 else 0) = ∑ v ∈ Finset.range (n + 1), v := by
    intro n
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl (fun v hv => R1 n v (by rw [Finset.mem_range] at hv; omega))
  -- peeling off the first entry
  have P6 : ∀ n (r : ℕ × ℕ × ℕ × ℕ × ℕ), r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) →
      ∑ x ∈ Finset.range (n + 1),
        (if ok x r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 then 1 else 0) =
      (if r.2.1 < r.1 ∧ r.2.2.1 < r.1 ∧ r.2.2.2.1 < r.1 ∧ r.2.2.2.2 < r.1 then 1 else 0) +
      n * (if (r.1 = r.2.1 → r.2.2.1 < r.1 ∧ r.2.2.2.1 < r.1 ∧ r.2.2.2.2 < r.1) ∧
        (r.1 ≠ r.2.1 → r.2.1 = r.2.2.1 → r.2.2.2.1 < r.2.1 ∧ r.2.2.2.2 < r.2.1) ∧
        (r.1 ≠ r.2.1 → r.2.1 ≠ r.2.2.1 → r.2.2.1 = r.2.2.2.1 → r.2.2.2.2 < r.2.2.1)
        then 1 else 0) := by
    intro n r hr
    have hr1 : r.1 ≤ n := by
      rw [Finset.mem_product, Finset.mem_range] at hr
      omega
    exact Lsplit n r.1 _ _ _ hr1
      (fun x hx hne => by split_ifs <;> simp only [ok] at * <;> omega)
      (by exact if_congr (by unfold ok; omega) rfl rfl)
  have P5 : ∀ n (r : ℕ × ℕ × ℕ × ℕ), r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1) →
      ∑ x ∈ Finset.range (n + 1),
        (if (x = r.1 → r.2.1 < x ∧ r.2.2.1 < x ∧ r.2.2.2 < x) ∧
          (x ≠ r.1 → r.1 = r.2.1 → r.2.2.1 < r.1 ∧ r.2.2.2 < r.1) ∧
          (x ≠ r.1 → r.1 ≠ r.2.1 → r.2.1 = r.2.2.1 → r.2.2.2 < r.2.1) then 1 else 0) =
      (if r.2.1 < r.1 ∧ r.2.2.1 < r.1 ∧ r.2.2.2 < r.1 then 1 else 0) +
      n * (if (r.1 = r.2.1 → r.2.2.1 < r.1 ∧ r.2.2.2 < r.1) ∧
        (r.1 ≠ r.2.1 → r.2.1 = r.2.2.1 → r.2.2.2 < r.2.1) then 1 else 0) := by
    intro n r hr
    have hr1 : r.1 ≤ n := by
      rw [Finset.mem_product, Finset.mem_range] at hr
      omega
    exact Lsplit n r.1 _ _ _ hr1 (fun x hx hne => by split_ifs <;> omega)
      (by split_ifs <;> omega)
  have P4 : ∀ n (r : ℕ × ℕ × ℕ), r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) →
      ∑ x ∈ Finset.range (n + 1),
        (if (x = r.1 → r.2.1 < x ∧ r.2.2 < x) ∧ (x ≠ r.1 → r.1 = r.2.1 → r.2.2 < r.1)
          then 1 else 0) =
      (if r.2.1 < r.1 ∧ r.2.2 < r.1 then 1 else 0) +
      n * (if (r.1 = r.2.1 → r.2.2 < r.1) then 1 else 0) := by
    intro n r hr
    have hr1 : r.1 ≤ n := by
      rw [Finset.mem_product, Finset.mem_range] at hr
      omega
    exact Lsplit n r.1 _ _ _ hr1 (fun x hx hne => by split_ifs <;> omega)
      (by split_ifs <;> omega)
  have P3 : ∀ n (r : ℕ × ℕ), r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) →
      ∑ x ∈ Finset.range (n + 1), (if (x = r.1 → r.2 < x) then 1 else 0) =
      (if r.2 < r.1 then 1 else 0) + n * 1 := by
    intro n r hr
    have hr1 : r.1 ≤ n := by
      rw [Finset.mem_product, Finset.mem_range] at hr
      omega
    exact Lsplit n r.1 _ _ _ hr1 (fun x hx hne => by split_ifs <;> omega)
      (by split_ifs <;> omega)
  -- the counts of the arrays of length 6, 5, 4, 3
  have E6 : ∀ n, a n = ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      (if r.2.1 < r.1 ∧ r.2.2.1 < r.1 ∧ r.2.2.2.1 < r.1 ∧ r.2.2.2.2 < r.1 then 1 else 0) +
      n * ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      (if (r.1 = r.2.1 → r.2.2.1 < r.1 ∧ r.2.2.2.1 < r.1 ∧ r.2.2.2.2 < r.1) ∧
        (r.1 ≠ r.2.1 → r.2.1 = r.2.2.1 → r.2.2.2.1 < r.2.1 ∧ r.2.2.2.2 < r.2.1) ∧
        (r.1 ≠ r.2.1 → r.2.1 ≠ r.2.2.1 → r.2.2.1 = r.2.2.2.1 → r.2.2.2.2 < r.2.2.1)
        then 1 else 0) := by
    intro n
    have e0 : a n = ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
        Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
        ∑ x ∈ Finset.range (n + 1),
          (if ok x r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2 then 1 else 0) := by
      unfold a
      rw [Finset.card_filter, Finset.sum_product]
      exact Finset.sum_comm
    rw [e0, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r hr => P6 n r hr)
  have E5 : ∀ n, ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      (if (r.1 = r.2.1 → r.2.2.1 < r.1 ∧ r.2.2.2.1 < r.1 ∧ r.2.2.2.2 < r.1) ∧
        (r.1 ≠ r.2.1 → r.2.1 = r.2.2.1 → r.2.2.2.1 < r.2.1 ∧ r.2.2.2.2 < r.2.1) ∧
        (r.1 ≠ r.2.1 → r.2.1 ≠ r.2.2.1 → r.2.2.1 = r.2.2.2.1 → r.2.2.2.2 < r.2.2.1)
        then 1 else 0) =
      ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1),
      (if r.2.1 < r.1 ∧ r.2.2.1 < r.1 ∧ r.2.2.2 < r.1 then 1 else 0) +
      n * ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1),
      (if (r.1 = r.2.1 → r.2.2.1 < r.1 ∧ r.2.2.2 < r.1) ∧
        (r.1 ≠ r.2.1 → r.2.1 = r.2.2.1 → r.2.2.2 < r.2.1) then 1 else 0) := by
    intro n
    rw [Finset.sum_product, Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r hr => P5 n r hr)
  have E4 : ∀ n, ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ
      Finset.range (n + 1),
      (if (r.1 = r.2.1 → r.2.2.1 < r.1 ∧ r.2.2.2 < r.1) ∧
        (r.1 ≠ r.2.1 → r.2.1 = r.2.2.1 → r.2.2.2 < r.2.1) then 1 else 0) =
      ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      (if r.2.1 < r.1 ∧ r.2.2 < r.1 then 1 else 0) +
      n * ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      (if (r.1 = r.2.1 → r.2.2 < r.1) then 1 else 0) := by
    intro n
    rw [Finset.sum_product, Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r hr => P4 n r hr)
  have E3 : ∀ n, ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      (if (r.1 = r.2.1 → r.2.2 < r.1) then 1 else 0) =
      ∑ r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1), (if r.2 < r.1 then 1 else 0) +
      n * ((n + 1) * (n + 1)) := by
    intro n
    have e2 : ∑ _r ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1), (1 : ℕ) =
        (n + 1) * (n + 1) := by
      rw [Finset.sum_const, Finset.card_product, Finset.card_range, smul_eq_mul, mul_one]
    rw [← e2, Finset.sum_product, Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun r hr => P3 n r hr)
  have hA : ∀ n, a n = ∑ v ∈ Finset.range (n + 1), v ^ 4 + n * (∑ v ∈ Finset.range (n + 1), v ^ 3 +
      n * (∑ v ∈ Finset.range (n + 1), v ^ 2 + n * (∑ v ∈ Finset.range (n + 1), v +
      n * ((n + 1) * (n + 1))))) := by
    intro n
    rw [E6, E5, E4, E3, Q4, Q3, Q2, Q1]
  -- power sums
  have PS1 : ∀ n, 2 * ∑ v ∈ Finset.range (n + 1), v = n * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      linarith
  have PS2 : ∀ n, 6 * ∑ v ∈ Finset.range (n + 1), v ^ 2 = n * (n + 1) * (2 * n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      linarith
  have PS3 : ∀ n, 4 * ∑ v ∈ Finset.range (n + 1), v ^ 3 = n ^ 2 * (n + 1) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      linarith
  have PS4 : ∀ n, 30 * ∑ v ∈ Finset.range (n + 1), v ^ 4 + n * (n + 1) * (2 * n + 1) =
      3 * n ^ 2 * (n + 1) ^ 2 * (2 * n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      linarith
  -- the closed form
  have hcfq : ∀ n : ℕ, (60 : ℚ) * (a n : ℚ) + 2 * (n : ℚ) =
      60 * (n : ℚ) ^ 6 + 197 * (n : ℚ) ^ 5 + 180 * (n : ℚ) ^ 4 + 45 * (n : ℚ) ^ 3 := by
    intro n
    obtain ⟨S1, hS1⟩ : ∃ S1 : ℕ, S1 = ∑ v ∈ Finset.range (n + 1), v := ⟨_, rfl⟩
    obtain ⟨S2, hS2⟩ : ∃ S2 : ℕ, S2 = ∑ v ∈ Finset.range (n + 1), v ^ 2 := ⟨_, rfl⟩
    obtain ⟨S3, hS3⟩ : ∃ S3 : ℕ, S3 = ∑ v ∈ Finset.range (n + 1), v ^ 3 := ⟨_, rfl⟩
    obtain ⟨S4, hS4⟩ : ∃ S4 : ℕ, S4 = ∑ v ∈ Finset.range (n + 1), v ^ 4 := ⟨_, rfl⟩
    have h0 := hA n
    have h1 := PS1 n
    have h2 := PS2 n
    have h3 := PS3 n
    have h4 := PS4 n
    rw [← hS1, ← hS2, ← hS3, ← hS4] at h0
    rw [← hS1] at h1
    rw [← hS2] at h2
    rw [← hS3] at h3
    rw [← hS4] at h4
    have q0 : (a n : ℚ) = (S4 : ℚ) + (n : ℚ) * ((S3 : ℚ) + (n : ℚ) * ((S2 : ℚ) +
        (n : ℚ) * ((S1 : ℚ) + (n : ℚ) * (((n : ℚ) + 1) * ((n : ℚ) + 1))))) := by
      exact_mod_cast h0
    have q1 : (2 : ℚ) * (S1 : ℚ) = (n : ℚ) * ((n : ℚ) + 1) := by
      exact_mod_cast h1
    have q2 : (6 : ℚ) * (S2 : ℚ) = (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) := by
      exact_mod_cast h2
    have q3 : (4 : ℚ) * (S3 : ℚ) = (n : ℚ) ^ 2 * ((n : ℚ) + 1) ^ 2 := by
      exact_mod_cast h3
    have q4 : (30 : ℚ) * (S4 : ℚ) + (n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) =
        3 * (n : ℚ) ^ 2 * ((n : ℚ) + 1) ^ 2 * (2 * (n : ℚ) + 1) := by
      exact_mod_cast h4
    linear_combination 60 * q0 + 2 * q4 + 15 * (n : ℚ) * q3 + 10 * (n : ℚ) ^ 2 * q2 +
      30 * (n : ℚ) ^ 3 * q1
  have hcf : ∀ n, 60 * a n + 2 * n = 60 * n ^ 6 + 197 * n ^ 5 + 180 * n ^ 4 + 45 * n ^ 3 := by
    intro n
    exact_mod_cast hcfq n
  have hcfz : ∀ n : ℕ, (60 : ℤ) * (a n : ℤ) + 2 * (n : ℤ) =
      60 * (n : ℤ) ^ 6 + 197 * (n : ℤ) ^ 5 + 180 * (n : ℤ) ^ 4 + 45 * (n : ℤ) ^ 3 := by
    intro n
    exact_mod_cast hcf n
  have a0 : a 0 = 0 := by
    have h := hcf 0
    norm_num at h
    omega
  have a1 : a 1 = 8 := by
    have h := hcf 1
    norm_num at h
    omega
  have a2 : a 2 = 223 := by
    have h := hcf 2
    norm_num at h
    omega
  have a3 : a 3 = 1790 := by
    have h := hcf 3
    norm_num at h
    omega
  have a4 : a 4 = 8274 := by
    have h := hcf 4
    norm_num at h
    omega
  have a5 : a 5 = 27854 := by
    have h := hcf 5
    norm_num at h
    omega
  have a6 : a 6 = 76237 := by
    have h := hcf 6
    norm_num at h
    omega
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega,
      show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega,
      show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega,
      show k + 8 - 7 = k + 1 by omega]
    have h1 := hcfz (k + 1)
    have h2 := hcfz (k + 2)
    have h3 := hcfz (k + 3)
    have h4 := hcfz (k + 4)
    have h5 := hcfz (k + 5)
    have h6 := hcfz (k + 6)
    have h7 := hcfz (k + 7)
    have h8 := hcfz (k + 8)
    push_cast at h1 h2 h3 h4 h5 h6 h7 h8
    linarith
  · have e : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 7 =
        PowerSeries.mk (fun n => (a n : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 35 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 35 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 5)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 6)
          - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 7 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 35]
      ring
    have e2 : (PowerSeries.X * (8 + 167 * PowerSeries.X + 397 * PowerSeries.X ^ 2 +
        147 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4) : PowerSeries ℚ) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 * PowerSeries.X ^ 1 +
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 167 * PowerSeries.X ^ 2 +
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 397 * PowerSeries.X ^ 3 +
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 147 * PowerSeries.X ^ 4 +
          PowerSeries.X ^ 5 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 167,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 397,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 147]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge m 7 with hm | hm
    · interval_cases m <;> norm_num [a0, a1, a2, a3, a4, a5, a6]
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 7 := ⟨m - 7, by omega⟩
      rw [if_pos (show 1 ≤ j + 7 by omega), if_pos (show 2 ≤ j + 7 by omega),
        if_pos (show 3 ≤ j + 7 by omega), if_pos (show 4 ≤ j + 7 by omega),
        if_pos (show 5 ≤ j + 7 by omega), if_pos (show 6 ≤ j + 7 by omega),
        if_pos (show 7 ≤ j + 7 by omega),
        if_neg (show ¬ (j + 7 = 1) by omega), if_neg (show ¬ (j + 7 = 2) by omega),
        if_neg (show ¬ (j + 7 = 3) by omega), if_neg (show ¬ (j + 7 = 4) by omega),
        if_neg (show ¬ (j + 7 = 5) by omega),
        show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
        show j + 7 - 3 = j + 4 by omega, show j + 7 - 4 = j + 3 by omega,
        show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega,
        show j + 7 - 7 = j by omega]
      have h0 := hcfq j
      have h1 := hcfq (j + 1)
      have h2 := hcfq (j + 2)
      have h3 := hcfq (j + 3)
      have h4 := hcfq (j + 4)
      have h5 := hcfq (j + 5)
      have h6 := hcfq (j + 6)
      have h7 := hcfq (j + 7)
      push_cast at h1 h2 h3 h4 h5 h6 h7
      linarith
