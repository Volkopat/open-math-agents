import OMAStatements.S_oeis_a376527

-- Problem: A376527: a(n) = Sum_{k=0..n*(n-1)/2} A227543(n,k)^2 for n >= 0.
-- Upstream: formal-conjectures statements/oeis-a376527.lean:0 (declaration OMA.S_oeis_a376527.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: c^2 and c have the same parity, and the row polynomial R n has degree at most
-- n(n-1)/2, so a(n) has the parity of the row sum R n (1). Setting q = 1 in the recurrence gives
-- the Catalan recurrence, so R n (1) = catalan n. Pairing the terms i and N - i of
-- catalan (N+1) = Sum_i catalan i * catalan (N-i) gives catalan (2m+2) even and
-- catalan (2m+1) = catalan m mod 2, hence catalan n is odd iff n + 1 is a power of 2.

open OMA.S_oeis_a376527 in
theorem OMA.solution : type_of% @OMA.S_oeis_a376527.main := by
  have R0 : R 0 = 1 := by rw [R]
  have Rsucc : ∀ n : ℕ,
      R (n + 1) = ∑ i : Fin n.succ, Polynomial.X ^ (i : ℕ) * R i * R (n - i) := by
    intro n
    rw [R]
  have key : ∀ x y dx dy : ℕ, 2 * dx + 2 * x ≤ x * (x + 1) → 2 * dy + 2 * y ≤ y * (y + 1) →
      2 * (x + dx + dy) ≤ (x + y) * (x + y + 1) := by
    intro x y dx dy hx hy
    have e : (x + y) * (x + y + 1) = x * (x + 1) + y * (y + 1) + 2 * (x * y) := by ring
    omega
  have deg : ∀ n : ℕ, 2 * (R n).natDegree + 2 * n ≤ n * (n + 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · simp [R0]
      · rw [Rsucc]
        have hs : (∑ i : Fin n.succ, Polynomial.X ^ (i : ℕ) * R i * R (n - i)).natDegree ≤
            n * (n + 1) / 2 := by
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro i _
          have hi := i.2
          have h1 := ih i (by omega)
          have h2 := ih (n - i) (by omega)
          have h3 : (Polynomial.X ^ (i : ℕ) * R i * R (n - i)).natDegree ≤
              (i : ℕ) + (R i).natDegree + (R (n - i)).natDegree := by
            calc (Polynomial.X ^ (i : ℕ) * R i * R (n - i)).natDegree
                ≤ (Polynomial.X ^ (i : ℕ) * R i).natDegree + (R (n - i)).natDegree :=
                  Polynomial.natDegree_mul_le
              _ ≤ (Polynomial.X ^ (i : ℕ) : Polynomial ℕ).natDegree + (R i).natDegree +
                  (R (n - i)).natDegree :=
                  Nat.add_le_add_right Polynomial.natDegree_mul_le _
              _ ≤ (i : ℕ) + (R i).natDegree + (R (n - i)).natDegree :=
                  Nat.add_le_add_right
                    (Nat.add_le_add_right (Polynomial.natDegree_X_pow_le _) _) _
          have h4 : 2 * ((i : ℕ) + (R i).natDegree + (R (n - i)).natDegree) ≤ n * (n + 1) := by
            obtain ⟨b, hb⟩ : ∃ b, n = (i : ℕ) + b := ⟨n - i, by omega⟩
            rw [show n - (i : ℕ) = b by omega] at h2 ⊢
            have h5 := key _ _ _ _ h1 h2
            rw [← hb] at h5
            exact h5
          omega
        have hev : n * (n + 1) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self n)
        have e : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
        omega
  have ev : ∀ n : ℕ, (R n).eval 1 = catalan n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · simp [R0]
      · rw [Rsucc, catalan_succ, Polynomial.eval_finsetSum]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, one_pow, one_mul]
        rw [ih i i.2, ih (n - i) (Nat.lt_succ_of_le (Nat.sub_le n i))]
  have sqmod : ∀ c : ℕ, c ^ 2 % 2 = c % 2 := by
    intro c
    rcases Nat.even_or_odd' c with ⟨m, rfl | rfl⟩
    · rw [show (2 * m) ^ 2 = 2 * (2 * m * m) by ring]
      omega
    · rw [show (2 * m + 1) ^ 2 = 2 * (2 * m * m + 2 * m) + 1 by ring]
      omega
  have amod : ∀ n : ℕ, a n % 2 = catalan n % 2 := by
    intro n
    have hd := deg n
    have e : n * (n + 1) = n * (n - 1) + 2 * n := by
      rcases n with _ | m
      · simp
      · rw [show m + 1 - 1 = m by omega]
        ring
    have hlt : (R n).natDegree < n * (n - 1) / 2 + 1 := by omega
    have hev : (R n).eval 1 = ∑ k ∈ Finset.range (n * (n - 1) / 2 + 1), (R n).coeff k := by
      rw [Polynomial.eval_eq_sum_range' hlt]
      simp
    unfold a T
    rw [Finset.sum_nat_mod]
    simp only [sqmod]
    rw [← Finset.sum_nat_mod, ← hev, ev]
  have csum : ∀ N : ℕ,
      catalan (N + 1) = ∑ i ∈ Finset.range (N + 1), catalan i * catalan (N - i) := by
    intro N
    exact (catalan_succ N).trans
      (Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (N - i)) (N + 1))
  have ceven : ∀ m : ℕ, catalan (2 * m + 1 + 1) % 2 = 0 := by
    intro m
    have h1 : ∑ i ∈ Finset.range (2 * m + 1 + 1), catalan i * catalan (2 * m + 1 - i) =
        ∑ i ∈ Finset.range (m + 1), catalan i * catalan (2 * m + 1 - i) +
        ∑ i ∈ Finset.range (m + 1), catalan (m + 1 + i) * catalan (2 * m + 1 - (m + 1 + i)) := by
      rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by ring, Finset.sum_range_add]
    have h2 : ∑ i ∈ Finset.range (m + 1), catalan (m + 1 + i) * catalan (2 * m + 1 - (m + 1 + i)) =
        ∑ i ∈ Finset.range (m + 1), catalan i * catalan (2 * m + 1 - i) := by
      rw [← Finset.sum_range_reflect (fun i => catalan i * catalan (2 * m + 1 - i)) (m + 1)]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mem_range] at hi
      show catalan (m + 1 + i) * catalan (2 * m + 1 - (m + 1 + i)) =
        catalan (m + 1 - 1 - i) * catalan (2 * m + 1 - (m + 1 - 1 - i))
      rw [show m + 1 - 1 - i = m - i by omega, show 2 * m + 1 - (m + 1 + i) = m - i by omega,
        show 2 * m + 1 - (m - i) = m + 1 + i by omega, mul_comm]
    rw [csum, h1, h2]
    omega
  have codd : ∀ m : ℕ, catalan (2 * m + 1) % 2 = catalan m % 2 := by
    intro m
    have h1 : ∑ i ∈ Finset.range (2 * m + 1), catalan i * catalan (2 * m - i) =
        (∑ i ∈ Finset.range m, catalan i * catalan (2 * m - i) + catalan m * catalan (2 * m - m)) +
        ∑ i ∈ Finset.range m, catalan (m + 1 + i) * catalan (2 * m - (m + 1 + i)) := by
      rw [show 2 * m + 1 = (m + 1) + m by ring, Finset.sum_range_add, Finset.sum_range_succ]
    have h2 : ∑ i ∈ Finset.range m, catalan (m + 1 + i) * catalan (2 * m - (m + 1 + i)) =
        ∑ i ∈ Finset.range m, catalan i * catalan (2 * m - i) := by
      rw [← Finset.sum_range_reflect (fun i => catalan i * catalan (2 * m - i)) m]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.mem_range] at hi
      show catalan (m + 1 + i) * catalan (2 * m - (m + 1 + i)) =
        catalan (m - 1 - i) * catalan (2 * m - (m - 1 - i))
      rw [show 2 * m - (m + 1 + i) = m - 1 - i by omega,
        show 2 * m - (m - 1 - i) = m + 1 + i by omega, mul_comm]
    have hm := sqmod (catalan m)
    rw [sq] at hm
    rw [csum, h1, h2, show 2 * m - m = m by omega]
    omega
  have cpar : ∀ n : ℕ, catalan n % 2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
      · rcases m with _ | m
        · constructor
          · intro _
            exact ⟨0, by norm_num⟩
          · intro _
            simp
        · rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, ceven m]
          constructor
          · intro h
            exact absurd h (by norm_num)
          · rintro ⟨k, hk⟩
            rcases k with _ | k
            · rw [pow_zero] at hk
              omega
            · rw [pow_succ] at hk
              omega
      · rw [codd m, ih m (by omega)]
        constructor
        · rintro ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          have hk0 : 0 < 2 ^ k := by positivity
          rw [pow_succ]
          omega
        · rintro ⟨k, hk⟩
          rcases k with _ | k
          · rw [pow_zero] at hk
            exfalso
            omega
          · refine ⟨k, ?_⟩
            rw [pow_succ] at hk
            omega
  intro n
  rw [Nat.odd_iff, amod n]
  exact cpar n
