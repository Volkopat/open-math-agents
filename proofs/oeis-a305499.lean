import OMAStatements.S_oeis_a305499

-- Problem: A305499: Square array A(n,k), n > 0 and k > 0, read by antidiagonals, with initial values A(1,k) = k and recurrence equations A(n+1,k) = A(n,k) for 0 < k <= n and A(n+1,k) = A(n,k) - A000035(n+k) for 0 < n < k.
-- Upstream: formal-conjectures statements/oeis-a305499.lean:0 (declaration OMA.S_oeis_a305499.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: by induction on the row, A(m+1,k) = floor((k+1)/2) + [k > m+1] floor((k-m)/2).
-- With F(n,i) the resulting term of the antidiagonal sum S(n), one has F(n+1,i) = F(n,i) - [n even,
-- i > n/2] for 1 <= i <= n and F(n+1,n+1) = n+1, so S(n+1) = S(n) + n + 1 - [n even] n/2.
-- Hence 2 S(2t) = 3t(t+1) and 2 S(2t+1) = (3t+2)(t+1), which is the formula of A211538 at n+3.

open OMA.S_oeis_a305499 in
theorem OMA.solution : type_of% @OMA.S_oeis_a305499.main := by
  have hA : ∀ m k : ℕ, A (m + 1) k =
      ((k : ℤ) + 1) / 2 + (if k ≤ m + 1 then 0 else ((k : ℤ) - (m : ℤ)) / 2) := by
    intro m
    induction m with
    | zero =>
      intro k
      show (k : ℤ) = ((k : ℤ) + 1) / 2 + (if k ≤ 0 + 1 then 0 else ((k : ℤ) - ((0 : ℕ) : ℤ)) / 2)
      split_ifs <;> omega
    | succ m ih =>
      intro k
      show (if k ≤ m + 1 then A (m + 1) k else A (m + 1) k - A000035 (m + 1 + k)) =
        ((k : ℤ) + 1) / 2 + (if k ≤ m + 1 + 1 then 0 else ((k : ℤ) - ((m + 1 : ℕ) : ℤ)) / 2)
      rw [ih k]
      unfold A000035
      split_ifs <;> omega
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ → ℤ, ∀ n i, F n i =
      ((i : ℤ) + 1) / 2 + (if i ≤ n - i + 1 then 0 else ((i : ℤ) - ((n - i : ℕ) : ℤ)) / 2) :=
    ⟨fun n i => ((i : ℤ) + 1) / 2 + (if i ≤ n - i + 1 then 0 else ((i : ℤ) - ((n - i : ℕ) : ℤ)) / 2),
      fun _ _ => rfl⟩
  have hsum : ∀ n, ∑ i ∈ Finset.Icc 1 n, A (n + 1 - i) i = ∑ i ∈ Finset.Icc 1 n, F n i := by
    intro n
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨-, hi2⟩ := Finset.mem_Icc.mp hi
    rw [show n + 1 - i = n - i + 1 by omega, hA (n - i) i, hF]
  have hdiff : ∀ n i, i ∈ Finset.Icc 1 n →
      F (n + 1) i = F n i - (if n % 2 = 0 then (if n / 2 < i then (1 : ℤ) else 0) else 0) := by
    intro n i hi
    obtain ⟨-, hi2⟩ := Finset.mem_Icc.mp hi
    rw [hF, hF]
    split_ifs <;> omega
  have hind : ∀ n m : ℕ, ∑ i ∈ Finset.Icc 1 m,
      (if n % 2 = 0 then (if n / 2 < i then (1 : ℤ) else 0) else 0) =
      (if n % 2 = 0 then (if n / 2 < m then (m : ℤ) - ((n / 2 : ℕ) : ℤ) else 0) else 0) := by
    intro n m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
      split_ifs <;> omega
  have hlast : ∀ n : ℕ, F (n + 1) (n + 1) = (n : ℤ) + 1 := by
    intro n
    rw [hF]
    split_ifs <;> omega
  obtain ⟨S, hS⟩ : ∃ S : ℕ → ℤ, ∀ n, S n = ∑ i ∈ Finset.Icc 1 n, F n i :=
    ⟨fun n => ∑ i ∈ Finset.Icc 1 n, F n i, fun _ => rfl⟩
  have hstep : ∀ n : ℕ, S (n + 1) = S n + ((n : ℤ) + 1) -
      (if n % 2 = 0 then (if n / 2 < n then (n : ℤ) - ((n / 2 : ℕ) : ℤ) else 0) else 0) := by
    intro n
    rw [hS, hS, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), Finset.sum_congr rfl (hdiff n),
      Finset.sum_sub_distrib, hind n n, hlast n]
    ring
  have hodd : ∀ t : ℕ, S (2 * t + 1) = S (2 * t) + (t : ℤ) + 1 := by
    intro t
    have e := hstep (2 * t)
    split_ifs at e <;> omega
  have heven : ∀ t : ℕ, S (2 * t + 1 + 1) = S (2 * t + 1) + 2 * (t : ℤ) + 2 := by
    intro t
    have e := hstep (2 * t + 1)
    split_ifs at e <;> omega
  have key : ∀ t : ℕ, 2 * S (2 * t) = 3 * (t : ℤ) * ((t : ℤ) + 1) ∧
      2 * S (2 * t + 1) = (3 * (t : ℤ) + 2) * ((t : ℤ) + 1) := by
    intro t
    induction t with
    | zero =>
      have h0 : S (2 * 0) = 0 := by
        rw [hS]
        simp
      refine ⟨?_, ?_⟩
      · rw [h0]
        norm_num
      · rw [hodd 0, h0]
        norm_num
    | succ t ih =>
      have e1 := heven t
      have e2 := hodd (t + 1)
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring] at e2 ⊢
      rw [Nat.cast_succ] at e2 ⊢
      refine ⟨?_, ?_⟩
      · linear_combination 2 * e1 + ih.2
      · linear_combination 2 * e2 + 2 * e1 + ih.2
  intro n _
  rw [hsum n, ← hS n]
  unfold A211538
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · have k : (2 : ℚ) * (S (2 * t) : ℚ) = 3 * (t : ℚ) * ((t : ℚ) + 1) := by
      exact_mod_cast (key t).1
    rw [Odd.neg_one_pow (show Odd (2 * t + 3) from ⟨t + 1, by ring⟩)]
    push_cast
    linear_combination k / 2
  · have k : (2 : ℚ) * (S (2 * t + 1) : ℚ) = (3 * (t : ℚ) + 2) * ((t : ℚ) + 1) := by
      exact_mod_cast (key t).2
    rw [Even.neg_one_pow (show Even (2 * t + 1 + 3) from ⟨t + 2, by ring⟩)]
    push_cast
    linear_combination k / 2
