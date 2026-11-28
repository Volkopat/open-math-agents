import OMAStatements.S_oeis_a247727

-- Problem: A247727: Number of length 1+3 0..n arrays with no disjoint pairs in any consecutive four terms having the same sum.
-- Upstream: formal-conjectures statements/oeis-a247727.lean:0 (declaration OMA.S_oeis_a247727.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with A, B, C the three equalities x1+x2 = x3+x4, x1+x3 = x2+x4, x1+x4 = x2+x3,
-- inclusion-exclusion gives a(n) = (n+1)^4 - |A| - |B| - |C| + |AB| + |AC| + |BC| - |ABC|.
-- A and B force x2 = x3, x1 = x4 (and similarly for the other pairs), all three force x1 = ... = x4,
-- so the pair terms are (n+1)^2 and the triple term n+1. Permuting coordinates gives
-- |A| = |B| = |C|, and |A| = sum over (x1, x2) of #{x3 : x3 <= x1+x2 <= x3+n} = (n+1)(2n^2+4n+3)/3.
-- Hence a(n) = n^4 + 2n^3 + 3n^2 + 2n for all n; the recurrence, the g.f. and the e.g.f. follow
-- from this polynomial by comparing coefficients.

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a247727 in
theorem OMA.solution : type_of% @OMA.S_oeis_a247727.main := by
  have quad : ∀ (A B C : ℚ) (N : ℕ), ∑ w ∈ Finset.range N, (A + B * (w : ℚ) + C * (w : ℚ) ^ 2) =
      (N : ℚ) * A + B * ((N : ℚ) * ((N : ℚ) - 1) / 2)
        + C * ((N : ℚ) * ((N : ℚ) - 1) * (2 * (N : ℚ) - 1) / 6) := by
    intro A B C N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have pieZ : ∀ x1 x2 x3 x4 : ℕ,
      (if x1 + x2 ≠ x3 + x4 ∧ x1 + x3 ≠ x2 + x4 ∧ x1 + x4 ≠ x2 + x3 then (1 : ℤ) else 0) =
        1 - (if x1 + x2 = x3 + x4 then 1 else 0) - (if x1 + x3 = x2 + x4 then 1 else 0)
          - (if x1 + x4 = x2 + x3 then 1 else 0) + (if x2 = x3 ∧ x1 = x4 then 1 else 0)
          + (if x2 = x4 ∧ x1 = x3 then 1 else 0) + (if x3 = x4 ∧ x1 = x2 then 1 else 0)
          - (if (x1 = x2 ∧ x2 = x3) ∧ x3 = x4 then 1 else 0) := by
    intro x1 x2 x3 x4
    split_ifs <;> omega
  have pieQ : ∀ t : ℕ × ℕ × ℕ × ℕ,
      (if t.1 + t.2.1 ≠ t.2.2.1 + t.2.2.2 ∧ t.1 + t.2.2.1 ≠ t.2.1 + t.2.2.2 ∧
          t.1 + t.2.2.2 ≠ t.2.1 + t.2.2.1 then (1 : ℚ) else 0) =
        1 - (if t.1 + t.2.1 = t.2.2.1 + t.2.2.2 then (1 : ℚ) else 0)
          - (if t.1 + t.2.2.1 = t.2.1 + t.2.2.2 then (1 : ℚ) else 0)
          - (if t.1 + t.2.2.2 = t.2.1 + t.2.2.1 then (1 : ℚ) else 0)
          + (if t.2.1 = t.2.2.1 ∧ t.1 = t.2.2.2 then (1 : ℚ) else 0)
          + (if t.2.1 = t.2.2.2 ∧ t.1 = t.2.2.1 then (1 : ℚ) else 0)
          + (if t.2.2.1 = t.2.2.2 ∧ t.1 = t.2.1 then (1 : ℚ) else 0)
          - (if (t.1 = t.2.1 ∧ t.2.1 = t.2.2.1) ∧ t.2.2.1 = t.2.2.2 then (1 : ℚ) else 0) := by
    intro t
    have h := congrArg (fun z : ℤ => (z : ℚ)) (pieZ t.1 t.2.1 t.2.2.1 t.2.2.2)
    push_cast at h
    linarith
  have hcl : ∀ n : ℕ, (a n : ℚ) =
      (n : ℚ) ^ 4 + 2 * (n : ℚ) ^ 3 + 3 * (n : ℚ) ^ 2 + 2 * (n : ℚ) := by
    intro n
    have hI : Finset.Icc 0 n = Finset.range (n + 1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_range]
      constructor
      · intro hx
        omega
      · intro hx
        omega
    have memb : ∀ t : ℕ × ℕ × ℕ × ℕ,
        t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ↔
          t.1 ≤ n ∧ t.2.1 ≤ n ∧ t.2.2.1 ≤ n ∧ t.2.2.2 ≤ n := by
      intro t
      simp only [Finset.mem_product, Finset.mem_Icc]
      omega
    have permSum : ∀ (σ τ : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ),
        (∀ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
          σ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n) →
        (∀ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
          τ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n) →
        (∀ t, τ (σ t) = t) → (∀ t, σ (τ t) = t) → ∀ f : ℕ × ℕ × ℕ × ℕ → ℚ,
        ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n, f (σ t) =
          ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n, f t := by
      intro σ τ hσ hτ h1 h2 f
      exact Finset.sum_nbij' σ τ hσ hτ (fun t _ => h1 t) (fun t _ => h2 t) (fun _ _ => rfl)
    have conj : ∀ (P : Prop) [Decidable P] (y : ℕ), y ∈ Finset.Icc 0 n →
        ∑ x ∈ Finset.Icc 0 n, (if P ∧ y = x then (1 : ℚ) else 0) = if P then 1 else 0 := by
      intro P _ y hy
      by_cases hP : P
      · rw [if_pos hP, Finset.sum_eq_single y]
        · rw [if_pos (show P ∧ y = y from ⟨hP, rfl⟩)]
        · intro x _ hx
          rw [if_neg (show ¬ (P ∧ y = x) from fun hh => hx hh.2.symm)]
        · intro hn
          exact (hn hy).elim
      · rw [if_neg hP]
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg (show ¬ (P ∧ y = x) from fun hh => hP hh.1)]
    have L4a : ∀ p q r : ℕ, ∑ x ∈ Finset.Icc 0 n, (if p + q = r + x then (1 : ℚ) else 0) =
        if r ≤ p + q ∧ p + q ≤ r + n then 1 else 0 := by
      intro p q r
      by_cases hc : r ≤ p + q ∧ p + q ≤ r + n
      · rw [if_pos hc, Finset.sum_eq_single (p + q - r)]
        · rw [if_pos (show p + q = r + (p + q - r) by omega)]
        · intro x _ hx
          rw [if_neg (show ¬ (p + q = r + x) by omega)]
        · intro hn
          exact (hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)).elim
      · rw [if_neg hc]
        apply Finset.sum_eq_zero
        intro x hx
        rw [Finset.mem_Icc] at hx
        rw [if_neg (show ¬ (p + q = r + x) by omega)]
    have LT : ∀ s : ℕ, s ≤ 2 * n →
        ∑ w ∈ Finset.Icc 0 n, (if w ≤ s ∧ s ≤ w + n then (1 : ℚ) else 0) =
          if s ≤ n then (s : ℚ) + 1 else 2 * (n : ℚ) + 1 - (s : ℚ) := by
      intro s hs
      rw [Finset.sum_boole]
      by_cases hsn : s ≤ n
      · have e : (Finset.Icc 0 n).filter (fun w => w ≤ s ∧ s ≤ w + n) = Finset.Icc 0 s := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro hw
            omega
          · intro hw
            omega
        rw [e, Nat.card_Icc, Nat.sub_zero, if_pos hsn, Nat.cast_add, Nat.cast_one]
      · have e : (Finset.Icc 0 n).filter (fun w => w ≤ s ∧ s ≤ w + n) =
            Finset.Icc (s - n) n := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro hw
            omega
          · intro hw
            omega
        rw [e, Nat.card_Icc, if_neg hsn]
        have h1 : n + 1 - (s - n) + s = 2 * n + 1 := by omega
        have h2 : ((n + 1 - (s - n) + s : ℕ) : ℚ) = ((2 * n + 1 : ℕ) : ℚ) := by rw [h1]
        push_cast at h2
        linarith
    have LI : ∀ u : ℕ, u ≤ n →
        ∑ v ∈ Finset.Icc 0 n, ∑ w ∈ Finset.Icc 0 n,
          (if w ≤ u + v ∧ u + v ≤ w + n then (1 : ℚ) else 0) =
          ((n : ℚ) + 1) * ((n : ℚ) + 2) / 2 + (n : ℚ) * (u : ℚ) + (-1) * (u : ℚ) ^ 2 := by
      intro u hu
      have t : ∀ v ∈ Finset.Icc 0 n, ∑ w ∈ Finset.Icc 0 n,
          (if w ≤ u + v ∧ u + v ≤ w + n then (1 : ℚ) else 0) =
          if u + v ≤ n then ((u + v : ℕ) : ℚ) + 1 else 2 * (n : ℚ) + 1 - ((u + v : ℕ) : ℚ) := by
        intro v hv
        have hv' := (Finset.mem_Icc.mp hv).2
        exact LT (u + v) (by omega)
      rw [Finset.sum_congr rfl t, hI, show n + 1 = (n + 1 - u) + u by omega, Finset.sum_range_add]
      have t1 : ∀ v ∈ Finset.range (n + 1 - u),
          (if u + v ≤ n then ((u + v : ℕ) : ℚ) + 1 else 2 * (n : ℚ) + 1 - ((u + v : ℕ) : ℚ)) =
            ((u : ℚ) + 1) + 1 * (v : ℚ) + 0 * (v : ℚ) ^ 2 := by
        intro v hv
        have hv' := Finset.mem_range.mp hv
        rw [if_pos (show u + v ≤ n by omega)]
        push_cast
        ring
      have t2 : ∀ j ∈ Finset.range u,
          (if u + (n + 1 - u + j) ≤ n then ((u + (n + 1 - u + j) : ℕ) : ℚ) + 1
            else 2 * (n : ℚ) + 1 - ((u + (n + 1 - u + j) : ℕ) : ℚ)) =
            (n : ℚ) + (-1) * (j : ℚ) + 0 * (j : ℚ) ^ 2 := by
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have e1 : u + (n + 1 - u + j) = n + 1 + j := by omega
        have e : ((u + (n + 1 - u + j) : ℕ) : ℚ) = (n : ℚ) + 1 + (j : ℚ) := by
          exact_mod_cast e1
        rw [if_neg (show ¬ (u + (n + 1 - u + j) ≤ n) by omega), e]
        ring
      rw [Finset.sum_congr rfl t1, Finset.sum_congr rfl t2, quad, quad,
        Nat.cast_sub (show u ≤ n + 1 by omega)]
      push_cast
      ring
    have LG : ∑ u ∈ Finset.Icc 0 n, ∑ v ∈ Finset.Icc 0 n, ∑ w ∈ Finset.Icc 0 n,
        (if w ≤ u + v ∧ u + v ≤ w + n then (1 : ℚ) else 0) =
        ((n : ℚ) + 1) * (2 * (n : ℚ) ^ 2 + 4 * (n : ℚ) + 3) / 3 := by
      have t : ∀ u ∈ Finset.Icc 0 n, ∑ v ∈ Finset.Icc 0 n, ∑ w ∈ Finset.Icc 0 n,
          (if w ≤ u + v ∧ u + v ≤ w + n then (1 : ℚ) else 0) =
          ((n : ℚ) + 1) * ((n : ℚ) + 2) / 2 + (n : ℚ) * (u : ℚ) + (-1) * (u : ℚ) ^ 2 :=
        fun u hu => LI u (Finset.mem_Icc.mp hu).2
      rw [Finset.sum_congr rfl t, hI, quad]
      push_cast
      ring
    have SA : ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
        (if t.1 + t.2.1 = t.2.2.1 + t.2.2.2 then (1 : ℚ) else 0) =
        ((n : ℚ) + 1) * (2 * (n : ℚ) ^ 2 + 4 * (n : ℚ) + 3) / 3 := by
      rw [← LG, Finset.sum_product]
      refine Finset.sum_congr rfl (fun x1 _ => ?_)
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl (fun x2 _ => ?_)
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl (fun x3 _ => ?_)
      exact L4a x1 x2 x3
    have SB : ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
        (if t.1 + t.2.2.1 = t.2.1 + t.2.2.2 then (1 : ℚ) else 0) =
        ((n : ℚ) + 1) * (2 * (n : ℚ) ^ 2 + 4 * (n : ℚ) + 3) / 3 := by
      rw [← SA]
      exact permSum (fun t => (t.1, t.2.2.1, t.2.1, t.2.2.2))
        (fun t => (t.1, t.2.2.1, t.2.1, t.2.2.2))
        (fun t ht => by
          rw [memb] at ht ⊢
          exact ⟨ht.1, ht.2.2.1, ht.2.1, ht.2.2.2⟩)
        (fun t ht => by
          rw [memb] at ht ⊢
          exact ⟨ht.1, ht.2.2.1, ht.2.1, ht.2.2.2⟩)
        (fun _ => rfl) (fun _ => rfl)
        (fun t => if t.1 + t.2.1 = t.2.2.1 + t.2.2.2 then (1 : ℚ) else 0)
    have SC : ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
        (if t.1 + t.2.2.2 = t.2.1 + t.2.2.1 then (1 : ℚ) else 0) =
        ((n : ℚ) + 1) * (2 * (n : ℚ) ^ 2 + 4 * (n : ℚ) + 3) / 3 := by
      rw [← SA]
      exact permSum (fun t => (t.1, t.2.2.2, t.2.1, t.2.2.1))
        (fun t => (t.1, t.2.2.1, t.2.2.2, t.2.1))
        (fun t ht => by
          rw [memb] at ht ⊢
          exact ⟨ht.1, ht.2.2.2, ht.2.1, ht.2.2.1⟩)
        (fun t ht => by
          rw [memb] at ht ⊢
          exact ⟨ht.1, ht.2.2.1, ht.2.2.2, ht.2.1⟩)
        (fun _ => rfl) (fun _ => rfl)
        (fun t => if t.1 + t.2.1 = t.2.2.1 + t.2.2.2 then (1 : ℚ) else 0)
    have SE1 : ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
        (if t.2.1 = t.2.2.1 ∧ t.1 = t.2.2.2 then (1 : ℚ) else 0) = ((n : ℚ) + 1) ^ 2 := by
      have step : ∀ x1 ∈ Finset.Icc 0 n,
          ∑ p ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
            (if p.1 = p.2.1 ∧ x1 = p.2.2 then (1 : ℚ) else 0) = (n : ℚ) + 1 := by
        intro x1 hx1
        have st2 : ∀ x2 ∈ Finset.Icc 0 n, ∑ q ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
            (if x2 = q.1 ∧ x1 = q.2 then (1 : ℚ) else 0) = 1 := by
          intro x2 hx2
          rw [Finset.sum_product]
          exact (Finset.sum_congr rfl (fun x3 _ => conj (x2 = x3) x1 hx1)).trans
            (by rw [Finset.sum_ite_eq, if_pos hx2])
        rw [Finset.sum_product]
        refine (Finset.sum_congr rfl st2).trans ?_
        rw [Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul, mul_one, Nat.cast_add,
          Nat.cast_one]
      calc ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
            (if t.2.1 = t.2.2.1 ∧ t.1 = t.2.2.2 then (1 : ℚ) else 0) =
            ∑ x1 ∈ Finset.Icc 0 n, ((n : ℚ) + 1) := by
              rw [Finset.sum_product]
              exact Finset.sum_congr rfl step
        _ = ((n : ℚ) + 1) ^ 2 := by
              rw [Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul]
              push_cast
              ring
    have SE2 : ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
        (if t.2.1 = t.2.2.2 ∧ t.1 = t.2.2.1 then (1 : ℚ) else 0) = ((n : ℚ) + 1) ^ 2 := by
      rw [← SE1]
      exact permSum (fun t => (t.1, t.2.1, t.2.2.2, t.2.2.1))
        (fun t => (t.1, t.2.1, t.2.2.2, t.2.2.1))
        (fun t ht => by
          rw [memb] at ht ⊢
          exact ⟨ht.1, ht.2.1, ht.2.2.2, ht.2.2.1⟩)
        (fun t ht => by
          rw [memb] at ht ⊢
          exact ⟨ht.1, ht.2.1, ht.2.2.2, ht.2.2.1⟩)
        (fun _ => rfl) (fun _ => rfl)
        (fun t => if t.2.1 = t.2.2.1 ∧ t.1 = t.2.2.2 then (1 : ℚ) else 0)
    have SE3 : ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
        (if t.2.2.1 = t.2.2.2 ∧ t.1 = t.2.1 then (1 : ℚ) else 0) = ((n : ℚ) + 1) ^ 2 := by
      rw [← SE1]
      exact permSum (fun t => (t.1, t.2.2.1, t.2.2.2, t.2.1))
        (fun t => (t.1, t.2.2.2, t.2.1, t.2.2.1))
        (fun t ht => by
          rw [memb] at ht ⊢
          exact ⟨ht.1, ht.2.2.1, ht.2.2.2, ht.2.1⟩)
        (fun t ht => by
          rw [memb] at ht ⊢
          exact ⟨ht.1, ht.2.2.2, ht.2.1, ht.2.2.1⟩)
        (fun _ => rfl) (fun _ => rfl)
        (fun t => if t.2.1 = t.2.2.1 ∧ t.1 = t.2.2.2 then (1 : ℚ) else 0)
    have SE4 : ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
        (if (t.1 = t.2.1 ∧ t.2.1 = t.2.2.1) ∧ t.2.2.1 = t.2.2.2 then (1 : ℚ) else 0) =
        (n : ℚ) + 1 := by
      have step : ∀ x1 ∈ Finset.Icc 0 n,
          ∑ p ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
            (if (x1 = p.1 ∧ p.1 = p.2.1) ∧ p.2.1 = p.2.2 then (1 : ℚ) else 0) = 1 := by
        intro x1 hx1
        have s2 : ∀ x2 ∈ Finset.Icc 0 n, ∑ q ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
            (if (x1 = x2 ∧ x2 = q.1) ∧ q.1 = q.2 then (1 : ℚ) else 0) =
              if x1 = x2 then 1 else 0 := by
          intro x2 hx2
          rw [Finset.sum_product]
          exact (Finset.sum_congr rfl (fun x3 hx3 => conj (x1 = x2 ∧ x2 = x3) x3 hx3)).trans
            (conj (x1 = x2) x2 hx2)
        rw [Finset.sum_product]
        exact (Finset.sum_congr rfl s2).trans (by rw [Finset.sum_ite_eq, if_pos hx1])
      calc ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
            (if (t.1 = t.2.1 ∧ t.2.1 = t.2.2.1) ∧ t.2.2.1 = t.2.2.2 then (1 : ℚ) else 0) =
            ∑ x1 ∈ Finset.Icc 0 n, (1 : ℚ) := by
              rw [Finset.sum_product]
              exact Finset.sum_congr rfl step
        _ = (n : ℚ) + 1 := by
              rw [Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul, mul_one,
                Nat.cast_add, Nat.cast_one]
    have S1 : ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
        (1 : ℚ) = ((n : ℚ) + 1) ^ 4 := by
      rw [Finset.sum_const, Finset.card_product, Finset.card_product, Finset.card_product,
        Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul]
      push_cast
      ring
    have h0 : (a n : ℚ) =
        ∑ t ∈ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n,
          (if t.1 + t.2.1 ≠ t.2.2.1 + t.2.2.2 ∧ t.1 + t.2.2.1 ≠ t.2.1 + t.2.2.2 ∧
            t.1 + t.2.2.2 ≠ t.2.1 + t.2.2.1 then (1 : ℚ) else 0) := by
      unfold a
      exact Finset.natCast_card_filter _ _
    rw [h0, Finset.sum_congr rfl (fun t _ => pieQ t)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [S1, SA, SB, SC, SE1, SE2, SE3, SE4]
    ring
  have hN : ∀ n : ℕ, a n = n ^ 4 + 2 * n ^ 3 + 3 * n ^ 2 + 2 * n := by
    intro n
    exact_mod_cast hcl n
  have q0 : (a 0 : ℚ) = 0 := by
    rw [hcl 0]
    norm_num
  have q1 : (a 1 : ℚ) = 8 := by
    rw [hcl 1]
    norm_num
  have q2 : (a 2 : ℚ) = 48 := by
    rw [hcl 2]
    norm_num
  have q3 : (a 3 : ℚ) = 168 := by
    rw [hcl 3]
    norm_num
  have q4 : (a 4 : ℚ) = 440 := by
    rw [hcl 4]
    norm_num
  refine ⟨fun n _ => hN n, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
      show k + 6 - 5 = k + 1 by omega, hN (k + 6), hN (k + 5), hN (k + 4), hN (k + 3),
      hN (k + 2), hN (k + 1)]
    push_cast
    ring
  · have key : PowerSeries.mk (fun n => (a n : ℚ))
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 *
          (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4)
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 5 =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8
        + PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8
        + PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 := by
      ext m
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow]
      rcases Nat.lt_or_ge m 5 with hm | hm
      · interval_cases m
        · norm_num [q0]
        · norm_num [q0, q1]
        · norm_num [q0, q1, q2]
        · norm_num [q0, q1, q2, q3]
        · norm_num [q0, q1, q2, q3, q4]
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
        rw [if_pos (show 1 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
          if_pos (show 3 ≤ k + 5 by omega), if_pos (show 4 ≤ k + 5 by omega),
          if_pos (show 5 ≤ k + 5 by omega),
          if_neg (show ¬ (k + 5 = 1) by omega), if_neg (show ¬ (k + 5 = 2) by omega),
          if_neg (show ¬ (k + 5 = 3) by omega),
          show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
          show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
          show k + 5 - 5 = k by omega, hN (k + 5), hN (k + 4), hN (k + 3), hN (k + 2),
          hN (k + 1), hN k]
        push_cast
        ring
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8] at key
    linear_combination key
  · have am : ∀ q : ℚ, (algebraMap ℚ ℚ) q = q := fun q => by simp
    have f1 : ∀ k : ℕ, (((k + 1).factorial : ℕ) : ℚ) = ((k : ℚ) + 1) * (k.factorial : ℚ) := by
      intro k
      exact_mod_cast Nat.factorial_succ k
    have f2 : ∀ k : ℕ, (((k + 2).factorial : ℕ) : ℚ) =
        ((k : ℚ) + 2) * ((k : ℚ) + 1) * (k.factorial : ℚ) := by
      intro k
      have e : (k + 2).factorial = (k + 2) * (k + 1) * k.factorial := by
        rw [Nat.factorial_succ (k + 1), Nat.factorial_succ k]
        ring
      exact_mod_cast e
    have f3 : ∀ k : ℕ, (((k + 3).factorial : ℕ) : ℚ) =
        ((k : ℚ) + 3) * ((k : ℚ) + 2) * ((k : ℚ) + 1) * (k.factorial : ℚ) := by
      intro k
      have e : (k + 3).factorial = (k + 3) * (k + 2) * (k + 1) * k.factorial := by
        rw [Nat.factorial_succ (k + 2), Nat.factorial_succ (k + 1), Nat.factorial_succ k]
        ring
      exact_mod_cast e
    have f4 : ∀ k : ℕ, (((k + 4).factorial : ℕ) : ℚ) =
        ((k : ℚ) + 4) * ((k : ℚ) + 3) * ((k : ℚ) + 2) * ((k : ℚ) + 1) * (k.factorial : ℚ) := by
      intro k
      have e : (k + 4).factorial = (k + 4) * (k + 3) * (k + 2) * (k + 1) * k.factorial := by
        rw [Nat.factorial_succ (k + 3), Nat.factorial_succ (k + 2), Nat.factorial_succ (k + 1),
          Nat.factorial_succ k]
        ring
      exact_mod_cast e
    have key2 : PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 * (PowerSeries.exp ℚ * PowerSeries.X ^ 1)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16 * (PowerSeries.exp ℚ * PowerSeries.X ^ 2)
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 * (PowerSeries.exp ℚ * PowerSeries.X ^ 3)
        + PowerSeries.exp ℚ * PowerSeries.X ^ 4 := by
      ext m
      simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mk, PowerSeries.coeff_exp, am]
      rcases Nat.lt_or_ge m 4 with hm | hm
      · interval_cases m
        · norm_num [q0]
        · norm_num [q1]
        · norm_num [q2]
        · norm_num [q3]
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
        rw [if_pos (show 1 ≤ k + 4 by omega), if_pos (show 2 ≤ k + 4 by omega),
          if_pos (show 3 ≤ k + 4 by omega), if_pos (show 4 ≤ k + 4 by omega),
          show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
          show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega, hN (k + 4),
          f4 k, f3 k, f2 k, f1 k]
        have hk : (k.factorial : ℚ) ≠ 0 := by positivity
        have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
        have hk2 : (k : ℚ) + 2 ≠ 0 := by positivity
        have hk3 : (k : ℚ) + 3 ≠ 0 := by positivity
        have hk4 : (k : ℚ) + 4 ≠ 0 := by positivity
        push_cast
        field_simp
        ring
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16] at key2
    linear_combination key2
