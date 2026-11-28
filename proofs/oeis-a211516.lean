import OMAStatements.S_oeis_a211516

-- Problem: A211516: Number of ordered triples (w,x,y) with all terms in {1,...,n} and w^2=x+y.
-- Upstream: formal-conjectures statements/oeis-a211516.lean:0 (declaration OMA.S_oeis_a211516.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for fixed w the pairs (x, y) in {1..n}^2 with x + y = s = w^2 are given by x in an
-- interval, so there are s - 1 of them if s <= n + 1 and 2n + 1 - s otherwise (0 if s > 2n).
-- Hence the term for w is w^2 - 1 for w <= sqrt n, 2n + 1 - w^2 for sqrt n < w <= sqrt (2n), and 0
-- beyond; summing with 1^2 + ... + K^2 = K(K+1)(2K+1)/6 gives the formula.

open OMA.S_oeis_a211516 in
theorem OMA.solution : type_of% @OMA.S_oeis_a211516.main := by
  have inner : ∀ n s x : ℕ, (∑ y ∈ Finset.Icc 1 n, (if s = x + y then 1 else 0 : ℕ)) =
      if x < s ∧ s ≤ x + n then 1 else 0 := by
    intro n s x
    by_cases h : x < s ∧ s ≤ x + n
    · rw [if_pos h, Finset.sum_eq_single (s - x)]
      · rw [if_pos (show s = x + (s - x) by omega)]
      · intro y _ hy
        rw [if_neg (show ¬ s = x + y by omega)]
      · intro hn
        exact (hn (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).elim
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro y hy
      rw [Finset.mem_Icc] at hy
      rw [if_neg (show ¬ s = x + y by omega)]
  have pairs : ∀ n s : ℕ,
      (∑ x ∈ Finset.Icc 1 n, ∑ y ∈ Finset.Icc 1 n, (if s = x + y then 1 else 0 : ℕ)) =
        if s ≤ n + 1 then s - 1 else 2 * n + 1 - s := by
    intro n s
    rw [Finset.sum_congr rfl (fun x _ => inner n s x), ← Finset.card_filter]
    by_cases hs : s ≤ n + 1
    · rw [if_pos hs]
      have e : (Finset.Icc 1 n).filter (fun x => x < s ∧ s ≤ x + n) = Finset.Icc 1 (s - 1) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro hx
          omega
        · intro hx
          omega
      rw [e, Nat.card_Icc]
      omega
    · rw [if_neg hs]
      have e : (Finset.Icc 1 n).filter (fun x => x < s ∧ s ≤ x + n) = Finset.Icc (s - n) n := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · intro hx
          omega
        · intro hx
          omega
      rw [e, Nat.card_Icc]
      omega
  have sq_sum : ∀ K : ℕ,
      ∑ w ∈ Finset.Icc 1 K, (w : ℚ) ^ 2 = (K : ℚ) * (K + 1) * (2 * K + 1) / 6 := by
    intro K
    induction K with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih]
      push_cast
      ring
  have csum : ∀ K : ℕ, ∀ c : ℚ, ∑ _w ∈ Finset.Icc 1 K, c = (K : ℚ) * c := by
    intro K c
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  intro n
  have hA : a n = ∑ w ∈ Finset.Icc 1 n,
      (if w ^ 2 ≤ n + 1 then w ^ 2 - 1 else 2 * n + 1 - w ^ 2) := by
    unfold a
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.sum_product]
    exact pairs n (w ^ 2)
  have W1n : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have W2n : Nat.sqrt (2 * n) ≤ n := by
    have h := Nat.sqrt_lt'.mpr (show 2 * n < (n + 1) ^ 2 by nlinarith)
    omega
  have point : ∀ w : ℕ, 1 ≤ w →
      ((if w ^ 2 ≤ n + 1 then w ^ 2 - 1 else 2 * n + 1 - w ^ 2 : ℕ) : ℚ) =
        (if w ≤ Nat.sqrt n then (w : ℚ) ^ 2 - 1 else 0)
        + (if w ≤ Nat.sqrt (2 * n) then 2 * (n : ℚ) + 1 - (w : ℚ) ^ 2 else 0)
        - (if w ≤ Nat.sqrt n then 2 * (n : ℚ) + 1 - (w : ℚ) ^ 2 else 0) := by
    intro w hw
    have h1 : 1 ≤ w ^ 2 := Nat.one_le_pow _ _ hw
    rcases le_or_gt w (Nat.sqrt n) with hle | hlt
    · have hn : w ^ 2 ≤ n := Nat.le_sqrt'.mp hle
      have hle2 : w ≤ Nat.sqrt (2 * n) := Nat.le_sqrt'.mpr (by omega)
      rw [if_pos hle, if_pos hle, if_pos hle2, if_pos (show w ^ 2 ≤ n + 1 by omega),
        Nat.cast_sub h1]
      push_cast
      ring
    · have hn : n < w ^ 2 := Nat.sqrt_lt'.mp hlt
      rw [if_neg (show ¬ w ≤ Nat.sqrt n by omega), if_neg (show ¬ w ≤ Nat.sqrt n by omega)]
      rcases le_or_gt w (Nat.sqrt (2 * n)) with hle2 | hlt2
      · have hn2 : w ^ 2 ≤ 2 * n := Nat.le_sqrt'.mp hle2
        rw [if_pos hle2]
        have e : (if w ^ 2 ≤ n + 1 then w ^ 2 - 1 else 2 * n + 1 - w ^ 2) = 2 * n + 1 - w ^ 2 := by
          split_ifs <;> omega
        rw [e, Nat.cast_sub (show w ^ 2 ≤ 2 * n + 1 by omega)]
        push_cast
        ring
      · have hn2 : 2 * n < w ^ 2 := Nat.sqrt_lt'.mp hlt2
        rw [if_neg (show ¬ w ≤ Nat.sqrt (2 * n) by omega)]
        have e : (if w ^ 2 ≤ n + 1 then w ^ 2 - 1 else 2 * n + 1 - w ^ 2) = 0 := by
          split_ifs <;> omega
        rw [e]
        simp
  have filt : ∀ K : ℕ, K ≤ n → (Finset.Icc 1 n).filter (fun w => w ≤ K) = Finset.Icc 1 K := by
    intro K hK
    ext w
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hx
      omega
    · intro hx
      omega
  have hsplit : ∀ K : ℕ, K ≤ n → ∀ f : ℕ → ℚ,
      ∑ w ∈ Finset.Icc 1 n, (if w ≤ K then f w else 0) = ∑ w ∈ Finset.Icc 1 K, f w := by
    intro K hK f
    rw [← Finset.sum_filter, filt K hK]
  rw [hA, Nat.cast_sum,
    Finset.sum_congr rfl (fun w (hw : w ∈ Finset.Icc 1 n) => point w (Finset.mem_Icc.mp hw).1),
    Finset.sum_sub_distrib, Finset.sum_add_distrib, hsplit _ W1n, hsplit _ W2n, hsplit _ W1n]
  simp only [Finset.sum_sub_distrib, sq_sum, csum]
  ring
