import OMAStatements.S_oeis_a325046

-- Problem: A325046: G.f.: Sum_{n>=0} x^n * (1 + x^n)^n / (1 - x^(n+1))^(n+1).
-- Upstream: formal-conjectures statements/oeis-a325046.lean:0 (declaration OMA.S_oeis_a325046.main)
-- Credit: @Progren (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset OMA.S_oeis_a325046

private lemma choose_mul_symm (i j k : ℕ) :
    (i + j).choose i * (i + j + k).choose k = (i + k).choose i * (i + k + j).choose j := by
  have hpos : 0 < i.factorial * j.factorial * k.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have h1 : (i + j).choose i * i.factorial * j.factorial = (i + j).factorial := by
    simpa [Nat.add_sub_cancel_left] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
  have h2 : (i + j + k).choose k * k.factorial * (i + j).factorial = (i + j + k).factorial := by
    simpa [Nat.add_sub_cancel] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k (i + j))
  have h3 : (i + k).choose i * i.factorial * k.factorial = (i + k).factorial := by
    simpa [Nat.add_sub_cancel_left] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i k)
  have h4 : (i + k + j).choose j * j.factorial * (i + k).factorial = (i + k + j).factorial := by
    simpa [Nat.add_sub_cancel] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left j (i + k))
  have hl : (i + j).choose i * (i + j + k).choose k * (i.factorial * j.factorial * k.factorial) =
      (i + j + k).factorial := by
    calc (i + j).choose i * (i + j + k).choose k * (i.factorial * j.factorial * k.factorial)
        = (i + j + k).choose k * k.factorial * ((i + j).choose i * i.factorial * j.factorial) := by ring
      _ = (i + j + k).choose k * k.factorial * (i + j).factorial := by rw [h1]
      _ = (i + j + k).factorial := h2
  have hr : (i + k).choose i * (i + k + j).choose j * (i.factorial * j.factorial * k.factorial) =
      (i + k + j).factorial := by
    calc (i + k).choose i * (i + k + j).choose j * (i.factorial * j.factorial * k.factorial)
        = (i + k + j).choose j * j.factorial * ((i + k).choose i * i.factorial * k.factorial) := by ring
      _ = (i + k + j).choose j * j.factorial * (i + k).factorial := by rw [h3]
      _ = (i + k + j).factorial := h4
  rw [hl, hr, Nat.add_right_comm]

private lemma choose_diag_eq (i j : ℕ) :
    (i + j).choose i * (i + j + j).choose j = (i + 2 * j).choose i * (2 * j).choose j := by
  have hpos : 0 < i.factorial * j.factorial * j.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  have h1 : (i + j).choose i * i.factorial * j.factorial = (i + j).factorial := by
    simpa [Nat.add_sub_cancel_left] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
  have h2 : (i + j + j).choose j * j.factorial * (i + j).factorial = (i + j + j).factorial := by
    simpa [Nat.add_sub_cancel] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left j (i + j))
  have h3 : (2 * j).choose j * j.factorial * j.factorial = (2 * j).factorial := by
    have hj : j ≤ 2 * j := by omega
    have hsub : 2 * j - j = j := by omega
    simpa [hsub] using Nat.choose_mul_factorial_mul_factorial hj
  have h4 : (i + 2 * j).choose i * i.factorial * (2 * j).factorial = (i + 2 * j).factorial := by
    simpa [Nat.add_sub_cancel_left] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i (2 * j))
  have hl : (i + j).choose i * (i + j + j).choose j * (i.factorial * j.factorial * j.factorial) =
      (i + j + j).factorial := by
    calc (i + j).choose i * (i + j + j).choose j * (i.factorial * j.factorial * j.factorial)
        = (i + j + j).choose j * j.factorial * ((i + j).choose i * i.factorial * j.factorial) := by ring
      _ = (i + j + j).choose j * j.factorial * (i + j).factorial := by rw [h1]
      _ = (i + j + j).factorial := h2
  have hr : (i + 2 * j).choose i * (2 * j).choose j * (i.factorial * j.factorial * j.factorial) =
      (i + 2 * j).factorial := by
    calc (i + 2 * j).choose i * (2 * j).choose j * (i.factorial * j.factorial * j.factorial)
        = (i + 2 * j).choose i * i.factorial * ((2 * j).choose j * j.factorial * j.factorial) := by ring
      _ = (i + 2 * j).choose i * i.factorial * (2 * j).factorial := by rw [h3]
      _ = (i + 2 * j).factorial := h4
  have hadd : i + j + j = i + 2 * j := by omega
  rw [hl, hr, hadd]

private lemma even_central_choose (j : ℕ) (hj : 0 < j) : Even ((2 * j).choose j) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  have h2 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
  rw [h2, Nat.choose_succ_succ]
  have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    have h := Nat.choose_symm (show m + 1 ≤ 2 * m + 1 by omega)
    have hsub : 2 * m + 1 - (m + 1) = m := by omega
    rw [hsub] at h
    exact h.symm
  rw [hsymm]
  exact ⟨(2 * m + 1).choose m, rfl⟩

private lemma even_diag_term (i j : ℕ) (hj : 0 < j) :
    Even ((i + j).choose i * (i + j + j).choose j) := by
  rw [choose_diag_eq]
  exact (even_central_choose j hj).mul_left _

private lemma even_sum_of_even {α : Type*} (s : Finset α) (f : α → ℕ)
    (h : ∀ x ∈ s, Even (f x)) : Even (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

theorem OMA.solution : type_of% @OMA.S_oeis_a325046.main := by
  intro N
  let f : ℕ × ℕ × ℕ → ℕ := fun t => t.1.choose t.2.1 * (t.1 + t.2.2).choose t.2.2
  change Odd (∑ t ∈ coefficientTerms N, f t) ↔ _
  have hsplit1 : ∑ t ∈ coefficientTerms N, f t =
      (∑ t ∈ (coefficientTerms N).filter (fun t => t.1 - t.2.1 = t.2.2), f t) +
      (∑ t ∈ (coefficientTerms N).filter (fun t => t.1 - t.2.1 ≠ t.2.2), f t) :=
    (Finset.sum_filter_add_sum_filter_not (coefficientTerms N) (fun t => t.1 - t.2.1 = t.2.2) f).symm
  have hoff_even : Even (∑ t ∈ (coefficientTerms N).filter (fun t => t.1 - t.2.1 ≠ t.2.2), f t) := by
    set S_off := (coefficientTerms N).filter (fun t => t.1 - t.2.1 ≠ t.2.2)
    have hsplit2 : ∑ t ∈ S_off, f t =
        (∑ t ∈ S_off.filter (fun t => t.1 - t.2.1 < t.2.2), f t) +
        (∑ t ∈ S_off.filter (fun t => ¬ (t.1 - t.2.1 < t.2.2)), f t) :=
      (Finset.sum_filter_add_sum_filter_not S_off (fun t => t.1 - t.2.1 < t.2.2) f).symm
    have hbij : ∑ t ∈ S_off.filter (fun t => t.1 - t.2.1 < t.2.2), f t =
        ∑ t ∈ S_off.filter (fun t => ¬ (t.1 - t.2.1 < t.2.2)), f t := by
      refine Finset.sum_bij (fun t _ => (t.2.1 + t.2.2, t.2.1, t.1 - t.2.1)) ?_ ?_ ?_ ?_
      · intro t ht
        simp only [S_off, coefficientTerms, mem_filter, mem_product, mem_range] at ht ⊢
        rcases ht with ⟨⟨⟨⟨hn, hi, hk⟩, hin, heq⟩, hne⟩, hlt⟩
        have hsum_le : t.2.1 + t.2.2 ≤ N := by
          have h1 : t.2.1 ≤ t.1 * (t.2.1 + 1) := by nlinarith
          have h2 : t.2.2 ≤ (t.1 + 1) * t.2.2 := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
          omega
        refine ⟨⟨⟨⟨by omega, hi, by omega⟩, by omega, ?_⟩, by omega⟩, by omega⟩
        have hdecomp : t.1 = t.2.1 + (t.1 - t.2.1) := (Nat.add_sub_of_le hin).symm
        nlinarith
      · intro t₁ ht₁ t₂ ht₂ heq
        simp only [S_off, coefficientTerms, mem_filter] at ht₁ ht₂
        rcases t₁ with ⟨n₁, i₁, k₁⟩
        rcases t₂ with ⟨n₂, i₂, k₂⟩
        simp only [Prod.mk.injEq] at heq
        have hin₁ : i₁ ≤ n₁ := ht₁.1.1.2.1
        have hin₂ : i₂ ≤ n₂ := ht₂.1.1.2.1
        ext <;> dsimp <;> omega
      · intro t ht
        simp only [S_off, coefficientTerms, mem_filter, mem_product, mem_range] at ht
        rcases ht with ⟨⟨⟨⟨hn, hi, hk⟩, hin, heq⟩, hne⟩, hnlt⟩
        refine ⟨(t.2.1 + t.2.2, t.2.1, t.1 - t.2.1), ?_, ?_⟩
        · simp only [S_off, coefficientTerms, mem_filter, mem_product, mem_range]
          have hsum_le : t.2.1 + t.2.2 ≤ N := by
            have h1 : t.2.1 ≤ t.1 * (t.2.1 + 1) := by nlinarith
            have h2 : t.2.2 ≤ (t.1 + 1) * t.2.2 := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
            omega
          refine ⟨⟨⟨⟨by omega, hi, by omega⟩, by omega, ?_⟩, by omega⟩, by omega⟩
          have hdecomp : t.1 = t.2.1 + (t.1 - t.2.1) := (Nat.add_sub_of_le hin).symm
          nlinarith
        · rcases t with ⟨n, i, k⟩
          dsimp at hin ⊢
          ext <;> dsimp <;> omega
      · intro t ht
        simp only [S_off, coefficientTerms, mem_filter] at ht
        have hin : t.2.1 ≤ t.1 := ht.1.1.2.1
        dsimp only [f]
        have hdecomp : t.1 = t.2.1 + (t.1 - t.2.1) := (Nat.add_sub_of_le hin).symm
        conv_lhs => rw [hdecomp]
        exact choose_mul_symm t.2.1 (t.1 - t.2.1) t.2.2
    rw [hsplit2, ← hbij]
    exact ⟨_, rfl⟩
  set S_diag := (coefficientTerms N).filter (fun t => t.1 - t.2.1 = t.2.2)
  have hsplit3 : ∑ t ∈ S_diag, f t =
      (∑ t ∈ S_diag.filter (fun t => t.2.2 = 0), f t) +
      (∑ t ∈ S_diag.filter (fun t => t.2.2 ≠ 0), f t) :=
    (Finset.sum_filter_add_sum_filter_not S_diag (fun t => t.2.2 = 0) f).symm
  have hpos_even : Even (∑ t ∈ S_diag.filter (fun t => t.2.2 ≠ 0), f t) := by
    apply even_sum_of_even
    intro t ht
    simp only [S_diag, coefficientTerms, mem_filter] at ht
    have hin : t.2.1 ≤ t.1 := ht.1.1.2.1
    have hjk : t.1 - t.2.1 = t.2.2 := ht.1.2
    have hk : 0 < t.2.2 := Nat.pos_of_ne_zero ht.2
    have hn : t.1 = t.2.1 + t.2.2 := by omega
    dsimp only [f]
    rw [hn]
    exact even_diag_term t.2.1 t.2.2 hk
  set S_zero := S_diag.filter (fun t => t.2.2 = 0)
  have htotal : ∑ t ∈ coefficientTerms N, f t =
      (∑ t ∈ S_zero, f t) +
      ((∑ t ∈ S_diag.filter (fun t => t.2.2 ≠ 0), f t) +
       (∑ t ∈ (coefficientTerms N).filter (fun t => t.1 - t.2.1 ≠ t.2.2), f t)) := by
    rw [hsplit1, hsplit3]; ring
  have heven_tail : Even ((∑ t ∈ S_diag.filter (fun t => t.2.2 ≠ 0), f t) +
      (∑ t ∈ (coefficientTerms N).filter (fun t => t.1 - t.2.1 ≠ t.2.2), f t)) :=
    hpos_even.add hoff_even
  rw [htotal]
  constructor
  · intro hodd
    have hzero_odd : Odd (∑ t ∈ S_zero, f t) := by
      rcases heven_tail with ⟨r, hr⟩
      rcases hodd with ⟨q, hq⟩
      exact ⟨q - r, by omega⟩
    have hne : S_zero.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at hzero_odd
      exact Nat.not_odd_zero hzero_odd
    rcases hne with ⟨t, ht⟩
    simp only [S_zero, S_diag, coefficientTerms, mem_filter] at ht
    refine ⟨t.2.1, ?_⟩
    have hin : t.2.1 ≤ t.1 := ht.1.1.2.1
    have hjk : t.1 - t.2.1 = t.2.2 := ht.1.2
    have hk : t.2.2 = 0 := ht.2
    have hn : t.1 = t.2.1 := by omega
    have heq : t.1 * (t.2.1 + 1) + (t.1 + 1) * t.2.2 = N := ht.1.1.2.2
    rw [hn, hk] at heq
    linarith
  · rintro ⟨m, rfl⟩
    have hSzero : S_zero = {(m, m, 0)} := by
      ext ⟨n, i, k⟩
      simp only [S_zero, S_diag, coefficientTerms, mem_filter, mem_product, mem_range,
        mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨⟨_, _, _⟩, hin, heq⟩, hjk⟩, hk⟩
        have hni : n = i := by omega
        rw [hni, hk, mul_zero, add_zero] at heq
        have him : i = m := by nlinarith
        exact ⟨by omega, him, hk⟩
      · rintro ⟨hn, hi, hk⟩
        rw [hn, hi, hk]
        have hmle : m ≤ m * (m + 1) := Nat.le_mul_of_pos_right m (Nat.succ_pos m)
        refine ⟨⟨⟨⟨by omega, by omega, by omega⟩, le_rfl, by ring⟩, by omega⟩, rfl⟩
    rw [hSzero, Finset.sum_singleton]
    have hf1 : f (m, m, 0) = 1 := by simp [f]
    rw [hf1]
    rcases heven_tail with ⟨r, hr⟩
    exact ⟨r, by omega⟩
