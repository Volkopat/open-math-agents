import OMAStatements.S_oeis_a350532

-- Problem: A350532: Triangle read by rows: T(n,k) is the number of degree-n polynomials over Z/2Z of the form f(x)^m for some m > 1 with exactly k nonzero terms; 1 <= k <= n + 1.
-- Upstream: formal-conjectures statements/oeis-a350532.lean:0 (declaration OMA.S_oeis_a350532.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 15 is a counterexample to the first conjecture. The only degree-15 polynomial over
-- Z/2Z with 16 nonzero terms is S = 1 + x + ... + x^15, and S = ((x + 1)^5)^3, because
-- S * (x + 1) = x^16 + 1 = (x + 1)^16 in characteristic 2. So T(15,16) = 1, but 15 is not prime.

open OMA.S_oeis_a350532 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a350532.main) := by
  intro H
  have z2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  obtain ⟨S, hSdef⟩ : ∃ S : Polynomial (ZMod 2),
      S = ∑ i ∈ Finset.range 16, (Polynomial.X : Polynomial (ZMod 2)) ^ i := ⟨_, rfl⟩
  have hc : ∀ j : ℕ, S.coeff j = if j < 16 then 1 else 0 := by
    intro j
    rw [hSdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  have hsupp : S.support = Finset.range 16 := by
    ext j
    rw [Polynomial.mem_support_iff, hc, Finset.mem_range]
    by_cases hj : j < 16
    · rw [if_pos hj]
      exact ⟨fun _ => hj, fun _ => one_ne_zero⟩
    · rw [if_neg hj]
      exact ⟨fun h => absurd rfl h, fun h => absurd h hj⟩
  have hdeg : S.natDegree = 15 := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hc, if_neg (show ¬ (N < 16) by omega)]
    · rw [hc, if_pos (show (15 : ℕ) < 16 by norm_num)]
      exact one_ne_zero
  have hS0 : S ≠ 0 := by
    intro h0
    have h1 := hc 0
    rw [h0, Polynomial.coeff_zero, if_pos (show (0 : ℕ) < 16 by norm_num)] at h1
    exact zero_ne_one h1
  have hX1 : (Polynomial.X + 1 : Polynomial (ZMod 2)) ≠ 0 := by
    intro h
    have h1 := congrArg (fun q : Polynomial (ZMod 2) => q.coeff 0) h
    simp at h1
  have h2 : ∀ q : Polynomial (ZMod 2), (q + 1) ^ 2 = q ^ 2 + 1 := by
    intro q
    rw [CharTwo.add_sq, one_pow]
  have h16 : (Polynomial.X + 1 : Polynomial (ZMod 2)) ^ 16 = Polynomial.X ^ 16 + 1 := by
    calc (Polynomial.X + 1 : Polynomial (ZMod 2)) ^ 16
        = ((((Polynomial.X + 1) ^ 2) ^ 2) ^ 2) ^ 2 := by ring
      _ = Polynomial.X ^ 16 + 1 := by
        rw [h2, h2, h2, h2]
        ring
  have hgeom : S * (Polynomial.X + 1) = Polynomial.X ^ 16 + 1 := by
    have h3 := geom_sum_mul (Polynomial.X : Polynomial (ZMod 2)) 16
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at h3
    rw [hSdef]
    exact h3
  have h15 : S = (Polynomial.X + 1) ^ 15 := by
    apply mul_right_cancel₀ hX1
    rw [hgeom, ← h16]
    ring
  have hpow : S = ((Polynomial.X + 1) ^ 5) ^ 3 := by
    rw [h15]
    ring
  have hT : T 15 16 = 1 := by
    unfold T
    rw [Set.ncard_eq_one]
    refine ⟨S, ?_⟩
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, hpd, hpc, _⟩
      have hsub : p.support ⊆ Finset.range 16 := by
        have h4 := Polynomial.supp_subset_range_natDegree_succ (p := p)
        rw [hpd] at h4
        exact h4
      have hps : p.support = Finset.range 16 :=
        Finset.eq_of_subset_of_card_le hsub (by simp [hpc])
      ext j
      rw [hc]
      by_cases hj : j < 16
      · rw [if_pos hj]
        have hm : j ∈ p.support := by
          rw [hps]
          exact Finset.mem_range.mpr hj
        exact z2 _ (Polynomial.mem_support_iff.mp hm)
      · rw [if_neg hj]
        have hm : j ∉ p.support := by
          rw [hps, Finset.mem_range]
          exact hj
        exact Polynomial.notMem_support_iff.mp hm
    · rintro rfl
      refine ⟨hS0, hdeg, ?_, (Polynomial.X + 1) ^ 5, 3, by norm_num, hpow⟩
      rw [hsupp, Finset.card_range]
  have h15m := (H.1 15).mp hT
  obtain ⟨hp, _⟩ := h15m
  exact absurd hp (by norm_num)
