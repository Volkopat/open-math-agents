import OMAStatements.S_oeis_a138808

-- Problem: A138808: Number of integer pairs (x,y), x > 0, y > 0, such that x <= p, y <= q for any factorization n = p*q.
-- Upstream: formal-conjectures statements/oeis-a138808.lean:0 (declaration OMA.S_oeis_a138808.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: if x <= p and y <= n/p for a divisor p of n, then x*y <= p*(n/p) = n. So the set
-- counted by a(n) lies inside the set of pairs (x, y) in [1, n]^2 with x*y <= n, and for each
-- x in [1, n] the y with x*y <= n are exactly 1, ..., floor(n/x); that set has
-- Sum_{x=1..n} floor(n/x) elements.

open OMA.S_oeis_a138808 in
theorem OMA.solution : type_of% @OMA.S_oeis_a138808.main := by
  intro n hn
  have hsub : (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
      (fun xy : ℕ × ℕ => ∃ p ∈ Nat.divisors n, xy.1 ≤ p ∧ xy.2 ≤ n / p) ⊆
      (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun xy : ℕ × ℕ => xy.1 * xy.2 ≤ n) := by
    intro xy hxy
    rw [Finset.mem_filter] at hxy ⊢
    obtain ⟨hmem, p, hp, h1, h2⟩ := hxy
    refine ⟨hmem, ?_⟩
    have hpn : p * (n / p) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hp)
    calc xy.1 * xy.2 ≤ p * (n / p) := Nat.mul_le_mul h1 h2
      _ = n := hpn
  have hfib : ∀ k ∈ Finset.Icc 1 n,
      (∑ y ∈ Finset.Icc 1 n, if k * y ≤ n then 1 else 0) = n / k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 : 0 < k := by omega
    rw [← Finset.card_filter]
    have hset : (Finset.Icc 1 n).filter (fun y => k * y ≤ n) = Finset.Icc 1 (n / k) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hy1, _⟩, hy⟩
        refine ⟨hy1, (Nat.le_div_iff_mul_le hk0).mpr ?_⟩
        rw [mul_comm]
        exact hy
      · rintro ⟨hy1, hy⟩
        have h3 : y * k ≤ n := (Nat.le_div_iff_mul_le hk0).mp hy
        have h4 : y ≤ y * k := Nat.le_mul_of_pos_right y hk0
        refine ⟨⟨hy1, by omega⟩, ?_⟩
        rw [mul_comm]
        exact h3
    rw [hset, Nat.card_Icc, Nat.add_sub_cancel]
  have hcount : ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
      (fun xy : ℕ × ℕ => xy.1 * xy.2 ≤ n)).card = ∑ k ∈ Finset.Icc 1 n, n / k := by
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl hfib
  unfold a
  exact (Finset.card_le_card hsub).trans hcount.le
