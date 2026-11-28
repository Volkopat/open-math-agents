import OMAStatements.S_oeis_a203751

-- Problem: A203751: Square root of v(2*n+1)/(3*v(2*n)), where v = A203748.
-- Upstream: formal-conjectures statements/oeis-a203751.lean:0 (declaration OMA.S_oeis_a203751.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: v(2n+1) = v(2n) * u, where u = Product_{j=1..2n} G(floor(j/2)) with
-- G(i) = i^2 + i n + n^2, because floor((2n+1)/2) = n. The values floor(j/2), j = 1..2n, are
-- 0, 1, 1, 2, 2, ..., n-1, n-1, n, so u = G(0) G(n) P^2 = 3 (n^2 P)^2 with
-- P = Product_{k=1..n-1} G(k), and a(n) = n^2 P. On the other side
-- n^3 - k^3 = (n - k) G(k) and Product_{k=1..n-1} (n - k) = (n-1)!, so the conjectured
-- formula is also n^2 P.

namespace R08A203751

open OMA.S_oeis_a203751

theorem pair_prod (G : ℕ → ℕ) (m : ℕ) :
    ∏ j ∈ Finset.Icc 1 (2 * m), G (j / 2) =
      (∏ i ∈ Finset.range m, G i) * ∏ i ∈ Finset.range m, G (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
      Finset.prod_Icc_succ_top (show 1 ≤ 2 * m + 1 + 1 by omega),
      Finset.prod_Icc_succ_top (show 1 ≤ 2 * m + 1 by omega), ih,
      Finset.prod_range_succ, Finset.prod_range_succ,
      show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega]
    ring

theorem v_succ (N : ℕ) (h : 1 ≤ N) : v (N + 1) = v N *
    ∏ j ∈ Finset.Icc 1 N, ((j / 2) ^ 2 + (j / 2) * ((N + 1) / 2) + ((N + 1) / 2) ^ 2) := by
  simp only [v]
  rw [Finset.prod_Icc_succ_top (show 2 ≤ N + 1 by omega), show N + 1 - 1 = N by omega]

theorem v_pos (N : ℕ) : 0 < v N := by
  simp only [v]
  apply Finset.prod_pos
  intro k hk
  apply Finset.prod_pos
  intro j _
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have h1 : 0 < k / 2 := by omega
  have h3 : 0 < (k / 2) ^ 2 := pow_pos h1 2
  exact lt_of_lt_of_le h3 (Nat.le_add_left _ _)

theorem u_eq (m : ℕ) :
    v (2 * (m + 1) + 1) = v (2 * (m + 1)) * (3 * ((m + 1) ^ 2 *
      ∏ i ∈ Finset.range m, ((i + 1) ^ 2 + (i + 1) * (m + 1) + (m + 1) ^ 2)) ^ 2) := by
  have hp : ∏ j ∈ Finset.Icc 1 (2 * (m + 1)), ((j / 2) ^ 2 + (j / 2) * (m + 1) + (m + 1) ^ 2) =
      (∏ i ∈ Finset.range (m + 1), (i ^ 2 + i * (m + 1) + (m + 1) ^ 2)) *
        ∏ i ∈ Finset.range (m + 1), ((i + 1) ^ 2 + (i + 1) * (m + 1) + (m + 1) ^ 2) :=
    pair_prod (fun i => i ^ 2 + i * (m + 1) + (m + 1) ^ 2) (m + 1)
  rw [Finset.prod_range_succ', Finset.prod_range_succ] at hp
  rw [v_succ (2 * (m + 1)) (by omega), show (2 * (m + 1) + 1) / 2 = m + 1 by omega, hp]
  ring

theorem sqrt_step (V X : ℕ) (hV : 0 < V) :
    Real.sqrt (((V * (3 * X ^ 2) : ℕ) : ℝ) / (3 * (V : ℝ))) = (X : ℝ) := by
  have hV' : (V : ℝ) ≠ 0 := by exact_mod_cast hV.ne'
  have h0 : 3 * (V : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hV'
  have e : ((V * (3 * X ^ 2) : ℕ) : ℝ) / (3 * (V : ℝ)) = (X : ℝ) ^ 2 := by
    rw [div_eq_iff h0]
    push_cast
    ring
  rw [e, Real.sqrt_sq (Nat.cast_nonneg X)]

theorem a_eq (m : ℕ) : a (m + 1) = (((m + 1) ^ 2 *
    ∏ i ∈ Finset.range m, ((i + 1) ^ 2 + (i + 1) * (m + 1) + (m + 1) ^ 2) : ℕ) : ℝ) := by
  rw [a, u_eq m]
  exact sqrt_step _ _ (v_pos _)

theorem Icc_range (f : ℕ → ℝ) (m : ℕ) :
    ∏ k ∈ Finset.Icc 1 m, f k = ∏ i ∈ Finset.range m, f (i + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (show 1 ≤ m + 1 by omega), ih, Finset.prod_range_succ]

theorem rhs_eq (m : ℕ) : ((m + 1 : ℕ) : ℝ) ^ 2 / (m.factorial : ℝ) *
      ∏ k ∈ Finset.Icc 1 m, (((m + 1 : ℕ) : ℝ) ^ 3 - (k : ℝ) ^ 3) =
    (((m + 1) ^ 2 *
      ∏ i ∈ Finset.range m, ((i + 1) ^ 2 + (i + 1) * (m + 1) + (m + 1) ^ 2) : ℕ) : ℝ) := by
  have hfac : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hd : ∏ i ∈ Finset.range m, ((m - i : ℕ) : ℝ) = (m.factorial : ℝ) := by
    rw [← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have hprod : ∏ k ∈ Finset.Icc 1 m, (((m + 1 : ℕ) : ℝ) ^ 3 - (k : ℝ) ^ 3) =
      (m.factorial : ℝ) *
        ∏ i ∈ Finset.range m, (((i + 1) ^ 2 + (i + 1) * (m + 1) + (m + 1) ^ 2 : ℕ) : ℝ) := by
    rw [Icc_range, ← hd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' : i < m := Finset.mem_range.mp hi
    rw [Nat.cast_sub hi'.le]
    push_cast
    ring
  rw [hprod, div_mul_eq_mul_div, div_eq_iff hfac]
  push_cast
  ring

end R08A203751

open OMA.S_oeis_a203751 R08A203751 in
theorem OMA.solution : type_of% @OMA.S_oeis_a203751.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, a_eq m, rhs_eq m]
