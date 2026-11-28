import OMAStatements.S_oeis_a394578

-- Problem: A394578: a(n) = 2^(2*n-1) * p(n, n+1/2), where p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1.
-- Upstream: formal-conjectures statements/oeis-a394578.lean:0 (declaration OMA.S_oeis_a394578.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Disproof idea: p(n, n+1/2) = 1 - c(n) with c(n) = prod_{i<n} (1/2-i)/(i+1) (Lagrange basis at the node 1, reindexed and reflected), |c(n)| <= 1/2 for n >= 1, so 4^n/4 <= a(n) <= 3*4^n/4 and a(n+1)/a(n) >= 4/3 for n >= 1, which contradicts the limit 1/4.

open OMA.S_oeis_a394578 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a394578.main) := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ n : ℕ,
      c n = ∏ i ∈ Finset.range n, ((1 / 2 - (i : ℝ)) / ((i : ℝ) + 1)) := ⟨_, fun _ => rfl⟩
  have hinj : ∀ n : ℕ,
      Set.InjOn (fun i : ℕ => (i : ℝ) + 1) (Finset.range (n + 1) : Set ℕ) := by
    intro n x _ y _ hxy
    simpa using hxy
  have hsplit : ∀ (n : ℕ) (e : ℕ → ℝ),
      ∑ i ∈ Finset.range (n + 1), (if i = 0 then (0 : ℝ) else 1) * e i
        = ∑ i ∈ Finset.range n, e (i + 1) := by
    intro n e
    rw [Finset.sum_range_succ', if_pos (rfl : (0 : ℕ) = 0), zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [if_neg (show ¬(i + 1 = 0) by omega), one_mul]
  have heval : ∀ n : ℕ, (p n).eval ((n : ℝ) + 1 / 2)
      = 1 - (Lagrange.basis (Finset.range (n + 1)) (fun i : ℕ => (i : ℝ) + 1) 0).eval
          ((n : ℝ) + 1 / 2) := by
    intro n
    have hb := congrArg (Polynomial.eval ((n : ℝ) + 1 / 2))
      (Lagrange.sum_basis (hinj n) ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩)
    rw [Polynomial.eval_finsetSum, Polynomial.eval_one, Finset.sum_range_succ'] at hb
    unfold p
    rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [hsplit]
    linarith
  have hbasis : ∀ n : ℕ,
      (Lagrange.basis (Finset.range (n + 1)) (fun i : ℕ => (i : ℝ) + 1) 0).eval ((n : ℝ) + 1 / 2)
        = ∏ i ∈ Finset.range n, (((i : ℝ) + 3 / 2 - (n : ℝ)) / ((i : ℝ) + 1)) := by
    intro n
    rw [Lagrange.basis, Polynomial.eval_prod]
    refine Finset.prod_nbij' (fun j => j - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      have hj0 := Finset.ne_of_mem_erase hj
      have hj1 := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
      show j - 1 ∈ Finset.range n
      exact Finset.mem_range.mpr (by omega)
    · intro i hi
      have hi1 := Finset.mem_range.mp hi
      show i + 1 ∈ (Finset.range (n + 1)).erase 0
      exact Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
    · intro j hj
      have hj0 := Finset.ne_of_mem_erase hj
      show j - 1 + 1 = j
      omega
    · intro i _
      show i + 1 - 1 = i
      omega
    · intro j hj
      have hj0 := Finset.ne_of_mem_erase hj
      simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_sub, Polynomial.eval_X]
      rw [Nat.cast_sub (show 1 ≤ j by omega)]
      push_cast
      ring
  have hrefl : ∀ n : ℕ,
      ∏ i ∈ Finset.range n, (((i : ℝ) + 3 / 2 - (n : ℝ)) / ((i : ℝ) + 1)) = c n := by
    intro n
    rw [hc, Finset.prod_div_distrib, Finset.prod_div_distrib]
    congr 1
    refine Eq.trans ?_ (Finset.prod_range_reflect (fun i : ℕ => (1 / 2 - (i : ℝ))) n)
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    show (i : ℝ) + 3 / 2 - (n : ℝ) = 1 / 2 - ((n - 1 - i : ℕ) : ℝ)
    rw [Nat.cast_sub (by omega : i ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  have h2pow : ∀ n : ℕ, (2 : ℝ) ^ (2 * (n : ℤ) - 1) = 4 ^ n / 2 := by
    intro n
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_mul, zpow_natCast, zpow_one, zpow_two]
    norm_num
  have hclosed : ∀ n : ℕ, a n = 4 ^ n / 2 * (1 - c n) := by
    intro n
    unfold a
    rw [heval n, hbasis n, hrefl n, h2pow n]
  have hcbound : ∀ n : ℕ, 1 ≤ n → |c n| ≤ 1 / 2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      rw [hc, Finset.prod_range_one, Nat.cast_zero, abs_le]
      constructor <;> norm_num
    | succ k _ ih =>
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hf : |(1 / 2 - (k : ℝ)) / ((k : ℝ) + 1)| ≤ 1 := by
        rw [abs_le]
        constructor
        · rw [le_div_iff₀ hk1]
          linarith
        · rw [div_le_iff₀ hk1]
          linarith
      rw [hc, Finset.prod_range_succ, ← hc, abs_mul]
      calc |c k| * |(1 / 2 - (k : ℝ)) / ((k : ℝ) + 1)| ≤ 1 / 2 * 1 :=
            mul_le_mul ih hf (abs_nonneg _) (by norm_num)
        _ = 1 / 2 := by norm_num
  have hbounds : ∀ n : ℕ, 1 ≤ n → 4 ^ n / 4 ≤ a n ∧ a n ≤ 3 * 4 ^ n / 4 := by
    intro n hn
    obtain ⟨hl, hu⟩ := abs_le.mp (hcbound n hn)
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    rw [hclosed n]
    constructor
    · nlinarith
    · nlinarith
  rintro ⟨hT, -⟩
  have ev := hT.eventually (gt_mem_nhds (show (1 / 4 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ev
  have hlt : a (N + 1 + 1) / a (N + 1) < 1 / 2 := hN (N + 1) (by omega)
  obtain ⟨l1, u1⟩ := hbounds (N + 1) (by omega)
  obtain ⟨l2, -⟩ := hbounds (N + 1 + 1) (by omega)
  have h4 : (0 : ℝ) < 4 ^ (N + 1) := by positivity
  have hpos : 0 < a (N + 1) := by linarith
  rw [div_lt_iff₀ hpos] at hlt
  rw [pow_succ (4 : ℝ) (N + 1)] at l2
  linarith
