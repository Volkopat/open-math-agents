import OMAStatements.S_oeis_a301517

/-! A smaller counterexample to Michel Lagneau's A301517 conjecture.
The earlier disproof in #7662 uses the composite root 3107. Here the root
is 268. The squarefree-divisor product argument follows @anmolspace.
Source: https://oeis.org/A301517
Credit: @dwilfand-sys (smaller witness and proof)
-/

open Finset OMA.S_oeis_a301517 Nat

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a301517.main) := by
  intro h
  let w : ℕ := 19773000
  let l : List ℕ := [2,2,2,3,3,5,5,5,13,13,13]
  have hw : w ≠ 0 := by decide
  have hf : w.primeFactorsList = l := by
    symm
    apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (by decide) (primeFactorsList_sorted w).pairwise
    apply primeFactorsList_unique (by decide)
    norm_num [l, List.forall_mem_cons]
  have hs : squarefreeSum w = 1008 := by
    rw [squarefreeSum, sum_divisors_filter_squarefree hw, factors_eq]
    change ∑ s ∈ w.primeFactors.powerset, s.val.prod = _
    calc
      _ = ∏ p ∈ w.primeFactors, (1+p) := by
        rw [prod_one_add]
        exact sum_congr rfl fun s _ ↦ prod_val s
      _ = _ := by rw [← toFinset_factors, hf]; decide
  have ht : ∑ d ∈ w.divisors, d = 72399600 := by
    rw [sum_divisors hw]
    simp only [← primeFactorsList_count_eq, ← toFinset_factors, hf]
    decide
  have split : squarefreeSum w + nonsquarefreeSum w = ∑ d ∈ w.divisors, d :=
    sum_filter_add_sum_filter_not _ _ _
  apply (show ¬ Nat.Prime 268 by norm_num)
  apply h w 268 (by decide) (by decide)
  have hn : nonsquarefreeSum w = 72398592 := by omega
  rw [hs, hn]
  decide
