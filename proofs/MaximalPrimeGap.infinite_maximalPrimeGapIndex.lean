import FormalConjectures.Wikipedia.MaximalPrimeGap

/-!
# Shorter proof of `MaximalPrimeGap.infinite_maximalPrimeGapIndex`
-/

open MaximalPrimeGap Nat

theorem OMA.solution : type_of% @MaximalPrimeGap.infinite_maximalPrimeGapIndex := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  set M := (Finset.range (N + 1)).sup primeGap
  have hex : ∃ n, M < primeGap n := by
    set x := (M + 1)! + 1
    set c := count Nat.Prime (x + 1)
    have hc0 : 0 < c := lt_of_lt_of_le (by decide : 0 < count Nat.Prime 3)
      (count_monotone _ (by have := factorial_pos (M + 1); omega))
    refine ⟨c - 1, ?_⟩
    have hlow : nth Nat.Prime (c - 1) < x + 1 := nth_lt_of_lt_count (by omega)
    have hhigh : x + 1 ≤ nth Nat.Prime c := le_nth_count infinite_setOfPred_prime _
    have hp : (nth Nat.Prime c).Prime := prime_nth_prime c
    have hfar : x + M < nth Nat.Prime c := by
      by_contra h
      set j := nth Nat.Prime c - (M + 1)!
      have hd : j ∣ nth Nat.Prime c := by
        rw [show nth Nat.Prime c = (M + 1)! + j by omega]
        exact (dvd_factorial (by omega) (by omega)).add dvd_rfl
      rcases hp.eq_one_or_self_of_dvd j hd with h1 | h2 <;>
        (have := factorial_pos (M + 1); omega)
    rw [primeGap, show c - 1 + 1 = c by omega]; omega
  refine ⟨Nat.find hex, fun m hm => (not_lt.1 (Nat.find_min hex hm)).trans_lt (Nat.find_spec hex), ?_⟩
  by_contra! hle
  exact not_lt.2 (Finset.le_sup (f := primeGap) (Finset.mem_range.2 (by omega))) (Nat.find_spec hex)
