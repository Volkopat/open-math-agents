import OMAStatements.S_mo_282089

open Finset Polynomial OMA.S_mo_282089

namespace ZeroSignSums

theorem coefficient (n k : ℕ) :
    (generating n).coeff k = ((range n).powerset.filter fun s => weight s = k).card := by
  rw [generating, prod_one_add, finsetSum_coeff]
  simp only [Finset.prod_pow_eq_pow_sum, Polynomial.coeff_X_pow]
  simp [weight, eq_comm]

theorem total (n : ℕ) : weight (range n) = n * (n + 1) / 2 := by
  have h := sum_range_id (n + 1)
  rw [Finset.sum_range_succ' ] at h
  simpa [weight, Nat.mul_comm] using h

theorem count (n : ℕ) :
    ways n = if n * (n + 1) / 2 % 2 = 0
             then (generating n).coeff (n * (n + 1) / 4) else 0 := by
  have splitSum (s : Finset ℕ) (hs : s ∈ (range n).powerset) :
      weight (range n \ s) + weight s = n * (n + 1) / 2 := by
    rw [← total]
    exact sum_sdiff (f := fun i => i + 1) (mem_powerset.mp hs)
  unfold ways
  split
  · rename_i heven
    rw [coefficient]
    apply congrArg Finset.card
    apply filter_congr
    intro s hs
    have := splitSum s hs
    omega
  · rename_i hodd
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s hs
    have := splitSum s hs
    omega

end ZeroSignSums

theorem OMA.solution : type_of% @OMA.S_mo_282089.main := ZeroSignSums.count
