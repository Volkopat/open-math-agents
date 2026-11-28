import OMAStatements.S_oeis_a062282
import Mathlib

/-!
Split the permutations with an even number of fixed points according to that number
`k ∈ [0, n]`: the fiber over `k` is the set counted by `A008290(n, k)` when `k` is even,
and is empty when `k` is odd, which is what the factor `A059841(k)` records.
-/

namespace R062282
open OMA.S_oeis_a062282

theorem fixedPts_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : fixedPts σ ≤ n := by
  unfold fixedPts
  calc (Finset.univ.filter fun i => σ i = i).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_filter_le _ _
    _ = n := by simp

theorem fiber (n k : ℕ) :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => Even (fixedPts σ)).filter
      fun σ => fixedPts σ = k).card = T n k * chiEven k := by
  rw [Finset.filter_filter]
  unfold T chiEven
  rcases Nat.even_or_odd k with hk | hk
  · have h0 : k % 2 = 0 := Nat.even_iff.mp hk
    rw [h0, Nat.sub_zero, Nat.mul_one]
    congr 1
    apply Finset.filter_congr
    intro σ _
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨h ▸ hk, h⟩
  · have h1 : k % 2 = 1 := Nat.odd_iff.mp hk
    rw [h1, Nat.sub_self, Nat.mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ h
    rw [h.2] at h
    exact (Nat.not_even_iff_odd.mpr hk) h.1

end R062282

open OMA.S_oeis_a062282 R062282 in
theorem OMA.solution : type_of% @OMA.S_oeis_a062282.main := by
  intro n
  unfold a
  rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Equiv.Perm (Fin n) => fixedPts σ)
    (t := Finset.range (n + 1))]
  · apply Finset.sum_congr rfl
    intro k _
    exact fiber n k
  · intro σ _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (fixedPts_le σ)
