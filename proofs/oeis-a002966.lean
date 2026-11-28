import OMAStatements.S_oeis_a002966
import Mathlib

/-!
# A002966 / A003167: Egyptian fractions for `1/2`

For positive integers `x₁, …, x_m` put `P = ∏ xᵢ`.  Since `∏_{j ≠ i} x_j = P / xᵢ`, we have
`∑ᵢ ∏_{j ≠ i} x_j = P · ∑ᵢ 1 / xᵢ`, so `P = 2 ∑ᵢ ∏_{j ≠ i} x_j` holds exactly when
`∑ᵢ 1 / xᵢ = 1 / 2`.  Hence the two solution sets are literally the same set.
-/

namespace OMA.S_oeis_a002966

/-- Clearing denominators: the unit-fraction equation is the product equation. -/
lemma key {m : ℕ} (x : Fin m → ℕ) (hp : ∀ i, 0 < x i) :
    (∑ i, (1 : ℚ) / (x i : ℚ) = 1 / ((2 : ℕ) : ℚ)) ↔
      ∏ i, x i = 2 * ∑ i, ∏ j ∈ Finset.univ.erase i, x j := by
  have e2 : ((2 : ℕ) : ℚ) = 2 := by norm_num
  rw [e2]
  have hP : (∏ i, (x i : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (hp i).ne'
  -- the sum of the "all but one" products is `P * ∑ 1 / xᵢ`
  have hS : (∑ i, ∏ j ∈ Finset.univ.erase i, (x j : ℚ)) =
      (∏ i, (x i : ℚ)) * ∑ i, (1 : ℚ) / (x i : ℚ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hx : (x i : ℚ) ≠ 0 := by exact_mod_cast (hp i).ne'
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (x j : ℚ)) (Finset.mem_univ i)]
    field_simp
  -- move the natural-number equation to `ℚ`
  have hcast : (∏ i, x i = 2 * ∑ i, ∏ j ∈ Finset.univ.erase i, x j) ↔
      (∏ i, (x i : ℚ)) = 2 * ∑ i, ∏ j ∈ Finset.univ.erase i, (x j : ℚ) := by
    rw [← Nat.cast_inj (R := ℚ)]
    push_cast
    rfl
  rw [hcast, hS]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    have h0 : (∏ i, (x i : ℚ)) * (2 * ∑ i, (1 : ℚ) / (x i : ℚ) - 1) = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hP
    · linarith

end OMA.S_oeis_a002966

open OMA.S_oeis_a002966 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002966.main := by
  intro m _
  unfold T A003167
  refine congrArg Set.ncard (Set.ext fun x => ?_)
  constructor
  · rintro ⟨hm, hp, hs⟩
    exact ⟨hm, hp, (key x hp).mp hs⟩
  · rintro ⟨hm, hp, hs⟩
    exact ⟨hm, hp, (key x hp).mpr hs⟩
