import OMAStatements.S_oeis_a072124

/-! Separate the finite factorial computation from the assertion about all later factorials. -/

namespace OMA.R_oeis_a072124_R1

/-- The observed prefix attains 9255 distinct counts at most 10000, including zero. -/
def H1 : Prop :=
  ((Finset.range 10001) ∩ ((Finset.range 27337).image fun k =>
    (Nat.digits 10 (Nat.factorial k)).count 1)).card = 9255

/-- A later factorial with at most 10000 ones repeats an already observed count. -/
def H2 : Prop :=
  ∀ k : ℕ, 27336 < k → (Nat.digits 10 (Nat.factorial k)).count 1 ≤ 10000 →
    ∃ j : ℕ, j ≤ 27336 ∧
      (Nat.digits 10 (Nat.factorial j)).count 1 = (Nat.digits 10 (Nat.factorial k)).count 1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a072124.main := by
  intro hcard tail
  let f := fun k : ℕ => (Nat.digits 10 (Nat.factorial k)).count 1
  let u := Finset.range 10001
  let seen := u ∩ (Finset.range 27337).image f
  have he : {n : ℕ | n ≤ 10000 ∧ ∀ k, f k ≠ n} = (↑(u \ seen) : Set ℕ) := by
    ext n
    change (n ≤ 10000 ∧ ∀ k, f k ≠ n) ↔ n ∈ u \ seen
    rw [Finset.mem_sdiff]
    constructor
    · rintro ⟨hn,hm⟩
      refine ⟨Finset.mem_range.mpr (by omega),?_⟩
      intro hs
      obtain ⟨k,_,hk⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hs).2
      exact hm k hk
    · rintro ⟨hu,hs⟩
      have hn : n < 10001 := Finset.mem_range.mp hu
      refine ⟨by omega,?_⟩
      intro k hk
      apply hs
      apply Finset.mem_inter.mpr
      refine ⟨hu,Finset.mem_image.mpr ?_⟩
      by_cases h : k ≤ 27336
      · exact ⟨k,Finset.mem_range.mpr (by omega),hk⟩
      · obtain ⟨j,hj,heq⟩ := tail k (by omega) (show f k ≤ 10000 by omega)
        exact ⟨j,Finset.mem_range.mpr (by omega),heq.trans hk⟩
  change Set.ncard {n : ℕ | n ≤ 10000 ∧ ∀ k, f k ≠ n} = 746
  rw [he,Set.ncard_coe_finset,Finset.card_sdiff_of_subset (Finset.inter_subset_left)]
  change seen.card = 9255 at hcard
  rw [hcard]
  simp [u]

end OMA.R_oeis_a072124_R1
