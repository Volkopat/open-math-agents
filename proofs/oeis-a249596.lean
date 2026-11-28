import OMAStatements.S_oeis_a249596

/-! The n = 2 counterexample from @Solitude1312 (#26090), checked directly.
The original proof also establishes the corrected-index identity; the registered
target here is the disproof of the same-index formula. -/

open OMA.S_oeis_a249596

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a249596.main) := by
  intro h
  have ha : a249596 2 ≤ 2 :=
    Nat.sInf_le (s := {m : ℕ | 0 < m ∧ m = 2 * rotate m}) (by decide)
  have hp : period 2 = 4 := by
    apply IsLeast.csInf_eq
    refine ⟨by decide, ?_⟩
    intro e he
    by_contra! hlt
    interval_cases e <;> revert he <;> decide
  have hbad := h 2 (by decide)
  norm_num [a165781, hp] at hbad
  omega
