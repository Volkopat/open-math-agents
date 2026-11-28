import OMAStatements.S_oeis_a056158

/-!
# OEIS A056158: the order-three recurrence of the shifted sequence

Unfolding the first-order recurrence of `fromThree` three times expresses
`fromThree (k + 1)`, `fromThree (k + 2)` and `fromThree (k + 3)` in terms of
`fromThree k`; the claimed combination then vanishes identically.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a056158.main := by
  intro k
  simp only [OMA.S_oeis_a056158.fromThree]
  push_cast
  grind
