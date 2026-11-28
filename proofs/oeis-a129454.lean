import OMAStatements.S_oeis_a129454

open OMA.S_oeis_a129454

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a129454.main) := by
  intro h
  have htable : table 3 1 = 1 := by
    unfold table
    apply Finset.prod_eq_one
    intro v hv
    unfold tupleGCD
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    simp
  have he := h 2 2 Nat.prime_two
  change (table 3 1).factorization 2 = _ at he
  have hr : (∑ i ∈ Finset.Ico 1 (2+1), (2 / 2^i)^3) = 1 := by decide
  rw [htable, hr, Nat.factorization_one] at he
  simp at he