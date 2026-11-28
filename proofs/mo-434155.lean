import OMAStatements.S_mo_434155
import Mathlib

theorem OMA.solution : type_of% @OMA.S_mo_434155.main := by
  intro n lam hl
  have e : {mu : Fin n → ℕ // ∀ i, lam i.succ ≤ mu i ∧ mu i ≤ lam i.castSucc} ≃
      (Fintype.piFinset fun i : Fin n => Finset.Icc (lam i.succ) (lam i.castSucc)) :=
    Equiv.subtypeEquivRight (fun mu => by simp [Fintype.mem_piFinset, Finset.mem_Icc])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _
  rw [Nat.card_Icc]
  have := hl (Fin.castSucc_lt_succ (i := i)).le
  omega
