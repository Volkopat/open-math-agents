import OMAStatements.S_mo_316142

open scoped BigOperators

namespace OMA.RestrictedWeightedSum

private def A : Finset (ZMod 5) := {0, 1, 2}

private def sums : Set (ZMod 5) :=
  {s | ∃ a : Fin 2 → ZMod 5, Function.Injective a ∧ (∀ k, a k ∈ A) ∧
    s = ∑ k : Fin 2, ((k : ℕ) + 1 : ZMod 5) * a k}

private theorem omitted : (3 : ZMod 5) ∉ sums := by
  rintro ⟨a, ha, hm, hs⟩
  have finite_check : ∀ x y : ZMod 5, x ∈ A → y ∈ A → x ≠ y → x + 2 * y ≠ 3 := by
    decide
  have hne : a 0 ≠ a 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (ha h)
  apply finite_check (a 0) (a 1) (hm 0) (hm 1) hne
  simpa [Fin.sum_univ_two, one_add_one_eq_two] using hs.symm

theorem result : ¬ (type_of% @OMA.S_mo_316142.main) := by
  intro h
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hchar : ringChar (ZMod 5) = 5 := ZMod.ringChar_zmod_n 5
  have cardA : A.card = 3 := by decide
  have lower := h 2 (by decide) (ZMod 5) (Or.inr (by rw [hchar]; decide)) A (by decide)
  change (if ringChar (ZMod 5) = 0 then (A.card - 2) * (2 * (2 + 1) / 2) +
      2 * (2 ^ 2 - 1) / 6 + 1 else min (ringChar (ZMod 5))
      ((A.card - 2) * (2 * (2 + 1) / 2) + 2 * (2 ^ 2 - 1) / 6 + 1)) ≤ sums.ncard at lower
  norm_num [hchar, cardA] at lower
  have upper := Set.ncard_lt_card (s := sums) (by
    intro hfull
    exact omitted (hfull.symm ▸ Set.mem_univ (3 : ZMod 5)))
  rw [Nat.card_zmod] at upper
  exact (not_lt_of_ge lower) upper

end OMA.RestrictedWeightedSum

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_316142.main) := OMA.RestrictedWeightedSum.result