import OMAStatements.S_mo_161445
import Mathlib

-- Problem: MO 161445, Hamiltonicity of the Cayley digraphs A'G_n (statement from PR #18481 by @AgentsAlex).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Disproof: the suspicion fails at n = 5. Starting from the identity and multiplying on the right
-- by the generators (0 i 1) with the listed indices i visits all 60 even permutations of Fin 5
-- once and returns to the identity, so A'G_5 has a directed Hamiltonian cycle.

namespace OMA.MO161445Disproof

/-- The indices i of the generators used along the cycle. -/
def gens : List (Fin 5) := [2, 2, 3, 2, 2, 3, 2, 2, 4, 2, 2, 3, 2, 2, 3, 2, 2, 4, 2, 3, 3, 2, 2, 3, 2, 2, 4, 4, 2, 2, 4, 3, 2, 3, 4, 2, 4, 3, 3, 4, 3, 3, 2, 2, 3, 2, 2, 3, 2, 4, 4, 2, 3, 3, 2, 4, 4, 2, 4, 4]

/-- The generator (0 i 1) = swap 0 1 * swap 0 i. -/
def stepPerm (i : Fin 5) : Equiv.Perm (Fin 5) :=
  Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩ * Equiv.swap ⟨0, by decide⟩ i

/-- The k-th vertex of the cycle: the product of the first k generators. -/
def f (k : ZMod 60) : Equiv.Perm (Fin 5) := ((gens.take k.val).map stepPerm).prod

theorem f_inj : Function.Injective f := by decide +kernel

theorem f_step : ∀ k : ZMod 60, ∃ i : Fin 5, 2 ≤ i.val ∧ f (k + 1) = f k * stepPerm i := by
  decide +kernel

theorem sign_step (i : Fin 5) (hi : i ≠ ⟨0, by decide⟩) : Equiv.Perm.sign (stepPerm i) = 1 := by
  rw [stepPerm, map_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (Ne.symm hi)]
  decide

theorem gens_ne : ∀ i ∈ gens, i ≠ ⟨0, by decide⟩ := by decide

theorem f_sign (k : ZMod 60) : Equiv.Perm.sign (f k) = 1 := by
  rw [f, map_list_prod]
  apply List.prod_eq_one
  intro x hx
  rw [List.map_map, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact sign_step i (gens_ne i (List.mem_of_mem_take hi))

end OMA.MO161445Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_161445.main) := by
  intro h
  exact h 5 (by norm_num) ⟨OMA.MO161445Disproof.f, OMA.MO161445Disproof.f_inj,
    OMA.MO161445Disproof.f_sign, OMA.MO161445Disproof.f_step⟩
