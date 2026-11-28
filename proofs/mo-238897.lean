import OMAStatements.S_mo_238897
import Mathlib

-- Problem: mo-238897, for every N and every real k > 0, is there a matrix representation of
-- S_N whose trace at g is k^(number of cycles of g)?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. The trace of the identity is the dimension d, a natural number, while the Markov trace of
-- the identity is k^N. For N = 1 and k = 1/2 this would give d = 1/2.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_238897.main) := by
  intro h
  obtain ⟨d, D, hD⟩ := h 1 (1 / 2) (by norm_num)
  have h1 := hD 1
  have hc : OMA.S_mo_238897.numCycles (1 : Equiv.Perm (Fin 1)) = 1 := by
    simp [OMA.S_mo_238897.numCycles, Equiv.Perm.parts_partition]
  have h2 : Matrix.trace ((1 : Matrix.GeneralLinearGroup (Fin d) ℂ) :
      Matrix (Fin d) (Fin d) ℂ) = (d : ℂ) := by
    simp
  rw [hc, map_one, h2] at h1
  have h3 : ((2 * d : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
    push_cast
    rw [h1]
    norm_num
  have h4 : 2 * d = 1 := by exact_mod_cast h3
  omega
