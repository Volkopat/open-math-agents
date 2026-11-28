import OMAStatements.S_mo_154707
import Mathlib

-- Problem: mo-154707, a set of reals with the Rothberger property (one set can be picked from
-- each of countably many open covers so that the picks still cover) has strong measure zero.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Given lengths eps_n, let the n-th cover consist of the traces on X of all open intervals
-- shorter than eps_n. Picking one member from each cover so that the picks cover X gives
-- intervals (a_n, b_n) of length less than eps_n whose union contains X.

theorem OMA.solution : type_of% @OMA.S_mo_154707.main := by
  intro X hX ε hε
  have h := hX (fun n => {V : Set X | ∃ a b : ℝ, (a < b ∧ b - a < ε n) ∧
    V = Subtype.val ⁻¹' Set.Ioo a b}) ?_ ?_
  · obtain ⟨V, hV, hcover⟩ := h
    have hV' : ∀ n, ∃ a b : ℝ, (a < b ∧ b - a < ε n) ∧
        V n = Subtype.val ⁻¹' Set.Ioo a b := hV
    choose a b hab hVeq using hV'
    refine ⟨a, b, hab, ?_⟩
    intro x hx
    have hmem : (⟨x, hx⟩ : X) ∈ ⋃ n, V n := by
      rw [hcover]
      exact Set.mem_univ _
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    rw [hVeq n] at hn
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · rintro n V ⟨a, b, _, rfl⟩
    exact isOpen_Ioo.preimage continuous_subtype_val
  · intro n
    apply Set.eq_univ_of_forall
    intro x
    have hpos := hε n
    refine Set.mem_sUnion.mpr ⟨Subtype.val ⁻¹' Set.Ioo (x.val - ε n / 3) (x.val + ε n / 3),
      ⟨_, _, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
    exact ⟨by linarith, by linarith⟩
