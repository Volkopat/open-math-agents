import OMAStatements.S_mo_240260
import Mathlib

-- Builds on @ivillar’s main proof and @caa1982’s pending #25540.
-- Coloring directly by integer units uses the standard finite-color cardinality API.

open OMA.S_mo_240260

lemma mo240260_sign {n : ℕ} {σ τ : Equiv.Perm (Fin n)}
    (h : ∃ a b : Fin n, b.val = a.val + 1 ∧ τ = Equiv.swap a b * σ) :
    Equiv.Perm.sign τ = - Equiv.Perm.sign σ := by
  obtain ⟨a, b, hab, rfl⟩ := h
  have hne : a ≠ b := by intro h; rw [h] at hab; omega
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]; simp

theorem OMA.solution : type_of% @OMA.S_mo_240260.main := by
  intro n hn
  apply le_antisymm
  · let C : (permutahedronGraph n).Coloring ℤˣ := SimpleGraph.Coloring.mk Equiv.Perm.sign (by
      intro σ τ hadj he
      simp only [permutahedronGraph, SimpleGraph.fromRel_adj] at hadj
      obtain ⟨_, h | h⟩ := hadj
      all_goals
        have hc := congrArg Units.val (mo240260_sign h)
        have he' := congrArg Units.val he
        have hn := (Equiv.Perm.sign σ).ne_zero
        simp only [Units.val_neg] at hc
        omega)
    simpa using C.colorable.chromaticNumber_le
  · let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    have hadj : (permutahedronGraph n).Adj 1 (Equiv.swap a b * 1) := by
      simp only [permutahedronGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨a, b, rfl, rfl⟩⟩
      intro h
      have h2 := congrArg (fun p : Equiv.Perm (Fin n) => p a) h
      simp [Equiv.swap_apply_left] at h2
      exact absurd (congrArg Fin.val h2) (by simp [a, b])
    exact SimpleGraph.two_le_chromaticNumber_of_adj hadj

