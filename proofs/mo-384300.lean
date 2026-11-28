import OMAStatements.S_mo_384300
import Mathlib

-- Retains @caa1982’s fourteen-vector counterexample from PR #26785.
-- A basis determinant is a unit; its reduction modulo two remains a unit.

open OMA.S_mo_384300

/-- Two distinct vectors of a basis of `ℤ^m` are distinct and nonzero modulo `2`. -/
lemma basis_mod_two {m : ℕ} (b : Module.Basis (Fin m) ℤ (Fin m → ℤ)) :
    (∀ j, ¬ ∀ r, ((b j r : ℤ) : ZMod 2) = 0) ∧
      ∀ j₁ j₂, j₁ ≠ j₂ → ¬ ∀ r, ((b j₁ r : ℤ) : ZMod 2) = ((b j₂ r : ℤ) : ZMod 2) := by
  set e := Pi.basisFun ℤ (Fin m)
  set M := e.toMatrix b with hM
  have hMij : ∀ i j, M i j = b j i := by
    intro i j; rw [hM, Module.Basis.toMatrix_apply]; simp [e]
  set N := (Int.castRingHom (ZMod 2)).mapMatrix M with hN
  have hNdet : N.det ≠ 0 := by
    rw [hN, ← RingHom.map_det]
    simpa only [Module.Basis.det_apply] using
      ((e.isUnit_det b).map (Int.castRingHom (ZMod 2))).ne_zero
  have hNij : ∀ i j, N i j = ((b j i : ℤ) : ZMod 2) := by
    intro i j; simp [hN, hMij]
  refine ⟨fun j hj => hNdet (Matrix.det_eq_zero_of_column_eq_zero j fun i => ?_),
    fun j₁ j₂ hne hj => hNdet (Matrix.det_zero_of_column_eq hne fun k => ?_)⟩
  · rw [hNij]; exact hj i
  · rw [hNij, hNij]; exact hj k

/-- The fourteen vectors: every nonzero class of `(ℤ/2)^3` is hit twice. -/
def vs : Fin 14 → Fin 3 → ℤ :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1],
    ![1, 2, 0], ![0, 1, 2], ![2, 0, 1], ![1, 1, 2], ![1, 2, 1], ![2, 1, 1], ![1, 1, 3]]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_384300.main) := by
  intro h
  have hone : ∀ i : Fin 14, ∃ j, vs i j = 1 := by decide
  have hprim : ∀ i, IsPrimitive (vs i) := by
    intro i d hd
    obtain ⟨j, hj⟩ := hone i
    have := hd j
    rw [hj] at this
    exact isUnit_of_dvd_one this
  obtain ⟨w, hw⟩ := h 2 14 vs hprim
  have hnz : ∀ i, ¬ ∀ r, ((vs i r : ℤ) : ZMod 2) = 0 := by decide
  have hcov : ∀ x : Fin 3 → ZMod 2, (¬ ∀ r, x r = 0) → ∃ i i' : Fin 14, vs i ≠ vs i' ∧
      (∀ r, ((vs i r : ℤ) : ZMod 2) = x r) ∧ (∀ r, ((vs i' r : ℤ) : ZMod 2) = x r) := by
    decide
  -- from {u, w} ⊆ range b with u ≠ w, get two distinct basis indices
  have pair : ∀ i, vs i ≠ w → ∃ b : Module.Basis (Fin 3) ℤ (Fin 3 → ℤ), ∃ j₁ j₂, j₁ ≠ j₂ ∧
      b j₁ = vs i ∧ b j₂ = w := by
    intro i hne
    obtain ⟨b, hb⟩ := hw i
    obtain ⟨j₁, hj₁⟩ := hb (Set.mem_insert _ _)
    obtain ⟨j₂, hj₂⟩ := hb (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    refine ⟨b, j₁, j₂, fun e => hne ?_, hj₁, hj₂⟩
    rw [← hj₁, ← hj₂, e]
  by_cases h0 : ∀ r, ((w r : ℤ) : ZMod 2) = 0
  · -- w is zero mod 2; use any vector of the family
    have hne : vs 0 ≠ w := by
      intro e; apply hnz 0; rw [e]; exact h0
    obtain ⟨b, j₁, j₂, -, -, hj₂⟩ := pair 0 hne
    apply (basis_mod_two b).1 j₂
    rw [hj₂]; exact h0
  · obtain ⟨i, i', hii', hi, hi'⟩ := hcov (fun r => ((w r : ℤ) : ZMod 2)) h0
    have key : ∀ t, vs t ≠ w → (∀ r, ((vs t r : ℤ) : ZMod 2) = ((w r : ℤ) : ZMod 2)) → False := by
      intro t hne ht
      obtain ⟨b, j₁, j₂, hj, hj₁, hj₂⟩ := pair t hne
      apply (basis_mod_two b).2 j₁ j₂ hj
      rw [hj₁, hj₂]; exact ht
    by_cases hiw : vs i = w
    · exact key i' (fun e => hii' (hiw.trans e.symm)) hi'
    · exact key i hiw hi
