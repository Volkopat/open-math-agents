import OMAStatements.S_mo_35878



/-! Adapt @AkiRA-COM-FP's proof in pending #15468, with the merged proof
by @Salofe in #19128 also inspected. Use restriction-of-scalars injectivity
for properness of the same maximal submodule. -/

open OMA.S_mo_35878

private theorem residue_dvd_module_dimension (k A : Type) [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] (d : ℕ) :
    ∀ (M : Type) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
      [FiniteDimensional k M], Module.finrank k M = d →
      Module.finrank k (IsLocalRing.ResidueField A) ∣ Module.finrank k M := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro M _ _ _ _ _ hDim
    by_cases hd : d = 0
    · rw [hDim,hd]
      exact dvd_zero _
    have hp : 0 < Module.finrank k M := by omega
    let _ : Nontrivial M := Module.nontrivial_of_finrank_pos hp
    let _ : IsNoetherian A M := isNoetherian_of_tower k (inferInstance : IsNoetherian k M)
    obtain ⟨S,hS⟩ := IsCoatomic.exists_coatom (α := Submodule A M)
    have hSimple : IsSimpleModule A (M ⧸ S) := isSimpleModule_iff_isCoatom.mpr hS
    obtain ⟨I,hI,⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hSimple
    have eqIdeal := IsLocalRing.eq_maximalIdeal hI
    subst I
    have hResidue :
        Module.finrank k (M ⧸ S) = Module.finrank k (IsLocalRing.ResidueField A) :=
      (e.restrictScalars k).finrank_eq
    let Sₖ := S.restrictScalars k
    let _ : FiniteDimensional k ↥S := inferInstanceAs (FiniteDimensional k ↥Sₖ)
    have hProper : Sₖ ≠ ⊤ := by simpa [Sₖ] using hS.1
    have hLt := Submodule.finrank_lt hProper
    have hDiv := ih (Module.finrank k S) (hDim ▸ hLt) (↥S) rfl
    have hSum := Sₖ.finrank_quotient_add_finrank
    change Module.finrank k (M ⧸ S) + Module.finrank k S = Module.finrank k M at hSum
    rw [←hSum,hResidue]
    exact Nat.dvd_add (dvd_refl _) hDiv

theorem OMA.solution : type_of% @OMA.S_mo_35878.main := by
  intro k A _ _ _ _ _
  exact residue_dvd_module_dimension k A (Module.finrank k A) A rfl
