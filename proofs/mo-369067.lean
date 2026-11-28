import OMAStatements.S_mo_369067

-- Retains @caa1982's projective-group counterexample from PR #26819.
-- The gcd-of-exponents and generator-closure APIs shorten the kernel argument.

open OMA.S_mo_369067

/-- The character `g ↦ det(g)^2` of `GL_3(F_7)`. -/
def chi : GL (Fin 3) (ZMod 7) →* (ZMod 7)ˣ :=
  (powMonoidHom 2).comp Matrix.GeneralLinearGroup.det

lemma units7_pow_six (u : (ZMod 7)ˣ) : u ^ 6 = 1 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have := ZMod.units_pow_card_sub_one_eq_one 7 u
  simpa using this

lemma center_le_ker : Subgroup.center (GL (Fin 3) (ZMod 7)) ≤ chi.ker := by
  intro g hg
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
  obtain ⟨u, rfl⟩ := hg
  rw [MonoidHom.mem_ker]
  simp only [chi, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) u) = u ^ 3 := by
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  rw [hdet, ← pow_mul]
  exact units7_pow_six u

/-- The induced character of `PGL_3(F_7)`. -/
def chiBar : Matrix.ProjGenLinGroup (Fin 3) (ZMod 7) →* (ZMod 7)ˣ :=
  QuotientGroup.lift (Subgroup.center (GL (Fin 3) (ZMod 7))) chi center_le_ker

/-- An element of `GL_3(F_7)` of determinant `3`. -/
def g3 : GL (Fin 3) (ZMod 7) :=
  ⟨!![3, 0, 0; 0, 1, 0; 0, 0, 1], !![5, 0, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

lemma chi_g3 : chi g3 ≠ 1 := by
  intro this
  simp only [chi, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply] at this
  have hval := congrArg Units.val this
  simp only [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
    g3, Matrix.det_fin_three] at hval
  revert hval
  decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_369067.main) := by
  intro h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨a, b, c, ha, hb, hc, hgen⟩ := h (ZMod 7)
  -- every value of chiBar is a square of a unit, hence has cube 1
  have hcube : ∀ x, chiBar x ^ 3 = 1 := by
    intro x
    obtain ⟨g, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    show chi g ^ 3 = 1
    simp only [chi, MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply, ← pow_mul]
    exact units7_pow_six _
  have hinv : ∀ x, IsInvolution x → x ∈ chiBar.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have h2 : chiBar x ^ 2 = 1 := by rw [← map_pow, hx.1, map_one]
    simpa using (pow_gcd_eq_one.mpr ⟨h2, hcube x⟩)
  have hle : Subgroup.closure {a, b, c} ≤ chiBar.ker := by
    simpa [Subgroup.closure_le, Set.insert_subset_iff] using ⟨hinv a ha, hinv b hb, hinv c hc⟩
  rw [hgen] at hle
  have hg := hle (Subgroup.mem_top (Matrix.ProjGenLinGroup.mk g3))
  rw [MonoidHom.mem_ker] at hg
  exact chi_g3 hg
