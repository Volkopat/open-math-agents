import OMAStatements.S_mse_4636083

-- Problem mse-4636083: for some field K of characteristic 0 and some n >= 2 there is a proper subgroup of
-- GL_n(K) that is isomorphic to GL_n(K).
-- Upstream: statements/mse-4636083.lean (declaration OMA.S_mse_4636083.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: take K = Q and n = 2, and let phi(g) = det(g) * g. Scalars are central and det is multiplicative, so
-- phi is a group homomorphism of GL_2(Q) to itself. It is injective: det(phi(g)) = det(g)^3, cubing is injective
-- on Q, so phi(g) = phi(h) gives det g = det h and then g = h. It is not surjective: every matrix in the image
-- has determinant a rational cube, and diag(2, 1) has determinant 2, which is not a cube in Q (compare 2-adic
-- valuations). So the image of phi is a proper subgroup isomorphic to GL_2(Q).

open Matrix

private lemma two_not_cube (q : ℚ) : q ^ 3 ≠ 2 := by
  intro h
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := congrArg (padicValRat 2) h
  rw [padicValRat.pow q] at h1
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    have h0 := padicValRat.self (p := 2) (by norm_num)
    simpa using h0
  rw [h2] at h1
  push_cast at h1
  omega

theorem OMA.solution : type_of% @OMA.S_mse_4636083.main := by
  have hne : ∀ g : GL (Fin 2) ℚ, (g : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  have hne2 : ∀ g : GL (Fin 2) ℚ,
      ((g : Matrix (Fin 2) (Fin 2) ℚ).det • (g : Matrix (Fin 2) (Fin 2) ℚ)).det ≠ 0 := by
    intro g
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (hne g)) (hne g)
  obtain ⟨φ, hφ⟩ : ∃ φ : GL (Fin 2) ℚ →* GL (Fin 2) ℚ, ∀ g : GL (Fin 2) ℚ,
      ((φ g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
        (g : Matrix (Fin 2) (Fin 2) ℚ).det • (g : Matrix (Fin 2) (Fin 2) ℚ) := by
    refine ⟨MonoidHom.mk' (fun g => Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hne2 g)) ?_, fun g => rfl⟩
    intro g k
    apply Units.ext
    show ((g * k : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det •
        ((g * k : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((g : Matrix (Fin 2) (Fin 2) ℚ).det • (g : Matrix (Fin 2) (Fin 2) ℚ)) *
        ((k : Matrix (Fin 2) (Fin 2) ℚ).det • (k : Matrix (Fin 2) (Fin 2) ℚ))
    rw [Units.val_mul, Matrix.det_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hcube : ∀ t : ℚ, t ^ 2 * t = t ^ 3 := fun t => by ring
  have hdetφ : ∀ g : GL (Fin 2) ℚ,
      ((φ g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det = (g : Matrix (Fin 2) (Fin 2) ℚ).det ^ 3 := by
    intro g
    rw [hφ, Matrix.det_smul, Fintype.card_fin, hcube]
  have hinj : Function.Injective φ := by
    intro g k hgk
    have h1 : (g : Matrix (Fin 2) (Fin 2) ℚ).det ^ 3 = (k : Matrix (Fin 2) (Fin 2) ℚ).det ^ 3 := by
      rw [← hdetφ, ← hdetφ, hgk]
    have h2 : (g : Matrix (Fin 2) (Fin 2) ℚ).det = (k : Matrix (Fin 2) (Fin 2) ℚ).det :=
      (Odd.strictMono_pow (by decide : Odd 3)).injective h1
    have h3 : (g : Matrix (Fin 2) (Fin 2) ℚ).det • (g : Matrix (Fin 2) (Fin 2) ℚ) =
        (k : Matrix (Fin 2) (Fin 2) ℚ).det • (k : Matrix (Fin 2) (Fin 2) ℚ) := by
      rw [← hφ, ← hφ, hgk]
    rw [h2] at h3
    apply Units.ext
    exact smul_right_injective _ (hne k) h3
  have hA : (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    norm_num
  have hlt : φ.range < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hmem : Matrix.GeneralLinearGroup.mkOfDetNeZero (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) hA
        ∈ φ.range := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨g, hg⟩ := hmem
    have h1 := hdetφ g
    rw [hg] at h1
    have h2 : ((Matrix.GeneralLinearGroup.mkOfDetNeZero (!![2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) hA :
        GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![2, 0; 0, 1] := rfl
    rw [h2, Matrix.det_fin_two_of] at h1
    apply two_not_cube (g : Matrix (Fin 2) (Fin 2) ℚ).det
    rw [← h1]
    norm_num
  exact ⟨ℚ, inferInstance, inferInstance, 2, le_refl 2, φ.range, hlt,
    ⟨(MonoidHom.ofInjective hinj).symm⟩⟩
