import OMAStatements.S_mo_218860

open OMA.S_mo_218860

private theorem quad_relation (x y : ℝ × ℝ) :
    let v := quadratic x - quadratic y
    (v 1)^2*v 2 - 2*v 0*v 1*v 3 + (v 0)^2*v 4 = 0 := by
  simp [quadratic, Pi.sub_apply, Matrix.cons_val_zero]
  ring

private theorem quad_realize (v : Fin 5 → ℝ) (s t : ℝ)
    (hs : v 0 * s = v 2) (ht : v 1 * t = v 4)
    (hm : (v 0 * t + v 1 * s) / 2 = v 3) :
    ∃ x y : ℝ × ℝ, quadratic x - quadratic y = v := by
  refine ⟨((s + v 0)/2, (t + v 1)/2), ((s - v 0)/2, (t - v 1)/2), ?_⟩
  funext i
  fin_cases i <;> simp [quadratic, Pi.sub_apply, Matrix.cons_val_zero] <;>
    linarith only [hs, ht, hm]

private theorem quad_realize_of_relation (v : Fin 5 → ℝ)
    (hr : (v 1)^2*v 2 - 2*v 0*v 1*v 3 + (v 0)^2*v 4 = 0)
    (hne : v 0 ≠ 0 ∨ v 1 ≠ 0) :
    ∃ x y : ℝ × ℝ, quadratic x - quadratic y = v := by
  by_cases hu : v 0 = 0
  · have hw : v 1 ≠ 0 := hne.resolve_left (fun hn => hn hu)
    refine quad_realize v (2 * v 3 / v 1) (v 4 / v 1) ?_ ?_ ?_
    · rw [hu, zero_mul]
      have hq : (v 1)^2 * v 2 = 0 := by simpa [hu] using hr
      exact ((mul_eq_zero.mp hq).resolve_left (pow_ne_zero _ hw)).symm
    · field_simp
    · rw [hu, zero_mul, zero_add]
      field_simp
  · refine quad_realize v (v 2 / v 0) ((2*v 3 - v 1 * (v 2 / v 0)) / v 0) ?_ ?_ ?_
    · field_simp
    · field_simp
      linear_combination -hr
    · field_simp
      ring

private theorem quad_test (m : ℕ) (A : Matrix (Fin m) (Fin 5) ℝ) :
    Function.Injective (fun x : ℝ × ℝ => A.mulVec (quadratic x)) ↔
      ∀ v, A.mulVec v = 0 → (v 1)^2*v 2 - 2*v 0*v 1*v 3 + (v 0)^2*v 4 = 0 → v 0 = 0 ∧ v 1 = 0 := by
  constructor
  · intro hinj v hv hr
    by_contra h
    have hn : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_cases h₁ : v 0 = 0
      · exact Or.inr fun h₂ => h ⟨h₁,h₂⟩
      · exact Or.inl h₁
    obtain ⟨x,y,hxy⟩ := quad_realize_of_relation v hr hn
    rw [← hxy, Matrix.mulVec_sub, sub_eq_zero] at hv
    have he : x = y := hinj hv
    subst y
    rw [sub_self] at hxy
    apply h
    rw [← hxy]
    exact ⟨rfl,rfl⟩
  · intro h x y hxy
    change A.mulVec (quadratic x) = A.mulVec (quadratic y) at hxy
    have hk : A.mulVec (quadratic x - quadratic y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    obtain ⟨h₁,h₂⟩ := h _ hk (quad_relation x y)
    apply Prod.ext
    · exact sub_eq_zero.mp (by simpa [quadratic, Pi.sub_apply] using h₁)
    · exact sub_eq_zero.mp (by simpa [quadratic, Pi.sub_apply] using h₂)

private theorem lin_coordinate {d p : ℕ} (hp : 2 ≤ p) (x : Fin d → ℝ) (i : Fin d) :
    veronese x (linIdx hp i) = x i := by simp [veronese, linIdx]

private theorem quad_coordinate {d p : ℕ} (hp : 2 ≤ p) (x : Fin d → ℝ) (i j : Fin d) :
    veronese x (quadIdx hp i j) = x i * x j := by simp [veronese, quadIdx]

private theorem reconstruct_difference {d p : ℕ} (hp : 2 ≤ p) (x y : Fin d → ℝ)
    (j : Fin d) (hj : x j - y j ≠ 0) (i : Fin d) :
    midpointSum hp (veronese x - veronese y) j i = x i + y i := by
  simp only [midpointSum, Pi.sub_apply, lin_coordinate, quad_coordinate]
  field_simp
  ring

private theorem veronese_test (d m p : ℕ) (hp : 2 ≤ p) (A : Matrix (Fin m) (Mono d p) ℝ) :
    Function.Injective (fun x : Fin d → ℝ => A.mulVec (veronese x)) ↔
      ∀ v, A.mulVec v = 0 → ∀ j, v (linIdx hp j) ≠ 0 →
        ∃ s, v s ≠ veronese (reconstructed hp v j 1) s - veronese (reconstructed hp v j (-1)) s := by
  constructor
  · intro hinj v hv j hj
    by_contra! h
    have he : v = veronese (reconstructed hp v j 1) - veronese (reconstructed hp v j (-1)) :=
      funext h
    rw [he, Matrix.mulVec_sub, sub_eq_zero] at hv
    have eqp : reconstructed hp v j 1 = reconstructed hp v j (-1) := hinj hv
    apply hj
    rw [he, Pi.sub_apply, eqp, sub_self]
  · intro h x y hxy
    funext j
    by_contra hj
    let v : Mono d p → ℝ := veronese x - veronese y
    change A.mulVec (veronese x) = A.mulVec (veronese y) at hxy
    have hk : A.mulVec v = 0 := by
      dsimp only [v]
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hjv : v (linIdx hp j) ≠ 0 := by simpa [v, Pi.sub_apply, lin_coordinate, sub_ne_zero] using hj
    obtain ⟨s,hs⟩ := h v hk j hjv
    have hx : reconstructed hp v j 1 = x := by
      funext i
      simp only [reconstructed, v, reconstruct_difference hp x y j (sub_ne_zero.mpr hj) i,
        Pi.sub_apply, lin_coordinate]
      ring
    have hy : reconstructed hp v j (-1) = y := by
      funext i
      simp only [reconstructed, v, reconstruct_difference hp x y j (sub_ne_zero.mpr hj) i,
        Pi.sub_apply, lin_coordinate]
      ring
    apply hs
    rw [hx, hy]
    rfl

private theorem linear_test (d m : ℕ) (A : Matrix (Fin m) (Fin d) ℝ) :
    Function.Injective A.mulVec ↔ ∀ v, A.mulVec v = 0 → v = 0 := by
  constructor
  · intro h v hv
    apply h
    rwa [Matrix.mulVec_zero]
  · intro h x y hxy
    apply sub_eq_zero.mp
    apply h
    rw [Matrix.mulVec_sub, hxy, sub_self]

theorem OMA.solution : type_of% @OMA.S_mo_218860.main := ⟨quad_test, veronese_test, linear_test⟩