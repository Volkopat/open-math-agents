import OMAStatements.S_mo_42902
import Mathlib

/-!
# The Marcus–de Oliveira conjecture for n ≤ 2

For `n ≤ 2` the conjecture holds. For `n = 2`, with `W = Uᴴ V` unitary and `t = |W₀₀|²`,
`det(A + B) = t (α₀+β₀)(α₁+β₁) + (1-t) (α₀+β₁)(α₁+β₀)`, a point of the segment between the two
permutation products. H1 is the case `n = 3` (Bebiano–Kovačec–da Providência 1994);
H2 is the open case `n ≥ 4`.
-/
namespace OMA.R_mo_42902_R1

open Matrix

/-- Conjugation by a unitary preserves the determinant. -/
theorem det_conj_unitary {n : Type} [Fintype n] [DecidableEq n]
    (U : Matrix.unitaryGroup n ℂ) (M : Matrix n n ℂ) :
    ((U : Matrix n n ℂ) * M * star (U : Matrix n n ℂ)).det = M.det := by
  have h := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  simp only [Matrix.det_mul, Matrix.det_one] at h ⊢
  linear_combination M.det * h

/-- Reduce to `diagonal α + W diagonal β Wᴴ` with `W = Uᴴ V`. -/
theorem relative_det {n : Type} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (U V : Matrix.unitaryGroup n ℂ) :
    ((U : Matrix n n ℂ) * diagonal a * star (U : Matrix n n ℂ) +
        (V : Matrix n n ℂ) * diagonal b * star (V : Matrix n n ℂ)).det =
      (diagonal a + ((star U * V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ) * diagonal b *
        star ((star U * V : Matrix.unitaryGroup n ℂ) : Matrix n n ℂ)).det := by
  rw [← det_conj_unitary U (diagonal a + _)]
  congr 1
  have hu : (U : Matrix n n ℂ) * star (U : Matrix n n ℂ) = 1 := Unitary.coe_mul_star_self U
  simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star, mul_add, add_mul,
    mul_assoc, hu, mul_one]
  rw [← mul_assoc (U : Matrix n n ℂ) (star (U : Matrix n n ℂ)), hu, one_mul]

/-- Key identity for `n = 2`. -/
theorem det_two_identity (a b : Fin 2 → ℂ) (W : Matrix (Fin 2) (Fin 2) ℂ)
    (h1 : W * star W = 1) (h2 : star W * W = 1) :
    (diagonal a + W * diagonal b * star W).det =
      (Complex.normSq (W 0 0) : ℂ) * ((a 0 + b 0) * (a 1 + b 1)) +
        (1 - (Complex.normSq (W 0 0) : ℂ)) * ((a 0 + b 1) * (a 1 + b 0)) := by
  have hdet : W.det * (star W).det = 1 := by
    rw [← Matrix.det_mul, h1, Matrix.det_one]
  have r1 := congrFun (congrFun h1 0) 0
  have r2 := congrFun (congrFun h1 1) 1
  have c1 := congrFun (congrFun h2 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq] at r1 r2 c1
  rw [Matrix.det_fin_two, Matrix.det_fin_two] at hdet
  simp only [Matrix.star_apply] at hdet
  rw [← Complex.mul_conj, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
    Matrix.star_apply, Fin.isValue, if_true, if_false, one_ne_zero, zero_ne_one, mul_zero,
    add_zero, zero_add]
  simp only [Complex.star_def] at r1 r2 c1 hdet ⊢
  linear_combination a 1 * b 1 * r1 + a 0 * b 0 * c1 + a 0 * b 1 * (r2 - c1) + b 0 * b 1 * hdet

/-- `normSq (W 0 0) ≤ 1` for a unitary `2 × 2` matrix. -/
theorem normSq_entry_le_one (W : Matrix (Fin 2) (Fin 2) ℂ) (h1 : W * star W = 1) :
    Complex.normSq (W 0 0) ≤ 1 := by
  have r1 := congrFun (congrFun h1 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, Matrix.one_apply_eq,
    Complex.star_def, Complex.mul_conj] at r1
  have r1' : Complex.normSq (W 0 0) + Complex.normSq (W 0 1) = 1 := by exact_mod_cast r1
  linarith [Complex.normSq_nonneg (W 0 1)]

/-- Segment membership in the convex hull of the permutation products, `n = 2`. -/
theorem mem_hull_two (a b : Fin 2 → ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t : ℂ) * ((a 0 + b 0) * (a 1 + b 1)) + (1 - (t : ℂ)) * ((a 0 + b 1) * (a 1 + b 0)) ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 2) => ∏ i, (a i + b (σ i))) := by
  have hx : (a 0 + b 0) * (a 1 + b 1) ∈
      Set.range fun σ : Equiv.Perm (Fin 2) => ∏ i, (a i + b (σ i)) :=
    ⟨1, by simp [Fin.prod_univ_two]⟩
  have hy : (a 0 + b 1) * (a 1 + b 0) ∈
      Set.range fun σ : Equiv.Perm (Fin 2) => ∏ i, (a i + b (σ i)) :=
    ⟨Equiv.swap 0 1, by simp [Fin.prod_univ_two]⟩
  apply segment_subset_convexHull hx hy
  refine ⟨t, 1 - t, ht0, by linarith, by ring, ?_⟩
  simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]

/-- The case `n = 2` of the statement. -/
theorem case_two (α β : Fin 2 → ℂ) (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    ((U : Matrix (Fin 2) (Fin 2) ℂ) * diagonal α * star (U : Matrix (Fin 2) (Fin 2) ℂ) +
        (V : Matrix (Fin 2) (Fin 2) ℂ) * diagonal β * star (V : Matrix (Fin 2) (Fin 2) ℂ)).det ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 2) => ∏ i, (α i + β (σ i))) := by
  rw [relative_det]
  set W := star U * V
  have h1 : (W : Matrix (Fin 2) (Fin 2) ℂ) * star (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Unitary.coe_mul_star_self W
  have h2 : star (W : Matrix (Fin 2) (Fin 2) ℂ) * (W : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Unitary.coe_star_mul_self W
  rw [det_two_identity α β _ h1 h2]
  exact mem_hull_two α β _ (Complex.normSq_nonneg _) (normSq_entry_le_one _ h1)

/-- The case `n = 1`. -/
theorem case_one (α β : Fin 1 → ℂ) (U V : Matrix.unitaryGroup (Fin 1) ℂ) :
    ((U : Matrix (Fin 1) (Fin 1) ℂ) * diagonal α * star (U : Matrix (Fin 1) (Fin 1) ℂ) +
        (V : Matrix (Fin 1) (Fin 1) ℂ) * diagonal β * star (V : Matrix (Fin 1) (Fin 1) ℂ)).det ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 1) => ∏ i, (α i + β (σ i))) := by
  rw [relative_det]
  set W := star U * V
  have h1 : (W : Matrix (Fin 1) (Fin 1) ℂ) * star (W : Matrix (Fin 1) (Fin 1) ℂ) = 1 :=
    Unitary.coe_mul_star_self W
  have r1 := congrFun (congrFun h1 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.star_apply, Matrix.one_apply_eq] at r1
  apply subset_convexHull
  refine ⟨1, ?_⟩
  simp only [Matrix.det_unique, Fin.default_eq_zero, Fin.prod_univ_one, Matrix.add_apply,
    Matrix.mul_apply, Fin.sum_univ_one, Matrix.diagonal_apply_eq, Matrix.star_apply,
    Equiv.Perm.coe_one, id_eq]
  linear_combination (-(β 0)) * r1

/-- The case `n = 0`. -/
theorem case_zero (α β : Fin 0 → ℂ) (U V : Matrix.unitaryGroup (Fin 0) ℂ) :
    ((U : Matrix (Fin 0) (Fin 0) ℂ) * diagonal α * star (U : Matrix (Fin 0) (Fin 0) ℂ) +
        (V : Matrix (Fin 0) (Fin 0) ℂ) * diagonal β * star (V : Matrix (Fin 0) (Fin 0) ℂ)).det ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 0) => ∏ i, (α i + β (σ i))) := by
  apply subset_convexHull
  exact ⟨1, by simp⟩


def H1 : Prop := ∀ (α β : Fin 3 → ℂ) (U V : Matrix.unitaryGroup (Fin 3) ℂ),
    let A : Matrix (Fin 3) (Fin 3) ℂ := (U : Matrix (Fin 3) (Fin 3) ℂ) * diagonal α * star (U : Matrix (Fin 3) (Fin 3) ℂ)
    let B : Matrix (Fin 3) (Fin 3) ℂ := (V : Matrix (Fin 3) (Fin 3) ℂ) * diagonal β * star (V : Matrix (Fin 3) (Fin 3) ℂ)
    (A + B).det ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin 3) => ∏ i, (α i + β (σ i)))

def H2 : Prop := ∀ (n : ℕ), 4 ≤ n → ∀ (α β : Fin n → ℂ) (U V : Matrix.unitaryGroup (Fin n) ℂ),
    let A : Matrix (Fin n) (Fin n) ℂ := (U : Matrix (Fin n) (Fin n) ℂ) * diagonal α * star (U : Matrix (Fin n) (Fin n) ℂ)
    let B : Matrix (Fin n) (Fin n) ℂ := (V : Matrix (Fin n) (Fin n) ℂ) * diagonal β * star (V : Matrix (Fin n) (Fin n) ℂ)
    (A + B).det ∈ convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) => ∏ i, (α i + β (σ i)))

theorem small (n : ℕ) (hn : n ≤ 2) (α β : Fin n → ℂ) (U V : Matrix.unitaryGroup (Fin n) ℂ) :
    ((U : Matrix (Fin n) (Fin n) ℂ) * diagonal α * star (U : Matrix (Fin n) (Fin n) ℂ) +
      (V : Matrix (Fin n) (Fin n) ℂ) * diagonal β * star (V : Matrix (Fin n) (Fin n) ℂ)).det ∈
      convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin n) => ∏ i, (α i + β (σ i))) := by
  interval_cases n
  · exact case_zero α β U V
  · exact case_one α β U V
  · exact case_two α β U V

theorem main : H1 → H2 → type_of% @OMA.S_mo_42902.main := by
  intro h3 h4 n α β U V A B
  rcases Nat.lt_or_ge n 3 with hn | hn
  · exact small n (by omega) α β U V
  · rcases Nat.eq_or_lt_of_le hn with h | h
    · subst h
      exact h3 α β U V
    · exact h4 n h α β U V

end OMA.R_mo_42902_R1
