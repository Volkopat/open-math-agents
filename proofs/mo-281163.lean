import OMAStatements.S_mo_281163

/-!
Problem by fanfare, “Can a quadratic matrix inequality constraint be convex?”
https://mathoverflow.net/questions/281163 (CC BY-SA 3.0).
Formal statement credit: @connoranderson. Independent proof by @grp06.
-/

namespace OMA.S_mo_281163

open scoped BigOperators

private theorem quad_scale {n q : ℕ}
    (M : Fin q → Fin q → Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x : Fin n → ℝ) :
    quad M (c • x) = c ^ 2 • quad M x := by
  ext a b
  change (∑ i, ∑ j, (c * x i) * M a b i j * (c * x j)) =
    c ^ 2 * (∑ i, ∑ j, x i * M a b i j * x j)
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem convex_part {n q : ℕ}
    (M : Fin q → Fin q → Matrix (Fin n) (Fin n) ℝ) :
    let S := {x : Fin n → ℝ | (-(quad M x)).PosSemidef}
    (Convex ℝ S ↔ ∃ W : Submodule ℝ (Fin n → ℝ), S = (W : Set (Fin n → ℝ))) ∧
    (Convex ℝ S → ∃ L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ),
      ∀ x, x ∈ S ↔ (lmi L x).PosSemidef) := by
  classical
  let S := {x : Fin n → ℝ | (-(quad M x)).PosSemidef}
  change (Convex ℝ S ↔ _) ∧ (Convex ℝ S → _)
  have scale_mem (c : ℝ) {x : Fin n → ℝ} (hx : x ∈ S) : c • x ∈ S := by
    change (-(quad M x)).PosSemidef at hx
    change (-(quad M (c • x))).PosSemidef
    rw [quad_scale, ← smul_neg]
    exact hx.smul (sq_nonneg c)
  have subspace (h : Convex ℝ S) :
      ∃ W : Submodule ℝ (Fin n → ℝ), S = (W : Set (Fin n → ℝ)) := by
    let W : Submodule ℝ (Fin n → ℝ) :=
      { carrier := S
        zero_mem' := by
          change (-(quad M 0)).PosSemidef
          have hz : quad M 0 = 0 := by
            ext a b
            simp [quad]
          rw [hz, neg_zero]
          exact Matrix.PosSemidef.zero
        add_mem' := by
          intro x y hx hy
          have hm := scale_mem 2 (h.midpoint_mem hx hy)
          rwa [midpoint_eq_smul_add, smul_smul, mul_invOf_self, one_smul] at hm
        smul_mem' := fun c _ hx => scale_mem c hx }
    exact ⟨W, rfl⟩
  constructor
  · refine ⟨subspace, ?_⟩
    rintro ⟨W, hW⟩
    change S = (W : Set (Fin n → ℝ)) at hW
    rw [hW]
    exact W.convex
  · intro h
    obtain ⟨W, hW⟩ := subspace h
    obtain ⟨V, hV⟩ := W.exists_isCompl
    let L := V.projection W hV.symm
    refine ⟨L, fun x => ?_⟩
    have hker : L x = 0 ↔ x ∈ W :=
      Submodule.projection_apply_eq_zero_iff hV.symm
    change x ∈ S ↔ (lmi L x).PosSemidef
    rw [hW]
    change x ∈ W ↔ (lmi L x).PosSemidef
    rw [← hker, lmi, Matrix.posSemidef_diagonal_iff]
    constructor
    · intro hx i
      simp [hx]
    · intro hx
      funext i
      have hp : 0 ≤ L x i := by simpa using hx (i, true)
      have hn : 0 ≤ -L x i := by simpa using hx (i, false)
      exact le_antisymm (nonpos_of_neg_nonneg hn) hp

private theorem quad_gram {n q r : ℕ}
    (F : Fin r → Fin q → Fin n → ℝ) (x : Fin n → ℝ)
    (G : Matrix (Fin r) (Fin q) ℝ) (hG : ∀ t a, G t a = ∑ i, F t a i * x i) :
    quad (symmGram F) x = G.conjTranspose * G := by
  have coeff (a b : Fin q) :
      (∑ i, ∑ j, x i * gramCoeff F a b i j * x j) = ∑ t, G t a * G t b := by
    calc
      _ = ∑ i, ∑ j, ∑ t, (F t a i * x i) * (F t b j * x j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [gramCoeff, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun t _ => by ring
      _ = ∑ i, ∑ t, ∑ j, (F t a i * x i) * (F t b j * x j) := by
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ t, ∑ i, ∑ j, (F t a i * x i) * (F t b j * x j) :=
        Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hG t a, hG t b, Finset.sum_mul]
        simp only [Finset.mul_sum]
  ext a b
  have havg : quad (symmGram F) x a b =
      (1 / 2 : ℝ) * ((∑ i, ∑ j, x i * gramCoeff F a b i j * x j) +
        (∑ i, ∑ j, x i * gramCoeff F b a i j * x j)) := by
    calc
      _ = ∑ i, ∑ j, (1 / 2 : ℝ) *
          (x i * gramCoeff F a b i j * x j + x i * gramCoeff F b a i j * x j) := by
        simp only [quad, symmGram, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [havg, coeff a b, coeff b a, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, star_trivial]
  have hswap : (∑ t, G t b * G t a) = ∑ t, G t a * G t b :=
    Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [hswap]
  ring

private theorem gram_part {n q r : ℕ} (F : Fin r → Fin q → Fin n → ℝ)
    (x : Fin n → ℝ) :
    (∀ a b, symmGram F a b = symmGram F b a) ∧
      ((-(quad (symmGram F) x)).PosSemidef ↔
        ∀ t a, (∑ i, F t a i * x i) = 0) := by
  constructor
  · intro a b
    simp only [symmGram, add_comm (gramCoeff F a b) (gramCoeff F b a)]
  · let G : Matrix (Fin r) (Fin q) ℝ := fun t a => ∑ i, F t a i * x i
    have hG : ∀ t a, G t a = ∑ i, F t a i * x i := fun _ _ => rfl
    change (-(quad (symmGram F) x)).PosSemidef ↔ ∀ t a, G t a = 0
    rw [quad_gram F x G hG]
    constructor
    · intro h t a
      have hdiag : 0 ≤ -(∑ s, G s a * G s a) := by
        simpa only [Matrix.neg_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
          star_trivial] using (h.diag_nonneg (i := a))
      have hnonneg : 0 ≤ ∑ s, G s a * G s a :=
        Finset.sum_nonneg fun s _ => mul_self_nonneg (G s a)
      have hsum : (∑ s, G s a * G s a) = 0 :=
        le_antisymm (nonpos_of_neg_nonneg hdiag) hnonneg
      have ht : G t a * G t a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => mul_self_nonneg (G s a))).mp
          hsum t (Finset.mem_univ t)
      exact (mul_eq_zero.mp ht).elim id id
    · intro hz
      have hzero : G = 0 := by
        ext t a
        exact hz t a
      rw [hzero, Matrix.conjTranspose_zero, Matrix.zero_mul, neg_zero]
      exact Matrix.PosSemidef.zero

end OMA.S_mo_281163

theorem OMA.solution : type_of% @OMA.S_mo_281163.main := by
  constructor
  · intro n q M _
    exact OMA.S_mo_281163.convex_part M
  · intro n q r F x
    exact OMA.S_mo_281163.gram_part F x
