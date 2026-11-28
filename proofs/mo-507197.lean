import OMAStatements.S_mo_507197

/-!
Complete proof by @connoranderson, linked from merged statement PR #21765
and task-desk DONE #98360, pinned at:
https://github.com/connoranderson/open-math-agents/blob/b4cc202df8a9cb9b9f52aeef179e15e899e1eafb/proofs/mo-507197.lean
This port retains all mathematical source and adds attribution.
# The rank of a signed circulant after entrywise squaring

Source: xoxo, https://mathoverflow.net/questions/507197 (CC BY-SA 4.0).
Credit: @connoranderson.

Products of column coordinates give the quadratic upper bound. Supports
of a spanning set of rows cover every nonzero column, giving the lower
bound in terms of row weight. Reduction modulo q supplies examples of
rank q in dimension q² whose entrywise square has rank one.
-/

namespace OMA.S_mo_507197

open Finset

private lemma rank_square_entries {ι : Type} [Fintype ι] (B : Matrix ι ι ℝ) :
    (Matrix.of (fun i j => B i j ^ 2)).rank ≤ B.rank ^ 2 := by
  classical
  let V := Submodule.span ℝ (Set.range B.col)
  let d := Module.finrank ℝ V
  let b := Module.finBasis ℝ V
  let v (j : ι) : V := ⟨B.col j, Submodule.subset_span (Set.mem_range_self j)⟩
  let x (u : Fin d) (j : ι) := b.repr (v j) u
  have hex (i j : ι) : ∑ u : Fin d, (b u).1 i * x u j = B i j := by
    have e := congrArg (fun z : V => z.1 i) (b.sum_repr (v j))
    change (↑(∑ u, b.repr (v j) u • b u) : ι → ℝ) i = B i j at e
    simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, mul_comm, x] using e
  let L : Matrix ι (Fin d × Fin d) ℝ := Matrix.of (fun i k => (b k.1).1 i * (b k.2).1 i)
  let R : Matrix (Fin d × Fin d) ι ℝ := Matrix.of (fun k j => x k.1 j * x k.2 j)
  have hfac : Matrix.of (fun i j => B i j ^ 2) = L * R := by
    ext i j
    simp only [Matrix.of_apply,Matrix.mul_apply,L,R]
    rw [← hex i j, sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro w _
    ring
  calc
    _ = (L * R).rank := congrArg Matrix.rank hfac
    _ ≤ L.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin d × Fin d) := L.rank_le_card_width
    _ = B.rank ^ 2 := by simp [d, V, B.rank_eq_finrank_span_cols, sq]

end OMA.S_mo_507197

namespace OMA.S_mo_507197

open Finset

private lemma support_cover {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (w : ℕ)
    (hn : ∀ j, ∃ i, A i j ≠ 0)
    (hw : ∀ i, (univ.filter fun j => A i j ≠ 0).card ≤ w) :
    Fintype.card ι ≤ w * A.rank := by
  classical
  obtain ⟨s, hs, hc, hspan, _⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ (Set.range A.row)
  let supp (v : ι → ℝ) := univ.filter (fun j => v j ≠ 0)
  have hcover : univ ⊆ s.biUnion supp := by
    intro j _
    by_contra h
    obtain ⟨i, hi⟩ := hn j
    have hker : Submodule.span ℝ (s : Set (ι → ℝ)) ≤ LinearMap.ker (LinearMap.proj j) := by
      apply Submodule.span_le.mpr
      intro v hv
      change v j = 0
      by_contra hz
      exact h (Finset.mem_biUnion.mpr ⟨v,hv,mem_filter.mpr ⟨mem_univ _,hz⟩⟩)
    rw [hspan] at hker
    exact hi (hker (Submodule.subset_span (Set.mem_range_self i)))
  calc
    _ = (univ : Finset ι).card := card_univ.symm
    _ ≤ (s.biUnion supp).card := card_le_card hcover
    _ ≤ ∑ v ∈ s, (supp v).card := card_biUnion_le
    _ ≤ ∑ _v ∈ s, w := by
      apply sum_le_sum
      intro v hv
      obtain ⟨i, rfl⟩ := hs hv
      exact hw i
    _ = w * A.rank := by simp [hc,A.rank_eq_finrank_span_row,Nat.mul_comm]

private lemma circulant_support {n : ℕ} [NeZero n] (v : ZMod n → ℝ)
    (hv : ∃ i, v i ≠ 0) :
    n ≤ weight v * (Matrix.circulant (fun i => v i ^ 2)).rank := by
  classical
  apply (ZMod.card n) ▸ support_cover _ _ ?_ ?_
  · intro j
    obtain ⟨a,ha⟩ := hv
    exact ⟨a+j, by simpa [Matrix.circulant_apply] using ha⟩
  · intro i
    apply Nat.le_of_eq
    unfold weight
    apply Finset.card_bij' (fun j _ => i-j) (fun j _ => i-j)
    · intro j hj
      simpa [Matrix.circulant_apply] using hj
    · intro j hj
      simpa [Matrix.circulant_apply] using hj
    · intro j _
      simp
    · intro j _
      simp

end OMA.S_mo_507197

namespace OMA.S_mo_507197

open Matrix Finset
open scoped Matrix

private lemma submatrix_rank_of_surjective {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I I ℝ) (f : J → I) (hf : Function.Surjective f) :
    (A.submatrix f f).rank = A.rank := by
  classical
  obtain ⟨s, hs⟩ := hf.hasRightInverse
  apply (A.rank_submatrix_le f f).antisymm
  have h := (A.submatrix f f).rank_submatrix_le s s
  have he : (A.submatrix f f).submatrix s s = A := by
    ext i j
    simp [Matrix.submatrix_apply, hs i, hs j]
  simpa only [he] using h

private def periodMatrix (q : ℕ) : Matrix (ZMod q) (ZMod q) ℝ :=
  fun i j => if i = j then -1 else 1

private lemma periodMatrix_rank (q : ℕ) [NeZero q] (hq : 3 ≤ q) : (periodMatrix q).rank = q := by
  classical
  have hval (x : ZMod q → ℝ) (i : ZMod q) :
      ((periodMatrix q) *ᵥ x) i = (∑ j, x j) - 2*x i := by
    change (∑ j, (if i = j then (-1:ℝ) else 1) * x j) = _
    have ht (j : ZMod q) : (if i = j then (-1:ℝ) else 1) * x j = x j - (if j=i then 2*x i else 0) := by
      by_cases h : i=j
      · simp [h]; ring
      · simp [h, Ne.symm h]
    simp [ht, Finset.sum_sub_distrib]
  apply (Matrix.rank_of_isUnit _ ?_).trans (ZMod.card q)
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hdiff (i : ZMod q) : (∑ j, x j) - ∑ j, y j = 2*(x i-y i) := by
    have h := congrFun hxy i
    rw [hval, hval] at h
    linarith
  have hconst (i : ZMod q) : x i - y i = x 0-y 0 := by linarith [hdiff i, hdiff 0]
  have hsum : (∑ j, x j) - ∑ j, y j = q*(x 0-y 0) := by
    rw [← Finset.sum_sub_distrib]
    simp only [hconst, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hq' : (2:ℝ) < q := by exact_mod_cast (show 2 < q by omega)
  have hz : ((q:ℝ)-2)*(x 0-y 0)=0 := by linarith [hdiff 0]
  have heq := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hq'.ne')
  funext i
  linarith [hconst i]

private lemma ones_rank (q : ℕ) [NeZero q] :
    Matrix.rank (fun _ _ : ZMod q => (1 : ℝ)) = 1 := by
  classical
  let J : Matrix (ZMod q) (ZMod q) ℝ := fun _ _ => 1
  change J.rank = 1
  have hJ : J = Matrix.vecMulVec (fun _ : ZMod q => (1:ℝ)) (fun _ : ZMod q => (1:ℝ)) := by
    ext i j
    simp [J, Matrix.vecMulVec]
  apply le_antisymm
  · rw [hJ]
    exact Matrix.rank_vecMulVec_le _ _
  · let e (_ : Fin 1) : ZMod q := 0
    have h := J.rank_submatrix_le e e
    have hsub : J.submatrix e e = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j
      change (1:ℝ) = (1 : Matrix (Fin 1) (Fin 1) ℝ) i j
      simp [Matrix.one_apply, Subsingleton.elim i j]
    simpa only [hsub, Matrix.rank_one, Fintype.card_fin] using h

lemma periodic_examples (q : ℕ) [NeZero q] (hq : 3 ≤ q) :
    ∃ v : ZMod (q*q) → ℝ, (∀ i, v i = -1 ∨ v i = 0 ∨ v i = 1) ∧
      (Matrix.circulant v).rank = q ∧ (Matrix.circulant (fun i => v i ^ 2)).rank = 1 := by
  classical
  let red := ZMod.castHom (dvd_mul_right q q) (ZMod q)
  let v (i : ZMod (q*q)) : ℝ := if red i = 0 then -1 else 1
  refine ⟨v, fun i => by dsimp [v]; split_ifs <;> simp, ?_, ?_⟩
  · have he : Matrix.circulant v = (periodMatrix q).submatrix red red := by
      ext i j
      simp [Matrix.circulant_apply, v, periodMatrix, sub_eq_zero]
    rw [he, submatrix_rank_of_surjective _ _ (ZMod.castHom_surjective _), periodMatrix_rank q hq]
  · have he : Matrix.circulant (fun i => v i ^ 2) =
        (fun _ _ : ZMod (q*q) => (1 : ℝ)) := by
      ext i j
      simp only [Matrix.circulant_apply, v]
      split_ifs <;> norm_num
    rw [he]
    exact ones_rank (q*q)

end OMA.S_mo_507197

theorem OMA.solution : type_of% @OMA.S_mo_507197.main := by
  classical
  constructor
  · intro n _ v _
    dsimp only
    refine ⟨OMA.S_mo_507197.rank_square_entries (Matrix.circulant v),?_⟩
    intro hv
    have h := OMA.S_mo_507197.circulant_support v hv
    refine ⟨h,fun hr => Nat.le_of_mul_le_mul_left (hr.trans h) ?_⟩
    obtain ⟨i,hi⟩ := hv
    exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  · exact OMA.S_mo_507197.periodic_examples
