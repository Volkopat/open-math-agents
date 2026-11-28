import OMAStatements.S_mo_450037

/-!
Complete proof by @connoranderson, linked from statement PR #21676 and desk DONE #97378.
Pinned source: https://github.com/connoranderson/open-math-agents/blob/eb9153a9e3c88aca39758e8c206232e47a1c66d0/proofs/mo-450037.lean
All mathematical source is unchanged; this port adds provenance and current-checker validation.
Port and validation: @rodolfoquint.

The finite grid tests polynomial identities of bounded coordinate degree.
Linear relations between the product polynomials are therefore exactly
the relations between the columns of their evaluation table.

For a pair of linear forms with real coefficient vectors a,b, symmetrize
the tensor a⊗a⊗b⊗b over the six choices of two positions. Pairing it
with x⊗x⊗x⊗x evaluates six times the quartic. Fourth powers of a+b, a-b,
a and b recover this symmetric tensor by polarization, so the quartic
relations are exactly the corresponding tensor relations. Their Gram
matrix is six times the explicit matrix of pairwise coefficient contractions.

The MathOverflow source and Luc Guyot's valuation and leading-term sufficient
criteria are at https://mathoverflow.net/questions/450037 . The grid
and symmetric-tensor determinant tests below are necessary and sufficient.
-/

namespace OMA.S_mo_450037

private theorem grid_test (K : Type) [Field K] (m n k d : ℕ) (F : Fin n → MvPolynomial (Fin m) K)
    (grid : Fin (k*d+1) → K) (hg : Function.Injective grid) (hf : ∀ i, (F i).IsHomogeneous d) :
    LinearIndependent K (fun S : Subsets n k => ∏ i ∈ S.1, F i) ↔
      (valueTable F grid).rank=Fintype.card (Subsets n k) := by
  classical
  let P (s : Subsets n k) := ∏ i ∈ s.1, F i
  let V := valueTable F grid
  let T := Finset.univ.image grid
  have hc : T.card=k*d+1 := by
    rw [Finset.card_image_of_injective _ hg];simp
  have degree (s : Subsets n k) : (P s).IsHomogeneous (k*d) := by
    simpa [P,s.2] using (MvPolynomial.IsHomogeneous.prod s.1 F (fun _ => d) (fun i _ => hf i))
  have ev (v : Subsets n k → K) (x : Fin m → Fin (k*d+1)) :
      MvPolynomial.eval (fun i => grid (x i)) (∑ s, v s • P s)=(∑ s, v s • V.col s) x := by
    simp [P,V,valueTable,Matrix.col,Finset.sum_apply,MvPolynomial.smul_eq_C_mul]
  have iff_rel (v : Subsets n k → K) : ∑ s, v s • P s=0 ↔ ∑ s, v s • V.col s=0 := by
    constructor
    · intro h;funext x;rw [← ev,h,map_zero];rfl
    · intro h
      apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ (fun _ => T)
      · intro i
        have hh : (∑ s, v s • P s).IsHomogeneous (k*d) :=
          MvPolynomial.IsHomogeneous.sum _ _ _ (fun s _ => by rw [MvPolynomial.smul_eq_C_mul];exact (degree s).C_mul _)
        exact lt_of_le_of_lt ((MvPolynomial.degreeOf_le_totalDegree _ _).trans hh.totalDegree_le) (by omega)
      · intro x hx
        have ex (i : Fin m) : ∃ a, grid a=x i := by
          obtain ⟨a,_,h⟩ := Finset.mem_image.mp (hx i)
          exact ⟨a,h⟩
        choose y hy using ex
        rw [← (funext hy),ev,h];rfl
  change LinearIndependent K P ↔ V.rank=_
  rw [V.rank_eq_finrank_span_cols,eq_comm]
  change LinearIndependent K P ↔ Fintype.card (Subsets n k) = (Set.range V.col).finrank K
  rw [← linearIndependent_iff_card_eq_finrank_span]
  simp only [Fintype.linearIndependent_iff,iff_rel]

end OMA.S_mo_450037

namespace OMA.S_mo_450037
open scoped InnerProductSpace
private abbrev Four (m : ℕ) := Fin m × Fin m × Fin m × Fin m
private abbrev E (m : ℕ) := EuclideanSpace ℝ (Four m)
private abbrev Vec (m : ℕ) := Fin m → ℝ

private noncomputable def tensor {m : ℕ} (a b c d : Vec m) : E m :=
  WithLp.toLp 2 (fun z => a z.1*b z.2.1*c z.2.2.1*d z.2.2.2)

private lemma sum_four {m : ℕ} (a b c d : Vec m) :
    ∑ z : Four m, a z.1*b z.2.1*c z.2.2.1*d z.2.2.2 =
      (∑ i,a i)*(∑ i,b i)*(∑ i,c i)*(∑ i,d i) := by
  simp only [Fintype.sum_prod_type,mul_assoc]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]

private lemma tensor_inner {m : ℕ} (a b c d w x y z : Vec m) :
    ⟪tensor a b c d,tensor w x y z⟫_ℝ =
      dotProduct a w*dotProduct b x*dotProduct c y*dotProduct d z := by
  rw [PiLp.inner_apply]
  calc
    _ = ∑ i : Four m, (a i.1*w i.1)*(b i.2.1*x i.2.1)*(c i.2.2.1*y i.2.2.1)*(d i.2.2.2*z i.2.2.2) := by
      apply Finset.sum_congr rfl;intro i _
      change (w i.1*x i.2.1*y i.2.2.1*z i.2.2.2)*(a i.1*b i.2.1*c i.2.2.1*d i.2.2.2)=_
      ring
    _ = _ := sum_four (fun i => a i*w i) (fun i => b i*x i) (fun i => c i*y i) (fun i => d i*z i)

private noncomputable def symTensor {m : ℕ} (a b : Vec m) : E m :=
  tensor a a b b + tensor a b a b + tensor a b b a + tensor b a a b +
    tensor b a b a + tensor b b a a

private noncomputable def pureTensor {m : ℕ} (a : Vec m) : E m := tensor a a a a

private lemma polarization {m : ℕ} (a b : Vec m) :
    pureTensor (a+b)+pureTensor (a-b)-(2:ℝ) • pureTensor a-(2:ℝ) • pureTensor b =
      (2:ℝ) • symTensor a b := by
  ext i
  change ((a i.1+b i.1)*(a i.2.1+b i.2.1)*(a i.2.2.1+b i.2.2.1)*(a i.2.2.2+b i.2.2.2) +
    (a i.1-b i.1)*(a i.2.1-b i.2.1)*(a i.2.2.1-b i.2.2.1)*(a i.2.2.2-b i.2.2.2) -
    2*(a i.1*a i.2.1*a i.2.2.1*a i.2.2.2)-2*(b i.1*b i.2.1*b i.2.2.1*b i.2.2.2)) =
    2*((a i.1*a i.2.1*b i.2.2.1*b i.2.2.2) +
      (a i.1*b i.2.1*a i.2.2.1*b i.2.2.2) +
      (a i.1*b i.2.1*b i.2.2.1*a i.2.2.2) +
      (b i.1*a i.2.1*a i.2.2.1*b i.2.2.2) +
      (b i.1*a i.2.1*b i.2.2.1*a i.2.2.2) +
      (b i.1*b i.2.1*a i.2.2.1*a i.2.2.2))
  ring

private lemma sym_inner_pure {m : ℕ} (a b x : Vec m) :
    ⟪symTensor a b,pureTensor x⟫_ℝ=6*dotProduct a x^2*dotProduct b x^2 := by
  simp only [symTensor,pureTensor,inner_add_left,tensor_inner]
  ring

private lemma sym_inner {m : ℕ} (a b c d : Vec m) :
    ⟪symTensor a b,symTensor c d⟫_ℝ =
      6*(dotProduct a c^2*dotProduct b d^2+
        4*dotProduct a c*dotProduct a d*dotProduct b c*dotProduct b d+
        dotProduct a d^2*dotProduct b c^2) := by
  simp only [symTensor,inner_add_left,inner_add_right,tensor_inner]
  ring

end OMA.S_mo_450037

namespace OMA.S_mo_450037
open scoped InnerProductSpace

private lemma eval_form {m : ℕ} (x a : Vec m) : MvPolynomial.eval x (form a)=dotProduct a x := by
  simp [form,dotProduct]

private theorem pairs_test (m n : ℕ) (u : Fin n → Fin m → ℝ) :
    LinearIndependent ℝ (fun s : Pairs n => form (u s.1.1)^2*form (u s.1.2)^2) ↔
      (pairMatrix u).det ≠ 0 := by
  classical
  let Q (s : Pairs n) := form (u s.1.1)^2*form (u s.1.2)^2
  let V (s : Pairs n) := symTensor (u s.1.1) (u s.1.2)
  have rel (c : Pairs n → ℝ) : ∑ s, c s • Q s=0 ↔ ∑ s, c s • V s=0 := by
    let f := ∑ s, c s • Q s
    let T := ∑ s, c s • V s
    have value (x : Vec m) : ⟪T,pureTensor x⟫_ℝ=6*MvPolynomial.eval x f := by
      simp only [T,f,sum_inner,real_inner_smul_left,V,sym_inner_pure,Q,map_sum,
        MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,map_pow,eval_form,Finset.mul_sum]
      apply Finset.sum_congr rfl;intro _ _;ring
    change f=0 ↔ T=0
    constructor
    · intro hf
      have hd (x : Vec m) : ⟪T,pureTensor x⟫_ℝ=0 := by simp [value,hf]
      have hV (s : Pairs n) : ⟪T,V s⟫_ℝ=0 := by
        have h := congrArg (fun t : E m => ⟪T,t⟫_ℝ) (polarization (u s.1.1) (u s.1.2))
        simp only [inner_sub_right,inner_add_right,real_inner_smul_right,hd] at h
        change ⟪T,symTensor _ _⟫_ℝ=0
        linarith
      apply (inner_self_eq_zero (𝕜:=ℝ)).mp
      change ⟪T,∑ s, c s • V s⟫_ℝ=0
      simp only [inner_sum,real_inner_smul_right,hV,mul_zero,Finset.sum_const_zero]
    · intro hT
      apply MvPolynomial.funext
      intro x
      have e := value x
      rw [hT,inner_zero_left] at e
      rw [map_zero];linarith
  have li : LinearIndependent ℝ Q ↔ LinearIndependent ℝ V := by
    simp only [Fintype.linearIndependent_iff,rel]
  have gram : Matrix.gram ℝ V=(6:ℝ) • pairMatrix u := by
    ext i j
    exact sym_inner _ _ _ _
  change LinearIndependent ℝ Q ↔ _
  rw [li,← Matrix.det_gram_ne_zero_iff_linearIndependent,gram,Matrix.det_smul]
  simp

end OMA.S_mo_450037

theorem OMA.solution : type_of% @OMA.S_mo_450037.main :=
  ⟨OMA.S_mo_450037.grid_test,OMA.S_mo_450037.pairs_test⟩
