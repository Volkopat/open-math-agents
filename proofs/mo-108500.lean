import OMAStatements.S_mo_108500

namespace OMA.S_mo_108500
open Matrix Finset Set

private def matrices {n : ℕ} (u : Coord n → ℝ) : P n :=
  (fun i j => u (some (false,i,j)), fun i j => u (some (true,i,j)))

private def coords {n : ℕ} (X : P n) : Coord n → ℝ
  | none => 1
  | some (false,i,j) => X.1 i j
  | some (true,i,j) => X.2 i j

private def residual {n : ℕ} (u : Coord n → ℝ) (b : Bool) (i j : Fin n) : ℝ :=
  ∑ a : Term n, termWeight i j a * u (termSlot b i a) * u (termSlot b j a)

private lemma square_pure {n : ℕ} (u : Coord n → ℝ) (c : Bool) (i j : Fin n) :
    squareTest c i j (power4 u) = residual u c i j ^ 2 := by
  simp only [squareTest, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    entry4, LinearMap.coe_mk, AddHom.coe_mk, power4, residual, sq, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma residual_eq {n : ℕ} (u : Coord n → ℝ) (b : Bool) (i j : Fin n) :
    residual u b i j =
      (if b then colGram (matrices u) i j else rowGram (matrices u) i j) -
          (u none)^2 * (1 : Mat n) i j := by
  have hr (x : P n) : rowGram x i j =
      (∑ k, x.1 i k * x.1 j k) + ∑ k, x.2 i k * x.2 j k := rfl
  have hc (x : P n) : colGram x i j =
      (∑ k, x.1 k i * x.1 k j) + ∑ k, x.2 k i * x.2 k j := rfl
  cases b <;> simp [residual, Fintype.sum_option, Fintype.sum_prod_type,
      termWeight, termSlot, hr, hc, matrices] <;> ring

private lemma energy_pure {n : ℕ} (u : Coord n → ℝ) :
    energy n (power4 u) = ∑ i, ∑ j, (residual u false i j ^ 2 + residual u true i j ^ 2) := by
  simp [energy, LinearMap.sum_apply, square_pure]

private lemma energy_nonneg {n : ℕ} (u : Coord n → ℝ) : 0 ≤ energy n (power4 u) := by
  rw [energy_pure]
  positivity

private lemma energy_zero_iff {n : ℕ} (u : Coord n → ℝ) :
    energy n (power4 u) = 0 ↔
      rowGram (matrices u) = (u none)^2 • (1 : Mat n) ∧
      colGram (matrices u) = (u none)^2 • (1 : Mat n) := by
  rw [energy_pure, Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp only [Finset.mem_univ, forall_true_left,
    Finset.sum_eq_zero_iff_of_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _)),
    residual_eq, Bool.false_eq_true, if_false, if_true]
  constructor
  · intro h
    constructor <;> ext i j <;> specialize h i j <;>
      simp only [Matrix.smul_apply, smul_eq_mul] <;> nlinarith [sq_nonneg
        (rowGram (matrices u) i j - u none ^ 2 * (1 : Mat n) i j), sq_nonneg
        (colGram (matrices u) i j - u none ^ 2 * (1 : Mat n) i j)]
  · rintro ⟨hr,hc⟩ i j
    simp [hr,hc,Matrix.smul_apply]


private lemma project_pure {n : ℕ} (u : Coord n → ℝ) :
    project4 n (power4 u) = (u none)^3 • matrices u := by
  apply Prod.ext <;> ext i j
  · change u none * u none * u none * _ = (u none)^3 * _
    dsimp [matrices]
    ring
  · change u none * u none * u none * _ = (u none)^3 * _
    dsimp [matrices]
    ring

private lemma mass_pure {n : ℕ} (u : Coord n → ℝ) :
    entry4 none none none none (power4 u) = (u none)^4 := by
  change u none * u none * u none * u none = _
  ring

private lemma normalize_balanced {n : ℕ} (u : Coord n → ℝ) (ht : u none ≠ 0)
    (he : energy n (power4 u) = 0) : (u none)⁻¹ • matrices u ∈ balanced n := by
  obtain ⟨hr,hc⟩ := (energy_zero_iff u).mp he
  have hsc : ∀ (v : ℝ) (x : P n), rowGram (v • x) = v^2 • rowGram x ∧
      colGram (v • x) = v^2 • colGram x := by
    intro v x
    simp [rowGram, colGram, Matrix.transpose_smul,
      smul_smul, smul_add, pow_two]
  change rowGram _ = 1 ∧ colGram _ = 1
  rw [(hsc _ _).1,(hsc _ _).2,hr,hc,smul_smul]
  simp [ht]

lemma conic_exact (n : ℕ) : convexHull ℝ (balanced n) = quarticHull n := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨ι, _, c, z, hc, hc1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hx
    let u (i : ι) := coords (z i)
    have hmat (i : ι) : matrices (u i) = z i := rfl
    have ht (i : ι) : u i none = 1 := rfl
    have he (i : ι) : energy n (power4 (u i)) = 0 := by
      apply (energy_zero_iff _).mpr
      simpa [balanced, hmat, ht] using hz i
    refine ⟨∑ i, c i • power4 (u i), ⟨ι, inferInstance,c,u,hc,rfl⟩, ?_, ?_, ?_⟩
    · change entry4 none none none none (∑ i, c i • power4 (u i)) = 1
      simpa [map_sum, mass_pure, ht] using hc1
    · simp [map_sum,he]
    · simpa [map_sum,project_pure,ht,hmat] using hsum
  · rintro ⟨_, ⟨ι, _, c, u, hc, rfl⟩, hm, he, hx⟩
    change entry4 none none none none (∑ i, c i • power4 (u i)) = 1 at hm
    simp only [map_sum, map_smul, smul_eq_mul, mass_pure] at hm
    simp only [map_sum, map_smul, smul_eq_mul] at he
    have heach := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hc i) (energy_nonneg (u i)))).mp he
    let z (i : ι) : P n :=
      if c i * (u i none)^4 = 0 then (1,0) else (u i none)⁻¹ • matrices (u i)
    refine mem_convexHull_of_exists_fintype (fun i => c i * (u i none)^4) z
      (fun i => mul_nonneg (hc i) (by positivity)) hm ?_ ?_
    · intro i
      dsimp [z]
      split_ifs with h
      · simp [balanced, rowGram, colGram]
      · have hc' : c i ≠ 0 := fun hi => h (by simp [hi])
        have ht : u i none ≠ 0 := fun hi => h (by simp [hi])
        exact normalize_balanced _ ht ((mul_eq_zero.mp (heach i (mem_univ _))).resolve_left hc')
    · rw [← hx,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, project_pure, smul_smul]
      dsimp [z]
      split_ifs with h
      · rcases mul_eq_zero.mp h with hc0 | ht0
        · simp [hc0]
        · have ht : u i none = 0 := by simpa using ht0
          simp [ht]
      · rw [smul_smul]
        congr 1
        have ht : u i none ≠ 0 := fun hi => h (by simp [hi])
        field_simp

end OMA.S_mo_108500

namespace OMA.S_mo_108500
open Matrix Finset Set
private lemma gramJensen {n : ℕ} (X Y : P n) (a b : ℝ) (hab : a+b=1) :
    (1:Mat n) - rowGram (a • X + b • Y) =
      a • (1-rowGram X) + b • (1-rowGram Y) + (a*b) • rowGram (X-Y) := by
  obtain rfl : b=1-a := by linarith
  simp only [rowGram,Prod.fst_add, Prod.snd_add, Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,Matrix.transpose_add,Matrix.transpose_smul,
    Matrix.transpose_sub,add_mul,mul_add,sub_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul]
  module
private lemma row_psd {n : ℕ} (X : P n) : (rowGram X).PosSemidef := by
  simpa [rowGram] using (Matrix.posSemidef_self_mul_conjTranspose X.1).add
    (Matrix.posSemidef_self_mul_conjTranspose X.2)
private lemma row_conv {n : ℕ} {X Y : P n}
    (hx : ((1:Mat n)-rowGram X).PosSemidef) (hy : ((1:Mat n)-rowGram Y).PosSemidef)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) :
    ((1:Mat n)-rowGram (a • X + b • Y)).PosSemidef := by
  rw [gramJensen X Y a b hab]
  exact ((hx.smul ha).add (hy.smul hb)).add ((row_psd _).smul (mul_nonneg ha hb))
lemma hull_subset (n : ℕ) : convexHull ℝ (balanced n) ⊆ relaxed n := by
  apply convexHull_min
  · intro X hX
    exact ⟨by simpa [hX.1] using (Matrix.PosSemidef.zero (n:=Fin n) (R:=ℝ)),
      by simpa [hX.2] using (Matrix.PosSemidef.zero (n:=Fin n) (R:=ℝ))⟩
  · intro X hX Y hY a b ha hb hab
    refine ⟨row_conv hX.1 hY.1 ha hb hab,?_⟩
    let tr (X : P n) : P n := (X.1.transpose,X.2.transpose)
    have ht (X : P n) : rowGram (tr X) = colGram X := by simp [rowGram,colGram,tr]
    have hh := row_conv (X:=tr X) (Y:=tr Y) (ht X ▸ hX.2) (ht Y ▸ hY.2) ha hb hab
    simpa [rowGram,colGram,tr,Matrix.transpose_add,Matrix.transpose_smul] using hh
end OMA.S_mo_108500

namespace OMA.S_mo_108500
open Matrix Finset Set

private def tp (X : P 3) : P 3 := (X.1.transpose, X.2.transpose)
private def rd (X Y : P 3) (i : Fin 3) : ℝ :=
  ∑ j, (X.1 i j * Y.1 i j + X.2 i j * Y.2 i j)
private noncomputable def score (X : P 3) : ℝ :=
  rd X examplePair 0 + rd X examplePair 1 +
  rd (tp X) examplePair 0 + rd (tp X) examplePair 1

private lemma row_self (X : P 3) (i : Fin 3) : rd X X i = rowGram X i i := by
  simp [rd, rowGram, Matrix.mul_apply, Finset.sum_add_distrib]
private lemma tp_rel {X : P 3} (h : X ∈ relaxed 3) : tp X ∈ relaxed 3 := by
  exact ⟨by simpa [rowGram, colGram, tp] using h.2,
    by simpa [rowGram, colGram, tp] using h.1⟩
private lemma row_le {X : P 3} (h : X ∈ relaxed 3) (i : Fin 3) : rd X X i ≤ 1 := by
  have hh := h.1.diag_nonneg (i := i)
  simpa [row_self] using (sub_nonneg.mp (show 0 ≤ (1:ℝ) - rowGram X i i by simpa using hh))
private lemma unit_row (i : Fin 3) (hi : i=0 ∨ i=1) : rd examplePair examplePair i = 1 := by
  rcases hi with rfl | rfl <;> norm_num [rd, examplePair, Fin.sum_univ_succ]
private lemma row_contact {X : P 3} (h : X ∈ relaxed 3) (i : Fin 3) (hi : i=0 ∨ i=1) :
    rd X examplePair i ≤ 1 ∧ (rd X examplePair i = 1 →
      ∀ j, X.1 i j = examplePair.1 i j ∧ X.2 i j = examplePair.2 i j) := by
  let gap (j : Fin 3) := (X.1 i j-examplePair.1 i j)^2 + (X.2 i j-examplePair.2 i j)^2
  have hnn (j) : 0 ≤ gap j := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hg : ∑ j, gap j = rd X X i + rd examplePair examplePair i - 2*rd X examplePair i := by
    simp only [rd, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by dsimp [gap]; ring
  have h1 := row_le h i
  have h2 := unit_row i hi
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun j _ => hnn j)
  refine ⟨by linarith, ?_⟩
  intro h3 j
  have hz : ∑ j, gap j = 0 := by linarith
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnn j)).mp hz j (Finset.mem_univ _)
  dsimp [gap] at hj
  rw [add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _),sq_eq_zero_iff,sq_eq_zero_iff,
    sub_eq_zero,sub_eq_zero] at hj
  exact hj

private lemma zero_col {M : Mat 3} (h : M.PosSemidef) {i : Fin 3} (hi : M i i = 0)
    (j : Fin 3) : M j i = 0 := by
  let v : Fin 3 → ℝ := Pi.single i 1
  have he : star v ⬝ᵥ M *ᵥ v = 0 := by
    simpa [v, Matrix.mulVec_single_one, single_dotProduct] using hi
  have hz := congrFun ((h.dotProduct_mulVec_zero_iff v).mp he) j
  simpa [v, Matrix.mulVec_single_one] using hz

private lemma example_rel : examplePair ∈ relaxed 3 := by
  have hr : (1:Mat 3)-rowGram examplePair = diagonal ![0,0,(7/25:ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rowGram,Matrix.sub_apply,Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply]
      <;> norm_num [examplePair,Fin.sum_univ_succ,Matrix.diagonal]
  have hc : colGram examplePair = rowGram examplePair := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [colGram,rowGram,Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply]
      <;> norm_num [examplePair,Fin.sum_univ_succ]
  have hd : (diagonal ![0,0,(7/25:ℝ)]).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num
  exact ⟨hr ▸ hd, hc ▸ hr ▸ hd⟩

private lemma example_unbalanced : examplePair ∉ balanced 3 := by
  intro h
  have hG : rowGram examplePair = Matrix.diagonal ![1,1,(18/25:ℝ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rowGram,Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply]
      <;> norm_num [examplePair,Fin.sum_univ_succ,Matrix.diagonal]
  have he := congrFun (congrFun (hG.symm.trans h.1) (2:Fin 3)) 2
  change (18/25:ℝ) = 1 at he
  norm_num at he

end OMA.S_mo_108500

namespace OMA.S_mo_108500
open Matrix Finset Set
private lemma at_most {X : P 3} (h : X ∈ relaxed 3) : score X ≤ 4 := by
  unfold score
  linarith [(row_contact h 0 (Or.inl rfl)).1,(row_contact h 1 (Or.inr rfl)).1,
    (row_contact (tp_rel h) 0 (Or.inl rfl)).1,(row_contact (tp_rel h) 1 (Or.inr rfl)).1]

private noncomputable def filled (a b : ℝ) : P 3 :=
  ( !![0,0,3/5; 0,4/5,0; 3/5,0,a], !![4/5,0,0; 0,0,3/5; 0,3/5,b] )

private lemma filled_slack (a b : ℝ) :
    (1:Mat 3) - rowGram (filled a b) =
    !![0,0,-3/5*a; 0,0,-3/5*b; -3/5*a,-3/5*b,7/25-a^2-b^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rowGram,Matrix.sub_apply,Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply]
    <;> norm_num [filled,Fin.sum_univ_succ,Matrix.one_apply] <;> ring

private lemma filled_unique {a b : ℝ} (h : filled a b ∈ relaxed 3) : filled a b = examplePair := by
  let M := (1:Mat 3) - rowGram (filled a b)
  have hM := filled_slack a b
  have z0 : M 0 0 = 0 := by dsimp only [M]; rw [hM]; rfl
  have z1 : M 1 1 = 0 := by dsimp only [M]; rw [hM]; rfl
  have e0 := zero_col h.1 z0 2
  have e1 := zero_col h.1 z1 2
  rw [hM] at e0 e1
  change -3/5*a = 0 at e0
  change -3/5*b = 0 at e1
  have ea : a=0 := by linarith
  have eb : b=0 := by linarith
  rw [ea,eb]
  rfl

private lemma four_tight {a b c d : ℝ} (ha : a≤1) (hb : b≤1) (hc : c≤1) (hd : d≤1)
    (he : a+b+c+d=4) : a=1 ∧ b=1 ∧ c=1 ∧ d=1 := by
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

private lemma make_three {α : Type*} (f : Fin 3 → α) {a b c : α}
    (ha : f 0=a) (hb : f 1=b) (hc : f 2=c) : f = ![a,b,c] := by
  funext j
  fin_cases j
  · exact ha
  · exact hb
  · exact hc

private lemma unique_max {X : P 3} (h : X ∈ relaxed 3) (hs : score X = 4) : X = examplePair := by
  have h0 := row_contact h 0 (Or.inl rfl)
  have h1 := row_contact h 1 (Or.inr rfl)
  have t0 := row_contact (tp_rel h) 0 (Or.inl rfl)
  have t1 := row_contact (tp_rel h) 1 (Or.inr rfl)
  obtain ⟨e0,e1,e2,e3⟩ := four_tight h0.1 h1.1 t0.1 t1.1 hs
  have r0 := h0.2 e0
  have r1 := h1.2 e1
  have c0 := t0.2 e2
  have c1 := t1.2 e3
  have hf : X = filled (X.1 2 2) (X.2 2 2) := by
    apply Prod.ext
    · apply make_three
      · exact funext fun j => (r0 j).1
      · exact funext fun j => (r1 j).1
      · exact make_three _ (c0 2).1 (c1 2).1 rfl
    · apply make_three
      · exact funext fun j => (r0 j).2
      · exact funext fun j => (r1 j).2
      · exact make_three _ (c0 2).2 (c1 2).2 rfl
  exact hf.trans (filled_unique ((congrArg (fun Y => Y ∈ relaxed 3) hf).mp h))

private lemma score_combo (X Y : P 3) (a b : ℝ) :
    score (a • X + b • Y) = a * score X + b * score Y := by
  simp [score,rd,tp,examplePair,Fin.sum_univ_succ]
  ring

private lemma score_example : score examplePair = 4 := by
  norm_num [score,rd,tp,examplePair,Fin.sum_univ_succ]

lemma example_extreme : examplePair ∈ (relaxed 3).extremePoints ℝ := by
  refine mem_extremePoints_iff_left.mpr ⟨example_rel, ?_⟩
  intro X hX Y hY hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hxy := congrArg score he
  rw [score_combo,score_example] at hxy
  apply unique_max hX
  have hbound := at_most hX
  have hother := mul_nonneg hb.le (sub_nonneg.mpr (at_most hY))
  have hzero : a*(4-score X) ≤ 0 := by nlinarith
  exact le_antisymm hbound (by
    by_contra! hlt
    exact (not_lt_of_ge hzero) (mul_pos ha (sub_pos.mpr hlt)))

lemma example_outside : examplePair ∉ convexHull ℝ (balanced 3) := by
  have hsub : balanced 3 ⊆ {X | score X < 4} := by
    intro X hX
    have hr : X ∈ relaxed 3 := ⟨by simpa [hX.1] using (Matrix.PosSemidef.zero (n:=Fin 3) (R:=ℝ)),
      by simpa [hX.2] using (Matrix.PosSemidef.zero (n:=Fin 3) (R:=ℝ))⟩
    refine lt_of_le_of_ne (at_most hr) ?_
    intro he
    exact example_unbalanced (unique_max hr he ▸ hX)
  have hc : Convex ℝ {X : P 3 | score X < 4} := by
    intro X hX Y hY a b ha hb hab
    change score X < 4 at hX
    change score Y < 4 at hY
    change score (a • X + b • Y) < 4
    rw [score_combo]
    rcases eq_or_lt_of_le ha with haz | hap
    · rw [← haz] at hab ⊢
      simpa [show b=1 by linarith] using hY
    · nlinarith [mul_pos hap (sub_pos.mpr hX),mul_nonneg hb (sub_nonneg.mpr hY.le)]
  intro hh
  have hh' : score examplePair < 4 := convexHull_min hsub hc hh
  linarith [score_example,hh']
end OMA.S_mo_108500

open OMA.S_mo_108500
theorem OMA.solution : type_of% @OMA.S_mo_108500.main :=
  ⟨conic_exact,hull_subset,example_extreme,example_outside⟩
