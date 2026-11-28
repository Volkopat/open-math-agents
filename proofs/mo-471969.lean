import OMAStatements.S_mo_471969

/-!
# A fifteen-vertex counterexample to the diagonal cofactor assertion

Source: user528497, https://mathoverflow.net/questions/471969 (CC BY-SA 4.0).
Credit: @connoranderson.

The graph is Figure 2 in A. Birkinshaw, P. W. Fowler, J. Goedgebeur,
and J. Jooken, On graphs isomorphic with their conduction graph (2025),
https://doi.org/10.46793/match.93-2.379B, House of Graphs 35457,
https://houseofgraphs.org/graphs/35457.

The row masks reproduce its adjacency matrix A. The integral certificate
H has zero diagonal and satisfies AH=4I. Determinants give nonsingularity,
and multiplying by the adjugate gives 4 adj(A)=det(A) H.
-/

namespace OMA.S_mo_471969

open Matrix

private def masks : Fin 15 → ℕ := ![3086, 25345, 19009, 5505, 5728, 3472, 24724, 12392, 18474, 12310, 24633, 12581, 19096, 3778, 5446]

private def adjacency : Matrix (Fin 15) (Fin 15) ℤ :=
  Matrix.of (fun i j => if (masks i).testBit j.val then 1 else 0)

private def witness : Matrix (Fin 15) (Fin 15) ℤ := !![
  0, -1, 1, 1, -1, -1, -1, -1, -1, 0, 2, 1, 0, 1, 0;
  -1, 0, -1, 0, -1, -1, -1, -1, 1, 1, 1, 0, 0, 2, 1;
  1, -1, 0, -1, 0, -1, 1, -1, -1, -1, 0, 2, 1, 0, 1;
  1, 0, -1, 0, -1, -1, -1, 1, -1, -1, 1, 0, 2, 0, 1;
  -1, -1, 0, -1, 0, 1, -1, -1, -1, 1, 2, 0, 1, 0, 1;
  -1, -1, -1, -1, 1, 0, 0, -1, 1, -1, 1, 2, 0, 1, 0;
  -1, -1, 1, -1, -1, 0, 0, 1, -1, -1, 1, 0, 0, 1, 2;
  -1, -1, -1, 1, -1, -1, 1, 0, 0, -1, 0, 1, 1, 2, 0;
  -1, 1, -1, -1, -1, 1, -1, 0, 0, -1, 0, 1, 1, 0, 2;
  0, 1, -1, -1, 1, -1, -1, -1, -1, 0, 0, 1, 2, 1, 0;
  2, 1, 0, 1, 2, 1, 1, 0, 0, 0, 0, -2, -2, -1, -1;
  1, 0, 2, 0, 0, 2, 0, 1, 1, 1, -2, 0, -1, -1, -2;
  0, 0, 1, 2, 1, 0, 0, 1, 1, 2, -2, -1, 0, -2, -1;
  1, 2, 0, 0, 0, 1, 1, 2, 0, 1, -1, -1, -2, 0, -2;
  0, 1, 1, 1, 1, 0, 2, 0, 2, 0, -1, -2, -1, -2, 0]

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private lemma checkBits : (∀ i j, adjacency i j = adjacency j i) ∧
    (∀ i, adjacency i i = 0) ∧ (∀ i, witness i i = 0) := by
  refine ⟨?_,by decide,by decide⟩
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private lemma product_cert : adjacency * witness = (4 : ℤ) • 1 := by
  have h : ∀ i j, (adjacency * witness) i j = (if i=j then 4 else 0) := by decide
  ext i j
  rw [h]
  simp [Matrix.one_apply]

private lemma counterexample : ∃ A : Matrix (Fin 15) (Fin 15) ℝ,
    A.IsSymm ∧ (∀ i j, A i j = 0 ∨ A i j = 1) ∧ (∀ i, A i i = 0) ∧
    A.det ≠ 0 ∧ ∀ i, A.adjugate i i = 0 := by
  let f := Int.castRingHom ℝ
  let A := f.mapMatrix adjacency
  let H := f.mapMatrix witness
  have hs : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact congrArg f ((checkBits.1 _ _))
  have h01 (i j : Fin 15) : A i j = 0 ∨ A i j = 1 := by
    change f (if (masks i).testBit j.val then 1 else 0) = 0 ∨
      f (if (masks i).testBit j.val then 1 else 0) = 1
    split_ifs <;> simp
  have hA (i : Fin 15) : A i i = 0 := by
    change f (adjacency i i) = 0
    rw [checkBits.2.1 i,map_zero]
  have hH (i : Fin 15) : H i i = 0 := by
    change f (witness i i) = 0
    rw [checkBits.2.2 i,map_zero]
  have hprod : A * H = (4 : ℝ) • 1 := by
    change f.mapMatrix adjacency * f.mapMatrix witness = _
    rw [← map_mul,product_cert]
    ext i j
    change f ((4:ℤ) * (1 : Matrix (Fin 15) (Fin 15) ℤ) i j) =
      (4:ℝ) * (1 : Matrix (Fin 15) (Fin 15) ℝ) i j
    by_cases he : i = j <;> simp [Matrix.one_apply,he]
  have hdet : A.det ≠ 0 := by
    intro h
    have e := congrArg Matrix.det hprod
    rw [Matrix.det_mul,h,zero_mul,Matrix.det_smul,Matrix.det_one,mul_one] at e
    norm_num at e
  refine ⟨A,hs,h01,hA,hdet,?_⟩
  have e : (4 : ℝ) • A.adjugate = A.det • H := by
    calc
      _ = A.adjugate * ((4 : ℝ) • 1) := by simp
      _ = A.adjugate * (A*H) := by rw [hprod]
      _ = (A.adjugate*A)*H := (Matrix.mul_assoc ..).symm
      _ = A.det • H := by simp [Matrix.adjugate_mul]
  intro i
  have v := congrArg (fun M : Matrix (Fin 15) (Fin 15) ℝ => M i i) e
  change 4 * A.adjugate i i = A.det * H i i at v
  rw [hH,mul_zero] at v
  exact (mul_eq_zero.mp v).resolve_left (by norm_num)

end OMA.S_mo_471969

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_471969.main) := by
  intro h
  obtain ⟨A,hs,h01,hzero,hd,hcof⟩ := OMA.S_mo_471969.counterexample
  obtain ⟨i,hi⟩ := h 15 (by decide) A hs h01 hzero hd
  exact hi (hcof i)
