import OMAStatements.S_mo_387067

/-!
Retains @romechenko’s grid counterexample from #16418.
Uses standard outer-product and linear-map range APIs for the rank bounds.

Index rows and columns by pairs in a square grid. Let B and D be the matrices
recording equality of the first and second coordinates. Then the signed
matrix B-D has rank linear in the grid side length, whereas its absolute value
is B+D-2I and has rank quadratic. For blocks of size two the positive and
negative indicator matrices both occur as submatrices of the blow-up.
-/

open Matrix OMA.S_mo_387067

namespace OMA.MO387067

private theorem rankAdd {ι κ : Type} [Fintype ι] [Fintype κ] (A B : Matrix ι κ ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

private theorem rankNeg {ι κ : Type} [Fintype κ] (A : Matrix ι κ ℝ) :
    (-A).rank = A.rank := by
  have h : (-A).mulVecLin = -A.mulVecLin := LinearMap.ext (fun v => neg_mulVec v A)
  unfold Matrix.rank
  rw [h, LinearMap.range_neg]

private abbrev Grid (r : ℕ) := Fin r × Fin r

private def first (r : ℕ) : Matrix (Grid r) (Grid r) ℝ :=
  of fun i j => if i.1 = j.1 then 1 else 0

private def second (r : ℕ) : Matrix (Grid r) (Grid r) ℝ :=
  of fun i j => if i.2 = j.2 then 1 else 0

private def signedGrid (r : ℕ) : Matrix (Grid r) (Grid r) ℝ :=
  first r - second r

private def absMatrix {ι : Type} (A : Matrix ι ι ℝ) : Matrix ι ι ℝ := of fun i j => |A i j|

private theorem rankFirst (r : ℕ) : (first r).rank ≤ r := by
  simpa [first, Matrix.submatrix, Matrix.one_apply] using
    rank_submatrix_le (1 : Matrix (Fin r) (Fin r) ℝ)
      (Prod.fst : Grid r → Fin r) (Prod.fst : Grid r → Fin r)

private theorem rankSecond (r : ℕ) : (second r).rank ≤ r := by
  simpa [second, Matrix.submatrix, Matrix.one_apply] using
    rank_submatrix_le (1 : Matrix (Fin r) (Fin r) ℝ)
      (Prod.snd : Grid r → Fin r) (Prod.snd : Grid r → Fin r)

private theorem rankUpper (r : ℕ) : (signedGrid r).rank ≤ 2 * r := by
  have h := rankAdd (first r) (-second r)
  rw [rankNeg, ← sub_eq_add_neg, ← signedGrid] at h
  exact h.trans ((Nat.add_le_add (rankFirst r) (rankSecond r)).trans_eq (by omega))

private theorem entries (r : ℕ) (i j : Grid r) :
    signedGrid r i j = -1 ∨ signedGrid r i j = 0 ∨ signedGrid r i j = 1 := by
  by_cases h : i.1 = j.1 <;> by_cases h' : i.2 = j.2 <;>
    norm_num [signedGrid, first, second, h, h']

private theorem rankLower (r : ℕ) (hr : 0 < r) : r ≤ (signedGrid r).rank + 1 := by
  let z : Fin r := ⟨0, hr⟩
  let J : Matrix (Fin r) (Fin r) ℝ := of fun _ _ => 1
  let K := (signedGrid r).submatrix (fun i : Fin r => (i, z)) (fun j : Fin r => (j, z))
  have hjrank : J.rank ≤ 1 := by
    simpa [J, vecMulVec] using rank_vecMulVec_le (fun _ : Fin r => (1 : ℝ)) (fun _ : Fin r => (1 : ℝ))
  have hK : K + J = (1 : Matrix (Fin r) (Fin r) ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [K, J, signedGrid, first, second, Matrix.one_apply, h]
  have hrank := rankAdd K J
  rw [hK, rank_one, Fintype.card_fin] at hrank
  have hkRank : K.rank ≤ (signedGrid r).rank := rank_submatrix_le _ _ _
  omega

private theorem absLower (r : ℕ) : r * r ≤ 2 * r + (absMatrix (signedGrid r)).rank := by
  let A := absMatrix (signedGrid r)
  have h : first r + second r - A = (2 : ℝ) • (1 : Matrix (Grid r) (Grid r) ℝ) := by
    ext i j
    obtain ⟨i₁, i₂⟩ := i
    obtain ⟨j₁, j₂⟩ := j
    by_cases h₀ : i₁ = j₁ <;> by_cases h₁ : i₂ = j₂ <;>
      norm_num [A, absMatrix, signedGrid, first, second, Matrix.one_apply, h₀, h₁]
  have h1 : ((2 : ℝ) • (1 : Matrix (Grid r) (Grid r) ℝ)).rank = r * r := by
    rw [rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (show (2 : ℝ) ≠ 0 by norm_num)), rank_one]
    simp
  have h2 := rankAdd (first r + second r) (-A)
  rw [rankNeg, ← sub_eq_add_neg, h, h1] at h2
  have h3 := rankAdd (first r) (second r)
  have h4 := rankFirst r
  have h5 := rankSecond r
  exact h2.trans (Nat.add_le_add_right (h3.trans (by omega)) _)

private theorem absUpper {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) :
    (absMatrix A).rank ≤ 2 * (blowUp 2 n A).rank := by
  let f (i : Fin n) : Fin n × Fin 2 := (i, 0)
  let g (i : Fin n) : Fin n × Fin 2 := (i, 1)
  let P := (blowUp 2 n A).submatrix f f
  let Q := (blowUp 2 n A).submatrix g f
  have hEq : absMatrix A = P + Q := by
    ext i j
    rcases h i j with h₀ | h₀ | h₀ <;>
      norm_num [P, Q, f, g, absMatrix, blowUp, h₀]
  rw [hEq]
  have hp : P.rank ≤ (blowUp 2 n A).rank := rank_submatrix_le _ _ _
  have hq : Q.rank ≤ (blowUp 2 n A).rank := rank_submatrix_le _ _ _
  have htotal := rankAdd P Q
  omega

theorem disproof : ¬ (type_of% @OMA.S_mo_387067.main) := by
  intro h
  obtain ⟨C, r₀, hC⟩ := h 2
  let r := max (r₀ + 1) (4 * C + 3)
  have hr₀ : r₀ + 1 ≤ r := le_max_left _ _
  have hrC : 4 * C + 3 ≤ r := le_max_right _ _
  have hr : 0 < r := by omega
  let e : Grid r ≃ Fin (r * r) := finProdFinEquiv
  let A := (signedGrid r).reindex e e
  have hA : A.rank = (signedGrid r).rank := rank_reindex _ _ _
  have hentries (i j : Fin (r * r)) : A i j = -1 ∨ A i j = 0 ∨ A i j = 1 :=
    entries r (e.symm i) (e.symm j)
  have hrank : r₀ ≤ A.rank := by
    rw [hA]
    have := rankLower r hr
    omega
  have hupper := hC (r * r) A hentries hrank
  have hArUpper : A.rank ≤ 2 * r := hA ▸ rankUpper r
  have hblow := hupper.trans (Nat.mul_le_mul_left C hArUpper)
  have habs : (absMatrix A).rank = (absMatrix (signedGrid r)).rank :=
    rank_reindex e e (absMatrix (signedGrid r))
  have hlarge := absLower r
  rw [← habs] at hlarge
  have hgrowth := hlarge.trans (Nat.add_le_add_left ((absUpper A hentries).trans
    (Nat.mul_le_mul_left 2 hblow)) (2 * r))
  have hlimit : r * r ≤ (4 * C + 2) * r := hgrowth.trans_eq (by ring)
  exact (not_le_of_gt (Nat.mul_lt_mul_of_pos_right (by omega) hr)) hlimit

end OMA.MO387067

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_387067.main) := OMA.MO387067.disproof
