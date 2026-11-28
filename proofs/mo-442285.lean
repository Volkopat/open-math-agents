import OMAStatements.S_mo_442285
import Mathlib

/-!
# Cigler's Catalan convolution determinant and two proposed refinements

Source: Johann Cigler, MathOverflow 442285. Credit: @connoranderson.
Reference: https://mathoverflow.net/questions/442285

Theorem `catalan_determinant` proves the ordinary Catalan identity for all
k, n and m in the question. With h = k−1, the modified moment functional has
monic multiplier X^m S_h(X−2). The first h rows in remainder coordinates are
unchanged at even n and negated and reversed at odd n. The remaining m rows
pair around index kn+h. Their low-coefficient determinant contributes the
m-th power of the ratio of constant terms of S_(kn+h)(X−2) and S_h(X−2),
whose absolute value is n+1.

The monic-multiplier determinant, the coordinate-change lemma and portions of
the Jacobi action, Chebyshev product, row-reversal sign and truncated
coefficient arguments are adapted from The Omega Institute's TrureTuring
project, Apache License 2.0, revision c6adc5ebc6592e960b8eae4d9ac97ef3b07509d7.
Upstream modules are CiglerMotzkinColumnDeterminant, CiglerElevenReduction,
CiglerElevenMoments, CiglerElevenPolynomials and CiglerEleven.
https://github.com/The-Omega-Institute/trureturing/tree/c6adc5ebc6592e960b8eae4d9ac97ef3b07509d7/D5/S3/Combinatorics

The Narayana formula at k=2, n=m=1 and q=2 predicts −3 for a determinant
equal to −5. Han, arXiv:2512.12603, gives related formulas with q^k in the
q-integer. The last edit's leading coefficient also fails, already at k=1,
m=2. The four exact determinants 1, 5, 14, 30 give cubic leading coefficient
1/3, whereas the printed Bernoulli expression gives 1/6.
-/
/-! The general remainder and coordinate determinants below are adapted from
The Omega Institute, TrureTuring, revision c6adc5ebc6592e960b8eae4d9ac97ef3b07509d7,
CiglerMotzkinColumnDeterminant and CiglerElevenReduction, under Apache 2.0. -/
namespace OMA.S_mo_442285
noncomputable section
open Polynomial Finset Matrix
theorem multiplier_remainders {R : Type*} [CommRing R] [Nontrivial R]
    (p : ℕ → R[X]) (hp : ∀ i : ℕ, (p i).IsMonicOfDegree i)
    (ℓ : R[X] →ₗ[R] R)
    (ho : ∀ i j : ℕ, ℓ (p i * p j) = if i = j then 1 else 0)
    (g : R[X]) (h n : ℕ) (hg : g.IsMonicOfDegree h) :
    (Matrix.of fun i j : Fin n => ℓ (g * X ^ (i.val + j.val))).det =
      (-1 : R) ^ (n * h) *
        (Matrix.of fun i j : Fin h => ((p (n + i.val)) %ₘ g).coeff j.val).det := by
  classical
  have expand (f : R[X]) (b : ℕ) (hb : f.degree < b) :
      f = ∑ a : Fin b, C (f.coeff a.val) * X ^ a.val := by
    rw [Polynomial.sum_fin (fun a c => C c * X ^ a) (by simp) hb]
    exact f.sum_C_mul_X_pow_eq.symm
  have scalar (c : R) (f : R[X]) : ℓ (C c * f) = c * ℓ f := by
    simpa only [smul_eq_C_mul, smul_eq_mul] using ℓ.map_smul c f
  let total := h + n
  let P : Matrix (Fin total) (Fin total) R :=
    Matrix.of fun i j => (p i.val).coeff j.val
  let W : Matrix (Fin total) (Fin total) R :=
    Matrix.of fun i j => ℓ (X ^ i.val * p j.val)
  have p_degree (i : ℕ) : (p i).degree = i := by
    rw [degree_eq_natDegree (hp i).monic.ne_zero, (hp i).natDegree_eq]
  have inverse : P * W = 1 := by
    ext i j
    simp only [Matrix.mul_apply, P, W, Matrix.of_apply]
    have expansion := expand (p i.val) total (by rw [p_degree]; exact_mod_cast i.isLt)
    have pairing := congrArg (fun f : R[X] => ℓ (f * p j.val)) expansion
    simp only [sum_mul, map_sum, mul_assoc, scalar] at pairing
    rw [← pairing, ho]
    simp [Matrix.one_apply, Fin.ext_iff]
  have reverse_inverse : W * P = 1 := mul_eq_one_comm.mp inverse
  have P_det : P.det = 1 := by
    have triangular : P.IsLowerTriangular := by
      intro i j larger
      apply coeff_eq_zero_of_natDegree_lt
      rw [(hp i.val).natDegree_eq]
      exact larger
    rw [Matrix.det_of_isLowerTriangular P triangular]
    apply prod_eq_one
    intro i _
    change (p i.val).coeff i.val = 1
    simpa [(hp i.val).natDegree_eq] using (hp i.val).monic.coeff_natDegree
  let f : Fin total → R[X] := fun i =>
    if i.val < n then g * X ^ i.val else p (n + (i.val - n))
  have f_degree (i : Fin total) : (f i).degree < total := by
    dsimp only [f]
    split_ifs with top
    · rw [degree_mul_X_pow, degree_eq_natDegree hg.monic.ne_zero, hg.natDegree_eq]
      norm_cast
      dsimp only [total] at i ⊢
      omega
    · rw [p_degree]
      norm_cast
      dsimp only [total] at i ⊢
      omega
  let T : Matrix (Fin total) (Fin total) R := Matrix.of fun i j => (f i).coeff j.val
  let U := T * W
  have U_entry (i j : Fin total) : U i j = ℓ (f i * p j.val) := by
    dsimp only [U]
    simp only [Matrix.mul_apply, T, W, Matrix.of_apply]
    have pairing := congrArg (fun q : R[X] => ℓ (q * p j.val))
      (expand (f i) total (f_degree i))
    simp only [sum_mul, map_sum, mul_assoc, scalar] at pairing
    exact pairing.symm
  have U_det : U.det = T.det := by
    have product : U * P = T := by
      dsimp only [U]
      rw [Matrix.mul_assoc, reverse_inverse, Matrix.mul_one]
    have determinant := congrArg Matrix.det product
    simpa [Matrix.det_mul, P_det] using determinant
  let H : Matrix (Fin n) (Fin n) R :=
    Matrix.of fun i j => ℓ (g * X ^ (i.val + j.val))
  let Q : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => (p i.val).coeff j.val
  have Q_det : Q.det = 1 := by
    have triangular : Q.IsLowerTriangular := by
      intro i j larger
      apply coeff_eq_zero_of_natDegree_lt
      rw [(hp i.val).natDegree_eq]
      exact larger
    rw [Matrix.det_of_isLowerTriangular Q triangular]
    apply prod_eq_one
    intro i _
    change (p i.val).coeff i.val = 1
    simpa [(hp i.val).natDegree_eq] using (hp i.val).monic.coeff_natDegree
  let index : Fin n ⊕ Fin h ≃ Fin total :=
    (finSumFinEquiv : Fin n ⊕ Fin h ≃ Fin (n + h)).trans (finCongr (Nat.add_comm n h))
  let side : Matrix (Fin n) (Fin h) R :=
    Matrix.of fun i j => ℓ (g * X ^ i.val * p (n + j.val))
  have U_block : U.submatrix index index = Matrix.fromBlocks (H * Q.transpose) side 0 1 := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [Matrix.submatrix_apply, U_entry]
        have left_index : (index (Sum.inl i)).val = i.val := by simp [index]
        have right_index : (index (Sum.inl j)).val = j.val := by simp [index]
        simp only [f, left_index, i.isLt, if_true, right_index,
          Matrix.fromBlocks_apply₁₁, Matrix.mul_apply, H, Q,
          Matrix.transpose_apply, Matrix.of_apply]
        have pairing := congrArg (fun q : R[X] => ℓ (g * X ^ i.val * q))
          (expand (p j.val) n (by rw [p_degree]; exact_mod_cast j.isLt))
        simp only [mul_sum, map_sum] at pairing
        rw [pairing]
        apply sum_congr rfl
        intro a _
        rw [show g * X ^ i.val * (C ((p j.val).coeff a.val) * X ^ a.val) =
          C ((p j.val).coeff a.val) * (g * X ^ (i.val + a.val)) by rw [pow_add]; ring,
          scalar]
        ring
      | inr j =>
        simp [Matrix.submatrix_apply, U_entry, f, index, side, Matrix.fromBlocks,
          i.isLt, Nat.add_comm]
    | inr i =>
      cases j with
      | inl j =>
        have unequal : n + i.val ≠ j.val := by omega
        simp [Matrix.submatrix_apply, U_entry, f, index, Matrix.fromBlocks,
          ho, unequal]
      | inr j =>
        simp [Matrix.submatrix_apply, U_entry, f, index, Matrix.fromBlocks,
          ho, Matrix.one_apply, Fin.ext_iff, Nat.add_comm]
  have T_det : T.det = H.det := by
    rw [← U_det, ← Matrix.det_submatrix_equiv_self index U, U_block,
      Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_mul,
      Matrix.det_transpose, Q_det, mul_one]
  let basis : Fin total → R[X] := fun i =>
    if i.val < h then X ^ i.val else g * X ^ (i.val - h)
  let B : Matrix (Fin total) (Fin total) R :=
    Matrix.of fun i j => (basis i).coeff j.val
  have basis_monic (i : Fin total) : (basis i).IsMonicOfDegree i.val := by
    dsimp only [basis]
    split_ifs with first
    · simpa using (isMonicOfDegree_X (R := R)).pow i.val
    · have product := hg.mul ((isMonicOfDegree_X (R := R)).pow (i.val - h))
      simpa [Nat.add_sub_of_le (le_of_not_gt first)] using product
  have B_det : B.det = 1 := by
    have triangular : B.IsLowerTriangular := by
      intro i j larger
      change (basis i).coeff j.val = 0
      apply coeff_eq_zero_of_natDegree_lt
      rw [(basis_monic i).natDegree_eq]
      exact larger
    rw [Matrix.det_of_isLowerTriangular B triangular]
    apply prod_eq_one
    intro i _
    change (basis i).coeff i.val = 1
    simpa [(basis_monic i).natDegree_eq] using (basis_monic i).monic.coeff_natDegree
  let Cmat : Matrix (Fin total) (Fin total) R := Matrix.of fun i j =>
    if i.val < n then (if j.val = h + i.val then 1 else 0)
    else if j.val < h then ((p (n + (i.val - n))) %ₘ g).coeff j.val
    else ((p (n + (i.val - n))) /ₘ g).coeff (j.val - h)
  have reconstruction (i : Fin total) :
      f i = ∑ a : Fin total, C (Cmat i a) * basis a := by
    by_cases top : i.val < n
    · let pivot : Fin total := ⟨h + i.val, by dsimp [total]; omega⟩
      rw [sum_eq_single pivot]
      · simp [Cmat, top, pivot, basis, f]
      · intro a _ different
        have unequal : a.val ≠ h + i.val := by
          intro equal
          exact different (Fin.ext equal)
        simp [Cmat, top, unequal]
      · simp
    · let q := p (n + (i.val - n))
      have remainder_degree : (q %ₘ g).degree < h := by
        simpa [degree_eq_natDegree hg.monic.ne_zero, hg.natDegree_eq] using
          degree_modByMonic_lt q hg.monic
      have quotient_degree : (q /ₘ g).degree < n := by
        by_cases qzero : q /ₘ g = 0
        · simp [qzero]
        · have enough : h ≤ n + (i.val - n) := by
            have lower := not_lt.mp ((divByMonic_eq_zero_iff hg.monic).not.mp qzero)
            rw [degree_eq_natDegree hg.monic.ne_zero, hg.natDegree_eq,
              show q.degree = (n + (i.val - n) : ℕ) by exact p_degree _] at lower
            exact_mod_cast lower
          rw [degree_eq_natDegree qzero, natDegree_divByMonic q hg.monic,
            hg.natDegree_eq, (hp (n + (i.val - n))).natDegree_eq]
          norm_cast
          dsimp only [total] at i
          omega
      rw [Fin.sum_univ_add]
      have first_part :
          (∑ a : Fin h, C (Cmat i (Fin.castAdd n a)) * basis (Fin.castAdd n a)) =
          q %ₘ g := by
        simpa [Cmat, top, basis, q] using (expand _ h remainder_degree).symm
      have second_part :
          (∑ a : Fin n, C (Cmat i (Fin.natAdd h a)) * basis (Fin.natAdd h a)) =
          g * (q /ₘ g) := by
        simp only [Cmat, Matrix.of_apply, top, if_false, Fin.val_natAdd,
          show ∀ a : Fin n, ¬h + a.val < h by intro a; omega,
          if_false, Nat.add_sub_cancel_left, basis]
        change (∑ a : Fin n, C ((q /ₘ g).coeff a.val) * (g * X ^ a.val)) = _
        calc
          _ = ∑ a : Fin n, g * (C ((q /ₘ g).coeff a.val) * X ^ a.val) := by
            apply sum_congr rfl
            intro a _
            ring
          _ = g * (∑ a : Fin n, C ((q /ₘ g).coeff a.val) * X ^ a.val) :=
            (mul_sum _ _ _).symm
          _ = g * (q /ₘ g) := congrArg (g * ·) (expand _ n quotient_degree).symm
      rw [first_part, second_part, modByMonic_add_div]
      simp [f, top, q]
  have product : Cmat * B = T := by
    ext i j
    have coefficient := congrArg (fun q : R[X] => q.coeff j.val) (reconstruction i)
    simp only [finsetSum_coeff, coeff_C_mul] at coefficient
    simpa only [Matrix.mul_apply, T, B, Matrix.of_apply] using coefficient.symm
  have Cmat_det : Cmat.det = T.det := by
    have determinant := congrArg Matrix.det product
    simpa [Matrix.det_mul, B_det] using determinant
  have delete : ∀ count width : ℕ, ∀ bottom : ℕ → ℕ → R,
      (Matrix.of fun i j : Fin (width + count) =>
        if i.val < count then (if j.val = width + i.val then 1 else 0)
        else bottom (i.val - count) j.val).det =
        (-1 : R) ^ (count * width) *
          (Matrix.of fun i j : Fin width => bottom i.val j.val).det := by
    intro count
    induction count with
    | zero => intro width bottom; simp
    | succ count ih =>
      intro width bottom
      let A : Matrix (Fin (width + count + 1)) (Fin (width + count + 1)) R :=
        Matrix.of fun i j =>
          if i.val < count + 1 then (if j.val = width + i.val then 1 else 0)
          else bottom (i.val - (count + 1)) j.val
      let pivot : Fin (width + count + 1) := ⟨width, by omega⟩
      have expansion : A.det = (-1 : R) ^ width *
          (A.submatrix Fin.succ pivot.succAbove).det := by
        rw [Matrix.det_succ_row_zero, sum_eq_single pivot]
        · simp [A, pivot]
        · intro j _ different
          have unequal : j.val ≠ width := by
            intro equal
            exact different (Fin.ext equal)
          simp [A, unequal]
        · simp
      have minor : A.submatrix Fin.succ pivot.succAbove =
          Matrix.of (fun i j : Fin (width + count) =>
            if i.val < count then (if j.val = width + i.val then 1 else 0)
            else bottom (i.val - count) (if j.val < width then j.val else j.val + 1)) := by
        ext i j
        have hole : (pivot.succAbove j).val =
            if j.val < width then j.val else j.val + 1 := by
          by_cases before : j.val < width
          · rw [Fin.succAbove_of_castSucc_lt pivot j (by exact before)]
            simp [before]
          · rw [Fin.succAbove_of_le_castSucc pivot j (by exact le_of_not_gt before)]
            simp [before]
        simp only [Matrix.submatrix_apply, A, Matrix.of_apply, Fin.val_succ, hole]
        have test : i.val + 1 < count + 1 ↔ i.val < count := by omega
        rw [if_congr test rfl rfl]
        by_cases top : i.val < count
        · simp only [top, if_true]
          have column_test :
              (if j.val < width then j.val else j.val + 1) = width + (i.val + 1) ↔
                j.val = width + i.val := by split_ifs <;> omega
          rw [if_congr column_test rfl rfl]
        · simp only [top, if_false]
          congr 1
          omega
      have bottom_fixed :
          (Matrix.of fun i j : Fin width =>
            bottom i.val (if j.val < width then j.val else j.val + 1)) =
          Matrix.of (fun i j : Fin width => bottom i.val j.val) := by
        ext i j
        simp
      change A.det = _
      rw [expansion, minor, ih width
        (fun i j => bottom i (if j < width then j else j + 1)), bottom_fixed,
        ← mul_assoc, ← pow_add]
      congr 1
      ring
  rw [← T_det, ← Cmat_det]
  have reduction := delete n h (fun i j =>
    if j < h then ((p (n + i)) %ₘ g).coeff j
    else ((p (n + i)) /ₘ g).coeff (j - h))
  simpa only [Cmat, total, Fin.isLt, if_true] using reduction


theorem coordinate_change (k d : ℕ) (v : ℚ[X])
    (hv : v.Monic) (hdeg : v.natDegree = k) (Q : Fin (k + d) → ℚ[X]) :
    det (Matrix.of fun i j : Fin (k + d) =>
      if j.val < k then (Q i %ₘ v).coeff j.val else (Q i).coeff (j.val - k)) =
    v.coeff 0 ^ d *
      det (Matrix.of fun i j : Fin (k + d) => (Q i %ₘ (X ^ d * v)).coeff j.val) := by
  classical
  by_cases hz : k + d = 0
  · have hk : k = 0 := by omega
    have hd : d = 0 := by omega
    subst k
    subst d
    simp
  let u : ℚ[X] := X ^ d * v
  have hu : u.Monic := (monic_X_pow d).mul hv
  have hdu : u.natDegree = k + d := by
    dsimp [u]
    rw [(monic_X_pow d).natDegree_mul hv, natDegree_X_pow, hdeg, Nat.add_comm]
  have hune : u ≠ 1 := by
    intro h
    have he := congrArg natDegree h
    rw [hdu, natDegree_one] at he
    omega
  let C : Fin (k + d) → ℚ[X] →ₗ[ℚ] ℚ := fun j =>
    if j.val < k then (lcoeff ℚ j.val).comp (modByMonicHom v)
    else lcoeff ℚ (j.val - k)
  let E : Matrix (Fin (k + d)) (Fin (k + d)) ℚ :=
    Matrix.of fun i j => C j (X ^ i.val)
  let R : Matrix (Fin (k + d)) (Fin (k + d)) ℚ :=
    Matrix.of fun i j => (Q i %ₘ u).coeff j.val
  have expand (w : ℚ[X]) (hw : w.natDegree < k + d) :
      w = ∑ a : Fin (k + d), w.coeff a.val • X ^ a.val := by
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => w.coeff a • (X : ℚ[X]) ^ a)]
    simpa only [smul_eq_C_mul] using w.as_sum_range_C_mul_X_pow' hw
  have preserves (w : ℚ[X]) (j : Fin (k + d)) : C j (w %ₘ u) = C j w := by
    dsimp [C]
    split_ifs with hj
    · change ((w %ₘ u) %ₘ v).coeff j.val = (w %ₘ v).coeff j.val
      have hdiv : v ∣ u * (w /ₘ u) := by
        refine ⟨X ^ d * (w /ₘ u), ?_⟩
        dsimp [u]
        ring
      rw [modByMonic_eq_sub_mul_div w u, sub_modByMonic,
        (modByMonic_eq_zero_iff_dvd hv).mpr hdiv, sub_zero]
    · change (w %ₘ u).coeff (j.val - k) = w.coeff (j.val - k)
      rw [modByMonic_eq_sub_mul_div, coeff_sub]
      have hr : u * (w /ₘ u) = X ^ d * (v * (w /ₘ u)) := by dsimp [u]; ring
      rw [hr, coeff_X_pow_mul', if_neg (by have := j.isLt; omega), sub_zero]
  have factor : (Matrix.of fun i j : Fin (k + d) => C j (Q i)) = R * E := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, R, E]
    rw [← preserves (Q i) j]
    conv_lhs =>
      rw [expand (Q i %ₘ u) (by rw [← hdu]; exact natDegree_modByMonic_lt _ hu hune),
        map_sum]
    simp only [map_smul, smul_eq_mul]
  let W : Fin (k + d) → ℚ[X] := fun i =>
    if i.val < k then X ^ i.val else v * X ^ (i.val - k)
  have hW (i : Fin (k + d)) : (W i).Monic ∧ (W i).natDegree = i.val := by
    dsimp [W]
    split_ifs with hi
    · exact ⟨monic_X_pow _, natDegree_X_pow _⟩
    · refine ⟨hv.mul (monic_X_pow _), ?_⟩
      rw [hv.natDegree_mul (monic_X_pow _), hdeg, natDegree_X_pow]
      omega
  let H : Matrix (Fin (k + d)) (Fin (k + d)) ℚ :=
    Matrix.of fun i j => (W i).coeff j.val
  have hHdet : H.det = 1 := by
    rw [← det_transpose]
    exact det_matrixOfPolynomials W (fun i => (hW i).2) (fun i => (hW i).1)
  have basis_factor : H * E = Matrix.of (fun i j => C j (W i)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, H, E]
    conv_rhs => rw [expand (W i) (by rw [(hW i).2]; exact i.isLt), map_sum]
    simp only [map_smul, smul_eq_mul]
  let U : Matrix (Fin d) (Fin d) ℚ := Matrix.of fun i j => (v * X ^ i.val).coeff j.val
  have hU : U.IsUpperTriangular := by
    intro i j hij
    simp only [U, Matrix.of_apply, coeff_mul_X_pow',
      if_neg (show ¬ i.val ≤ j.val by exact not_le_of_gt hij)]
  have hUdet : U.det = v.coeff 0 ^ d := by
    rw [det_of_isUpperTriangular hU]
    simp [U, coeff_mul_X_pow']
  let e : Fin k ⊕ Fin d ≃ Fin (k + d) := @finSumFinEquiv k d
  have rem_X (i : Fin k) : (X ^ i.val : ℚ[X]) %ₘ v = X ^ i.val := by
    apply (modByMonic_eq_self_iff hv).mpr
    rw [degree_X_pow, degree_eq_natDegree hv.ne_zero, hdeg]
    exact_mod_cast i.isLt
  have block : (Matrix.of (fun i j => C j (W i))).submatrix e e =
      fromBlocks (1 : Matrix (Fin k) (Fin k) ℚ)
        (Matrix.of fun i : Fin k => fun j : Fin d => (X ^ i.val : ℚ[X]).coeff j.val)
        0 U := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e,
          i.isLt, j.isLt, rem_X, coeff_X_pow, Matrix.one_apply, Fin.ext_iff, eq_comm]
      | inr j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, i.isLt]
    | inr i =>
      cases j with
      | inl j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, j.isLt,
          self_mul_modByMonic hv]
      | inr j =>
        simp [Matrix.submatrix, Matrix.fromBlocks, Matrix.of_apply, C, W, e, U]
  have hEdet : E.det = v.coeff 0 ^ d := by
    have hh := congrArg Matrix.det basis_factor
    rw [det_mul, hHdet, one_mul,
      ← det_submatrix_equiv_self e (Matrix.of fun i j => C j (W i)), block,
      det_fromBlocks_zero₂₁, det_one, one_mul, hUdet] at hh
    exact hh
  have form : (Matrix.of fun i j : Fin (k + d) =>
      if j.val < k then (Q i %ₘ v).coeff j.val else (Q i).coeff (j.val - k)) =
      Matrix.of (fun i j => C j (Q i)) := by
    ext i j
    simp only [Matrix.of_apply, C]
    split_ifs <;> rfl
  rw [form, factor, det_mul, hEdet, mul_comm]



end
end OMA.S_mo_442285

namespace OMA.S_mo_442285
noncomputable section
open Polynomial Matrix

def S (j : ℤ) : ℚ[X] := (Chebyshev.S ℚ j).comp (X - 2)
def T (j : ℕ) : ℚ[X] := (Chebyshev.C ℚ (j : ℤ)).comp (X - 2)
def P (j : ℕ) : ℚ[X] := S (j : ℤ)

@[simp] theorem P_zero : P 0 = 1 := by simp [P,S]
@[simp] theorem P_one : P 1 = X-2 := by simp [P,S,Chebyshev.S_one]
theorem P_next (j : ℕ) : P (j+2) = (X-2)*P (j+1) - P j := by
  simp only [P,S,Nat.cast_add,Nat.cast_ofNat,Chebyshev.S_add_two,sub_comp,mul_comp,X_comp,
    Nat.cast_one]

theorem P_deg (j : ℕ) : (P j).IsMonicOfDegree j := by
  have hlin : (X - 2 : ℚ[X]).IsMonicOfDegree 1 :=
    by
      rw [← Polynomial.C_ofNat (R := ℚ) (n := 2)]
      exact ⟨natDegree_X_sub_C _, monic_X_sub_C _⟩
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hlin
  | more j h₀ h₁ =>
    rw [P_next]
    have h := hlin.mul h₁
    rw [show 1+(j+1)=j+2 by omega] at h
    exact h.sub (by rw [h₀.natDegree_eq]; omega)

theorem P_endpoint (j : ℕ) : (P j).coeff 0 = (-1 : ℚ)^j*(j+1 : ℕ) := by
  rw [coeff_zero_eq_eval_zero, P,S,eval_comp]
  simp [Chebyshev.S_eval_neg_two]

private theorem cheb_product (n : ℤ) (m : ℕ) :
      Chebyshev.C ℚ (m : ℤ) * Chebyshev.S ℚ n =
        Chebyshev.S ℚ (n + m) + Chebyshev.S ℚ (n - m) := by
    induction m using Nat.twoStepInduction with
    | zero => simp; ring
    | one =>
      have hh := Chebyshev.S_add_one ℚ n
      simp only [Nat.cast_one, Chebyshev.C_one]
      linear_combination -hh
    | more m ih₀ ih₁ =>
      have hc := Chebyshev.C_add_two ℚ (m : ℤ)
      have hf := Chebyshev.S_add_two ℚ (n + m)
      have hb := Chebyshev.S_sub_two ℚ (n - m)
      simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at ih₁ ⊢
      have hi₁ : n + ((m : ℤ) + 1) = n + m + 1 := by omega
      have hi₂ : n - ((m : ℤ) + 1) = n - m - 1 := by omega
      have hi₃ : n + ((m : ℤ) + 2) = n + m + 2 := by omega
      have hi₄ : n - ((m : ℤ) + 2) = n - m - 2 := by omega
      rw [hi₁, hi₂] at ih₁
      rw [hi₃, hi₄]
      linear_combination Chebyshev.S ℚ n * hc + X * ih₁ - ih₀ - hf - hb

theorem pair (a : ℤ) (j : ℕ) : S (a+j) + S (a-j) = T j * S a := by
  have h := congrArg (fun f : ℚ[X] => f.comp (X-2)) (cheb_product a j)
  simpa [S,T,mul_comp,add_comp] using h.symm

def G (j : ℕ) : ℚ[X] := if j=0 then 1 else T j

theorem G_deg (j : ℕ) : (G j).IsMonicOfDegree j := by
  cases j with
  | zero => simp [G]
  | succ j =>
    have h := Chebyshev.C_eq_S_sub_X_mul_S ℚ ((j : ℤ)+1)
    have h' := Chebyshev.S_add_one ℚ (j : ℤ)
    simp only [add_sub_cancel_right] at h
    have e : Chebyshev.C ℚ ((j : ℤ)+1) = Chebyshev.S ℚ ((j : ℤ)+1) -
        Chebyshev.S ℚ ((j : ℤ)-1) := by linear_combination h + h'
    change (G (j+1)).IsMonicOfDegree (j+1)
    rw [G,if_neg (by omega),T,Nat.cast_add,Nat.cast_one,e,sub_comp]
    apply (P_deg (j+1)).sub
    cases j with
    | zero => simp [Chebyshev.S_neg_one]
    | succ j =>
      change (S (((j+1 : ℕ) : ℤ)-1)).natDegree < j+1+1
      rw [show ((j+1 : ℕ) : ℤ)-1 = (j : ℤ) by omega]
      change (P j).natDegree < _
      rw [(P_deg j).natDegree_eq]
      omega

theorem P_period (h j : ℕ) :
    P h ∣ P (2*(h+1)+j) - P j := by
  have hpair := pair (h : ℤ) (h+j+2)
  have e₁ : (h : ℤ) + (h+j+2 : ℕ) = ((2*(h+1)+j : ℕ) : ℤ) := by omega
  have e₂ : (h : ℤ) - (h+j+2 : ℕ) = -(j : ℤ)-2 := by omega
  have neg : S (-(j:ℤ)-2) = -P j := by simp [S,P,Chebyshev.S_neg_sub_two]
  rw [e₁,e₂,neg] at hpair
  refine ⟨T (h+j+2), ?_⟩
  simpa only [sub_eq_add_neg,P,mul_comm] using hpair

theorem P_rem_period (h t j : ℕ) :
    P ((h+1)*(2*t)+j) %ₘ P h = P j %ₘ P h := by
  induction t with
  | zero => simp
  | succ t ih =>
    exact (modByMonic_eq_of_dvd_sub (P_deg h).monic (by
      rw [show (h+1)*(2*(t+1))+j = 2*(h+1)+((h+1)*(2*t)+j) by ring]
      exact P_period h _)).trans ih

theorem P_reflect (h j : ℕ) (hj : j<h) :
    P ((h+1)+j) %ₘ P h = -(P (h-1-j) %ₘ P h) := by
  have he := pair (h : ℤ) (j+1)
  have e₁ : (h : ℤ)+(j+1 : ℕ) = (h+1+j : ℕ) := by omega
  have e₂ : (h : ℤ)-(j+1 : ℕ) = (h-1-j : ℕ) := by omega
  rw [e₁,e₂] at he
  have hz := congrArg (fun f : ℚ[X] => f %ₘ P h) he
  change _ = (T (j+1) * P h) %ₘ P h at hz
  rw [add_modByMonic,mul_comm, self_mul_modByMonic (P_deg h).monic] at hz
  exact eq_neg_of_add_eq_zero_left hz

theorem P_multiple_rem (h n : ℕ) : P ((h+1)*n+h) %ₘ P h = 0 := by
  rcases Nat.even_or_odd n with ⟨t,ht⟩ | ⟨t,ht⟩
  · rw [show n=2*t by omega,P_rem_period,modByMonic_self (P_deg h).monic]
  · have he := pair (h : ℤ) (h+1)
    rw [show (h : ℤ)+(h+1 : ℕ) = (h+1+h : ℕ) by omega,
      show (h : ℤ)-(h+1 : ℕ) = -1 by omega] at he
    have h0 : S (-1) = 0 := by simp [S]
    rw [h0,add_zero] at he
    rw [show (h+1)*n+h = (h+1)*(2*t)+(h+1+h) by rw [show n=2*t+1 by omega]; ring,
      P_rem_period]
    change S ((h+1+h : ℕ) : ℤ) %ₘ P h = 0
    rw [he,mul_comm]
    exact self_mul_modByMonic (P_deg h).monic

end
end OMA.S_mo_442285

namespace OMA.S_mo_442285
noncomputable section
open Polynomial
/-! The Jacobi action proof adapts the odd-power dictionary of TrureTuring,
CiglerElevenMoments. Here the boundary diagonal is 2 and the Pascal row is odd. -/
theorem moment_dictionary : ∃ moment : ℚ[X] →ₗ[ℚ] ℚ,
    (∀ a b : ℕ, moment (P a * P b) = if a=b then 1 else 0) ∧
    (∀ t h : ℕ, moment (X^t * P h) = catalanConvolution (h+1) (t+1)) := by
  let jacobi : Module.End ℚ (ℕ → ℚ) := {
    toFun := fun v => fun
      | 0 => 2 * v 0 + v 1
      | k + 1 => v k + 2 * v (k + 1) + v (k + 2)
    map_add' := by
      intro v w
      ext k
      cases k <;> simp <;> ring
    map_smul' := by
      intro c v
      ext k
      cases k <;> simp <;> ring }
  let moment : ℚ[X] →ₗ[ℚ] ℚ := {
    toFun := fun f => (aeval jacobi f) (Pi.single 0 1) 0
    map_add' := by intros; simp
    map_smul' := by intros; simp }
  have row (n : ℕ) (v : ℕ → ℚ) : (aeval jacobi (P n)) v 0 = v n := by
    induction n using Nat.twoStepInduction generalizing v with
    | zero => simp [P_zero]
    | one =>
      rw [P_one,map_sub,aeval_X,show aeval jacobi (2 : ℚ[X]) = (2 : Module.End ℚ (ℕ → ℚ)) from aeval_natCast jacobi 2]
      simp [jacobi, LinearMap.sub_apply, Module.End.ofNat_apply, Pi.sub_apply]
    | more n ih₀ ih₁ =>
      rw [P_next]
      have hc : aeval jacobi ((X - 2) * P (n + 1)) =
          aeval jacobi (P (n + 1)) * (jacobi - 2) := by
        rw [mul_comm, map_mul]
        rw [map_sub, aeval_X]
        congr 2
        exact aeval_natCast jacobi 2
      rw [map_sub, hc]
      change (aeval jacobi (P (n + 1))) ((jacobi - 2) v) 0 -
        (aeval jacobi (P n)) v 0 = v (n + 2)
      rw [ih₁, ih₀]
      simp [jacobi, LinearMap.sub_apply, Pi.sub_apply]
      ring
  have jzero : jacobi (Pi.single 0 1) = 2 • Pi.single 0 1 + Pi.single 1 1 := by
    ext l
    cases l with
    | zero => simp [jacobi]
    | succ l =>
      simp [jacobi, Pi.single_apply]
  have jsucc (n : ℕ) : jacobi (Pi.single (n + 1) 1) =
      Pi.single n 1 + 2 • Pi.single (n + 1) 1 + Pi.single (n + 2) 1 := by
    ext l
    cases l with
    | zero =>
      simp [jacobi, Pi.single_apply, eq_comm]
    | succ l =>
      simp only [jacobi, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Pi.smul_apply,
        Pi.single_apply]
      split_ifs <;> simp_all
      all_goals omega
  have column (n : ℕ) : (aeval jacobi (P n)) (Pi.single 0 1) = Pi.single n 1 := by
    induction n using Nat.twoStepInduction with
    | zero => simp [P_zero]
    | one =>
      simp only [P_one, map_sub, aeval_X, map_ofNat, LinearMap.sub_apply, jzero, Module.End.ofNat_apply]
      change 2 • Pi.single 0 1 + Pi.single 1 1 - (2 : ℕ) • Pi.single 0 1 = _
      abel
    | more n ih₀ ih₁ =>
      rw [P_next]
      simp only [map_sub, map_mul, aeval_X, map_ofNat, LinearMap.sub_apply,
        Module.End.mul_apply, ih₀, ih₁]
      rw [jsucc, Module.End.ofNat_apply]
      change Pi.single n 1 + 2 • Pi.single (n + 1) 1 + Pi.single (n + 2) 1 -
        2 • Pi.single (n + 1) 1 - Pi.single n 1 = _
      abel

  let A (t k : ℕ) : ℚ :=
    ((2*t+1).choose (t+k+1) : ℚ) - ((2*t+1).choose (t+k+2) : ℚ)
  have dict (t h : ℕ) : A t h = catalanConvolution (h+1) (t+1) := by
    simp only [catalanConvolution, Nat.add_one_ne_zero, if_false]
    dsimp [A]
    rw [show 2*(t+1)-1=2*t+1 by omega,
      show t+1+h=t+h+1 by omega,show t+1+(h+1)=t+h+2 by omega]
  have pascal₂ (a b : ℕ) : ((a + 2).choose (b + 2) : ℚ) =
      (a.choose b : ℚ) + 2 * (a.choose (b + 1) : ℚ) + (a.choose (b + 2) : ℚ) := by
    rw [show a + 2 = (a + 1) + 1 by omega,
      show b + 2 = (b + 1) + 1 by omega, Nat.choose_succ_succ',
      Nat.choose_succ_succ', Nat.choose_succ_succ']
    push_cast
    ring

  have azero (k : ℕ) : A 0 k = if k=0 then 1 else 0 := by
    cases k with
    | zero => norm_num [A,Nat.choose]
    | succ k =>
      simp [A,Nat.choose_eq_zero_of_lt (show 1<k+1+1 by omega),
        Nat.choose_eq_zero_of_lt (show 1<k+1+2 by omega)]
  have asucc (t k : ℕ) : A (t+1) (k+1) = A t k + 2*A t (k+1) + A t (k+2) := by
    dsimp [A]
    rw [show 2*(t+1)+1 = (2*t+1)+2 by omega,
      show t+1+(k+1)+1=(t+k+1)+2 by omega,
      show t+1+(k+1)+2=(t+k+2)+2 by omega,pascal₂,pascal₂]
    simp only [show t+(k+1)+1=t+k+2 by omega,show t+(k+1)+2=t+k+3 by omega,
      show t+(k+2)+1=t+k+3 by omega,show t+(k+2)+2=t+k+4 by omega]
    ring
  have aboundary (t : ℕ) : A (t+1) 0 = 2*A t 0 + A t 1 := by
    have hs := Nat.choose_symm (n:=2*t+1) (k:=t+1) (by omega)
    rw [show 2*t+1-(t+1)=t by omega] at hs
    dsimp [A]
    rw [show 2*(t+1)+1=(2*t+1)+2 by omega,
      show t+1+1=t+2 by omega,pascal₂,pascal₂,hs]
    ring
  have powers (t k : ℕ) : (jacobi ^ t) (Pi.single 0 1) k = A t k := by
    induction t generalizing k with
    | zero => simp [azero, Pi.single_apply]
    | succ t ih =>
      rw [pow_succ']
      change jacobi ((jacobi ^ t) (Pi.single 0 1)) k = _
      cases k with
      | zero =>
        change 2 * (jacobi ^ t) (Pi.single 0 1) 0 +
          (jacobi ^ t) (Pi.single 0 1) 1 = _
        rw [ih, ih]
        exact (aboundary t).symm
      | succ k =>
        change (jacobi ^ t) (Pi.single 0 1) k +
          2 * (jacobi ^ t) (Pi.single 0 1) (k + 1) +
          (jacobi ^ t) (Pi.single 0 1) (k + 2) = _
        rw [ih, ih, ih]
        exact (asucc t k).symm
  refine ⟨moment, ?_, ?_⟩
  · intro a b
    change (aeval jacobi (P a * P b)) (Pi.single 0 1) 0 = _
    rw [map_mul, Module.End.mul_apply, row, column]
    simp [Pi.single_apply]
  · intro t k
    change (aeval jacobi (X ^ t * P k)) (Pi.single 0 1) 0 = _
    rw [mul_comm, map_mul, Module.End.mul_apply, row, map_pow, aeval_X, powers, dict]


end
end OMA.S_mo_442285

namespace OMA.S_mo_442285
noncomputable section
open Matrix Polynomial

private theorem reverse_det (a : ℕ) :
      det (Matrix.of fun i j : Fin a => if i.val + j.val + 1 = a then (1 : ℚ) else 0) =
        (-1) ^ a.choose 2 := by
    induction a with
    | zero => simp
    | succ a ih =>
      rw [det_succ_column_zero]
      rw [Finset.sum_eq_single (Fin.last a)]
      · have minor :
            (Matrix.of fun i j : Fin (a + 1) =>
              if i.val + j.val + 1 = a + 1 then (1 : ℚ) else 0).submatrix
                (Fin.last a).succAbove Fin.succ =
            Matrix.of (fun i j : Fin a => if i.val + j.val + 1 = a then 1 else 0) := by
          ext i j
          simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_last,
            Fin.val_castSucc, Fin.val_succ]
          have he : i.val + (j.val + 1) + 1 = a + 1 ↔
              i.val + j.val + 1 = a := by omega
          simp only [he]
        simp only [Matrix.of_apply, Fin.val_last, Fin.val_zero, Nat.add_zero,
          mul_one, minor, ih, ite_true]
        rw [Nat.choose_succ_succ', Nat.choose_one_right, pow_add]
      · intro i _ hi
        have hv : i.val ≠ a := by intro hv; apply hi; exact Fin.ext hv
        simp [Matrix.of_apply, hv]
      · simp
private theorem reverse_sign (a : ℕ) : (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin a)) : ℚ) =
      (-1) ^ a.choose 2 := by
    have hrev : (1 : Matrix (Fin a) (Fin a) ℚ).submatrix Fin.revPerm id =
        Matrix.of (fun i j : Fin a => if i.val + j.val + 1 = a then 1 else 0) := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.one_apply, Fin.revPerm_apply, id_eq,
        Matrix.of_apply]
      have he : i.rev = j ↔ i.val + j.val + 1 = a := by
        rw [Fin.ext_iff, Fin.val_rev]
        have := i.isLt
        have := j.isLt
        omega
      simp only [he]
    have he := det_permute (Fin.revPerm : Equiv.Perm (Fin a)) (1 : Matrix (Fin a) (Fin a) ℚ)
    rw [hrev, reverse_det, det_one, mul_one] at he
    exact he.symm

private theorem prefix_det (h n : ℕ) :
    (Matrix.of fun i j : Fin h => (P ((h+1)*n+i.val) %ₘ P h).coeff j.val).det =
      (-1 : ℚ)^((h+1).choose 2 * n) := by
  classical
  let B := Matrix.of fun i j : Fin h => (P i.val).coeff j.val
  have hd : B.det = 1 := by
    rw [← det_transpose]
    exact det_matrixOfPolynomials (fun i : Fin h => P i.val)
      (fun i => (P_deg i.val).natDegree_eq) (fun i => (P_deg i.val).monic)
  have small (i : Fin h) : P i.val %ₘ P h = P i.val := by
    apply (modByMonic_eq_self_iff (P_deg h).monic).mpr
    exact degree_lt_degree (by rw [(P_deg i.val).natDegree_eq,(P_deg h).natDegree_eq]; exact i.isLt)
  have evenpow (t : ℕ) : (-1 : ℚ)^((h+1).choose 2*(2*t))=1 := by
    rw [show (h+1).choose 2*(2*t) = 2*((h+1).choose 2*t) by ring, pow_mul]
    norm_num
  rcases Nat.even_or_odd n with ⟨t,ht⟩ | ⟨t,ht⟩
  · rw [show n=2*t by omega,evenpow]
    simpa only [P_rem_period, small] using hd
  · have form : (Matrix.of fun i j : Fin h => (P ((h+1)*n+i.val) %ₘ P h).coeff j.val) =
        -B.submatrix Fin.revPerm id := by
      ext i j
      simp only [Matrix.of_apply,Matrix.neg_apply,Matrix.submatrix_apply,Fin.revPerm_apply,id_eq,B]
      rw [show (h+1)*n+i.val = (h+1)*(2*t)+(h+1+i.val) by rw [ht]; ring,
        P_rem_period,P_reflect h i.val i.isLt]
      rw [show h-1-i.val=i.rev.val by rw [Fin.val_rev]; omega]
      rw [small,coeff_neg]
    rw [form,det_neg,Fintype.card_fin,det_permute,reverse_sign,hd,mul_one,
      ht, Nat.mul_add, pow_add, evenpow,one_mul,Nat.mul_one,Nat.choose_succ_succ',Nat.choose_one_right,
      pow_add]

private theorem coefficient_det (m : ℕ) (F : ℚ[X]) :
    (Matrix.of fun i j : Fin m => (F * G i.val).coeff j.val).det = F.coeff 0 ^ m := by
  classical
  let M := Matrix.of fun i j : Fin m => (G i.val).coeff j.val
  let U := Matrix.of fun i j : Fin m => if i.val ≤ j.val then F.coeff (j.val-i.val) else 0
  have hd : M.det = 1 := by
    rw [← det_transpose]
    exact det_matrixOfPolynomials (fun i : Fin m => G i.val)
      (fun i => (G_deg i.val).natDegree_eq) (fun i => (G_deg i.val).monic)
  have hu : U.IsUpperTriangular := by
    intro i j hij
    exact if_neg (not_le_of_gt hij)
  have hdu : U.det = F.coeff 0 ^ m := by
    rw [det_of_isUpperTriangular hu]
    simp [U]
  have factor : (Matrix.of fun i j : Fin m => (F * G i.val).coeff j.val) = M * U := by
    ext i j
    have hexp : G i.val = ∑ a : Fin m, (G i.val).coeff a.val • X^a.val := by
      rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => (G i.val).coeff a • (X : ℚ[X])^a)]
      simpa only [smul_eq_C_mul] using
        (G i.val).as_sum_range_C_mul_X_pow' (by rw [(G_deg i.val).natDegree_eq]; exact i.isLt)
    simp only [M,U,Matrix.of_apply,Matrix.mul_apply]
    conv_lhs => rw [hexp, Finset.mul_sum, finsetSum_coeff]
    simp only [mul_smul_comm, coeff_smul, smul_eq_mul, coeff_mul_X_pow', mul_ite, mul_zero]
  rw [factor,det_mul,hd,one_mul,hdu]

set_option maxHeartbeats 1200000 in
theorem mixed_residue (h n m : ℕ) (hm : m ≤ h+1) :
    (Matrix.of fun i j : Fin (h+m) => if j.val<h then
      (P ((h+1)*n+i.val) %ₘ P h).coeff j.val else
      (P ((h+1)*n+i.val)).coeff (j.val-h)).det =
      (-1 : ℚ)^((h+1).choose 2*n) * (P ((h+1)*n+h)).coeff 0 ^ m := by
  classical
  let N := (h+1)*n
  let F := P (N+h)
  let L (j : ℕ) : ℚ[X] →ₗ[ℚ] ℚ := if j<h then (lcoeff ℚ j).comp (modByMonicHom (P h))
    else lcoeff ℚ (j-h)
  let M := Matrix.of fun i j : Fin (h+m) => L j.val (P (N+i.val))
  let U := Matrix.of fun i j : Fin h => L j.val (P (N+i.val))
  let V := Matrix.of fun i : Fin h => fun j : Fin m => L (h+j.val) (P (N+i.val))
  let W := Matrix.of fun i : Fin m => fun j : Fin h => L j.val (P (N+(h+i.val)))
  let D := Matrix.of fun i j : Fin m => L (h+j.val) (P (N+(h+i.val)))
  let E := Matrix.of fun i : Fin m => fun j : Fin h =>
    if i.val ≠ 0 ∧ j.val=h-i.val then (1 : ℚ) else 0
  let H := Matrix.of fun i j : Fin m => (F * G i.val).coeff j.val
  let e : Fin h ⊕ Fin m ≃ Fin (h+m) := finSumFinEquiv
  have block : M.submatrix e e = fromBlocks U V W D := by
    ext i j
    cases i <;> cases j <;> simp [M,U,V,W,D,e,submatrix,fromBlocks]
  have sum_row {s : Type} (C : s → ℚ[X] →ₗ[ℚ] ℚ) (i : Fin m) (j : s) :
      (E * (Matrix.of fun l : Fin h => fun a : s => C a (P (N+l.val)))) i j +
        C j (P (N+(h+i.val))) = C j (F * G i.val) := by
    by_cases hi : i.val = 0
    · simp [Matrix.mul_apply,E,hi,F,G]
    · have ha : i.val ≤ h := by have := i.isLt; omega
      let l : Fin h := ⟨h-i.val, by omega⟩
      have hr (b : Fin h) : (i.val ≠ 0 ∧ b.val=h-i.val) ↔ b=l :=
        ⟨fun z => Fin.ext z.2, fun e => ⟨hi,congrArg Fin.val e⟩⟩
      simp only [Matrix.mul_apply,E,Matrix.of_apply,hr,
        ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rw [← map_add]
      apply congrArg (C j)
      have he := pair ((N+h : ℕ) : ℤ) i.val
      rw [show ((N+h : ℕ) : ℤ)+(i.val:ℤ) = ((N+(h+i.val) : ℕ) : ℤ) by omega,
        show ((N+h : ℕ) : ℤ)-(i.val:ℤ) = ((N+l.val : ℕ) : ℤ) by dsimp [l]; omega] at he
      simpa only [G,hi,if_false,F,P,add_comm,mul_comm] using he
  have zeroBlock : E * U + W = 0 := by
    ext i j
    change (E * U) i j + L j.val (P (N+(h+i.val))) = 0
    rw [show (E * U) i j + L j.val (P (N+(h+i.val))) = L j.val (F * G i.val) from
      sum_row (fun b : Fin h => L b.val) i j]
    have dvdF : P h ∣ F := (modByMonic_eq_zero_iff_dvd (P_deg h).monic).mp
      (P_multiple_rem h n)
    have hz := (modByMonic_eq_zero_iff_dvd (P_deg h).monic).mpr
      (dvd_mul_of_dvd_left dvdF (G i.val))
    simp [L,j.isLt,hz]
  have lower : E * V + D = H := by
    ext i j
    change (E * V) i j + L (h+j.val) (P (N+(h+i.val))) = _
    rw [show (E * V) i j + L (h+j.val) (P (N+(h+i.val))) =
      L (h+j.val) (F * G i.val) from sum_row (fun b : Fin m => L (h+b.val)) i j]
    simp [L,H]
  have hU : U.det = (-1 : ℚ)^((h+1).choose 2*n) := by
    simpa [U,L,N] using prefix_det h n
  have hH : H.det = F.coeff 0^m := coefficient_det m F
  let A := fromBlocks (1 : Matrix (Fin h) (Fin h) ℚ) (0 : Matrix (Fin h) (Fin m) ℚ)
    E (1 : Matrix (Fin m) (Fin m) ℚ)
  have hA : A.det = 1 := by simp [A]
  have changed : A * M.submatrix e e = fromBlocks U V 0 H := by
    rw [block]
    simp [A,fromBlocks_multiply,zeroBlock,lower]
  have d := congrArg det changed
  rw [det_mul,hA,one_mul,det_submatrix_equiv_self,det_fromBlocks_zero₂₁,hU,hH] at d
  convert d using 2
  ext i j
  simp only [M,Matrix.of_apply,L]
  split_ifs <;> rfl

end
end OMA.S_mo_442285

namespace OMA.S_mo_442285
noncomputable section
open Matrix Polynomial

theorem catalan_determinant (k n m : ℕ) (hk : 0<k) (hm : m≤k) :
    hankel (catalanConvolution k) (k*n) m =
      (-1 : ℚ)^(k.choose 2*n) * (n+1 : ℕ)^m := by
  obtain ⟨h,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  let N := (h+1)*n
  let u : ℚ[X] := X^m * P h
  have hu : u.IsMonicOfDegree (h+m) := by
    have hu := ((isMonicOfDegree_X (R:=ℚ)).pow m).mul (P_deg h)
    simpa [u,Nat.add_comm] using hu
  obtain ⟨L,orth,mom⟩ := moment_dictionary
  let D := (Matrix.of fun i j : Fin (h+m) => (P (N+i.val) %ₘ u).coeff j.val).det
  let Z := (Matrix.of fun i j : Fin (h+m) => if j.val<h then
      (P (N+i.val) %ₘ P h).coeff j.val else (P (N+i.val)).coeff (j.val-h)).det
  let sign : ℚ := (-1)^((h+1).choose 2*n)
  have dictionary : hankel (catalanConvolution (h+1)) N m =
      (Matrix.of fun i j : Fin N => L (u*X^(i.val+j.val))).det := by
    unfold hankel
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    rw [show u*X^(i.val+j.val) = X^(i.val+j.val+m)*P h by
      dsimp [u]; rw [pow_add]; ring, mom]
  have red : hankel (catalanConvolution (h+1)) N m = (-1)^(N*(h+m))*D :=
    dictionary.trans (multiplier_remainders P P_deg L orth u (h+m) N hu)
  have coords : Z = (P h).coeff 0^m*D :=
    coordinate_change h m (P h) (P_deg h).monic (P_deg h).natDegree_eq
      (fun i => P (N+i.val))
  have reduced : Z = sign*(P (N+h)).coeff 0^m := mixed_residue h n m hm
  have constTerm : (P (N+h)).coeff 0 =
      (P h).coeff 0*((-1 : ℚ)^N*(n+1 : ℕ)) := by
    rw [P_endpoint,P_endpoint,pow_add]
    push_cast
    dsimp [N]
    push_cast
    ring
  have nonzero : (P h).coeff 0 ≠ 0 := by
    rw [P_endpoint]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by positivity)
  have Dval : D = sign*((-1 : ℚ)^(N*m)*(n+1 : ℕ)^m) := by
    apply mul_left_cancel₀ (pow_ne_zero m nonzero)
    calc
      (P h).coeff 0^m*D = Z := coords.symm
      _ = sign*(P (N+h)).coeff 0^m := reduced
      _ = _ := by rw [constTerm,mul_pow,mul_pow,pow_mul]; ring
  have even : Even (N*h) := by
    obtain ⟨l,hl⟩ := Nat.two_dvd_mul_add_one h
    refine ⟨l*n, ?_⟩
    calc
      N*h = (h*(h+1))*n := by dsimp [N]; ring
      _ = _ := by rw [hl]; ring
  have cancel : (-1 : ℚ)^(N*m)*(-1)^(N*m)=1 := by rw [← mul_pow]; norm_num
  change hankel (catalanConvolution (h+1)) N m = sign*(n+1 : ℕ)^m
  rw [red,Dval,Nat.mul_add,pow_add,even.neg_one_pow,one_mul]
  calc
    _ = sign*((-1 : ℚ)^(N*m)*(-1)^(N*m))*(n+1 : ℕ)^m := by ring
    _ = _ := by rw [cancel,mul_one]

end
end OMA.S_mo_442285

namespace OMA.S_mo_442285

theorem narayana_counterexample :
    hankel (fun t => narayanaConvolution 2 t 2) 2 1 = -5 := by
  rw [hankel, Matrix.det_fin_two]
  norm_num [Matrix.of_apply, narayanaConvolution, narayana, Finset.sum_range_succ, Nat.choose]


/-- The neighboring-size prediction for k=1 and m=2 gives the wrong leading
coefficient. Four integer evaluations already determine a cubic. -/
theorem bernoulli_counterexample : ¬ ∃ p : Polynomial ℚ,
    (∀ n : ℕ, p.eval (n : ℚ) = hankel (catalanConvolution 1) n 2) ∧
    p.degree = (3 : ℕ) ∧ p.leadingCoeff = 1/6 := by
  rintro ⟨p,h,hd,hl⟩
  have hn : p.natDegree=3 := Polynomial.natDegree_eq_of_degree_eq_some hd
  have h3 : p.coeff 3 = 1/6 := by rw [← hn,Polynomial.coeff_natDegree,hl]
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3' := h 3
  norm_num [hankel] at h0
  norm_num [hankel, Matrix.det_fin_one, catalanConvolution, Nat.choose] at h1
  norm_num [hankel, Matrix.det_fin_two, catalanConvolution, Nat.choose] at h2
  norm_num [hankel, Matrix.det_fin_three, catalanConvolution, Nat.choose] at h3'
  have ev (x : ℚ) : p.eval x = p.coeff 0 + p.coeff 1*x + p.coeff 2*x^2 + p.coeff 3*x^3 := by
    have hp := p.as_sum_range_C_mul_X_pow' (n:=4) (by omega)
    apply_fun Polynomial.eval x at hp
    simpa [Finset.sum_range_succ,Polynomial.eval_add,Polynomial.eval_mul] using hp
  rw [ev] at h1 h2 h3'
  have e0 : p.coeff 0 = 1 := by simpa [Polynomial.coeff_zero_eq_eval_zero] using h0
  linarith only [h1,h2,h3',h3,e0]

theorem bernoulli_prediction_fails :
    ¬ (∀ k : ℕ, 0 < k → ∀ m : ℕ, 2 ≤ m → m ≤ k+2 → ∃ p : Polynomial ℚ,
      (∀ n : ℕ, p.eval (n : ℚ) =
        (-1 : ℚ)^(n*k.choose 2+(k-1).choose 2) * hankel (catalanConvolution k) (k*n+k-1) m) ∧
      p.degree = (3*(m-1) : ℕ) ∧
      p.leadingCoeff = (-1 : ℚ)^m * bernoulli (2*m-2) /
        (2*m-2).factorial * 2^(2*m-3) * (k : ℚ)^(2*m-2)) := by
  intro h
  obtain ⟨p,he,hd,hl⟩ := h 1 (by decide) 2 (by decide) (by decide)
  apply bernoulli_counterexample
  refine ⟨p,?_,by norm_num at hd; exact hd,?_⟩
  · intro n
    simpa [Nat.choose] using he n
  · norm_num [bernoulli_two,Nat.factorial] at hl
    exact hl

end OMA.S_mo_442285

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_442285.main) := by
  intro h
  have hc := (h 2 (by decide)).2.1 1 1 2 (by decide)
  rw [show 2 * 1 = 2 by decide, OMA.S_mo_442285.narayana_counterexample] at hc
  norm_num [OMA.S_mo_442285.qInt, Finset.sum_range_succ] at hc
