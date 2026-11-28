import OMAStatements.S_mo_403025

/-!
# Sun's four derangement identities

For the determinant, the finite Fourier transform of the centered arithmetic
progression gives the kernel 1 / (1 - q) at nontrivial roots of unity, and zero
at q = 1. Taking an adjugate gives the odd-order principal minor.
For the permanent, insertion of one element in a permutation cancels the
longer-cycle contributions. This implements the ideas of Calogero and
Perelomov, Sun, and Guo, Li, Tao and Wei (arXiv:2206.02592).

Credit: @connoranderson
-/

section

namespace OMA.S_mo_403025
open Matrix Finset

private lemma weighted_geometric (c q : ℂ) (n : ℕ) :
    (1-q) * (∑ k ∈ range n, (c-k)*q^k) =
      c+1-(c+1-n)*q^n - ∑ k ∈ range n, q^k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,sum_range_succ,mul_add,ih,pow_succ,Nat.cast_succ]
    ring

private lemma linear_sum (c : ℂ) (n : ℕ) :
    2 * (∑ k ∈ range n, (c-k)) = n*(2*c-n+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,mul_add,ih,Nat.cast_succ]; ring

lemma kernel_fourier_sum {n : ℕ} (hn : 0 < n) {q : ℂ} (hq : q ^ n = 1) :
    (∑ k : Fin n, (((n:ℂ)-1)/2-k.val) * q^k.val) / n = (1-q)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (((n:ℂ)-1)/2-k) * q^k)]
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  by_cases he : q = 1
  · subst q
    simp only [one_pow,mul_one,sub_self,_root_.inv_zero,div_eq_zero_iff]
    left
    linear_combination (linear_sum (((n:ℂ)-1)/2) n)/2
  · have hg : ∑ k ∈ range n, q^k = 0 := by rw [geom_sum_eq he,hq]; simp
    have h := weighted_geometric (((n:ℂ)-1)/2) q n
    rw [hq,hg,mul_one,sub_zero] at h
    let S := ∑ k ∈ range n, (((n:ℂ)-1)/2-k)*q^k
    have H : (1-q)*S = n := by dsimp only [S]; linear_combination h
    change S / (n:ℂ) = (1-q)⁻¹
    field_simp [hnC,sub_ne_zero.mpr (Ne.symm he)]
    linear_combination H

noncomputable def node {n : ℕ} (ζ : ℂ) (i : Fin n) : ℂ := ζ^i.val

noncomputable def kernel {n : ℕ} (ζ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (1-node ζ i / node ζ j)⁻¹

noncomputable def fourier {n : ℕ} (ζ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i k => node ζ i ^ k.val

noncomputable def inverseFourier {n : ℕ} (ζ : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun k j => (node ζ j ^ k.val)⁻¹ / n

noncomputable def eigenvalue (n : ℕ) (k : Fin n) : ℂ := ((n:ℂ)-1)/2-k.val

private theorem node_power {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (i : Fin n) :
    node ζ i ^ n = 1 := by rw [node,← pow_mul,mul_comm i.val n,pow_mul,h.pow_eq_one,one_pow]

theorem fourier_inverse {n : ℕ} (hn : 0 < n) {ζ : ℂ} (h : IsPrimitiveRoot ζ n) :
    fourier (n := n) ζ * inverseFourier ζ = 1 := by
  classical
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  ext i j
  have hj : node ζ j ≠ 0 := pow_ne_zero _ (h.ne_zero hn.ne')
  have hroot : (node ζ i / node ζ j)^n = 1 := by simp [div_pow,node_power h]
  rw [Matrix.mul_apply]
  simp only [fourier,inverseFourier,Matrix.of_apply,mul_div_assoc',← div_eq_mul_inv, ← div_pow]
  by_cases hij : i=j
  · subst j
    simp [hj,hnC]
  · have hq : node ζ i / node ζ j ≠ 1 := fun he =>
      hij (Fin.ext (h.pow_inj i.isLt j.isLt ((div_eq_one_iff_eq hj).mp he)))
    simp only [Matrix.one_apply,hij,if_false]
    rw [← Finset.sum_div,Fin.sum_univ_eq_sum_range,geom_sum_eq hq,hroot]
    simp

theorem kernel_diagonalization {n : ℕ} (hn : 0 < n) {ζ : ℂ} (h : IsPrimitiveRoot ζ n) :
    kernel (n := n) ζ = fourier ζ * diagonal (eigenvalue n) * inverseFourier ζ := by
  classical
  ext i j
  have hr : (node ζ i / node ζ j)^n = 1 := by simp [div_pow,node_power h]
  rw [Matrix.mul_apply]
  simp only [kernel,Matrix.of_apply,Matrix.mul_diagonal,fourier,inverseFourier,eigenvalue]
  rw [← kernel_fourier_sum hn hr, Finset.sum_div]
  apply sum_congr rfl
  intro k _
  rw [div_pow]
  ring

end OMA.S_mo_403025
end

section

namespace OMA.S_mo_403025
open Finset Matrix

theorem adjugate_conjugation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V D W : Matrix ι ι ℂ) (h : V*W=1) :
    adjugate (V*D*W) = V * adjugate D * W := by
  have h' := _root_.mul_eq_one_comm.mp h
  have rule (A B : Matrix ι ι ℂ) (hAB : A*B=1) : adjugate A = A.det • B := by
    calc
      adjugate A = adjugate A * (A*B) := by rw [hAB,mul_one]
      _ = A.det • B := by rw [← Matrix.mul_assoc,adjugate_mul,Matrix.smul_mul,one_mul]
  rw [adjugate_mul_distrib,adjugate_mul_distrib,rule V W h,rule W V h',Matrix.mul_smul,
    Matrix.smul_mul,Matrix.mul_smul,smul_smul,← det_mul,h',det_one,one_smul,Matrix.mul_assoc]

theorem det_kernel {n : ℕ} (hn : 0 < n) (ζ : ℂ) (h : IsPrimitiveRoot ζ n) :
    (kernel (n := n) ζ).det = ∏ k, eigenvalue n k := by
  rw [kernel_diagonalization hn h,det_mul,det_mul,mul_right_comm,← det_mul,
    fourier_inverse hn h,det_one,one_mul,det_diagonal]

theorem det_kernel_minor {r : ℕ} (ζ : ℂ) (h : IsPrimitiveRoot ζ (r+1)) :
    ((kernel (n := r+1) ζ).submatrix Fin.succ Fin.succ).det =
      (∑ k : Fin (r+1), ∏ j ∈ univ.erase k, eigenvalue (r+1) j) / (r+1 : ℕ) := by
  have hminor := adjugate_fin_succ_eq_det_submatrix (kernel (n := r+1) ζ) 0 0
  simp only [Fin.val_zero, Nat.zero_add, pow_zero, one_mul,Fin.succAbove_zero] at hminor
  rw [← hminor, kernel_diagonalization (by omega) h,adjugate_conjugation _ _ _ (fourier_inverse (by omega) h),
    adjugate_diagonal,Matrix.mul_apply,Finset.sum_div]
  apply sum_congr rfl
  intro j _
  simp [mul_diagonal,fourier,inverseFourier,node,div_eq_mul_inv]

theorem det_kernel_odd {m : ℕ} (ζ : ℂ) (h : IsPrimitiveRoot ζ (2*m+1))
    (mid : Fin (2*m+1)) (hm : mid.val=m) :
    ((kernel (n := 2*m+1) ζ).submatrix Fin.succ Fin.succ).det =
      (∏ j ∈ univ.erase mid, eigenvalue (2*m+1) j) / (2*m+1 : ℕ) := by
  rw [det_kernel_minor ζ h]
  congr 1
  apply Fintype.sum_eq_single mid
  intro j hne
  have hz : eigenvalue (2*m+1) mid = 0 := by simp [eigenvalue,hm]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne,Finset.mem_univ _⟩) hz

end OMA.S_mo_403025
end

section

namespace OMA.S_mo_403025
open Finset

private lemma odd_product (m : ℕ) :
    ∏ i ∈ range m, (2*(i:ℂ)+1) = (Nat.doubleFactorial (2*m-1):ℂ) := by
  cases m with
  | zero => norm_num
  | succ k =>
    rw [show 2*(k+1)-1=2*k+1 by omega,Nat.doubleFactorial_eq_prod_odd]
    push_cast
    rw [prod_range_succ']
    simp

private lemma half_product (m : ℕ) :
    ∏ i ∈ range m, ((i:ℂ)+1/2) = (Nat.doubleFactorial (2*m-1):ℂ)/2^m := by
  have hterm (i : ℕ) : (i:ℂ)+1/2=(2*(i:ℂ)+1)/2 := by ring
  simp_rw [hterm]
  rw [prod_div_distrib,odd_product]
  simp

/-- The product of the entire half-integral centered spectrum in even dimension. -/
theorem signed_product_even (m : ℕ) :
    (∏ j : Fin (2*m), ((((2*m:ℕ):ℂ)-1)/2-(j.val:ℂ))) =
      (-1:ℂ)^m*(Nat.doubleFactorial (2*m-1):ℂ)^2/2^(2*m) := by
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => (((2*m:ℕ):ℂ)-1)/2-(j:ℂ)),show 2*m=m+m by omega,prod_range_add]
  have hl : (∏ j ∈ range m, ((((m+m:ℕ):ℂ)-1)/2-(j:ℂ))) =
      ∏ j ∈ range m, ((j:ℂ)+1/2) := by
    rw [← prod_range_reflect (fun i : ℕ => (i:ℂ)+1/2) m]
    apply prod_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [Nat.cast_sub (by omega : j ≤ m-1),Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast; ring
  have hr : (∏ j ∈ range m, ((((m+m:ℕ):ℂ)-1)/2-((m+j:ℕ):ℂ))) =
      (-1:ℂ)^m * ∏ j ∈ range m, ((j:ℂ)+1/2) := by
    calc
      _ = ∏ j ∈ range m, (-1:ℂ)*((j:ℂ)+1/2) := by
        apply prod_congr rfl
        intro j hj; push_cast; ring
      _ = _ := by rw [prod_mul_distrib,prod_const,card_range]
  rw [hl,hr,half_product]
  rw [pow_add]
  ring

private lemma integers_product (m : ℕ) :
    ∏ j ∈ range m, ((j:ℂ)+1) = (m.factorial:ℂ) := by
  induction m with
  | zero => simp
  | succ m ih => rw [prod_range_succ,ih,Nat.factorial_succ]; push_cast; ring

/-- In odd dimension the middle eigenvalue is omitted and each positive
integer is paired with its negative. -/
theorem signed_product_odd (m : ℕ) :
    (∏ j : Fin (2*m+1), if j.val=m then 1 else (m:ℂ)-(j.val:ℂ)) =
      (-1:ℂ)^m*(m.factorial:ℂ)^2 := by
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => if j=m then 1 else (m:ℂ)-(j:ℂ)),
    show 2*m+1=m+(m+1) by omega,prod_range_add,prod_range_succ']
  have hl : (∏ j ∈ range m, if j=m then 1 else (m:ℂ)-(j:ℂ)) =
      ∏ j ∈ range m, ((j:ℂ)+1) := by
    rw [← prod_range_reflect (fun i : ℕ => (i:ℂ)+1) m]
    apply prod_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    rw [if_neg (by omega),Nat.cast_sub (by omega : j ≤ m-1),Nat.cast_sub (by omega : 1 ≤ m)]
    push_cast; ring
  have hr : (∏ j ∈ range m, if m+(j+1)=m then 1 else (m:ℂ)-((m+(j+1):ℕ):ℂ)) =
      (-1:ℂ)^m * ∏ j ∈ range m, ((j:ℂ)+1) := by
    calc
      _ = ∏ j ∈ range m, (-1:ℂ)*((j:ℂ)+1) := by
        apply prod_congr rfl
        intro j hj; simp
      _ = _ := by rw [prod_mul_distrib,prod_const,card_range]
  rw [hl,hr,integers_product]
  simp
  ring

theorem signed_product_odd_erase (m : ℕ) :
    (∏ j ∈ (univ : Finset (Fin (2*m+1))).erase ⟨m,by omega⟩, ((m:ℂ)-(j.val:ℂ))) =
      (-1:ℂ)^m*(m.factorial:ℂ)^2 := by
  rw [← signed_product_odd m]
  have he : (univ : Finset (Fin (2*m+1))).erase ⟨m,by omega⟩ = univ.filter (fun j => j.val≠m) := by
    ext j
    simp [Fin.ext_iff]
  rw [he,prod_filter]
  simp

end OMA.S_mo_403025
end

section

namespace OMA.S_mo_403025
open Matrix Finset

/-- Matrix of Sun's derangement weights. The diagonal is zero since 0⁻¹ = 0. -/
noncomputable def derangementMatrix (m : ℕ) (ζ : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => (1 - ζ^((i.val:ℤ)-(j.val:ℤ)))⁻¹

private lemma derangementSum_univ (m : ℕ) (ζ : ℂ) (signed : Bool) :
    derangementSum m ζ signed = ∑ σ : Equiv.Perm (Fin m),
      (if signed then (((Equiv.Perm.sign σ : ℤˣ):ℤ):ℂ) else 1) *
        ∏ i, derangementMatrix m ζ i (σ i) := by
  classical
  rw [derangementSum, sum_filter]
  apply sum_congr rfl
  intro σ hσ
  by_cases h : ∀ i, σ i ≠ i
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    push Not at h
    obtain ⟨i,hi⟩ := h
    have hz : derangementMatrix m ζ i (σ i) = 0 := by simp [hi,derangementMatrix]
    rw [prod_eq_zero (mem_univ i) hz, mul_zero]

theorem derangementSum_eq_det (m : ℕ) (ζ : ℂ) :
    derangementSum m ζ true = (derangementMatrix m ζ).det := by
  rw [derangementSum_univ, ← Matrix.det_transpose, Matrix.det_apply']
  rfl

theorem derangementSum_eq_permanent (m : ℕ) (ζ : ℂ) :
    derangementSum m ζ false = (derangementMatrix m ζ).permanent := by
  rw [derangementSum_univ, ← Matrix.permanent_transpose, Matrix.permanent]
  simp

theorem derangementMatrix_eq_kernel (m : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    derangementMatrix m ζ = Matrix.of (fun i j : Fin m => (1-ζ^i.val/ζ^j.val)⁻¹) := by
  ext i j
  simp [derangementMatrix,zpow_sub₀ hζ,div_eq_mul_inv]

/-- Off the diagonal the underlying Cauchy entry is 1/(x_j−x_i);
the same formula also gives zero on the diagonal. -/
noncomputable def skewCauchyMatrix {m : ℕ} (x : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => (x j - x i)⁻¹

theorem derangementMatrix_eq_cauchy_mul_diagonal (m : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    derangementMatrix m ζ = skewCauchyMatrix (fun i : Fin m => ζ^i.val) *
      diagonal (fun j : Fin m => ζ^j.val) := by
  classical
  rw [derangementMatrix_eq_kernel m hζ]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.of_apply, one_sub_div (pow_ne_zero _ hζ)]
  simp [skewCauchyMatrix, div_eq_mul_inv, mul_comm]

theorem derangementMatrix_eq_cauchy_scaled (m : ℕ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    derangementMatrix m ζ =
      Matrix.of (fun i j : Fin m => ζ^j.val * (ζ^j.val - ζ^i.val)⁻¹) := by
  classical
  rw [derangementMatrix_eq_cauchy_mul_diagonal m hζ]
  ext i j
  simp [skewCauchyMatrix, Matrix.mul_diagonal, mul_comm]

theorem rootNodes_injective {m n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hm : m ≤ n) :
    Function.Injective (fun i : Fin m => ζ^i.val) := by
  intro i j h
  exact Fin.ext (hζ.pow_inj (i.isLt.trans_le hm) (j.isLt.trans_le hm) h)

/-- Simultaneously deleting row and column zero does not change the integer
difference in any remaining entry. -/
theorem derangementMatrix_submatrix_succ (m : ℕ) (ζ : ℂ) :
    (derangementMatrix (m+1) ζ).submatrix Fin.succ Fin.succ = derangementMatrix m ζ := by
  ext i j
  simp [derangementMatrix,Matrix.submatrix]

theorem permanent_mul_diagonal_right {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin m → ℂ) : (A * diagonal x).permanent = A.permanent * ∏ j, x j := by
  classical
  simp only [Matrix.permanent, Matrix.mul_diagonal, prod_mul_distrib, sum_mul]

end OMA.S_mo_403025
end

section

/-! A skew-Cauchy permanent identity by insertion of one vertex into a permutation.
The cancellation of cycles underlies the proof of Guo, Li, Tao and Wei, arXiv:2206.02592.
Arbitrary diagonal entries permit a single induction over the dimension. -/

namespace OMA.S_mo_403025.Cauchy
open Finset Equiv
open scoped BigOperators

private noncomputable def edge {n : ℕ} (x d : Fin n → ℂ) (a : ℂ) (i j : Fin n) : ℂ :=
  if i = j then d i else a / (x j - x i)

private noncomputable def term {n : ℕ} (x d : Fin n → ℂ) (a : ℂ) (σ : Perm (Fin n)) : ℂ :=
  ∏ i, edge x d a i (σ i)

private noncomputable def omittedTerm {n : ℕ} (x d : Fin n → ℂ) (a : ℂ) (σ : Perm (Fin n))
    (k : Fin n) : ℂ := ∏ i ∈ univ.erase k, edge x d a i (σ i)

private lemma term_at {n : ℕ} (x d : Fin n → ℂ) (a : ℂ) (σ : Perm (Fin n)) (k : Fin n) :
    term x d a σ = edge x d a k (σ k) * omittedTerm x d a σ k := by
  exact (mul_prod_erase _ _ (mem_univ k)).symm

private lemma term_update {n : ℕ} (x d : Fin n → ℂ) (a : ℂ) (σ : Perm (Fin n))
    (k : Fin n) (t : ℂ) :
    term x (Function.update d k t) a σ =
      (if k = σ k then t else a / (x (σ k) - x k)) * omittedTerm x d a σ k := by
  rw [term_at _ _ _ _ k]
  congr 1
  · simp [edge]
  · apply prod_congr rfl
    intro i hi
    simp [edge, ne_of_mem_erase hi]

private lemma term_fix {n : ℕ} (x d : Fin (n+1) → ℂ) (a : ℂ) (σ : Perm (Fin n)) :
    term x d a (Perm.decomposeFin.symm (0, σ)) =
      d 0 * term (x ∘ Fin.succ) (d ∘ Fin.succ) a σ := by
  simp [term, Fin.prod_univ_succ, edge]

private lemma term_insert {n : ℕ} (x d : Fin (n+1) → ℂ) (a : ℂ) (σ : Perm (Fin n))
    (k : Fin n) :
    term x d a (Perm.decomposeFin.symm ((σ k).succ, σ)) =
      a / (x (σ k).succ - x 0) * (a / (x 0 - x k.succ)) *
        omittedTerm (x ∘ Fin.succ) (d ∘ Fin.succ) a σ k := by
  rw [term, Fin.prod_univ_succ, ← mul_prod_erase _ _ (mem_univ k)]
  rw [mul_assoc (a / _) (a / _) (omittedTerm _ _ _ _ _)]
  apply congrArg₂ (· * ·)
  · simp [edge, Ne.symm (Fin.succ_ne_zero (σ k))]
  · apply congrArg₂ (· * ·)
    · simp [edge]
    · apply prod_congr rfl
      intro i hi
      have h : σ i ≠ σ k := σ.injective.ne (ne_of_mem_erase hi)
      simp [edge, Equiv.swap_apply_def, h]

private noncomputable def pole {n : ℕ} (x : Fin (n+1) → ℂ) (k : Fin n) : ℂ :=
  (x k.succ - x 0)⁻¹

private noncomputable def pair {n : ℕ} (x : Fin (n+1) → ℂ) (k : Fin n) : ℂ :=
  (x k.succ - x 0)⁻¹ * (x 0 - x k.succ)⁻¹

private lemma insert_difference {n : ℕ} (x d : Fin (n+1) → ℂ) (hx : Function.Injective x)
    (a : ℂ) (σ : Perm (Fin n)) (k : Fin n) :
    let y := x ∘ Fin.succ
    let e := d ∘ Fin.succ
    term x d a (Perm.decomposeFin.symm ((σ k).succ, σ)) =
      a * term y e a σ * (pole x (σ k) - pole x k) +
      a^2 * pair x k * (term y (Function.update e k 1) a σ -
        term y (Function.update e k 0) a σ) := by
  dsimp only
  rw [term_insert, term_at _ _ _ _ k, term_update, term_update]
  by_cases hk : k = σ k
  · rw [← hk]
    simp only [ite_true, sub_self, mul_zero, zero_add, one_mul, zero_mul, sub_zero]
    simp only [pair, div_eq_mul_inv]
    ring
  · simp only [edge, if_neg hk, sub_self, mul_zero, add_zero, Function.comp_apply]
    have h1 : x (σ k).succ - x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero _))
    have h2 : x k.succ - x 0 ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero _))
    have h3 : x 0 - x k.succ ≠ 0 := sub_ne_zero.mpr (hx.ne (Fin.succ_ne_zero _).symm)
    have h4 : x (σ k).succ - x k.succ ≠ 0 := sub_ne_zero.mpr
      (hx.ne ((Fin.succ_injective _).ne (Ne.symm hk)))
    dsimp only [pole]
    field_simp
    ring

private noncomputable def weight {n : ℕ} (s : Bool) (σ : Perm (Fin n)) : ℂ :=
  if s then ((Perm.sign σ : ℤ) : ℂ) else 1

private def parity (s : Bool) : ℂ := if s then -1 else 1

private noncomputable def score {n : ℕ} (s : Bool) (x d : Fin n → ℂ) (a : ℂ) : ℂ :=
  ∑ σ : Perm (Fin n), weight s σ * term x d a σ

private lemma fibre {n : ℕ} (s : Bool) (x d : Fin (n+1) → ℂ) (hx : Function.Injective x)
    (a : ℂ) (σ : Perm (Fin n)) :
    let y := x ∘ Fin.succ
    let e := d ∘ Fin.succ
    (∑ p : Fin (n+1), weight s (Perm.decomposeFin.symm (p, σ)) *
      term x d a (Perm.decomposeFin.symm (p, σ))) =
      d 0 * (weight s σ * term y e a σ) +
      (parity s * a^2) * ∑ k, pair x k *
        (weight s σ * term y (Function.update e k 1) a σ -
          weight s σ * term y (Function.update e k 0) a σ) := by
  dsimp only
  rw [Fin.sum_univ_succ, term_fix]
  have h0 : weight s (Perm.decomposeFin.symm (0, σ)) = weight s σ := by cases s <;> simp [weight]
  have hs (k : Fin n) : weight s (Perm.decomposeFin.symm (k.succ, σ)) =
      parity s * weight s σ := by cases s <;> simp [weight, parity]
  rw [h0, mul_left_comm (weight s σ), ← Equiv.sum_comp σ]
  simp_rw [hs, insert_difference x d hx a σ]
  congr 1
  let y := x ∘ Fin.succ
  let e := d ∘ Fin.succ
  have hz : ∑ k, (pole x (σ k) - pole x k) = 0 := by
    rw [sum_sub_distrib, Equiv.sum_comp σ, sub_self]
  calc
    _ = ((parity s * weight s σ) * (a * term y e a σ)) *
          (∑ k, (pole x (σ k) - pole x k)) +
        (parity s * a^2) * ∑ k, pair x k *
          (weight s σ * term y (Function.update e k 1) a σ -
            weight s σ * term y (Function.update e k 0) a σ) := by
              simp only [mul_sum, ← sum_add_distrib]
              apply sum_congr rfl
              intro k _
              dsimp only [y, e]
              ring
    _ = _ := by rw [hz, mul_zero, zero_add]

private lemma score_succ {n : ℕ} (s : Bool) (x d : Fin (n+1) → ℂ)
    (hx : Function.Injective x) (a : ℂ) :
    let y := x ∘ Fin.succ
    let e := d ∘ Fin.succ
    score s x d a = d 0 * score s y e a +
      (parity s * a^2) * ∑ k, pair x k *
        (score s y (Function.update e k 1) a - score s y (Function.update e k 0) a) := by
  dsimp only
  unfold score
  rw [← Perm.decomposeFin.symm.sum_comp]
  rw [Fintype.sum_prod_type, sum_comm]
  simp_rw [fibre s x d hx a]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_comm]
  congr 2
  apply sum_congr rfl
  intro k _
  rw [← mul_sum, sum_sub_distrib]

private lemma score_identity {n : ℕ} (x d : Fin n → ℂ) (hx : Function.Injective x) :
    score false x d 1 = score true x d Complex.I := by
  induction n with
  | zero => simp [score, term, weight]
  | succ n ih =>
    rw [score_succ false x d hx, score_succ true x d hx]
    simp only [parity, Bool.false_eq_true, ↓reduceIte, one_pow, Complex.I_sq, mul_one, neg_mul,
      one_mul, neg_neg]
    have hy := hx.comp (Fin.succ_injective n)
    simp_rw [ih _ _ hy]

/-- The permanent of a skew-Cauchy matrix is the determinant of its multiple by i. -/
theorem permanent_eq_i_pow_det {n : ℕ} (x : Fin n → ℂ) (hx : Function.Injective x) :
    let B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (x j - x i)⁻¹
    B.permanent = Complex.I ^ n * B.det := by
  let B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (x j - x i)⁻¹
  change B.permanent = Complex.I ^ n * B.det
  have hentry (a : ℂ) (i j : Fin n) :
      edge x (fun _ => 0) a i j = a * B i j := by
    by_cases h : i = j <;> simp [edge, h, B, div_eq_mul_inv]
  calc
    B.permanent = B.transpose.permanent := (Matrix.permanent_transpose B).symm
    _ = score false x (fun _ => 0) 1 := by
      simp [Matrix.permanent, score, term, weight, hentry]
    _ = score true x (fun _ => 0) Complex.I := score_identity _ _ hx
    _ = (Complex.I • B.transpose).det := by
      simp [Matrix.det_apply', score, term, weight, hentry]
    _ = Complex.I ^ n * B.det := by simp

/-- For even size 2m, the permanent is (-1)^m times the determinant.
Each column may independently be multiplied by a scalar. -/
theorem permanent_scaled {n : ℕ} (hn : Even n) (x c : Fin n → ℂ) (hx : Function.Injective x) :
    let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => c j * (x j - x i)⁻¹
    A.permanent = (-1 : ℂ)^(n/2) * A.det := by
  let B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (x j - x i)⁻¹
  change (Matrix.of fun i j => c j * B i j).permanent =
    (-1 : ℂ)^(n/2) * (Matrix.of fun i j => c j * B i j).det
  have hp : (Matrix.of fun i j => c j * B i j).permanent = (∏ j, c j) * B.permanent := by
    simp [Matrix.permanent, prod_mul_distrib, mul_sum]
  have hI : Complex.I^n = (-1 : ℂ)^(n/2) := by
    obtain ⟨m, hm⟩ := hn
    have h : n = 2*m := by omega
    rw [h, pow_mul, Complex.I_sq]
    simp
  rw [hp, Matrix.det_mul_row, permanent_eq_i_pow_det x hx, hI]
  ring

end OMA.S_mo_403025.Cauchy
end

namespace OMA.S_mo_403025
open Matrix Finset

private theorem signed_even (m : ℕ) (hm : 0 < 2*m) (ζ : ℂ) (hz : IsPrimitiveRoot ζ (2*m)) :
    derangementSum (2*m) ζ true =
      (-1:ℂ)^m * (Nat.doubleFactorial (2*m-1):ℂ)^2 / 2^(2*m) := by
  rw [derangementSum_eq_det]
  have he : derangementMatrix (2*m) ζ = kernel ζ := derangementMatrix_eq_kernel _ (hz.ne_zero hm.ne')
  rw [he,det_kernel hm ζ hz]
  exact signed_product_even m

private theorem signed_odd (m : ℕ) (ζ : ℂ) (hz : IsPrimitiveRoot ζ (2*m+1)) :
    derangementSum (2*m) ζ true = (-1:ℂ)^m * (m.factorial:ℂ)^2 / (2*m+1:ℕ) := by
  rw [derangementSum_eq_det,← derangementMatrix_submatrix_succ]
  have he : derangementMatrix (2*m+1) ζ = kernel ζ :=
    derangementMatrix_eq_kernel _ (hz.ne_zero (by omega))
  rw [he,det_kernel_odd ζ hz ⟨m,by omega⟩ rfl]
  have E (j : Fin (2*m+1)) : eigenvalue (2*m+1) j = (m:ℂ)-j.val := by simp [eigenvalue]
  simp only [E,signed_product_odd_erase]

private theorem unsigned_eq_signed {m n : ℕ} (hm : Even m) (hle : m ≤ n) (hn : n ≠ 0)
    (ζ : ℂ) (hz : IsPrimitiveRoot ζ n) :
    derangementSum m ζ false = (-1:ℂ)^(m/2)*derangementSum m ζ true := by
  rw [derangementSum_eq_det,derangementSum_eq_permanent,derangementMatrix_eq_cauchy_scaled m (hz.ne_zero hn)]
  exact Cauchy.permanent_scaled hm _ _ (rootNodes_injective hz hle)

private theorem sign_mul_sign (m : ℕ) : (-1:ℂ)^m * (-1)^m = 1 := by
  rw [← mul_pow]
  simp

end OMA.S_mo_403025

open OMA.S_mo_403025 in
theorem OMA.solution : type_of% @OMA.S_mo_403025.main := by
  intro n ζ hn hz
  constructor
  · intro he
    obtain ⟨m,hm⟩ := he
    have en : n = 2*m := by omega
    clear hm
    subst n
    have hd : 2*m/2 = m := by omega
    rw [hd]
    have h := signed_even m (by omega) ζ hz
    refine ⟨?_,h⟩
    rw [unsigned_eq_signed (by exact ⟨m,by omega⟩) le_rfl (by omega) ζ hz,hd,h]
    linear_combination (Nat.doubleFactorial (2*m-1):ℂ)^2 / 2^(2*m) * sign_mul_sign m
  · intro ho
    obtain ⟨m,hm⟩ := ho
    have en : n = 2*m+1 := by omega
    clear hm
    subst n
    have hd : (2*m+1-1)/2=m := by omega
    rw [hd, Nat.add_sub_cancel]
    have h := signed_odd m ζ hz
    refine ⟨?_,h⟩
    rw [unsigned_eq_signed (by exact ⟨m,by omega⟩) (by omega) (by omega) ζ hz,
      show 2*m/2=m by omega,h]
    linear_combination (m.factorial:ℂ)^2 / (2*m+1:ℕ) * sign_mul_sign m
