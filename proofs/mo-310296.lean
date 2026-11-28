import OMAStatements.S_mo_310296
import Mathlib

/-!
# Proof of MathOverflow 310296: Equality in a trace bound for Lyapunov equations

Agent: antigravity
Model: Gemini 4 Neon
Credit: @Andyi955

Given a real Hurwitz matrix `A` of size `(n + 1) × (n + 1)`, we consider the compact convex set
`F = {P : 0 ≼ P ≼ I, -(A P + P Aᵀ) ≽ 0}` and maximize the linear functional `-2 tr(A P) = tr(Q)`.
By Hahn-Banach separation applied to the truncated cone image and the dual inequality
`tr(X) ≥ tr(W⁻¹ X) ≥ -tr(W⁻¹ (Aᵀ W + W A)) = -2 tr(A)` for `W = I + Y ≽ I`, the maximum is at
least `-2 tr(A)`. A block-diagonal kernel decomposition via the spectral theorem and Hurwitz
trace negativity on the zero-eigenspace forces any maximizer `P*` to be strictly positive definite,
yielding `P* ≻ 0`, `Q* ≽ 0`, `A P* + P* Aᵀ = -Q*`, and `-2 tr(A) = tr(Q*) / λ_max(P*)`.
-/

namespace OMA.S_mo_310296

open Matrix BigOperators

section Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
private lemma isHermitian_iff_transpose_eq {M : Matrix ι ι ℝ} :
    M.IsHermitian ↔ Mᵀ = M := by
  constructor
  · intro h
    ext i j
    have := congr_fun (congr_fun h i) j
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using this
  · intro h
    ext i j
    have := congr_fun (congr_fun h i) j
    simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using this

omit [DecidableEq ι] in
private lemma posSemidef_iff_real {M : Matrix ι ι ℝ} :
    M.PosSemidef ↔ Mᵀ = M ∧ ∀ x : ι → ℝ, 0 ≤ x ⬝ᵥ M.mulVec x := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec, isHermitian_iff_transpose_eq]
  simp

omit [DecidableEq ι] in
private lemma posDef_iff_real {M : Matrix ι ι ℝ} :
    M.PosDef ↔ Mᵀ = M ∧ ∀ x : ι → ℝ, x ≠ 0 → 0 < x ⬝ᵥ M.mulVec x := by
  rw [Matrix.posDef_iff_dotProduct_mulVec, isHermitian_iff_transpose_eq]
  simp

private lemma posSemidef_diag_nonneg {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (i : ι) :
    0 ≤ M i i := by
  have h := (posSemidef_iff_real.mp hM).2 (Pi.single i 1)
  simpa [dotProduct, mulVec, Pi.single_apply] using h

private lemma posSemidef_trace_nonneg {M : Matrix ι ι ℝ} (hM : M.PosSemidef) :
    0 ≤ M.trace :=
  Finset.sum_nonneg fun i _ => posSemidef_diag_nonneg hM i

private lemma posSemidef_abs_entry_le_diag_avg {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (i j : ι) :
    |M i j| ≤ (M i i + M j j) / 2 := by
  obtain ⟨hsym, hq⟩ := posSemidef_iff_real.mp hM
  have hji : M j i = M i j := by
    have := congr_fun (congr_fun hsym i) j
    simpa [Matrix.transpose_apply] using this
  have eval_quad : ∀ s : ℝ,
      (Pi.single i (1 : ℝ) + s • Pi.single j (1 : ℝ)) ⬝ᵥ
        M.mulVec (Pi.single i (1 : ℝ) + s • Pi.single j (1 : ℝ)) =
      M i i + 2 * s * M i j + s ^ 2 * M j j := by
    intro s
    simp only [dotProduct, mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_add, add_mul, hji]
    ring
  have h1 := hq (Pi.single i (1 : ℝ) + (1 : ℝ) • Pi.single j (1 : ℝ))
  have h2 := hq (Pi.single i (1 : ℝ) + (-1 : ℝ) • Pi.single j (1 : ℝ))
  rw [eval_quad 1] at h1
  rw [eval_quad (-1)] at h2
  rw [abs_le]
  constructor <;> linarith

private lemma posSemidef_diagonal {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) :
    (Matrix.diagonal d).PosSemidef := by
  rw [posSemidef_iff_real]
  refine ⟨by simp, fun x => ?_⟩
  have : x ⬝ᵥ (Matrix.diagonal d).mulVec x = ∑ i, d i * (x i) ^ 2 := by
    simp [dotProduct, mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [this]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sq_nonneg _)

omit [DecidableEq ι] in
private lemma posSemidef_vecMulVec (x : ι → ℝ) :
    (Matrix.vecMulVec x x).PosSemidef := by
  rw [posSemidef_iff_real]
  refine ⟨by ext i j; simp [Matrix.vecMulVec_apply, mul_comm], fun y => ?_⟩
  have : y ⬝ᵥ (Matrix.vecMulVec x x).mulVec y = (∑ i, x i * y i) ^ 2 := by
    simp only [dotProduct, mulVec, Matrix.vecMulVec_apply, sq]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [this]
  exact sq_nonneg _

private lemma posSemidef_one : (1 : Matrix ι ι ℝ).PosSemidef := by
  simpa [Matrix.diagonal_one] using posSemidef_diagonal (fun _ : ι => (zero_le_one : (0 : ℝ) ≤ 1))

omit [DecidableEq ι] in
private lemma posSemidef_zero : (0 : Matrix ι ι ℝ).PosSemidef := by
  rw [posSemidef_iff_real]
  exact ⟨by simp, fun _ => by simp⟩

private lemma spectral_real {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ := by
  have h := hA.spectral_theorem
  simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using h

private lemma spectral_conj_real {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ * A * (hA.eigenvectorUnitary : Matrix ι ι ℝ) =
      Matrix.diagonal hA.eigenvalues := by
  let U : Matrix ι ι ℝ := hA.eigenvectorUnitary
  have hU2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have h0 : Uᴴ * A * U = Uᴴ * (U * Matrix.diagonal hA.eigenvalues * Uᴴ) * U :=
    congr_arg (fun X => Uᴴ * X * U) (spectral_real hA)
  calc
    Uᴴ * A * U = Uᴴ * (U * Matrix.diagonal hA.eigenvalues * Uᴴ) * U := h0
    _ = (Uᴴ * U) * Matrix.diagonal hA.eigenvalues * (Uᴴ * U) := by simp [Matrix.mul_assoc]
    _ = Matrix.diagonal hA.eigenvalues := by rw [hU2, Matrix.one_mul, Matrix.mul_one]

private lemma posSemidef_trace_mul_nonneg {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hAh : A.IsHermitian := hA.1
  let U : Matrix ι ι ℝ := hAh.eigenvectorUnitary
  have htr : (A * B).trace = (Matrix.diagonal hAh.eigenvalues * (Uᴴ * B * U)).trace := by
    conv_lhs => rw [spectral_real hAh]
    change (U * Matrix.diagonal hAh.eigenvalues * Uᴴ * B).trace = _
    calc
      (U * Matrix.diagonal hAh.eigenvalues * Uᴴ * B).trace
          = (U * (Matrix.diagonal hAh.eigenvalues * (Uᴴ * B))).trace := by
              simp [Matrix.mul_assoc]
      _ = (Matrix.diagonal hAh.eigenvalues * (Uᴴ * B) * U).trace :=
            Matrix.trace_mul_comm _ _
      _ = (Matrix.diagonal hAh.eigenvalues * (Uᴴ * B * U)).trace := by
            simp [Matrix.mul_assoc]
  rw [htr, Matrix.trace]
  have hUBU : (Uᴴ * B * U).PosSemidef := hB.conjTranspose_mul_mul_same U
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [Matrix.diag_apply, Matrix.diagonal_mul]
  exact mul_nonneg (hA.eigenvalues_nonneg i) (posSemidef_diag_nonneg hUBU i)

private lemma spectral_inv_eq {P : Matrix ι ι ℝ} (hP : P.PosDef) :
    P⁻¹ = (hP.1.eigenvectorUnitary : Matrix ι ι ℝ) *
      Matrix.diagonal (fun i => (hP.1.eigenvalues i)⁻¹) *
      (hP.1.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ := by
  have hPh : P.IsHermitian := hP.1
  let U : Matrix ι ι ℝ := hPh.eigenvectorUnitary
  have hU1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hPh.eigenvectorUnitary.2
  have hU2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hPh.eigenvectorUnitary.2
  have hmul : P * (U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹) * Uᴴ) = 1 := by
    have h0 : P * (U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹) * Uᴴ) =
        (U * Matrix.diagonal hPh.eigenvalues * Uᴴ) *
        (U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹) * Uᴴ) :=
      congr_arg (fun X => X * (U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹) * Uᴴ))
        (spectral_real hPh)
    calc
      P * (U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹) * Uᴴ)
          = U * Matrix.diagonal hPh.eigenvalues * Uᴴ *
              (U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹) * Uᴴ) := h0
      _ = U * (Matrix.diagonal hPh.eigenvalues * (Uᴴ * U) *
              Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹)) * Uᴴ := by
              simp [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal hPh.eigenvalues *
              Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹)) * Uᴴ := by
              rw [hU2, Matrix.mul_one]
      _ = U * (1 : Matrix ι ι ℝ) * Uᴴ := by
              congr 2
              rw [Matrix.diagonal_mul_diagonal]
              ext i j
              by_cases hij : i = j
              · subst hij
                simp [(hP.eigenvalues_pos i).ne']
              · simp [hij]
      _ = 1 := by rw [Matrix.mul_one, hU1]
  exact Matrix.inv_eq_right_inv hmul

private lemma posDef_of_sub_one_posSemidef {W : Matrix ι ι ℝ} (hW : (W - 1).PosSemidef) :
    W.PosDef := by
  obtain ⟨hsym, hq⟩ := posSemidef_iff_real.mp hW
  rw [posDef_iff_real]
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : Wᵀ - 1 = W - 1 := by simpa [Matrix.transpose_sub] using hsym
    have := congr_arg (· + (1 : Matrix ι ι ℝ)) h1
    simpa using this
  · have hx0 : 0 < x ⬝ᵥ x := by
      have ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
      have hpos : 0 < x i * x i := mul_self_pos.mpr hi
      have hle : x i * x i ≤ ∑ j, x j * x j :=
        Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
      exact lt_of_lt_of_le hpos hle
    have hsub := hq x
    have : x ⬝ᵥ (W - 1).mulVec x = x ⬝ᵥ W.mulVec x - x ⬝ᵥ x := by
      simp [Matrix.sub_mulVec, dotProduct_sub]
    linarith

private lemma one_sub_inv_posSemidef {W : Matrix ι ι ℝ} (hWsub : (W - 1).PosSemidef) :
    (1 - W⁻¹).PosSemidef := by
  have hW : W.PosDef := posDef_of_sub_one_posSemidef hWsub
  have hWh : W.IsHermitian := hW.1
  let U : Matrix ι ι ℝ := hWh.eigenvectorUnitary
  have hU1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hWh.eigenvectorUnitary.2
  have hU2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hWh.eigenvectorUnitary.2
  have hge1 : ∀ i, 1 ≤ hWh.eigenvalues i := by
    intro i
    have hconj : (Uᴴ * (W - 1) * U).PosSemidef := hWsub.conjTranspose_mul_mul_same U
    have hd := posSemidef_diag_nonneg hconj i
    have heq : Uᴴ * (W - 1) * U = Matrix.diagonal hWh.eigenvalues - 1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]
      exact congr_arg (· - (1 : Matrix ι ι ℝ)) (spectral_conj_real hWh)
    rw [heq] at hd
    simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at hd
    linarith
  have hinv := spectral_inv_eq hW
  have hdiff : 1 - W⁻¹ = U * Matrix.diagonal (fun i => 1 - (hWh.eigenvalues i)⁻¹) * Uᴴ := by
    rw [hinv]
    calc
      (1 : Matrix ι ι ℝ) - U * Matrix.diagonal (fun i => (hWh.eigenvalues i)⁻¹) * Uᴴ
          = U * 1 * Uᴴ - U * Matrix.diagonal (fun i => (hWh.eigenvalues i)⁻¹) * Uᴴ := by
              rw [Matrix.mul_one, hU1]
      _ = U * (1 - Matrix.diagonal (fun i => (hWh.eigenvalues i)⁻¹)) * Uᴴ := by
              rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = U * Matrix.diagonal (fun i => 1 - (hWh.eigenvalues i)⁻¹) * Uᴴ := by
              congr 2
              ext i j
              by_cases hij : i = j
              · subst hij; simp
              · simp [hij]
  rw [hdiff]
  refine (posSemidef_diagonal fun i => ?_).mul_mul_conjTranspose_same U
  have hi := hge1 i
  have hinv_le : (hWh.eigenvalues i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hi
  linarith

private lemma inv_sub_smul_one_posSemidef {P : Matrix ι ι ℝ} {l : ℝ}
    (hP : P.PosDef) (hl : 0 < l) (hle : ∀ i, hP.1.eigenvalues i ≤ l) :
    (P⁻¹ - l⁻¹ • (1 : Matrix ι ι ℝ)).PosSemidef := by
  have hPh : P.IsHermitian := hP.1
  let U : Matrix ι ι ℝ := hPh.eigenvectorUnitary
  have hU1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hPh.eigenvectorUnitary.2
  have hinv := spectral_inv_eq hP
  have hdiff : P⁻¹ - l⁻¹ • (1 : Matrix ι ι ℝ) =
      U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹ - l⁻¹) * Uᴴ := by
    rw [hinv]
    calc
      U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹) * Uᴴ - l⁻¹ • (1 : Matrix ι ι ℝ)
          = U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹) * Uᴴ -
              U * (l⁻¹ • (1 : Matrix ι ι ℝ)) * Uᴴ := by
              congr 1
              rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU1]
      _ = U * (Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹) -
              l⁻¹ • (1 : Matrix ι ι ℝ)) * Uᴴ := by
              rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = U * Matrix.diagonal (fun i => (hPh.eigenvalues i)⁻¹ - l⁻¹) * Uᴴ := by
              congr 2
              ext i j
              by_cases hij : i = j
              · subst hij; simp
              · simp [hij]
  rw [hdiff]
  refine (posSemidef_diagonal fun i => ?_).mul_mul_conjTranspose_same U
  have hpos := hP.eigenvalues_pos i
  have := (inv_le_inv₀ hl hpos).mpr (hle i)
  linarith

private lemma trace_inv_mul_lyapunov {A P Q : Matrix ι ι ℝ}
    (hP : P.PosDef) (hlyap : A * P + P * Aᵀ = -Q) :
    (P⁻¹ * Q).trace = -2 * A.trace := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hQ : Q = -(A * P + P * Aᵀ) := by
    have := congr_arg Neg.neg hlyap
    simpa using this.symm
  rw [hQ, Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_add, Matrix.trace_add]
  have h1 : (P⁻¹ * (A * P)).trace = A.trace := by
    calc
      (P⁻¹ * (A * P)).trace = (P⁻¹ * A * P).trace := by rw [Matrix.mul_assoc]
      _ = (P * P⁻¹ * A).trace := Matrix.trace_mul_cycle P⁻¹ A P
      _ = A.trace := by rw [hPP, Matrix.one_mul]
  have h2 : (P⁻¹ * (P * Aᵀ)).trace = A.trace := by
    rw [← Matrix.mul_assoc, hPP', Matrix.one_mul, Matrix.trace_transpose]
  rw [h1, h2]
  ring

private lemma trace_inv_mul_dual {A W : Matrix ι ι ℝ} (hW : W.PosDef) :
    (W⁻¹ * (Aᵀ * W + W * A)).trace = 2 * A.trace := by
  have hdet : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det W).mp hW.isUnit
  have hWW : W * W⁻¹ = 1 := Matrix.mul_nonsing_inv W hdet
  have hWW' : W⁻¹ * W = 1 := Matrix.nonsing_inv_mul W hdet
  rw [Matrix.mul_add, Matrix.trace_add]
  have h1 : (W⁻¹ * (Aᵀ * W)).trace = A.trace := by
    calc
      (W⁻¹ * (Aᵀ * W)).trace = (W⁻¹ * Aᵀ * W).trace := by rw [Matrix.mul_assoc]
      _ = (W * W⁻¹ * Aᵀ).trace := Matrix.trace_mul_cycle W⁻¹ Aᵀ W
      _ = A.trace := by rw [hWW, Matrix.one_mul, Matrix.trace_transpose]
  have h2 : (W⁻¹ * (W * A)).trace = A.trace := by
    rw [← Matrix.mul_assoc, hWW', Matrix.one_mul]
  rw [h1, h2]
  ring

-- Vieta relation for a multiset product of monic linear factors over ℂ.
private lemma multiset_prod_X_sub_C_monic (s : Multiset ℂ) :
    (s.map fun r => Polynomial.X - Polynomial.C r).prod.Monic := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact (Polynomial.monic_X_sub_C a).mul ih

private lemma multiset_prod_X_sub_C_natDegree (s : Multiset ℂ) :
    (s.map fun r => Polynomial.X - Polynomial.C r).prod.natDegree = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C a)
      (multiset_prod_X_sub_C_monic s), Polynomial.natDegree_X_sub_C, ih]
    omega

private lemma multiset_prod_X_sub_C_coeff_pred (s : Multiset ℂ) (hs : s ≠ 0) :
    (s.map fun r => Polynomial.X - Polynomial.C r).prod.coeff (s.card - 1) = -s.sum := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    by_cases hs0 : s = 0
    · subst hs0
      simp
    · rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, Multiset.sum_cons]
      have hscard : 1 ≤ s.card := Nat.pos_of_ne_zero (Multiset.card_eq_zero.not.mpr hs0)
      set q := (s.map fun r => Polynomial.X - Polynomial.C r).prod
      have hqm : q.Monic := multiset_prod_X_sub_C_monic s
      have hqdeg : q.natDegree = s.card := multiset_prod_X_sub_C_natDegree s
      have hqlead : q.coeff s.card = 1 := by
        rw [← hqdeg]
        exact hqm.leadingCoeff
      have hqpred : q.coeff (s.card - 1) = -s.sum := ih hs0
      have hstep : ((Polynomial.X - Polynomial.C a) * q).coeff s.card =
          q.coeff (s.card - 1) - a * q.coeff s.card := by
        have hsc : s.card = (s.card - 1) + 1 := (Nat.sub_add_cancel hscard).symm
        rw [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
        congr 1
        rw [hsc, Polynomial.coeff_X_mul]
        simp
      simp only [Nat.add_sub_cancel]
      rw [hstep, hqpred, hqlead]
      ring

private lemma trace_neg_of_hurwitz [Nonempty ι] {B : Matrix ι ι ℝ}
    (hB : ∀ z ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)), z.re < 0) :
    B.trace < 0 := by
  let BC : Matrix ι ι ℂ := B.map (algebraMap ℝ ℂ)
  let p : Polynomial ℂ := BC.charpoly
  have hpm : p.Monic := Matrix.charpoly_monic BC
  have hpdeg : p.natDegree = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim BC
  have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hroots_card : p.roots.card = Fintype.card ι := by
    rw [Polynomial.Splits.natDegree_eq_card_roots hsplit] at hpdeg
    exact hpdeg
  have hpeq : p = (p.roots.map fun r => Polynomial.X - Polynomial.C r).prod := by
    have := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hpm
      (by rw [hroots_card, hpdeg])
    exact this.symm
  have hroots_ne : p.roots ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hroots_card
    omega
  have htrC : BC.trace = p.roots.sum := by
    rw [Matrix.trace_eq_neg_charpoly_coeff BC]
    change -p.coeff (Fintype.card ι - 1) = p.roots.sum
    rw [← hroots_card]
    have hcoeff : p.coeff (p.roots.card - 1) =
        (p.roots.map fun r => Polynomial.X - Polynomial.C r).prod.coeff (p.roots.card - 1) :=
      congr_arg (fun q => q.coeff (p.roots.card - 1)) hpeq
    rw [hcoeff, multiset_prod_X_sub_C_coeff_pred p.roots hroots_ne, neg_neg]
  have htr_re : B.trace = (BC.trace).re := by
    simp [BC, Matrix.trace]
  rw [htr_re, htrC]
  have hsum_re : ∀ s : Multiset ℂ, s ≠ 0 → (∀ r ∈ s, r.re < 0) → s.sum.re < 0 := by
    intro s hs hall
    induction s using Multiset.induction_on with
    | empty => exact absurd rfl hs
    | cons a t ih =>
      rw [Multiset.sum_cons, Complex.add_re]
      have ha : a.re < 0 := hall a (Multiset.mem_cons_self a t)
      by_cases ht : t = 0
      · subst ht; simpa using ha
      · have htr := ih ht (fun r hr => hall r (Multiset.mem_cons_of_mem hr))
        linarith
  refine hsum_re p.roots hroots_ne fun r hr => hB r ?_
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  exact Polynomial.isRoot_of_mem_roots hr

private lemma charpoly_conj_unitary {A : Matrix ι ι ℝ} (U : Matrix.unitaryGroup ι ℝ) :
    ((U : Matrix ι ι ℝ)ᴴ * A * (U : Matrix ι ι ℝ)).charpoly = A.charpoly := by
  have hU : (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  calc
    ((U : Matrix ι ι ℝ)ᴴ * A * (U : Matrix ι ι ℝ)).charpoly
        = ((U : Matrix ι ι ℝ)ᴴ * (A * (U : Matrix ι ι ℝ))).charpoly := by rw [Matrix.mul_assoc]
    _ = ((A * (U : Matrix ι ι ℝ)) * (U : Matrix ι ι ℝ)ᴴ).charpoly := Matrix.charpoly_mul_comm _ _
    _ = (A * ((U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)ᴴ)).charpoly := by rw [Matrix.mul_assoc]
    _ = A.charpoly := by rw [hU, Matrix.mul_one]

private lemma charpoly_submatrix_equiv {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix ι ι ℝ} (e : α ≃ ι) :
    (A.submatrix e e).charpoly = A.charpoly := by
  have h := Matrix.charpoly_reindex e.symm A
  simpa [Matrix.reindex_apply] using h

private lemma trace_conj_unitary {A : Matrix ι ι ℝ} (U : Matrix.unitaryGroup ι ℝ) :
    ((U : Matrix ι ι ℝ)ᴴ * A * (U : Matrix ι ι ℝ)).trace = A.trace := by
  have hU : (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp U.2
  calc
    ((U : Matrix ι ι ℝ)ᴴ * A * (U : Matrix ι ι ℝ)).trace
        = ((U : Matrix ι ι ℝ)ᴴ * (A * (U : Matrix ι ι ℝ))).trace := by rw [Matrix.mul_assoc]
    _ = ((A * (U : Matrix ι ι ℝ)) * (U : Matrix ι ι ℝ)ᴴ).trace := Matrix.trace_mul_comm _ _
    _ = (A * ((U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)ᴴ)).trace := by rw [Matrix.mul_assoc]
    _ = A.trace := by rw [hU, Matrix.mul_one]

-- Any maximizer P in F with -2 tr(A) ≤ tr(Q) must be strictly positive definite.
private lemma maximizer_posDef [Nonempty ι] {A P : Matrix ι ι ℝ}
    (hA : ∀ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), z.re < 0)
    (hP : P.PosSemidef) (hP1 : (1 - P).PosSemidef)
    (hQ : (-(A * P + P * Aᵀ)).PosSemidef)
    (htr : -2 * A.trace ≤ (-(A * P + P * Aᵀ)).trace) :
    P.PosDef := by
  have hPh : P.IsHermitian := hP.1
  let U : Matrix ι ι ℝ := hPh.eigenvectorUnitary
  have hU2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hPh.eigenvectorUnitary.2
  have hd_nonneg : ∀ i, 0 ≤ hPh.eigenvalues i := hP.eigenvalues_nonneg
  have hd_le1 : ∀ i, hPh.eigenvalues i ≤ 1 := by
    intro i
    have hconj : (Uᴴ * (1 - P) * U).PosSemidef := hP1.conjTranspose_mul_mul_same U
    have hd := posSemidef_diag_nonneg hconj i
    have heq : Uᴴ * (1 - P) * U = 1 - Matrix.diagonal hPh.eigenvalues := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]
      exact congr_arg ((1 : Matrix ι ι ℝ) - ·) (spectral_conj_real hPh)
    rw [heq] at hd
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at hd
    linarith
  by_contra hnotpd
  have hzero_exists : ∃ i, ¬ 0 < hPh.eigenvalues i := by
    by_contra hall
    push Not at hall
    apply hnotpd
    rw [hP.posDef_iff_det_ne_zero, hPh.det_eq_prod_eigenvalues]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => (hall i).ne'
  let Pos := {i : ι // 0 < hPh.eigenvalues i}
  let Zero := {i : ι // ¬ 0 < hPh.eigenvalues i}
  have : Nonempty Zero := ⟨⟨hzero_exists.choose, hzero_exists.choose_spec⟩⟩
  let e : Pos ⊕ Zero ≃ ι := Equiv.sumCompl (fun i => 0 < hPh.eigenvalues i)
  let A' : Matrix ι ι ℝ := Uᴴ * A * U
  let Q' : Matrix ι ι ℝ := Uᴴ * (-(A * P + P * Aᵀ)) * U
  have hQ'_pos : Q'.PosSemidef := hQ.conjTranspose_mul_mul_same U
  have hQ'_eq : Q' = -(A' * Matrix.diagonal hPh.eigenvalues +
      Matrix.diagonal hPh.eigenvalues * A'ᵀ) := by
    have hA'T : A'ᵀ = Uᴴ * Aᵀ * U := by
      dsimp [A']
      simp [Matrix.transpose_mul, Matrix.mul_assoc]
    have h1 : Uᴴ * (A * P) * U = A' * Matrix.diagonal hPh.eigenvalues := by
      conv_lhs => rw [spectral_real hPh]
      change Uᴴ * (A * (U * Matrix.diagonal hPh.eigenvalues * Uᴴ)) * U = _
      calc
        Uᴴ * (A * (U * Matrix.diagonal hPh.eigenvalues * Uᴴ)) * U
            = (Uᴴ * A * U) * Matrix.diagonal hPh.eigenvalues * (Uᴴ * U) := by
                simp [Matrix.mul_assoc]
        _ = A' * Matrix.diagonal hPh.eigenvalues := by rw [hU2, Matrix.mul_one]
    have h2 : Uᴴ * (P * Aᵀ) * U = Matrix.diagonal hPh.eigenvalues * A'ᵀ := by
      rw [hA'T]
      conv_lhs => rw [spectral_real hPh]
      change Uᴴ * (U * Matrix.diagonal hPh.eigenvalues * Uᴴ * Aᵀ) * U = _
      calc
        Uᴴ * (U * Matrix.diagonal hPh.eigenvalues * Uᴴ * Aᵀ) * U
            = (Uᴴ * U) * Matrix.diagonal hPh.eigenvalues * (Uᴴ * Aᵀ * U) := by
                simp [Matrix.mul_assoc]
        _ = Matrix.diagonal hPh.eigenvalues * (Uᴴ * Aᵀ * U) := by rw [hU2, Matrix.one_mul]
    dsimp [Q']
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul, h1, h2]
  let At : Matrix (Pos ⊕ Zero) (Pos ⊕ Zero) ℝ := A'.submatrix e e
  let Qt : Matrix (Pos ⊕ Zero) (Pos ⊕ Zero) ℝ := Q'.submatrix e e
  have hQt_pos : Qt.PosSemidef := by
    rw [posSemidef_iff_real]
    obtain ⟨hsym, hq⟩ := posSemidef_iff_real.mp hQ'_pos
    refine ⟨by ext a b; exact congr_fun (congr_fun hsym (e a)) (e b), fun x => ?_⟩
    have hx := hq (x ∘ e.symm)
    have : x ⬝ᵥ Qt.mulVec x = (x ∘ e.symm) ⬝ᵥ Q'.mulVec (x ∘ e.symm) := by
      simp only [dotProduct, mulVec, Qt, Matrix.submatrix_apply, Function.comp_apply]
      rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Equiv.symm_apply_apply]
      congr 1
      rw [← Equiv.sum_comp e]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Equiv.symm_apply_apply]
    rw [this]
    exact hx
  have hQt_entry : ∀ a b : Pos ⊕ Zero,
      Qt a b = -(At a b * hPh.eigenvalues (e b) + hPh.eigenvalues (e a) * At b a) := by
    intro a b
    simp [Qt, At, hQ'_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hd_zero : ∀ j : Zero, hPh.eigenvalues (e (Sum.inr j)) = 0 := by
    intro j
    have hle0 : hPh.eigenvalues j.1 ≤ 0 := le_of_not_gt j.2
    have hge0 : 0 ≤ hPh.eigenvalues j.1 := hd_nonneg j.1
    change hPh.eigenvalues j.1 = 0
    exact le_antisymm hle0 hge0
  have hd_pos : ∀ i : Pos, 0 < hPh.eigenvalues (e (Sum.inl i)) := fun i => i.2
  have hQt_22 : ∀ j1 j2 : Zero, Qt (Sum.inr j1) (Sum.inr j2) = 0 := by
    intro j1 j2
    rw [hQt_entry, hd_zero j1, hd_zero j2]
    ring
  have hAt_21 : ∀ (j : Zero) (i : Pos), At (Sum.inr j) (Sum.inl i) = 0 := by
    intro j i
    have hq_entry : Qt (Sum.inr j) (Sum.inl i) = 0 := by
      obtain ⟨hsym, hq⟩ := posSemidef_iff_real.mp hQt_pos
      have hji : Qt (Sum.inl i) (Sum.inr j) = Qt (Sum.inr j) (Sum.inl i) := by
        have := congr_fun (congr_fun hsym (Sum.inr j)) (Sum.inl i)
        simpa [Matrix.transpose_apply] using this
      have hquad : ∀ t : ℝ, 0 ≤ Qt (Sum.inl i) (Sum.inl i) +
          2 * t * Qt (Sum.inr j) (Sum.inl i) := by
        intro t
        have h := hq (Pi.single (Sum.inl i) (1 : ℝ) + t • Pi.single (Sum.inr j) (1 : ℝ))
        have hev : (Pi.single (Sum.inl i) (1 : ℝ) + t • Pi.single (Sum.inr j) (1 : ℝ)) ⬝ᵥ
            Qt.mulVec (Pi.single (Sum.inl i) (1 : ℝ) + t • Pi.single (Sum.inr j) (1 : ℝ)) =
            Qt (Sum.inl i) (Sum.inl i) + 2 * t * Qt (Sum.inr j) (Sum.inl i) +
            t ^ 2 * Qt (Sum.inr j) (Sum.inr j) := by
          simp only [dotProduct, mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
            mul_add, add_mul, hji]
          ring
        rw [hev, hQt_22 j j] at h
        linarith
      by_contra hne
      have hval := hquad (-(Qt (Sum.inl i) (Sum.inl i) + 1) / (2 * Qt (Sum.inr j) (Sum.inl i)))
      have hsimp : 2 * (-(Qt (Sum.inl i) (Sum.inl i) + 1) / (2 * Qt (Sum.inr j) (Sum.inl i))) *
          Qt (Sum.inr j) (Sum.inl i) = -(Qt (Sum.inl i) (Sum.inl i) + 1) := by
        field_simp [hne]
      linarith
    rw [hQt_entry, hd_zero j] at hq_entry
    have hmul0 : At (Sum.inr j) (Sum.inl i) * hPh.eigenvalues (e (Sum.inl i)) = 0 := by
      linarith
    exact (mul_eq_zero.mp hmul0).resolve_right (hd_pos i).ne'
  let A11 : Matrix Pos Pos ℝ := Matrix.toBlocks₁₁ At
  let A12 : Matrix Pos Zero ℝ := Matrix.toBlocks₁₂ At
  let A22 : Matrix Zero Zero ℝ := Matrix.toBlocks₂₂ At
  have hAt_blocks : At = Matrix.fromBlocks A11 A12 0 A22 := by
    ext a b
    cases a with
    | inl i =>
      cases b with
      | inl i' => rfl
      | inr j' => rfl
    | inr j =>
      cases b with
      | inl i' => simpa using hAt_21 j i'
      | inr j' => rfl
  have hA22_hurwitz : ∀ z ∈ spectrum ℂ (A22.map (algebraMap ℝ ℂ)), z.re < 0 := by
    intro z hz
    apply hA z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hz ⊢
    have hchar : A.charpoly = A11.charpoly * A22.charpoly := by
      have h1 : A'.charpoly = A.charpoly := charpoly_conj_unitary hPh.eigenvectorUnitary
      have h2 : At.charpoly = A'.charpoly := charpoly_submatrix_equiv e
      rw [← h1, ← h2, hAt_blocks, Matrix.charpoly_fromBlocks_zero₂₁]
    rw [Matrix.charpoly_map, hchar, Polynomial.map_mul, Polynomial.IsRoot.def, Polynomial.eval_mul]
    rw [Matrix.charpoly_map, Polynomial.IsRoot.def] at hz
    simp [hz]
  have hA22_tr_neg : A22.trace < 0 := trace_neg_of_hurwitz hA22_hurwitz
  have hA_tr : A.trace = A11.trace + A22.trace := by
    have h1 : A'.trace = A.trace := trace_conj_unitary hPh.eigenvectorUnitary
    have h2 : At.trace = A'.trace := by
      simp only [Matrix.trace, Matrix.diag, At, Matrix.submatrix_apply]
      exact Equiv.sum_comp e (fun i => A' i i)
    have h3 : At.trace = A11.trace + A22.trace := by
      rw [hAt_blocks, Matrix.trace, Fintype.sum_sum_type]
      rfl
    linarith
  have hQ_tr : (-(A * P + P * Aᵀ)).trace = Qt.trace := by
    have h1 : Q'.trace = (-(A * P + P * Aᵀ)).trace := trace_conj_unitary hPh.eigenvectorUnitary
    have h2 : Qt.trace = Q'.trace := by
      simp only [Matrix.trace, Matrix.diag, Qt, Matrix.submatrix_apply]
      exact Equiv.sum_comp e (fun i => Q' i i)
    linarith
  have hQt_le : Qt.trace ≤ -2 * A11.trace := by
    rw [Matrix.trace, Fintype.sum_sum_type]
    have hsum2 : ∑ j : Zero, Matrix.diag Qt (Sum.inr j) = 0 :=
      Finset.sum_eq_zero fun j _ => hQt_22 j j
    rw [hsum2, add_zero]
    have hsum1 : ∑ i : Pos, Matrix.diag Qt (Sum.inl i) ≤
        ∑ i : Pos, -2 * A11 i i := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hdiag : Matrix.diag Qt (Sum.inl i) =
          -2 * A11 i i * hPh.eigenvalues (e (Sum.inl i)) := by
        change Qt (Sum.inl i) (Sum.inl i) = _
        rw [hQt_entry]
        change -(A11 i i * hPh.eigenvalues (e (Sum.inl i)) +
          hPh.eigenvalues (e (Sum.inl i)) * A11 i i) = _
        ring
      have hnn : 0 ≤ Qt (Sum.inl i) (Sum.inl i) := posSemidef_diag_nonneg hQt_pos (Sum.inl i)
      have hle : hPh.eigenvalues (e (Sum.inl i)) ≤ 1 := hd_le1 (e (Sum.inl i))
      have hpos : 0 < hPh.eigenvalues (e (Sum.inl i)) := hd_pos i
      have hA11_le : 0 ≤ -2 * A11 i i := by
        have : 0 ≤ (-2 * A11 i i) * hPh.eigenvalues (e (Sum.inl i)) := by
          rw [← hdiag]; exact hnn
        exact nonneg_of_mul_nonneg_left this hpos
      rw [hdiag]
      nlinarith
    calc
      ∑ i : Pos, Matrix.diag Qt (Sum.inl i) ≤ ∑ i : Pos, -2 * A11 i i := hsum1
      _ = -2 * A11.trace := by rw [← Finset.mul_sum]; rfl
  rw [hQ_tr, hA_tr] at htr
  linarith

-- Representation of a continuous linear functional on (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ
-- via symmetric matrices X, Y when evaluated on symmetric matrices U, V.
private lemma linear_repr_on_sym {m : ℕ}
    (g : ((Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ) →L[ℝ] ℝ) :
    ∃ (X Y : Matrix (Fin m) (Fin m) ℝ) (γ : ℝ),
      Xᵀ = X ∧ Yᵀ = Y ∧
      ∀ (U V : Matrix (Fin m) (Fin m) ℝ) (r : ℝ),
        Uᵀ = U → Vᵀ = V →
        g (U, V, r) = (X * U).trace + (Y * V).trace + γ * r := by
  let Eij : Fin m → Fin m → Matrix (Fin m) (Fin m) ℝ :=
    fun i j => (1 / 2 : ℝ) • (Matrix.single i j (1 : ℝ) + Matrix.single j i (1 : ℝ))
  let X : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => g (Eij i j, 0, 0)
  let Y : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => g (0, Eij i j, 0)
  let γ : ℝ := g (0, 0, 1)
  have hEsym : ∀ i j, Eij i j = Eij j i := fun i j => by
    dsimp [Eij]; rw [add_comm]
  have hXsym : Xᵀ = X := by ext i j; simp [X, hEsym]
  have hYsym : Yᵀ = Y := by ext i j; simp [Y, hEsym]
  have hdecomp : ∀ M : Matrix (Fin m) (Fin m) ℝ, Mᵀ = M →
      M = ∑ i : Fin m, ∑ j : Fin m, M i j • Eij i j := by
    intro M hM
    ext a b
    have hab : M b a = M a b := by
      have := congr_fun (congr_fun hM a) b
      simpa [Matrix.transpose_apply] using this
    simp only [Eij, Matrix.sum_apply, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Matrix.single_apply]
    have h1 : (∑ i : Fin m, ∑ j : Fin m, M i j * ((1 / 2 : ℝ) *
        ((if i = a ∧ j = b then (1 : ℝ) else 0) + (if j = a ∧ i = b then (1 : ℝ) else 0)))) =
        (1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin m, M i j *
          (if i = a ∧ j = b then (1 : ℝ) else 0)) +
        (1 / 2 : ℝ) * (∑ i : Fin m, ∑ j : Fin m, M i j *
          (if j = a ∧ i = b then (1 : ℝ) else 0)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_ <;> ring
    rw [h1]
    have hs1 : (∑ i : Fin m, ∑ j : Fin m, M i j * (if i = a ∧ j = b then (1 : ℝ) else 0)) =
        M a b := by
      simp [ite_and]
    have hs2 : (∑ i : Fin m, ∑ j : Fin m, M i j * (if j = a ∧ i = b then (1 : ℝ) else 0)) =
        M b a := by
      simp [ite_and]
    rw [hs1, hs2, hab]
    ring
  refine ⟨X, Y, γ, hXsym, hYsym, fun U V r hU hV => ?_⟩
  let u0 : (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ := (U, 0, 0)
  let v0 : (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ := (0, V, 0)
  let r0 : (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ := (0, 0, r)
  have hsplit : ((U : Fin m → Fin m → ℝ), (V : Fin m → Fin m → ℝ), r) = u0 + v0 + r0 := by
    apply Prod.ext
    · ext i j; change U i j = U i j + 0 + 0; ring
    · apply Prod.ext
      · ext i j; change V i j = 0 + V i j + 0; ring
      · change r = 0 + 0 + r; ring
  have hgeval : g (U, V, r) = g (u0 + v0 + r0) := congr_arg g hsplit
  rw [hgeval, map_add, map_add]
  let ι1 : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] ((Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ) :=
    { toFun := fun M => (M, 0, 0)
      map_add' := fun M N => by
        apply Prod.ext
        · rfl
        · apply Prod.ext <;> simp
      map_smul' := fun c M => by
        apply Prod.ext
        · rfl
        · apply Prod.ext <;> simp }
  let ι2 : Matrix (Fin m) (Fin m) ℝ →ₗ[ℝ] ((Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ) :=
    { toFun := fun M => (0, M, 0)
      map_add' := fun M N => by
        apply Prod.ext
        · simp
        · apply Prod.ext
          · rfl
          · simp
      map_smul' := fun c M => by
        apply Prod.ext
        · simp
        · apply Prod.ext
          · rfl
          · simp }
  have h1 : g u0 = (X * U).trace := by
    have hUeq : u0 =
        ∑ i : Fin m, ∑ j : Fin m, U i j • ((Eij i j, 0, 0) :
          (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ) := by
      calc
        u0 = ι1 U := rfl
        _ = ι1 (∑ i : Fin m, ∑ j : Fin m, U i j • Eij i j) := congr_arg ι1 (hdecomp U hU)
        _ = ∑ i : Fin m, ∑ j : Fin m, U i j • ((Eij i j, 0, 0) :
              (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ) := by
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [map_smul]
              rfl
    rw [hUeq, map_sum]
    simp_rw [map_sum, map_smul, smul_eq_mul]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, X, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hji : U j i = U i j := by
      have := congr_fun (congr_fun hU i) j
      simpa [Matrix.transpose_apply] using this
    rw [hji, mul_comm]
  have h2 : g v0 = (Y * V).trace := by
    have hVeq : v0 =
        ∑ i : Fin m, ∑ j : Fin m, V i j • ((0, Eij i j, 0) :
          (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ) := by
      calc
        v0 = ι2 V := rfl
        _ = ι2 (∑ i : Fin m, ∑ j : Fin m, V i j • Eij i j) := congr_arg ι2 (hdecomp V hV)
        _ = ∑ i : Fin m, ∑ j : Fin m, V i j • ((0, Eij i j, 0) :
              (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ) := by
              rw [map_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [map_smul]
              rfl
    rw [hVeq, map_sum]
    simp_rw [map_sum, map_smul, smul_eq_mul]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Y, Matrix.of_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hji : V j i = V i j := by
      have := congr_fun (congr_fun hV i) j
      simpa [Matrix.transpose_apply] using this
    rw [hji, mul_comm]
  have h3 : g r0 = γ * r := by
    have : r0 = r • ((0, 0, 1) : (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ) := by
      apply Prod.ext
      · ext i j; simp [r0]
      · apply Prod.ext
        · ext i j; simp [r0]
        · simp [r0]
    rw [this, map_smul, smul_eq_mul, mul_comm]
  rw [h1, h2, h3]

private lemma continuous_entry {m : ℕ} (i j : Fin m) :
    Continuous (fun M : Fin m → Fin m → ℝ => M i j) :=
  (continuous_apply j).comp (continuous_apply i)

private lemma isClosed_posSemidef (m : ℕ) :
    IsClosed {M : Fin m → Fin m → ℝ | (Matrix.of M).PosSemidef} := by
  have heq : {M : Fin m → Fin m → ℝ | (Matrix.of M).PosSemidef} =
      (⋂ i : Fin m, ⋂ j : Fin m, {M : Fin m → Fin m → ℝ | M j i = M i j}) ∩
      (⋂ x : Fin m → ℝ, {M : Fin m → Fin m → ℝ | 0 ≤ ∑ i, x i * ∑ j, M i j * x j}) := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, posSemidef_iff_real]
    constructor
    · rintro ⟨hsym, hq⟩
      refine ⟨fun i j => congr_fun (congr_fun hsym i) j, fun x => ?_⟩
      simpa [dotProduct, mulVec] using hq x
    · rintro ⟨hsym, hq⟩
      refine ⟨by ext i j; exact hsym i j, fun x => ?_⟩
      simpa [dotProduct, mulVec] using hq x
  rw [heq]
  refine IsClosed.inter ?_ ?_
  · refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    exact isClosed_eq (continuous_entry j i) (continuous_entry i j)
  · refine isClosed_iInter fun x => isClosed_le continuous_const ?_
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    refine continuous_finsetSum _ fun j _ => ?_
    exact (continuous_entry i j).mul continuous_const

private lemma isCompact_posSemidef_trace_le (m : ℕ) (M : ℝ) :
    IsCompact {P : Fin m → Fin m → ℝ | (Matrix.of P).PosSemidef ∧ (Matrix.of P).trace ≤ M} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have htr_closed : IsClosed {P : Fin m → Fin m → ℝ | (Matrix.of P).trace ≤ M} :=
      isClosed_le (continuous_finsetSum _ fun i _ => continuous_entry i i) continuous_const
    exact (isClosed_posSemidef m).inter htr_closed
  · rw [Metric.isBounded_iff_subset_closedBall (0 : Fin m → Fin m → ℝ)]
    refine ⟨max M 0, fun P ⟨hP, htr⟩ => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (le_max_right M 0)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (le_max_right M 0)]
    intro j
    rw [Real.norm_eq_abs]
    have habs : |P i j| ≤ (P i i + P j j) / 2 := posSemidef_abs_entry_le_diag_avg hP i j
    have hdi : P i i ≤ (Matrix.of P).trace :=
      Finset.single_le_sum (fun k _ => posSemidef_diag_nonneg hP k) (Finset.mem_univ i)
    have hdj : P j j ≤ (Matrix.of P).trace :=
      Finset.single_le_sum (fun k _ => posSemidef_diag_nonneg hP k) (Finset.mem_univ j)
    have hM : (Matrix.of P).trace ≤ max M 0 := le_trans htr (le_max_left M 0)
    linarith

private lemma lyapunov_continuous {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (fun P : Fin m → Fin m → ℝ =>
      (((Matrix.of P - 1 : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ),
       ((A * Matrix.of P + Matrix.of P * Aᵀ : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ),
       -2 * (A * Matrix.of P).trace)) := by
  have hmat : ∀ (L R : Matrix (Fin m) (Fin m) ℝ),
      Continuous (fun P : Fin m → Fin m → ℝ =>
        ((L * Matrix.of P * R : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ)) := by
    intro L R
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.mul_apply]
    refine continuous_finsetSum _ fun k _ => Continuous.mul ?_ continuous_const
    refine continuous_finsetSum _ fun l _ => continuous_const.mul ?_
    exact continuous_entry l k
  have h1 : Continuous (fun P : Fin m → Fin m → ℝ =>
      ((Matrix.of P - 1 : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_entry i j).sub continuous_const
  have h2 : Continuous (fun P : Fin m → Fin m → ℝ =>
      ((A * Matrix.of P + Matrix.of P * Aᵀ : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    change Continuous (fun P : Fin m → Fin m → ℝ =>
      (∑ k : Fin m, A i k * P k j) + ∑ k : Fin m, P i k * A j k)
    exact (continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_entry k j)).add
      (continuous_finsetSum _ fun k _ => (continuous_entry i k).mul continuous_const)
  have h3 : Continuous (fun P : Fin m → Fin m → ℝ => -2 * (A * Matrix.of P).trace) := by
    refine continuous_const.mul ?_
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
    exact continuous_const.mul (continuous_entry k i)
  exact h1.prodMk (h2.prodMk h3)

-- Core SDP duality step via Hahn-Banach separation.
private lemma exists_feasible_ge_neg_two_trace {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), z.re < 0) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      P.PosSemidef ∧ (1 - P).PosSemidef ∧ (-(A * P + P * Aᵀ)).PosSemidef ∧
      -2 * A.trace ≤ -2 * (A * P).trace := by
  let m := n + 1
  let F : Set (Fin m → Fin m → ℝ) :=
    {P | (Matrix.of P).PosSemidef ∧ (1 - Matrix.of P).PosSemidef ∧
      (-(A * Matrix.of P + Matrix.of P * Aᵀ)).PosSemidef}
  have hF_compact : IsCompact F := by
    have hF_sub : F ⊆ {P | (Matrix.of P).PosSemidef ∧ (Matrix.of P).trace ≤ (m : ℝ)} := by
      intro P ⟨hP, h1P, _⟩
      refine ⟨hP, ?_⟩
      have hle : ∀ i : Fin m, (Matrix.of P) i i ≤ 1 := fun i => by
        have := posSemidef_diag_nonneg h1P i
        simp only [Matrix.sub_apply, Matrix.one_apply_eq] at this
        linarith
      calc
        (Matrix.of P).trace = ∑ i : Fin m, (Matrix.of P) i i := rfl
        _ ≤ ∑ _i : Fin m, (1 : ℝ) := Finset.sum_le_sum fun i _ => hle i
        _ = (m : ℝ) := by simp [m]
    have hF_closed : IsClosed F := by
      have h1 : IsClosed {P : Fin m → Fin m → ℝ | (1 - Matrix.of P).PosSemidef} := by
        have hcont : Continuous (fun P : Fin m → Fin m → ℝ =>
            ((1 - Matrix.of P : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ)) :=
          continuous_pi fun i => continuous_pi fun j => continuous_const.sub (continuous_entry i j)
        exact (isClosed_posSemidef m).preimage hcont
      have h2 : IsClosed {P : Fin m → Fin m → ℝ |
          (-(A * Matrix.of P + Matrix.of P * Aᵀ)).PosSemidef} := by
        have hcont : Continuous (fun P : Fin m → Fin m → ℝ =>
            ((-(A * Matrix.of P + Matrix.of P * Aᵀ) : Matrix (Fin m) (Fin m) ℝ) :
              Fin m → Fin m → ℝ)) :=
          ((continuous_fst.comp continuous_snd).comp (lyapunov_continuous A)).neg
        exact (isClosed_posSemidef m).preimage hcont
      exact (isClosed_posSemidef m).inter (h1.inter h2)
    exact (isCompact_posSemidef_trace_le m m).of_isClosed_subset hF_closed hF_sub
  have h0F : (0 : Fin m → Fin m → ℝ) ∈ F := by
    refine ⟨posSemidef_zero, ?_, ?_⟩
    · simpa using (posSemidef_one : (1 : Matrix (Fin m) (Fin m) ℝ).PosSemidef)
    · simpa using (posSemidef_zero : (0 : Matrix (Fin m) (Fin m) ℝ).PosSemidef)
  have hobj_cont : Continuous (fun P : Fin m → Fin m → ℝ => -2 * (A * Matrix.of P).trace) :=
    (continuous_snd.comp continuous_snd).comp (lyapunov_continuous A)
  obtain ⟨Pstar, hPstar_mem, hPstar_max⟩ :=
    hF_compact.exists_isMaxOn ⟨0, h0F⟩ hobj_cont.continuousOn
  refine ⟨Pstar, hPstar_mem.1, hPstar_mem.2.1, hPstar_mem.2.2, ?_⟩
  set α : ℝ := -2 * (A * Matrix.of Pstar).trace
  by_contra hlt
  push Not at hlt
  change α < -2 * A.trace at hlt
  have hα_nonneg : 0 ≤ α := by
    have h0le : -2 * (A * Matrix.of (0 : Fin m → Fin m → ℝ)).trace ≤
        -2 * (A * Matrix.of Pstar).trace := hPstar_max h0F
    have h0val : -2 * (A * Matrix.of (0 : Fin m → Fin m → ℝ)).trace = 0 := by simp
    linarith
  have hAtr_neg : A.trace < 0 := trace_neg_of_hurwitz hA
  set β : ℝ := (α + -2 * A.trace) / 2
  have hαβ : α < β := by dsimp [β]; linarith
  have hβ_lt : β < -2 * A.trace := by dsimp [β]; linarith
  have hβ_pos : 0 < β := lt_of_le_of_lt hα_nonneg hαβ
  have hgap : 0 < -2 * A.trace - β := by linarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  set M : ℝ := (m : ℝ) * β / (-2 * A.trace - β) + 1
  have hM_pos : 0 < M := by positivity
  have hM_bound : β + (m : ℝ) * β / M < -2 * A.trace := by
    have hltM : (m : ℝ) * β / (-2 * A.trace - β) < M := by linarith
    have h1 : (m : ℝ) * β < M * (-2 * A.trace - β) := (div_lt_iff₀ hgap).mp hltM
    have h2 : (m : ℝ) * β / M < -2 * A.trace - β := (div_lt_iff₀ hM_pos).mpr (by linarith)
    linarith
  let E := (Fin m → Fin m → ℝ) × (Fin m → Fin m → ℝ) × ℝ
  let B_M : Set (Fin m → Fin m → ℝ) :=
    {P | (Matrix.of P).PosSemidef ∧ (Matrix.of P).trace ≤ M}
  let φ : (Fin m → Fin m → ℝ) → E := fun P =>
    (((Matrix.of P - 1 : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ),
     ((A * Matrix.of P + Matrix.of P * Aᵀ : Matrix (Fin m) (Fin m) ℝ) : Fin m → Fin m → ℝ),
     -2 * (A * Matrix.of P).trace)
  let K_M : Set E := φ '' B_M
  let C : Set E := {z : E | (-Matrix.of z.1).PosSemidef ∧ (-Matrix.of z.2.1).PosSemidef ∧ β ≤ z.2.2}
  have hBM_conv : Convex ℝ B_M := by
    intro P hP Q hQ a b ha hb hab
    refine ⟨(Matrix.PosSemidef.smul hP.1 ha).add (Matrix.PosSemidef.smul hQ.1 hb), ?_⟩
    have : (Matrix.of (a • P + b • Q)).trace =
        a * (Matrix.of P).trace + b * (Matrix.of Q).trace := by
      change (a • Matrix.of P + b • Matrix.of Q).trace = _
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    rw [this]
    nlinarith [hP.2, hQ.2]
  have hKM_conv : Convex ℝ K_M := by
    rintro _ ⟨P, hP, rfl⟩ _ ⟨Q, hQ, rfl⟩ a b ha hb hab
    refine ⟨a • P + b • Q, hBM_conv hP hQ ha hb hab, ?_⟩
    apply Prod.ext
    · ext i j
      change (a * P i j + b * Q i j) - (1 : Matrix (Fin m) (Fin m) ℝ) i j =
        a * (P i j - (1 : Matrix (Fin m) (Fin m) ℝ) i j) +
        b * (Q i j - (1 : Matrix (Fin m) (Fin m) ℝ) i j)
      calc
        a * P i j + b * Q i j - (1 : Matrix (Fin m) (Fin m) ℝ) i j
            = a * P i j + b * Q i j - (a + b) * (1 : Matrix (Fin m) (Fin m) ℝ) i j := by
                rw [hab, one_mul]
        _ = a * (P i j - (1 : Matrix (Fin m) (Fin m) ℝ) i j) +
            b * (Q i j - (1 : Matrix (Fin m) (Fin m) ℝ) i j) := by ring
    · apply Prod.ext
      · ext i j
        have hmat : A * Matrix.of (a • P + b • Q) + Matrix.of (a • P + b • Q) * Aᵀ =
            a • (A * Matrix.of P + Matrix.of P * Aᵀ) +
            b • (A * Matrix.of Q + Matrix.of Q * Aᵀ) := by
          change A * (a • Matrix.of P + b • Matrix.of Q) +
              (a • Matrix.of P + b • Matrix.of Q) * Aᵀ = _
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
            Matrix.smul_mul, Matrix.smul_mul, smul_add, smul_add]
          abel
        exact congr_fun (congr_fun hmat i) j
      · change -2 * (A * (a • Matrix.of P + b • Matrix.of Q)).trace =
          a * (-2 * (A * Matrix.of P).trace) + b * (-2 * (A * Matrix.of Q).trace)
        rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_add,
          Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
        ring
  have hKM_compact : IsCompact K_M :=
    (isCompact_posSemidef_trace_le m M).image (lyapunov_continuous A)
  have hC_conv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_, ?_⟩
    · have : -Matrix.of (a • x + b • y).1 = a • (-Matrix.of x.1) + b • (-Matrix.of y.1) := by
        ext i j
        change -(a * x.1 i j + b * y.1 i j) = a * (-x.1 i j) + b * (-y.1 i j)
        ring
      rw [this]
      exact (Matrix.PosSemidef.smul hx.1 ha).add (Matrix.PosSemidef.smul hy.1 hb)
    · have : -Matrix.of (a • x + b • y).2.1 =
          a • (-Matrix.of x.2.1) + b • (-Matrix.of y.2.1) := by
        ext i j
        change -(a * x.2.1 i j + b * y.2.1 i j) = a * (-x.2.1 i j) + b * (-y.2.1 i j)
        ring
      rw [this]
      exact (Matrix.PosSemidef.smul hx.2.1 ha).add (Matrix.PosSemidef.smul hy.2.1 hb)
    · change β ≤ a * x.2.2 + b * y.2.2
      nlinarith [hx.2.2, hy.2.2]
  have hC_closed : IsClosed C := by
    have h1 : IsClosed {z : E | (-Matrix.of z.1).PosSemidef} :=
      (isClosed_posSemidef m).preimage continuous_fst.neg
    have h2 : IsClosed {z : E | (-Matrix.of z.2.1).PosSemidef} :=
      (isClosed_posSemidef m).preimage (continuous_fst.comp continuous_snd).neg
    have h3 : IsClosed {z : E | β ≤ z.2.2} :=
      isClosed_le continuous_const (continuous_snd.comp continuous_snd)
    exact h1.inter (h2.inter h3)
  have hdisj : Disjoint K_M C := by
    rw [Set.disjoint_left]
    rintro _ ⟨P, hP, rfl⟩ ⟨hC1, hC2, hC3⟩
    have hP_in_F : P ∈ F := by
      refine ⟨hP.1, ?_, hC2⟩
      have : (1 - Matrix.of P : Matrix (Fin m) (Fin m) ℝ) = -(Matrix.of P - 1) := by abel
      rw [this]
      exact hC1
    have hle : -2 * (A * Matrix.of P).trace ≤ α := hPstar_max hP_in_F
    linarith
  obtain ⟨f, u, v, hfK, huv, hfC⟩ :=
    geometric_hahn_banach_compact_closed hKM_conv hKM_compact hC_conv hC_closed hdisj
  let g : E →L[ℝ] ℝ := -f
  obtain ⟨X, Y, γ, hXsym, hYsym, hg⟩ := linear_repr_on_sym g
  have hgK : ∀ P ∈ B_M, -u < (X * (Matrix.of P - 1)).trace +
      (Y * (A * Matrix.of P + Matrix.of P * Aᵀ)).trace + γ * (-2 * (A * Matrix.of P).trace) := by
    intro P hP
    have hPsym : (Matrix.of P)ᵀ = Matrix.of P := isHermitian_iff_transpose_eq.mp hP.1.1
    have h1sym : (Matrix.of P - 1)ᵀ = Matrix.of P - 1 := by simp [hPsym]
    have h2sym : (A * Matrix.of P + Matrix.of P * Aᵀ)ᵀ = A * Matrix.of P + Matrix.of P * Aᵀ := by
      simp [Matrix.transpose_add, Matrix.transpose_mul, hPsym, add_comm]
    have h := hfK (φ P) ⟨P, hP, rfl⟩
    have hneg : -u < g (φ P) := by simpa [g] using neg_lt_neg h
    rwa [hg _ _ _ h1sym h2sym] at hneg
  have hgC : ∀ (U V : Matrix (Fin m) (Fin m) ℝ) (r : ℝ),
      (-U).PosSemidef → (-V).PosSemidef → β ≤ r →
      (X * U).trace + (Y * V).trace + γ * r < -v := by
    intro U V r hU hV hr
    have hUsym : Uᵀ = U := by
      have := isHermitian_iff_transpose_eq.mp hU.1
      simpa using congr_arg Neg.neg this
    have hVsym : Vᵀ = V := by
      have := isHermitian_iff_transpose_eq.mp hV.1
      simpa using congr_arg Neg.neg this
    have h := hfC (U, V, r) ⟨hU, hV, hr⟩
    have hneg : g (U, V, r) < -v := by simpa [g] using neg_lt_neg h
    rwa [hg U V r hUsym hVsym] at hneg
  have h0C : γ * β < -v := by
    have h := hgC 0 0 β
      (by simpa using (posSemidef_zero : (0 : Matrix (Fin m) (Fin m) ℝ).PosSemidef))
      (by simpa using (posSemidef_zero : (0 : Matrix (Fin m) (Fin m) ℝ).PosSemidef))
      le_rfl
    simpa using h
  have hX_pos : X.PosSemidef := by
    rw [posSemidef_iff_real]
    refine ⟨hXsym, fun x => ?_⟩
    by_contra hneg
    push Not at hneg
    set q : ℝ := x ⬝ᵥ X.mulVec x
    have hq_neg : q < 0 := hneg
    set s : ℝ := (-v - γ * β + 1) / (-q)
    have hs_pos : 0 < s := div_pos (by linarith) (by linarith)
    have hU : (-(-(s • Matrix.vecMulVec x x))).PosSemidef := by
      simpa using (posSemidef_vecMulVec x).smul hs_pos.le
    have h := hgC (-(s • Matrix.vecMulVec x x)) 0 β hU
      (by simpa using (posSemidef_zero : (0 : Matrix (Fin m) (Fin m) ℝ).PosSemidef)) le_rfl
    have htrX : (X * (-(s • Matrix.vecMulVec x x))).trace = -s * q := by
      rw [Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      have hvec : (X * Matrix.vecMulVec x x).trace = q := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
          q, dotProduct, mulVec]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hvec]; ring
    simp only [Matrix.mul_zero, Matrix.trace_zero, add_zero] at h
    rw [htrX] at h
    have hsq : s * (-q) = -v - γ * β + 1 := div_mul_cancel₀ _ (by linarith)
    linarith
  have hY_pos : Y.PosSemidef := by
    rw [posSemidef_iff_real]
    refine ⟨hYsym, fun x => ?_⟩
    by_contra hneg
    push Not at hneg
    set q : ℝ := x ⬝ᵥ Y.mulVec x
    have hq_neg : q < 0 := hneg
    set s : ℝ := (-v - γ * β + 1) / (-q)
    have hs_pos : 0 < s := div_pos (by linarith) (by linarith)
    have hV : (-(-(s • Matrix.vecMulVec x x))).PosSemidef := by
      simpa using (posSemidef_vecMulVec x).smul hs_pos.le
    have h := hgC 0 (-(s • Matrix.vecMulVec x x)) β
      (by simpa using (posSemidef_zero : (0 : Matrix (Fin m) (Fin m) ℝ).PosSemidef)) hV le_rfl
    have htrY : (Y * (-(s • Matrix.vecMulVec x x))).trace = -s * q := by
      rw [Matrix.mul_neg, Matrix.trace_neg, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      have hvec : (Y * Matrix.vecMulVec x x).trace = q := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
          q, dotProduct, mulVec]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hvec]; ring
    simp only [Matrix.mul_zero, Matrix.trace_zero, zero_add] at h
    rw [htrY] at h
    have hsq : s * (-q) = -v - γ * β + 1 := div_mul_cancel₀ _ (by linarith)
    linarith
  have h0BM : (0 : Fin m → Fin m → ℝ) ∈ B_M :=
    ⟨posSemidef_zero, by simpa using hM_pos.le⟩
  have hK0 := hgK 0 h0BM
  simp only [Matrix.of_zero, zero_sub, Matrix.mul_neg, Matrix.mul_one, Matrix.trace_neg,
    Matrix.zero_mul, add_zero, Matrix.trace_zero, mul_zero] at hK0
  set μ : ℝ := -γ
  have hXtr_lt : X.trace < μ * β := by
    have : γ * β < -X.trace := by linarith
    dsimp [μ]; linarith
  have hμ_pos : 0 < μ := by
    have hXtr_nn : 0 ≤ X.trace := posSemidef_trace_nonneg hX_pos
    have : 0 < μ * β := lt_of_le_of_lt hXtr_nn hXtr_lt
    exact pos_of_mul_pos_left this hβ_pos.le
  let X' : Matrix (Fin m) (Fin m) ℝ := μ⁻¹ • X
  let Y' : Matrix (Fin m) (Fin m) ℝ := μ⁻¹ • Y
  let W : Matrix (Fin m) (Fin m) ℝ := 1 + Y'
  have hX'_pos : X'.PosSemidef := hX_pos.smul (inv_pos.mpr hμ_pos).le
  have hY'_pos : Y'.PosSemidef := hY_pos.smul (inv_pos.mpr hμ_pos).le
  have hX'_tr_lt : X'.trace < β := by
    rw [Matrix.trace_smul, smul_eq_mul]
    have : μ⁻¹ * X.trace < μ⁻¹ * (μ * β) := mul_lt_mul_of_pos_left hXtr_lt (inv_pos.mpr hμ_pos)
    simpa [inv_mul_cancel_left₀ hμ_pos.ne'] using this
  let Z : Matrix (Fin m) (Fin m) ℝ := X' + (β / M) • 1 + Aᵀ * W + W * A
  have hZ_sym : Zᵀ = Z := by
    have hX's : X'ᵀ = X' := isHermitian_iff_transpose_eq.mp hX'_pos.1
    have hY's : Y'ᵀ = Y' := isHermitian_iff_transpose_eq.mp hY'_pos.1
    have hWs : Wᵀ = W := by simp [W, hY's]
    dsimp [Z]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.transpose_mul, Matrix.transpose_transpose, hX's, hWs]
    abel
  have hZ_pos : Z.PosSemidef := by
    rw [posSemidef_iff_real]
    refine ⟨hZ_sym, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · have hx2 : 0 < x ⬝ᵥ x := by
        have ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
        exact lt_of_lt_of_le (mul_self_pos.mpr hi)
          (Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
      set c : ℝ := M / (x ⬝ᵥ x)
      have hc_pos : 0 < c := div_pos hM_pos hx2
      let P : Matrix (Fin m) (Fin m) ℝ := c • Matrix.vecMulVec x x
      have hP_pos : P.PosSemidef := (posSemidef_vecMulVec x).smul hc_pos.le
      have hP_tr : P.trace = M := by
        dsimp [P]
        rw [Matrix.trace_smul, smul_eq_mul]
        have : (Matrix.vecMulVec x x).trace = x ⬝ᵥ x := rfl
        rw [this]
        dsimp [c]
        exact div_mul_cancel₀ M hx2.ne'
      have hP_mem : (P : Fin m → Fin m → ℝ) ∈ B_M := ⟨hP_pos, hP_tr.le⟩
      have hKP : -u < (X * (P - 1)).trace + (Y * (A * P + P * Aᵀ)).trace +
          γ * (-2 * (A * P).trace) := hgK P hP_mem
      have hbound : -μ * β < (X * P).trace - X.trace +
          (Y * (A * P + P * Aᵀ)).trace + 2 * μ * (A * P).trace := by
        have h1 : (X * (P - 1)).trace = (X * P).trace - X.trace := by
          rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub]
        have h2 : γ * (-2 * (A * P).trace) = 2 * μ * (A * P).trace := by
          dsimp [μ]; ring
        rw [h1, h2] at hKP
        have h3 : -μ * β < -u := by dsimp [μ]; linarith
        linarith
      have hP_sym : Pᵀ = P := isHermitian_iff_transpose_eq.mp hP_pos.1
      have htr_id : ((X' + Aᵀ * W + W * A) * P).trace =
          μ⁻¹ * ((X * P).trace + (Y * (A * P + P * Aᵀ)).trace + 2 * μ * (A * P).trace) := by
        have hY1 : (Y' * (A * P + P * Aᵀ)).trace = ((Aᵀ * Y' + Y' * A) * P).trace := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add]
          have ha : (Y' * (A * P)).trace = (Y' * A * P).trace := by rw [Matrix.mul_assoc]
          have hb : (Y' * (P * Aᵀ)).trace = (Aᵀ * Y' * P).trace := by
            rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
          rw [ha, hb, add_comm]
        have hA2 : 2 * (A * P).trace = ((Aᵀ + A) * P).trace := by
          rw [Matrix.add_mul, Matrix.trace_add]
          have hAT : (Aᵀ * P).trace = (A * P).trace := by
            rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, hP_sym,
              Matrix.trace_mul_comm]
          rw [hAT]; ring
        have hWexpand : X' + Aᵀ * W + W * A = X' + (Aᵀ + A) + (Aᵀ * Y' + Y' * A) := by
          dsimp [W]
          simp [Matrix.mul_add, Matrix.add_mul]
          abel
        rw [hWexpand, Matrix.add_mul, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add,
          ← hY1, ← hA2]
        dsimp [X', Y']
        simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
        field_simp [hμ_pos.ne']
        ring
      have hZP : 0 < (Z * P).trace := by
        have h1 : (Z * P).trace = ((X' + Aᵀ * W + W * A) * P).trace + (β / M) * P.trace := by
          have : Z = (X' + Aᵀ * W + W * A) + (β / M) • 1 := by dsimp [Z]; abel
          rw [this, Matrix.add_mul, Matrix.trace_add, Matrix.smul_mul, Matrix.one_mul,
            Matrix.trace_smul, smul_eq_mul]
        rw [h1, htr_id, hP_tr, div_mul_cancel₀ β hM_pos.ne']
        have hXnn : 0 ≤ X.trace := posSemidef_trace_nonneg hX_pos
        have h2 : -μ * β < (X * P).trace + (Y * (A * P + P * Aᵀ)).trace +
            2 * μ * (A * P).trace := by linarith
        have h3 : -β < μ⁻¹ * ((X * P).trace + (Y * (A * P + P * Aᵀ)).trace +
            2 * μ * (A * P).trace) := by
          have := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hμ_pos)
          simpa [inv_mul_cancel_left₀ hμ_pos.ne'] using this
        linarith
      have hZP_eq : (Z * P).trace = c * (x ⬝ᵥ Z.mulVec x) := by
        dsimp [P]
        rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        congr 1
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
          dotProduct, mulVec]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [hZP_eq] at hZP
      exact (pos_of_mul_pos_right hZP hc_pos.le).le
  have hWsub : (W - 1).PosSemidef := by
    have : W - 1 = Y' := by dsimp [W]; abel
    rw [this]; exact hY'_pos
  have hW_pd : W.PosDef := posDef_of_sub_one_posSemidef hWsub
  have hWinv_pd : W⁻¹.PosDef := hW_pd.inv
  have h1subWinv : (1 - W⁻¹).PosSemidef := one_sub_inv_posSemidef hWsub
  have hX'b_pos : (X' + (β / M) • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    hX'_pos.add (posSemidef_one.smul (div_pos hβ_pos hM_pos).le)
  have hstep1 : 0 ≤ (W⁻¹ * Z).trace := posSemidef_trace_mul_nonneg hWinv_pd.posSemidef hZ_pos
  have hstep1' : -2 * A.trace ≤ (W⁻¹ * (X' + (β / M) • 1)).trace := by
    have hZeq : Z = (X' + (β / M) • 1) + (Aᵀ * W + W * A) := by dsimp [Z]; abel
    rw [hZeq, Matrix.mul_add, Matrix.trace_add, trace_inv_mul_dual hW_pd] at hstep1
    linarith
  have hstep2 : (W⁻¹ * (X' + (β / M) • 1)).trace ≤ (X' + (β / M) • 1).trace := by
    have hnn := posSemidef_trace_mul_nonneg h1subWinv hX'b_pos
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub] at hnn
    linarith
  have hstep3 : (X' + (β / M) • (1 : Matrix (Fin m) (Fin m) ℝ)).trace < β + (m : ℝ) * β / M := by
    rw [Matrix.trace_add]
    have htr1 : ((β / M) • (1 : Matrix (Fin m) (Fin m) ℝ)).trace = (m : ℝ) * β / M := by
      rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
      ring
    linarith
  linarith

private lemma isGreatest_spectrum_real_hermitian {n : ℕ}
    {P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hPh : P.IsHermitian) :
    IsGreatest (spectrum ℝ P) (Finset.univ.sup' Finset.univ_nonempty hPh.eigenvalues) := by
  have hchar : P.charpoly = (Matrix.diagonal hPh.eigenvalues).charpoly := by
    have h1 := charpoly_conj_unitary (A := P) hPh.eigenvectorUnitary
    rw [← h1]
    exact congr_arg Matrix.charpoly (spectral_conj_real hPh)
  have hmem : ∀ r : ℝ, r ∈ spectrum ℝ P ↔ ∃ i, hPh.eigenvalues i = r := by
    intro r
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hchar, Matrix.charpoly_diagonal,
      Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff]
    simp only [Finset.mem_univ, true_and, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  set l := Finset.univ.sup' Finset.univ_nonempty hPh.eigenvalues
  obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hPh.eigenvalues
  refine ⟨(hmem l).mpr ⟨i0, hi0.symm⟩, fun r hr => ?_⟩
  obtain ⟨i, rfl⟩ := (hmem r).mp hr
  exact Finset.le_sup' hPh.eigenvalues (Finset.mem_univ i)

end Helpers

private theorem main_proof : ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    (∀ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)), z.re < 0) →
    ∃ (Q P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (l : ℝ),
      Q.PosSemidef ∧ P.PosDef ∧ A * P + P * A.transpose = -Q ∧
      IsGreatest (spectrum ℝ P) l ∧ -2 * A.trace = Q.trace / l := by
  intro n A hA
  obtain ⟨P, hP_psd, h1P, hQ_psd, htr_le⟩ := exists_feasible_ge_neg_two_trace A hA
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := -(A * P + P * Aᵀ)
  have hlyap : A * P + P * Aᵀ = -Q := by simp [Q]
  have hQ_tr_ge : -2 * A.trace ≤ Q.trace := by
    have : Q.trace = -2 * (A * P).trace := by
      dsimp [Q]
      rw [Matrix.trace_neg, Matrix.trace_add]
      have hPsym : Pᵀ = P := isHermitian_iff_transpose_eq.mp hP_psd.1
      have h1 : (P * Aᵀ).trace = (A * P).trace := by
        rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose, hPsym]
      rw [h1]; ring
    rw [this]; exact htr_le
  have hP_pd : P.PosDef := maximizer_posDef hA hP_psd h1P hQ_psd hQ_tr_ge
  set l : ℝ := Finset.univ.sup' Finset.univ_nonempty hP_pd.1.eigenvalues
  have hl_great : IsGreatest (spectrum ℝ P) l := isGreatest_spectrum_real_hermitian hP_pd.1
  obtain ⟨i0, _, hi0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hP_pd.1.eigenvalues
  have hl_eq : l = hP_pd.1.eigenvalues i0 := hi0
  have hl_pos : 0 < l := by
    rw [hl_eq]
    exact hP_pd.eigenvalues_pos i0
  have hl_le1 : l ≤ 1 := by
    rw [hl_eq]
    have hPh := hP_pd.1
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := hPh.eigenvectorUnitary
    have hU2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hPh.eigenvectorUnitary.2
    have hconj : (Uᴴ * (1 - P) * U).PosSemidef := h1P.conjTranspose_mul_mul_same U
    have hd := posSemidef_diag_nonneg hconj i0
    have heq : Uᴴ * (1 - P) * U = 1 - Matrix.diagonal hPh.eigenvalues := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]
      exact congr_arg ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - ·) (spectral_conj_real hPh)
    rw [heq] at hd
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at hd
    linarith
  have hinv_ge : (P⁻¹ - l⁻¹ • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).PosSemidef :=
    inv_sub_smul_one_posSemidef hP_pd hl_pos fun i =>
      Finset.le_sup' hP_pd.1.eigenvalues (Finset.mem_univ i)
  have hdiv_le : Q.trace / l ≤ -2 * A.trace := by
    have hnn := posSemidef_trace_mul_nonneg hinv_ge hQ_psd
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul,
      smul_eq_mul, trace_inv_mul_lyapunov hP_pd hlyap] at hnn
    rw [div_eq_inv_mul]
    linarith
  have hQ_tr_nn : 0 ≤ Q.trace := posSemidef_trace_nonneg hQ_psd
  have hge_div : Q.trace ≤ Q.trace / l := by
    rw [le_div_iff₀ hl_pos]
    nlinarith
  have heq : -2 * A.trace = Q.trace / l := by linarith
  exact ⟨Q, P, l, hQ_psd, hP_pd, hlyap, hl_great, heq⟩

end OMA.S_mo_310296

theorem OMA.solution : type_of% @OMA.S_mo_310296.main :=
  OMA.S_mo_310296.main_proof
