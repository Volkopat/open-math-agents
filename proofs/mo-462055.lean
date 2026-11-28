import OMAStatements.S_mo_462055
import Mathlib

namespace OMA.Mo462055

open Matrix Filter Topology
open scoped MatrixOrder

lemma quad_gram_pow_nonneg {n : ℕ} (x : Fin n → Fin n → ℝ) (k : ℕ) (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * v j * (∑ l : Fin n, x i l * x j l) ^ k := by
  induction k generalizing v with
  | zero =>
    have h : (∑ i : Fin n, ∑ j : Fin n, v i * v j * (∑ l : Fin n, x i l * x j l) ^ 0) =
        (∑ i : Fin n, v i) ^ 2 := by
      simp only [pow_zero, mul_one, sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [h]
    exact sq_nonneg _
  | succ k ih =>
    have h : (∑ i : Fin n, ∑ j : Fin n, v i * v j * (∑ l : Fin n, x i l * x j l) ^ (k + 1)) =
        ∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          (v i * x i l) * (v j * x j l) * (∑ r : Fin n, x i r * x j r) ^ k := by
      calc
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * (∑ l : Fin n, x i l * x j l) ^ (k + 1)
            = ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
                (v i * x i l) * (v j * x j l) * (∑ r : Fin n, x i r * x j r) ^ k := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              rw [pow_succ, ← mul_assoc, Finset.mul_sum]
              refine Finset.sum_congr rfl fun l _ => by ring
        _ = ∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n,
              (v i * x i l) * (v j * x j l) * (∑ r : Fin n, x i r * x j r) ^ k := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              (v i * x i l) * (v j * x j l) * (∑ r : Fin n, x i r * x j r) ^ k := Finset.sum_comm
    rw [h]
    exact Finset.sum_nonneg fun l _ => ih (fun i => v i * x i l)

lemma quad_exp_gram_nonneg {n : ℕ} (x : Fin n → Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) (v : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      v i * v j * Real.exp (2 * t * ∑ l : Fin n, x i l * x j l) := by
  let G : Fin n → Fin n → ℝ := fun i j => ∑ l : Fin n, x i l * x j l
  have hterm : ∀ i j : Fin n,
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (2 * t * G i j) ^ k / (Nat.factorial k : ℝ))
        atTop (nhds (Real.exp (2 * t * G i j))) := by
    intro i j
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (2 * t * G i j)).tendsto_sum_nat
  have hsum : Tendsto
      (fun N : ℕ => ∑ i : Fin n, ∑ j : Fin n, v i * v j *
        ∑ k ∈ Finset.range N, (2 * t * G i j) ^ k / (Nat.factorial k : ℝ))
      atTop
      (nhds (∑ i : Fin n, ∑ j : Fin n, v i * v j * Real.exp (2 * t * G i j))) :=
    tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
      (hterm i j).const_mul (v i * v j)
  refine ge_of_tendsto hsum (Eventually.of_forall fun N => ?_)
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, v i * v j *
        ∑ k ∈ Finset.range N, (2 * t * G i j) ^ k / (Nat.factorial k : ℝ)) =
      ∑ k ∈ Finset.range N, ((2 * t) ^ k / (Nat.factorial k : ℝ)) *
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * (G i j) ^ k := by
    calc
      ∑ i : Fin n, ∑ j : Fin n, v i * v j *
          ∑ k ∈ Finset.range N, (2 * t * G i j) ^ k / (Nat.factorial k : ℝ)
          = ∑ i : Fin n, ∑ j : Fin n, ∑ k ∈ Finset.range N,
              ((2 * t) ^ k / (Nat.factorial k : ℝ)) * (v i * v j * (G i j) ^ k) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [mul_pow]
            ring
      _ = ∑ i : Fin n, ∑ k ∈ Finset.range N, ∑ j : Fin n,
            ((2 * t) ^ k / (Nat.factorial k : ℝ)) * (v i * v j * (G i j) ^ k) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k ∈ Finset.range N, ∑ i : Fin n, ∑ j : Fin n,
            ((2 * t) ^ k / (Nat.factorial k : ℝ)) * (v i * v j * (G i j) ^ k) := Finset.sum_comm
      _ = ∑ k ∈ Finset.range N, ((2 * t) ^ k / (Nat.factorial k : ℝ)) *
            ∑ i : Fin n, ∑ j : Fin n, v i * v j * (G i j) ^ k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  rw [hswap]
  refine Finset.sum_nonneg fun k _ => ?_
  have hc : 0 ≤ (2 * t) ^ k / (Nat.factorial k : ℝ) := by positivity
  exact mul_nonneg hc (quad_gram_pow_nonneg x k v)

lemma gaussian_imp {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ} (hG : OMA.S_mo_462055.Gaussian C) :
    C.IsSymm ∧ (∀ i, C i i = 1) ∧ (∀ i j, 0 < C i j) ∧
      ∀ t : ℝ, 0 < t → (OMA.S_mo_462055.pw C t).PosSemidef := by
  rcases hG with ⟨x, hx⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, hx]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun l _ => by ring
  · intro i
    simp [hx]
  · intro i j
    rw [hx]
    exact Real.exp_pos _
  · intro t ht
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    have hsymm : (OMA.S_mo_462055.pw C t).IsHermitian := by
      ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, OMA.S_mo_462055.pw, Matrix.of_apply, hx]
      congr 2
      congr 1
      refine Finset.sum_congr rfl fun l _ => by ring
    refine ⟨hsymm, fun v => ?_⟩
    let w : Fin n → ℝ := fun i => v i * Real.exp (-t * ∑ l : Fin n, x i l ^ 2)
    have hq : star v ⬝ᵥ (OMA.S_mo_462055.pw C t).mulVec v =
        ∑ i : Fin n, ∑ j : Fin n,
          w i * w j * Real.exp (2 * t * ∑ l : Fin n, x i l * x j l) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [OMA.S_mo_462055.pw, Matrix.of_apply, hx, w]
      rw [← Real.exp_mul]
      have hexp : Real.exp (-(∑ l : Fin n, (x i l - x j l) ^ 2) * t) =
          Real.exp (-t * ∑ l : Fin n, x i l ^ 2) *
          Real.exp (-t * ∑ l : Fin n, x j l ^ 2) *
          Real.exp (2 * t * ∑ l : Fin n, x i l * x j l) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        have hsq : ∑ l : Fin n, (x i l - x j l) ^ 2 =
            (∑ l : Fin n, x i l ^ 2) + (∑ l : Fin n, x j l ^ 2) -
            2 * ∑ l : Fin n, x i l * x j l := by
          have : ∀ l : Fin n, (x i l - x j l) ^ 2 =
              x i l ^ 2 + x j l ^ 2 - 2 * (x i l * x j l) := fun l => by ring
          simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [hsq]
        ring
      rw [hexp]
      ring
    rw [hq]
    exact quad_exp_gram_nonneg x ht.le w

lemma neg_log_cnd {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hpos : ∀ i j, 0 < C i j)
    (hpsd : ∀ t : ℝ, 0 < t → (OMA.S_mo_462055.pw C t).PosSemidef)
    (v : Fin n → ℝ) (hv : ∑ i : Fin n, v i = 0) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, v i * v j * Real.log (C i j) := by
  have hzero : ∑ i : Fin n, ∑ j : Fin n, v i * v j = 0 := by
    have : (∑ i : Fin n, ∑ j : Fin n, v i * v j) = (∑ i : Fin n, v i) * (∑ j : Fin n, v j) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    rw [this, hv, zero_mul]
  have hderiv : ∀ i j : Fin n,
      Tendsto (fun t : ℝ => ((C i j) ^ t - 1) / t) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (Real.log (C i j))) := by
    intro i j
    have hfun : (fun t : ℝ => (C i j) ^ t) = fun t => Real.exp (Real.log (C i j) * t) := by
      funext t
      exact Real.rpow_def_of_pos (hpos i j) t
    have hd : HasDerivAt (fun t : ℝ => Real.exp (Real.log (C i j) * t)) (Real.log (C i j)) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => Real.log (C i j) * t) (Real.log (C i j) * 1) 0 :=
        (hasDerivAt_id (0 : ℝ)).const_mul (Real.log (C i j))
      have h2 := h1.exp
      simpa using h2
    rw [← hfun] at hd
    have hs := hd.tendsto_slope_zero_right
    have heq : (fun t : ℝ => ((C i j) ^ t - 1) / t) =
        fun t : ℝ => t⁻¹ * ((C i j) ^ t - (C i j) ^ (0 : ℝ)) := by
      funext t
      rw [Real.rpow_zero, div_eq_inv_mul]
    rw [heq]
    simpa [slope_def_field] using hs
  have hsum_lim :
      Tendsto (fun t : ℝ => ∑ i : Fin n, ∑ j : Fin n, v i * v j * (((C i j) ^ t - 1) / t))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ i : Fin n, ∑ j : Fin n, v i * v j * Real.log (C i j))) :=
    tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ =>
      (hderiv i j).const_mul (v i * v j)
  refine ge_of_tendsto hsum_lim ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have hnonneg : 0 ≤ star v ⬝ᵥ (OMA.S_mo_462055.pw C t).mulVec v :=
    ((Matrix.posSemidef_iff_dotProduct_mulVec).mp (hpsd t htpos)).2 v
  have heq : (∑ i : Fin n, ∑ j : Fin n, v i * v j * (((C i j) ^ t - 1) / t)) =
      (star v ⬝ᵥ (OMA.S_mo_462055.pw C t).mulVec v) / t := by
    have h1 : star v ⬝ᵥ (OMA.S_mo_462055.pw C t).mulVec v =
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * (C i j) ^ t := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        OMA.S_mo_462055.pw, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h1]
    have h2 : ∑ i : Fin n, ∑ j : Fin n, v i * v j * ((C i j) ^ t - 1) =
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * (C i j) ^ t := by
      have : ∀ i j : Fin n, v i * v j * ((C i j) ^ t - 1) =
          v i * v j * (C i j) ^ t - v i * v j := fun i j => by ring
      simp only [this, Finset.sum_sub_distrib, hzero, sub_zero]
    rw [← h2, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => by ring
  rw [heq]
  exact div_nonneg hnonneg htpos.le

lemma anch_posSemidef {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : C.IsSymm) (hdiag : ∀ i, C i i = 1) (hpos : ∀ i j, 0 < C i j)
    (hpsd : ∀ t : ℝ, 0 < t → (OMA.S_mo_462055.pw C t).PosSemidef) (a : Fin n) :
    (OMA.S_mo_462055.anch C a).PosSemidef := by
  have hL_symm : ∀ i j, Real.log (C i j) = Real.log (C j i) := by
    intro i j
    have h := congrFun (congrFun hsymm i) j
    simp only [Matrix.transpose_apply] at h
    rw [h]
  have hL_diag : ∀ i, Real.log (C i i) = 0 := fun i => by rw [hdiag i, Real.log_one]
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hB_herm : (OMA.S_mo_462055.anch C a).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, OMA.S_mo_462055.anch, Matrix.of_apply]
    rw [hL_symm j i, hL_symm j a, hL_symm a i]
    ring
  refine ⟨hB_herm, fun w => ?_⟩
  let S : ℝ := ∑ k : Fin n, w k
  let v : Fin n → ℝ := fun i => w i - if i = a then S else 0
  have hv_sum : ∑ i : Fin n, v i = 0 := by
    simp [v, S, Finset.sum_sub_distrib]
  have hnonneg := neg_log_cnd hpos hpsd v hv_sum
  have hrel : 2 * (star w ⬝ᵥ (OMA.S_mo_462055.anch C a).mulVec w) =
      ∑ i : Fin n, ∑ j : Fin n, v i * v j * Real.log (C i j) := by
    have hL : ∀ i j, v i * v j * Real.log (C i j) =
        w i * w j * Real.log (C i j)
        - (if i = a then S * w j * Real.log (C a j) else 0)
        - (if j = a then w i * S * Real.log (C i a) else 0)
        + (if i = a then if j = a then S * S * Real.log (C a a) else 0 else 0) := by
      intro i j
      by_cases hi : i = a <;> by_cases hj : j = a <;> simp [v, hi, hj] <;> ring
    have hsum_v : ∑ i : Fin n, ∑ j : Fin n, v i * v j * Real.log (C i j) =
        (∑ i : Fin n, ∑ j : Fin n, w i * w j * Real.log (C i j))
        - S * (∑ j : Fin n, w j * Real.log (C a j))
        - S * (∑ i : Fin n, w i * Real.log (C i a)) := by
      simp only [hL, hL_diag, mul_zero, ite_self, add_zero, Finset.sum_sub_distrib]
      have h1 : (∑ i : Fin n, ∑ j : Fin n, if i = a then S * w j * Real.log (C a j) else 0) =
          S * ∑ j : Fin n, w j * Real.log (C a j) := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      have h2 : (∑ i : Fin n, ∑ j : Fin n, if j = a then w i * S * Real.log (C i a) else 0) =
          S * ∑ i : Fin n, w i * Real.log (C i a) := by
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [h1, h2]
    rw [hsum_v]
    have hS1 : S * ∑ j : Fin n, w j * Real.log (C a j) =
        ∑ i : Fin n, ∑ j : Fin n, w i * w j * Real.log (C a j) := by
      dsimp only [S]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
    have hS2 : S * ∑ i : Fin n, w i * Real.log (C i a) =
        ∑ i : Fin n, ∑ j : Fin n, w i * w j * Real.log (C i a) := by
      dsimp only [S]
      rw [mul_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
    rw [hS1, hS2]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      OMA.S_mo_462055.anch, Matrix.of_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  linarith

lemma imp_gaussian {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : C.IsSymm) (hdiag : ∀ i, C i i = 1) (hpos : ∀ i j, 0 < C i j)
    (hpsd : ∀ t : ℝ, 0 < t → (OMA.S_mo_462055.pw C t).PosSemidef) :
    OMA.S_mo_462055.Gaussian C := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  · let a : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hB : (OMA.S_mo_462055.anch C a).PosSemidef :=
      anch_posSemidef hsymm hdiag hpos hpsd a
    obtain ⟨X, hX_sa, -, hX_sq⟩ :=
      CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hB.isHermitian
        (QuasispectrumRestricts.nnreal_of_nonneg hB.nonneg)
    have hX : Xᴴ * X = OMA.S_mo_462055.anch C a := by
      rw [show Xᴴ = X from hX_sa.star_eq]
      exact hX_sq
    refine ⟨fun i l => X l i, fun i j => ?_⟩
    have hgram : ∀ p q : Fin n, ∑ l : Fin n, X l p * X l q = OMA.S_mo_462055.anch C a p q := by
      intro p q
      have h := congrFun (congrFun hX p) q
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
    have hL_symm : ∀ p q, Real.log (C p q) = Real.log (C q p) := by
      intro p q
      have h := congrFun (congrFun hsymm p) q
      simp only [Matrix.transpose_apply] at h
      rw [h]
    have hdist : ∑ l : Fin n, (X l i - X l j) ^ 2 = -Real.log (C i j) := by
      have hexp : ∑ l : Fin n, (X l i - X l j) ^ 2 =
          (∑ l : Fin n, X l i * X l i) + (∑ l : Fin n, X l j * X l j) -
          2 * ∑ l : Fin n, X l i * X l j := by
        have : ∀ l : Fin n, (X l i - X l j) ^ 2 =
            X l i * X l i + X l j * X l j - 2 * (X l i * X l j) := fun l => by ring
        simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hexp, hgram i i, hgram j j, hgram i j]
      simp only [OMA.S_mo_462055.anch, Matrix.of_apply, hdiag i, hdiag j, Real.log_one]
      rw [hL_symm a i, hL_symm a j]
      ring
    rw [hdist, neg_neg, Real.exp_log (hpos i j)]

end OMA.Mo462055

theorem OMA.solution : type_of% @OMA.S_mo_462055.main := by
  intro n C
  exact ⟨OMA.Mo462055.gaussian_imp,
    fun ⟨hsymm, hdiag, hpos, hpsd⟩ => OMA.Mo462055.imp_gaussian hsymm hdiag hpos hpsd⟩
