import Mathlib

namespace OMA.S_arxiv_2210_11650

/-- A unital ring `A` is directly finite if `x * y = 1 → y * x = 1` for all `x, y ∈ A`. -/
def IsDirectlyFinite (A : Type*) [Ring A] : Prop :=
  ∀ x y : A, x * y = 1 → y * x = 1

/-- A unital ring `A` is stably finite if `M_n(A)` is directly finite for every `n : ℕ`. -/
def IsStablyFinite (A : Type*) [Ring A] : Prop :=
  ∀ n : ℕ, IsDirectlyFinite (Matrix (Fin n) (Fin n) A)

/-- The asymptotic-rank-zero kernel `Ker(ρ_U)` inside `∏_k M_{n_k}(F)` for an ultrafilter
`U` on `ℕ` and a dimension sequence `n : ℕ → ℕ`. -/
def rankNull (F : Type*) [Field F] (U : Ultrafilter ℕ) (n : ℕ → ℕ)
    (M : ∀ k : ℕ, Matrix (Fin (n k)) (Fin (n k)) F) : Prop :=
  ∀ ε : ℝ, 0 < ε → { k : ℕ | ((M k).rank : ℝ) ≤ ε * (n k : ℝ) } ∈ U

/-- Equivalence relation `M ~ N ↔ M - N ∈ Ker(ρ_U)` on `∏_k M_{n_k}(F)`. -/
def rankRel (F : Type*) [Field F] (U : Ultrafilter ℕ) (n : ℕ → ℕ)
    (M N : ∀ k : ℕ, Matrix (Fin (n k)) (Fin (n k)) F) : Prop :=
  rankNull F U n (M - N)

/-- Ring congruence on `∏_k M_{n_k}(F)` defined by `Ker(ρ_U)`, whose quotient is the
metric ultraproduct `∏_{k → U} M_{n_k}(F) / Ker(ρ_U)`. -/
noncomputable def rankRingCon (F : Type*) [Field F] (U : Ultrafilter ℕ) (n : ℕ → ℕ) :
    RingCon (∀ k : ℕ, Matrix (Fin (n k)) (Fin (n k)) F) where
  r := rankRel F U n
  iseqv := by
    have matrix_rank_add_le : ∀ {m : ℕ} (A B : Matrix (Fin m) (Fin m) F),
        (A + B).rank ≤ A.rank + B.rank := by
      intro m A B
      unfold Matrix.rank
      rw [Matrix.mulVecLin_add]
      have hsub : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
          LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
        rintro _ ⟨v, rfl⟩
        exact Submodule.add_mem_sup (LinearMap.mem_range_self _ v) (LinearMap.mem_range_self _ v)
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
      have hmono := Submodule.finrank_mono hsub
      omega
    have matrix_rank_neg : ∀ {m : ℕ} (A : Matrix (Fin m) (Fin m) F), (-A).rank = A.rank := by
      intro m A
      unfold Matrix.rank
      have hrange : LinearMap.range (-A).mulVecLin = LinearMap.range A.mulVecLin := by
        ext v
        simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, Matrix.neg_mulVec]
        constructor
        · rintro ⟨w, hw⟩; exact ⟨-w, by rw [Matrix.mulVec_neg]; exact hw⟩
        · rintro ⟨w, hw⟩; exact ⟨-w, by rw [Matrix.mulVec_neg, neg_neg]; exact hw⟩
      rw [hrange]
    refine ⟨?_, ?_, ?_⟩
    · intro M ε hε
      have huniv : { k : ℕ | (((M - M) k).rank : ℝ) ≤ ε * (n k : ℝ) } = Set.univ := by
        ext k; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, Pi.sub_apply, sub_self,
          Matrix.rank_zero, Nat.cast_zero]
        positivity
      rw [huniv]; exact Filter.univ_mem
    · intro M N hMN ε hε
      have heq : { k : ℕ | (((N - M) k).rank : ℝ) ≤ ε * (n k : ℝ) } =
          { k : ℕ | (((M - N) k).rank : ℝ) ≤ ε * (n k : ℝ) } := by
        ext k
        simp only [Set.mem_ofPred_eq, Pi.sub_apply]
        have : N k - M k = -(M k - N k) := by abel
        rw [this, matrix_rank_neg]
      rw [heq]; exact hMN ε hε
    · intro M N P hMN hNP ε hε
      have h1 := hMN (ε / 2) (by linarith)
      have h2 := hNP (ε / 2) (by linarith)
      filter_upwards [h1, h2] with k hk1 hk2
      simp only [Pi.sub_apply] at hk1 hk2 ⊢
      have hsub : M k - P k = (M k - N k) + (N k - P k) := by abel
      have hrk : ((M k - P k).rank : ℝ) ≤ ((M k - N k).rank : ℝ) + ((N k - P k).rank : ℝ) := by
        rw [hsub]; exact_mod_cast matrix_rank_add_le (M k - N k) (N k - P k)
      linarith
  add' := by
    have matrix_rank_add_le : ∀ {m : ℕ} (A B : Matrix (Fin m) (Fin m) F),
        (A + B).rank ≤ A.rank + B.rank := by
      intro m A B
      unfold Matrix.rank
      rw [Matrix.mulVecLin_add]
      have hsub : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
          LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
        rintro _ ⟨v, rfl⟩
        exact Submodule.add_mem_sup (LinearMap.mem_range_self _ v) (LinearMap.mem_range_self _ v)
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
      have hmono := Submodule.finrank_mono hsub
      omega
    intro M1 M2 N1 N2 h1 h2 ε hε
    have ha := h1 (ε / 2) (by linarith)
    have hb := h2 (ε / 2) (by linarith)
    filter_upwards [ha, hb] with k hka hkb
    simp only [Pi.sub_apply, Pi.add_apply] at hka hkb ⊢
    have hsub : M1 k + N1 k - (M2 k + N2 k) = (M1 k - M2 k) + (N1 k - N2 k) := by abel
    have hrk : ((M1 k + N1 k - (M2 k + N2 k)).rank : ℝ) ≤
        ((M1 k - M2 k).rank : ℝ) + ((N1 k - N2 k).rank : ℝ) := by
      rw [hsub]; exact_mod_cast matrix_rank_add_le (M1 k - M2 k) (N1 k - N2 k)
    linarith
  mul' := by
    have matrix_rank_add_le : ∀ {m : ℕ} (A B : Matrix (Fin m) (Fin m) F),
        (A + B).rank ≤ A.rank + B.rank := by
      intro m A B
      unfold Matrix.rank
      rw [Matrix.mulVecLin_add]
      have hsub : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤
          LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
        rintro _ ⟨v, rfl⟩
        exact Submodule.add_mem_sup (LinearMap.mem_range_self _ v) (LinearMap.mem_range_self _ v)
      have hsup := Submodule.finrank_sup_add_finrank_inf_eq
        (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
      have hmono := Submodule.finrank_mono hsub
      omega
    have matrix_rank_mul_le_left : ∀ {m : ℕ} (A B : Matrix (Fin m) (Fin m) F),
        (A * B).rank ≤ A.rank := by
      intro m A B
      unfold Matrix.rank
      rw [Matrix.mulVecLin_mul]
      exact Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
    have matrix_rank_mul_le_right : ∀ {m : ℕ} (A B : Matrix (Fin m) (Fin m) F),
        (A * B).rank ≤ B.rank := by
      intro m A B
      unfold Matrix.rank
      rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
      exact Submodule.finrank_map_le _ _
    intro M1 M2 N1 N2 h1 h2 ε hε
    have ha := h1 (ε / 2) (by linarith)
    have hb := h2 (ε / 2) (by linarith)
    filter_upwards [ha, hb] with k hka hkb
    simp only [Pi.sub_apply, Pi.mul_apply] at hka hkb ⊢
    have hsub : M1 k * N1 k - M2 k * N2 k = (M1 k - M2 k) * N1 k + M2 k * (N1 k - N2 k) := by
      noncomm_ring
    have hr1 : (((M1 k - M2 k) * N1 k).rank : ℝ) ≤ ((M1 k - M2 k).rank : ℝ) := by
      exact_mod_cast matrix_rank_mul_le_left (M1 k - M2 k) (N1 k)
    have hr2 : ((M2 k * (N1 k - N2 k)).rank : ℝ) ≤ ((N1 k - N2 k).rank : ℝ) := by
      exact_mod_cast matrix_rank_mul_le_right (M2 k) (N1 k - N2 k)
    have hadd : ((M1 k * N1 k - M2 k * N2 k).rank : ℝ) ≤
        (((M1 k - M2 k) * N1 k).rank : ℝ) + ((M2 k * (N1 k - N2 k)).rank : ℝ) := by
      rw [hsub]; exact_mod_cast matrix_rank_add_le _ _
    linarith

/-- An associative unital `F`-algebra `A` is linear sofic (Arzhantseva–Păunescu 2017)
if there exist a non-principal ultrafilter `U` on `ℕ`, a sequence of positive dimensions
`n : ℕ → ℕ` tending to `∞`, and an injective ring homomorphism from `A` into the metric
ultraproduct `∏_{k → U} M_{n_k}(F) / Ker(ρ_U)`. -/
def IsLinearSofic (F : Type*) [Field F] (A : Type*) [Ring A] [Algebra F A] : Prop :=
  ∃ (U : Ultrafilter ℕ) (n : ℕ → ℕ),
    (↑U : Filter ℕ) ≤ Filter.cofinite ∧
    Filter.Tendsto n Filter.atTop Filter.atTop ∧
    (∀ k : ℕ, 0 < n k) ∧
    ∃ Φ : A →+* (rankRingCon F U n).Quotient, Function.Injective Φ

/-- Theorem 1.2 of arXiv:2210.11650 (resolving the open problem of Arzhantseva and
Păunescu 2017): over any field `F`, there exists a finitely generated, stably finite
unital `F`-algebra that is not linear sofic. -/
theorem main :
    ∀ (F : Type) [Field F],
      ∃ (A : Type) (_ : Ring A) (_ : Algebra F A),
        Algebra.FiniteType F A ∧ IsStablyFinite A ∧ ¬ IsLinearSofic F A := by sorry

end OMA.S_arxiv_2210_11650
