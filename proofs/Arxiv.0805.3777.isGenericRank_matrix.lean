import FormalConjectures.Arxiv.«0805.3777».TensorRank

-- Problem: Generic and maximal rank of 3-tensors — isGenericRank matrix
-- Upstream: formal-conjectures FormalConjectures/Arxiv/0805.3777/TensorRank.lean:183 (declaration Arxiv.«0805.3777».isGenericRank_matrix)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- This formalises the classical textbook fact that a generic m x n complex matrix has rank min(m, n).
-- No new mathematical result is claimed.
-- Proof idea: identify a holor of format [m, n] with the matrix of its entries.
--   * CP rank is at least matrix rank: a CP-rank-one holor gives a vecMulVec matrix (rank at most 1)
--     and matrix rank is subadditive.
--   * CP rank is at most min(m, n): decompose a holor into its m rows or its n columns.
--   * Take U = holors whose matrix A has det (A * P) /= 0 for some P (case m <= n), or
--     det (Q * A) /= 0 for some Q (case n < m). U is a union of open sets, so open, and every
--     holor in U has matrix rank min(m, n). U is dense: perturb T to T + t H with
--     A_H * R = 1, then det (A_T * R + t 1) is a monic polynomial in t, nonzero for small t /= 0.

open Filter Topology Matrix
open scoped Arxiv.«0805.3777»

namespace OMAProofGenRank

-- Matrix rank subadditivity from the linear-map range API.
theorem rank_add_le {m n : Type*} [Fintype n] (A B : Matrix m n ℂ) :
    (A + B).rank ≤ A.rank + B.rank :=
  (Submodule.finrank_mono (by
    simpa only [Matrix.mulVecLin_add] using LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

variable {m n : ℕ}

/-- the index of entry (i, j) -/
def idx (i : Fin m) (j : Fin n) : HolorIndex [m, n] :=
  ⟨[i.1, j.1], List.Forall₂.cons i.2 (List.Forall₂.cons j.2 List.Forall₂.nil)⟩

lemma idx_surj (t : HolorIndex [m, n]) : ∃ i j, t = idx i j := by
  obtain ⟨l, hl⟩ := t
  cases hl with
  | cons h1 hl2 =>
    cases hl2 with
    | cons h2 hl3 =>
      cases hl3
      exact ⟨⟨_, h1⟩, ⟨_, h2⟩, rfl⟩

lemma holor_ext {T T' : Holor ℂ [m, n]} (h : ∀ i j, T (idx i j) = T' (idx i j)) : T = T' := by
  funext t
  obtain ⟨i, j, rfl⟩ := idx_surj t
  exact h i j

/-- the matrix of entries of a holor -/
def Mat (T : Holor ℂ [m, n]) : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun i j => T (idx i j)

lemma Mat_apply (T : Holor ℂ [m, n]) (i : Fin m) (j : Fin n) : Mat T i j = T (idx i j) := rfl

lemma Mat_add (T T' : Holor ℂ [m, n]) : Mat (T + T') = Mat T + Mat T' := by
  ext i j; rfl

lemma Mat_zero : Mat (0 : Holor ℂ [m, n]) = 0 := by
  ext i j; rfl

lemma continuous_Mat : Continuous (Mat : Holor ℂ [m, n] → Matrix (Fin m) (Fin n) ℂ) :=
  continuous_matrix fun i j => continuous_apply (idx i j)

lemma sum_apply_holor {ds : List ℕ} {ι : Type*} (s : Finset ι) (f : ι → Holor ℂ ds)
    (t : HolorIndex ds) : (∑ k ∈ s, f k) t = ∑ k ∈ s, f k t := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/- ### lower bound: matrix rank is at most CP rank -/

lemma rank_le_one_of_cprankMax1 {x : Holor ℂ [m, n]} (hx : Holor.CPRankMax1 x) :
    (Mat x).rank ≤ 1 := by
  cases hx with
  | cons a y hy =>
    cases hy with
    | cons b z hz =>
      have : Mat (Holor.mul a (Holor.mul b z)) =
          Matrix.vecMulVec (fun i : Fin m => a ⟨[i.1], List.Forall₂.cons i.2 List.Forall₂.nil⟩)
            (fun j : Fin n => b ⟨[j.1], List.Forall₂.cons j.2 List.Forall₂.nil⟩ *
              z ⟨[], List.Forall₂.nil⟩) := by
        ext i j; rfl
      rw [this]
      exact Matrix.rank_vecMulVec_le _ _

lemma rank_le_of_cprankMax {k : ℕ} {ds : List ℕ} {x : Holor ℂ ds} (hx : Holor.CPRankMax k x) :
    ∀ h : ds = [m, n], (Mat (h ▸ x)).rank ≤ k := by
  induction hx with
  | zero =>
    intro h
    subst h
    show (Mat 0).rank ≤ 0
    rw [Mat_zero, Matrix.rank_zero]
  | @succ k ds x y hx _ ih =>
    intro h
    subst h
    show (Mat (x + y)).rank ≤ k + 1
    rw [Mat_add]
    have h1 := rank_le_one_of_cprankMax1 hx
    have h2 := ih rfl
    have h3 := rank_add_le (Mat x) (Mat y)
    change (Mat y).rank ≤ k at h2
    omega

lemma rank_le_cprank (T : Holor ℂ [m, n]) : (Mat T).rank ≤ T.cprank := by
  classical
  have hspec : Holor.CPRankMax T.cprank T := by
    unfold Holor.cprank
    exact Nat.find_spec (p := fun n => Holor.CPRankMax n T)
      (H := ⟨[m, n].prod, Holor.cprankMax_upper_bound T⟩)
  exact rank_le_of_cprankMax hspec rfl

/- ### upper bound: CP rank is at most min m n -/

/-- a vector as a one-dimensional holor -/
def vecH (k : ℕ) (u : Fin k → ℂ) : Holor ℂ [k] := fun t =>
  if h : t.1.headI < k then u ⟨_, h⟩ else 0

lemma vecH_apply (k : ℕ) (u : Fin k → ℂ) (i : Fin k) :
    vecH k u ⟨[i.1], List.Forall₂.cons i.2 List.Forall₂.nil⟩ = u i := by
  simp [vecH]

/-- the scalar one -/
def one0 : Holor ℂ [] := fun _ => 1

/-- the outer product of two vectors as a holor of format [m, n] -/
def outer (u : Fin m → ℂ) (v : Fin n → ℂ) : Holor ℂ [m, n] :=
  Holor.mul (vecH m u) (Holor.mul (vecH n v) one0)

lemma outer_apply (u : Fin m → ℂ) (v : Fin n → ℂ) (i : Fin m) (j : Fin n) :
    outer u v (idx i j) = u i * v j := by
  change vecH m u ⟨[i.1], List.Forall₂.cons i.2 List.Forall₂.nil⟩ *
      (vecH n v ⟨[j.1], List.Forall₂.cons j.2 List.Forall₂.nil⟩ * one0 ⟨[], List.Forall₂.nil⟩) = _
  rw [vecH_apply, vecH_apply]
  simp [one0]

lemma outer_cprankMax1 (u : Fin m → ℂ) (v : Fin n → ℂ) : Holor.CPRankMax1 (outer u v) :=
  Holor.CPRankMax1.cons _ _ (Holor.CPRankMax1.cons _ _ (Holor.CPRankMax1.nil _))

lemma sum_outer_apply {r : ℕ} (u : Fin r → Fin m → ℂ) (v : Fin r → Fin n → ℂ)
    (i : Fin m) (j : Fin n) :
    (∑ k, outer (u k) (v k)) (idx i j) = ∑ k, u k i * v k j := by
  rw [sum_apply_holor]
  simp only [outer_apply]

lemma cprankMax_of_decomp {r : ℕ} (u : Fin r → Fin m → ℂ) (v : Fin r → Fin n → ℂ)
    (T : Holor ℂ [m, n]) (h : ∀ i j, T (idx i j) = ∑ k, u k i * v k j) :
    Holor.CPRankMax r T := by
  have hT : T = ∑ k, outer (u k) (v k) :=
    holor_ext fun i j => by rw [h, sum_outer_apply]
  have := Holor.cprankMax_sum (n := 1) Finset.univ (fun k => outer (u k) (v k))
    (fun k _ => Holor.cprankMax_1 (outer_cprankMax1 (u k) (v k)))
  rw [Finset.card_univ, Fintype.card_fin, mul_one] at this
  rw [hT]
  exact this

lemma cprankMax_rows (T : Holor ℂ [m, n]) : Holor.CPRankMax m T :=
  cprankMax_of_decomp (fun k i => if i = k then 1 else 0) (fun k j => T (idx k j)) T
    (fun i j => by simp [ite_mul])

lemma cprankMax_cols (T : Holor ℂ [m, n]) : Holor.CPRankMax n T :=
  cprankMax_of_decomp (fun k i => T (idx i k)) (fun k j => if k = j then 1 else 0) T
    (fun i j => by simp [mul_ite])

lemma cprank_le_of {T : Holor ℂ [m, n]} {r : ℕ} (h : Holor.CPRankMax r T) : T.cprank ≤ r := by
  classical
  unfold Holor.cprank
  exact Nat.find_min' _ h

lemma cprank_le (T : Holor ℂ [m, n]) : T.cprank ≤ min m n :=
  le_min (cprank_le_of (cprankMax_rows T)) (cprank_le_of (cprankMax_cols T))

/- ### matrix facts -/

lemma le_rank_of_det_mul {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ) (P : Matrix (Fin l) (Fin k) ℂ)
    (h : (A * P).det ≠ 0) : k ≤ A.rank := by
  have hu : IsUnit (A * P) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  have h1 := Matrix.rank_of_isUnit _ hu
  rw [Fintype.card_fin] at h1
  have h2 := Matrix.rank_mul_le_left A P
  omega

lemma le_rank_of_det_mul' {k l : ℕ} (A : Matrix (Fin l) (Fin k) ℂ) (Q : Matrix (Fin k) (Fin l) ℂ)
    (h : (Q * A).det ≠ 0) : k ≤ A.rank := by
  have hu : IsUnit (Q * A) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)
  have h1 := Matrix.rank_of_isUnit _ hu
  rw [Fintype.card_fin] at h1
  have h2 := Matrix.rank_mul_le_right Q A
  omega

lemma eventually_det_ne {k : ℕ} (B : Matrix (Fin k) (Fin k) ℂ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), (B + t • (1 : Matrix (Fin k) (Fin k) ℂ)).det ≠ 0 := by
  have h := (Polynomial.eventually_cofinite_not_isRoot (Matrix.charpoly_monic (-B)).ne_zero).filter_mono
    (nhdsNE_le_cofinite (0 : ℂ))
  simpa only [Polynomial.IsRoot, Matrix.eval_charpoly, sub_neg_eq_add, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, add_comm] using h

/-- the k x l matrix selecting the first k coordinates -/
def Sel (k l : ℕ) (h : k ≤ l) : Matrix (Fin k) (Fin l) ℂ :=
  (1 : Matrix (Fin l) (Fin l) ℂ).submatrix (Fin.castLE h) id

/-- its transpose-shaped partner -/
def Sel' (k l : ℕ) (h : k ≤ l) : Matrix (Fin l) (Fin k) ℂ :=
  (1 : Matrix (Fin l) (Fin l) ℂ).submatrix id (Fin.castLE h)

lemma Sel_mul (k l : ℕ) (h : k ≤ l) : Sel k l h * Sel' k l h = 1 := by
  unfold Sel Sel'
  rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
    Matrix.submatrix_one _ (Fin.castLE_injective h)]

/- ### a holor with a prescribed matrix -/

/-- the holor whose matrix is A -/
def ofMat (A : Matrix (Fin m) (Fin n) ℂ) : Holor ℂ [m, n] :=
  ∑ k : Fin m, outer (fun i => if i = k then 1 else 0) (A k)

lemma Mat_ofMat (A : Matrix (Fin m) (Fin n) ℂ) : Mat (ofMat A) = A := by
  ext i j
  rw [Mat_apply, ofMat, sum_apply_holor]
  simp [outer_apply, ite_mul]

lemma Mat_perturb (T : Holor ℂ [m, n]) (H : Holor ℂ [m, n]) (t : ℂ) :
    Mat (T + t • H) = Mat T + t • Mat H := by
  ext i j; rfl

lemma tendsto_perturb (T H : Holor ℂ [m, n]) :
    Tendsto (fun t : ℂ => T + t • H) (𝓝[≠] 0) (𝓝 T) := by
  have hc : Continuous fun t : ℂ => T + t • H := by
    refine continuous_pi fun x => ?_
    change Continuous fun t : ℂ => T x + t * H x
    exact continuous_const.add (continuous_id.mul continuous_const)
  have h0 : T + (0 : ℂ) • H = T := by
    funext x
    change T x + 0 * H x = T x
    simp
  have := hc.continuousAt (x := 0)
  rw [ContinuousAt, h0] at this
  exact this.mono_left nhdsWithin_le_nhds

/- ### the two cases -/

theorem generic_le (h : m ≤ n) : Arxiv.«0805.3777».IsGenericRank [m, n] (min m n) := by
  refine ⟨{T | ∃ P : Matrix (Fin n) (Fin m) ℂ, (Mat T * P).det ≠ 0}, ?_, ?_, ?_⟩
  · have : {T : Holor ℂ [m, n] | ∃ P : Matrix (Fin n) (Fin m) ℂ, (Mat T * P).det ≠ 0} =
        ⋃ P : Matrix (Fin n) (Fin m) ℂ, {T | (Mat T * P).det ≠ 0} := by
      ext T; simp
    rw [this]
    exact isOpen_iUnion fun P =>
      isOpen_ne_fun ((continuous_Mat.matrix_mul continuous_const).matrix_det) continuous_const
  · intro T
    apply mem_closure_of_tendsto (tendsto_perturb T (ofMat (Sel m n h)))
    filter_upwards [eventually_det_ne (Mat T * Sel' m n h)] with t ht
    refine ⟨Sel' m n h, ?_⟩
    rw [Mat_perturb, Mat_ofMat, Matrix.add_mul, Matrix.smul_mul, Sel_mul]
    exact ht
  · rintro T ⟨P, hP⟩
    have h1 := le_rank_of_det_mul _ _ hP
    have h2 := rank_le_cprank T
    have h3 := cprank_le T
    omega

theorem generic_ge (h : n ≤ m) : Arxiv.«0805.3777».IsGenericRank [m, n] (min m n) := by
  refine ⟨{T | ∃ Q : Matrix (Fin n) (Fin m) ℂ, (Q * Mat T).det ≠ 0}, ?_, ?_, ?_⟩
  · have : {T : Holor ℂ [m, n] | ∃ Q : Matrix (Fin n) (Fin m) ℂ, (Q * Mat T).det ≠ 0} =
        ⋃ Q : Matrix (Fin n) (Fin m) ℂ, {T | (Q * Mat T).det ≠ 0} := by
      ext T; simp
    rw [this]
    exact isOpen_iUnion fun Q =>
      isOpen_ne_fun ((continuous_const.matrix_mul continuous_Mat).matrix_det) continuous_const
  · intro T
    apply mem_closure_of_tendsto (tendsto_perturb T (ofMat (Sel' n m h)))
    filter_upwards [eventually_det_ne (Sel n m h * Mat T)] with t ht
    refine ⟨Sel n m h, ?_⟩
    rw [Mat_perturb, Mat_ofMat, Matrix.mul_add, Matrix.mul_smul, Sel_mul]
    exact ht
  · rintro T ⟨Q, hQ⟩
    have h1 := le_rank_of_det_mul' _ _ hQ
    have h2 := rank_le_cprank T
    have h3 := cprank_le T
    omega

end OMAProofGenRank

theorem OMA.solution : type_of% @Arxiv.«0805.3777».isGenericRank_matrix := by
  intro m n
  rcases le_total m n with h | h
  · exact OMAProofGenRank.generic_le h
  · exact OMAProofGenRank.generic_ge h
