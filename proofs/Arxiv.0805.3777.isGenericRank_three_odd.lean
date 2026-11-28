import FormalConjectures.Arxiv.«0805.3777».TensorRank

-- Problem: Generic and maximal rank of 3-tensors — isGenericRank three odd
-- Upstream: formal-conjectures FormalConjectures/Arxiv/0805.3777/TensorRank.lean:211 (declaration Arxiv.«0805.3777».isGenericRank_three_odd)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- REUSE AND CREDIT. Most of this file is assembled from work already merged in this repository;
-- only the upper bound for the odd format is new.
-- * The namespace Arxiv08053777H1 and the theorem Arxiv08053777H1.lower (the generic lower bound
--   3p + 2, by Strassen's commutator obstruction) are the merged proof
--   proofs/Arxiv.0805.3777.isGenericRank_three_odd.R1.H1.lean by green-notes (PR #2403), copied
--   unchanged; only its final theorem is restated under a new name.
-- * The split into a lower and an upper bound and the ceiling computation in OMA.solution are the
--   merged reduction reductions/Arxiv.0805.3777.isGenericRank_three_odd.R1.lean by Euclides
--   Pinheiro (PR #1969).
-- * The namespaces ThreeEven, ThreeEven.Grid, ThreeEven.Dimension and ThreeEven.Dominance (the
--   two-by-two block cells with their certificates, the polynomial avoidance lemmas, the
--   constructibility and Nullstellensatz argument that turns one surjective differential into a
--   dense open set, and the theorem ThreeEven.upper) are copied from the merged proof
--   proofs/Arxiv.0805.3777.isGenericRank_three_even.lean by mattdorman (PR #2694), with the part
--   used only for its lower bound removed.
-- * New: ThreeEven.Grid.common_avoiding (the lemma common with one more polynomial condition) and
--   the namespace ThreeOdd.

/-!
# The generic rank of complex `3 × (2p+1) × (2p+1)` tensors

The generic rank is `3 p + 2`, one more than the dimension count predicts (Strassen 1983;
[Friedland, (5.4)](https://arxiv.org/abs/0805.3777)).

**Lower bound.** Merged step H1 of the reduction R1, reproduced in `Arxiv08053777H1`.

**Upper bound** (`ThreeOdd.upper`, the missing step H2). By the argument of the even case, it is
enough to exhibit `3 p + 2` points `(a t, b t, c t)` whose tangent spaces to the variety of
rank-one tensors span the whole space (`ThreeOdd.SpansOn`). Take the `3 p` points of the even
format `3 × 2p × 2p` (three per two-by-two block), padded by zero in a new last coordinate `e`,
and add the two points `(e₁, e, e)` and `(e₂, e, e)`. The tangent directions then decouple:
* the old points with variations inside the old coordinates span the main block, as before;
* the corner entries are spanned by the variation of the first factor of a new point;
* the last column (and symmetrically the last row) receives `a t ⊗ b t` from the old points,
  through the new coordinate of their third factor, and `e₁ ⊗ v`, `e₂ ⊗ v` with `v` free from
  the new points. The latter fill the slices `1` and `2`, so only the slice `0` has to be
  matched by the old points. This is a two-by-two linear system in every block, solvable when
  the first coordinate of every `a t` is nonzero and the first two `b` (respectively `c`) of
  every block are independent (`ThreeOdd.solve2`).
These nonvanishing conditions are one more polynomial to avoid when choosing the parameters
(`ThreeOdd.good`, `ThreeEven.Grid.common_avoiding`).
-/

namespace Arxiv08053777H1

open scoped Matrix Arxiv.«0805.3777»

private def idx3 {n : ℕ} (k : Fin 3) (i j : Fin n) : HolorIndex [3, n, n] :=
  ⟨[k.1, i.1, j.1],
    List.Forall₂.cons k.isLt (List.Forall₂.cons i.isLt (List.Forall₂.cons j.isLt List.Forall₂.nil))⟩

private def sliceMat {R : Type*} {n : ℕ} (T : Holor R [3, n, n]) (k : Fin 3) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => T (idx3 k i j)

private lemma sliceMat_continuous {n : ℕ} (k : Fin 3) :
    Continuous (fun T : Holor ℂ [3, n, n] => sliceMat T k) :=
  continuous_matrix fun i j => continuous_apply (idx3 k i j)

private noncomputable def commAdjugate {R : Type*} [CommRing R] {n : ℕ}
    (T : Holor R [3, n, n]) : Matrix (Fin n) (Fin n) R :=
  sliceMat T 1 * (sliceMat T 0).adjugate * sliceMat T 2 -
    sliceMat T 2 * (sliceMat T 0).adjugate * sliceMat T 1

private noncomputable def polyObstruction {R : Type*} [CommRing R] {n : ℕ}
    (T : Holor R [3, n, n]) : R :=
  (sliceMat T 0).det * (commAdjugate T).det

private lemma polyObstruction_continuous {n : ℕ} :
    Continuous (fun T : Holor ℂ [3, n, n] => polyObstruction T) := by
  have h0 : Continuous (fun T : Holor ℂ [3, n, n] => sliceMat T 0) := sliceMat_continuous 0
  have h1 : Continuous (fun T : Holor ℂ [3, n, n] => sliceMat T 1) := sliceMat_continuous 1
  have h2 : Continuous (fun T : Holor ℂ [3, n, n] => sliceMat T 2) := sliceMat_continuous 2
  have hadj : Continuous (fun T : Holor ℂ [3, n, n] => (sliceMat T 0).adjugate) :=
    h0.matrix_adjugate
  have hcomm : Continuous (fun T : Holor ℂ [3, n, n] => commAdjugate T) :=
    ((h1.matrix_mul hadj).matrix_mul h2).sub ((h2.matrix_mul hadj).matrix_mul h1)
  exact h0.matrix_det.mul hcomm.matrix_det

private lemma sliceMat_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (T : Holor R [3, n, n]) (k : Fin 3) :
    sliceMat (fun idx => f (T idx)) k = f.mapMatrix (sliceMat T k) :=
  rfl

private lemma map_polyObstruction {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (T : Holor R [3, n, n]) :
    f (polyObstruction T) = polyObstruction (fun idx => f (T idx)) := by
  simp only [polyObstruction, commAdjugate, map_mul, map_sub, RingHom.map_det,
    RingHom.map_adjugate, ← sliceMat_map]

private def witnessMat0 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := 1

private def witnessMat1 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => (i.1 : ℂ)

private def witnessMat2 (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if (i.1 + 1) % n = j.1 then (1 : ℂ) else 0

private def witnessTensor (n : ℕ) : Holor ℂ [3, n, n] := fun idx =>
  match idx.1 with
  | [0, i, j] => if h : i < n ∧ j < n then witnessMat0 n ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  | [1, i, j] => if h : i < n ∧ j < n then witnessMat1 n ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  | [2, i, j] => if h : i < n ∧ j < n then witnessMat2 n ⟨i, h.1⟩ ⟨j, h.2⟩ else 0
  | _ => 0

private lemma sliceMat_witness_0 (n : ℕ) : sliceMat (witnessTensor n) 0 = witnessMat0 n := by
  ext i j
  simp [sliceMat, idx3, witnessTensor]

private lemma sliceMat_witness_1 (n : ℕ) : sliceMat (witnessTensor n) 1 = witnessMat1 n := by
  ext i j
  simp [sliceMat, idx3, witnessTensor]

private lemma sliceMat_witness_2 (n : ℕ) : sliceMat (witnessTensor n) 2 = witnessMat2 n := by
  ext i j
  simp [sliceMat, idx3, witnessTensor]

private lemma polyObstruction_witness_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    polyObstruction (witnessTensor n) ≠ 0 := by
  have hdet0 : (sliceMat (witnessTensor n) 0).det = 1 := by
    rw [sliceMat_witness_0, witnessMat0, Matrix.det_one]
  have hadj0 : (sliceMat (witnessTensor n) 0).adjugate = 1 := by
    rw [sliceMat_witness_0, witnessMat0, Matrix.adjugate_one]
  have hcomm_eq :
      commAdjugate (witnessTensor n) =
        witnessMat1 n * witnessMat2 n - witnessMat2 n * witnessMat1 n := by
    simp [commAdjugate, sliceMat_witness_1, sliceMat_witness_2, hadj0]
  have hcomm_det : (commAdjugate (witnessTensor n)).det ≠ 0 := by
    intro hzero
    obtain ⟨x, hxne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
    apply hxne
    ext j
    let nextIdx : Fin n → Fin n := fun i => ⟨(i.1 + 1) % n, Nat.mod_lt _ (by omega)⟩
    have hshift : ∀ i : Fin n, x (nextIdx i) = 0 := by
      intro i
      have hi := congrFun hmul i
      rw [hcomm_eq, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hi
      have h2_mul : ∀ y : Fin n → ℂ, (witnessMat2 n *ᵥ y) i = y (nextIdx i) := by
        intro y
        simp only [witnessMat2, Matrix.mulVec, dotProduct, Matrix.of_apply]
        rw [Finset.sum_eq_single (nextIdx i)]
        · simp [nextIdx]
        · intro k _ hkne
          have hne_val : (i.1 + 1) % n ≠ k.1 := by
            intro heq
            apply hkne
            exact Fin.ext heq.symm
          simp [hne_val]
        · intro hmem
          exact absurd (Finset.mem_univ (nextIdx i)) hmem
      have h1_mul : ∀ (k : Fin n) (y : Fin n → ℂ),
          (witnessMat1 n *ᵥ y) k = (k.1 : ℂ) * y k := by
        intro k y
        simp [witnessMat1, Matrix.mulVec_diagonal]
      have h12 : (witnessMat1 n *ᵥ (witnessMat2 n *ᵥ x)) i = (i.1 : ℂ) * x (nextIdx i) := by
        rw [h1_mul i (witnessMat2 n *ᵥ x), h2_mul x]
      have h21 : (witnessMat2 n *ᵥ (witnessMat1 n *ᵥ x)) i =
          ((nextIdx i).1 : ℂ) * x (nextIdx i) := by
        rw [h2_mul (witnessMat1 n *ᵥ x), h1_mul (nextIdx i) x]
      have hdiff : ((i.1 : ℂ) - ((nextIdx i).1 : ℂ)) * x (nextIdx i) = 0 := by
        rw [Pi.sub_apply, h12, h21, ← sub_mul] at hi
        exact hi
      have hne_coeff : (i.1 : ℂ) - ((nextIdx i).1 : ℂ) ≠ 0 := by
        rw [sub_ne_zero]
        intro hcast
        have hval : i.1 = (i.1 + 1) % n := Nat.cast_injective hcast
        by_cases hlt : i.1 + 1 < n
        · rw [Nat.mod_eq_of_lt hlt] at hval
          omega
        · have heq : i.1 + 1 = n := by omega
          rw [heq, Nat.mod_self] at hval
          omega
      exact (mul_eq_zero.mp hdiff).resolve_left hne_coeff
    let prevIdx : Fin n := ⟨(j.1 + n - 1) % n, Nat.mod_lt _ (by omega)⟩
    have hprev : nextIdx prevIdx = j := by
      ext
      dsimp only [nextIdx, prevIdx]
      have hle : 1 ≤ j.1 + n := by omega
      have hmod : ((j.1 + n - 1) % n + 1) % n = (j.1 + n - 1 + 1) % n := by
        simp [Nat.add_mod]
      rw [hmod, Nat.sub_add_cancel hle, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    simpa [hprev] using hshift prevIdx
  rw [polyObstruction, hdet0, one_mul]
  exact hcomm_det

private lemma open_and_dense_nonvanishing {n : ℕ} (hn : 2 ≤ n) :
    let U : Set (Holor ℂ [3, n, n]) := {T | polyObstruction T ≠ 0}
    IsOpen U ∧ Dense U := by
  intro U
  refine ⟨isOpen_ne.preimage polyObstruction_continuous, ?_⟩
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro T
  let Tpoly : Holor (Polynomial ℂ) [3, n, n] := fun idx =>
    Polynomial.C (T idx) + Polynomial.X * Polynomial.C (witnessTensor n idx - T idx)
  let P : Polynomial ℂ := polyObstruction Tpoly
  have hP_eval : ∀ t : ℂ, P.eval t =
      polyObstruction (fun idx => T idx + t * (witnessTensor n idx - T idx)) := by
    intro t
    have h := map_polyObstruction (Polynomial.evalRingHom t) Tpoly
    simpa [P, Tpoly, Polynomial.coe_evalRingHom] using h
  have hP_ne : P ≠ 0 := by
    intro h0
    have hev := hP_eval 1
    rw [h0, Polynomial.eval_zero] at hev
    have hW : (fun idx => T idx + 1 * (witnessTensor n idx - T idx)) = witnessTensor n := by
      ext idx
      ring
    rw [hW] at hev
    exact polyObstruction_witness_ne_zero hn hev.symm
  let seq : ℕ → ℂ := fun k => 1 / ((k : ℂ) + 1)
  have hseq_inj : Function.Injective seq := by
    intro a b hab
    have hab' : (a : ℂ) + 1 = (b : ℂ) + 1 := by
      simpa [seq] using hab
    exact Nat.cast_injective (add_right_cancel hab')
  let bad : Set ℕ := seq ⁻¹' (P.roots.toFinset : Set ℂ)
  have hbad_fin : bad.Finite :=
    (P.roots.toFinset.finite_toSet).preimage hseq_inj.injOn
  obtain ⟨N, hN⟩ := hbad_fin.bddAbove
  let pts : ℕ → Holor ℂ [3, n, n] := fun k =>
    fun idx => T idx + seq k * (witnessTensor n idx - T idx)
  have h_tend : Filter.Tendsto pts Filter.atTop (nhds T) := by
    refine tendsto_pi_nhds.2 fun idx => ?_
    have hs : Filter.Tendsto seq Filter.atTop (nhds (0 : ℂ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul := hs.mul_const (witnessTensor n idx - T idx)
    simpa [pts, zero_mul, add_zero] using tendsto_const_nhds.add hmul
  have h_mem : ∀ᶠ k in Filter.atTop, pts k ∈ U := by
    refine Filter.eventually_atTop.2 ⟨N + 1, fun k hk => ?_⟩
    show polyObstruction (pts k) ≠ 0
    rw [← hP_eval (seq k)]
    intro hroot
    have hk_mem : k ∈ bad := by
      simp only [bad, Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hP_ne).2 hroot
    have hle := hN hk_mem
    omega
  exact mem_closure_of_tendsto h_tend h_mem

private lemma cprankMax1_decomp {n : ℕ} {x : Holor ℂ [3, n, n]} (hx : Holor.CPRankMax1 x) :
    ∃ (α β γ : ℂ) (v w : Fin n → ℂ),
      (∀ i j : Fin n, sliceMat x 0 i j = α * v i * w j) ∧
      (∀ i j : Fin n, sliceMat x 1 i j = β * v i * w j) ∧
      (∀ i j : Fin n, sliceMat x 2 i j = γ * v i * w j) := by
  cases hx with
  | cons u y hy =>
    cases hy with
    | cons v z hz =>
      cases hz with
      | cons w c hc =>
        cases hc with
        | nil c =>
          let c0 : ℂ := c ⟨[], List.Forall₂.nil⟩
          let u0 : ℂ := u ⟨[0], List.Forall₂.cons (by omega : 0 < 3) List.Forall₂.nil⟩ * c0
          let u1 : ℂ := u ⟨[1], List.Forall₂.cons (by omega : 1 < 3) List.Forall₂.nil⟩ * c0
          let u2 : ℂ := u ⟨[2], List.Forall₂.cons (by omega : 2 < 3) List.Forall₂.nil⟩ * c0
          let vv : Fin n → ℂ := fun i => v ⟨[i.1], List.Forall₂.cons i.isLt List.Forall₂.nil⟩
          let ww : Fin n → ℂ := fun j => w ⟨[j.1], List.Forall₂.cons j.isLt List.Forall₂.nil⟩
          refine ⟨u0, u1, u2, vv, ww, ?_, ?_, ?_⟩
          · intro i j
            change u ⟨[0], _⟩ * (v ⟨[i.1], _⟩ * (w ⟨[j.1], _⟩ * c ⟨[], _⟩)) = u0 * vv i * ww j
            dsimp only [u0, c0, vv, ww]
            ring
          · intro i j
            change u ⟨[1], _⟩ * (v ⟨[i.1], _⟩ * (w ⟨[j.1], _⟩ * c ⟨[], _⟩)) = u1 * vv i * ww j
            dsimp only [u1, c0, vv, ww]
            ring
          · intro i j
            change u ⟨[2], _⟩ * (v ⟨[i.1], _⟩ * (w ⟨[j.1], _⟩ * c ⟨[], _⟩)) = u2 * vv i * ww j
            dsimp only [u2, c0, vv, ww]
            ring

private lemma cprankMax_decomp {n : ℕ} :
    ∀ (r : ℕ) {T : Holor ℂ [3, n, n]}, Holor.CPRankMax r T →
      ∃ (α β γ : Fin r → ℂ) (v w : Fin r → Fin n → ℂ),
        (∀ i j : Fin n, sliceMat T 0 i j = ∑ k : Fin r, α k * v k i * w k j) ∧
        (∀ i j : Fin n, sliceMat T 1 i j = ∑ k : Fin r, β k * v k i * w k j) ∧
        (∀ i j : Fin n, sliceMat T 2 i j = ∑ k : Fin r, γ k * v k i * w k j)
  | 0, T, h => by
    cases h with
    | zero =>
      refine ⟨Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩ <;>
        intro i j <;> simp [sliceMat] <;> rfl
  | r + 1, T, h => by
    cases h with
    | succ _ x y hx hy =>
      obtain ⟨a0, b0, c0, v0, w0, hx0, hx1, hx2⟩ := cprankMax1_decomp hx
      obtain ⟨ar, br, cr, vr, wr, hy0, hy1, hy2⟩ := cprankMax_decomp r hy
      refine ⟨Fin.cons a0 ar, Fin.cons b0 br, Fin.cons c0 cr,
        Fin.cons v0 vr, Fin.cons w0 wr, ?_, ?_, ?_⟩
      · intro i j
        have hadd : sliceMat (x + y) 0 i j = sliceMat x 0 i j + sliceMat y 0 i j := rfl
        rw [hadd, hx0 i j, hy0 i j, Fin.sum_univ_succ]
        simp
      · intro i j
        have hadd : sliceMat (x + y) 1 i j = sliceMat x 1 i j + sliceMat y 1 i j := rfl
        rw [hadd, hx1 i j, hy1 i j, Fin.sum_univ_succ]
        simp
      · intro i j
        have hadd : sliceMat (x + y) 2 i j = sliceMat x 2 i j + sliceMat y 2 i j := rfl
        rw [hadd, hx2 i j, hy2 i j, Fin.sum_univ_succ]
        simp

private lemma sum_split_nz {r : ℕ} (α : Fin r → ℂ) (f : Fin r → ℂ) :
    (∑ k : Fin r, f k) =
      (∑ k : {k : Fin r // α k ≠ 0}, f k.1) + ∑ k : {k : Fin r // α k = 0}, f k.1 := by
  let e : {k : Fin r // α k ≠ 0} ⊕ {k : Fin r // α k = 0} ≃ Fin r :=
    { toFun := Sum.elim Subtype.val Subtype.val
      invFun := fun k => if h : α k ≠ 0 then Sum.inl ⟨k, h⟩ else Sum.inr ⟨k, not_not.mp h⟩
      left_inv := fun s => by
        cases s with
        | inl k => simp [k.2]
        | inr k => simp [k.2]
      right_inv := fun k => by
        by_cases h : α k ≠ 0 <;> simp [h] }
  rw [← Equiv.sum_comp e f, Fintype.sum_sum_type]
  rfl

private lemma commAdjugate_det_eq_zero_of_cprankMax {p r : ℕ} {T : Holor ℂ [3, 2 * p + 1, 2 * p + 1]}
    (hr : r ≤ 3 * p + 1) (hcp : Holor.CPRankMax r T)
    (hdet0 : (sliceMat T 0).det ≠ 0) :
    (commAdjugate T).det = 0 := by
  let n : ℕ := 2 * p + 1
  obtain ⟨α, β, γ, v, w, hA0, hA1, hA2⟩ := cprankMax_decomp r hcp
  let A₀ : Matrix (Fin n) (Fin n) ℂ := sliceMat T 0
  let A₁ : Matrix (Fin n) (Fin n) ℂ := sliceMat T 1
  let A₂ : Matrix (Fin n) (Fin n) ℂ := sliceMat T 2
  have hu : IsUnit A₀.det := hdet0.isUnit
  have hinv_mul : A₀⁻¹ * A₀ = 1 := Matrix.nonsing_inv_mul A₀ hu
  have hadj_eq : A₀.adjugate = A₀.det • A₀⁻¹ := by
    have hm := congrArg (fun M => A₀⁻¹ * M) (Matrix.mul_adjugate A₀)
    simpa [← Matrix.mul_assoc, hinv_mul, Matrix.mul_smul] using hm
  let B : Matrix (Fin n) (Fin n) ℂ := A₀⁻¹ * A₁
  let C : Matrix (Fin n) (Fin n) ℂ := A₀⁻¹ * A₂
  let K := {k : Fin r // α k ≠ 0}
  let Kc := {k : Fin r // α k = 0}
  let vtilde : Fin r → Fin n → ℂ := fun k => A₀⁻¹ *ᵥ v k
  let u : K → Fin n → ℂ := fun k => α k.1 • vtilde k.1
  let b₁ : K → ℂ := fun k => β k.1 / α k.1
  let b₂ : K → ℂ := fun k => γ k.1 / α k.1
  have hvtilde_sum : ∀ (c : Fin r → ℂ) (x : Fin n → ℂ) (i : Fin n),
      (A₀⁻¹ *ᵥ (Matrix.of (fun a b => ∑ k : Fin r, c k * v k a * w k b) *ᵥ x)) i =
        ∑ k : Fin r, c k * (w k ⬝ᵥ x) * vtilde k i := by
    intro c x i
    simp only [vtilde, Matrix.mulVec, dotProduct, Matrix.of_apply]
    have hstep1 :
        ∑ a : Fin n, A₀⁻¹ i a * ∑ b : Fin n, (∑ k : Fin r, c k * v k a * w k b) * x b =
          ∑ a : Fin n, ∑ b : Fin n, ∑ k : Fin r,
            c k * (w k b * x b) * (A₀⁻¹ i a * v k a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have hstep2 :
        ∑ a : Fin n, ∑ b : Fin n, ∑ k : Fin r, c k * (w k b * x b) * (A₀⁻¹ i a * v k a) =
          ∑ k : Fin r, ∑ b : Fin n, ∑ a : Fin n,
            c k * (w k b * x b) * (A₀⁻¹ i a * v k a) := by
      rw [Finset.sum_comm]
      have hinner :
          (∑ b : Fin n, ∑ a : Fin n, ∑ k : Fin r, c k * (w k b * x b) * (A₀⁻¹ i a * v k a)) =
            ∑ b : Fin n, ∑ k : Fin r, ∑ a : Fin n, c k * (w k b * x b) * (A₀⁻¹ i a * v k a) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
      rw [hinner, Finset.sum_comm]
    have hstep3 :
        ∑ k : Fin r, ∑ b : Fin n, ∑ a : Fin n, c k * (w k b * x b) * (A₀⁻¹ i a * v k a) =
          ∑ k : Fin r, c k * (∑ b : Fin n, w k b * x b) * ∑ a : Fin n, A₀⁻¹ i a * v k a := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have hs1 :
          (∑ b : Fin n, ∑ a : Fin n, c k * (w k b * x b) * (A₀⁻¹ i a * v k a)) =
            ∑ b : Fin n, c k * (w k b * x b) * ∑ a : Fin n, A₀⁻¹ i a * v k a :=
        Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
      rw [hs1, ← Finset.sum_mul, ← Finset.mul_sum, mul_assoc]
    exact hstep1.trans (hstep2.trans hstep3)
  have hA0_mat : A₀ = Matrix.of (fun a b => ∑ k : Fin r, α k * v k a * w k b) := by
    ext a b; exact hA0 a b
  have hA1_mat : A₁ = Matrix.of (fun a b => ∑ k : Fin r, β k * v k a * w k b) := by
    ext a b; exact hA1 a b
  have hA2_mat : A₂ = Matrix.of (fun a b => ∑ k : Fin r, γ k * v k a * w k b) := by
    ext a b; exact hA2 a b
  let U : (K → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun z i => ∑ k : K, z k * u k i
      map_add' := fun z₁ z₂ => by
        ext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun c z => by
        ext i; simp [Finset.mul_sum, mul_assoc] }
  let W : (Fin n → ℂ) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun x k => w k.1 ⬝ᵥ x
      map_add' := fun x₁ x₂ => by
        ext k; simp [dotProduct_add]
      map_smul' := fun c x => by
        ext k; simp [dotProduct_smul] }
  let D₁ : (K → ℂ) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun z k => b₁ k * z k
      map_add' := fun z₁ z₂ => by
        ext k; simp [mul_add]
      map_smul' := fun c z => by
        ext k; simp [mul_left_comm] }
  let D₂ : (K → ℂ) →ₗ[ℂ] (K → ℂ) :=
    { toFun := fun z k => b₂ k * z k
      map_add' := fun z₁ z₂ => by
        ext k; simp [mul_add]
      map_smul' := fun c z => by
        ext k; simp [mul_left_comm] }
  have hUW : ∀ x : Fin n → ℂ, U (W x) = x := by
    intro x
    ext i
    have hmul : (A₀⁻¹ *ᵥ ((Matrix.of fun a b => ∑ k : Fin r, α k * v k a * w k b) *ᵥ x)) i = x i := by
      rw [← hA0_mat, Matrix.mulVec_mulVec, hinv_mul, Matrix.one_mulVec]
    rw [← hmul, hvtilde_sum α x i, sum_split_nz α]
    have hzero : (∑ k : Kc, α k.1 * (w k.1 ⬝ᵥ x) * vtilde k.1 i) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [k.2]
    rw [hzero, add_zero]
    dsimp only [U, W, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [u, Pi.smul_apply, smul_eq_mul]
    ring
  have hU_surj : Function.Surjective U := fun x => ⟨W x, hUW x⟩
  have hU_range : LinearMap.range U = ⊤ := LinearMap.range_eq_top.mpr hU_surj
  let Q : (K → ℂ) →ₗ[ℂ] (K → ℂ) := LinearMap.id - W.comp U
  have hQ_ker : ∀ z : K → ℂ, Q z ∈ LinearMap.ker U := by
    intro z
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, hUW (U z), sub_self]
  let B_K : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := U.comp (D₁.comp W)
  let C_K : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := U.comp (D₂.comp W)
  let E₁ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x => ∑ j : Kc, (β j.1 * (w j.1 ⬝ᵥ x)) • vtilde j.1
      map_add' := fun x₁ x₂ => by
        simp [dotProduct_add, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp [dotProduct_smul, Finset.smul_sum, smul_smul, mul_left_comm] }
  let E₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x => ∑ j : Kc, (γ j.1 * (w j.1 ⬝ᵥ x)) • vtilde j.1
      map_add' := fun x₁ x₂ => by
        simp [dotProduct_add, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp [dotProduct_smul, Finset.smul_sum, smul_smul, mul_left_comm] }
  have hB_split : ∀ x : Fin n → ℂ, B *ᵥ x = B_K x + E₁ x := by
    intro x
    ext i
    dsimp only [B, B_K, E₁, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Pi.add_apply, Finset.sum_apply, ← Matrix.mulVec_mulVec, hA1_mat, hvtilde_sum β x i,
      sum_split_nz α]
    congr 1
    simp only [U, D₁, W, LinearMap.coe_mk, AddHom.coe_mk, u, b₁, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : α k.1 ≠ 0 := k.2
    field_simp [hne]
  have hC_split : ∀ x : Fin n → ℂ, C *ᵥ x = C_K x + E₂ x := by
    intro x
    ext i
    dsimp only [C, C_K, E₂, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Pi.add_apply, Finset.sum_apply, ← Matrix.mulVec_mulVec, hA2_mat, hvtilde_sum γ x i,
      sum_split_nz α]
    congr 1
    simp only [U, D₂, W, LinearMap.coe_mk, AddHom.coe_mk, u, b₂, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : α k.1 ≠ 0 := k.2
    field_simp [hne]
  let Φ₁ : (Fin n → ℂ) →ₗ[ℂ] LinearMap.ker U :=
    { toFun := fun x => ⟨Q (D₁ (W x)), hQ_ker _⟩
      map_add' := fun x₁ x₂ => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let Φ₂ : (Fin n → ℂ) →ₗ[ℂ] LinearMap.ker U :=
    { toFun := fun x => ⟨Q (D₂ (W x)), hQ_ker _⟩
      map_add' := fun x₁ x₂ => by ext; simp
      map_smul' := fun c x => by ext; simp }
  let Φ₃ : (Fin n → ℂ) →ₗ[ℂ] (Kc → ℂ) :=
    { toFun := fun x j => w j.1 ⬝ᵥ x
      map_add' := fun x₁ x₂ => by ext j; simp [dotProduct_add]
      map_smul' := fun c x => by ext j; simp [dotProduct_smul] }
  let Φ₄ : (Fin n → ℂ) →ₗ[ℂ] (Kc → ℂ) :=
    { toFun := fun x j => β j.1 * (w j.1 ⬝ᵥ (C *ᵥ x)) - γ j.1 * (w j.1 ⬝ᵥ (B_K x))
      map_add' := fun x₁ x₂ => by
        ext j
        simp only [Matrix.mulVec_add, map_add, dotProduct_add, Pi.add_apply]
        ring
      map_smul' := fun c x => by
        ext j
        simp only [Matrix.mulVec_smul, map_smul, dotProduct_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  let Φ : (Fin n → ℂ) →ₗ[ℂ] (LinearMap.ker U × LinearMap.ker U × (Kc → ℂ) × (Kc → ℂ)) :=
    Φ₁.prod (Φ₂.prod (Φ₃.prod Φ₄))
  have hker_dim : Module.finrank ℂ (LinearMap.ker U) + n = Fintype.card K := by
    have h := LinearMap.finrank_range_add_finrank_ker U
    rw [hU_range, finrank_top, Module.finrank_pi ℂ, Module.finrank_pi ℂ,
      Fintype.card_fin] at h
    omega
  have hcard_split : Fintype.card K + Fintype.card Kc = r := by
    let e : K ⊕ Kc ≃ Fin r :=
      { toFun := Sum.elim Subtype.val Subtype.val
        invFun := fun k => if h : α k ≠ 0 then Sum.inl ⟨k, h⟩ else Sum.inr ⟨k, not_not.mp h⟩
        left_inv := fun s => by
          cases s with
          | inl k => simp [k.2]
          | inr k => simp [k.2]
        right_inv := fun k => by
          by_cases h : α k ≠ 0 <;> simp [h] }
    have hcard := Fintype.card_congr e
    rw [Fintype.card_sum, Fintype.card_fin] at hcard
    exact hcard
  have hfinrank_lt :
      Module.finrank ℂ (LinearMap.ker U × LinearMap.ker U × (Kc → ℂ) × (Kc → ℂ)) <
        Module.finrank ℂ (Fin n → ℂ) := by
    simp only [Module.finrank_prod, Module.finrank_pi ℂ, Fintype.card_fin]
    omega
  have hker_ne : LinearMap.ker Φ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hfinrank_lt
  obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  rw [LinearMap.mem_ker] at hx_mem
  have hΦ₁ : Q (D₁ (W x)) = 0 := by
    have := congrArg (fun t => t.1.1) hx_mem
    simpa [Φ, Φ₁] using this
  have hΦ₂ : Q (D₂ (W x)) = 0 := by
    have := congrArg (fun t => t.2.1.1) hx_mem
    simpa [Φ, Φ₂] using this
  have hΦ₃ : ∀ j : Kc, w j.1 ⬝ᵥ x = 0 := by
    intro j
    have := congrFun (congrArg (fun t => t.2.2.1) hx_mem) j
    simpa [Φ, Φ₃] using this
  have hΦ₄ : ∀ j : Kc, β j.1 * (w j.1 ⬝ᵥ (C *ᵥ x)) - γ j.1 * (w j.1 ⬝ᵥ (B_K x)) = 0 := by
    intro j
    have := congrFun (congrArg (fun t => t.2.2.2) hx_mem) j
    simpa [Φ, Φ₄] using this
  have hE1x : E₁ x = 0 := by
    dsimp only [E₁, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hΦ₃ j]
  have hE2x : E₂ x = 0 := by
    dsimp only [E₂, LinearMap.coe_mk, AddHom.coe_mk]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hΦ₃ j]
  have hBK_CK : B_K (C_K x) = C_K (B_K x) := by
    have hWU1 : W (U (D₁ (W x))) = D₁ (W x) := by
      have : D₁ (W x) - W (U (D₁ (W x))) = 0 := hΦ₁
      exact (sub_eq_zero.mp this).symm
    have hWU2 : W (U (D₂ (W x))) = D₂ (W x) := by
      have : D₂ (W x) - W (U (D₂ (W x))) = 0 := hΦ₂
      exact (sub_eq_zero.mp this).symm
    have hD12 : D₁ (D₂ (W x)) = D₂ (D₁ (W x)) := by
      ext k
      simp only [D₁, D₂, LinearMap.coe_mk, AddHom.coe_mk]
      ring
    calc
      B_K (C_K x) = U (D₁ (W (U (D₂ (W x))))) := rfl
      _ = U (D₁ (D₂ (W x))) := by rw [hWU2]
      _ = U (D₂ (D₁ (W x))) := by rw [hD12]
      _ = U (D₂ (W (U (D₁ (W x))))) := by rw [hWU1]
      _ = C_K (B_K x) := rfl
  have hE12_diff : E₁ (C *ᵥ x) - E₂ (B_K x) = 0 := by
    dsimp only [E₁, E₂, LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← sub_smul, hΦ₄ j, zero_smul]
  have hcomm_BC : (B * C - C * B) *ᵥ x = 0 := by
    have hCx : C *ᵥ x = C_K x := by rw [hC_split x, hE2x, add_zero]
    have hBx : B *ᵥ x = B_K x := by rw [hB_split x, hE1x, add_zero]
    have hBCx : (B * C) *ᵥ x = B_K (C_K x) + E₁ (C *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, hCx, hB_split (C_K x), show E₁ (C_K x) = E₁ (C *ᵥ x) from congrArg E₁ hCx.symm]
    have hCBx : (C * B) *ᵥ x = C_K (B_K x) + E₂ (B_K x) := by
      rw [← Matrix.mulVec_mulVec, hBx, hC_split (B_K x)]
    rw [Matrix.sub_mulVec, hBCx, hCBx, hBK_CK]
    simpa [add_sub_add_left_eq_sub] using hE12_diff
  have hcomm_adj : commAdjugate T *ᵥ x = 0 := by
    have hmul_inv : A₀ * A₀⁻¹ = 1 := Matrix.mul_nonsing_inv A₀ hu
    have h1 : A₀ * (B * C) = A₁ * A₀⁻¹ * A₂ := by
      calc
        A₀ * (B * C) = (A₀ * A₀⁻¹) * (A₁ * (A₀⁻¹ * A₂)) := by
          simp only [B, C, Matrix.mul_assoc]
        _ = A₁ * A₀⁻¹ * A₂ := by
          rw [hmul_inv, Matrix.one_mul, Matrix.mul_assoc]
    have h2 : A₀ * (C * B) = A₂ * A₀⁻¹ * A₁ := by
      calc
        A₀ * (C * B) = (A₀ * A₀⁻¹) * (A₂ * (A₀⁻¹ * A₁)) := by
          simp only [B, C, Matrix.mul_assoc]
        _ = A₂ * A₀⁻¹ * A₁ := by
          rw [hmul_inv, Matrix.one_mul, Matrix.mul_assoc]
    have hmat : commAdjugate T = A₀.det • (A₀ * (B * C - C * B)) := by
      rw [Matrix.mul_sub, h1, h2]
      simp only [commAdjugate, A₀, A₁, A₂, hadj_eq, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have hsmul_mv : ∀ (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ),
        (c • M) *ᵥ y = c • (M *ᵥ y) := by
      intro c M y
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    rw [hmat, hsmul_mv, ← Matrix.mulVec_mulVec, hcomm_BC, Matrix.mulVec_zero, smul_zero]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx_ne, hcomm_adj⟩

end Arxiv08053777H1

open scoped Arxiv.«0805.3777» in
/-- The generic lower bound: hypothesis H1 of the reduction R1. -/
theorem Arxiv08053777H1.lower (p : ℕ) (hp : 1 ≤ p) :
    ∃ U : Set (Holor ℂ [3, 2 * p + 1, 2 * p + 1]),
      IsOpen U ∧ Dense U ∧ ∀ T ∈ U, 3 * p + 2 ≤ T.cprank := by
  obtain ⟨hopen, hdense⟩ := Arxiv08053777H1.open_and_dense_nonvanishing (n := 2 * p + 1) (by omega)
  refine ⟨{T | Arxiv08053777H1.polyObstruction T ≠ 0}, hopen, hdense, ?_⟩
  intro T hT
  by_contra! hlt
  have hle : T.cprank ≤ 3 * p + 1 := by omega
  have hcp : Holor.CPRankMax T.cprank T := by
    unfold Holor.cprank
    exact @Nat.find_spec (fun n => Holor.CPRankMax n T) (Classical.decPred _)
      ⟨([3, 2 * p + 1, 2 * p + 1] : List ℕ).prod, Holor.cprankMax_upper_bound T⟩
  have hdet0 : (Arxiv08053777H1.sliceMat T 0).det ≠ 0 := by
    intro h0
    apply hT
    simp [Arxiv08053777H1.polyObstruction, h0]
  have hcomm0 := Arxiv08053777H1.commAdjugate_det_eq_zero_of_cprankMax hle hcp hdet0
  apply hT
  simp [Arxiv08053777H1.polyObstruction, hcomm0]

namespace ThreeEven

/-- The tangent spaces at three points per two-dimensional block span the
entire space of tensors with three slices. -/
def Spans (p : ℕ) : Prop :=
  ∃ a : Fin (3*p) → Fin 3 → ℂ, ∃ b c : Fin (3*p) → Fin (2*p) → ℂ,
    ∀ T : Fin 3 → Fin (2*p) → Fin (2*p) → ℂ, ∃ u : Fin (3*p) → Fin 3 → ℂ,
      ∃ v w : Fin (3*p) → Fin (2*p) → ℂ, ∀ i j k,
        T i j k = ∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) +
          a t i * (b t j * w t k))

end ThreeEven

namespace ThreeEven

/-- Restriction to one two-by-two pair of coordinate blocks. The first term
is present when both block labels coincide. -/
def Cell (diagonal : Prop) [Decidable diagonal] (a₁ a₂ : Fin 3 → Fin 3 → ℂ)
    (b c : Fin 3 → Fin 2 → ℂ) : Prop :=
  ∀ T : Fin 3 → Fin 2 → Fin 2 → ℂ, ∃ u : Fin 3 → Fin 3 → ℂ, ∃ v w : Fin 3 → Fin 2 → ℂ, ∀ i j k,
    T i j k = ∑ t, (u t i * (if diagonal then b t j * c t k else 0) +
      a₂ t i * (v t j * c t k) + a₁ t i * (b t j * w t k))

end ThreeEven

namespace ThreeEven.Grid
open MvPolynomial

/-- A single surjective specialization gives a polynomial whose nonvanishing
guarantees surjectivity. Its determinant uses a fixed right inverse at that point. -/
lemma surjectivity_polynomial {I J V : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I J (MvPolynomial V ℂ)) (x₀ : V → ℂ)
    (h₀ : Function.Surjective (M.map (eval x₀)).mulVec) :
    ∃ Q : MvPolynomial V ℂ, Q ≠ 0 ∧ ∀ x : V → ℂ,
      eval x Q ≠ 0 → Function.Surjective (M.map (eval x)).mulVec := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h₀
  let D := M * B.map (C : ℂ →+* MvPolynomial V ℂ)
  have specialize (x : V → ℂ) : eval x D.det = (M.map (eval x) * B).det := by
    have hconst : (B.map (C : ℂ →+* MvPolynomial V ℂ)).map (eval x) = B := by
      ext i j
      simp [Matrix.map_apply]
    rw [RingHom.map_det, RingHom.mapMatrix_apply, show D = _ from rfl, Matrix.map_mul, hconst]
  have hvalue : eval x₀ D.det = 1 := by rw [specialize, hB, Matrix.det_one]
  refine ⟨D.det, ?_, ?_⟩
  · intro he
    rw [he, map_zero] at hvalue
    exact zero_ne_one hvalue
  · intro x hx
    rw [specialize] at hx
    have hprod : Function.Surjective (M.map (eval x) * B).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))
    intro y
    obtain ⟨z, hz⟩ := hprod y
    refine ⟨B.mulVec z, ?_⟩
    rw [Matrix.mulVec_mulVec]
    exact hz

lemma avoid_two {V : Type} {P Q : MvPolynomial V ℂ} (hP : P ≠ 0) (hQ : Q ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ eval x Q ≠ 0 := by
  by_contra! h
  apply (mul_ne_zero hP hQ)
  apply MvPolynomial.funext
  intro x
  rw [map_mul, map_zero]
  by_cases hx : eval x P = 0
  · exact mul_eq_zero.mpr (Or.inl hx)
  · exact mul_eq_zero.mpr (Or.inr (h x hx))

/-- Separate specializations can verify blocks depending on the same parameters:
the product of their certificate polynomials is nonzero over the complex numbers. -/
lemma simultaneous_surjectivity {K V : Type} [Fintype K] {I J : K → Type}
    [∀ k, Fintype (I k)] [∀ k, DecidableEq (I k)] [∀ k, Fintype (J k)]
    (M : ∀ k, Matrix (I k) (J k) (MvPolynomial V ℂ))
    (h : ∀ k, ∃ x : V → ℂ, Function.Surjective ((M k).map (eval x)).mulVec)
    (P : MvPolynomial V ℂ) (hP : P ≠ 0) :
    ∃ x : V → ℂ, eval x P ≠ 0 ∧ ∀ k, Function.Surjective ((M k).map (eval x)).mulVec := by
  classical
  choose z hz using h
  choose Q hQ hgood using fun k => surjectivity_polynomial (M k) (z k) (hz k)
  have hprod : (∏ k, Q k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hQ k
  obtain ⟨x, hx, hrest⟩ := avoid_two hP hprod
  have hvals : (∏ k, eval x (Q k)) ≠ 0 := by simpa only [map_prod] using hrest
  exact ⟨x, hx, fun k => hgood k x (Finset.prod_ne_zero_iff.mp hvals k (Finset.mem_univ k))⟩
end ThreeEven.Grid

namespace ThreeEven.Grid

open MvPolynomial

abbrev Param (G : Type) := (G × Fin 3) × (Fin 3 ⊕ (Fin 2 ⊕ Fin 2))
abbrev Row := Fin 3 × Fin 2 × Fin 2
abbrev Col := Fin 3 × (Fin 3 ⊕ (Fin 2 ⊕ Fin 2))

def a {G K : Type} (z : Param G → K) (g : G) (t i : Fin 3) := z ((g,t),Sum.inl i)
def b {G K : Type} (z : Param G → K) (g : G) (t : Fin 3) (j : Fin 2) := z ((g,t),Sum.inr (Sum.inl j))
def c {G K : Type} (z : Param G → K) (g : G) (t : Fin 3) (k : Fin 2) := z ((g,t),Sum.inr (Sum.inr k))

def mat {G K : Type} [DecidableEq G] [CommSemiring K] (z : Param G → K) (g h : G) : Matrix Row Col K
  | (i,j,k),(t,Sum.inl u) =>
      if u=i then (if g=h then b z g t j*c z h t k else 0) else 0
  | (i,j,k),(t,Sum.inr (Sum.inl u)) => if u=j then a z h t i*c z h t k else 0
  | (i,j,k),(t,Sum.inr (Sum.inr u)) => if u=k then a z g t i*b z g t j else 0

lemma action {G : Type} [DecidableEq G] (z : Param G → ℂ) (g h : G) (y : Col → ℂ)
    (i : Fin 3) (j k : Fin 2) : (mat z g h).mulVec y (i,j,k) =
      ∑ t, (y (t,Sum.inl i)*(if g=h then b z g t j*c z h t k else 0) +
        a z h t i*(y (t,Sum.inr (Sum.inl j))*c z h t k) + a z g t i*(b z g t j*y (t,Sum.inr (Sum.inr k)))) := by
  change (∑ q : Col, mat z g h (i,j,k) q*y q)=_
  by_cases he : g=h <;>
    simp [Fintype.sum_prod_type,Fintype.sum_sum_type,mat,he,Finset.sum_ite_eq',
      mul_comm,mul_left_comm,add_assoc]

lemma cell_iff {G : Type} [DecidableEq G] (z : Param G → ℂ) (g h : G) :
    Cell (g=h) (a z g) (a z h) (b z g) (c z h) ↔ Function.Surjective (mat z g h).mulVec := by
  constructor
  · intro hs T
    obtain ⟨u,v,w,ht⟩ := hs fun i j k => T (i,j,k)
    let y : Col → ℂ := fun q => q.2.elim (u q.1) (Sum.elim (v q.1) (w q.1))
    refine ⟨y,?_⟩
    funext r
    obtain ⟨i,j,k⟩ := r
    exact (action z g h y i j k).trans (ht i j k).symm
  · intro hs T
    obtain ⟨y,hy⟩ := hs fun r => T r.1 r.2.1 r.2.2
    refine ⟨fun t i => y (t,Sum.inl i),fun t j => y (t,Sum.inr (Sum.inl j)),
      fun t k => y (t,Sum.inr (Sum.inr k)),?_⟩
    intro i j k
    exact (congrFun hy (i,j,k)).symm.trans (action z g h y i j k)

lemma eval_matrix {G : Type} [DecidableEq G] (z : Param G → ℂ) (g h : G) :
    (mat (MvPolynomial.X : Param G → MvPolynomial (Param G) ℂ) g h).map (eval z)=mat z g h := by
  ext ⟨i,j,k⟩ ⟨t,u⟩
  rcases u with u | u | u
  · by_cases hu : u=i <;> by_cases he : g=h <;> simp [Matrix.map_apply,mat,b,c,hu,he]
  · by_cases hu : u=j <;> simp [Matrix.map_apply,mat,a,c,hu]
  · by_cases hu : u=k <;> simp [Matrix.map_apply,mat,a,b,hu]

def pad {G : Type} [DecidableEq G] (g : G) (f : Fin 2 → ℂ) (i : G×Fin 2) := if g=i.1 then f i.2 else 0

lemma assemble {G : Type} [Fintype G] [DecidableEq G] (z : Param G → ℂ)
    (hc : ∀g h, Cell (g=h) (a z g) (a z h) (b z g) (c z h))
    (T : Fin 3 → (G×Fin 2) → (G×Fin 2) → ℂ) :
    ∃ u : (G×Fin 3) → Fin 3 → ℂ, ∃ v w : (G×Fin 3) → (G×Fin 2) → ℂ, ∀ i j k,
    T i j k = ∑ t : G×Fin 3, (u t i * (pad t.1 (b z t.1 t.2) j * pad t.1 (c z t.1 t.2) k) +
      a z t.1 t.2 i * (v t j * pad t.1 (c z t.1 t.2) k) +
      a z t.1 t.2 i * (pad t.1 (b z t.1 t.2) j * w t k)) := by
  classical
  choose U V W hh using fun g h => hc g h (fun i j k => T i (g,j) (h,k))
  refine ⟨fun t => U t.1 t.1 t.2,fun t j => V j.1 t.1 t.2 j.2,fun t k => W t.1 k.1 t.2 k.2,?_⟩
  rintro i ⟨g,j⟩ ⟨h,k⟩
  rw [hh g h i j k]
  by_cases he : g=h
  · subst h
    simp [Fintype.sum_prod_type,pad,Finset.sum_add_distrib,ite_mul,mul_ite,Finset.sum_ite_irrel]
  · simp [Fintype.sum_prod_type,pad,he,Ne.symm he,Finset.sum_add_distrib,ite_mul,mul_ite,Finset.sum_ite_irrel]

end ThreeEven.Grid

namespace ThreeEven

private def delta (t i : Fin 3) : ℂ := if t=i then 1 else 0

private def direction (t : Fin 3) (j : Fin 2) : ℤ :=
  (![![1,0],![0,1],![1,1]] : Fin 3 → Fin 2 → ℤ) t j

private lemma vec_two {α : Type} (a : α) (f : Fin 2 → α) :
    Matrix.vecCons a f (2 : Fin 3) = f 1 := rfl

/-- For each slice the two diagonal entries are free. At the last point the
two variations in the second factor fix both off-diagonal entries. -/
lemma diagonal_cell :
    ∃ a : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell True a a b c := by
  refine ⟨delta,fun t j => (direction t j : ℂ),fun t k => (direction t k : ℂ),?_⟩
  intro T
  let u : Fin 3 → Fin 3 → ℂ :=
    ![![T 0 0 0,T 1 0 0,T 2 0 0-T 2 0 1],![T 0 1 1,T 1 1 1,T 2 1 1-T 2 1 0],![0,0,0]]
  let v : Fin 3 → Fin 2 → ℂ := ![![0,T 0 1 0],![T 1 0 1,0],![T 2 0 1,T 2 1 0]]
  let w : Fin 3 → Fin 2 → ℂ := ![![0,T 0 0 1],![T 1 1 0,0],![0,0]]
  refine ⟨u,v,w,?_⟩
  intro i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp (disch := decide) [Fin.sum_univ_three,u,v,w,delta,direction,vec_two]

private abbrev R := Fin 3 × Fin 2 × Fin 2
private abbrev Q := Fin 2 × Fin 3 × Fin 2

private def A (t i : Fin 3) : ℤ := (![![1,0,1],![1,1,0],![1,1,1]] : Fin 3 → Fin 3 → ℤ) t i
private def B (t : Fin 3) (j : Fin 2) : ℤ := (![![0,1],![1,0],![1,1]] : Fin 3 → Fin 2 → ℤ) t j

private def M : Matrix R Q ℤ := fun ⟨i,j,k⟩ ⟨q,t,h⟩ =>
  if q=0 then (if h=j then (if t=i then direction t k else 0) else 0)
  else (if h=k then A t i * B t j else 0)

private def entries : Array ℤ := #[
  1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, 1,
  0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, -1, 1, 1, -1, 0, 0,
  0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0,
  0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1,
  0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 1, -1,
  0, 0, 0, 1, 0, 0, -1, 0, 1, -1, 0, 0,
  0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0,
  0, 1, 0, 0, 0, 0, -1, 0, 1, -1, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 1, 0, -1, 1, 0, 0]

private def N : Matrix Q R ℤ := fun ⟨q,t,h⟩ ⟨i,j,k⟩ =>
  entries[((q.val*3+t.val)*2+h.val)*12 + (i.val*2+j.val)*2+k.val]?.getD 0

private lemma exact_inverse : M * N = 1 := by
  have h : ∀ (i : Fin 3) (j k : Fin 2) (a : Fin 3) (b c : Fin 2),
      (M * N) (i,j,k) (a,b,c) = (1 : Matrix R R ℤ) (i,j,k) (a,b,c) := by decide +kernel
  exact Matrix.ext fun ⟨i,j,k⟩ ⟨a,b,c⟩ => h i j k a b c


/-- The two independent three-point families give complementary directions
on the twelve coordinates of a pair of distinct blocks. -/
lemma off_diagonal_cell :
    ∃ a₁ a₂ : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell False a₁ a₂ b c := by
  classical
  have hs : Function.Surjective (M.map (Int.castRingHom ℂ)).mulVec := by
    apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
    refine ⟨N.map (Int.castRingHom ℂ), ?_⟩
    rw [← Matrix.map_mul,exact_inverse,← RingHom.mapMatrix_apply,map_one]
  refine ⟨fun t i => (A t i : ℂ),delta,fun t j => (B t j : ℂ),fun t k => (direction t k : ℂ),?_⟩
  intro T
  obtain ⟨y,hy⟩ := hs fun z => T z.1 z.2.1 z.2.2
  refine ⟨0,fun t j => y (0,t,j),fun t k => y (1,t,k),?_⟩
  intro i j k
  refine (congrFun hy (i,j,k)).symm.trans ?_
  change (∑ z : Q, ((M (i,j,k) z : ℤ) : ℂ) * y z) = _
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  simp [Fintype.sum_prod_type,M,delta,apply_ite,ite_mul,Finset.sum_ite_eq',Finset.sum_add_distrib,
    mul_comm,mul_left_comm]

end ThreeEven

namespace ThreeEven

open Arxiv.«0805.3777» Set Filter
open scoped Topology

namespace Dimension

lemma interior_polynomial_zero_locus {J : Type} (P : MvPolynomial J ℂ) (hP : P ≠ 0) :
    interior {y : J → ℂ | MvPolynomial.eval y P = 0} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hn := mem_interior_iff_mem_nhds.mp ha
  rw [nhds_pi, Filter.mem_pi] at hn
  obtain ⟨I, _, box, hin, hsub⟩ := hn
  apply hP
  apply MvPolynomial.funext_set box (fun j => infinite_of_mem_nhds (a j) (hin j))
  intro y hy
  have hyI : y ∈ I.pi box := fun j _ => hy j (Set.mem_univ _)
  have hzero : MvPolynomial.eval y P = 0 := hsub hyI
  simpa only [map_zero] using hzero

lemma eval_substitution {I J : Type} (F : J → MvPolynomial I ℂ) (x : I → ℂ)
    (P : MvPolynomial J ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval F P) =
      MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) P := by
  have he : (MvPolynomial.aeval x).comp (MvPolynomial.aeval F) =
      MvPolynomial.aeval (fun j => MvPolynomial.eval x (F j)) := by
    ext j
    simp [MvPolynomial.aeval_eq_eval]
  exact DFunLike.congr_fun he P

def index_cons_equiv (n : ℕ) (ds : List ℕ) : HolorIndex (n :: ds) ≃ Fin n × HolorIndex ds where
  toFun
    | ⟨i :: is, h⟩ => (⟨i, (List.forall₂_cons.mp h).1⟩, ⟨is, (List.forall₂_cons.mp h).2⟩)
    | ⟨[], h⟩ => nomatch h
  invFun q := ⟨q.1.val :: q.2.val, List.Forall₂.cons q.1.isLt q.2.property⟩
  left_inv := by
    rintro ⟨l, h⟩
    cases l with
    | nil => cases h
    | cons i is => rfl
  right_inv := by rintro ⟨⟨i, hi⟩, ⟨is, his⟩⟩; rfl

end Dimension

end ThreeEven

namespace ThreeEven.Dominance

open Set Filter
open ThreeEven.Dimension (interior_polynomial_zero_locus eval_substitution index_cons_equiv)
open scoped Topology Classical

lemma vector_is_simple {n : ℕ} (v : Holor ℂ [n]) : Holor.CPRankMax1 v := by
  let oneScalar : Holor ℂ [] := fun _ => 1
  have he : Holor.mul v oneScalar = v := by
    funext t
    change v t.take * (1 : ℂ) = v t
    rw [mul_one]
    congr 1
    apply Subtype.ext
    exact List.take_of_length_le t.property.length_eq.le
  rw [← he]
  exact Holor.CPRankMax1.cons _ _ (.nil _)

lemma tensor_sum_rank {d e f r : ℕ} (a : Fin r → Holor ℂ [d])
    (b : Fin r → Holor ℂ [e]) (c : Fin r → Holor ℂ [f]) :
    Holor.CPRankMax r (∑ i, Holor.mul (a i) (Holor.mul (b i) (c i))) := by
  have hs (i : Fin r) : Holor.CPRankMax1 (Holor.mul (a i) (Holor.mul (b i) (c i))) :=
    .cons _ _ (.cons _ _ (vector_is_simple (c i)))
  simpa using Holor.cprankMax_sum (n := 1) Finset.univ
    (fun i => Holor.mul (a i) (Holor.mul (b i) (c i))) (fun i _ => Holor.cprankMax_1 (hs i))

/-- A constructible spectral image containing the generic point contains a
principal open neighborhood of it. -/
lemma open_in_spectral_image {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hfp : φ.FinitePresentation) :
    ∃ f : A, f ≠ 0 ∧ ∀ q : PrimeSpectrum A, f ∉ q.asIdeal →
      q ∈ Set.range (PrimeSpectrum.comap φ) := by
  classical
  let z : PrimeSpectrum A := ⟨⊥, inferInstance⟩
  let w : PrimeSpectrum B := ⟨⊥, inferInstance⟩
  have hg : PrimeSpectrum.comap φ w = z := by
    apply PrimeSpectrum.ext
    change Ideal.comap φ ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hinj
  obtain ⟨T, hT⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  have hz : z ∈ T.toSet := by rw [hT]; exact ⟨w, hg⟩
  obtain ⟨C, hC, hzC⟩ := Set.mem_iUnion₂.mp hz
  change z ∈ PrimeSpectrum.zeroLocus (Set.range C.g) ∧
    z ∉ PrimeSpectrum.zeroLocus {C.f} at hzC
  have hg0 (i : Fin C.n) : C.g i = 0 := by
    have h := (PrimeSpectrum.mem_zeroLocus z _).mp hzC.1 (Set.mem_range_self i)
    exact (Ideal.mem_bot : C.g i ∈ (⊥ : Ideal A) ↔ _).mp h
  have hf0 : C.f ≠ 0 := by
    intro e
    apply hzC.2
    exact (PrimeSpectrum.mem_zeroLocus z _).mpr (Set.singleton_subset_iff.mpr (e ▸ z.asIdeal.zero_mem))
  refine ⟨C.f, hf0, ?_⟩
  intro q hq
  rw [← hT]
  apply Set.mem_iUnion₂.mpr
  refine ⟨C, hC, ?_⟩
  constructor
  · apply (PrimeSpectrum.mem_zeroLocus q _).mpr
    rintro _ ⟨i, rfl⟩
    rw [hg0 i]
    exact q.asIdeal.zero_mem
  · intro e
    exact hq ((PrimeSpectrum.mem_zeroLocus q _).mp e (Set.mem_singleton _))

/-- Hilbert's Nullstellensatz converts the principal open in the spectral image
to actual complex points in the image of the polynomial map. -/
lemma principal_open_in_image {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ)) :
    ∃ P : MvPolynomial J ℂ, P ≠ 0 ∧ ∀ y : J → ℂ, MvPolynomial.eval y P ≠ 0 →
      ∃ x : I → ℂ, ∀ j, MvPolynomial.eval x (F j) = y j := by
  classical
  let φ : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ := MvPolynomial.aeval F
  have hfp : φ.toRingHom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial J ℂ))
    have he : φ.toRingHom.comp (algebraMap ℂ (MvPolynomial J ℂ)) =
        algebraMap ℂ (MvPolynomial I ℂ) :=
      RingHom.ext (fun a => φ.commutes a)
    rw [he]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨P, hP, hU⟩ := open_in_spectral_image φ.toRingHom hinj hfp
  refine ⟨P, hP, ?_⟩
  intro y hy
  let m := MvPolynomial.pointToPoint (k := ℂ) y
  have hy' : P ∉ m.asIdeal := fun h => hy ((MvPolynomial.mem_vanishingIdeal_singleton_iff y P).mp h)
  obtain ⟨q, hq⟩ := hU m hy'
  obtain ⟨M, hM, hle⟩ := q.asIdeal.exists_le_maximal q.isPrime.ne_top
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x, ?_⟩
  intro j
  let v : MvPolynomial J ℂ := MvPolynomial.X j - MvPolynomial.C (y j)
  have hv : v ∈ m.asIdeal := by
    apply (MvPolynomial.mem_vanishingIdeal_singleton_iff y _).mpr
    simp [v]
  have hvq : φ v ∈ q.asIdeal := by
    change v ∈ (PrimeSpectrum.comap φ.toRingHom q).asIdeal
    rwa [hq]
  have hMx := hle hvq
  rw [hx] at hMx
  have he := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).mp hMx
  simpa [φ, v, MvPolynomial.aeval_eq_eval, sub_eq_zero] using he

lemma dense_image_interior_of_nonempty {I J : Type} [Finite I] [Finite J] (F : J → MvPolynomial I ℂ)
    (h : (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))).Nonempty) :
    Dense (interior (Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j)))) := by
  classical
  let image := Set.range (fun x : I → ℂ => fun j => MvPolynomial.eval x (F j))
  have hinj : Function.Injective (MvPolynomial.aeval F : MvPolynomial J ℂ →ₐ[ℂ] MvPolynomial I ℂ) := by
    apply algebraicIndependent_iff_injective_aeval.mp
    apply algebraicIndependent_iff.mpr
    intro Q hQ
    by_contra hne
    have hs : image ⊆ {y : J → ℂ | MvPolynomial.eval y Q = 0} := by
      rintro _ ⟨x, rfl⟩
      change MvPolynomial.eval (fun j => MvPolynomial.eval x (F j)) Q = 0
      rw [← eval_substitution F x Q, hQ, map_zero]
    obtain ⟨y, hy⟩ := h
    have bad := interior_mono hs hy
    rw [interior_polynomial_zero_locus Q hne] at bad
    exact bad
  obtain ⟨P, hP, hsurj⟩ := principal_open_in_image F hinj
  let Z := {y : J → ℂ | MvPolynomial.eval y P = 0}
  have ho : IsOpen Zᶜ := (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).isOpen_compl
  have hd : Dense Zᶜ := interior_eq_empty_iff_dense_compl.mp (interior_polynomial_zero_locus P hP)
  apply hd.mono
  apply interior_maximal _ ho
  intro y hy
  obtain ⟨x, hx⟩ := hsurj y hy
  exact ⟨x, funext hx⟩

/-- The derivative of each coordinate is the sum of its three factor variations. -/
lemma trilinear_image_has_interior {I J S : Type} [Fintype I] [Fintype J] [Fintype S]
    (a b c : S → J → I) (base : I → ℂ)
    (hspan : ∀ y : J → ℂ, ∃ z : I → ℂ, ∀ j,
      y j = ∑ t : S, (z (a t j) * (base (b t j) * base (c t j)) +
        base (a t j) * (z (b t j) * base (c t j)) +
        base (a t j) * (base (b t j) * z (c t j)))) :
    (interior (Set.range (fun x : I → ℂ => fun j : J =>
      ∑ t : S, x (a t j) * (x (b t j) * x (c t j))))).Nonempty := by
  classical
  let φ (x : I → ℂ) (j : J) := ∑ t : S, x (a t j) * (x (b t j) * x (c t j))
  let pr (i : I) : (I → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  let D : (I → ℂ) →L[ℂ] (J → ℂ) := ContinuousLinearMap.pi fun j =>
    ∑ t : S, (base (a t j) • (base (b t j) • pr (c t j) + base (c t j) • pr (b t j)) +
      (base (b t j) * base (c t j)) • pr (a t j))
  have hder : HasStrictFDerivAt φ D base := by
    apply hasStrictFDerivAt_pi.mpr
    intro j
    apply HasStrictFDerivAt.fun_sum
    intro t _
    exact (pr (a t j)).hasStrictFDerivAt.fun_mul
      ((pr (b t j)).hasStrictFDerivAt.fun_mul (pr (c t j)).hasStrictFDerivAt)
  have hsurj : Function.Surjective D := by
    intro y
    obtain ⟨z, hz⟩ := hspan y
    refine ⟨z, funext fun j => ?_⟩
    rw [hz j]
    simp only [D, ContinuousLinearMap.pi_apply, _root_.sum_apply,
      _root_.add_apply, _root_.smul_apply, smul_eq_mul, pr,
      ContinuousLinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hN : Set.range φ ∈ 𝓝 (φ base) := by
    rw [← hder.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hsurj)]
    exact Filter.range_mem_map
  exact ⟨φ base, mem_interior_iff_mem_nhds.mpr hN⟩

def index_nil_equiv : HolorIndex [] ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], .nil⟩
  left_inv := by rintro ⟨l, h⟩; cases h; rfl
  right_inv := by intro x; cases x; rfl

lemma finite_index (ds : List ℕ) : Finite (HolorIndex ds) := by
  induction ds with
  | nil => exact Finite.of_equiv Unit index_nil_equiv.symm
  | cons n ds ih =>
    let _ : Finite (HolorIndex ds) := ih
    exact Finite.of_equiv (Fin n × HolorIndex ds) (index_cons_equiv n ds).symm

lemma eval_holor_sum {ds : List ℕ} {r : ℕ} (u : Fin r → Holor ℂ ds) (j : HolorIndex ds) :
    (∑ i, u i) j = ∑ i, u i j :=
  Finset.sum_apply (M := fun _ : HolorIndex ds => ℂ) j Finset.univ (fun i x => u i x)

def point {d e f : ℕ} (i : Fin d) (j : Fin e) (k : Fin f) : HolorIndex [d,e,f] :=
  ⟨[i.val,j.val,k.val], .cons i.isLt (.cons j.isLt (.cons k.isLt .nil))⟩

lemma point_surjective {d e f : ℕ} (z : HolorIndex [d,e,f]) :
    ∃ i j k, z = point i j k := by
  obtain ⟨⟨i,z⟩,rfl⟩ := (index_cons_equiv d [e,f]).symm.surjective z
  obtain ⟨⟨j,z⟩,rfl⟩ := (index_cons_equiv e [f]).symm.surjective z
  obtain ⟨⟨k,z⟩,rfl⟩ := (index_cons_equiv f []).symm.surjective z
  obtain ⟨⟨⟩,rfl⟩ := index_nil_equiv.symm.surjective z
  exact ⟨i,j,k,rfl⟩

abbrev Coordinate (p : ℕ) := HolorIndex [3,2*p,2*p]
abbrev Parameter (p : ℕ) := Fin (3*p) × (Fin 3 ⊕ (Fin (2*p) ⊕ Fin (2*p)))

def entry {n : ℕ} (i : HolorIndex [n]) : Fin n := (index_cons_equiv n [] i).1

def first {p : ℕ} (t : Fin (3*p)) (z : Coordinate p) : Parameter p :=
  (t, Sum.inl (entry (HolorIndex.take (ds₁ := [3]) (ds₂ := [2*p,2*p]) z)))

def second {p : ℕ} (t : Fin (3*p)) (z : Coordinate p) : Parameter p :=
  (t, Sum.inr (.inl (entry (HolorIndex.take (ds₁ := [2*p]) (ds₂ := [2*p])
    (HolorIndex.drop (ds₁ := [3]) (ds₂ := [2*p,2*p]) z)))))

def third {p : ℕ} (t : Fin (3*p)) (z : Coordinate p) : Parameter p :=
  (t, Sum.inr (.inr (entry (HolorIndex.drop (ds₁ := [2*p]) (ds₂ := [2*p])
    (HolorIndex.drop (ds₁ := [3]) (ds₂ := [2*p,2*p]) z)))))

def pack {p : ℕ} (a : Fin (3*p) → Fin 3 → ℂ) (b c : Fin (3*p) → Fin (2*p) → ℂ)
    (q : Parameter p) : ℂ :=
  q.2.elim (a q.1) (Sum.elim (b q.1) (c q.1))

end ThreeEven.Dominance

namespace ThreeEven

open Set Dominance Arxiv.«0805.3777»

/-- Surjectivity of the tangent map at one parameter gives a dense open
set of tensors expressible as sums of at most 3p simple tensors. -/
theorem upper (p : ℕ) (hs : Spans p) : ∃ U : Set (Holor ℂ [3,2*p,2*p]),
    IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ 3*p := by
  classical
  obtain ⟨a,b,c,hspan⟩ := hs
  let _ : Finite (Coordinate p) := finite_index _
  let _ : Fintype (Coordinate p) := Fintype.ofFinite _
  let φ (x : Parameter p → ℂ) (j : Coordinate p) :=
    ∑ t : Fin (3*p), x (first t j) * (x (second t j) * x (third t j))
  have hopen : (interior (Set.range φ)).Nonempty := by
    apply trilinear_image_has_interior first second third (pack a b c)
    intro y
    obtain ⟨u,v,w,h⟩ := hspan fun i j k => y (point i j k)
    refine ⟨pack u v w, ?_⟩
    intro z
    obtain ⟨i,j,k,rfl⟩ := point_surjective z
    exact h i j k
  let F (j : Coordinate p) : MvPolynomial (Parameter p) ℂ :=
    ∑ t : Fin (3*p), MvPolynomial.X (first t j) *
      (MvPolynomial.X (second t j) * MvPolynomial.X (third t j))
  have he : (fun x : Parameter p → ℂ => fun j => MvPolynomial.eval x (F j)) = φ := by
    funext x j
    simp [F, φ]
  have hd := dense_image_interior_of_nonempty F (by rw [he]; exact hopen)
  rw [he] at hd
  refine ⟨interior (Set.range φ), isOpen_interior, hd, ?_⟩
  intro T hT
  obtain ⟨x,rfl⟩ := interior_subset hT
  let xa (t : Fin (3*p)) (i : HolorIndex [3]) := x (t, Sum.inl (entry i))
  let xb (t : Fin (3*p)) (j : HolorIndex [2*p]) := x (t, Sum.inr (.inl (entry j)))
  let xc (t : Fin (3*p)) (k : HolorIndex [2*p]) := x (t, Sum.inr (.inr (entry k)))
  have hx : (φ x : Holor ℂ [3,2*p,2*p]) = ∑ t, Holor.mul (xa t) (Holor.mul (xb t) (xc t)) := by
    funext j
    rw [eval_holor_sum]
    rfl
  rw [hx]
  exact Nat.find_min' _ (tensor_sum_rank xa xb xc)

end ThreeEven

namespace ThreeEven.Grid

open MvPolynomial

/-- The lemma `common`, with an extra polynomial condition on the parameters. -/
lemma common_avoiding {G : Type} [Fintype G] [DecidableEq G]
    (diag : ∃ a : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell True a a b c)
    (off : ∃ a₁ a₂ : Fin 3 → Fin 3 → ℂ, ∃ b c : Fin 3 → Fin 2 → ℂ, Cell False a₁ a₂ b c)
    (P : MvPolynomial (Param G) ℂ) (hP : P ≠ 0) :
    ∃ z : Param G → ℂ, eval z P ≠ 0 ∧
      ∀ g h : G, Cell (g=h) (a z g) (a z h) (b z g) (c z h) := by
  classical
  have separate (r : G×G) : ∃ z : Param G → ℂ, Function.Surjective
      ((mat (MvPolynomial.X : Param G → MvPolynomial (Param G) ℂ) r.1 r.2).map (eval z)).mulVec := by
    obtain ⟨g,h⟩ := r
    by_cases he : g=h
    · subst h
      obtain ⟨aa,bb,cc,hh⟩ := diag
      let z : Param G → ℂ := fun t => t.2.elim (aa t.1.2) (Sum.elim (bb t.1.2) (cc t.1.2))
      refine ⟨z,?_⟩
      rw [eval_matrix,← cell_iff]
      simpa [Cell,z,a,b,c] using hh
    · obtain ⟨a₁,a₂,bb,cc,hh⟩ := off
      let z : Param G → ℂ := fun t => t.2.elim (fun i => if t.1.1=g then a₁ t.1.2 i else a₂ t.1.2 i)
        (Sum.elim (bb t.1.2) (cc t.1.2))
      refine ⟨z,?_⟩
      rw [eval_matrix,← cell_iff]
      simpa [Cell,z,a,b,c,he,Ne.symm he] using hh
  obtain ⟨z,hzP,hz⟩ := simultaneous_surjectivity
    (fun r : G×G => mat (MvPolynomial.X : Param G → MvPolynomial (Param G) ℂ) r.1 r.2) separate P hP
  refine ⟨z,hzP,fun g h => (cell_iff z g h).mpr ?_⟩
  simpa only [eval_matrix] using hz (g,h)

end ThreeEven.Grid

namespace ThreeOdd

open MvPolynomial ThreeEven ThreeEven.Grid

theorem det_poly_ne_zero {σ : Type} [DecidableEq σ] (p q r s : σ) (hrp : r ≠ p) (hrq : r ≠ q) :
    (X p * X q - X r * X s : MvPolynomial σ ℂ) ≠ 0 := by
  intro h
  have h2 := congrArg (eval (fun x : σ => if x = p ∨ x = q then (1 : ℂ) else 0)) h
  simp [hrp, hrq] at h2

/-- The parameters at which the first coordinate of every `a` is nonzero and, in every block,
the first two `b` and the first two `c` are linearly independent. -/
noncomputable def good (G : Type) [Fintype G] : MvPolynomial (Param G) ℂ :=
  (∏ t : G × Fin 3, X ((t, Sum.inl 0) : Param G)) *
    ((∏ g : G, (X (((g, 0), Sum.inr (Sum.inl 0)) : Param G) *
          X (((g, 1), Sum.inr (Sum.inl 1)) : Param G) -
        X (((g, 0), Sum.inr (Sum.inl 1)) : Param G) *
          X (((g, 1), Sum.inr (Sum.inl 0)) : Param G))) *
      (∏ g : G, (X (((g, 0), Sum.inr (Sum.inr 0)) : Param G) *
          X (((g, 1), Sum.inr (Sum.inr 1)) : Param G) -
        X (((g, 0), Sum.inr (Sum.inr 1)) : Param G) *
          X (((g, 1), Sum.inr (Sum.inr 0)) : Param G))))

theorem good_ne_zero (G : Type) [Fintype G] [DecidableEq G] : good G ≠ 0 := by
  unfold good
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun t _ => X_ne_zero _)
    (mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun g _ => det_poly_ne_zero _ _ _ _ (by simp) (by simp))
      (Finset.prod_ne_zero_iff.mpr fun g _ => det_poly_ne_zero _ _ _ _ (by simp) (by simp)))

theorem good_spec {G : Type} [Fintype G] (z : Param G → ℂ) (h : eval z (good G) ≠ 0) :
    (∀ g t, a z g t 0 ≠ 0) ∧
    (∀ g, b z g 0 0 * b z g 1 1 - b z g 0 1 * b z g 1 0 ≠ 0) ∧
    (∀ g, c z g 0 0 * c z g 1 1 - c z g 0 1 * c z g 1 0 ≠ 0) := by
  simp only [good, map_mul, map_prod, map_sub, eval_X] at h
  have h1 := (mul_ne_zero_iff.mp h).1
  have h23 := (mul_ne_zero_iff.mp h).2
  have h2 := (mul_ne_zero_iff.mp h23).1
  have h3 := (mul_ne_zero_iff.mp h23).2
  exact ⟨fun g t => Finset.prod_ne_zero_iff.mp h1 (g, t) (Finset.mem_univ _),
    fun g => Finset.prod_ne_zero_iff.mp h2 g (Finset.mem_univ _),
    fun g => Finset.prod_ne_zero_iff.mp h3 g (Finset.mem_univ _)⟩

/-- Cramer's rule for two unknowns, with weights. -/
theorem solve2 (b0 b1 : Fin 2 → ℂ) (α0 α1 : ℂ) (hα0 : α0 ≠ 0) (hα1 : α1 ≠ 0)
    (hD : b0 0 * b1 1 - b0 1 * b1 0 ≠ 0) (L : Fin 2 → ℂ) :
    ∃ ω0 ω1 : ℂ, ∀ j, L j = α0 * (b0 j * ω0) + α1 * (b1 j * ω1) := by
  refine ⟨(L 0 * b1 1 - L 1 * b1 0) / (b0 0 * b1 1 - b0 1 * b1 0) / α0,
    (b0 0 * L 1 - b0 1 * L 0) / (b0 0 * b1 1 - b0 1 * b1 0) / α1, ?_⟩
  have key : ∀ (N D α x : ℂ), α ≠ 0 → α * (x * (N / D / α)) = x * N / D := by
    intro N D α x hα
    field_simp
  intro j
  rw [key _ _ _ _ hα0, key _ _ _ _ hα1, ← add_div, eq_div_iff hD]
  fin_cases j
  · show L 0 * (b0 0 * b1 1 - b0 1 * b1 0) =
      b0 0 * (L 0 * b1 1 - L 1 * b1 0) + b1 0 * (b0 0 * L 1 - b0 1 * L 0)
    ring
  · show L 1 * (b0 0 * b1 1 - b0 1 * b1 0) =
      b0 1 * (L 0 * b1 1 - L 1 * b1 0) + b1 1 * (b0 0 * L 1 - b0 1 * L 0)
    ring

/-- The tangent spaces at the points `(a t, b t, c t)` span all tensors with three slices. -/
def SpansOn (S J : Type) [Fintype S] : Prop :=
  ∃ a : S → Fin 3 → ℂ, ∃ b c : S → J → ℂ,
    ∀ T : Fin 3 → J → J → ℂ, ∃ u : S → Fin 3 → ℂ, ∃ v w : S → J → ℂ, ∀ i j k,
      T i j k = ∑ t, (u t i * (b t j * c t k) + a t i * (v t j * c t k) +
        a t i * (b t j * w t k))

theorem sum_succ (f : Fin 3 → ℂ) (hf : f 0 = 0) (i : Fin 3) :
    ∑ σ : Fin 2, (if i = σ.succ then (1 : ℂ) else 0) * f σ.succ = f i := by
  rw [Fin.sum_univ_two]
  fin_cases i
  · simp [hf]
  · simp
  · simp

/-- One more coordinate and two more points: the even configuration of `3 p` points, padded by
zero, together with two points `(e₁, e, e)` and `(e₂, e, e)` at the new coordinate `e`. -/
theorem spansOn_odd (G : Type) [Fintype G] [DecidableEq G] :
    SpansOn ((G × Fin 3) ⊕ Fin 2) ((G × Fin 2) ⊕ Unit) := by
  classical
  obtain ⟨z, hzP, hz⟩ := common_avoiding (G := G) diagonal_cell off_diagonal_cell (good G)
    (good_ne_zero G)
  obtain ⟨ha0, hbdet, hcdet⟩ := good_spec z hzP
  refine ⟨Sum.elim (fun t => a z t.1 t.2) (fun σ i => if i = σ.succ then 1 else 0),
    Sum.elim (fun t => Sum.elim (pad t.1 (b z t.1 t.2)) (fun _ => 0))
      (fun _ => Sum.elim (fun _ => 0) (fun _ => 1)),
    Sum.elim (fun t => Sum.elim (pad t.1 (c z t.1 t.2)) (fun _ => 0))
      (fun _ => Sum.elim (fun _ => 0) (fun _ => 1)), ?_⟩
  intro T
  obtain ⟨u₀, v₀, w₀, h₀⟩ := assemble z hz (fun i j k => T i (Sum.inl j) (Sum.inl k))
  choose ω0 ω1 hω using fun g => solve2 (b z g 0) (b z g 1) (a z g 0 0) (a z g 1 0)
    (ha0 g 0) (ha0 g 1) (hbdet g) (fun j => T 0 (Sum.inl (g, j)) (Sum.inr ()))
  choose ν0 ν1 hν using fun g => solve2 (c z g 0) (c z g 1) (a z g 0 0) (a z g 1 0)
    (ha0 g 0) (ha0 g 1) (hcdet g) (fun k => T 0 (Sum.inr ()) (Sum.inl (g, k)))
  let ω : G × Fin 3 → ℂ := fun t => if t.2 = 0 then ω0 t.1 else if t.2 = 1 then ω1 t.1 else 0
  let ν : G × Fin 3 → ℂ := fun t => if t.2 = 0 then ν0 t.1 else if t.2 = 1 then ν1 t.1 else 0
  have hcol : ∀ (i : Fin 3) (gj : G × Fin 2),
      ∑ t : G × Fin 3, a z t.1 t.2 i * (pad t.1 (b z t.1 t.2) gj * ω t) =
        a z gj.1 0 i * (b z gj.1 0 gj.2 * ω0 gj.1) +
          a z gj.1 1 i * (b z gj.1 1 gj.2 * ω1 gj.1) := by
    rintro i ⟨g, j⟩
    rw [Fintype.sum_prod_type, Finset.sum_eq_single g]
    · simp [pad, Fin.sum_univ_three, ω]
    · intro g' _ hne
      simp [pad, hne]
    · intro h
      exact absurd (Finset.mem_univ g) h
  have hrow : ∀ (i : Fin 3) (gk : G × Fin 2),
      ∑ t : G × Fin 3, a z t.1 t.2 i * (ν t * pad t.1 (c z t.1 t.2) gk) =
        a z gk.1 0 i * (c z gk.1 0 gk.2 * ν0 gk.1) +
          a z gk.1 1 i * (c z gk.1 1 gk.2 * ν1 gk.1) := by
    rintro i ⟨g, k⟩
    rw [Fintype.sum_prod_type, Finset.sum_eq_single g]
    · simp [pad, Fin.sum_univ_three, ν, mul_comm]
    · intro g' _ hne
      simp [pad, hne]
    · intro h
      exact absurd (Finset.mem_univ g) h
  let colRes : G × Fin 2 → Fin 3 → ℂ := fun gj i => T i (Sum.inl gj) (Sum.inr ()) -
    (a z gj.1 0 i * (b z gj.1 0 gj.2 * ω0 gj.1) + a z gj.1 1 i * (b z gj.1 1 gj.2 * ω1 gj.1))
  let rowRes : G × Fin 2 → Fin 3 → ℂ := fun gk i => T i (Sum.inr ()) (Sum.inl gk) -
    (a z gk.1 0 i * (c z gk.1 0 gk.2 * ν0 gk.1) + a z gk.1 1 i * (c z gk.1 1 gk.2 * ν1 gk.1))
  have hcol0 : ∀ gj, colRes gj 0 = 0 := by
    rintro ⟨g, j⟩
    exact sub_eq_zero.mpr (hω g j)
  have hrow0 : ∀ gk, rowRes gk 0 = 0 := by
    rintro ⟨g, k⟩
    exact sub_eq_zero.mpr (hν g k)
  refine ⟨Sum.elim u₀ (fun σ i => if σ = 0 then T i (Sum.inr ()) (Sum.inr ()) else 0),
    Sum.elim (fun t => Sum.elim (v₀ t) (fun _ => ν t))
      (fun σ => Sum.elim (fun gj => colRes gj σ.succ) (fun _ => 0)),
    Sum.elim (fun t => Sum.elim (w₀ t) (fun _ => ω t))
      (fun σ => Sum.elim (fun gk => rowRes gk σ.succ) (fun _ => 0)), ?_⟩
  intro i j k
  rw [Fintype.sum_sum_type]
  rcases j with j | ⟨⟩ <;> rcases k with k | ⟨⟩
  · simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
    exact h₀ i j k
  · simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, add_zero, zero_add, mul_one]
    rw [hcol i j, sum_succ (colRes j) (hcol0 j) i]
    simp only [colRes]
    ring
  · simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, zero_mul, add_zero, zero_add, one_mul]
    rw [hrow i k, sum_succ (rowRes k) (hrow0 k) i]
    simp only [rowRes]
    ring
  · simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, zero_mul, add_zero, zero_add, mul_one,
      Finset.sum_const_zero]
    rw [Fin.sum_univ_two]
    simp

theorem spansOn_fin (p : ℕ) : SpansOn (Fin (3 * p + 2)) (Fin (2 * p + 1)) := by
  classical
  obtain ⟨A, B, C, h⟩ := spansOn_odd (Fin p)
  let eS : Fin (3 * p + 2) ≃ (Fin p × Fin 3) ⊕ Fin 2 := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin]
    omega)
  let eJ : Fin (2 * p + 1) ≃ (Fin p × Fin 2) ⊕ Unit := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_unit]
    omega)
  refine ⟨fun t => A (eS t), fun t j => B (eS t) (eJ j), fun t k => C (eS t) (eJ k), ?_⟩
  intro T
  obtain ⟨u, v, w, huvw⟩ := h (fun i j k => T i (eJ.symm j) (eJ.symm k))
  refine ⟨fun t => u (eS t), fun t j => v (eS t) (eJ j), fun t k => w (eS t) (eJ k), ?_⟩
  intro i j k
  have h1 := huvw i (eJ j) (eJ k)
  simp only [Equiv.symm_apply_apply] at h1
  rw [h1]
  exact (eS.sum_comp (fun t => u t i * (B t (eJ j) * C t (eJ k)) +
    A t i * (v t (eJ j) * C t (eJ k)) + A t i * (B t (eJ j) * w t (eJ k)))).symm

abbrev Coord (n : ℕ) := HolorIndex [3, n, n]
abbrev Par (n r : ℕ) := Fin r × (Fin 3 ⊕ (Fin n ⊕ Fin n))

def gfirst {n r : ℕ} (t : Fin r) (z : Coord n) : Par n r :=
  (t, Sum.inl (Dominance.entry (HolorIndex.take (ds₁ := [3]) (ds₂ := [n, n]) z)))

def gsecond {n r : ℕ} (t : Fin r) (z : Coord n) : Par n r :=
  (t, Sum.inr (.inl (Dominance.entry (HolorIndex.take (ds₁ := [n]) (ds₂ := [n])
    (HolorIndex.drop (ds₁ := [3]) (ds₂ := [n, n]) z)))))

def gthird {n r : ℕ} (t : Fin r) (z : Coord n) : Par n r :=
  (t, Sum.inr (.inr (Dominance.entry (HolorIndex.drop (ds₁ := [n]) (ds₂ := [n])
    (HolorIndex.drop (ds₁ := [3]) (ds₂ := [n, n]) z)))))

def gpack {n r : ℕ} (a : Fin r → Fin 3 → ℂ) (b c : Fin r → Fin n → ℂ) (q : Par n r) : ℂ :=
  q.2.elim (a q.1) (Sum.elim (b q.1) (c q.1))

open Set Arxiv.«0805.3777» in
/-- The theorem `ThreeEven.upper` for a general number of points and a general side length. -/
theorem upper_gen (n r : ℕ) (hs : SpansOn (Fin r) (Fin n)) :
    ∃ U : Set (Holor ℂ [3, n, n]), IsOpen U ∧ Dense U ∧ ∀ T ∈ U, T.cprank ≤ r := by
  classical
  obtain ⟨a,b,c,hspan⟩ := hs
  let _ : Finite (Coord n) := Dominance.finite_index _
  let _ : Fintype (Coord n) := Fintype.ofFinite _
  let φ (x : Par n r → ℂ) (j : Coord n) :=
    ∑ t : Fin r, x (gfirst t j) * (x (gsecond t j) * x (gthird t j))
  have hopen : (interior (Set.range φ)).Nonempty := by
    apply Dominance.trilinear_image_has_interior gfirst gsecond gthird (gpack a b c)
    intro y
    obtain ⟨u,v,w,h⟩ := hspan fun i j k => y (Dominance.point i j k)
    refine ⟨gpack u v w, ?_⟩
    intro z
    obtain ⟨i,j,k,rfl⟩ := Dominance.point_surjective z
    exact h i j k
  let F (j : Coord n) : MvPolynomial (Par n r) ℂ :=
    ∑ t : Fin r, MvPolynomial.X (gfirst t j) *
      (MvPolynomial.X (gsecond t j) * MvPolynomial.X (gthird t j))
  have he : (fun x : Par n r → ℂ => fun j => MvPolynomial.eval x (F j)) = φ := by
    funext x j
    simp [F, φ]
  have hd := Dominance.dense_image_interior_of_nonempty F (by rw [he]; exact hopen)
  rw [he] at hd
  refine ⟨interior (Set.range φ), isOpen_interior, hd, ?_⟩
  intro T hT
  obtain ⟨x,rfl⟩ := interior_subset hT
  let xa (t : Fin r) (i : HolorIndex [3]) := x (t, Sum.inl (Dominance.entry i))
  let xb (t : Fin r) (j : HolorIndex [n]) := x (t, Sum.inr (.inl (Dominance.entry j)))
  let xc (t : Fin r) (k : HolorIndex [n]) := x (t, Sum.inr (.inr (Dominance.entry k)))
  have hx : (φ x : Holor ℂ [3,n,n]) = ∑ t, Holor.mul (xa t) (Holor.mul (xb t) (xc t)) := by
    funext j
    rw [Dominance.eval_holor_sum]
    rfl
  rw [hx]
  exact Nat.find_min' _ (Dominance.tensor_sum_rank xa xb xc)

open Arxiv.«0805.3777» in
/-- The generic upper bound: tensors of rank at most `3 p + 2` contain a dense open set. -/
theorem upper (p : ℕ) : ∃ V : Set (Holor ℂ [3, 2 * p + 1, 2 * p + 1]),
    IsOpen V ∧ Dense V ∧ ∀ T ∈ V, T.cprank ≤ 3 * p + 2 :=
  upper_gen (2 * p + 1) (3 * p + 2) (spansOn_fin p)

end ThreeOdd

open scoped Arxiv.«0805.3777» in
theorem OMA.solution : type_of% @Arxiv.«0805.3777».isGenericRank_three_odd := by
  intro p hp
  have hDen : 0 < 4 * p + 3 := by omega
  have hNumerator : 3 * (2 * p + 1) ^ 2 = (4 * p + 3) * (3 * p) + (3 * p + 3) := by
    ring
  have hCeil : 3 * (2 * p + 1) ^ 2 ⌈/⌉ (4 * p + 3) = 3 * p + 1 := by
    apply Nat.le_antisymm
    · apply (ceilDiv_le_iff_le_mul hDen).2
      rw [hNumerator, Nat.mul_add, Nat.mul_one]
      omega
    · by_contra! h
      have hSmall : 3 * (2 * p + 1) ^ 2 ⌈/⌉ (4 * p + 3) ≤ 3 * p := by omega
      have hLe := (ceilDiv_le_iff_le_mul hDen).1 hSmall
      rw [hNumerator] at hLe
      omega
  rw [hCeil]
  obtain ⟨U, hUOpen, hUDense, hURank⟩ := Arxiv08053777H1.lower p hp
  obtain ⟨V, hVOpen, hVDense, hVRank⟩ := ThreeOdd.upper p
  refine ⟨U ∩ V, hUOpen.inter hVOpen, hUDense.inter_of_isOpen_left hVDense hUOpen, ?_⟩
  intro T hT
  exact Nat.le_antisymm (hVRank T hT.2) (hURank T hT.1)
