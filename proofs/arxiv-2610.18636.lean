import OMAStatements.S_arxiv_2610_18636
import Mathlib

namespace OMA.P_arxiv_2610_18636

open OMA.S_arxiv_2610_18636 Polynomial Matrix

/-- The counterexample graph `H_4 = 3 K_1 ∇ (K_1 ∪ K_{4,4})` on `Fin 12`:
blocks are `0 = {0,1,2}` (size 3), `1 = {3}` (size 1), `2 = {4,5,6,7}` (size 4),
`3 = {8,9,10,11}` (size 4), with complete joins between blocks `(0,1), (0,2), (0,3), (2,3)`. -/
def h4Part (u : Fin 12) : Fin 4 :=
  if u.val < 3 then 0 else if u.val < 4 then 1 else if u.val < 8 then 2 else 3

def h4BlockAdj (a b : Fin 4) : Bool :=
  (a == 0 && b != 0) || (b == 0 && a != 0) ||
  (a == 2 && b == 3) || (a == 3 && b == 2)

def H4 : SimpleGraph (Fin 12) where
  Adj u v := h4BlockAdj (h4Part u) (h4Part v) = true
  symm := ⟨by
    intro u v h
    revert u v h; decide⟩
  loopless := ⟨by
    intro u h
    revert u h; decide⟩

lemma H4_not_iso_K444 : ¬ Nonempty (H4 ≃g completeTripartite3 4 4 4) := by
  rintro ⟨e⟩
  classical
  have hdeg3 : (Finset.univ.filter (fun u : Fin 12 => H4.Adj 3 u)).card = 3 := by
    have hd : (Finset.univ.filter (fun u : Fin 12 => h4BlockAdj (h4Part 3) (h4Part u) = true)).card = 3 := by
      decide
    convert hd using 1
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hdegK : ∀ w : Fin 12,
      (Finset.univ.filter (fun u : Fin 12 => (completeTripartite3 4 4 4).Adj w u)).card = 8 := by
    intro w
    have hd : (Finset.univ.filter (fun u : Fin 12 =>
        (if w.val < 4 then (0 : Fin 3) else if w.val < 8 then 1 else 2) ≠
        (if u.val < 4 then (0 : Fin 3) else if u.val < 8 then 1 else 2))).card = 8 := by
      revert w; decide
    convert hd using 1
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have hcard : (Finset.univ.filter (fun u : Fin 12 => H4.Adj 3 u)).card =
      (Finset.univ.filter (fun u : Fin 12 => (completeTripartite3 4 4 4).Adj (e 3) u)).card := by
    refine Finset.card_bij (fun u _ => e u) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact e.map_rel_iff.mpr hu
    · intro u _ v _ huv
      exact e.injective huv
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : (completeTripartite3 4 4 4).Adj (e 3) (e (e.symm v)) := by
        simpa using hv
      exact e.map_rel_iff.mp h1
  rw [hdeg3, hdegK (e 3)] at hcard
  omega

/-- Characteristic polynomial commutes with ring homomorphisms `ℤ →+* ℝ`. -/
lemma charpoly_map_int {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.map (Int.castRingHom ℝ)).charpoly = A.charpoly.map (Int.castRingHom ℝ) := by
  simp only [Matrix.charpoly, Matrix.charmatrix]
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.scalar_apply,
    Matrix.diagonal_apply, map_sub, Polynomial.coe_mapRingHom, Polynomial.map_C]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- Conjugate matrices over `ℤ` have the same characteristic polynomial. -/
lemma charpoly_eq_of_conj {n : ℕ} (A P Pinv M : Matrix (Fin n) (Fin n) ℤ)
    (hPP : P * Pinv = 1) (hsim : Pinv * A * P = M) :
    A.charpoly = M.charpoly := by
  rw [← hsim, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hPP, Matrix.one_mul]

/-- Characteristic polynomial of a block lower-triangular matrix `fromBlocks Q 0 R 0` over `ℤ`. -/
lemma charpoly_fromBlocks_zero_right {k m : ℕ}
    (Q : Matrix (Fin k) (Fin k) ℤ) (R : Matrix (Fin m) (Fin k) ℤ) :
    (Matrix.fromBlocks Q (0 : Matrix (Fin k) (Fin m) ℤ) R (0 : Matrix (Fin m) (Fin m) ℤ)).charpoly =
      Q.charpoly * Polynomial.X ^ m := by
  unfold Matrix.charpoly
  have hcm :
      (Matrix.fromBlocks Q (0 : Matrix (Fin k) (Fin m) ℤ) R
        (0 : Matrix (Fin m) (Fin m) ℤ)).charmatrix =
      Matrix.fromBlocks Q.charmatrix 0 (-(R.map Polynomial.C))
        (Matrix.scalar (Fin m) Polynomial.X) := by
    ext (i | i) (j | j) <;>
      simp [Matrix.charmatrix, Matrix.fromBlocks, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [hcm, Matrix.det_fromBlocks_zero₁₂, Matrix.scalar_apply, Matrix.det_diagonal]
  simp [Finset.prod_const]

/-- Integer adjacency matrix helper. -/
def adjZ (f : Fin 12 → Fin 12 → Bool) : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of fun i j => if f i j then 1 else 0

lemma adjMatrix_eq_map_adjZ {G : SimpleGraph (Fin 12)} [DecidableRel G.Adj]
    (f : Fin 12 → Fin 12 → Bool) (hf : ∀ i j, G.Adj i j ↔ f i j = true) :
    G.adjMatrix ℝ = (adjZ f).map (Int.castRingHom ℝ) := by
  ext i j
  simp only [SimpleGraph.adjMatrix_apply, Matrix.map_apply, adjZ, Matrix.of_apply,
    Int.coe_castRingHom]
  by_cases h : G.Adj i j
  · have h' : f i j = true := (hf i j).mp h
    simp [h, h']
  · have h' : f i j = false := Bool.eq_false_iff.mpr (fun ht => h ((hf i j).mpr ht))
    simp [h, h']

/-- Block similarity helper for `k` blocks on `Fin 12` (so `k + m = 12`). -/
def mkP (k : ℕ) (blockOf : Fin 12 → Fin k) (reps : Fin k → Fin 12)
    (others : Fin (12 - k) → Fin 12) : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of fun r c =>
    if hc : c.val < k then
      if r = reps ⟨c.val, hc⟩ then 1 else 0
    else
      let v := others ⟨c.val - k, by omega⟩
      let rep := reps (blockOf v)
      if r = v then 1 else if r = rep then -1 else 0

def mkPinv (k : ℕ) (blockOf : Fin 12 → Fin k)
    (others : Fin (12 - k) → Fin 12) : Matrix (Fin 12) (Fin 12) ℤ :=
  Matrix.of fun r c =>
    if hr : r.val < k then
      if blockOf c = ⟨r.val, hr⟩ then 1 else 0
    else
      if c = others ⟨r.val - k, by omega⟩ then 1 else 0

/-! ### 1. Characteristic polynomial of `K_{4,4,4}` -/

def k0Block (u : Fin 12) : Fin 3 :=
  if u.val < 4 then 0 else if u.val < 8 then 1 else 2

def k0AdjB (u v : Fin 12) : Bool := k0Block u != k0Block v
def k0Reps : Fin 3 → Fin 12 := ![0, 4, 8]
def k0Others : Fin 9 → Fin 12 := ![1, 2, 3, 5, 6, 7, 9, 10, 11]
def k0P := mkP 3 k0Block k0Reps k0Others
def k0Pinv := mkPinv 3 k0Block k0Others
def k0Q : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => if i = j then 0 else 4
def k0M := k0Pinv * adjZ k0AdjB * k0P
def k0R : Matrix (Fin 9) (Fin 3) ℤ :=
  Matrix.of fun i j => k0M (Fin.natAdd 3 i) (Fin.castAdd 9 j)

lemma k0_PP : k0P * k0Pinv = 1 := by
  ext i j; simp only [Matrix.mul_apply, Matrix.one_apply]; revert i j; decide

lemma k0_M_11 : ∀ i j : Fin 3, k0M (Fin.castAdd 9 i) (Fin.castAdd 9 j) = k0Q i j := by
  intro i j; simp only [k0M, k0Q, Matrix.mul_apply, Matrix.of_apply]; revert i j; decide
lemma k0_M_12 : ∀ (i : Fin 3) (j : Fin 9), k0M (Fin.castAdd 9 i) (Fin.natAdd 3 j) = 0 := by
  intro i j; simp only [k0M, Matrix.mul_apply]; revert i j; decide
lemma k0_M_22 : ∀ i j : Fin 9, k0M (Fin.natAdd 3 i) (Fin.natAdd 3 j) = 0 := by
  intro i j; simp only [k0M, Matrix.mul_apply]; revert i j; decide

lemma k0_M_reindex :
    k0M.reindex (finSumFinEquiv (m := 3) (n := 9)).symm (finSumFinEquiv (m := 3) (n := 9)).symm =
    Matrix.fromBlocks k0Q 0 k0R 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  · exact k0_M_11 i j
  · exact k0_M_12 i j
  · rfl
  · exact k0_M_22 i j

lemma k0Q_charpoly : k0Q.charpoly = (X - C 8) * (X + C 4) ^ 2 := by
  unfold Matrix.charpoly
  rw [Matrix.det_fin_three]
  simp [Matrix.charmatrix, Matrix.scalar_apply, k0Q]
  ring

lemma K0_charpoly [DecidableRel (completeTripartite3 4 4 4).Adj] :
    ((completeTripartite3 4 4 4).adjMatrix ℝ).charpoly =
      X ^ 9 * (X - C 8) * (X + C 4) ^ 2 := by
  have hadj : (completeTripartite3 4 4 4).adjMatrix ℝ = (adjZ k0AdjB).map (Int.castRingHom ℝ) := by
    refine adjMatrix_eq_map_adjZ k0AdjB (fun i j => ?_)
    simp [completeTripartite3, k0AdjB, k0Block, bne_iff_ne]
  rw [hadj, charpoly_map_int]
  have h1 : (adjZ k0AdjB).charpoly = k0M.charpoly :=
    charpoly_eq_of_conj (adjZ k0AdjB) k0P k0Pinv k0M k0_PP rfl
  have h2 : k0M.charpoly = (Matrix.fromBlocks k0Q 0 k0R 0).charpoly := by
    rw [← k0_M_reindex, Matrix.charpoly_reindex]
  rw [h1, h2, charpoly_fromBlocks_zero_right, k0Q_charpoly]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C]
  simp only [map_ofNat]
  ring

/-! ### 2. Characteristic polynomial of `K_{3,4,5}` -/

def k1Block (u : Fin 12) : Fin 3 :=
  if u.val < 3 then 0 else if u.val < 7 then 1 else 2

def k1AdjB (u v : Fin 12) : Bool := k1Block u != k1Block v
def k1Reps : Fin 3 → Fin 12 := ![0, 3, 7]
def k1Others : Fin 9 → Fin 12 := ![1, 2, 4, 5, 6, 8, 9, 10, 11]
def k1P := mkP 3 k1Block k1Reps k1Others
def k1Pinv := mkPinv 3 k1Block k1Others
def k1Q : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => if i = j then 0 else match i.val with | 0 => 3 | 1 => 4 | _ => 5
def k1M := k1Pinv * adjZ k1AdjB * k1P
def k1R : Matrix (Fin 9) (Fin 3) ℤ :=
  Matrix.of fun i j => k1M (Fin.natAdd 3 i) (Fin.castAdd 9 j)

lemma k1_PP : k1P * k1Pinv = 1 := by
  ext i j; simp only [Matrix.mul_apply, Matrix.one_apply]; revert i j; decide

lemma k1_M_11 : ∀ i j : Fin 3, k1M (Fin.castAdd 9 i) (Fin.castAdd 9 j) = k1Q i j := by
  intro i j; simp only [k1M, k1Q, Matrix.mul_apply, Matrix.of_apply]; revert i j; decide
lemma k1_M_12 : ∀ (i : Fin 3) (j : Fin 9), k1M (Fin.castAdd 9 i) (Fin.natAdd 3 j) = 0 := by
  intro i j; simp only [k1M, Matrix.mul_apply]; revert i j; decide
lemma k1_M_22 : ∀ i j : Fin 9, k1M (Fin.natAdd 3 i) (Fin.natAdd 3 j) = 0 := by
  intro i j; simp only [k1M, Matrix.mul_apply]; revert i j; decide

lemma k1_M_reindex :
    k1M.reindex (finSumFinEquiv (m := 3) (n := 9)).symm (finSumFinEquiv (m := 3) (n := 9)).symm =
    Matrix.fromBlocks k1Q 0 k1R 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  · exact k1_M_11 i j
  · exact k1_M_12 i j
  · rfl
  · exact k1_M_22 i j

lemma k1Q_charpoly : k1Q.charpoly = X ^ 3 - C 47 * X - C 120 := by
  unfold Matrix.charpoly
  rw [Matrix.det_fin_three]
  simp [Matrix.charmatrix, Matrix.scalar_apply, k1Q]
  ring

lemma K1_charpoly [DecidableRel (completeTripartite3 4 3 4).Adj] :
    ((completeTripartite3 4 3 4).adjMatrix ℝ).charpoly =
      X ^ 9 * (X ^ 3 - C 47 * X - C 120) := by
  have hadj : (completeTripartite3 4 3 4).adjMatrix ℝ = (adjZ k1AdjB).map (Int.castRingHom ℝ) := by
    refine adjMatrix_eq_map_adjZ k1AdjB (fun i j => ?_)
    simp [completeTripartite3, k1AdjB, k1Block, bne_iff_ne]
  rw [hadj, charpoly_map_int]
  have h1 : (adjZ k1AdjB).charpoly = k1M.charpoly :=
    charpoly_eq_of_conj (adjZ k1AdjB) k1P k1Pinv k1M k1_PP rfl
  have h2 : k1M.charpoly = (Matrix.fromBlocks k1Q 0 k1R 0).charpoly := by
    rw [← k1_M_reindex, Matrix.charpoly_reindex]
  rw [h1, h2, charpoly_fromBlocks_zero_right, k1Q_charpoly]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C]
  simp only [map_ofNat]
  ring

/-! ### 3. Characteristic polynomial of `H_4` -/

def h4AdjB (u v : Fin 12) : Bool := h4BlockAdj (h4Part u) (h4Part v)
def h4Reps : Fin 4 → Fin 12 := ![0, 3, 4, 8]
def h4Others : Fin 8 → Fin 12 := ![1, 2, 5, 6, 7, 9, 10, 11]
def h4P := mkP 4 h4Part h4Reps h4Others
def h4Pinv := mkPinv 4 h4Part h4Others
def h4Q : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j =>
    match i.val, j.val with
    | 0, 1 => 3 | 0, 2 => 3 | 0, 3 => 3
    | 1, 0 => 1
    | 2, 0 => 4 | 2, 3 => 4
    | 3, 0 => 4 | 3, 2 => 4
    | _, _ => 0
def h4M := h4Pinv * adjZ h4AdjB * h4P
def h4R : Matrix (Fin 8) (Fin 4) ℤ :=
  Matrix.of fun i j => h4M (Fin.natAdd 4 i) (Fin.castAdd 8 j)

lemma h4_PP : h4P * h4Pinv = 1 := by
  ext i j; simp only [Matrix.mul_apply, Matrix.one_apply]; revert i j; decide

lemma h4_M_11 : ∀ i j : Fin 4, h4M (Fin.castAdd 8 i) (Fin.castAdd 8 j) = h4Q i j := by
  intro i j; simp only [h4M, h4Q, Matrix.mul_apply, Matrix.of_apply]; revert i j; decide
lemma h4_M_12 : ∀ (i : Fin 4) (j : Fin 8), h4M (Fin.castAdd 8 i) (Fin.natAdd 4 j) = 0 := by
  intro i j; simp only [h4M, Matrix.mul_apply]; revert i j; decide
lemma h4_M_22 : ∀ i j : Fin 8, h4M (Fin.natAdd 4 i) (Fin.natAdd 4 j) = 0 := by
  intro i j; simp only [h4M, Matrix.mul_apply]; revert i j; decide

lemma h4_M_reindex :
    h4M.reindex (finSumFinEquiv (m := 4) (n := 8)).symm (finSumFinEquiv (m := 4) (n := 8)).symm =
    Matrix.fromBlocks h4Q 0 h4R 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
  · exact h4_M_11 i j
  · exact h4_M_12 i j
  · rfl
  · exact h4_M_22 i j

lemma h4Q_charpoly : h4Q.charpoly = (X + C 4) * (X ^ 3 - C 4 * X ^ 2 - C 27 * X + C 12) := by
  unfold Matrix.charpoly
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_four, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove,
    Matrix.charmatrix, Matrix.scalar_apply, h4Q]
  ring

lemma H4_charpoly [DecidableRel H4.Adj] :
    (H4.adjMatrix ℝ).charpoly =
      X ^ 8 * (X + C 4) * (X ^ 3 - C 4 * X ^ 2 - C 27 * X + C 12) := by
  have hadj : H4.adjMatrix ℝ = (adjZ h4AdjB).map (Int.castRingHom ℝ) := by
    refine adjMatrix_eq_map_adjZ h4AdjB (fun i j => Iff.rfl)
  rw [hadj, charpoly_map_int]
  have h1 : (adjZ h4AdjB).charpoly = h4M.charpoly :=
    charpoly_eq_of_conj (adjZ h4AdjB) h4P h4Pinv h4M h4_PP rfl
  have h2 : h4M.charpoly = (Matrix.fromBlocks h4Q 0 h4R 0).charpoly := by
    rw [← h4_M_reindex, Matrix.charpoly_reindex]
  rw [h1, h2, charpoly_fromBlocks_zero_right, h4Q_charpoly]
  simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C]
  simp only [map_ofNat]
  ring

/-! ### 4. Monic cubic factorization and IVT root bounds -/

lemma monic_cubic_eq_prod {b c d r₁ r₂ r₃ : ℝ}
    (h12 : r₁ < r₂) (h23 : r₂ < r₃)
    (hr1 : r₁ ^ 3 + b * r₁ ^ 2 + c * r₁ + d = 0)
    (hr2 : r₂ ^ 3 + b * r₂ ^ 2 + c * r₂ + d = 0)
    (hr3 : r₃ ^ 3 + b * r₃ ^ 2 + c * r₃ + d = 0) :
    X ^ 3 + C b * X ^ 2 + C c * X + C d = (X - C r₁) * (X - C r₂) * (X - C r₃) := by
  set A := b + (r₁ + r₂ + r₃)
  set B := c - (r₁ * r₂ + r₁ * r₃ + r₂ * r₃)
  set E := d + r₁ * r₂ * r₃
  have hA1 : A * r₁ ^ 2 + B * r₁ + E = 0 := by dsimp [A, B, E]; linarith
  have hA2 : A * r₂ ^ 2 + B * r₂ + E = 0 := by dsimp [A, B, E]; linarith
  have hA3 : A * r₃ ^ 2 + B * r₃ + E = 0 := by dsimp [A, B, E]; linarith
  have h12' : A * (r₁ + r₂) + B = 0 := by
    have hmul : (r₂ - r₁) * (A * (r₁ + r₂) + B) = 0 := by nlinarith
    rcases mul_eq_zero.mp hmul with h | h
    · linarith
    · exact h
  have h23' : A * (r₂ + r₃) + B = 0 := by
    have hmul : (r₃ - r₂) * (A * (r₂ + r₃) + B) = 0 := by nlinarith
    rcases mul_eq_zero.mp hmul with h | h
    · linarith
    · exact h
  have hA0 : A = 0 := by nlinarith
  have hB0 : B = 0 := by nlinarith
  have hE0 : E = 0 := by nlinarith
  have hb : b = -(r₁ + r₂ + r₃) := by dsimp [A] at hA0; linarith
  have hc : c = r₁ * r₂ + r₁ * r₃ + r₂ * r₃ := by dsimp [B] at hB0; linarith
  have hd : d = -(r₁ * r₂ * r₃) := by dsimp [E] at hE0; linarith
  rw [hb, hc, hd]
  simp only [map_neg, map_add, map_mul]
  ring

lemma ivt_root_asc {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (ha : f a < 0) (hb : 0 < f b) : ∃ r, a ≤ r ∧ r ≤ b ∧ f r = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (f a) (f b) := ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc hab hf.continuousOn hmem
  exact ⟨r, hr.1, hr.2, hfr⟩

lemma ivt_root_desc {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b)
    (ha : 0 < f a) (hb : f b < 0) : ∃ r, a ≤ r ∧ r ≤ b ∧ f r = 0 := by
  have hmem : (0 : ℝ) ∈ Set.Icc (f b) (f a) := ⟨le_of_lt hb, le_of_lt ha⟩
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc' hab hf.continuousOn hmem
  exact ⟨r, hr.1, hr.2, hfr⟩

/-- Helper to check monotonicity of a 12-tuple from adjacent inequalities. -/
lemma monotone_fin12 (f : Fin 12 → ℝ)
    (h0 : f 0 ≤ f 1) (h1 : f 1 ≤ f 2) (h2 : f 2 ≤ f 3) (h3 : f 3 ≤ f 4)
    (h4 : f 4 ≤ f 5) (h5 : f 5 ≤ f 6) (h6 : f 6 ≤ f 7) (h7 : f 7 ≤ f 8)
    (h8 : f 8 ≤ f 9) (h9 : f 9 ≤ f 10) (h10 : f 10 ≤ f 11) : Monotone f := by
  have hstep : ∀ k : ℕ, ∀ (hk : k + 1 < 12), f ⟨k, by omega⟩ ≤ f ⟨k + 1, hk⟩ := by
    intro k hk
    match k with
    | 0 => exact h0
    | 1 => exact h1
    | 2 => exact h2
    | 3 => exact h3
    | 4 => exact h4
    | 5 => exact h5
    | 6 => exact h6
    | 7 => exact h7
    | 8 => exact h8
    | 9 => exact h9
    | 10 => exact h10
  intro i j hij
  have hle : i.val ≤ j.val := hij
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  induction d generalizing j with
  | zero =>
    have hij' : i = j := Fin.ext (by omega)
    subst hij'; exact le_refl _
  | succ d ih =>
    have hlt : i.val + d < 12 := by omega
    have hprev : f i ≤ f ⟨i.val + d, hlt⟩ :=
      ih (j := ⟨i.val + d, hlt⟩) (Nat.le_add_right _ _) (Nat.le_add_right _ _) rfl
    have hnxt : f ⟨i.val + d, hlt⟩ ≤ f ⟨i.val + d + 1, by omega⟩ := hstep (i.val + d) (by omega)
    have hj : (⟨i.val + d + 1, by omega⟩ : Fin 12) = j := by
      apply Fin.ext; dsimp; omega
    rw [hj] at hnxt
    exact le_trans hprev hnxt

lemma prod_fin12 (f : Fin 12 → Polynomial ℝ) :
    ∏ i : Fin 12, f i =
      f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 * f 8 * f 9 * f 10 * f 11 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change f 0 * (f 1 * (f 2 * (f 3 * (f 4 * (f 5 * (f 6 * (f 7 * (f 8 * (f 9 * (f 10 * f 11)))))))))) = _
  ring

lemma sum_fin12 (f : Fin 12 → ℝ) :
    ∑ i : Fin 12, f i =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + f 11)))))))))) = _
  ring

end OMA.P_arxiv_2610_18636

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2610_18636.main) := by
  intro h
  open OMA.P_arxiv_2610_18636 Polynomial in
  -- 1. Ordered spectrum of K_{4,4,4}
  let lam0 : Fin 12 → ℝ := ![-4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8]
  have hspec0 : OMA.S_arxiv_2610_18636.IsOrderedSpectrum
      (OMA.S_arxiv_2610_18636.completeTripartite3 4 4 4) lam0 := by
    unfold OMA.S_arxiv_2610_18636.IsOrderedSpectrum
    classical
    refine ⟨?_, ?_⟩
    · refine monotone_fin12 lam0 (by simp [lam0]) (by simp [lam0]) (by simp [lam0])
        (by simp [lam0]) (by simp [lam0]) (by simp [lam0]) (by simp [lam0])
        (by simp [lam0]) (by simp [lam0]) (by simp [lam0]) (by simp [lam0])
    · rw [K0_charpoly, prod_fin12]
      change X ^ 9 * (X - C 8) * (X + C 4) ^ 2 =
        (X - C (-4)) * (X - C (-4)) * (X - C 0) * (X - C 0) * (X - C 0) * (X - C 0) *
        (X - C 0) * (X - C 0) * (X - C 0) * (X - C 0) * (X - C 0) * (X - C 8)
      simp only [map_zero, sub_zero, map_neg]
      ring
  -- 2. Ordered spectrum of K_{3,4,5}: roots of x^3 - 47x - 120
  have hp1c : Continuous (fun x : ℝ => x ^ 3 - 47 * x - 120) := by fun_prop
  obtain ⟨r1, hr1lo, hr1hi, hr1⟩ := ivt_root_asc hp1c (a := -453 / 100) (b := -452 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨r2, hr2lo, hr2hi, hr2⟩ := ivt_root_desc hp1c (a := -337 / 100) (b := -336 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨r3, hr3lo, hr3hi, hr3⟩ := ivt_root_asc hp1c (a := 788 / 100) (b := 789 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  have hp1_fac : X ^ 3 - C (47 : ℝ) * X - C 120 = (X - C r1) * (X - C r2) * (X - C r3) := by
    have hfac := monic_cubic_eq_prod (b := (0 : ℝ)) (c := -47) (d := -120)
      (r₁ := r1) (r₂ := r2) (r₃ := r3)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    simp only [map_zero, zero_mul, add_zero, map_neg] at hfac
    simpa [sub_eq_add_neg, neg_mul] using hfac
  let lam1 : Fin 12 → ℝ := ![r1, r2, 0, 0, 0, 0, 0, 0, 0, 0, 0, r3]
  have hspec1 : OMA.S_arxiv_2610_18636.IsOrderedSpectrum
      (OMA.S_arxiv_2610_18636.completeTripartite3 4 3 4) lam1 := by
    unfold OMA.S_arxiv_2610_18636.IsOrderedSpectrum
    classical
    refine ⟨?_, ?_⟩
    · refine monotone_fin12 lam1
        (by simp [lam1]; linarith) (by simp [lam1]; linarith) (by simp [lam1])
        (by simp [lam1]) (by simp [lam1]) (by simp [lam1])
        (by simp [lam1]) (by simp [lam1]) (by simp [lam1])
        (by simp [lam1]) (by simp [lam1]; linarith)
    · rw [K1_charpoly, hp1_fac, prod_fin12]
      change X ^ 9 * ((X - C r1) * (X - C r2) * (X - C r3)) =
        (X - C r1) * (X - C r2) * (X - C 0) * (X - C 0) * (X - C 0) * (X - C 0) *
        (X - C 0) * (X - C 0) * (X - C 0) * (X - C 0) * (X - C 0) * (X - C r3)
      simp only [map_zero, sub_zero]
      ring
  -- 3. Ordered spectrum of H_4: -4 and roots of x^3 - 4x^2 - 27x + 12
  have hp2c : Continuous (fun x : ℝ => x ^ 3 - 4 * x ^ 2 - 27 * x + 12) := by fun_prop
  obtain ⟨m1, hm1lo, hm1hi, hm1⟩ := ivt_root_asc hp2c (a := -385 / 100) (b := -384 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨m2, hm2lo, hm2hi, hm2⟩ := ivt_root_desc hp2c (a := 42 / 100) (b := 43 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨m3, hm3lo, hm3hi, hm3⟩ := ivt_root_asc hp2c (a := 742 / 100) (b := 743 / 100)
    (by norm_num) (by norm_num) (by norm_num)
  have hp2_fac :
      X ^ 3 - C (4 : ℝ) * X ^ 2 - C 27 * X + C 12 = (X - C m1) * (X - C m2) * (X - C m3) := by
    have hfac := monic_cubic_eq_prod (b := (-4 : ℝ)) (c := -27) (d := 12)
      (r₁ := m1) (r₂ := m2) (r₃ := m3)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    simp only [map_neg] at hfac
    simpa [sub_eq_add_neg, neg_mul] using hfac
  let lam2 : Fin 12 → ℝ := ![-4, m1, 0, 0, 0, 0, 0, 0, 0, 0, m2, m3]
  have hspec2 : OMA.S_arxiv_2610_18636.IsOrderedSpectrum H4 lam2 := by
    unfold OMA.S_arxiv_2610_18636.IsOrderedSpectrum
    classical
    refine ⟨?_, ?_⟩
    · refine monotone_fin12 lam2
        (by simp [lam2]; linarith) (by simp [lam2]; linarith) (by simp [lam2])
        (by simp [lam2]) (by simp [lam2]) (by simp [lam2])
        (by simp [lam2]) (by simp [lam2]) (by simp [lam2])
        (by simp [lam2]; linarith) (by simp [lam2]; linarith)
    · rw [H4_charpoly, hp2_fac, prod_fin12]
      change X ^ 8 * (X + C 4) * ((X - C m1) * (X - C m2) * (X - C m3)) =
        (X - C (-4)) * (X - C m1) * (X - C 0) * (X - C 0) * (X - C 0) * (X - C 0) *
        (X - C 0) * (X - C 0) * (X - C 0) * (X - C 0) * (X - C m2) * (X - C m3)
      simp only [map_zero, sub_zero, map_neg]
      ring
  -- 4. Instantiate conjecture at n = 4 and refute the l_1 distance inequality
  have hineq := (h 4 (by norm_num) H4 H4_not_iso_K444 lam0 lam1 lam2 hspec0 hspec1 hspec2).1
  rw [sum_fin12, sum_fin12] at hineq
  change |-4 - r1| + |-4 - r2| + |0 - 0| + |0 - 0| + |0 - 0| + |0 - 0| + |0 - 0| + |0 - 0| +
    |0 - 0| + |0 - 0| + |0 - 0| + |8 - r3| ≤
    |-4 - (-4)| + |-4 - m1| + |0 - 0| + |0 - 0| + |0 - 0| + |0 - 0| + |0 - 0| + |0 - 0| +
    |0 - 0| + |0 - 0| + |0 - m2| + |8 - m3| at hineq
  simp only [sub_self, abs_zero, add_zero, zero_add, zero_sub, abs_neg] at hineq
  have ha1 : |-4 - r1| = -4 - r1 := abs_of_nonneg (by linarith)
  have ha2 : |-4 - r2| = r2 + 4 := by
    rw [abs_of_nonpos (by linarith)]; ring
  have ha3 : |8 - r3| = 8 - r3 := abs_of_nonneg (by linarith)
  have hb1 : |-4 - m1| = m1 + 4 := by
    rw [abs_of_nonpos (by linarith)]; ring
  have hb2 : |m2| = m2 := abs_of_nonneg (by linarith)
  have hb3 : |8 - m3| = 8 - m3 := abs_of_nonneg (by linarith)
  rw [ha1, ha2, ha3, hb1, hb2, hb3] at hineq
  linarith
