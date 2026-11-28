import OMAStatements.S_arxiv_1807_06436
import Mathlib

/- The four exceptional graphs violate the bound. A unique shortest path of
length d between two vertices forces at least d + 1 distinct eigenvalues for
every matrix of S(G): such a real symmetric matrix is killed by the product of
X - r over its eigenvalues, while the (u, v) entry of its d-th power is nonzero
and all lower powers vanish there. This gives q at least 4 for P4 and its
complement, 5 and 3 for P5 and its complement, and 4 for T22 and its complement.
The remaining direction is split at seven vertices: the source paper checks all
graphs on at most seven vertices, and larger graphs are the open part. -/
namespace OMA.R_arxiv_1807_06436_R1

open OMA.S_arxiv_1807_06436 SimpleGraph Polynomial Matrix

def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), n ≤ 7 →
    ¬ (Nonempty (G ≃g pathGraph 4) ∨ Nonempty (G ≃g pathGraph 5) ∨
      Nonempty (G ≃g (pathGraph 5)ᶜ) ∨ Nonempty (G ≃g T22)) →
    q G + q Gᶜ ≤ n + 2

def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 8 ≤ n → q G + q Gᶜ ≤ n + 2

theorem prod_monic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∏ r ∈ A.charpoly.roots.toFinset, (X - C r)).Monic :=
  monic_prod_of_monic _ _ (fun r _ => monic_X_sub_C r)

theorem prod_natDegree {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∏ r ∈ A.charpoly.roots.toFinset, (X - C r)).natDegree = A.charpoly.roots.toFinset.card := by
  rw [natDegree_prod_of_monic _ _ (fun r _ => monic_X_sub_C r)]
  simp

theorem isHermitian_of_isSymm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    A.IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA

/-- A real symmetric matrix is annihilated by the product of `X - r` over its distinct
eigenvalues. -/
theorem aeval_prod {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    aeval A (∏ r ∈ A.charpoly.roots.toFinset, (X - C r)) = 0 := by
  have hH := isHermitian_of_isSymm hA
  set p := ∏ r ∈ A.charpoly.roots.toFinset, (X - C r) with hp
  have hroot : ∀ i, p.eval (hH.eigenvalues i) = 0 := by
    intro i
    rw [hp, eval_prod]
    apply Finset.prod_eq_zero (i := hH.eigenvalues i)
    · rw [Multiset.mem_toFinset, hH.roots_charpoly_eq_eigenvalues]
      simp
    · simp
  have hD : aeval (diagonal (RCLike.ofReal ∘ hH.eigenvalues) : Matrix (Fin n) (Fin n) ℝ) p
      = 0 := by
    have : (diagonal (RCLike.ofReal ∘ hH.eigenvalues) : Matrix (Fin n) (Fin n) ℝ)
        = diagonalAlgHom ℝ (RCLike.ofReal ∘ hH.eigenvalues) := rfl
    rw [this, aeval_algHom_apply, aeval_pi_apply]
    have h0 : (fun j : Fin n => (aeval ((RCLike.ofReal ∘ hH.eigenvalues) j) p : ℝ)) = 0 := by
      funext j
      simpa [aeval_def, eval₂_eq_eval_map] using hroot j
    rw [h0, map_zero]
  rw [hH.spectral_theorem, aeval_algHom_apply, hD, map_zero]

theorem pow_entry_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (d : ℕ)
    (hk : A.charpoly.roots.toFinset.card ≤ d) (u v : Fin n)
    (hlow : ∀ j < d, (A ^ j) u v = 0) : (A ^ d) u v = 0 := by
  have hm := prod_monic A
  have hroot := aeval_prod A hA
  set p := ∏ r ∈ A.charpoly.roots.toFinset, (X - C r) with hp
  have heq : aeval A ((X : ℝ[X]) ^ d) = aeval A ((X ^ d) %ₘ p) :=
    (aeval_modByMonic_eq_self_of_root hroot).symm
  rw [map_pow, aeval_X] at heq
  rw [heq]
  by_cases h1 : p = 1
  · rw [h1, modByMonic_one, map_zero]
    rfl
  have hdeg : ((X : ℝ[X]) ^ d %ₘ p).natDegree < d := by
    have := natDegree_modByMonic_lt ((X : ℝ[X]) ^ d) hm h1
    have h2 := prod_natDegree A
    rw [← hp] at h2
    omega
  rw [aeval_eq_sum_range' hdeg, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_range] at hj
  rw [Matrix.smul_apply, hlow j hj, smul_zero]

theorem card_roots_ge {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (d : ℕ)
    (u v : Fin n) (hlow : ∀ j < d, (A ^ j) u v = 0) (hd : (A ^ d) u v ≠ 0) :
    d + 1 ≤ A.charpoly.roots.toFinset.card := by
  by_contra h
  exact hd (pow_entry_eq_zero A hA d (by omega) u v hlow)

open Classical in
theorem qset_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) :
    {k | ∃ A ∈ S G, A.charpoly.roots.toFinset.card = k}.Nonempty := by
  refine ⟨_, Matrix.of (fun i j => if G.Adj i j then (1 : ℝ) else 0), ⟨?_, ?_⟩, rfl⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, G.adj_comm]
  · intro i j _
    simp

theorem le_q {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ)
    (h : ∀ A ∈ S G, m ≤ A.charpoly.roots.toFinset.card) : m ≤ q G := by
  unfold q
  apply le_csInf (qset_nonempty G)
  rintro k ⟨A, hA, rfl⟩
  exact h A hA

theorem q_le {n : ℕ} (G : SimpleGraph (Fin n)) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ S G) :
    q G ≤ A.charpoly.roots.toFinset.card :=
  Nat.sInf_le ⟨A, hA, rfl⟩

theorem q_spec {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ A ∈ S G, A.charpoly.roots.toFinset.card = q G :=
  Nat.sInf_mem (qset_nonempty G)

theorem reindex_mem {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ≃g H) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ S G) :
    Matrix.reindex e.toEquiv e.toEquiv A ∈ S H := by
  obtain ⟨hs, hadj⟩ := hA
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact congrFun (congrFun hs _) _
  · intro i j hij
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    have hne : e.toEquiv.symm i ≠ e.toEquiv.symm j := fun h => hij (e.toEquiv.symm.injective h)
    rw [hadj _ _ hne]
    exact e.symm.map_adj_iff

theorem q_le_of_iso {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ≃g H) : q H ≤ q G := by
  obtain ⟨A, hA, hk⟩ := q_spec G
  rw [← hk]
  have := q_le H _ (reindex_mem e A hA)
  rwa [Matrix.charpoly_reindex] at this

theorem q_iso {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ≃g H) : q G = q H :=
  le_antisymm (q_le_of_iso e.symm) (q_le_of_iso e)

theorem q_ge_of_entry {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) (u v : Fin n)
    (h : ∀ A ∈ S G, (∀ j < d, (A ^ j) u v = 0) ∧ (A ^ d) u v ≠ 0) : d + 1 ≤ q G :=
  le_q G _ (fun A hA => card_roots_ge A hA.1 d u v (h A hA).1 (h A hA).2)

theorem iso_compl {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ≃g H) : Nonempty (Gᶜ ≃g Hᶜ) :=
  ⟨⟨e.toEquiv, by intro a b; simp [compl_adj, e.map_adj_iff]⟩⟩

theorem card_iso {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (e : G ≃g H) : n = m := by
  simpa using Fintype.card_congr e.toEquiv

theorem q_P4 : 4 ≤ q (pathGraph 4) := by
  apply q_ge_of_entry _ 3 0 3
  intro A hA
  have hz : ∀ i j, i ≠ j → ¬ (pathGraph 4).Adj i j → A i j = 0 :=
    fun i j hij h => by_contra (fun hne => h ((hA.2 i j hij).1 hne))
  have hn : ∀ i j, i ≠ j → (pathGraph 4).Adj i j → A i j ≠ 0 :=
    fun i j hij h => (hA.2 i j hij).2 h
  have z02 := hz 0 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z03 := hz 0 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z13 := hz 1 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z20 := hz 2 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z30 := hz 3 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z31 := hz 3 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n01 := hn 0 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n12 := hn 1 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n23 := hn 2 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have e2 : A ^ 2 = A * A := sq A
  have e3 : A ^ 3 = A * A * A := by rw [pow_succ, sq]
  have e4 : A ^ 4 = A * A * A * A := by rw [pow_succ, e3]
  refine ⟨?_, ?_⟩
  · intro j hj
    interval_cases j <;> simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four, z02, z03, z13, z20, z30, z31]
  · have hp : (A ^ 3) 0 3 = A 0 1 * A 1 2 * A 2 3 := by
      simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four, z02, z03, z13, z20, z30, z31]
      try ring
    rw [hp]
    simp [n01, n12, n23]

theorem q_P4c : 4 ≤ q (pathGraph 4)ᶜ := by
  apply q_ge_of_entry _ 3 2 1
  intro A hA
  have hz : ∀ i j, i ≠ j → ¬ ((pathGraph 4)ᶜ).Adj i j → A i j = 0 :=
    fun i j hij h => by_contra (fun hne => h ((hA.2 i j hij).1 hne))
  have hn : ∀ i j, i ≠ j → ((pathGraph 4)ᶜ).Adj i j → A i j ≠ 0 :=
    fun i j hij h => (hA.2 i j hij).2 h
  have z01 := hz 0 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z10 := hz 1 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z12 := hz 1 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z21 := hz 2 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z23 := hz 2 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z32 := hz 3 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n20 := hn 2 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n03 := hn 0 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n31 := hn 3 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have e2 : A ^ 2 = A * A := sq A
  have e3 : A ^ 3 = A * A * A := by rw [pow_succ, sq]
  have e4 : A ^ 4 = A * A * A * A := by rw [pow_succ, e3]
  refine ⟨?_, ?_⟩
  · intro j hj
    interval_cases j <;> simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four, z01, z10, z12, z21, z23, z32]
  · have hp : (A ^ 3) 2 1 = A 2 0 * A 0 3 * A 3 1 := by
      simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_four, z01, z10, z12, z21, z23, z32]
      try ring
    rw [hp]
    simp [n20, n03, n31]

theorem q_P5 : 5 ≤ q (pathGraph 5) := by
  apply q_ge_of_entry _ 4 0 4
  intro A hA
  have hz : ∀ i j, i ≠ j → ¬ (pathGraph 5).Adj i j → A i j = 0 :=
    fun i j hij h => by_contra (fun hne => h ((hA.2 i j hij).1 hne))
  have hn : ∀ i j, i ≠ j → (pathGraph 5).Adj i j → A i j ≠ 0 :=
    fun i j hij h => (hA.2 i j hij).2 h
  have z02 := hz 0 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z03 := hz 0 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z04 := hz 0 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z13 := hz 1 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z14 := hz 1 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z20 := hz 2 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z24 := hz 2 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z30 := hz 3 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z31 := hz 3 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z40 := hz 4 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z41 := hz 4 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z42 := hz 4 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n01 := hn 0 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n12 := hn 1 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n23 := hn 2 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n34 := hn 3 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have e2 : A ^ 2 = A * A := sq A
  have e3 : A ^ 3 = A * A * A := by rw [pow_succ, sq]
  have e4 : A ^ 4 = A * A * A * A := by rw [pow_succ, e3]
  refine ⟨?_, ?_⟩
  · intro j hj
    interval_cases j <;> simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_five, z02, z03, z04, z13, z14, z20, z24, z30, z31, z40, z41, z42]
  · have hp : (A ^ 4) 0 4 = A 0 1 * A 1 2 * A 2 3 * A 3 4 := by
      simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_five, z02, z03, z04, z13, z14, z20, z24, z30, z31, z40, z41, z42]
      try ring
    rw [hp]
    simp [n01, n12, n23, n34]

theorem q_P5c : 3 ≤ q (pathGraph 5)ᶜ := by
  apply q_ge_of_entry _ 2 1 2
  intro A hA
  have hz : ∀ i j, i ≠ j → ¬ ((pathGraph 5)ᶜ).Adj i j → A i j = 0 :=
    fun i j hij h => by_contra (fun hne => h ((hA.2 i j hij).1 hne))
  have hn : ∀ i j, i ≠ j → ((pathGraph 5)ᶜ).Adj i j → A i j ≠ 0 :=
    fun i j hij h => (hA.2 i j hij).2 h
  have z01 := hz 0 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z10 := hz 1 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z12 := hz 1 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z21 := hz 2 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z23 := hz 2 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z32 := hz 3 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z34 := hz 3 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z43 := hz 4 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n14 := hn 1 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n42 := hn 4 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have e2 : A ^ 2 = A * A := sq A
  have e3 : A ^ 3 = A * A * A := by rw [pow_succ, sq]
  have e4 : A ^ 4 = A * A * A * A := by rw [pow_succ, e3]
  refine ⟨?_, ?_⟩
  · intro j hj
    interval_cases j <;> simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_five, z01, z10, z12, z21, z23, z32, z34, z43]
  · have hp : (A ^ 2) 1 2 = A 1 4 * A 4 2 := by
      simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_five, z01, z10, z12, z21, z23, z32, z34, z43]
      try ring
    rw [hp]
    simp [n14, n42]

theorem q_T22 : 4 ≤ q T22 := by
  apply q_ge_of_entry _ 3 0 4
  intro A hA
  have hz : ∀ i j, i ≠ j → ¬ (T22).Adj i j → A i j = 0 :=
    fun i j hij h => by_contra (fun hne => h ((hA.2 i j hij).1 hne))
  have hn : ∀ i j, i ≠ j → (T22).Adj i j → A i j ≠ 0 :=
    fun i j hij h => (hA.2 i j hij).2 h
  have z02 := hz 0 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z03 := hz 0 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z04 := hz 0 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z14 := hz 1 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z20 := hz 2 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z24 := hz 2 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z30 := hz 3 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z40 := hz 4 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z41 := hz 4 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z42 := hz 4 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n01 := hn 0 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n13 := hn 1 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n34 := hn 3 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have e2 : A ^ 2 = A * A := sq A
  have e3 : A ^ 3 = A * A * A := by rw [pow_succ, sq]
  have e4 : A ^ 4 = A * A * A * A := by rw [pow_succ, e3]
  refine ⟨?_, ?_⟩
  · intro j hj
    interval_cases j <;> simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_five, z02, z03, z04, z14, z20, z24, z30, z40, z41, z42]
  · have hp : (A ^ 3) 0 4 = A 0 1 * A 1 3 * A 3 4 := by
      simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_five, z02, z03, z04, z14, z20, z24, z30, z40, z41, z42]
      try ring
    rw [hp]
    simp [n01, n13, n34]

theorem q_T22c : 4 ≤ q T22ᶜ := by
  apply q_ge_of_entry _ 3 1 3
  intro A hA
  have hz : ∀ i j, i ≠ j → ¬ (T22ᶜ).Adj i j → A i j = 0 :=
    fun i j hij h => by_contra (fun hne => h ((hA.2 i j hij).1 hne))
  have hn : ∀ i j, i ≠ j → (T22ᶜ).Adj i j → A i j ≠ 0 :=
    fun i j hij h => (hA.2 i j hij).2 h
  have z01 := hz 0 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z10 := hz 1 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z12 := hz 1 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z13 := hz 1 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z21 := hz 2 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z23 := hz 2 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z31 := hz 3 1 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z32 := hz 3 2 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z34 := hz 3 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have z43 := hz 4 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n14 := hn 1 4 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n40 := hn 4 0 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have n03 := hn 0 3 (by decide) (by simp only [T22, compl_adj, pathGraph_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj]; decide)
  have e2 : A ^ 2 = A * A := sq A
  have e3 : A ^ 3 = A * A * A := by rw [pow_succ, sq]
  have e4 : A ^ 4 = A * A * A * A := by rw [pow_succ, e3]
  refine ⟨?_, ?_⟩
  · intro j hj
    interval_cases j <;> simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_five, z01, z10, z12, z13, z21, z23, z31, z32, z34, z43]
  · have hp : (A ^ 3) 1 3 = A 1 4 * A 4 0 * A 0 3 := by
      simp [e2, e3, e4, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_five, z01, z10, z12, z13, z21, z23, z31, z32, z34, z43]
      try ring
    rw [hp]
    simp [n14, n40, n03]

theorem bad {n m : ℕ} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)} (e : Nonempty (G ≃g H))
    (h : m + 2 < q H + q Hᶜ) : ¬ q G + q Gᶜ ≤ n + 2 := by
  obtain ⟨e⟩ := e
  obtain ⟨ec⟩ := iso_compl e
  rw [q_iso e, q_iso ec, card_iso e]
  omega

theorem viol_P4 : 4 + 2 < q (pathGraph 4) + q (pathGraph 4)ᶜ := by
  have := q_P4; have := q_P4c; omega

theorem viol_P5 : 5 + 2 < q (pathGraph 5) + q (pathGraph 5)ᶜ := by
  have := q_P5; have := q_P5c; omega

theorem viol_P5c : 5 + 2 < q (pathGraph 5)ᶜ + q (pathGraph 5)ᶜᶜ := by
  rw [compl_compl]; have := q_P5; have := q_P5c; omega

theorem viol_T22 : 5 + 2 < q T22 + q T22ᶜ := by
  have := q_T22; have := q_T22c; omega

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1807_06436.main := by
  intro h1 h2 n G
  constructor
  · intro hle hex
    rcases hex with e | e | e | e
    · exact bad e viol_P4 hle
    · exact bad e viol_P5 hle
    · exact bad e viol_P5c hle
    · exact bad e viol_T22 hle
  · intro hne
    by_cases hn : n ≤ 7
    · exact h1 n G hn hne
    · exact h2 n G (by omega)

end OMA.R_arxiv_1807_06436_R1
