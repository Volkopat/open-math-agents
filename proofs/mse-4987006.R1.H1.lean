import OMAReductions.R_mse_4987006_R1

/-!
Step `mse-4987006.R1.H1`: cages of girth at most `3` are Hamiltonian.

* Girth `g ≤ 2` is impossible (`SimpleGraph.three_le_egirth`).
* In the complete graph on `Fin n`, the walk `0 → k → k-1 → ⋯ → 1 → 0` is a cycle of length
  `k + 1` for `2 ≤ k < n`: with `k = 2` the girth of `K_n` is `3`, with `k = n - 1` it is a
  Hamiltonian cycle.
* An `(r, 3)`-cage on `n` vertices has `n ≥ r + 1` (a degree is below the number of vertices)
  and `n ≤ r + 1` (minimality, as `K_(r+1)` is `r`-regular of girth `3`); an `r`-regular graph
  on `r + 1` vertices is complete, hence Hamiltonian.
-/

namespace OMA.R_mse_4987006_R1.Step1

open SimpleGraph OMA.S_mse_4987006

section
variable {n : ℕ}

def pathDown : (k : ℕ) → (hk : k < n) → (⊤ : SimpleGraph (Fin n)).Walk ⟨k, hk⟩ ⟨0, by omega⟩
  | 0, _ => Walk.nil
  | k + 1, hk => Walk.cons (by simp [Fin.ext_iff] : (⊤ : SimpleGraph (Fin n)).Adj ⟨k + 1, hk⟩
      ⟨k, by omega⟩) (pathDown k (by omega))

theorem pathDown_length : ∀ (k : ℕ) (hk : k < n), (pathDown k hk).length = k
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [pathDown, Walk.length_cons, pathDown_length k (by omega)]

theorem pathDown_support : ∀ (k : ℕ) (hk : k < n), ∀ v ∈ (pathDown k hk).support, v.val ≤ k
  | 0, _ => by
    intro v hv
    simp [pathDown] at hv
    subst hv; simp
  | k + 1, hk => by
    intro v hv
    simp only [pathDown, Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp
    · have := pathDown_support k (by omega) v hv
      omega

theorem pathDown_isPath : ∀ (k : ℕ) (hk : k < n), (pathDown k hk).IsPath
  | 0, _ => Walk.IsPath.nil
  | k + 1, hk => by
    simp only [pathDown]
    rw [Walk.cons_isPath_iff]
    refine ⟨pathDown_isPath k (by omega), ?_⟩
    intro hmem
    have := pathDown_support k (by omega) _ hmem
    simp at this

theorem pathDown_edges : ∀ (k : ℕ) (hk : k < n), ∀ e ∈ (pathDown k hk).edges,
    ∀ a b : Fin n, e = s(a, b) → a.val = b.val + 1 ∨ b.val = a.val + 1
  | 0, _ => by simp [pathDown]
  | k + 1, hk => by
    intro e he a b hab
    simp only [pathDown, Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · rw [Sym2.eq_iff] at hab
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [← h1, ← h2]
      · right; rw [← h1, ← h2]
    · exact pathDown_edges k (by omega) e he a b hab

def cyc (k : ℕ) (h2 : 2 ≤ k) (hk : k < n) : (⊤ : SimpleGraph (Fin n)).Walk ⟨0, by omega⟩ ⟨0, by omega⟩ :=
  Walk.cons (by simp [Fin.ext_iff]; omega : (⊤ : SimpleGraph (Fin n)).Adj ⟨0, by omega⟩ ⟨k, hk⟩)
    (pathDown k hk)

theorem cyc_isCycle (k : ℕ) (h2 : 2 ≤ k) (hk : k < n) : (cyc k h2 hk).IsCycle := by
  unfold cyc
  rw [Walk.cons_isCycle_iff]
  refine ⟨pathDown_isPath k hk, ?_⟩
  intro hmem
  have := pathDown_edges k hk _ hmem _ _ rfl
  simp at this
  omega

theorem cyc_length (k : ℕ) (h2 : 2 ≤ k) (hk : k < n) : (cyc k h2 hk).length = k + 1 := by
  simp [cyc, pathDown_length]

theorem top_hamiltonian (hn : 3 ≤ n) : (⊤ : SimpleGraph (Fin n)).IsHamiltonian := by
  intro _
  refine ⟨_, cyc (n - 1) (by omega) (by omega), ?_⟩
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨cyc_isCycle _ _ _, ?_⟩
  rw [cyc_length, Fintype.card_fin]
  omega

theorem top_egirth (hn : 3 ≤ n) : (⊤ : SimpleGraph (Fin n)).egirth = 3 := by
  apply le_antisymm _ three_le_egirth
  have := egirth_le_length (cyc_isCycle 2 le_rfl (by omega : 2 < n))
  rw [cyc_length] at this
  exact_mod_cast this

end

theorem cage3 (r n : ℕ) (hr : 3 ≤ r) (G : SimpleGraph (Fin n)) (hG : IsCage r 3 n G) :
    G.IsHamiltonian := by
  classical
  obtain ⟨hreg, hgirth, hmin⟩ := hG
  have hn0 : 0 < n := by
    by_contra h0
    have h0 : n = 0 := by omega
    subst h0
    have : G.egirth = ⊤ := egirth_eq_top.2 (fun v => v.elim0)
    rw [this] at hgirth
    exact ENat.top_ne_coe 3 hgirth
  have hle : n ≤ r + 1 := by
    by_contra h
    apply hmin (r + 1) (by omega) ⊤
    refine ⟨?_, top_egirth (by omega)⟩
    have := (IsRegularOfDegree.top : (⊤ : SimpleGraph (Fin (r + 1))).IsRegularOfDegree _)
    rw [Fintype.card_fin, Nat.add_sub_cancel] at this
    convert this
  have hge : r + 1 ≤ n := by
    have h1 := G.degree_lt_card_verts ⟨0, hn0⟩
    have h2 := hreg ⟨0, hn0⟩
    rw [Fintype.card_fin] at h1
    have : G.degree ⟨0, hn0⟩ = r := by convert h2
    omega
  have hG : G = ⊤ := by
    ext u v
    constructor
    · intro h; exact G.ne_of_adj h
    · intro huv
      have hsub : G.neighborFinset u ⊆ Finset.univ.erase u := by
        intro w hw
        rw [mem_neighborFinset] at hw
        exact Finset.mem_erase.2 ⟨(G.ne_of_adj hw).symm, Finset.mem_univ _⟩
      have hcard : (Finset.univ.erase u).card ≤ (G.neighborFinset u).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
          card_neighborFinset_eq_degree]
        have : G.degree u = r := by convert hreg u
        omega
      have heq := Finset.eq_of_subset_of_card_le hsub hcard
      have : v ∈ Finset.univ.erase u := Finset.mem_erase.2 ⟨Ne.symm huv, Finset.mem_univ _⟩
      rw [← heq, mem_neighborFinset] at this
      exact this
  rw [hG]
  exact top_hamiltonian (by omega)

theorem cage_le3 (r g n : ℕ) (hr : 3 ≤ r) (hg : g ≤ 3) (G : SimpleGraph (Fin n))
    (hG : IsCage r g n G) : G.IsHamiltonian := by
  have h3 : 3 ≤ g := by
    have := three_le_egirth (G := G)
    rw [hG.2.1] at this
    exact_mod_cast this
  obtain rfl : g = 3 := by omega
  exact cage3 r n hr G hG

end OMA.R_mse_4987006_R1.Step1

theorem OMA.solution : OMA.R_mse_4987006_R1.H1 :=
  OMA.R_mse_4987006_R1.Step1.cage_le3
