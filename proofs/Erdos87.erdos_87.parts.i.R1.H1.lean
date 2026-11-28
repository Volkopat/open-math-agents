import OMAReductions.R_Erdos87_erdos_87_parts_i_R1

/-!
# Proof of Erdos87.erdos_87.parts.i.R1.H1

We prove the step bound `R(k) ≤ 2 * (k - 2) * R(k - 1) + 2` for `k ≥ 2`, hence
`R(k) ≤ 2 * k * R(k - 1)`. For any graph `G` containing `K_(k - 1)`, monotonicity gives
`R(G) ≥ R(k - 1)`, and since `2 * k * (1 - ε) ^ k → 0` as `k → ∞` for `0 < ε < 1`, we obtain
`R(G) > (1 - ε) ^ k * R(k)` for all sufficiently large `k`.
-/

namespace NeonProof

open SimpleGraph Filter Finset

/-- A copy of `K_m` in `C.comap f`, where `f` injects into `S`, yields an `m`-clique of `C`
contained in `S`. -/
lemma isNClique_of_isContained_comap {V : Type*} [DecidableEq V] {C : SimpleGraph V}
    {S : Finset V} {m r : ℕ} {f : Fin r → V} (hf : Function.Injective f)
    (hfS : ∀ i, f i ∈ S) (h : completeGraph (Fin m) ⊑ C.comap f) :
    ∃ K ⊆ S, C.IsNClique m K := by
  obtain ⟨g⟩ := h
  refine ⟨Finset.univ.image (fun i => f (g i)), ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    exact hfS (g i)
  · intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨j, -, rfl⟩
    have hij : i ≠ j := fun h => hxy (by rw [h])
    exact g.toHom.map_rel hij
  · rw [Finset.card_image_of_injective _ (show Function.Injective (fun i => f (g i)) from
      hf.comp g.injective), Finset.card_fin]

/-- Any vertex subset of size at least `R(m)` contains an `m`-clique in `C` or in `Cᶜ`. -/
lemma ramsey_subset {V : Type*} [DecidableEq V] (C : SimpleGraph V) (S : Finset V) (m : ℕ)
    (hS : diagonalRamsey m ≤ S.card) :
    (∃ K ⊆ S, C.IsNClique m K) ∨ (∃ K ⊆ S, Cᶜ.IsNClique m K) := by
  let e := S.equivFin
  let f : Fin (diagonalRamsey m) → V := fun i => (e.symm (Fin.castLE hS i)).1
  have hf : Function.Injective f :=
    Subtype.val_injective.comp (e.symm.injective.comp (Fin.castLE_injective hS))
  have hfS : ∀ i, f i ∈ S := fun i => (e.symm (Fin.castLE hS i)).2
  have hmem : ∀ D : SimpleGraph (Fin (diagonalRamsey m)),
      completeGraph (Fin m) ⊑ D ∨ completeGraph (Fin m) ⊑ Dᶜ :=
    Nat.sInf_mem (OMA.R_Erdos87_erdos_87_parts_i_R1.ramsey_nonempty (completeGraph (Fin m)))
  rcases hmem (C.comap f) with h | h
  · exact Or.inl (isNClique_of_isContained_comap hf hfS h)
  · have hcompl : (C.comap f)ᶜ = Cᶜ.comap f := by
      ext i j
      simp [SimpleGraph.compl_adj, hf.ne_iff]
    rw [hcompl] at h
    exact Or.inr (isNClique_of_isContained_comap hf hfS h)

/-- If every vertex in `S` has fewer than `r` non-neighbours in `S`, and `|S| > m * r`, then `S`
contains an `(m + 1)`-clique of `C`. -/
lemma exists_clique_of_nondeg_lt {V : Type*} [DecidableEq V] (C : SimpleGraph V)
    [DecidableRel C.Adj] (r : ℕ) :
    ∀ m : ℕ, ∀ S : Finset V,
      (∀ w ∈ S, ((S.erase w).filter (fun u => ¬ C.Adj w u)).card < r) →
      m * r < S.card →
      ∃ K ⊆ S, C.IsNClique (m + 1) K := by
  intro m
  induction m with
  | zero =>
    intro S _ hcard
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by simpa using hcard)
    exact ⟨{w}, Finset.singleton_subset_iff.mpr hw, SimpleGraph.isNClique_singleton.mpr rfl⟩
  | succ m ih =>
    intro S hdeg hcard
    have hpos : 0 < S.card := Nat.lt_of_le_of_lt (Nat.zero_le _) hcard
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    set S_R := (S.erase w).filter (fun u => C.Adj w u) with hSR
    set S_B := (S.erase w).filter (fun u => ¬ C.Adj w u) with hSB
    have hsplit : S_R.card + S_B.card = S.card - 1 := by
      rw [hSR, hSB, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hw]
    have hB : S_B.card < r := hdeg w hw
    have hRcard : m * r < S_R.card := by
      rw [Nat.add_mul, one_mul] at hcard
      omega
    have hRsub : S_R ⊆ S := fun u hu => Finset.mem_of_mem_erase (Finset.mem_filter.mp hu).1
    have hRdeg : ∀ x ∈ S_R, ((S_R.erase x).filter (fun u => ¬ C.Adj x u)).card < r := by
      intro x hx
      refine lt_of_le_of_lt (Finset.card_le_card ?_) (hdeg x (hRsub hx))
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      have huer := Finset.mem_erase.mp hu'.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨huer.1, hRsub huer.2⟩, hu'.2⟩
    obtain ⟨K, hKR, hK⟩ := ih S_R hRdeg hRcard
    refine ⟨insert w K, Finset.insert_subset_iff.mpr ⟨hw, hKR.trans hRsub⟩, ?_⟩
    exact hK.insert (fun u hu => (Finset.mem_filter.mp (hKR hu)).2)

/-- In a graph `C` with no `k`-clique in `C` or `Cᶜ`, every vertex has at most
`(k - 2) * R(k - 1)` neighbours in `C`. -/
lemma card_neighbors_le {V : Type*} [Fintype V] [DecidableEq V] (C : SimpleGraph V)
    [DecidableRel C.Adj] {k : ℕ} (hk : 2 ≤ k)
    (hC : ¬ completeGraph (Fin k) ⊑ C) (hCc : ¬ completeGraph (Fin k) ⊑ Cᶜ) (v : V) :
    ((Finset.univ.erase v).filter (fun u => C.Adj v u)).card ≤
      (k - 2) * diagonalRamsey (k - 1) := by
  set A := (Finset.univ.erase v).filter (fun u => C.Adj v u) with hAdef
  set r := diagonalRamsey (k - 1) with hrdef
  by_contra hbig
  push Not at hbig
  have hdeg : ∀ w ∈ A, ((A.erase w).filter (fun u => ¬ C.Adj w u)).card < r := by
    intro w _
    set T := (A.erase w).filter (fun u => ¬ C.Adj w u) with hTdef
    by_contra hT
    push Not at hT
    rcases ramsey_subset C T (k - 1) hT with ⟨K, hKT, hK⟩ | ⟨K, hKT, hK⟩
    · have hK' : C.IsNClique (k - 1 + 1) (insert v K) := by
        refine hK.insert (fun u hu => ?_)
        have huA : u ∈ A := Finset.mem_of_mem_erase (Finset.mem_filter.mp (hKT hu)).1
        exact (Finset.mem_filter.mp huA).2
      rw [show k - 1 + 1 = k by omega] at hK'
      exact hC ((not_cliqueFree_iff_top_isContained k).mp (fun hf => hf (insert v K) hK'))
    · have hK' : Cᶜ.IsNClique (k - 1 + 1) (insert w K) := by
        refine hK.insert (fun u hu => ?_)
        have huT := Finset.mem_filter.mp (hKT hu)
        rw [SimpleGraph.compl_adj]
        exact ⟨fun h => (Finset.mem_erase.mp huT.1).1 h.symm, huT.2⟩
      rw [show k - 1 + 1 = k by omega] at hK'
      exact hCc ((not_cliqueFree_iff_top_isContained k).mp (fun hf => hf (insert w K) hK'))
  obtain ⟨K, hKA, hK⟩ := exists_clique_of_nondeg_lt C r (k - 2) A hdeg hbig
  have hK' : C.IsNClique (k - 2 + 1 + 1) (insert v K) :=
    hK.insert (fun u hu => (Finset.mem_filter.mp (hKA hu)).2)
  rw [show k - 2 + 1 + 1 = k by omega] at hK'
  exact hC ((not_cliqueFree_iff_top_isContained k).mp (fun hf => hf (insert v K) hK'))

/-- Step bound on diagonal Ramsey numbers: `R(k) ≤ 2 * (k - 2) * R(k - 1) + 2` for `k ≥ 2`. -/
lemma diagonalRamsey_step_le {k : ℕ} (hk : 2 ≤ k) :
    diagonalRamsey k ≤ 2 * (k - 2) * diagonalRamsey (k - 1) + 2 := by
  change sInf {n : ℕ | ∀ C : SimpleGraph (Fin n),
      completeGraph (Fin k) ⊑ C ∨ completeGraph (Fin k) ⊑ Cᶜ} ≤
    2 * (k - 2) * diagonalRamsey (k - 1) + 2
  apply Nat.sInf_le
  intro C
  classical
  by_contra h
  have hC : ¬ completeGraph (Fin k) ⊑ C := fun hc => h (Or.inl hc)
  have hCc : ¬ completeGraph (Fin k) ⊑ Cᶜ := fun hc => h (Or.inr hc)
  let v : Fin (2 * (k - 2) * diagonalRamsey (k - 1) + 2) := ⟨0, by omega⟩
  have h1 := card_neighbors_le C hk hC hCc v
  have h2 := card_neighbors_le Cᶜ hk hCc (by simpa using hC) v
  have hcompl_eq :
      (Finset.univ.erase v).filter (fun u => Cᶜ.Adj v u) =
        (Finset.univ.erase v).filter (fun u => ¬ C.Adj v u) := by
    refine Finset.filter_congr (fun u hu => ?_)
    have huv : v ≠ u := (Finset.mem_erase.mp hu).1.symm
    simp [SimpleGraph.compl_adj, huv]
  rw [hcompl_eq] at h2
  have hsum :
      ((Finset.univ.erase v).filter (fun u => C.Adj v u)).card +
        ((Finset.univ.erase v).filter (fun u => ¬ C.Adj v u)).card =
      2 * ((k - 2) * diagonalRamsey (k - 1)) + 1 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ, Fintype.card_fin, mul_assoc]
    omega
  omega

/-- Simplified step bound: `R(k) ≤ 2 * k * R(k - 1)` for `k ≥ 2`. -/
lemma diagonalRamsey_le_two_mul_mul {k : ℕ} (hk : 2 ≤ k) :
    diagonalRamsey k ≤ 2 * k * diagonalRamsey (k - 1) := by
  have hstep := diagonalRamsey_step_le hk
  have hr : 1 ≤ diagonalRamsey (k - 1) := by
    have hcard := OMA.R_Erdos87_erdos_87_parts_i_R1.card_le_graphRamsey
      (completeGraph (Fin (k - 1)))
    simp only [Fintype.card_fin] at hcard
    change k - 1 ≤ diagonalRamsey (k - 1) at hcard
    omega
  have hsub : 2 * (k - 2) + 4 = 2 * k := by omega
  have hmul : 2 * (k - 2) * diagonalRamsey (k - 1) + 4 * diagonalRamsey (k - 1) =
      2 * k * diagonalRamsey (k - 1) := by
    rw [← Nat.add_mul, hsub]
  omega

end NeonProof

theorem OMA.solution : OMA.R_Erdos87_erdos_87_parts_i_R1.H1 := by
  intro ε hε hε1
  have habs : |1 - ε| < 1 := by
    rw [abs_of_pos (by linarith)]
    linarith
  have htend := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 habs
  have hev : ∀ᶠ k : ℕ in Filter.atTop, (k : ℝ) ^ 1 * (1 - ε) ^ k < 1 / 2 :=
    htend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hev, Filter.eventually_ge_atTop 2] with k hklt hk2 V _ G _ _ hKk1 _
  have hmono : (SimpleGraph.diagonalRamsey (k - 1) : ℝ) ≤ (SimpleGraph.diagonalGraphRamsey G : ℝ) := by
    exact_mod_cast OMA.R_Erdos87_erdos_87_parts_i_R1.graphRamsey_mono hKk1
  have hstep : (SimpleGraph.diagonalRamsey k : ℝ) ≤
      2 * (k : ℝ) * (SimpleGraph.diagonalRamsey (k - 1) : ℝ) := by
    exact_mod_cast NeonProof.diagonalRamsey_le_two_mul_mul hk2
  have hrpos : (0 : ℝ) < (SimpleGraph.diagonalRamsey (k - 1) : ℝ) := by
    have hcard := OMA.R_Erdos87_erdos_87_parts_i_R1.card_le_graphRamsey
      (SimpleGraph.completeGraph (Fin (k - 1)))
    simp only [Fintype.card_fin] at hcard
    change k - 1 ≤ SimpleGraph.diagonalRamsey (k - 1) at hcard
    have h1 : (1 : ℕ) ≤ SimpleGraph.diagonalRamsey (k - 1) := by omega
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one h1
  have hpowpos : (0 : ℝ) < (1 - ε) ^ k := pow_pos (by linarith) k
  have h2k : 2 * (k : ℝ) * (1 - ε) ^ k < 1 := by
    rw [pow_one] at hklt
    linarith
  show (1 - ε) ^ k * (SimpleGraph.diagonalRamsey k : ℝ) <
    (SimpleGraph.diagonalGraphRamsey G : ℝ)
  calc
    (1 - ε) ^ k * (SimpleGraph.diagonalRamsey k : ℝ)
        ≤ (1 - ε) ^ k * (2 * (k : ℝ) * (SimpleGraph.diagonalRamsey (k - 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep hpowpos.le
    _ = (2 * (k : ℝ) * (1 - ε) ^ k) * (SimpleGraph.diagonalRamsey (k - 1) : ℝ) := by ring
    _ < 1 * (SimpleGraph.diagonalRamsey (k - 1) : ℝ) :=
          mul_lt_mul_of_pos_right h2k hrpos
    _ = (SimpleGraph.diagonalRamsey (k - 1) : ℝ) := one_mul _
    _ ≤ (SimpleGraph.diagonalGraphRamsey G : ℝ) := hmono
