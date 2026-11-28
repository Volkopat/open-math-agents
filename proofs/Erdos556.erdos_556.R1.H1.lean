import OMAReductions.R_Erdos556_erdos_556_R1

/-!
# Proof of `Erdos556.erdos_556.R1.H1`

Every 3-colouring of the edges of `K_13` contains a monochromatic `C_4`.
By pigeonhole some colour class `G` has sum of degrees at least `52`. If `G` is `C_4`-free,
every pair of distinct vertices has at most one common neighbour, so double-counting cherries
gives `∑ d(v)(d(v) - 1) ≤ 156`. Together with `∑ (d(v) - 4)^2 ≥ 0`, this forces `G` to be
`4`-regular with every pair of distinct vertices sharing a unique common neighbour.
Then `G` has `13 * 4 = 52` ordered triangles, which must be divisible by `3`, a contradiction.
-/

-- Step Erdos556.erdos_556.R1.H1: hypothesis H1 of reduction Erdos556.erdos_556.R1
-- Credit: @lettucrisp
-- H1 := ∀ c : Fin 3 → SimpleGraph (Fin 13),     (⊤ : SimpleGraph (Fin 13)).IsEdgeColouring c → ∃ i, cycleGraph 4 ⊑ c i

namespace Erdos556H1

open SimpleGraph
open scoped SimpleGraph

private lemma four_cycle_of_two_common {V : Type*} {G : SimpleGraph V}
    {u v x y : V} (huv : u ≠ v) (hxy : x ≠ y)
    (hux : G.Adj u x) (hvx : G.Adj v x) (huy : G.Adj u y) (hvy : G.Adj v y) :
    cycleGraph 4 ⊑ G := by
  let f : Fin 4 → V := ![u, x, v, y]
  have hux_ne : u ≠ x := G.ne_of_adj hux
  have huy_ne : u ≠ y := G.ne_of_adj huy
  have hvx_ne : v ≠ x := G.ne_of_adj hvx
  have hvy_ne : v ≠ y := G.ne_of_adj hvy
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
    | exact False.elim ((show ¬ (cycleGraph 4).Adj _ _ from by decide) hij)
    | simpa [f, adj_comm] using hux
    | simpa [f, adj_comm] using hvx
    | simpa [f, adj_comm] using huy
    | simpa [f, adj_comm] using hvy
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]

private lemma common_card_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ cycleGraph 4 ⊑ G) {u v : V} (huv : u ≠ v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  by_contra hxy
  rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hx hy
  exact hfree (four_cycle_of_two_common huv hxy hx.1 hx.2 hy.1 hy.2)

private lemma sum_deg_mul_pred_eq {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ w : V, G.degree w * (G.degree w - 1) =
      ∑ u : V, ∑ v ∈ Finset.univ.erase u, (G.neighborFinset u ∩ G.neighborFinset v).card := by
  have h1 : ∀ w : V, G.degree w * (G.degree w - 1) =
      ∑ u : V, ∑ v ∈ Finset.univ.erase u, if G.Adj w u ∧ G.Adj w v then 1 else 0 := by
    intro w
    have hcard : G.degree w * (G.degree w - 1) =
        ∑ u ∈ G.neighborFinset w, ((G.neighborFinset w).erase u).card := by
      rw [← card_neighborFinset_eq_degree]
      have : ∑ u ∈ G.neighborFinset w, ((G.neighborFinset w).erase u).card =
          ∑ _u ∈ G.neighborFinset w, ((G.neighborFinset w).card - 1) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        exact Finset.card_erase_of_mem hu
      rw [this, Finset.sum_const, smul_eq_mul]
    rw [hcard]
    trans ∑ u : V, if G.Adj w u then ((G.neighborFinset w).erase u).card else 0
    · rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext u
      simp [mem_neighborFinset]
    · refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hwu : G.Adj w u
      · rw [if_pos hwu]
        rw [Finset.card_eq_sum_ones]
        trans ∑ v ∈ Finset.univ.erase u, if G.Adj w v then 1 else 0
        · rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext v
          simp [mem_neighborFinset, and_comm]
        · refine Finset.sum_congr rfl fun v _ => by simp [hwu]
      · rw [if_neg hwu]
        symm
        exact Finset.sum_eq_zero fun v _ => by simp [hwu]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext w
  simp [mem_neighborFinset, G.adj_comm]

private lemma ordered_triangles_dvd_three {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    3 ∣ ∑ u : V, ∑ v : V, ∑ w : V,
      if G.Adj u v ∧ G.Adj v w ∧ G.Adj w u then 1 else 0 := by
  let T1 : ℕ := ∑ u : V, ∑ v : V, ∑ w : V,
      if u < v ∧ u < w ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u then 1 else 0
  let T2 : ℕ := ∑ u : V, ∑ v : V, ∑ w : V,
      if v < u ∧ v < w ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u then 1 else 0
  let T3 : ℕ := ∑ u : V, ∑ v : V, ∑ w : V,
      if w < u ∧ w < v ∧ G.Adj u v ∧ G.Adj v w ∧ G.Adj w u then 1 else 0
  have hT_split :
      (∑ u : V, ∑ v : V, ∑ w : V, if G.Adj u v ∧ G.Adj v w ∧ G.Adj w u then 1 else 0) =
        T1 + T2 + T3 := by
    simp only [T1, T2, T3, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ =>
      Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun w _ => ?_
    by_cases htri : G.Adj u v ∧ G.Adj v w ∧ G.Adj w u
    · have huv : u ≠ v := G.ne_of_adj htri.1
      have hvw : v ≠ w := G.ne_of_adj htri.2.1
      have hwu : w ≠ u := G.ne_of_adj htri.2.2
      rcases lt_or_gt_of_ne huv with h1 | h1 <;>
      rcases lt_or_gt_of_ne hvw with h2 | h2 <;>
      rcases lt_or_gt_of_ne hwu with h3 | h3
      · exact absurd (lt_trans h1 h2) (lt_asymm h3)
      · have : ¬ v < u := lt_asymm h1
        have : ¬ w < u := lt_asymm h3
        simp [htri, h1, h3, *]
      · have : ¬ u < w := lt_asymm h3
        have : ¬ v < w := lt_asymm h2
        simp [htri, h3, h2, *]
      · have : ¬ v < u := lt_asymm h1
        have : ¬ w < u := lt_asymm h3
        simp [htri, h1, h3, *]
      · have : ¬ u < v := lt_asymm h1
        have : ¬ w < v := lt_asymm h2
        simp [htri, h1, h2, *]
      · have : ¬ u < v := lt_asymm h1
        have : ¬ w < v := lt_asymm h2
        simp [htri, h1, h2, *]
      · have : ¬ u < w := lt_asymm h3
        have : ¬ v < w := lt_asymm h2
        simp [htri, h3, h2, *]
      · exact absurd (lt_trans h3 h2) (lt_asymm h1)
    · simp [htri]
  have hT2_eq : T2 = T1 := by
    dsimp only [T1, T2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ =>
      Finset.sum_congr rfl fun u _ => by
        split_ifs <;> first | rfl | (exfalso; tauto)
  have hT3_eq : T3 = T1 := by
    dsimp only [T1, T3]
    conv_lhs =>
      arg 2
      ext u
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ =>
      Finset.sum_congr rfl fun u _ =>
        Finset.sum_congr rfl fun v _ => by
          split_ifs <;> first | rfl | (exfalso; tauto)
  exact ⟨T1, by omega⟩

private lemma ordered_triangles_eq_52
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (hdeg4 : ∀ w : Fin 13, G.degree w = 4)
    (hcomm1 : ∀ u v : Fin 13, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card = 1) :
    (∑ u : Fin 13, ∑ v : Fin 13, ∑ w : Fin 13,
      if G.Adj u v ∧ G.Adj v w ∧ G.Adj w u then 1 else 0) = 52 := by
  have hinner : ∀ u v : Fin 13,
      (∑ w : Fin 13, if G.Adj u v ∧ G.Adj v w ∧ G.Adj w u then 1 else 0) =
        if G.Adj u v then 1 else 0 := by
    intro u v
    by_cases huv : G.Adj u v
    · rw [if_pos huv]
      have hne : u ≠ v := G.ne_of_adj huv
      trans (G.neighborFinset u ∩ G.neighborFinset v).card
      · rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext w
        simp [mem_neighborFinset, huv, G.adj_comm, and_comm]
      · exact hcomm1 u v hne
    · rw [if_neg huv]
      exact Finset.sum_eq_zero fun w _ => by simp [huv]
  calc (∑ u : Fin 13, ∑ v : Fin 13, ∑ w : Fin 13,
          if G.Adj u v ∧ G.Adj v w ∧ G.Adj w u then 1 else 0)
      = ∑ u : Fin 13, ∑ v : Fin 13, if G.Adj u v then 1 else 0 := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hinner u v
    _ = ∑ u : Fin 13, G.degree u := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← card_neighborFinset_eq_degree, Finset.card_eq_sum_ones, ← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext v
          simp [mem_neighborFinset]
    _ = ∑ _u : Fin 13, 4 := Finset.sum_congr rfl fun u _ => hdeg4 u
    _ = 52 := by decide

private lemma no_c4_free_with_sum_deg_ge_52
    (G : SimpleGraph (Fin 13)) [DecidableRel G.Adj]
    (hsum : 52 ≤ ∑ w : Fin 13, G.degree w)
    (hfree : ¬ cycleGraph 4 ⊑ G) : False := by
  have hle : ∀ u : Fin 13, ∀ v ∈ Finset.univ.erase u,
      (G.neighborFinset u ∩ G.neighborFinset v).card ≤ 1 := by
    intro u v hv
    exact common_card_le_one G hfree (Finset.ne_of_mem_erase hv).symm
  let S : ℕ := ∑ u : Fin 13, ∑ v ∈ Finset.univ.erase u,
      (G.neighborFinset u ∩ G.neighborFinset v).card
  have hS_eq : ∑ w : Fin 13, G.degree w * (G.degree w - 1) = S :=
    sum_deg_mul_pred_eq G
  have hS_le : S ≤ 156 := by
    calc S ≤ ∑ u : Fin 13, ∑ _v ∈ Finset.univ.erase u, 1 := by
          refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v hv => hle u v hv
      _ = 156 := by decide
  have hquad_nonneg : (0 : ℤ) ≤ ∑ w : Fin 13, ((G.degree w : ℤ) - 4) ^ 2 :=
    Finset.sum_nonneg fun w _ => sq_nonneg _
  have hquad_id : ∑ w : Fin 13, ((G.degree w : ℤ) - 4) ^ 2 =
      (S : ℤ) - 7 * (∑ w : Fin 13, (G.degree w : ℤ)) + 208 := by
    have hmul : ∀ d : ℕ, ((d * (d - 1) : ℕ) : ℤ) = (d : ℤ) * ((d : ℤ) - 1) := by
      intro d
      cases d with
      | zero => simp
      | succ k => push_cast; ring
    have hS_int : (S : ℤ) = ∑ w : Fin 13, (G.degree w : ℤ) * ((G.degree w : ℤ) - 1) := by
      rw [← hS_eq, Nat.cast_sum]
      exact Finset.sum_congr rfl fun w _ => hmul (G.degree w)
    rw [hS_int]
    have h208 : (208 : ℤ) = ∑ _w : Fin 13, (16 : ℤ) := by decide
    rw [h208, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => by ring
  have hsum_int : (52 : ℤ) ≤ ∑ w : Fin 13, (G.degree w : ℤ) := by
    exact_mod_cast hsum
  have hS_int_le : (S : ℤ) ≤ 156 := by exact_mod_cast hS_le
  have hquad_zero : ∑ w : Fin 13, ((G.degree w : ℤ) - 4) ^ 2 = 0 := by linarith
  have hS_exact : S = 156 := by omega
  have hdeg4 : ∀ w : Fin 13, G.degree w = 4 := by
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg ((G.degree w : ℤ) - 4))).mp hquad_zero
    intro w
    have hw := hall w (Finset.mem_univ w)
    have : (G.degree w : ℤ) - 4 = 0 := sq_eq_zero_iff.mp hw
    omega
  have hcomm1 : ∀ u v : Fin 13, u ≠ v → (G.neighborFinset u ∩ G.neighborFinset v).card = 1 := by
    have hdiff : ∑ u : Fin 13, ∑ v ∈ Finset.univ.erase u,
        (1 - (G.neighborFinset u ∩ G.neighborFinset v).card) = 0 := by
      have h156 : ∑ u : Fin 13, ∑ _v ∈ Finset.univ.erase u, (1 : ℕ) = 156 := by decide
      have hsub : ∑ u : Fin 13, ∑ v ∈ Finset.univ.erase u,
          (1 - (G.neighborFinset u ∩ G.neighborFinset v).card) + S = 156 := by
        rw [← Finset.sum_add_distrib]
        conv_lhs =>
          arg 2
          ext u
          rw [← Finset.sum_add_distrib]
        have heq : ∑ u : Fin 13, ∑ v ∈ Finset.univ.erase u,
            (1 - (G.neighborFinset u ∩ G.neighborFinset v).card +
              (G.neighborFinset u ∩ G.neighborFinset v).card) =
            ∑ u : Fin 13, ∑ _v ∈ Finset.univ.erase u, 1 := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v hv => ?_
          have := hle u v hv
          omega
        rw [heq, h156]
      omega
    intro u v huv
    have hu := (Finset.sum_eq_zero_iff.mp hdiff) u (Finset.mem_univ u)
    have hv := (Finset.sum_eq_zero_iff.mp hu) v (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩)
    have hle_uv := common_card_le_one G hfree huv
    omega
  have h52 := ordered_triangles_eq_52 G hdeg4 hcomm1
  have hdvd := ordered_triangles_dvd_three G
  rw [h52] at hdvd
  omega

end Erdos556H1

theorem OMA.solution : OMA.R_Erdos556_erdos_556_R1.H1 := by
  classical
  intro c hc
  by_contra hno
  have hno' : ∀ i : Fin 3, ¬ (SimpleGraph.cycleGraph 4).IsContained (c i) :=
    fun i hi => hno ⟨i, hi⟩
  have hcover : ∀ v : Fin 13, 12 ≤ ∑ i : Fin 3, (c i).degree v := by
    intro v
    have hsub : (Finset.univ.erase v : Finset (Fin 13)) ⊆
        Finset.univ.biUnion (fun i : Fin 3 => (c i).neighborFinset v) := by
      intro u hu
      have hne : v ≠ u := (Finset.ne_of_mem_erase hu).symm
      have hadj : ∃ i : Fin 3, (c i).Adj v u := by
        apply SimpleGraph.iSup_adj.mp
        rw [← hc.1]
        exact (SimpleGraph.top_adj v u).mpr hne
      rcases hadj with ⟨i, hi⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, (SimpleGraph.mem_neighborFinset (c i) v u).mpr hi⟩
    have hcard : 12 ≤ (Finset.univ.biUnion (fun i : Fin 3 => (c i).neighborFinset v)).card := by
      have h12 : (Finset.univ.erase v : Finset (Fin 13)).card = 12 := by
        simp
      rw [← h12]
      exact Finset.card_le_card hsub
    calc 12 ≤ (Finset.univ.biUnion (fun i : Fin 3 => (c i).neighborFinset v)).card := hcard
      _ ≤ ∑ i : Fin 3, ((c i).neighborFinset v).card := Finset.card_biUnion_le
      _ = ∑ i : Fin 3, (c i).degree v := by
            refine Finset.sum_congr rfl fun i _ => SimpleGraph.card_neighborFinset_eq_degree _ _
  have htot : 156 ≤ ∑ i : Fin 3, ∑ v : Fin 13, (c i).degree v := by
    rw [Finset.sum_comm]
    calc 156 = ∑ _v : Fin 13, 12 := by decide
      _ ≤ ∑ v : Fin 13, ∑ i : Fin 3, (c i).degree v :=
          Finset.sum_le_sum fun v _ => hcover v
  have hex : ∃ i : Fin 3, 52 ≤ ∑ v : Fin 13, (c i).degree v := by
    by_contra hall
    push Not at hall
    have hlt : ∑ i : Fin 3, ∑ v : Fin 13, (c i).degree v ≤ ∑ _i : Fin 3, 51 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have := hall i
      omega
    have h153 : ∑ _i : Fin 3, 51 = 153 := by decide
    omega
  rcases hex with ⟨i, hi⟩
  exact Erdos556H1.no_c4_free_with_sum_deg_ge_52 (c i) hi (hno' i)
