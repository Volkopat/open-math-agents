import OMAReductions.R_Erdos128_erdos_128_R1_H2_R1_H2_R1

-- Step Erdos128.erdos_128.R1.H2.R1.H2.R1.H2: Norin-Yepremyan upper-middle range (5n/14 <= delta <= 3n/8, alpha < 2n/5)
-- Credit: @DevinWatson (inlining verified R2 + R2.H1.R1 + R2.H1.R1.H1 + R2.H1.R1.H2 proofs)

namespace R2

open Finset SimpleGraph

lemma two_mul_induce_edgeSet_ncard {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    2 * (G.induce (S : Set V)).edgeSet.ncard = ∑ u ∈ S, #(S.filter (G.Adj u)) := by
  classical
  have h1 : (G.induce (S : Set V)).edgeSet.ncard = #(G.induce (S : Set V)).edgeFinset := by
    rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
  rw [h1, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
  rw [← Finset.sum_coe_sort S (fun u => #(S.filter (G.Adj u)))]
  apply Finset.sum_congr rfl
  intro u _
  rw [SimpleGraph.degree, ← Finset.card_map (Function.Embedding.subtype (· ∈ S))]
  congr 1
  ext v
  simp only [Finset.mem_map, SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj,
    Function.Embedding.coe_subtype, Subtype.exists, Finset.mem_filter]
  constructor
  · rintro ⟨w, hw, hadj, rfl⟩
    exact ⟨hw, hadj⟩
  · rintro ⟨hv, hadj⟩
    exact ⟨v, hv, hadj, rfl⟩

lemma sum_adj_union_indep {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I S : Finset V}
    (hdisj : Disjoint I S)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y) :
    ∑ u ∈ I ∪ S, #((I ∪ S).filter (G.Adj u)) =
      2 * (∑ w ∈ S, #(I.filter (G.Adj w))) + ∑ u ∈ S, #(S.filter (G.Adj u)) := by
  rw [Finset.sum_union hdisj]
  have hfilter : ∀ u, #((I ∪ S).filter (G.Adj u)) = #(I.filter (G.Adj u)) + #(S.filter (G.Adj u)) := by
    intro u
    rw [Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
  simp_rw [hfilter, Finset.sum_add_distrib]
  have hII : ∑ u ∈ I, #(I.filter (G.Adj u)) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv
    exact hI u hu v hv
  have hIS : ∑ u ∈ I, #(S.filter (G.Adj u)) = ∑ w ∈ S, #(I.filter (G.Adj w)) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro u _
    simp [G.adj_comm]
  omega

lemma card_powersetCard_mem {V : Type} [DecidableEq V]
    (R : Finset V) {r : ℕ} {w : V} (hw : w ∈ R) (hr : 1 ≤ r) :
    #((R.powersetCard r).filter (w ∈ ·)) = (#R - 1).choose (r - 1) := by
  have hbij : #((R.powersetCard r).filter (w ∈ ·)) = #((R.erase w).powersetCard (r - 1)) := by
    refine Finset.card_bij (fun S _ => S.erase w) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
      exact ⟨Finset.erase_subset_erase w hS.1.1, by rw [Finset.card_erase_of_mem hS.2, hS.1.2]⟩
    · intro S₁ hS₁ S₂ hS₂ heq
      simp only [Finset.mem_filter] at hS₁ hS₂
      rw [← Finset.insert_erase hS₁.2, ← Finset.insert_erase hS₂.2, heq]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      have hwT : w ∉ T := fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
      refine ⟨insert w T, ?_, Finset.erase_insert hwT⟩
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_insert, true_or, and_true]
      refine ⟨Finset.insert_subset hw (hT.1.trans (Finset.erase_subset _ _)), ?_⟩
      rw [Finset.card_insert_of_notMem hwT, hT.2]
      omega
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem hw]

lemma card_powersetCard_mem_pair {V : Type} [DecidableEq V]
    (R : Finset V) {r : ℕ} {u v : V}
    (hu : u ∈ R) (hv : v ∈ R) (huv : u ≠ v) (hr : 2 ≤ r) :
    #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) = (#R - 2).choose (r - 2) := by
  have hv' : v ∈ R.erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  have hbij : #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) =
      #(((R.erase u).erase v).powersetCard (r - 2)) := by
    refine Finset.card_bij (fun S _ => (S.erase u).erase v) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS ⊢
      have hvS : v ∈ S.erase u := Finset.mem_erase.mpr ⟨huv.symm, hS.2.2⟩
      refine ⟨Finset.erase_subset_erase v (Finset.erase_subset_erase u hS.1.1), ?_⟩
      rw [Finset.card_erase_of_mem hvS, Finset.card_erase_of_mem hS.2.1, hS.1.2]
      omega
    · intro S₁ hS₁ S₂ hS₂ heq
      simp only [Finset.mem_filter] at hS₁ hS₂
      have hv1 : v ∈ S₁.erase u := Finset.mem_erase.mpr ⟨huv.symm, hS₁.2.2⟩
      have hv2 : v ∈ S₂.erase u := Finset.mem_erase.mpr ⟨huv.symm, hS₂.2.2⟩
      have heq1 : S₁.erase u = S₂.erase u := by
        rw [← Finset.insert_erase hv1, ← Finset.insert_erase hv2, heq]
      rw [← Finset.insert_erase hS₁.2.1, ← Finset.insert_erase hS₂.2.1, heq1]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      have hvT : v ∉ T := fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
      have huT : u ∉ insert v T := by
        intro h
        rcases Finset.mem_insert.mp h with rfl | h'
        · exact huv rfl
        · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hT.1 h')).2).1 rfl
      refine ⟨insert u (insert v T), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_insert, true_or, or_true, and_true]
        refine ⟨Finset.insert_subset hu (Finset.insert_subset hv
          (hT.1.trans ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))), ?_⟩
        rw [Finset.card_insert_of_notMem huT, Finset.card_insert_of_notMem hvT, hT.2]
        omega
      · rw [Finset.erase_insert huT, Finset.erase_insert hvT]
  rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem hv', Finset.card_erase_of_mem hu,
    show #R - 1 - 1 = #R - 2 by omega]

lemma avg_indep_union_ge {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I R : Finset V} {r T : ℕ}
    (hdisj : Disjoint I R)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hr1 : 1 ≤ r) (hrR : r ≤ #R) (hR2 : 2 ≤ #R)
    (hbound : ∀ S ∈ R.powersetCard r, T ≤ 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard) :
    T * #R * (#R - 1) ≤
      2 * r * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
      r * (r - 1) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by
  have hsum_le : (#R).choose r * T ≤
      ∑ S ∈ R.powersetCard r, 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard := by
    calc (#R).choose r * T
        = ∑ _S ∈ R.powersetCard r, T := by rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hbound
  have hsum_eq : ∑ S ∈ R.powersetCard r, 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard =
      2 * (#R - 1).choose (r - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
      (if 2 ≤ r then (#R - 2).choose (r - 2) * (∑ u ∈ R, #(R.filter (G.Adj u))) else 0) := by
    have hstep : ∀ S ∈ R.powersetCard r,
        2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard =
        2 * (∑ w ∈ S, #(I.filter (G.Adj w))) + ∑ u ∈ S, #(S.filter (G.Adj u)) := by
      intro S hS
      rw [two_mul_induce_edgeSet_ncard]
      exact sum_adj_union_indep G (hdisj.mono_right (Finset.mem_powersetCard.mp hS).1) hI
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · have h1 : ∑ S ∈ R.powersetCard r, ∑ w ∈ S, #(I.filter (G.Adj w)) =
          ∑ w ∈ R, #((R.powersetCard r).filter (w ∈ ·)) * #(I.filter (G.Adj w)) := by
        calc ∑ S ∈ R.powersetCard r, ∑ w ∈ S, #(I.filter (G.Adj w))
            = ∑ S ∈ R.powersetCard r, ∑ w ∈ R, if w ∈ S then #(I.filter (G.Adj w)) else 0 := by
              apply Finset.sum_congr rfl
              intro S hS
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
                Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hS).1]
          _ = ∑ w ∈ R, ∑ S ∈ R.powersetCard r, if w ∈ S then #(I.filter (G.Adj w)) else 0 := Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl
              intro w _
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      rw [h1, mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      rw [card_powersetCard_mem R hw hr1]
    · by_cases hr2 : 2 ≤ r
      · rw [if_pos hr2]
        have h2 : ∑ S ∈ R.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u)) =
            ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) := by
          calc ∑ S ∈ R.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u))
              = ∑ S ∈ R.powersetCard r, ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u),
                  if u ∈ S ∧ v ∈ S then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro S hS
                have hSR := (Finset.mem_powersetCard.mp hS).1
                calc ∑ u ∈ S, #(S.filter (G.Adj u))
                    = ∑ u ∈ R, if u ∈ S then #(S.filter (G.Adj u)) else 0 := by
                      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSR]
                  _ = ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), if u ∈ S ∧ v ∈ S then 1 else 0 := by
                      apply Finset.sum_congr rfl
                      intro u _
                      by_cases hu : u ∈ S
                      · simp only [hu, true_and, if_true, ← Finset.card_filter]
                        congr 1
                        ext v
                        simp only [Finset.mem_filter]
                        exact ⟨fun ⟨hv, hadj⟩ => ⟨⟨hSR hv, hadj⟩, hv⟩, fun ⟨⟨_, hadj⟩, hv⟩ => ⟨hv, hadj⟩⟩
                      · simp [hu]
            _ = ∑ u ∈ R, ∑ S ∈ R.powersetCard r, ∑ v ∈ R.filter (G.Adj u),
                  if u ∈ S ∧ v ∈ S then 1 else 0 := Finset.sum_comm
            _ = ∑ u ∈ R, ∑ v ∈ R.filter (G.Adj u), ∑ S ∈ R.powersetCard r,
                  if u ∈ S ∧ v ∈ S then 1 else 0 := by
                apply Finset.sum_congr rfl
                intro u _
                exact Finset.sum_comm
            _ = _ := by
                apply Finset.sum_congr rfl
                intro u _
                apply Finset.sum_congr rfl
                intro v _
                rw [← Finset.card_filter]
        rw [h2, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        have hinner : ∑ v ∈ R.filter (G.Adj u), #((R.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) =
            ∑ _v ∈ R.filter (G.Adj u), (#R - 2).choose (r - 2) := by
          apply Finset.sum_congr rfl
          intro v hv
          have hv' := Finset.mem_filter.mp hv
          exact card_powersetCard_mem_pair R hu hv'.1 (G.ne_of_adj hv'.2) hr2
        rw [hinner, Finset.sum_const, smul_eq_mul, mul_comm]
      · rw [if_neg hr2]
        have hr_eq : r = 1 := by omega
        apply Finset.sum_eq_zero
        intro S hS
        have hScard : #S = 1 := by rw [(Finset.mem_powersetCard.mp hS).2, hr_eq]
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hScard
        simp
  rw [hsum_eq] at hsum_le
  have hpos : 0 < (#R).choose r := Nat.choose_pos hrR
  have hc1 : (#R).choose r * r = #R * (#R - 1).choose (r - 1) := by
    have := Nat.add_one_mul_choose_eq (#R - 1) (r - 1)
    rw [show #R - 1 + 1 = #R by omega, show r - 1 + 1 = r by omega] at this
    linarith
  have hc2 : 2 ≤ r → (#R).choose r * r * (r - 1) = #R * (#R - 1) * (#R - 2).choose (r - 2) := by
    intro hr2
    have hstep1 : (#R - 1).choose (r - 1) * (r - 1) = (#R - 1) * (#R - 2).choose (r - 2) := by
      have := Nat.add_one_mul_choose_eq (#R - 2) (r - 2)
      rw [show #R - 2 + 1 = #R - 1 by omega, show r - 2 + 1 = r - 1 by omega] at this
      linarith
    calc (#R).choose r * r * (r - 1)
        = (#R * (#R - 1).choose (r - 1)) * (r - 1) := by rw [hc1]
      _ = #R * ((#R - 1).choose (r - 1) * (r - 1)) := by ring
      _ = #R * ((#R - 1) * (#R - 2).choose (r - 2)) := by rw [hstep1]
      _ = #R * (#R - 1) * (#R - 2).choose (r - 2) := by ring
  have hmul := Nat.mul_le_mul_left (#R * (#R - 1)) hsum_le
  by_cases hr2 : 2 ≤ r
  · rw [if_pos hr2] at hmul
    have hkey : (#R).choose r * (T * #R * (#R - 1)) ≤
        (#R).choose r * (2 * r * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
          r * (r - 1) * (∑ u ∈ R, #(R.filter (G.Adj u)))) := by
      calc (#R).choose r * (T * #R * (#R - 1))
          = #R * (#R - 1) * ((#R).choose r * T) := by ring
        _ ≤ #R * (#R - 1) * (2 * (#R - 1).choose (r - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
              (#R - 2).choose (r - 2) * (∑ u ∈ R, #(R.filter (G.Adj u)))) := hmul
        _ = 2 * (#R * (#R - 1).choose (r - 1)) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
            (#R * (#R - 1) * (#R - 2).choose (r - 2)) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by ring
        _ = 2 * ((#R).choose r * r) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
            ((#R).choose r * r * (r - 1)) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by rw [← hc1, ← hc2 hr2]
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hkey hpos
  · rw [if_neg hr2, add_zero] at hmul
    have hr_eq : r = 1 := by omega
    subst hr_eq
    have hkey : (#R).choose 1 * (T * #R * (#R - 1)) ≤
        (#R).choose 1 * (2 * 1 * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
          1 * (1 - 1) * (∑ u ∈ R, #(R.filter (G.Adj u)))) := by
      calc (#R).choose 1 * (T * #R * (#R - 1))
          = #R * (#R - 1) * ((#R).choose 1 * T) := by ring
        _ ≤ #R * (#R - 1) * (2 * (#R - 1).choose (1 - 1) * (∑ w ∈ R, #(I.filter (G.Adj w)))) := hmul
        _ = 2 * (#R * (#R - 1).choose (1 - 1)) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) := by ring
        _ = 2 * ((#R).choose 1 * 1) * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) := by rw [← hc1]
        _ = _ := by simp; ring
    exact Nat.le_of_mul_le_mul_left hkey hpos

lemma avg_indep_union_gt {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {I R : Finset V} {r T : ℕ}
    (hdisj : Disjoint I R)
    (hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hr1 : 1 ≤ r) (hrR : r ≤ #R) (hR2 : 2 ≤ #R)
    (hbound : ∀ S ∈ R.powersetCard r, T < 2 * (G.induce ((I ∪ S : Finset V) : Set V)).edgeSet.ncard) :
    T * #R * (#R - 1) <
      2 * r * (#R - 1) * (∑ w ∈ R, #(I.filter (G.Adj w))) +
      r * (r - 1) * (∑ u ∈ R, #(R.filter (G.Adj u))) := by
  have hge := avg_indep_union_ge G hdisj hI hr1 hrR hR2 (fun S hS => Nat.succ_le_of_lt (hbound S hS))
  have hpos : 0 < #R * (#R - 1) := Nat.mul_pos (by omega) (by omega)
  nlinarith

lemma not_adj_of_cliqueFree_three {V : Type} {G : SimpleGraph V}
    (hTF : G.CliqueFree 3) {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    False := by
  classical
  have hne_ab : a ≠ b := G.ne_of_adj hab
  have hne_bc : b ≠ c := G.ne_of_adj hbc
  have hne_ac : a ≠ c := G.ne_of_adj hac
  apply hTF {a, b, c}
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals first | exact (hxy rfl).elim | exact hab | exact hab.symm | exact hbc | exact hbc.symm | exact hac | exact hac.symm
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hne_bc]
    · simp [hne_ab, hne_ac]

lemma filter_adj_indep {V : Type} {G : SimpleGraph V} [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) (A : Finset V) (v : V) :
    ∀ x ∈ A.filter (G.Adj v), ∀ y ∈ A.filter (G.Adj v), ¬ G.Adj x y := by
  intro x hx y hy hxy
  exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hx).2 hxy (Finset.mem_filter.mp hy).2

theorem five_mul_indep_lt_two_mul_card {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (I₀ : Set V) (hI₀ : G.IsIndepSet I₀) :
    5 * I₀.ncard < 2 * Fintype.card V := by
  classical
  by_contra hge
  push Not at hge
  set n := Fintype.card V
  set k := n / 2
  have hk_cond : ∀ S : Finset V, #S = k → 50 * (G.induce (S : Set V)).edgeSet.ncard > n ^ 2 := by
    intro S hS
    apply hH (S : Set V)
    rw [Set.ncard_coe_finset, hS]
    omega
  -- Pick maximum independent Finset I
  let indepSets : Finset (Finset V) :=
    Finset.univ.filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
  have hI₀_mem : I₀.toFinset ∈ indepSets := by
    simp only [indepSets, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset]
    intro x hx y hy hadj
    exact hI₀ hx hy (G.ne_of_adj hadj) hadj
  obtain ⟨I, hI_mem, hI_max⟩ := Finset.exists_max_image indepSets Finset.card ⟨I₀.toFinset, hI₀_mem⟩
  have hI : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y := (Finset.mem_filter.mp hI_mem).2
  have hI_le : ∀ J : Finset V, (∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y) → #J ≤ #I := by
    intro J hJ
    exact hI_max J (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩)
  set α := #I
  have h5a : 2 * n ≤ 5 * α := by
    have hcard : I₀.ncard = #I₀.toFinset := Set.ncard_eq_toFinset_card' I₀
    have hle : #I₀.toFinset ≤ α := hI_max I₀.toFinset hI₀_mem
    omega
  -- Step 1: α < k (else k-subset of I has 0 edges)
  have hα_lt_k : α < k := by
    by_contra hka
    push Not at hka
    obtain ⟨S, hSI, hScard⟩ := Finset.exists_subset_card_eq hka
    have hpos := hk_cond S hScard
    have hzero : 2 * (G.induce (S : Set V)).edgeSet.ncard = 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv
      exact hI u (hSI hu) v (hSI hv)
    omega
  set r := k - α
  have hr1 : 1 ≤ r := by omega
  have hα_pos : 0 < α := by omega
  -- Step 2: every k-subset has 2 * e > α * r
  have h_gt_ar : ∀ S : Finset V, #S = k → α * r < 2 * (G.induce (S : Set V)).edgeSet.ncard := by
    intro S hS
    have h50 := hk_cond S hS
    have h50ar : 50 * (α * r) ≤ 2 * n ^ 2 := by
      have h2r : 2 * r + 2 * α ≤ n := by omega
      have h1 : (0 : ℤ) ≤ (5 * (α : ℤ) - 2 * n) * (10 * α - n) :=
        mul_nonneg (by omega) (by omega)
      zify
      nlinarith
    omega
  -- Step 3: Partition V \ I into R₁ (high deg into I) and R₀ (low deg into I)
  let R₁ : Finset V := (Finset.univ \ I).filter (fun v => α < 2 * #(I.filter (G.Adj v)))
  let R₀ : Finset V := (Finset.univ \ I).filter (fun v => 2 * #(I.filter (G.Adj v)) ≤ α)
  have hR₁_indep : ∀ u ∈ R₁, ∀ v ∈ R₁, ¬ G.Adj u v := by
    intro u hu v hv huv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    have hdisj : Disjoint (I.filter (G.Adj u)) (I.filter (G.Adj v)) := by
      rw [Finset.disjoint_left]
      intro x hxu hxv
      exact not_adj_of_cliqueFree_three hTF huv (Finset.mem_filter.mp hxv).2 (Finset.mem_filter.mp hxu).2
    have hunion : #(I.filter (G.Adj u)) + #(I.filter (G.Adj v)) ≤ #I := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    omega
  set m₁ := #R₁
  set m₀ := #R₀
  have hm₁_le : m₁ ≤ α := hI_le R₁ hR₁_indep
  have hdisj_IR₀ : Disjoint I R₀ := by
    rw [Finset.disjoint_left]
    intro x hx hx0
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx0).1).2 hx
  have hdisj_IR₁ : Disjoint I R₁ := by
    rw [Finset.disjoint_left]
    intro x hx hx1
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx1).1).2 hx
  have hdisj_R₁R₀ : Disjoint R₁ R₀ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx0
    have h1 := (Finset.mem_filter.mp hx1).2
    have h0 := (Finset.mem_filter.mp hx0).2
    omega
  have hpart : α + m₁ + m₀ = n := by
    have hR : m₁ + m₀ = #(Finset.univ \ I) := by
      rw [← Finset.card_union_of_disjoint hdisj_R₁R₀]
      congr 1
      ext x
      simp only [R₁, R₀, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        by_cases h : α < 2 * #(I.filter (G.Adj x))
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by omega⟩
    have hsdiff : #(Finset.univ \ I) + α = n := by
      rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I), Finset.card_univ]
    omega
  set r₁ := k - m₁
  have hr_le_r₁ : r ≤ r₁ := by omega
  have hr_sum : r + r₁ ≤ m₀ := by omega
  have hm₀_ge_2r : 2 * r ≤ m₀ := by omega
  -- Step 4: Max independent subset J ⊆ R₀
  let indepR₀ : Finset (Finset V) :=
    R₀.powerset.filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
  have hEmpty_R₀ : (∅ : Finset V) ∈ indepR₀ := by
    simp [indepR₀]
  obtain ⟨J, hJ_mem, hJ_max⟩ := Finset.exists_max_image indepR₀ Finset.card ⟨∅, hEmpty_R₀⟩
  have hJ_sub : J ⊆ R₀ := Finset.mem_powerset.mp (Finset.mem_filter.mp hJ_mem).1
  have hJ_indep : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y := (Finset.mem_filter.mp hJ_mem).2
  set β := #J
  -- Case 1: r ≤ β
  by_cases hβ : r ≤ β
  · obtain ⟨S, hSJ, hScard⟩ := Finset.exists_subset_card_eq hβ
    have hSR₀ : S ⊆ R₀ := hSJ.trans hJ_sub
    have hS_indep : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y := fun x hx y hy => hJ_indep x (hSJ hx) y (hSJ hy)
    have hcard_IS : #(I ∪ S) = k := by
      rw [Finset.card_union_of_disjoint (hdisj_IR₀.mono_right hSR₀), hScard]
      omega
    have hgt := h_gt_ar (I ∪ S) hcard_IS
    rw [two_mul_induce_edgeSet_ncard, sum_adj_union_indep G (hdisj_IR₀.mono_right hSR₀) hI] at hgt
    have hSS : ∑ u ∈ S, #(S.filter (G.Adj u)) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v hv
      exact hS_indep u hu v hv
    have hIS : 2 * ∑ w ∈ S, #(I.filter (G.Adj w)) ≤ r * α := by
      calc 2 * ∑ w ∈ S, #(I.filter (G.Adj w))
          = ∑ w ∈ S, 2 * #(I.filter (G.Adj w)) := Finset.mul_sum _ _ _
        _ ≤ ∑ _w ∈ S, α := Finset.sum_le_sum (fun w hw => (Finset.mem_filter.mp (hSR₀ hw)).2)
        _ = r * α := by rw [Finset.sum_const, hScard, smul_eq_mul]
    nlinarith
  -- Case 2: β < r
  · push Not at hβ
    -- Show 1 ≤ β (hence 2 ≤ r and 4 ≤ m₀)
    have hβ_pos : 1 ≤ β := by
      have hm₀_pos : 0 < #R₀ := by omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp hm₀_pos
      have hw_mem : ({w} : Finset V) ∈ indepR₀ := by
        simp only [indepR₀, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff,
          Finset.mem_singleton]
        refine ⟨hw, ?_⟩
        rintro _ rfl _ rfl
        exact G.loopless.irrefl _
      have := hJ_max {w} hw_mem
      simpa using this
    have hr2 : 2 ≤ r := by omega
    have hm₀2 : 2 ≤ m₀ := by omega
    set e₁ := ∑ w ∈ R₀, #(I.filter (G.Adj w))
    set e₂ := ∑ w ∈ R₀, #(R₁.filter (G.Adj w))
    set d₀ := ∑ u ∈ R₀, #(R₀.filter (G.Adj u))
    -- (F1): e₁ + e₂ + d₀ ≤ m₀ * α
    have hF1 : e₁ + e₂ + d₀ ≤ m₀ * α := by
      have hsum : e₁ + e₂ + d₀ =
          ∑ w ∈ R₀, (#(I.filter (G.Adj w)) + #(R₁.filter (G.Adj w)) + #(R₀.filter (G.Adj w))) := by
        simp only [e₁, e₂, d₀, Finset.sum_add_distrib]
      rw [hsum]
      calc ∑ w ∈ R₀, (#(I.filter (G.Adj w)) + #(R₁.filter (G.Adj w)) + #(R₀.filter (G.Adj w)))
          ≤ ∑ _w ∈ R₀, α := by
            apply Finset.sum_le_sum
            intro w _
            have hd1 : Disjoint (I.filter (G.Adj w)) (R₁.filter (G.Adj w)) :=
              hdisj_IR₁.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
            have hd2 : Disjoint (I.filter (G.Adj w) ∪ R₁.filter (G.Adj w)) (R₀.filter (G.Adj w)) :=
              (Finset.disjoint_union_left.mpr ⟨hdisj_IR₀, hdisj_R₁R₀⟩).mono
                (Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _))
                (Finset.filter_subset _ _)
            rw [← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
            have hsub : I.filter (G.Adj w) ∪ R₁.filter (G.Adj w) ∪ R₀.filter (G.Adj w) ⊆
                Finset.univ.filter (G.Adj w) := by
              intro x hx
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              rcases hx with (⟨_, h⟩ | ⟨_, h⟩) | ⟨_, h⟩ <;> exact h
            exact (Finset.card_le_card hsub).trans (hI_le _ (filter_adj_indep hTF Finset.univ w))
        _ = m₀ * α := by rw [Finset.sum_const, smul_eq_mul]
    -- (F2): e₁ ≤ α * (r - 1)
    have hF2 : e₁ ≤ α * (r - 1) := by
      have hswap : e₁ = ∑ x ∈ I, #(R₀.filter (G.Adj x)) := by
        simp only [e₁, Finset.card_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro w _
        simp [G.adj_comm]
      rw [hswap]
      calc ∑ x ∈ I, #(R₀.filter (G.Adj x))
          ≤ ∑ _x ∈ I, (r - 1) := by
            apply Finset.sum_le_sum
            intro x _
            have hmem : R₀.filter (G.Adj x) ∈ indepR₀ :=
              Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
                filter_adj_indep hTF R₀ x⟩
            have hle := hJ_max _ hmem
            omega
        _ = α * (r - 1) := by rw [Finset.sum_const, smul_eq_mul]
    -- (F3): averaging over r-subsets S ⊆ R₀ added to I
    have hF3_raw : α * r * m₀ * (m₀ - 1) < 2 * r * (m₀ - 1) * e₁ + r * (r - 1) * d₀ := by
      refine avg_indep_union_gt G hdisj_IR₀ hI hr1 (by omega) hm₀2 ?_
      intro S hS
      apply h_gt_ar (I ∪ S)
      rw [Finset.card_union_of_disjoint (hdisj_IR₀.mono_right (Finset.mem_powersetCard.mp hS).1),
        (Finset.mem_powersetCard.mp hS).2]
      omega
    have hF3 : α * m₀ * (m₀ - 1) < 2 * (m₀ - 1) * e₁ + (r - 1) * d₀ := by
      have hrpos : 0 < r := by omega
      nlinarith
    -- (F4): averaging over r₁-subsets S' ⊆ R₀ added to R₁
    have hF4 : α * r * m₀ * (m₀ - 1) < 2 * r₁ * (m₀ - 1) * e₂ + r₁ * (r₁ - 1) * d₀ := by
      refine avg_indep_union_gt G hdisj_R₁R₀ hR₁_indep (by omega) (by omega) hm₀2 ?_
      intro S hS
      apply h_gt_ar (R₁ ∪ S)
      rw [Finset.card_union_of_disjoint (hdisj_R₁R₀.mono_right (Finset.mem_powersetCard.mp hS).1),
        (Finset.mem_powersetCard.mp hS).2]
      omega
    -- Exact integer cancellation ending in d² + (r+d)*s + 2r + 3d > 0
    have hfinal : False := by
      have hA : (0 : ℤ) < (α : ℤ) := Nat.cast_pos.mpr hα_pos
      have hR : (2 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr2
      have hRR1 : (r : ℤ) ≤ (r₁ : ℤ) := Nat.cast_le.mpr hr_le_r₁
      have hsumR : (r : ℤ) + (r₁ : ℤ) ≤ (m₀ : ℤ) := by exact_mod_cast hr_sum
      have hD0 : (0 : ℤ) ≤ (d₀ : ℤ) := Nat.cast_nonneg d₀
      have h1z : (e₁ : ℤ) + (e₂ : ℤ) + (d₀ : ℤ) ≤ (m₀ : ℤ) * (α : ℤ) := by exact_mod_cast hF1
      have h2z : (e₁ : ℤ) ≤ (α : ℤ) * ((r : ℤ) - 1) := by
        have : (e₁ : ℤ) ≤ ((α * (r - 1) : ℕ) : ℤ) := Nat.cast_le.mpr hF2
        rw [Nat.cast_mul, Nat.cast_sub (by omega)] at this
        simpa using this
      have h3z : (α : ℤ) * (m₀ : ℤ) * ((m₀ : ℤ) - 1) <
          2 * ((m₀ : ℤ) - 1) * (e₁ : ℤ) + ((r : ℤ) - 1) * (d₀ : ℤ) := by
        have : ((α * m₀ * (m₀ - 1) : ℕ) : ℤ) < ((2 * (m₀ - 1) * e₁ + (r - 1) * d₀ : ℕ) : ℤ) :=
          Nat.cast_lt.mpr hF3
        push_cast [Nat.cast_sub (show 1 ≤ m₀ by omega), Nat.cast_sub (show 1 ≤ r by omega)] at this
        simpa using this
      have h4z : (α : ℤ) * (r : ℤ) * (m₀ : ℤ) * ((m₀ : ℤ) - 1) <
          2 * (r₁ : ℤ) * ((m₀ : ℤ) - 1) * (e₂ : ℤ) + (r₁ : ℤ) * ((r₁ : ℤ) - 1) * (d₀ : ℤ) := by
        have : ((α * r * m₀ * (m₀ - 1) : ℕ) : ℤ) <
            ((2 * r₁ * (m₀ - 1) * e₂ + r₁ * (r₁ - 1) * d₀ : ℕ) : ℤ) :=
          Nat.cast_lt.mpr hF4
        push_cast [Nat.cast_sub (show 1 ≤ m₀ by omega), Nat.cast_sub (show 1 ≤ r₁ by omega)] at this
        simpa using this
      set A : ℤ := (α : ℤ)
      set M : ℤ := (m₀ : ℤ)
      set R : ℤ := (r : ℤ)
      set R1 : ℤ := (r₁ : ℤ)
      set E1 : ℤ := (e₁ : ℤ)
      set E2 : ℤ := (e₂ : ℤ)
      set D0 : ℤ := (d₀ : ℤ)
      have hM1 : 0 < M - 1 := by linarith
      have hMpos : 0 < M := by linarith
      have hR1pos : 0 < R1 := by linarith
      have hR1m : 0 < R - 1 := by linarith
      have hw1 : 0 < R1 * (M + R - 1) := mul_pos hR1pos (by linarith)
      have hc1 := mul_lt_mul_of_pos_left h3z hw1
      have hc2 := mul_lt_mul_of_pos_left h4z hR1m
      have hadd : R1 * (M + R - 1) * (A * M * (M - 1)) + (R - 1) * (A * R * M * (M - 1)) <
          R1 * (M + R - 1) * (2 * (M - 1) * E1 + (R - 1) * D0) +
          (R - 1) * (2 * R1 * (M - 1) * E2 + R1 * (R1 - 1) * D0) := add_lt_add hc1 hc2
      have hnn1 : 0 ≤ 2 * (M - 1) * R1 * (R - 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM1.le) hR1pos.le) hR1m.le
      have hnn2 : 0 ≤ 2 * (M - 1) * R1 * M :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM1.le) hR1pos.le) hMpos.le
      have hnn3 : 0 ≤ (R - 1) * R1 * D0 :=
        mul_nonneg (mul_nonneg hR1m.le hR1pos.le) hD0
      have hterm1 : 2 * (M - 1) * R1 * (R - 1) * (E1 + E2 + D0) ≤
          2 * (M - 1) * R1 * (R - 1) * (M * A) := mul_le_mul_of_nonneg_left h1z hnn1
      have hterm2 : 2 * (M - 1) * R1 * M * E1 ≤ 2 * (M - 1) * R1 * M * (A * (R - 1)) :=
        mul_le_mul_of_nonneg_left h2z hnn2
      have hterm3 : (R - 1) * R1 * D0 * (R + R1 - M) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hnn3 (by linarith)
      have hrhs : R1 * (M + R - 1) * (2 * (M - 1) * E1 + (R - 1) * D0) +
          (R - 1) * (2 * R1 * (M - 1) * E2 + R1 * (R1 - 1) * D0) ≤
          4 * A * M * (M - 1) * R1 * (R - 1) := by
        have hid : R1 * (M + R - 1) * (2 * (M - 1) * E1 + (R - 1) * D0) +
            (R - 1) * (2 * R1 * (M - 1) * E2 + R1 * (R1 - 1) * D0) =
            2 * (M - 1) * R1 * (R - 1) * (E1 + E2 + D0) +
            2 * (M - 1) * R1 * M * E1 +
            (R - 1) * R1 * D0 * (R + R1 - M) := by ring
        have hsum4 : 2 * (M - 1) * R1 * (R - 1) * (M * A) +
            2 * (M - 1) * R1 * M * (A * (R - 1)) = 4 * A * M * (M - 1) * R1 * (R - 1) := by ring
        linarith
      have hcore : 0 < R1 * (M - 3 * R + 3) + R * (R - 1) := by
        have hdecomp : R1 * (M - 3 * R + 3) + R * (R - 1) =
            (R1 - R) ^ 2 + R1 * (M - R - R1) + 2 * R + 3 * (R1 - R) := by ring
        have hnonneg1 : 0 ≤ (R1 - R) ^ 2 := sq_nonneg _
        have hnonneg2 : 0 ≤ R1 * (M - R - R1) := mul_nonneg hR1pos.le (by linarith)
        linarith
      have hlhs : 4 * A * M * (M - 1) * R1 * (R - 1) <
          R1 * (M + R - 1) * (A * M * (M - 1)) + (R - 1) * (A * R * M * (M - 1)) := by
        have hid2 : R1 * (M + R - 1) * (A * M * (M - 1)) + (R - 1) * (A * R * M * (M - 1)) -
            4 * A * M * (M - 1) * R1 * (R - 1) =
            (A * M * (M - 1)) * (R1 * (M - 3 * R + 3) + R * (R - 1)) := by ring
        have hpos_f : 0 < A * M * (M - 1) := mul_pos (mul_pos hA hMpos) hM1
        have := mul_pos hpos_f hcore
        linarith
      linarith
    exact hfinal

theorem five_mul_deg_lt_two_mul_card {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (v : V) :
    5 * (G.neighborSet v).ncard < 2 * Fintype.card V := by
  apply five_mul_indep_lt_two_mul_card G hTF hH (G.neighborSet v)
  intro x hx y hy _ hxy
  exact not_adj_of_cliqueFree_three hTF hx hxy hy

theorem five_mul_edges_lt_sq {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    5 * G.edgeSet.ncard < Fintype.card V ^ 2 := by
  classical
  have hne : 0 < Fintype.card V := by
    by_contra h0
    have hcard0 : Fintype.card V = 0 := by omega
    have h := hH ∅ (by simp [hcard0])
    have hempty : 2 * (G.induce (∅ : Set V)).edgeSet.ncard = 0 := by
      have h2 := two_mul_induce_edgeSet_ncard G (∅ : Finset V)
      rw [Finset.coe_empty] at h2
      simpa using h2
    omega
  have hedge : 2 * G.edgeSet.ncard = ∑ v : V, (G.neighborSet v).ncard := by
    have h1 : G.edgeSet.ncard = #G.edgeFinset := by
      rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
    rw [h1, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
    apply Finset.sum_congr rfl
    intro v _
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card']
  have hsum : ∑ v : V, 5 * (G.neighborSet v).ncard < ∑ _v : V, 2 * Fintype.card V := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by simpa using hne))
    intro v _
    exact five_mul_deg_lt_two_mul_card G hTF hH v
  rw [← Finset.mul_sum, ← hedge, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  nlinarith

lemma six_le_card {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    6 ≤ Fintype.card V := by
  classical
  by_contra hlt
  push Not at hlt
  set n := Fintype.card V
  by_cases hn3 : n ≤ 3
  · have hle : n / 2 ≤ #(Finset.univ : Finset V) := by simp; omega
    obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq hle
    have hpos := hH (S : Set V) (by rw [Set.ncard_coe_finset, hScard]; omega)
    have hzero : 2 * (G.induce (S : Set V)).edgeSet.ncard = 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      by_cases h0 : #S = 0
      · rw [Finset.card_eq_zero.mp h0]; simp
      · have h1 : #S = 1 := by omega
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
        simp
    omega
  · -- n = 4 or 5: every pair is adjacent, so any 3 distinct vertices form a triangle
    have hn4 : 4 ≤ n := by omega
    have hall : ∀ a b : V, a ≠ b → G.Adj a b := by
      intro a b hab
      have hcard2 : #({a, b} : Finset V) = 2 := Finset.card_pair hab
      have hpos := hH (({a, b} : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard2]; omega)
      by_contra hnadj
      have hzero : 2 * (G.induce (({a, b} : Finset V) : Set V)).edgeSet.ncard = 0 := by
        rw [two_mul_induce_edgeSet_ncard]
        rw [Finset.sum_pair hab]
        have ha : ({a, b} : Finset V).filter (G.Adj a) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact G.loopless.irrefl _
          · rw [Finset.mem_singleton.mp hx']; exact hnadj
        have hb : ({a, b} : Finset V).filter (G.Adj b) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact fun h => hnadj h.symm
          · rw [Finset.mem_singleton.mp hx']; exact G.loopless.irrefl _
        rw [ha, hb]; simp
      omega
    have h3le : 3 ≤ #(Finset.univ : Finset V) := by simp; omega
    obtain ⟨T, -, hTcard⟩ := Finset.exists_subset_card_eq h3le
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hTcard
    exact not_adj_of_cliqueFree_three hTF (hall a b hab) (hall b c hbc) (hall a c hac)

lemma exists_shortest_odd_walk_of_nonbip {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) (hnot2col : ¬ G.Colorable 2) :
    ∃ L : ℕ, Odd L ∧ 5 ≤ L ∧
      (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → V, g L' = g 0 ∧ ∀ i < L', G.Adj (g i) (g (i + 1))) ∧
      ∃ f : ℕ → V, f L = f 0 ∧ (∀ i < L, G.Adj (f i) (f (i + 1))) ∧
        (∀ i j, i < j → j < L → f i ≠ f j) ∧
        (∀ i j, i + 2 ≤ j → j < L → j - i ≤ L - 2 → ¬ G.Adj (f i) (f j)) := by
  classical
  have hex_odd : ∃ L : ℕ, Odd L ∧ ∃ f : ℕ → V, f L = f 0 ∧ ∀ i < L, G.Adj (f i) (f (i + 1)) := by
    rw [SimpleGraph.two_colorable_iff_forall_loop_even] at hnot2col
    push Not at hnot2col
    obtain ⟨u, w, hneven⟩ := hnot2col
    refine ⟨w.length, Nat.not_even_iff_odd.mp hneven, fun i => w.getVert i, ?_, ?_⟩
    · simp
    · intro i hi
      exact w.adj_getVert_succ hi
  set L := Nat.find hex_odd with hL_def
  have hL_spec : Odd L ∧ ∃ f : ℕ → V, f L = f 0 ∧ ∀ i < L, G.Adj (f i) (f (i + 1)) :=
    Nat.find_spec hex_odd
  have hL_min : ∀ L' < L, Odd L' → ¬ ∃ g : ℕ → V, g L' = g 0 ∧ ∀ i < L', G.Adj (g i) (g (i + 1)) :=
    fun L' hlt hodd => fun h => Nat.find_min hex_odd hlt ⟨hodd, h⟩
  obtain ⟨hL_odd, f, hf_loop, hf_adj⟩ := hL_spec
  have hL5 : 5 ≤ L := by
    obtain ⟨k, hk⟩ := hL_odd
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h01 := hf_adj 0 (by omega)
      rw [show (0 + 1 : ℕ) = L by omega, hf_loop] at h01
      exact G.loopless.irrefl _ h01
    have hk1 : k ≠ 1 := by
      rintro rfl
      have h01 := hf_adj 0 (by omega)
      have h12 := hf_adj 1 (by omega)
      have h23 := hf_adj 2 (by omega)
      rw [show (2 + 1 : ℕ) = L by omega, hf_loop] at h23
      exact not_adj_of_cliqueFree_three hTF h01 h12 h23.symm
    omega
  have hf_inj : ∀ i j, i < j → j < L → f i ≠ f j := by
    intro i j hij hjL heq
    by_cases hodd1 : Odd (j - i)
    · apply hL_min (j - i) (by omega) hodd1
      refine ⟨fun t => f (i + t), ?_, ?_⟩
      · dsimp only; rw [show i + (j - i) = j by omega, add_zero, heq.symm]
      · intro t ht
        dsimp only
        rw [show i + (t + 1) = (i + t) + 1 by omega]
        exact hf_adj (i + t) (by omega)
    · have hodd2 : Odd (L - (j - i)) := by
        obtain ⟨a, ha⟩ := hL_odd
        obtain ⟨b, hb⟩ := Nat.not_odd_iff_even.mp hodd1
        exact ⟨a - b, by omega⟩
      apply hL_min (L - (j - i)) (by omega) hodd2
      refine ⟨fun t => if t ≤ L - j then f (j + t) else f (t - (L - j)), ?_, ?_⟩
      · dsimp only
        by_cases hi0 : i = 0
        · subst hi0
          rw [if_pos (by omega), if_pos (by omega), show j + (L - (j - 0)) = L by omega, add_zero, hf_loop, heq]
        · rw [if_neg (by omega), if_pos (by omega), show L - (j - i) - (L - j) = i by omega, add_zero, heq]
      · intro t ht
        dsimp only
        by_cases ht1 : t + 1 ≤ L - j
        · rw [if_pos (by omega), if_pos ht1, show j + (t + 1) = (j + t) + 1 by omega]
          exact hf_adj (j + t) (by omega)
        · by_cases ht0 : t ≤ L - j
          · have hteq : t = L - j := by omega
            subst hteq
            rw [if_pos (le_refl _), if_neg (by omega), show j + (L - j) = L by omega, hf_loop,
              show L - j + 1 - (L - j) = 1 by omega]
            exact hf_adj 0 (by omega)
          · rw [if_neg ht0, if_neg ht1, show t + 1 - (L - j) = (t - (L - j)) + 1 by omega]
            exact hf_adj (t - (L - j)) (by omega)
  have hf_nochord : ∀ i j, i + 2 ≤ j → j < L → j - i ≤ L - 2 → ¬ G.Adj (f i) (f j) := by
    intro i j hij hjL hgap hadj
    by_cases heven1 : Even (j - i)
    · have hodd1 : Odd (j - i + 1) := by obtain ⟨b, hb⟩ := heven1; exact ⟨b, by omega⟩
      apply hL_min (j - i + 1) (by omega) hodd1
      refine ⟨fun t => if t ≤ j - i then f (i + t) else f i, ?_, ?_⟩
      · dsimp only
        rw [if_neg (by omega), if_pos (by omega), add_zero]
      · intro t ht
        dsimp only
        by_cases ht1 : t + 1 ≤ j - i
        · rw [if_pos (by omega), if_pos ht1, show i + (t + 1) = (i + t) + 1 by omega]
          exact hf_adj (i + t) (by omega)
        · have hteq : t = j - i := by omega
          subst hteq
          rw [if_pos (le_refl _), if_neg (by omega), show i + (j - i) = j by omega]
          exact hadj.symm
    · have heven2 : Even (L - (j - i)) := by
        obtain ⟨a, ha⟩ := hL_odd
        obtain ⟨b, hb⟩ := Nat.not_even_iff_odd.mp heven1
        exact ⟨a - b, by omega⟩
      have hodd2 : Odd (L - (j - i) + 1) := by obtain ⟨b, hb⟩ := heven2; exact ⟨b, by omega⟩
      apply hL_min (L - (j - i) + 1) (by omega) hodd2
      refine ⟨fun t => if t ≤ L - j then f (j + t) else if t ≤ L - (j - i) then f (t - (L - j)) else f j, ?_, ?_⟩
      · dsimp only
        rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), add_zero]
      · intro t ht
        dsimp only
        by_cases ht1 : t + 1 ≤ L - j
        · rw [if_pos (by omega), if_pos ht1, show j + (t + 1) = (j + t) + 1 by omega]
          exact hf_adj (j + t) (by omega)
        · by_cases ht0 : t ≤ L - j
          · have hteq : t = L - j := by omega
            subst hteq
            by_cases hi0 : i = 0
            · subst hi0
              rw [if_pos (le_refl _), if_neg (by omega), if_neg (by omega),
                show j + (L - j) = L by omega, hf_loop]
              exact hadj
            · rw [if_pos (le_refl _), if_neg (by omega), if_pos (by omega),
                show j + (L - j) = L by omega, hf_loop, show L - j + 1 - (L - j) = 1 by omega]
              exact hf_adj 0 (by omega)
          · by_cases ht2 : t + 1 ≤ L - (j - i)
            · rw [if_neg ht0, if_pos (by omega), if_neg ht1, if_pos ht2,
                show t + 1 - (L - j) = (t - (L - j)) + 1 by omega]
              exact hf_adj (t - (L - j)) (by omega)
            · have hteq : t = L - (j - i) := by omega
              subst hteq
              rw [if_neg ht0, if_pos (le_refl _), if_neg ht1, if_neg (by omega),
                show L - (j - i) - (L - j) = i by omega]
              exact hadj
  exact ⟨L, hL_odd, hL5, hL_min, f, hf_loop, hf_adj, hf_inj, hf_nochord⟩

lemma not_colorable_two_of_counterexample {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    ¬ G.Colorable 2 := by
  classical
  rintro ⟨col⟩
  let C0 : Set V := {v | col v = 0}
  let C1 : Set V := {v | col v = 1}
  have hC0 : G.IsIndepSet C0 := fun x hx y hy _ hxy => by
    have hne := col.valid hxy; exact hne (hx.trans hy.symm)
  have hC1 : G.IsIndepSet C1 := fun x hx y hy _ hxy => by
    have hne := col.valid hxy; exact hne (hx.trans hy.symm)
  have h50 := five_mul_indep_lt_two_mul_card G hTF hH C0 hC0
  have h51 := five_mul_indep_lt_two_mul_card G hTF hH C1 hC1
  have hsum : C0.ncard + C1.ncard = Fintype.card V := by
    rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    have hdisj : Disjoint C0.toFinset C1.toFinset := by
      rw [Finset.disjoint_left]
      intro v hv0 hv1
      have h0 : col v = 0 := by simpa [C0] using hv0
      have h1 : col v = 1 := by simpa [C1] using hv1
      have : (0 : Fin 2) = 1 := h0.symm.trans h1
      exact absurd this (by decide)
    rw [← Finset.card_union_of_disjoint hdisj]
    have hunion : C0.toFinset ∪ C1.toFinset = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Set.mem_toFinset, C0, C1, Finset.mem_univ, iff_true]
      change col v = 0 ∨ col v = 1
      cases hcv : col v with
      | mk val hlt =>
        have : val = 0 ∨ val = 1 := by omega
        rcases this with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    rw [hunion, Finset.card_univ]
  have hpos := six_le_card G hTF hH
  omega

lemma exists_shortest_odd_walk {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    ∃ L : ℕ, Odd L ∧ 5 ≤ L ∧
      (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → V, g L' = g 0 ∧ ∀ i < L', G.Adj (g i) (g (i + 1))) ∧
      ∃ f : ℕ → V, f L = f 0 ∧ (∀ i < L, G.Adj (f i) (f (i + 1))) ∧
        (∀ i j, i < j → j < L → f i ≠ f j) ∧
        (∀ i j, i + 2 ≤ j → j < L → j - i ≤ L - 2 → ¬ G.Adj (f i) (f j)) :=
  exists_shortest_odd_walk_of_nonbip G hTF (not_colorable_two_of_counterexample G hTF hH)

lemma shortest_odd_walk_deg_le_two {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) {L : ℕ} (hL_odd : Odd L) (hL5 : 5 ≤ L)
    (hL_min : ∀ L' < L, Odd L' → ¬ ∃ g : ℕ → V, g L' = g 0 ∧ ∀ i < L', G.Adj (g i) (g (i + 1)))
    {f : ℕ → V} (hf_loop : f L = f 0) (hf_adj : ∀ i < L, G.Adj (f i) (f (i + 1)))
    (w : V) :
    #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ 2 := by
  by_contra hgt
  have hge3 : 3 ≤ #((Finset.range L).filter (fun i => G.Adj w (f i))) := by omega
  obtain ⟨T, hTsub, hT3⟩ := Finset.exists_subset_card_eq hge3
  obtain ⟨a0, b0, c0, hab0, hac0, hbc0, rfl⟩ := Finset.card_eq_three.mp hT3
  -- Sort {a0, b0, c0} into i < j < k < L
  have hsort : ∃ i j k : ℕ, i < j ∧ j < k ∧ k < L ∧ G.Adj w (f i) ∧ G.Adj w (f j) ∧ G.Adj w (f k) := by
    have ha := Finset.mem_filter.mp (hTsub (by simp : a0 ∈ ({a0, b0, c0} : Finset ℕ)))
    have hb := Finset.mem_filter.mp (hTsub (by simp : b0 ∈ ({a0, b0, c0} : Finset ℕ)))
    have hc := Finset.mem_filter.mp (hTsub (by simp : c0 ∈ ({a0, b0, c0} : Finset ℕ)))
    have haL := Finset.mem_range.mp ha.1
    have hbL := Finset.mem_range.mp hb.1
    have hcL := Finset.mem_range.mp hc.1
    rcases lt_or_gt_of_ne hab0 with hab | hba <;>
    rcases lt_or_gt_of_ne hbc0 with hbc | hcb <;>
    rcases lt_or_gt_of_ne hac0 with hac | hca
    · exact ⟨a0, b0, c0, hab, hbc, hcL, ha.2, hb.2, hc.2⟩
    · omega
    · exact ⟨a0, c0, b0, hac, hcb, hbL, ha.2, hc.2, hb.2⟩
    · exact ⟨c0, a0, b0, hca, hab, hbL, hc.2, ha.2, hb.2⟩
    · exact ⟨b0, a0, c0, hba, hac, hcL, hb.2, ha.2, hc.2⟩
    · exact ⟨b0, c0, a0, hbc, hca, haL, hb.2, hc.2, ha.2⟩
    · omega
    · exact ⟨c0, b0, a0, hcb, hba, haL, hc.2, hb.2, ha.2⟩
  obtain ⟨i, j, k, hij, hjk, hkL, hwi, hwj, hwk⟩ := hsort
  -- No two of i, j, k can be adjacent on the cycle (triangle-free)
  have hd1 : 2 ≤ j - i := by
    by_contra h1
    have hj_eq : j = i + 1 := by omega
    rw [hj_eq] at hwj
    exact not_adj_of_cliqueFree_three hTF hwi (hf_adj i (by omega)) hwj
  have hd2 : 2 ≤ k - j := by
    by_contra h2
    have hk_eq : k = j + 1 := by omega
    rw [hk_eq] at hwk
    exact not_adj_of_cliqueFree_three hTF hwj (hf_adj j (by omega)) hwk
  have hd3 : 2 ≤ L - (k - i) := by
    by_contra h3
    have hki : k = L - 1 ∧ i = 0 := by omega
    have hk_adj : G.Adj (f k) (f 0) := by
      have := hf_adj k (by omega)
      rwa [show k + 1 = L by omega, hf_loop] at this
    rw [hki.2] at hwi
    exact not_adj_of_cliqueFree_three hTF hwk hk_adj hwi
  -- Helper: an odd arc from p to q (with p < q < L, q - p + 2 < L) gives a shorter odd closed walk via w
  have harc_short : ∀ p q : ℕ, p < q → q < L → Odd (q - p) → q - p + 2 < L →
      G.Adj w (f p) → G.Adj w (f q) → False := by
    intro p q hpq hqL hodd hshort hwp hwq
    have hodd2 : Odd (q - p + 2) := by obtain ⟨t, ht⟩ := hodd; exact ⟨t + 1, by omega⟩
    apply hL_min (q - p + 2) hshort hodd2
    refine ⟨fun t => if t = 0 then w else if t ≤ q - p + 1 then f (p + (t - 1)) else w, ?_, ?_⟩
    · dsimp only
      rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    · intro t ht
      dsimp only
      by_cases ht0 : t = 0
      · subst ht0
        rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
        simpa using hwp
      · by_cases ht1 : t + 1 ≤ q - p + 1
        · rw [if_neg ht0, if_pos (by omega), if_neg (by omega), if_pos ht1,
            show p + (t + 1 - 1) = (p + (t - 1)) + 1 by omega]
          exact hf_adj (p + (t - 1)) (by omega)
        · have hteq : t = q - p + 1 := by omega
          subst hteq
          rw [if_neg ht0, if_pos (le_refl _), if_neg (by omega), if_neg (by omega),
            show p + (q - p + 1 - 1) = q by omega]
          exact hwq.symm
  -- Since (j - i) + (k - j) + (L - (k - i)) = L is odd, at least one of the three arcs is odd!
  by_cases ho1 : Odd (j - i)
  · exact harc_short i j hij (by omega) ho1 (by omega) hwi hwj
  · by_cases ho2 : Odd (k - j)
    · exact harc_short j k hjk hkL ho2 (by omega) hwj hwk
    · -- Third arc L - (k - i) must be odd, length d3 + 2 <= L - 2 < L
      have ho3 : Odd (L - (k - i) + 2) := by
        obtain ⟨a, ha⟩ := hL_odd
        obtain ⟨b, hb⟩ := Nat.not_odd_iff_even.mp ho1
        obtain ⟨c, hc⟩ := Nat.not_odd_iff_even.mp ho2
        exact ⟨a - b - c + 1, by omega⟩
      apply hL_min (L - (k - i) + 2) (by omega) ho3
      refine ⟨fun t =>
        if t = 0 then w
        else if t ≤ L - k + 1 then f (k + (t - 1))
        else if t ≤ L - (k - i) + 1 then f (t - (L - k + 1))
        else w, ?_, ?_⟩
      · dsimp only
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
      · intro t ht
        dsimp only
        by_cases ht0 : t = 0
        · subst ht0
          rw [if_pos rfl, if_neg (by omega), if_pos (by omega)]
          simpa using hwk
        · by_cases ht1 : t + 1 ≤ L - k + 1
          · rw [if_neg ht0, if_pos (by omega), if_neg (by omega), if_pos ht1,
              show k + (t + 1 - 1) = (k + (t - 1)) + 1 by omega]
            exact hf_adj (k + (t - 1)) (by omega)
          · by_cases ht2 : t ≤ L - k + 1
            · have hteq : t = L - k + 1 := by omega
              subst hteq
              by_cases hi0 : i = 0
              · subst hi0
                rw [if_neg ht0, if_pos (le_refl _), if_neg (by omega), if_neg (by omega),
                  if_neg (by omega), show k + (L - k + 1 - 1) = L by omega, hf_loop]
                exact hwi.symm
              · rw [if_neg ht0, if_pos (le_refl _), if_neg (by omega), if_neg (by omega),
                  if_pos (by omega), show k + (L - k + 1 - 1) = L by omega, hf_loop,
                  show L - k + 1 + 1 - (L - k + 1) = 1 by omega]
                exact hf_adj 0 (by omega)
            · by_cases ht3 : t + 1 ≤ L - (k - i) + 1
              · rw [if_neg ht0, if_neg ht2, if_pos (by omega), if_neg (by omega), if_neg ht1, if_pos ht3,
                  show t + 1 - (L - k + 1) = (t - (L - k + 1)) + 1 by omega]
                exact hf_adj (t - (L - k + 1)) (by omega)
              · have hteq : t = L - (k - i) + 1 := by omega
                subst hteq
                rw [if_neg ht0, if_neg ht2, if_pos (le_refl _), if_neg (by omega), if_neg ht1, if_neg (by omega),
                  show L - (k - i) + 1 - (L - k + 1) = i by omega]
                exact hwi.symm

set_option maxHeartbeats 600000 in

lemma sq_sum_le_card_mul_sum_sq_int {m : ℕ} (a : Fin m → ℤ) :
    (∑ i : Fin m, a i) ^ 2 ≤ (m : ℤ) * ∑ i : Fin m, (a i) ^ 2 := by
  have hnonneg : (0 : ℤ) ≤ ∑ i : Fin m, ∑ j : Fin m, (a i - a j) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hexp : ∑ i : Fin m, ∑ j : Fin m, (a i - a j) ^ 2 =
      2 * (m : ℤ) * (∑ i : Fin m, (a i) ^ 2) - 2 * (∑ i : Fin m, a i) ^ 2 := by
    have hsub : ∀ i : Fin m, ∑ j : Fin m, (a i - a j) ^ 2 =
        (m : ℤ) * (a i) ^ 2 - 2 * a i * (∑ j : Fin m, a j) + ∑ j : Fin m, (a j) ^ 2 := by
      intro i
      have hstep : ∀ j : Fin m, (a i - a j) ^ 2 = (a i) ^ 2 - 2 * a i * a j + (a j) ^ 2 := fun _ => by ring
      simp_rw [hstep]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    simp_rw [hsub]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmul2 : ∑ i : Fin m, 2 * a i = 2 * ∑ i : Fin m, a i := (Finset.mul_sum _ _ _).symm
    rw [hmul2]; ring
  linarith

lemma int_eq_of_dvd_sub {n a b : ℤ} (hn : 0 < n) (hdvd : n ∣ (a - b))
    (h1 : a - b < n) (h2 : b - a < n) : a = b := by
  obtain ⟨q, hq⟩ := hdvd
  have hq0 : q = 0 := by nlinarith only [hn, hq, h1, h2]
  rw [hq0, mul_zero] at hq; omega

lemma int_eq_of_emod_eq {n x y : ℤ} (hn : 0 < n) (hmod : x % n = y % n)
    (h1 : x - y < n) (h2 : y - x < n) : x = y :=
  int_eq_of_dvd_sub hn (Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hmod, sub_self, Int.zero_emod])) h1 h2

lemma exists_sorted_equiv {V : Type} [Fintype V] (key : V → ℕ) :
    ∃ e : Fin (Fintype.card V) ≃ V, ∀ i j : Fin (Fintype.card V), i ≤ j → key (e i) ≤ key (e j) := by
  classical
  let L := (Finset.univ : Finset V).toList.mergeSort (fun a b => decide (key a ≤ key b))
  have hperm : L.Perm (Finset.univ : Finset V).toList := List.mergeSort_perm _ _
  have hlen : L.length = Fintype.card V := by
    rw [hperm.length_eq, Finset.length_toList, Finset.card_univ]
  have hnodup : L.Nodup := hperm.nodup_iff.mpr (Finset.nodup_toList _)
  have hpair : L.Pairwise (fun a b => key a ≤ key b) := by
    have h := List.pairwise_mergeSort (le := fun a b => decide (key a ≤ key b))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
      (by intro a b; rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]; omega)
      (Finset.univ : Finset V).toList
    exact h.imp (fun {a b} hab => by simpa only [decide_eq_true_eq] using hab)
  let fn : Fin (Fintype.card V) → V := fun i => L[i.val]'(by omega)
  have hbij : Function.Bijective fn := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hget : L[i.val]'(by omega) = L[j.val]'(by omega) := hij
      have hidx := (List.Nodup.getElem_inj_iff hnodup).mp hget
      exact Fin.ext hidx
    · intro x
      have hxmem : x ∈ L := hperm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ x))
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hxmem
      exact ⟨⟨idx, by omega⟩, rfl⟩
  refine ⟨Equiv.ofBijective fn hbij, ?_⟩
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · exact (List.pairwise_iff_getElem.mp hpair) i.val j.val (by omega) (by omega) hlt

lemma andrasfai_corner_orbit_contra
    {n k eF : ℕ} (hn2 : 2 ≤ n) (hk1 : 1 ≤ k) (h2k : 2 * k ≤ n)
    (h5e : 5 * eF < n ^ 2)
    (f : ℤ → ℤ)
    (hf_per : ∀ x : ℤ, f (x + n) = f x + n)
    (hf_gt : ∀ x : ℤ, x < f x)
    (hf_le : ∀ x : ℤ, f x ≤ x + k - 1)
    (hE_bound : 2 * (∑ i : Fin n, ((i.val : ℤ) + k - f i.val)) + (n : ℤ) ≤ 2 * (eF : ℤ))
    (hArc_gt : ∀ t : ℤ, ∀ h_t : ℤ, t < h_t →
      (∀ x : ℤ, t ≤ x → x < h_t → f x < t + k) → t + k ≤ f h_t →
      (n : ℤ) ^ 2 < 50 * ∑ j ∈ Finset.range (h_t - t).toNat, (t + k - f (t + (j : ℤ)))) :
    False := by
  have hn_pos_z : (0 : ℤ) < (n : ℤ) := by omega
  let g : ℤ → ℤ := fun x => x + k - f x
  have hg_per : ∀ x : ℤ, g (x + n) = g x := by intro x; dsimp only [g]; rw [hf_per]; ring
  have hex_h : ∀ t : ℤ, ∃ j : ℕ, t + k ≤ f (t + (j : ℤ)) := fun t => ⟨k, by have := hf_gt (t + k); omega⟩
  let h : ℤ → ℤ := fun t => t + (Nat.find (hex_h t) : ℤ)
  have hh_spec : ∀ t : ℤ, t + k ≤ f (h t) := fun t => Nat.find_spec (hex_h t)
  have hh_min : ∀ t x : ℤ, t ≤ x → x < h t → f x < t + k := by
    intro t x htx hxh
    have hlt_find : (x - t).toNat < Nat.find (hex_h t) := by dsimp only [h] at hxh; omega
    have hnot := Nat.find_min (hex_h t) hlt_find
    rw [show t + ((x - t).toNat : ℤ) = x by omega] at hnot; omega
  have hh_gt : ∀ t : ℤ, t < h t := by
    intro t
    have h0 : ¬ (t + k ≤ f (t + (0 : ℕ))) := by simp only [Nat.cast_zero, add_zero]; have := hf_le t; omega
    have hpos : 0 < Nat.find (hex_h t) := Nat.pos_of_ne_zero (fun hz => h0 (hz ▸ Nat.find_spec (hex_h t)))
    dsimp only [h]; omega
  let iter : ℕ → ℤ := fun j => Nat.iterate h j 0
  have hiter_succ : ∀ j : ℕ, iter (j + 1) = h (iter j) := fun j => Function.iterate_succ_apply' h j 0
  have hiter_mono : ∀ a b : ℕ, a < b → iter a < iter b := by
    intro a b hab
    induction b with
    | zero => omega
    | succ b ih =>
      rw [hiter_succ]
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hab) with rfl | hlt
      · exact hh_gt _
      · exact (ih hlt).trans (hh_gt _)
  let modFn : Fin (n + 1) → Fin n := fun j =>
    ⟨(iter j.val % (n : ℤ)).toNat, by
      have := Int.emod_nonneg (iter j.val) (by omega : (n : ℤ) ≠ 0)
      have := Int.emod_lt_of_pos (iter j.val) hn_pos_z; omega⟩
  have hnot_inj : ¬ Function.Injective modFn := by
    intro hinj; have hcard := Fintype.card_le_of_injective modFn hinj; simp at hcard
  rw [Function.Injective] at hnot_inj; push Not at hnot_inj
  obtain ⟨j₁, j₂, hmod_eq, hjne⟩ := hnot_inj
  have hex_ab : ∃ a b : ℕ, a < b ∧ iter a % (n : ℤ) = iter b % (n : ℤ) := by
    have heq_m : iter j₁.val % (n : ℤ) = iter j₂.val % (n : ℤ) := by
      have h1 := congrArg Fin.val hmod_eq
      have h2 := Int.emod_nonneg (iter j₁.val) (by omega : (n : ℤ) ≠ 0)
      have h3 := Int.emod_nonneg (iter j₂.val) (by omega : (n : ℤ) ≠ 0)
      dsimp only [modFn] at h1; omega
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjne) with hlt | hgt
    · exact ⟨j₁.val, j₂.val, hlt, heq_m⟩
    · exact ⟨j₂.val, j₁.val, hgt, heq_m.symm⟩
  obtain ⟨a, b, hab, hmod_ab⟩ := hex_ab
  set m := b - a
  have hm1 : 1 ≤ m := by omega
  let s : ℕ → ℤ := fun r => iter (a + r)
  have hs_succ : ∀ r : ℕ, s (r + 1) = h (s r) := fun r => by
    dsimp only [s]; rw [show a + (r + 1) = (a + r) + 1 by omega, hiter_succ]
  have hs_diff_pos : ∀ r : ℕ, 1 ≤ s (r + 1) - s r := fun r => by rw [hs_succ]; have := hh_gt (s r); omega
  have hdvd_sm : (n : ℤ) ∣ (s m - s 0) := by
    have hsm : s m = iter b := by dsimp only [s]; congr 1; omega
    have hs0 : s 0 = iter a := by simp [s]
    rw [hsm, hs0]
    exact Int.dvd_of_emod_eq_zero (by rw [Int.sub_emod, hmod_ab, sub_self, Int.zero_emod])
  obtain ⟨p, hp_eq⟩ := hdvd_sm
  have hp_pos : (1 : ℤ) ≤ p := by
    have hsm_gt : s 0 < s m := by
      have h1 : s m = iter b := by dsimp only [s]; congr 1; omega
      have h2 : s 0 = iter a := by simp [s]
      rw [h1, h2]; exact hiter_mono a b hab
    nlinarith only [hp_eq, hsm_gt, hn_pos_z]
  let Δ : Fin m → ℤ := fun r => s (r.val + 1) - s r.val
  have hΔ_sum : ∑ r : Fin m, Δ r = p * (n : ℤ) := by
    have htele : ∀ l : ℕ, ∑ r ∈ Finset.range l, (s (r + 1) - s r) = s l - s 0 := by
      intro l; induction l with | zero => simp | succ l ih => rw [Finset.sum_range_succ, ih]; ring
    rw [Fin.sum_univ_eq_sum_range (fun r => s (r + 1) - s r), htele m, hp_eq]; ring
  let eA : Fin m → ℤ := fun r =>
    ∑ j ∈ Finset.range (Δ r).toNat, (s r.val + k - f (s r.val + (j : ℤ)))
  have heA_gt : ∀ r : Fin m, (n : ℤ) ^ 2 < 50 * eA r := by
    intro r
    have hΔ_eq : h (s r.val) - s r.val = Δ r := by dsimp only [Δ]; rw [hs_succ]
    have h1 := hArc_gt (s r.val) (h (s r.val)) (hh_gt _) (hh_min _) (hh_spec _)
    rwa [hΔ_eq] at h1
  have htele_eA : 2 * (∑ r : Fin m, eA r) =
      p * (2 * (∑ i : Fin n, g i.val) + (n : ℤ)) - ∑ r : Fin m, (Δ r) ^ 2 := by
    have hper_r : ∀ r : Fin m, 2 * eA r =
        2 * (∑ j ∈ Finset.range (Δ r).toNat, g (s r.val + (j : ℤ))) - (Δ r) * (Δ r - 1) := by
      intro r
      dsimp only [eA]
      have hsplit : ∀ j ∈ Finset.range (Δ r).toNat,
          s r.val + k - f (s r.val + (j : ℤ)) = g (s r.val + (j : ℤ)) - (j : ℤ) := fun _ _ => by dsimp only [g]; ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, mul_sub]
      congr 1
      have hsum_j : 2 * ∑ j ∈ Finset.range (Δ r).toNat, (j : ℤ) =
          ((Δ r).toNat : ℤ) * (((Δ r).toNat : ℤ) - 1) := by
        have hnat : 2 * ∑ j ∈ Finset.range (Δ r).toNat, j = (Δ r).toNat * ((Δ r).toNat - 1) := by
          have := Finset.sum_range_id (Δ r).toNat
          have hmul := congrArg (2 * ·) this
          have hdiv : 2 * ((Δ r).toNat * ((Δ r).toNat - 1) / 2) = (Δ r).toNat * ((Δ r).toNat - 1) :=
            Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd
          linarith only [hmul, hdiv]
        have hcast : ((2 * ∑ j ∈ Finset.range (Δ r).toNat, j : ℕ) : ℤ) =
            (((Δ r).toNat * ((Δ r).toNat - 1) : ℕ) : ℤ) := congrArg (Nat.cast : ℕ → ℤ) hnat
        push_cast at hcast
        have hposΔ := hs_diff_pos r.val
        have hsub1 : (((Δ r).toNat - 1 : ℕ) : ℤ) = ((Δ r).toNat : ℤ) - 1 := by dsimp only [Δ]; omega
        rw [hsub1] at hcast; exact hcast
      have hposΔ := hs_diff_pos r.val
      have htoNat : ((Δ r).toNat : ℤ) = Δ r := by dsimp only [Δ]; omega
      rw [hsum_j, htoNat]
    have hsum_r : 2 * ∑ r : Fin m, eA r =
        2 * (∑ r : Fin m, ∑ j ∈ Finset.range (Δ r).toNat, g (s r.val + (j : ℤ))) -
        ∑ r : Fin m, (Δ r) * (Δ r - 1) := by
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun r _ => hper_r r), Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hcont : ∑ r : Fin m, ∑ j ∈ Finset.range (Δ r).toNat, g (s r.val + (j : ℤ)) =
        ∑ x ∈ Finset.range (p.toNat * n), g (s 0 + (x : ℤ)) := by
      have hgen : ∀ l : ℕ, l ≤ m →
          ∑ r ∈ Finset.range l, ∑ j ∈ Finset.range (s (r + 1) - s r).toNat, g (s r + (j : ℤ)) =
          ∑ x ∈ Finset.range (s l - s 0).toNat, g (s 0 + (x : ℤ)) := by
        intro l _; induction l with
        | zero => simp
        | succ l ih =>
          rw [Finset.sum_range_succ, ih (by omega)]
          have hpos_l : 0 ≤ s l - s 0 := by
            clear ih; induction l with | zero => simp | succ l' ih' => have := hs_diff_pos l'; omega
          have hpos_step := hs_diff_pos l
          have hadd_len : (s (l + 1) - s 0).toNat = (s l - s 0).toNat + (s (l + 1) - s l).toNat := by omega
          rw [hadd_len, Finset.sum_range_add]; congr 1
          apply Finset.sum_congr rfl; intro j _; congr 1; omega
      have h1 := hgen m (le_refl m)
      rw [← Fin.sum_univ_eq_sum_range (fun r => ∑ j ∈ Finset.range (s (r + 1) - s r).toNat, g (s r + (j : ℤ)))] at h1
      have hlen_pm : (s m - s 0).toNat = p.toNat * n := by
        rw [hp_eq]
        have heq : (n : ℤ) * p = ((p.toNat * n : ℕ) : ℤ) := by
          push_cast; rw [Int.toNat_of_nonneg (by omega)]; ring
        rw [heq, Int.toNat_natCast]
      rw [hlen_pm] at h1; exact h1
    have hper_block : ∀ q : ℕ, ∑ x ∈ Finset.range (q * n), g (s 0 + (x : ℤ)) =
        (q : ℤ) * ∑ i : Fin n, g i.val := by
      intro q
      have h1block : ∀ y : ℤ, ∑ x ∈ Finset.range n, g (y + (x : ℤ)) = ∑ i : Fin n, g i.val := by
        intro y
        have hstep : ∀ x : ℕ, g (y + (x : ℤ)) = g ((y + (x : ℤ)) % (n : ℤ)) := by
          intro x
          have hdiv := Int.mul_ediv_add_emod (y + (x : ℤ)) (n : ℤ)
          have hg_mul : ∀ t c : ℤ, g (t + c * (n : ℤ)) = g t := by
            intro t c
            induction c using Int.induction_on with
            | zero => simp
            | succ c ih => rw [show t + (↑c + 1) * (n : ℤ) = (t + ↑c * (n : ℤ)) + n by ring, hg_per, ih]
            | pred c ih =>
              have hback : g (t + (-(↑c : ℤ) - 1) * (n : ℤ)) = g ((t + (-(↑c : ℤ) - 1) * (n : ℤ)) + n) := (hg_per _).symm
              rw [hback, show t + (-(↑c : ℤ) - 1) * (n : ℤ) + n = t + (-(↑c : ℤ)) * (n : ℤ) by ring]; exact ih
          have heq : y + (x : ℤ) = (y + (x : ℤ)) % (n : ℤ) + ((y + (x : ℤ)) / (n : ℤ)) * (n : ℤ) := by linarith
          conv_lhs => rw [heq]; exact hg_mul _ _
        rw [← Fin.sum_univ_eq_sum_range (fun x => g (y + (x : ℤ)))]
        let sh : Fin n ≃ Fin n :=
          { toFun := fun x => ⟨((y + (x.val : ℤ)) % (n : ℤ)).toNat, by
              have := Int.emod_nonneg (y + x.val) (by omega : (n : ℤ) ≠ 0)
              have := Int.emod_lt_of_pos (y + x.val) hn_pos_z; omega⟩
            invFun := fun z => ⟨(((z.val : ℤ) - y) % (n : ℤ)).toNat, by
              have := Int.emod_nonneg ((z.val : ℤ) - y) (by omega : (n : ℤ) ≠ 0)
              have := Int.emod_lt_of_pos ((z.val : ℤ) - y) hn_pos_z; omega⟩
            left_inv := fun x => Fin.ext (by
              dsimp only
              have hx := x.isLt
              have h1 := Int.emod_nonneg (y + x.val) (by omega : (n : ℤ) ≠ 0)
              have h3 : ((((y + (x.val : ℤ)) % (n : ℤ)).toNat : ℤ) - y) % (n : ℤ) = (x.val : ℤ) := by
                rw [show (((y + (x.val : ℤ)) % (n : ℤ)).toNat : ℤ) = (y + (x.val : ℤ)) % (n : ℤ) by omega,
                  Int.sub_emod, Int.emod_emod, ← Int.sub_emod, add_sub_cancel_left,
                  Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)]
              rw [h3, Int.toNat_natCast])
            right_inv := fun z => Fin.ext (by
              dsimp only
              have hz := z.isLt
              have h1 := Int.emod_nonneg ((z.val : ℤ) - y) (by omega : (n : ℤ) ≠ 0)
              have h3 : (y + ((((z.val : ℤ) - y) % (n : ℤ)).toNat : ℤ)) % (n : ℤ) = (z.val : ℤ) := by
                rw [show ((((z.val : ℤ) - y) % (n : ℤ)).toNat : ℤ) = ((z.val : ℤ) - y) % (n : ℤ) by omega,
                  Int.add_emod, Int.emod_emod, ← Int.add_emod, add_sub_cancel,
                  Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)]
              rw [h3, Int.toNat_natCast]) }
        refine Fintype.sum_equiv sh _ _ (fun x => ?_)
        rw [hstep x.val]; congr 1
        show (y + (x.val : ℤ)) % (n : ℤ) = (((y + (x.val : ℤ)) % (n : ℤ)).toNat : ℤ)
        have := Int.emod_nonneg (y + x.val) (by omega : (n : ℤ) ≠ 0); omega
      induction q with
      | zero => simp
      | succ q ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih]
        have htail : ∑ x ∈ Finset.range n, g (s 0 + ((q * n + x : ℕ) : ℤ)) = ∑ i : Fin n, g i.val := by
          have : ∀ x : ℕ, s 0 + ((q * n + x : ℕ) : ℤ) = (s 0 + (q * n : ℕ)) + (x : ℤ) := fun _ => by push_cast; ring
          simp_rw [this]; exact h1block _
        rw [htail]; push_cast; ring
    rw [hsum_r, hcont, hper_block p.toNat]
    have hp_toNat : (p.toNat : ℤ) = p := by omega
    rw [hp_toNat]
    have hΔ_expand : ∑ r : Fin m, (Δ r) * (Δ r - 1) = (∑ r : Fin m, (Δ r) ^ 2) - p * (n : ℤ) := by
      have h1 : ∀ r : Fin m, (Δ r) * (Δ r - 1) = (Δ r) ^ 2 - Δ r := fun _ => by ring
      simp_rw [h1]; rw [Finset.sum_sub_distrib, hΔ_sum]
    rw [hΔ_expand]; ring
  set S_eA : ℤ := ∑ r : Fin m, eA r
  set eFz : ℤ := (eF : ℤ)
  have h1 : 2 * S_eA ≤ 2 * p * eFz - ∑ r : Fin m, (Δ r) ^ 2 := by
    have hmul : p * (2 * (∑ i : Fin n, g i.val) + (n : ℤ)) ≤ p * (2 * eFz) :=
      mul_le_mul_of_nonneg_left hE_bound (by omega)
    dsimp only [S_eA]; linarith only [htele_eA, hmul]
  have hcs : (p * (n : ℤ)) ^ 2 ≤ (m : ℤ) * ∑ r : Fin m, (Δ r) ^ 2 := by
    rw [← hΔ_sum]; exact sq_sum_le_card_mul_sum_sq_int Δ
  have h2 : 2 * (m : ℤ) * S_eA ≤ 2 * (m : ℤ) * p * eFz - (p * (n : ℤ)) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg m)
    linarith only [hmul, hcs]
  have h3 : 2 * (m : ℤ) * (n : ℤ) ^ 2 * S_eA ≤ (m : ℤ) ^ 2 * eFz ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left h2 (sq_nonneg (n : ℤ))
    have hsq : (m : ℤ) ^ 2 * eFz ^ 2 - (n : ℤ) ^ 2 * (2 * (m : ℤ) * p * eFz - (p * (n : ℤ)) ^ 2) =
        (p * (n : ℤ) ^ 2 - (m : ℤ) * eFz) ^ 2 := by ring
    have hsq0 : (0 : ℤ) ≤ (p * (n : ℤ) ^ 2 - (m : ℤ) * eFz) ^ 2 := sq_nonneg _
    linarith only [hmul, hsq, hsq0]
  have h4 : 50 * (n : ℤ) ^ 2 * S_eA < (m : ℤ) * (n : ℤ) ^ 4 := by
    have h5e_z : 5 * eFz < (n : ℤ) ^ 2 := by dsimp only [eFz]; exact_mod_cast h5e
    have heF_nn : (0 : ℤ) ≤ eFz := Int.natCast_nonneg _
    have h5e_sq : (5 * eFz) ^ 2 < ((n : ℤ) ^ 2) ^ 2 := by nlinarith only [h5e_z, heF_nn]
    have hm_pos : (0 : ℤ) < (m : ℤ) := by omega
    have hmul50 : (m : ℤ) * (50 * (n : ℤ) ^ 2 * S_eA) < (m : ℤ) * ((m : ℤ) * (n : ℤ) ^ 4) := by
      have hL : (m : ℤ) * (50 * (n : ℤ) ^ 2 * S_eA) = 25 * (2 * (m : ℤ) * (n : ℤ) ^ 2 * S_eA) := by ring
      have hR : 25 * ((m : ℤ) ^ 2 * eFz ^ 2) = (m : ℤ) ^ 2 * (5 * eFz) ^ 2 := by ring
      have hm2 : (0 : ℤ) < (m : ℤ) ^ 2 := sq_pos_of_pos hm_pos
      have hlt := mul_lt_mul_of_pos_left h5e_sq hm2
      have hR2 : (m : ℤ) ^ 2 * ((n : ℤ) ^ 2) ^ 2 = (m : ℤ) * ((m : ℤ) * (n : ℤ) ^ 4) := by ring
      linarith only [h3, hL, hR, hlt, hR2]
    exact lt_of_mul_lt_mul_left hmul50 hm_pos.le
  have hsum_gt : (m : ℤ) * (n : ℤ) ^ 2 < 50 * S_eA := by
    have hne : (Finset.univ : Finset (Fin m)).Nonempty := by rw [Finset.univ_nonempty_iff]; exact ⟨⟨0, by omega⟩⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun r _ => heA_gt r)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hlt
    exact hlt
  have hcontra : (m : ℤ) * (n : ℤ) ^ 4 < 50 * (n : ℤ) ^ 2 * S_eA := by
    have hn2_pos : (0 : ℤ) < (n : ℤ) ^ 2 := sq_pos_of_pos hn_pos_z
    have hmul := mul_lt_mul_of_pos_left hsum_gt hn2_pos
    have hL : (n : ℤ) ^ 2 * ((m : ℤ) * (n : ℤ) ^ 2) = (m : ℤ) * (n : ℤ) ^ 4 := by ring
    have hR : (n : ℤ) ^ 2 * (50 * S_eA) = 50 * (n : ℤ) ^ 2 * S_eA := by ring
    linarith only [hmul, hL, hR]
  linarith only [h4, hcontra]

theorem not_hom_andrasfai {V : Type} [Fintype V] (G : SimpleGraph V)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (h5e_rule : ∀ H : SimpleGraph V, H.CliqueFree 3 →
      (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
        50 * (H.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
      5 * H.edgeSet.ncard < Fintype.card V ^ 2)
    (d : ℕ) (hd : 1 ≤ d) (φ : V → Fin (3 * d - 1))
    (hφ : ∀ u v : V, G.Adj u v →
      d ≤ ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) ∧
      ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) < 2 * d) :
    False := by
  classical
  let N := 3 * d - 1
  set n := Fintype.card V
  set k := n / 2
  have hN2 : 2 ≤ N := by omega
  -- If n <= 1, V' = ∅ contradicts hH
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have h0 := hH (∅ : Set V) (by simp; omega)
    have hemp : (G.induce (∅ : Set V)).edgeSet.ncard = 0 := by
      have h1 := two_mul_induce_edgeSet_ncard G (∅ : Finset V)
      rw [Finset.coe_empty, Finset.sum_empty] at h1; omega
    omega
  have hk1 : 1 ≤ k := by omega
  -- Step 1: Pass to the complete And(d)-blowup Gfull >= G
  let adjFull : V → V → Prop := fun u v =>
    d ≤ ((φ v).val + N - (φ u).val) % N ∧ ((φ v).val + N - (φ u).val) % N < 2 * d
  have hadj_symm : ∀ u v : V, adjFull u v → adjFull v u := by
    intro u v ⟨hlo, hhi⟩
    have hu : (φ u).val < N := (φ u).isLt
    have hv : (φ v).val < N := (φ v).isLt
    dsimp only [adjFull]
    by_cases hle : (φ u).val ≤ (φ v).val
    · have h1 : ((φ v).val + N - (φ u).val) % N = (φ v).val - (φ u).val := by
        rw [show (φ v).val + N - (φ u).val = ((φ v).val - (φ u).val) + N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h2 : ((φ u).val + N - (φ v).val) % N = N - ((φ v).val - (φ u).val) := by
        rw [show (φ u).val + N - (φ v).val = N - ((φ v).val - (φ u).val) by omega,
          Nat.mod_eq_of_lt (by omega)]
      omega
    · have h1 : ((φ v).val + N - (φ u).val) % N = (φ v).val + N - (φ u).val :=
        Nat.mod_eq_of_lt (by omega)
      have h2 : ((φ u).val + N - (φ v).val) % N = (φ u).val - (φ v).val := by
        rw [show (φ u).val + N - (φ v).val = ((φ u).val - (φ v).val) + N by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
  have hadj_irrefl : ∀ u : V, ¬ adjFull u u := by
    intro u ⟨hlo, _⟩
    have hu : (φ u).val < N := (φ u).isLt
    have h0 : ((φ u).val + N - (φ u).val) % N = 0 := by
      rw [show (φ u).val + N - (φ u).val = N by omega, Nat.mod_self]
    omega
  let Gfull : SimpleGraph V :=
    { Adj := adjFull
      symm := ⟨fun _ _ h => hadj_symm _ _ h⟩
      loopless := ⟨hadj_irrefl⟩ }
  have hGGfull : ∀ u v : V, G.Adj u v → Gfull.Adj u v := by
    intro u v h; exact hφ u v h
  have hGfull_TF : Gfull.CliqueFree 3 := by
    intro s hs
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
    have h1 : Gfull.Adj a b := hs.1 (by simp) (by simp) hab
    have h2 : Gfull.Adj b c := hs.1 (by simp) (by simp) hbc
    have h3 : Gfull.Adj c a := hs.1 (by simp) (by simp) hac.symm
    have ha := (φ a).isLt; have hb := (φ b).isLt; have hc := (φ c).isLt
    set x := ((φ b).val + N - (φ a).val) % N
    set y := ((φ c).val + N - (φ b).val) % N
    set z := ((φ a).val + N - (φ c).val) % N
    have hmod : (x + y + z) % N = 0 := by
      have hsum : ((φ b).val + N - (φ a).val) + ((φ c).val + N - (φ b).val) +
          ((φ a).val + N - (φ c).val) = 3 * N := by omega
      have h1' : (x + y + z) % N =
          (((φ b).val + N - (φ a).val) + ((φ c).val + N - (φ b).val) +
            ((φ a).val + N - (φ c).val)) % N := by
        dsimp only [x, y, z]; simp [Nat.add_mod]
      rw [h1', hsum]; exact Nat.mul_mod_left 3 N
    have hlo : 3 * d ≤ x + y + z := by omega
    have hhi : x + y + z + 3 ≤ 6 * d := by omega
    have hdiv : N ∣ (x + y + z) := Nat.dvd_of_mod_eq_zero hmod
    obtain ⟨q, hq⟩ := hdiv
    have hN_eq : N + 1 = 3 * d := by omega
    have hq1 : 1 < q := by nlinarith only [hq, hlo, hN_eq]
    have hq2 : q < 2 := by nlinarith only [hq, hhi, hN_eq, hd]
    omega
  have hGfull_H : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ n →
      50 * (Gfull.induce V').edgeSet.ncard > n ^ 2 := by
    intro V' hV'
    have hG_gt := hH V' hV'
    have hmono : (G.induce V').edgeSet.ncard ≤ (Gfull.induce V').edgeSet.ncard := by
      have h1 := two_mul_induce_edgeSet_ncard G V'.toFinset
      have h2 := two_mul_induce_edgeSet_ncard Gfull V'.toFinset
      rw [Set.coe_toFinset] at h1 h2
      have hle : ∑ u ∈ V'.toFinset, #(V'.toFinset.filter (G.Adj u)) ≤
          ∑ u ∈ V'.toFinset, #(V'.toFinset.filter (Gfull.Adj u)) :=
        Finset.sum_le_sum (fun u _ => Finset.card_le_card (fun v hv => by
          have hv' := Finset.mem_filter.mp hv
          exact Finset.mem_filter.mpr ⟨hv'.1, hGGfull u v hv'.2⟩))
      omega
    omega
  have h5e : 5 * Gfull.edgeSet.ncard < n ^ 2 := h5e_rule Gfull hGfull_TF hGfull_H
  -- Step 2: Cyclic ordering e : Fin n ≃ V sorted by φ, lifted to ℤ
  obtain ⟨e, he_mono⟩ := exists_sorted_equiv (fun u : V => (φ u).val)
  have hn_pos_z : (0 : ℤ) < (n : ℤ) := by omega
  have hN_pos_z : (0 : ℤ) < (N : ℤ) := by omega
  let v : ℤ → V := fun x => e ⟨(x % (n : ℤ)).toNat, by
    have h1 := Int.emod_nonneg x (by omega : (n : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos x hn_pos_z
    omega⟩
  have hv_per : ∀ x : ℤ, v (x + n) = v x := by
    intro x; dsimp only [v]; congr 1; apply Fin.ext; simp [Int.add_emod_right]
  have hv_inj_mod : ∀ x y : ℤ, v x = v y ↔ x % (n : ℤ) = y % (n : ℤ) := by
    intro x y
    dsimp only [v]
    constructor
    · intro h
      have h1 := congrArg Fin.val (e.injective h)
      dsimp only at h1
      have hx0 := Int.emod_nonneg x (by omega : (n : ℤ) ≠ 0)
      have hy0 := Int.emod_nonneg y (by omega : (n : ℤ) ≠ 0)
      omega
    · intro h; congr 1; apply Fin.ext; simp [h]
  let w : ℕ → ℕ := fun r => #(Finset.univ.filter (fun u : V => (φ u).val = r))
  let P : ℕ → ℕ := fun r => ∑ i ∈ Finset.range r, w i
  have hP0 : P 0 = 0 := by simp [P]
  have hPN : P N = n := by
    dsimp only [P, w, n]
    have hbij : ∑ i ∈ Finset.range N, #(Finset.univ.filter (fun u : V => (φ u).val = i)) =
        ∑ r : Fin N, #(Finset.univ.filter (fun u : V => φ u = r)) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl; intro r _
      congr 1; ext u; simp [Fin.ext_iff]
    rw [hbij, ← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  have hP_mono : ∀ r₁ r₂ : ℕ, r₁ ≤ r₂ → P r₁ ≤ P r₂ := fun r₁ r₂ h =>
    Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hP_lt_card : ∀ r : ℕ, r ≤ N → P r = #(Finset.univ.filter (fun i : Fin n => (φ (e i)).val < r)) := by
    intro r _
    induction r with
    | zero => simp [P]
    | succ r ih =>
      rw [show P (r + 1) = P r + w r by dsimp only [P]; rw [Finset.sum_range_succ]]
      rw [ih (by omega)]
      have hsplit : Finset.univ.filter (fun i : Fin n => (φ (e i)).val < r + 1) =
          Finset.univ.filter (fun i : Fin n => (φ (e i)).val < r) ∪
          Finset.univ.filter (fun i : Fin n => (φ (e i)).val = r) := by
        ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have hdisj : Disjoint (Finset.univ.filter (fun i : Fin n => (φ (e i)).val < r))
          (Finset.univ.filter (fun i : Fin n => (φ (e i)).val = r)) := by
        rw [Finset.disjoint_left]; intro i h1 h2
        have a1 := (Finset.mem_filter.mp h1).2; have a2 := (Finset.mem_filter.mp h2).2; omega
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
      congr 1
      dsimp only [w]
      refine Finset.card_bij (fun u _ => e.symm u) ?_ ?_ ?_
      · intro u hu; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢; simp [hu]
      · intro u₁ _ u₂ _ h; exact e.symm.injective h
      · intro i hi; exact ⟨e i, by simpa using hi, e.symm_apply_apply i⟩
  have hP_interval : ∀ i : Fin n, P (φ (e i)).val ≤ i.val ∧ i.val < P ((φ (e i)).val + 1) := by
    intro i
    set r := (φ (e i)).val
    have hrN : r < N := (φ (e i)).isLt
    constructor
    · -- Every j < P r? No: every j with key (e j) < r must satisfy j < i!
      have hsub : Finset.univ.filter (fun j : Fin n => (φ (e j)).val < r) ⊆
          Finset.univ.filter (fun j : Fin n => j.val < i.val) := by
        intro j hj
        have hjr : (φ (e j)).val < r := (Finset.mem_filter.mp hj).2
        apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
        by_contra hge
        have hle : i ≤ j := Fin.le_def.mpr (by omega)
        have := he_mono i j hle; omega
      have h1 := hP_lt_card r (by omega)
      have h2 := Finset.card_le_card hsub
      have h3 : #(Finset.univ.filter (fun j : Fin n => j.val < i.val)) = i.val := by
        refine (Finset.card_bij (fun (j : Fin n) _ => j.val) ?_ ?_ ?_).trans (Finset.card_range i.val)
        · intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
        · intro j₁ _ j₂ _ h; exact Fin.ext h
        · intro m hm; exact ⟨⟨m, by have := Finset.mem_range.mp hm; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hm⟩, rfl⟩
      omega
    · -- Every j <= i has key (e j) <= r < r + 1!
      have hsub : Finset.univ.filter (fun j : Fin n => j.val ≤ i.val) ⊆
          Finset.univ.filter (fun j : Fin n => (φ (e j)).val < r + 1) := by
        intro j hj
        have hle : j ≤ i := Fin.le_def.mpr (Finset.mem_filter.mp hj).2
        have := he_mono j i hle
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have h1 := hP_lt_card (r + 1) (by omega)
      have h2 := Finset.card_le_card hsub
      have h3 : #(Finset.univ.filter (fun j : Fin n => j.val ≤ i.val)) = i.val + 1 := by
        refine (Finset.card_bij (fun (j : Fin n) _ => j.val) ?_ ?_ ?_).trans (Finset.card_range (i.val + 1))
        · intro j hj; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj).2; omega)
        · intro j₁ _ j₂ _ h; exact Fin.ext h
        · intro m hm; exact ⟨⟨m, by have := Finset.mem_range.mp hm; have := i.isLt; omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := Finset.mem_range.mp hm; dsimp only; omega⟩, rfl⟩
      omega
  let PZ : ℤ → ℤ := fun r => (r / (N : ℤ)) * (n : ℤ) + (P ((r % (N : ℤ)).toNat) : ℤ)
  have hPZ_per : ∀ r : ℤ, PZ (r + N) = PZ r + n := by
    intro r; dsimp only [PZ]
    rw [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self (by omega : (N : ℤ) ≠ 0), Int.add_emod_right]
    ring
  have hPZ_mono : ∀ r₁ r₂ : ℤ, r₁ ≤ r₂ → PZ r₁ ≤ PZ r₂ := by
    intro r₁ r₂ hle
    dsimp only [PZ]
    have hq_le : r₁ / (N : ℤ) ≤ r₂ / (N : ℤ) := Int.ediv_le_ediv hN_pos_z hle
    rcases eq_or_lt_of_le hq_le with hq | hq
    · rw [hq]
      have hm1 := Int.emod_nonneg r₁ (by omega : (N : ℤ) ≠ 0)
      have hm2 := Int.emod_nonneg r₂ (by omega : (N : ℤ) ≠ 0)
      have hdiv1 := Int.mul_ediv_add_emod r₁ (N : ℤ)
      have hdiv2 := Int.mul_ediv_add_emod r₂ (N : ℤ)
      rw [hq] at hdiv1
      have hm_le : (r₁ % (N : ℤ)).toNat ≤ (r₂ % (N : ℤ)).toNat := by omega
      have := hP_mono _ _ hm_le; omega
    · have hm1_lt : (r₁ % (N : ℤ)).toNat < N := by
        have := Int.emod_lt_of_pos r₁ hN_pos_z
        have := Int.emod_nonneg r₁ (by omega : (N : ℤ) ≠ 0); omega
      have hP1 : P ((r₁ % (N : ℤ)).toNat) ≤ n := by rw [← hPN]; exact hP_mono _ _ (by omega)
      have hstep : (r₁ / (N : ℤ) + 1) * (n : ℤ) ≤ (r₂ / (N : ℤ)) * (n : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) (by omega)
      have hP2 : (0 : ℤ) ≤ (P ((r₂ % (N : ℤ)).toNat) : ℤ) := Int.natCast_nonneg _
      linarith
  let partOf : ℤ → ℤ := fun x => (x / (n : ℤ)) * (N : ℤ) + ((φ (v x)).val : ℤ)
  have hpart_per : ∀ x : ℤ, partOf (x + n) = partOf x + N := by
    intro x; dsimp only [partOf]
    rw [hv_per, Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self (by omega : (n : ℤ) ≠ 0)]
    ring
  have hpart_mono : ∀ x y : ℤ, x ≤ y → partOf x ≤ partOf y := by
    intro x y hle
    dsimp only [partOf]
    have hq_le : x / (n : ℤ) ≤ y / (n : ℤ) := Int.ediv_le_ediv hn_pos_z hle
    rcases eq_or_lt_of_le hq_le with hq | hq
    · rw [hq]
      have hx0 := Int.emod_nonneg x (by omega : (n : ℤ) ≠ 0)
      have hy0 := Int.emod_nonneg y (by omega : (n : ℤ) ≠ 0)
      have hdx := Int.mul_ediv_add_emod x (n : ℤ)
      have hdy := Int.mul_ediv_add_emod y (n : ℤ)
      rw [hq] at hdx
      have hlt_x := Int.emod_lt_of_pos x hn_pos_z
      have hlt_y := Int.emod_lt_of_pos y hn_pos_z
      have hfin : (⟨(x % (n : ℤ)).toNat, by omega⟩ : Fin n) ≤ ⟨(y % (n : ℤ)).toNat, by omega⟩ :=
        Fin.le_def.mpr (by dsimp only; omega)
      have hm := he_mono _ _ hfin
      dsimp only [v]
      omega
    · have hxN : (φ (v x)).val < N := (φ (v x)).isLt
      have hstep : (x / (n : ℤ) + 1) * (N : ℤ) ≤ (y / (n : ℤ)) * (N : ℤ) :=
        mul_le_mul_of_nonneg_right (by omega) (by omega)
      have hy0 : (0 : ℤ) ≤ ((φ (v y)).val : ℤ) := Int.natCast_nonneg _
      linarith
  have hpart_int : ∀ x : ℤ, PZ (partOf x) ≤ x ∧ x < PZ (partOf x + 1) := by
    intro x
    set q := x / (n : ℤ)
    have hdx := Int.mul_ediv_add_emod x (n : ℤ)
    have hx0 := Int.emod_nonneg x (by omega : (n : ℤ) ≠ 0)
    have hxlt := Int.emod_lt_of_pos x hn_pos_z
    let i : Fin n := ⟨(x % (n : ℤ)).toNat, by omega⟩
    have hi_val : (i.val : ℤ) = x % (n : ℤ) := by dsimp only [i]; omega
    have hvx : v x = e i := rfl
    have ⟨hlo, hhi⟩ := hP_interval i
    set r := (φ (e i)).val
    have hrN : r < N := (φ (e i)).isLt
    have hPZ_r : PZ (partOf x) = q * (n : ℤ) + (P r : ℤ) := by
      dsimp only [PZ, partOf, q, r]
      rw [hvx]
      have hdiv : ((x / (n : ℤ)) * (N : ℤ) + ((φ (e i)).val : ℤ)) / (N : ℤ) = x / (n : ℤ) := by
        rw [Int.add_ediv_of_dvd_left (dvd_mul_left _ _), Int.mul_ediv_cancel _ (by omega : (N : ℤ) ≠ 0),
          Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by omega), add_zero]
      have hmod : ((x / (n : ℤ)) * (N : ℤ) + ((φ (e i)).val : ℤ)) % (N : ℤ) = ((φ (e i)).val : ℤ) := by
        rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod,
          Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)]
      rw [hdiv, hmod, Int.toNat_natCast]
    have hPZ_r1 : PZ (partOf x + 1) = q * (n : ℤ) + (P (r + 1) : ℤ) := by
      by_cases htop : r + 1 < N
      · have htop' : ((φ (e i)).val : ℤ) + 1 < (N : ℤ) := by dsimp only [r] at htop; omega
        have hdiv0 : (((φ (e i)).val : ℤ) + 1) / (N : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by omega) htop'
        have hmod0 : (((φ (e i)).val : ℤ) + 1) % (N : ℤ) = ((φ (e i)).val : ℤ) + 1 := Int.emod_eq_of_lt (by omega) htop'
        dsimp only [PZ, partOf, q, r]
        rw [hvx, add_assoc]
        have hdiv : ((x / (n : ℤ)) * (N : ℤ) + (((φ (e i)).val : ℤ) + 1)) / (N : ℤ) = x / (n : ℤ) := by
          rw [Int.add_ediv_of_dvd_left (dvd_mul_left _ _), Int.mul_ediv_cancel _ (by omega : (N : ℤ) ≠ 0),
            hdiv0, add_zero]
        have hmod : ((x / (n : ℤ)) * (N : ℤ) + (((φ (e i)).val : ℤ) + 1)) % (N : ℤ) = (((φ (e i)).val : ℤ) + 1) := by
          rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod, hmod0]
        rw [hdiv, hmod, show (((φ (e i)).val : ℤ) + 1).toNat = (φ (e i)).val + 1 by omega]
      · have hr_eq : r + 1 = N := by omega
        have hr_eq_z : ((φ (e i)).val : ℤ) + 1 = (N : ℤ) := by dsimp only [r] at hr_eq; exact_mod_cast hr_eq
        have heq : partOf x + 1 = (q + 1) * (N : ℤ) := by
          dsimp only [partOf, q]; rw [hvx]; linarith
        rw [heq]
        dsimp only [PZ]
        rw [Int.mul_ediv_cancel _ (by omega : (N : ℤ) ≠ 0), Int.mul_emod_left, Int.toNat_zero,
          hP0, hr_eq, hPN]
        push_cast; ring
    rw [hPZ_r, hPZ_r1]
    have hx_eq : x = q * (n : ℤ) + (i.val : ℤ) := by dsimp only [q]; linarith
    omega
  -- Define lifted non-neighbor map f : ℤ -> ℤ
  let f : ℤ → ℤ := fun x => PZ (partOf x + d)
  have hf_mono : ∀ x y : ℤ, x ≤ y → f x ≤ f y := fun x y h => hPZ_mono _ _ (by have := hpart_mono x y h; omega)
  have hf_per : ∀ x : ℤ, f (x + n) = f x + n := by
    intro x; dsimp only [f]; rw [hpart_per, show partOf x + N + d = (partOf x + d) + N by ring, hPZ_per]
  have hf_gt : ∀ x : ℤ, x < f x := by
    intro x
    have h1 := (hpart_int x).2
    have h2 : PZ (partOf x + 1) ≤ PZ (partOf x + d) := hPZ_mono _ _ (by omega)
    exact lt_of_lt_of_le h1 h2
  -- Independent-half check: f x <= x + k - 1 for all x
  have hf_le : ∀ x : ℤ, f x ≤ x + k - 1 := by
    intro x
    by_contra hgt
    push Not at hgt
    let A : Finset V := (Finset.range k).image (fun j : ℕ => v (x + (j : ℤ)))
    have hAcard : #A = k := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro a ha b hb hab
      have ha' := Finset.mem_range.mp ha; have hb' := Finset.mem_range.mp hb
      have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
      omega
    have hAindep : ∀ u ∈ A, ∀ w' ∈ A, ¬ Gfull.Adj u w' := by
      intro u hu w' hw' hadj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw'
      have ha' := Finset.mem_range.mp ha; have hb' := Finset.mem_range.mp hb
      have hbd : ∀ j : ℕ, j < k → partOf x ≤ partOf (x + (j : ℤ)) ∧ partOf (x + (j : ℤ)) < partOf x + d := by
        intro j hj
        refine ⟨hpart_mono x (x + j) (by omega), ?_⟩
        by_contra hge
        push Not at hge
        have h1 : PZ (partOf x + d) ≤ PZ (partOf (x + j)) := hPZ_mono _ _ hge
        have h2 := (hpart_int (x + j)).1
        dsimp only [f] at hgt; omega
      have hpa := hbd a ha'; have hpb := hbd b hb'
      -- Now |partOf (x+b) - partOf (x+a)| < d, contradicting Gfull.Adj!
      have hmod_eq : ∀ y : ℤ, ((partOf y) % (N : ℤ)) = ((φ (v y)).val : ℤ) := by
        intro y; dsimp only [partOf]
        rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have := (φ (v y)).isLt; omega)]
      have hdiff_mod : ((((φ (v (x + b))).val + N - (φ (v (x + a))).val) % N : ℕ) : ℤ) =
          (partOf (x + b) - partOf (x + a)) % (N : ℤ) := by
        have h1 : (((φ (v (x + b))).val + N - (φ (v (x + a))).val : ℕ) : ℤ) =
            ((φ (v (x + b))).val : ℤ) - ((φ (v (x + a))).val : ℤ) + (N : ℤ) := by
          have := (φ (v (x + a))).isLt; omega
        rw [Int.natCast_emod, h1, Int.add_emod_right, ← hmod_eq (x + b), ← hmod_eq (x + a),
          ← Int.sub_emod]
      have ⟨hlo, hhi⟩ := hadj
      have hlo_z : (d : ℤ) ≤ (partOf (x + b) - partOf (x + a)) % (N : ℤ) := by
        rw [← hdiff_mod]; exact_mod_cast hlo
      have hhi_z : (partOf (x + b) - partOf (x + a)) % (N : ℤ) < (2 * d : ℤ) := by
        rw [← hdiff_mod]; exact_mod_cast hhi
      by_cases hab_le : partOf (x + a) ≤ partOf (x + b)
      · have hmod0 : (partOf (x + b) - partOf (x + a)) % (N : ℤ) = partOf (x + b) - partOf (x + a) :=
          Int.emod_eq_of_lt (by omega) (by omega)
        omega
      · have hmod0 : (partOf (x + b) - partOf (x + a)) % (N : ℤ) = partOf (x + b) - partOf (x + a) + N := by
          have := Int.add_emod_right (partOf (x + b) - partOf (x + a)) (N : ℤ)
          rw [← this, Int.emod_eq_of_lt (by omega) (by omega)]
        omega
    have h50 := hGfull_H (A : Set V) (by rw [Set.ncard_coe_finset, hAcard]; omega)
    have h0 : 2 * (Gfull.induce (A : Set V)).edgeSet.ncard = 0 := by
      rw [two_mul_induce_edgeSet_ncard]
      apply Finset.sum_eq_zero; intro u hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w' hw'; exact hAindep u hu w' hw'
    omega
  -- Step 3: Exact equivalence Gfull.Adj (v x) (v y) ↔ f x ≤ y for all x ≤ y ≤ x + k
  have hadj_iff : ∀ x y : ℤ, x ≤ y → y ≤ x + k → (Gfull.Adj (v x) (v y) ↔ f x ≤ y) := by
    intro x y hxy hyx
    have hrx_le : partOf x ≤ partOf y := hpart_mono x y hxy
    have hfy_le : partOf y < partOf x + 2 * d := by
      by_contra hge
      push Not at hge
      have h1 : PZ ((partOf x + 1) + N) ≤ PZ (partOf y + d) := hPZ_mono _ _ (by omega)
      rw [hPZ_per] at h1
      have h2 := (hpart_int x).2
      have h3 := hf_le y
      dsimp only [f] at h3
      omega
    have hf_iff : f x ≤ y ↔ partOf x + d ≤ partOf y := by
      constructor
      · intro hfy
        by_contra hlt
        have h1 : PZ (partOf y + 1) ≤ PZ (partOf x + d) := hPZ_mono _ _ (by omega)
        have h2 := (hpart_int y).2
        dsimp only [f] at hfy; omega
      · intro hge
        have h1 : PZ (partOf x + d) ≤ PZ (partOf y) := hPZ_mono _ _ hge
        have h2 := (hpart_int y).1
        dsimp only [f]; omega
    rw [hf_iff]
    have hmod_eq : ∀ z : ℤ, ((partOf z) % (N : ℤ)) = ((φ (v z)).val : ℤ) := by
      intro z; dsimp only [partOf]
      rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod, Int.emod_eq_of_lt (Int.natCast_nonneg _) (by have := (φ (v z)).isLt; omega)]
    have hdiff_mod : ((((φ (v y)).val + N - (φ (v x)).val) % N : ℕ) : ℤ) = partOf y - partOf x := by
      have h1 : (((φ (v y)).val + N - (φ (v x)).val : ℕ) : ℤ) =
          ((φ (v y)).val : ℤ) - ((φ (v x)).val : ℤ) + (N : ℤ) := by
        have := (φ (v x)).isLt; omega
      rw [Int.natCast_emod, h1, Int.add_emod_right, ← hmod_eq y, ← hmod_eq x, ← Int.sub_emod,
        Int.emod_eq_of_lt (by omega) (by omega)]
    dsimp only [Gfull, adjFull]
    constructor
    · rintro ⟨hlo, _⟩
      have hlo_z : (d : ℤ) ≤ partOf y - partOf x := by rw [← hdiff_mod]; exact_mod_cast hlo
      omega
    · intro hge
      constructor
      · have : (d : ℤ) ≤ ((((φ (v y)).val + N - (φ (v x)).val) % N : ℕ) : ℤ) := by omega
        exact_mod_cast this
      · have : ((((φ (v y)).val + N - (φ (v x)).val) % N : ℕ) : ℤ) < (2 * d : ℤ) := by omega
        exact_mod_cast this
  -- Step 4: Exact edge count bound 2 * ∑_{x ∈ Fin n} (x + k - f x) + n <= 2 * e(Gfull)
  let g : ℤ → ℤ := fun x => x + k - f x
  have hg_per : ∀ x : ℤ, g (x + n) = g x := by intro x; dsimp only [g]; rw [hf_per]; ring
  have hg_pos : ∀ x : ℤ, 1 ≤ g x := fun x => by dsimp only [g]; have := hf_le x; omega
  have hE_bound : 2 * (∑ i : Fin n, g (i.val : ℤ)) + (n : ℤ) ≤ 2 * (Gfull.edgeSet.ncard : ℤ) := by
    have h2e : 2 * Gfull.edgeSet.ncard = ∑ i : Fin n, #(Finset.univ.filter (Gfull.Adj (e i))) := by
      have hcard : Gfull.edgeSet.ncard = #Gfull.edgeFinset := by
        rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      rw [← Equiv.sum_comp e (fun u => Gfull.degree u)]
      apply Finset.sum_congr rfl; intro i _
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset]; congr 1; ext u; simp
    -- For each i : Fin n, partition neighbors of v(i) into Fwd, Bwd, Ant (all pairwise disjoint!)
    let Fwd : Fin n → Finset V := fun i =>
      ((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val + (t + 1 : ℕ))))).image
        (fun t => v (i.val + (t + 1 : ℕ)))
    let Bwd : Fin n → Finset V := fun i =>
      ((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val - (t + 1 : ℕ))))).image
        (fun t => v (i.val - (t + 1 : ℕ)))
    have hper_deg : ∀ i : Fin n,
        #(Fwd i) + #(Bwd i) + 1 ≤ #(Finset.univ.filter (Gfull.Adj (e i))) := by
      intro i
      have hvi : v i.val = e i := by
        dsimp only [v]; congr 1; apply Fin.ext; dsimp only
        rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega), Int.toNat_natCast]
      have hFsub : Fwd i ⊆ Finset.univ.filter (Gfull.Adj (e i)) := by
        intro u hu
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hvi]; exact (Finset.mem_filter.mp ht).2⟩
      have hBsub : Bwd i ⊆ Finset.univ.filter (Gfull.Adj (e i)) := by
        intro u hu
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hvi]; exact (Finset.mem_filter.mp ht).2⟩
      have hAnt_mem : v (i.val + k) ∈ Finset.univ.filter (Gfull.Adj (e i)) := by
        apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hvi, hadj_iff i.val (i.val + k) (by omega) (le_refl _)]
        have := hf_le i.val; omega
      have hdisj_FB : Disjoint (Fwd i) (Bwd i) := by
        rw [Finset.disjoint_left]; intro u huF huB
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp huF
        obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp huB
        have ht' := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        have hs' := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp heq.symm) (by omega) (by omega)
        omega
      have hAnt_notF : v (i.val + k) ∉ Fwd i := by
        intro hmem
        obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
        have ht' := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp heq.symm) (by omega) (by omega)
        omega
      have hAnt_notB : v (i.val + k) ∉ Bwd i := by
        intro hmem
        obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp hmem
        have ht' := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp heq.symm) (by omega) (by omega)
        omega
      have hcard_union : #(insert (v (i.val + k)) (Fwd i ∪ Bwd i)) = #(Fwd i) + #(Bwd i) + 1 := by
        rw [Finset.card_insert_of_notMem (by simp [hAnt_notF, hAnt_notB]),
          Finset.card_union_of_disjoint hdisj_FB]
      rw [← hcard_union]
      exact Finset.card_le_card (Finset.insert_subset hAnt_mem (Finset.union_subset hFsub hBsub))
    have hFwd_card : ∀ i : Fin n, (#(Fwd i) : ℤ) = g i.val := by
      intro i
      have hinj : Set.InjOn (fun t : ℕ => v (i.val + (t + 1 : ℕ)))
          ((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val + (t + 1 : ℕ))))) := by
        intro a ha b hb hab
        have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
        omega
      rw [Finset.card_image_of_injOn hinj]
      have hbij : #((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val + (t + 1 : ℕ))))) =
          (g i.val).toNat := by
        have hf_gt_i := hf_gt i.val
        have hf_le_i := hf_le i.val
        refine (Finset.card_bij (fun t _ => ((i.val + (t + 1 : ℕ)) - f i.val).toNat) ?_ ?_ ?_).trans
          (Finset.card_range (g i.val).toNat)
        · intro t ht
          have ht' := Finset.mem_filter.mp ht
          have htr := Finset.mem_range.mp ht'.1
          have hge := (hadj_iff i.val (i.val + (t + 1 : ℕ)) (by omega) (by omega)).mp ht'.2
          exact Finset.mem_range.mpr (by dsimp only [g]; omega)
        · intro a ha b hb heq
          have ha' := Finset.mem_filter.mp ha; have hb' := Finset.mem_filter.mp hb
          have har := Finset.mem_range.mp ha'.1; have hbr := Finset.mem_range.mp hb'.1
          have hga := (hadj_iff i.val (i.val + (a + 1 : ℕ)) (by omega) (by omega)).mp ha'.2
          have hgb := (hadj_iff i.val (i.val + (b + 1 : ℕ)) (by omega) (by omega)).mp hb'.2
          omega
        · intro m hm
          have hmr := Finset.mem_range.mp hm
          set t := (f i.val + m - i.val - 1).toNat
          refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by dsimp only [g] at hmr; omega), ?_⟩, ?_⟩
          · rw [hadj_iff i.val (i.val + (t + 1 : ℕ)) (by omega) (by dsimp only [g] at hmr; omega)]
            dsimp only [t]; omega
          · dsimp only [t]; omega
      rw [hbij]; have := hg_pos i.val; omega
    have hBwd_sum : ∑ i : Fin n, #(Bwd i) = ∑ i : Fin n, #(Fwd i) := by
      have hcardB : ∀ i : Fin n, #(Bwd i) =
          #((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val - (t + 1 : ℕ))))) := by
        intro i
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
        omega
      have hcardF : ∀ i : Fin n, #(Fwd i) =
          #((Finset.range (k - 1)).filter (fun t => Gfull.Adj (v i.val) (v (i.val + (t + 1 : ℕ))))) := by
        intro i
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        have ha' := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hb' := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
        omega
      simp_rw [hcardB, hcardF, Finset.card_filter]
      rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
      apply Finset.sum_congr rfl; intro t _
      let shift : Fin n ≃ Fin n :=
        { toFun := fun i => ⟨(i.val + n - (t + 1) % n) % n, Nat.mod_lt _ (by omega)⟩
          invFun := fun i => ⟨(i.val + (t + 1)) % n, Nat.mod_lt _ (by omega)⟩
          left_inv := fun i => Fin.ext (by
            dsimp only
            have hi := i.isLt
            have hm := Nat.mod_lt (t + 1) (by omega : 0 < n)
            have h1 : ((i.val + n - (t + 1) % n) % n + (t + 1)) % n =
                ((i.val + n - (t + 1) % n) + (t + 1) % n) % n := by
              rw [Nat.add_mod, Nat.mod_mod, Nat.add_mod (i.val + n - (t + 1) % n), Nat.mod_mod]
            rw [h1, Nat.sub_add_cancel (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt hi])
          right_inv := fun i => Fin.ext (by
            dsimp only
            have hi := i.isLt
            have hm := Nat.mod_lt (t + 1) (by omega : 0 < n)
            have hmod : (i.val + (t + 1)) % n = (i.val + (t + 1) % n) % n := by
              rw [Nat.add_mod, Nat.add_mod i.val ((t + 1) % n), Nat.mod_mod]
            rw [hmod]
            by_cases hlt : i.val + (t + 1) % n < n
            · rw [Nat.mod_eq_of_lt hlt, show i.val + (t + 1) % n + n - (t + 1) % n = i.val + n by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt hi]
            · have hsub : (i.val + (t + 1) % n) % n = i.val + (t + 1) % n - n := by
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
              rw [hsub, show i.val + (t + 1) % n - n + n - (t + 1) % n = i.val by omega,
                Nat.mod_eq_of_lt hi]) }
      refine Fintype.sum_equiv shift _ _ (fun i => ?_)
      have h1 : v ((shift i).val : ℤ) = v (i.val - (t + 1 : ℕ)) := by
        rw [hv_inj_mod]
        have hi := i.isLt
        have hm := Nat.mod_lt (t + 1) (by omega : 0 < n)
        have hlt_s : (shift i).val < n := (shift i).isLt
        rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)]
        change (((i.val + n - (t + 1) % n) % n : ℕ) : ℤ) = _
        have hcast : (((i.val + n - (t + 1) % n) % n : ℕ) : ℤ) =
            ((i.val : ℤ) + (n : ℤ) - (((t + 1) % n : ℕ) : ℤ)) % (n : ℤ) := by
          rw [Int.natCast_emod]; congr 1; omega
        rw [hcast, show (i.val : ℤ) + (n : ℤ) - (((t + 1) % n : ℕ) : ℤ) =
            (n : ℤ) + ((i.val : ℤ) - (((t + 1) % n : ℕ) : ℤ)) by ring,
          Int.add_emod_left, Int.natCast_emod, Int.sub_emod, Int.emod_emod, ← Int.sub_emod]
      have h2 : v ((shift i).val + (t + 1 : ℕ)) = v i.val := by
        rw [hv_inj_mod]
        have h1' := (hv_inj_mod _ _).mp h1
        rw [Int.add_emod, h1', ← Int.add_emod, sub_add_cancel]
      simp only [h1, h2, Gfull.adj_comm]
    have hsum_le : ∑ i : Fin n, (#(Fwd i) + #(Bwd i) + 1) ≤ 2 * Gfull.edgeSet.ncard := by
      rw [h2e]; exact Finset.sum_le_sum (fun i _ => hper_deg i)
    simp_rw [Finset.sum_add_distrib] at hsum_le
    rw [hBwd_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum_le
    have hsum_z : (∑ i : Fin n, (#(Fwd i) : ℤ)) = ∑ i : Fin n, g i.val :=
      Finset.sum_congr rfl (fun i _ => hFwd_card i)
    have hcast : ((∑ i : Fin n, #(Fwd i) + ∑ i : Fin n, #(Fwd i) + n : ℕ) : ℤ) ≤
        ((2 * Gfull.edgeSet.ncard : ℕ) : ℤ) := Nat.cast_le.mpr hsum_le
    push_cast at hcast
    rw [hsum_z] at hcast
    linarith
  -- Step 5-6: Verify k-arc edge formula and invoke standalone corner-orbit contradiction!
  apply andrasfai_corner_orbit_contra hn2 hk1 (by omega) h5e f hf_per hf_gt hf_le hE_bound
  intro t h_t hht_gt hht_min hht_spec
  let A := (Finset.range k).image (fun j : ℕ => v (t + (j : ℤ)))
  have hinjA : Set.InjOn (fun j : ℕ => v (t + (j : ℤ))) (Finset.range k) := by
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp ha; have hb' := Finset.mem_range.mp hb
    have h := int_eq_of_emod_eq hn_pos_z ((hv_inj_mod _ _).mp hab) (by omega) (by omega)
    omega
  have hAcard : #A = k := by rw [Finset.card_image_of_injOn hinjA, Finset.card_range]
  have h50 := hGfull_H (A : Set V) (by rw [Set.ncard_coe_finset, hAcard]; omega)
  have h2A := two_mul_induce_edgeSet_ncard Gfull A
  have hdouble : ∑ u ∈ A, #(A.filter (Gfull.Adj u)) =
      2 * ∑ a ∈ Finset.range k, #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) := by
    rw [Finset.sum_image (fun a ha b hb h => hinjA ha hb h)]
    have hper : ∀ a ∈ Finset.range k, #(A.filter (Gfull.Adj (v (t + a)))) =
        #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) +
        #((Finset.range k).filter (fun b => b < a ∧ Gfull.Adj (v (t + b)) (v (t + a)))) := by
      intro a _
      have hbij : #(A.filter (Gfull.Adj (v (t + (a : ℤ))))) =
          #((Finset.range k).filter (fun b : ℕ => Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ))))) := by
        symm
        refine Finset.card_bij (fun (b : ℕ) _ => v (t + (b : ℤ))) ?_ ?_ ?_
        · intro b hb; have hb' := Finset.mem_filter.mp hb
          exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hb'.1, hb'.2⟩
        · intro b₁ hb₁ b₂ hb₂ heq
          exact hinjA (Finset.mem_filter.mp hb₁).1 (Finset.mem_filter.mp hb₂).1 heq
        · intro u hu; have hu' := Finset.mem_filter.mp hu
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu'.1
          exact ⟨b, Finset.mem_filter.mpr ⟨hb, hu'.2⟩, rfl⟩
      rw [hbij]
      have hsplit : (Finset.range k).filter (fun b : ℕ => Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ)))) =
          (Finset.range k).filter (fun b : ℕ => a < b ∧ Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ)))) ∪
          (Finset.range k).filter (fun b : ℕ => b < a ∧ Gfull.Adj (v (t + (b : ℤ))) (v (t + (a : ℤ)))) := by
        ext b; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hb, hadj⟩
          rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
          rcases lt_trichotomy a b with hlt | rfl | hgt
          · exact Or.inl ⟨hb, hlt, hadj⟩
          · exact (Gfull.loopless.irrefl _ hadj).elim
          · exact Or.inr ⟨hb, hgt, hadj.symm⟩
        · intro h; rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at h
          rcases h with ⟨hb, _, hadj⟩ | ⟨hb, _, hadj⟩
          · exact ⟨hb, hadj⟩
          · exact ⟨hb, hadj.symm⟩
      have hdisj : Disjoint ((Finset.range k).filter (fun b : ℕ => a < b ∧ Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ)))))
          ((Finset.range k).filter (fun b : ℕ => b < a ∧ Gfull.Adj (v (t + (b : ℤ))) (v (t + (a : ℤ))))) := by
        rw [Finset.disjoint_left]; intro b h1 h2
        have := (Finset.mem_filter.mp h1).2.1; have := (Finset.mem_filter.mp h2).2.1; omega
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
    rw [Finset.sum_congr rfl hper, Finset.sum_add_distrib]
    have hsym : ∑ a ∈ Finset.range k, #((Finset.range k).filter (fun b => b < a ∧ Gfull.Adj (v (t + b)) (v (t + a)))) =
        ∑ b ∈ Finset.range k, #((Finset.range k).filter (fun a => b < a ∧ Gfull.Adj (v (t + b)) (v (t + a)))) := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
    rw [hsym]; ring
  have heA : (Gfull.induce (A : Set V)).edgeSet.ncard =
      ∑ a ∈ Finset.range k, #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) := by
    omega
  have hht_le : h_t ≤ t + k := by
    by_contra hgt; push Not at hgt
    have := hht_min (t + k) (by omega) hgt
    have := hf_gt (t + k); omega
  set L := (h_t - t).toNat
  have hL_le : L ≤ k := by omega
  have hL_eq : (L : ℤ) = h_t - t := by omega
  have htail0 : ∑ a ∈ Finset.range k \ Finset.range L,
      #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) = 0 := by
    apply Finset.sum_eq_zero; intro a ha
    have ha_ge : L ≤ a := by have := (Finset.mem_sdiff.mp ha).2; simp only [Finset.mem_range] at this; omega
    have ha_lt : a < k := Finset.mem_range.mp (Finset.mem_sdiff.mp ha).1
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro b hb ⟨hab, hadj⟩
    have hb_lt := Finset.mem_range.mp hb
    have hge := (hadj_iff (t + a) (t + b) (by omega) (by omega)).mp hadj
    have hfa : t + k ≤ f (t + a) := hht_spec.trans (hf_mono h_t (t + a) (by omega))
    omega
  have houter : ∑ a ∈ Finset.range k,
      #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) =
      ∑ a ∈ Finset.range L,
        #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))) := by
    have h1 := (Finset.sum_union Finset.disjoint_sdiff (s₁ := Finset.range L) (s₂ := Finset.range k \ Finset.range L)
      (f := fun a => #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + a)) (v (t + b)))))).symm
    rw [Finset.union_sdiff_of_subset (Finset.range_mono hL_le)] at h1
    rw [← h1, htail0, add_zero]
  have heA_eq : ((Gfull.induce (A : Set V)).edgeSet.ncard : ℤ) =
      ∑ j ∈ Finset.range L, (t + k - f (t + (j : ℤ))) := by
    rw [heA, houter, Nat.cast_sum]
    apply Finset.sum_congr rfl; intro a ha
    have ha_lt : a < L := Finset.mem_range.mp ha
    have hfa_lt : f (t + a) < t + k := hht_min (t + a) (by omega) (by omega)
    have hfa_gt : t + a < f (t + a) := hf_gt (t + a)
    have hcnt : #((Finset.range k).filter (fun b => a < b ∧ Gfull.Adj (v (t + (a : ℤ))) (v (t + (b : ℤ))))) =
        (t + k - f (t + (a : ℤ))).toNat := by
      refine (Finset.card_bij (fun (b : ℕ) _ => ((t + (b : ℤ)) - f (t + (a : ℤ))).toNat) ?_ ?_ ?_).trans
        (Finset.card_range (t + k - f (t + (a : ℤ))).toNat)
      · intro b hb; have hb' := Finset.mem_filter.mp hb
        have hbr := Finset.mem_range.mp hb'.1
        have hge := (hadj_iff (t + a) (t + b) (by omega) (by omega)).mp hb'.2.2
        exact Finset.mem_range.mpr (by omega)
      · intro b₁ hb₁ b₂ hb₂ heq
        have h1 := Finset.mem_filter.mp hb₁; have h2 := Finset.mem_filter.mp hb₂
        have h1r := Finset.mem_range.mp h1.1; have h2r := Finset.mem_range.mp h2.1
        have hg1 := (hadj_iff (t + a) (t + b₁) (by omega) (by omega)).mp h1.2.2
        have hg2 := (hadj_iff (t + a) (t + b₂) (by omega) (by omega)).mp h2.2.2
        omega
      · intro m hm; have hmr := Finset.mem_range.mp hm
        set b := (f (t + a) + m - t).toNat
        refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega, ?_⟩, by omega⟩
        rw [hadj_iff (t + a) (t + b) (by omega) (by omega)]; dsimp only [b]; omega
    rw [hcnt]; omega
  rw [← heA_eq]
  exact_mod_cast h50

lemma exists_maximal_threeColorable_triangleFree {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) (col : V → Fin 3) (hcol : ∀ u v : V, G.Adj u v → col u ≠ col v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
      (∀ u v : V, H.Adj u v → col u ≠ col v) ∧
      (∀ u v : V, col u ≠ col v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w) := by
  classical
  suffices h : ∀ m : ℕ, ∀ G : SimpleGraph V, G.CliqueFree 3 →
      (∀ u v : V, G.Adj u v → col u ≠ col v) →
      Fintype.card (Sym2 V) - #G.edgeFinset ≤ m →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
        (∀ u v : V, H.Adj u v → col u ≠ col v) ∧
        (∀ u v : V, col u ≠ col v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w) from
    h (Fintype.card (Sym2 V) - #G.edgeFinset) G hTF hcol (le_refl _)
  intro m
  induction m with
  | zero =>
    intro G hTF hcol hm
    refine ⟨G, le_refl _, hTF, hcol, ?_⟩
    intro u v hne hna
    exfalso
    have hcard : #G.edgeFinset ≤ Fintype.card (Sym2 V) := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    have heq : G.edgeFinset = Finset.univ := Finset.eq_univ_of_card _ (by omega)
    exact hna (SimpleGraph.mem_edgeFinset.mp (heq ▸ Finset.mem_univ s(u, v)))
  | succ m ih =>
    intro G hTF hcol hm
    by_cases hmax : ∀ u v : V, col u ≠ col v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w
    · exact ⟨G, le_refl _, hTF, hcol, hmax⟩
    · push Not at hmax
      obtain ⟨u, v, hcol_uv, hna, hno_cn⟩ := hmax
      have huv : u ≠ v := fun h => hcol_uv (congrArg col h)
      let G' : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
      have hGG' : G ≤ G' := le_sup_left
      have hG'_adj : ∀ a b : V, G'.Adj a b ↔ G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
        intro a b
        simp only [G', SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
        constructor
        · rintro (h | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
          · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩
      have hG'_col : ∀ a b : V, G'.Adj a b → col a ≠ col b := by
        intro a b hab
        rcases (hG'_adj a b).mp hab with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hcol a b h
        · exact hcol_uv
        · exact hcol_uv.symm
      have hG'_TF : G'.CliqueFree 3 := by
        intro s hs
        obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
        have h1 : G'.Adj a b := hs.1 (by simp) (by simp) hab
        have h2 : G'.Adj b c := hs.1 (by simp) (by simp) hbc
        have h3 : G'.Adj a c := hs.1 (by simp) (by simp) hac
        rw [hG'_adj] at h1 h2 h3
        by_cases g1 : G.Adj a b
        · by_cases g2 : G.Adj b c
          · by_cases g3 : G.Adj a c
            · exact not_adj_of_cliqueFree_three hTF g1 g2 g3
            · rcases h3 with h3 | ⟨ha, hc⟩ | ⟨ha, hc⟩
              · exact g3 h3
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g1 g2.symm
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g2.symm g1
          · rcases h2 with h2 | ⟨hb, hc⟩ | ⟨hb, hc⟩
            · exact g2 h2
            · rcases h3 with g3 | ⟨ha, _⟩ | ⟨_, hcu⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g1.symm g3.symm
              · exact hab (ha.trans hb.symm)
              · exact huv (hcu.symm.trans hc)
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨ha, _⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g3.symm g1.symm
              · exact huv (hc.symm.trans hcv)
              · exact hab (ha.trans hb.symm)
        · rcases h1 with h1 | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact g1 h1
          · rcases h2 with g2 | ⟨hbu, _⟩ | ⟨_, hcu⟩
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨hau, _⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g3 g2
              · exact hbc (hb.trans hcv.symm)
              · exact huv (ha.symm.trans hau)
            · exact huv (hb.symm.trans hbu).symm
            · exact hac (ha.trans hcu.symm)
          · rcases h2 with g2 | ⟨_, hcv⟩ | ⟨hbv, _⟩
            · rcases h3 with g3 | ⟨hau, _⟩ | ⟨_, hcu⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g2 g3
              · exact huv (hau.symm.trans ha)
              · exact hbc (hb.trans hcu.symm)
            · exact hac (ha.trans hcv.symm)
            · exact huv (hb.symm.trans hbv)
      have hstrict : #G.edgeFinset < #G'.edgeFinset := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun e he => SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hGG' (SimpleGraph.mem_edgeFinset.mp he)), ?_⟩
        intro heq
        have hmem : s(u, v) ∈ G'.edgeFinset :=
          SimpleGraph.mem_edgeFinset.mpr ((hG'_adj u v).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        rw [← heq] at hmem; exact hna (SimpleGraph.mem_edgeFinset.mp hmem)
      have hcard_G' : #G'.edgeFinset ≤ Fintype.card (Sym2 V) := by
        rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
      have hstep_m : Fintype.card (Sym2 V) - #G'.edgeFinset ≤ m := by omega
      obtain ⟨H, hG'H, hHTF, hHcol, hHmax⟩ := ih G' hG'_TF hG'_col (by convert hstep_m)
      exact ⟨H, hGG'.trans hG'H, hHTF, hHcol, hHmax⟩

lemma fin3_third {a b c x : Fin 3} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c)
    (hx1 : x ≠ a) (hx2 : x ≠ b) : x = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases x <;> simp_all

lemma strictMono_fin_tight {a : ℕ} (f : Fin a → ℕ)
    (hmono : ∀ i j : Fin a, i < j → f i < f j) :
    ∀ i : Fin a, i.val ≤ f i := by
  intro i
  induction hval : i.val generalizing i with
  | zero => omega
  | succ m ih =>
    have hprev := ih ⟨m, by omega⟩ rfl
    have hlt := hmono ⟨m, by omega⟩ i (Fin.lt_def.mpr (by dsimp only; omega))
    omega

lemma strictMono_fin_eq_id {a : ℕ} (f : Fin a → ℕ)
    (hmono : ∀ i j : Fin a, i < j → f i < f j)
    (hhi : ∀ i : Fin a, f i < a) :
    ∀ i : Fin a, f i = i.val := by
  have hlo : ∀ i : Fin a, i.val ≤ f i := strictMono_fin_tight f hmono
  have hup : ∀ m : ℕ, ∀ i : Fin a, a - 1 - i.val = m → f i ≤ i.val := by
    intro m; induction m with
    | zero => intro i hm; have := hhi i; omega
    | succ m ih =>
      intro i hm
      have hnext := ih ⟨i.val + 1, by omega⟩ (by dsimp only; omega)
      have hlt := hmono i ⟨i.val + 1, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
      dsimp only at hnext; omega
  intro i; have := hlo i; have := hup (a - 1 - i.val) i rfl; omega

lemma strictMono_fin_eq_succ {a : ℕ} (f : Fin a → ℕ)
    (hmono : ∀ i j : Fin a, i < j → f i < f j)
    (h0 : ∀ i : Fin a, 1 ≤ f i) (hhi : ∀ i : Fin a, f i ≤ a) :
    ∀ i : Fin a, f i = i.val + 1 := by
  have h := strictMono_fin_eq_id (fun i => f i - 1)
    (fun i j hij => by have := hmono i j hij; have := h0 i; omega)
    (fun i => by have := hhi i; have := h0 i; omega)
  intro i; have := h i; have := h0 i; omega

lemma cjk_quotient_ordered {a b c : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (f : Fin a → ℕ) (g : Fin b → ℕ) (h : Fin c → ℕ)
    (hf_le : ∀ i, f i ≤ b) (hg_le : ∀ j, g j ≤ c) (hh_le : ∀ k, h k ≤ a)
    (hf_sm : ∀ i₁ i₂, i₁ < i₂ → f i₁ < f i₂)
    (hg_sm : ∀ j₁ j₂, j₁ < j₂ → g j₁ < g j₂)
    (hh_sm : ∀ k₁ k₂, k₁ < k₂ → h k₁ < h k₂)
    (hTF : ∀ (i : Fin a) (j : Fin b) (k : Fin c), ¬ (f i ≤ j.val ∧ g j ≤ k.val ∧ h k ≤ i.val))
    (hmaxXY : ∀ (i : Fin a) (j : Fin b), j.val < f i → ∃ k : Fin c, g j ≤ k.val ∧ h k ≤ i.val)
    (hmaxYZ : ∀ (j : Fin b) (k : Fin c), k.val < g j → ∃ i : Fin a, f i ≤ j.val ∧ h k ≤ i.val)
    (hmaxZX : ∀ (k : Fin c) (i : Fin a), i.val < h k → ∃ j : Fin b, f i ≤ j.val ∧ g j ≤ k.val) :
    ∃ (d : ℕ) (_ : 1 ≤ d) (φX : Fin a → Fin (3 * d - 1)) (φY : Fin b → Fin (3 * d - 1))
      (φZ : Fin c → Fin (3 * d - 1)),
      (∀ i j, f i ≤ j.val →
        d ≤ ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) ∧
        ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) < 2 * d) ∧
      (∀ j k, g j ≤ k.val →
        d ≤ ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) ∧
        ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) < 2 * d) ∧
      (∀ k i, h k ≤ i.val →
        d ≤ ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) ∧
        ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) < 2 * d) := by
  have hc_le : c ≤ a + 1 := by
    have h1 := strictMono_fin_tight h hh_sm ⟨c - 1, by omega⟩
    have h2 := hh_le ⟨c - 1, by omega⟩
    dsimp only at h1; omega
  -- Case split into the 3 exact shapes: (d-1, d, d), (d, d, d), (d-1, d-1, d)
  by_cases hac : a = c
  · -- Shape (d, d, d) with d = c >= 1
    have hbd : b = c := by omega
    -- At least one of f 0, g 0, h 0 is >= 1 by triangle-freeness at (0, 0, 0)
    have hge1 : 1 ≤ f ⟨0, by omega⟩ ∨ 1 ≤ g ⟨0, by omega⟩ ∨ 1 ≤ h ⟨0, by omega⟩ := by
      have h0 := hTF ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨0, by omega⟩
      dsimp only at h0; omega
    -- Helper when h 0 >= 1 in shape (d, d, d)
    have hDDD : ∀ (a' b' c' : ℕ) (h1 : a' = c') (h2 : b' = c') (hc' : 1 ≤ c')
        (f' : Fin a' → ℕ) (g' : Fin b' → ℕ) (h' : Fin c' → ℕ)
        (_ : ∀ i, f' i ≤ b') (_ : ∀ j, g' j ≤ c') (_ : ∀ k, h' k ≤ a')
        (_ : ∀ i₁ i₂, i₁ < i₂ → f' i₁ < f' i₂)
        (_ : ∀ j₁ j₂, j₁ < j₂ → g' j₁ < g' j₂)
        (_ : ∀ k₁ k₂, k₁ < k₂ → h' k₁ < h' k₂)
        (_ : ∀ i j k, ¬ (f' i ≤ j.val ∧ g' j ≤ k.val ∧ h' k ≤ i.val))
        (_ : ∀ j k, k.val < g' j → ∃ i, f' i ≤ j.val ∧ h' k ≤ i.val)
        (_ : ∀ k i, i.val < h' k → ∃ j, f' i ≤ j.val ∧ g' j ≤ k.val)
        (_ : 1 ≤ h' ⟨0, by omega⟩),
        ∃ (φX : Fin a' → Fin (3 * c' - 1)) (φY : Fin b' → Fin (3 * c' - 1))
          (φZ : Fin c' → Fin (3 * c' - 1)),
          (∀ i j, f' i ≤ j.val →
            c' ≤ ((φY j).val + (3 * c' - 1) - (φX i).val) % (3 * c' - 1) ∧
            ((φY j).val + (3 * c' - 1) - (φX i).val) % (3 * c' - 1) < 2 * c') ∧
          (∀ j k, g' j ≤ k.val →
            c' ≤ ((φZ k).val + (3 * c' - 1) - (φY j).val) % (3 * c' - 1) ∧
            ((φZ k).val + (3 * c' - 1) - (φY j).val) % (3 * c' - 1) < 2 * c') ∧
          (∀ k i, h' k ≤ i.val →
            c' ≤ ((φX i).val + (3 * c' - 1) - (φZ k).val) % (3 * c' - 1) ∧
            ((φX i).val + (3 * c' - 1) - (φZ k).val) % (3 * c' - 1) < 2 * c') := by
      intro a' b' c' h1 h2 hc' f' g' h' hf'l hg'l hh'l hf's hg's hh's hTF' hmYZ' hmZX' hh0
      have hh_all1 : ∀ k : Fin c', 1 ≤ h' k := by
        intro k; by_cases hk0 : k.val = 0
        · have : k = ⟨0, by omega⟩ := Fin.ext hk0; rw [this]; exact hh0
        · have := hh's ⟨0, by omega⟩ k (Fin.lt_def.mpr (by dsimp only; omega)); omega
      have hh_eq : ∀ k : Fin c', h' k = k.val + 1 :=
        strictMono_fin_eq_succ h' hh's hh_all1 (fun k => by have := hh'l k; omega)
      have hg_lt : ∀ j : Fin b', g' j < c' := by
        intro j; by_contra hge
        obtain ⟨i, _, hi⟩ := hmYZ' j ⟨c' - 1, by omega⟩ (by dsimp only; omega)
        have hlast := hh_eq ⟨c' - 1, by omega⟩; dsimp only at hlast; omega
      have hg_eq : ∀ j : Fin b', g' j = j.val :=
        strictMono_fin_eq_id g' hg's (fun j => by have := hg_lt j; omega)
      have hf_lt : ∀ i : Fin a', f' i < b' := by
        intro i; by_contra hge
        have hlast := hh_eq ⟨c' - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j, hj, _⟩ := hmZX' ⟨c' - 1, by omega⟩ i (by omega)
        omega
      have hf_eq : ∀ i : Fin a', f' i = i.val :=
        strictMono_fin_eq_id f' hf's (fun i => by have := hf_lt i; omega)
      refine ⟨fun i => if i.val = 0 then ⟨3 * c' - 2, by omega⟩ else ⟨i.val - 1, by omega⟩,
              fun j => ⟨c' - 1 + j.val, by omega⟩,
              fun k => ⟨2 * c' - 1 + k.val, by omega⟩, ?_, ?_, ?_⟩
      · intro i j hij; rw [hf_eq] at hij
        by_cases hi0 : i.val = 0
        · simp only [hi0, ite_true]
          have hmod : (c' - 1 + j.val + (3 * c' - 1) - (3 * c' - 2)) % (3 * c' - 1) = c' + j.val := by
            rw [show c' - 1 + j.val + (3 * c' - 1) - (3 * c' - 2) = c' + j.val by omega,
              Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
        · simp only [hi0, ite_false]
          have hmod : (c' - 1 + j.val + (3 * c' - 1) - (i.val - 1)) % (3 * c' - 1) = c' + (j.val - i.val) := by
            rw [show c' - 1 + j.val + (3 * c' - 1) - (i.val - 1) = (c' + (j.val - i.val)) + (3 * c' - 1) by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
      · intro j k hjk; rw [hg_eq] at hjk
        have hmod : (2 * c' - 1 + k.val + (3 * c' - 1) - (c' - 1 + j.val)) % (3 * c' - 1) = c' + (k.val - j.val) := by
          rw [show 2 * c' - 1 + k.val + (3 * c' - 1) - (c' - 1 + j.val) = (c' + (k.val - j.val)) + (3 * c' - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
      · intro k i hki; rw [hh_eq] at hki
        have hi0 : i.val ≠ 0 := by omega
        simp only [hi0, ite_false]
        have hmod : (i.val - 1 + (3 * c' - 1) - (2 * c' - 1 + k.val)) % (3 * c' - 1) = c' + (i.val - 1 - k.val) := by
          rw [show i.val - 1 + (3 * c' - 1) - (2 * c' - 1 + k.val) = c' + (i.val - 1 - k.val) by omega,
            Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
    rcases hge1 with hf0 | hg0 | hh0
    · obtain ⟨φY, φZ, φX, h1, h2, h3⟩ := hDDD b c a (by omega) (by omega) (by omega) g h f
        hg_le hh_le hf_le hg_sm hh_sm hf_sm (fun j k i ⟨a1, a2, a3⟩ => hTF i j k ⟨a3, a1, a2⟩)
        (fun k i hlt => by obtain ⟨j, h1, h2⟩ := hmaxZX k i hlt; exact ⟨j, h2, h1⟩)
        (fun i j hlt => by obtain ⟨k, h1, h2⟩ := hmaxXY i j hlt; exact ⟨k, h1, h2⟩) hf0
      exact ⟨a, by omega, φX, φY, φZ, h3, h1, h2⟩
    · obtain ⟨φZ, φX, φY, h1, h2, h3⟩ := hDDD c a b (by omega) (by omega) (by omega) h f g
        hh_le hf_le hg_le hh_sm hf_sm hg_sm (fun k i j ⟨a1, a2, a3⟩ => hTF i j k ⟨a2, a3, a1⟩)
        (fun i j hlt => by obtain ⟨k, h1, h2⟩ := hmaxXY i j hlt; exact ⟨k, h2, h1⟩)
        (fun j k hlt => by obtain ⟨i, h1, h2⟩ := hmaxYZ j k hlt; exact ⟨i, h2, h1⟩) hg0
      exact ⟨b, by omega, φX, φY, φZ, h2, h3, h1⟩
    · obtain ⟨φX, φY, φZ, h1, h2, h3⟩ := hDDD a b c hac hbd (by omega) f g h
        hf_le hg_le hh_le hf_sm hg_sm hh_sm hTF hmaxYZ hmaxZX hh0
      exact ⟨c, by omega, φX, φY, φZ, h1, h2, h3⟩
  · -- Now a = c - 1 (so c >= 2)
    have ha_eq : a = c - 1 := by omega
    have hc2 : 2 ≤ c := by omega
    have hh_eq : ∀ k : Fin c, h k = k.val :=
      strictMono_fin_eq_id h hh_sm (fun k => by have := hh_le k; omega)
    have hg_lt : ∀ j : Fin b, g j < c := by
      intro j; by_contra hge
      obtain ⟨i, _, hi⟩ := hmaxYZ j ⟨c - 1, by omega⟩ (by dsimp only; omega)
      have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast; omega
    by_cases hbc_eq : b = c
    · -- Shape (d-1, d, d): h k = k, g j = j, f i = i + 1 -> And(c)
      have hg_eq : ∀ j : Fin b, g j = j.val :=
        strictMono_fin_eq_id g hg_sm (fun j => by have := hg_lt j; omega)
      have hf_pos : ∀ i : Fin a, 1 ≤ f i := by
        intro i; by_contra h0
        have hg0 := hg_eq ⟨0, by omega⟩; have hh0 := hh_eq ⟨0, by omega⟩
        dsimp only at hg0 hh0
        exact hTF i ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨by omega, by omega, by omega⟩
      have hf_lt : ∀ i : Fin a, f i ≤ a := by
        intro i; by_contra hgt
        have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j, hj, _⟩ := hmaxZX ⟨c - 1, by omega⟩ i (by omega)
        omega
      have hf_eq : ∀ i : Fin a, f i = i.val + 1 := strictMono_fin_eq_succ f hf_sm hf_pos hf_lt
      refine ⟨c, by omega,
              fun i => ⟨i.val, by omega⟩,
              fun j => ⟨c - 1 + j.val, by omega⟩,
              fun k => ⟨2 * c - 1 + k.val, by omega⟩, ?_, ?_, ?_⟩
      · intro i j hij; rw [hf_eq] at hij
        have hmod : (c - 1 + j.val + (3 * c - 1) - i.val) % (3 * c - 1) = c + (j.val - (i.val + 1)) := by
          rw [show c - 1 + j.val + (3 * c - 1) - i.val = (c + (j.val - (i.val + 1))) + (3 * c - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
      · intro j k hjk; rw [hg_eq] at hjk
        have hmod : (2 * c - 1 + k.val + (3 * c - 1) - (c - 1 + j.val)) % (3 * c - 1) = c + (k.val - j.val) := by
          rw [show 2 * c - 1 + k.val + (3 * c - 1) - (c - 1 + j.val) = (c + (k.val - j.val)) + (3 * c - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
      · intro k i hki; rw [hh_eq] at hki
        have hmod : (i.val + (3 * c - 1) - (2 * c - 1 + k.val)) % (3 * c - 1) = c + (i.val - k.val) := by
          rw [show i.val + (3 * c - 1) - (2 * c - 1 + k.val) = c + (i.val - k.val) by omega,
            Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
    · -- Shape (d-1, d-1, d): h k = k, g j = j + 1, f i = i -> And(c - 1) via folding Z_0 and Z_{c-1}!
      have hb_eq : b = c - 1 := by omega
      have hg_pos : ∀ j : Fin b, 1 ≤ g j := by
        intro j; by_contra h0
        have hg0 : g ⟨0, by omega⟩ = 0 := by
          by_cases hj0 : j.val = 0
          · have : j = ⟨0, by omega⟩ := Fin.ext hj0; rw [← this]; omega
          · have := hg_sm ⟨0, by omega⟩ j (Fin.lt_def.mpr (by dsimp only; omega)); omega
        have hf_all1 : ∀ i : Fin a, 1 ≤ f i := by
          intro i; by_contra hfi0
          have hh0 := hh_eq ⟨0, by omega⟩; dsimp only at hh0
          exact hTF i ⟨0, by omega⟩ ⟨0, by omega⟩ ⟨by omega, by omega, by omega⟩
        have hf_eq1 : ∀ i : Fin a, f i = i.val + 1 :=
          strictMono_fin_eq_succ f hf_sm hf_all1 (fun i => by have := hf_le i; omega)
        have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j', hj', _⟩ := hmaxZX ⟨c - 1, by omega⟩ ⟨a - 1, by omega⟩ (by dsimp only; omega)
        have hfa := hf_eq1 ⟨a - 1, by omega⟩; dsimp only at hfa; omega
      have hg_eq : ∀ j : Fin b, g j = j.val + 1 :=
        strictMono_fin_eq_succ g hg_sm hg_pos (fun j => by have := hg_lt j; omega)
      have hf_lt : ∀ i : Fin a, f i < b := by
        intro i; by_contra hge
        have hlast := hh_eq ⟨c - 1, by omega⟩; dsimp only at hlast
        obtain ⟨j, hj, _⟩ := hmaxZX ⟨c - 1, by omega⟩ i (by omega)
        omega
      have hf_eq : ∀ i : Fin a, f i = i.val :=
        strictMono_fin_eq_id f hf_sm (fun i => by have := hf_lt i; omega)
      set d' := c - 1
      have hd'0 : d' ≠ 0 := by omega
      refine ⟨d', by omega,
              fun i => ⟨d' - 1 + i.val, by omega⟩,
              fun j => ⟨2 * d' - 1 + j.val, by omega⟩,
              fun k => if k.val = 0 then ⟨3 * d' - 2, by omega⟩
                       else if k.val = d' then ⟨d' - 1, by omega⟩
                       else ⟨k.val - 1, by omega⟩, ?_, ?_, ?_⟩
      · intro i j hij; rw [hf_eq] at hij
        have hmod : (2 * d' - 1 + j.val + (3 * d' - 1) - (d' - 1 + i.val)) % (3 * d' - 1) = d' + (j.val - i.val) := by
          rw [show 2 * d' - 1 + j.val + (3 * d' - 1) - (d' - 1 + i.val) = (d' + (j.val - i.val)) + (3 * d' - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]; omega
      · intro j k hjk; rw [hg_eq] at hjk
        have hk0 : k.val ≠ 0 := by omega
        by_cases hkd : k.val = d'
        · simp only [hkd, hd'0, ite_false, ite_true]
          have hmod : (d' - 1 + (3 * d' - 1) - (2 * d' - 1 + j.val)) % (3 * d' - 1) = 2 * d' - 1 - j.val := by
            rw [show d' - 1 + (3 * d' - 1) - (2 * d' - 1 + j.val) = 2 * d' - 1 - j.val by omega,
              Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
        · simp only [hk0, hkd, ite_false]
          have hmod : (k.val - 1 + (3 * d' - 1) - (2 * d' - 1 + j.val)) % (3 * d' - 1) = d' + (k.val - 1 - j.val) := by
            rw [show k.val - 1 + (3 * d' - 1) - (2 * d' - 1 + j.val) = d' + (k.val - 1 - j.val) by omega,
              Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
      · intro k i hki; rw [hh_eq] at hki
        have hkd : k.val ≠ d' := by omega
        by_cases hk0 : k.val = 0
        · simp only [hk0, ite_true]
          have hmod : (d' - 1 + i.val + (3 * d' - 1) - (3 * d' - 2)) % (3 * d' - 1) = d' + i.val := by
            rw [show d' - 1 + i.val + (3 * d' - 1) - (3 * d' - 2) = d' + i.val by omega,
              Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega
        · simp only [hk0, hkd, ite_false]
          have hmod : (d' - 1 + i.val + (3 * d' - 1) - (k.val - 1)) % (3 * d' - 1) = d' + (i.val - k.val) := by
            rw [show d' - 1 + i.val + (3 * d' - 1) - (k.val - 1) = (d' + (i.val - k.val)) + (3 * d' - 1) by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]; omega

lemma cjk_sym_mod {d : ℕ} (hd : 1 ≤ d) (u v : Fin (3 * d - 1))
    (h : d ≤ (v.val + (3 * d - 1) - u.val) % (3 * d - 1) ∧
      (v.val + (3 * d - 1) - u.val) % (3 * d - 1) < 2 * d) :
    d ≤ (u.val + (3 * d - 1) - v.val) % (3 * d - 1) ∧
    (u.val + (3 * d - 1) - v.val) % (3 * d - 1) < 2 * d := by
  have hu := u.isLt; have hv := v.isLt
  by_cases hle : u.val ≤ v.val
  · have e1 : (v.val + (3 * d - 1) - u.val) % (3 * d - 1) = v.val - u.val := by
      rw [show v.val + (3 * d - 1) - u.val = (v.val - u.val) + (3 * d - 1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have e2 : (u.val + (3 * d - 1) - v.val) % (3 * d - 1) = (3 * d - 1) - (v.val - u.val) := by
      rw [show u.val + (3 * d - 1) - v.val = (3 * d - 1) - (v.val - u.val) by omega,
        Nat.mod_eq_of_lt (by omega)]
    omega
  · have e1 : (v.val + (3 * d - 1) - u.val) % (3 * d - 1) = v.val + (3 * d - 1) - u.val :=
      Nat.mod_eq_of_lt (by omega)
    have e2 : (u.val + (3 * d - 1) - v.val) % (3 * d - 1) = u.val - v.val := by
      rw [show u.val + (3 * d - 1) - v.val = (u.val - v.val) + (3 * d - 1) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

lemma cjk_dual_threshold {m n : ℕ} (t : Fin m → ℕ)
    (hts : ∀ x₁ x₂ : Fin m, x₁ < x₂ → t x₁ < t x₂) :
    ∀ (y' : Fin n) (x' : Fin m),
      t ⟨m - 1 - x'.val, by have := x'.isLt; omega⟩ ≤ n - 1 - y'.val ↔
      m - #(Finset.univ.filter (fun u : Fin m => t ⟨m - 1 - u.val, by have := u.isLt; omega⟩ ≤ n - 1 - y'.val)) ≤ x'.val := by
  classical
  intro y' x'
  set S := Finset.univ.filter (fun u : Fin m => t ⟨m - 1 - u.val, by have := u.isLt; omega⟩ ≤ n - 1 - y'.val)
  have hSup : ∀ u₁ u₂ : Fin m, u₁ ∈ S → u₁ ≤ u₂ → u₂ ∈ S := by
    intro u₁ u₂ hu1 hle
    have h1 := (Finset.mem_filter.mp hu1).2
    apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_⟩
    rcases eq_or_lt_of_le hle with rfl | hlt
    · exact h1
    · have hu1l := u₁.isLt; have hu2l := u₂.isLt; have hlt' := Fin.lt_def.mp hlt
      have := hts ⟨m - 1 - u₂.val, by omega⟩ ⟨m - 1 - u₁.val, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
      omega
  have hS_eq : S = Finset.univ.filter (fun u : Fin m => m - #S ≤ u.val) := by
    have hcard_R : #(Finset.univ.filter (fun u : Fin m => m - #S ≤ u.val)) = #S := by
      have hSle : #S ≤ m := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
      refine (Finset.card_bij (fun (u : Fin m) _ => u.val - (m - #S)) ?_ ?_ ?_).trans (Finset.card_range #S)
      · intro u hu; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hu).2; have := u.isLt; omega)
      · intro u1 hu1 u2 hu2 heq
        have := (Finset.mem_filter.mp hu1).2; have := (Finset.mem_filter.mp hu2).2; exact Fin.ext (by omega)
      · intro r hr; have hr' := Finset.mem_range.mp hr
        exact ⟨⟨m - #S + r, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
    by_cases hsub : S ⊆ Finset.univ.filter (fun u : Fin m => m - #S ≤ u.val)
    · exact Finset.eq_of_subset_of_card_le hsub (by omega)
    · exfalso; obtain ⟨u0, hu0S, hu0n⟩ := Finset.not_subset.mp hsub
      have hu0lt : u0.val < m - #S := by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu0n; omega
      have hge : Finset.univ.filter (fun u : Fin m => u0.val ≤ u.val) ⊆ S :=
        fun u hu => hSup u0 u hu0S (Fin.le_def.mpr (Finset.mem_filter.mp hu).2)
      have hcard_ge : #(Finset.univ.filter (fun u : Fin m => u0.val ≤ u.val)) = m - u0.val := by
        refine (Finset.card_bij (fun (u : Fin m) _ => u.val - u0.val) ?_ ?_ ?_).trans (Finset.card_range (m - u0.val))
        · intro u hu; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hu).2; have := u.isLt; omega)
        · intro u1 hu1 u2 hu2 heq
          have := (Finset.mem_filter.mp hu1).2; have := (Finset.mem_filter.mp hu2).2; exact Fin.ext (by omega)
        · intro r hr; have hr' := Finset.mem_range.mp hr
          exact ⟨⟨u0.val + r, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
      have := Finset.card_le_card hge; omega
  have hmem := Finset.ext_iff.mp hS_eq x'
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact hmem

lemma cjk_quotient_rev {a b c : ℕ} (_ha : 1 ≤ a) (hb : 1 ≤ b) (_hc : 1 ≤ c)
    (f : Fin a → ℕ) (g : Fin b → ℕ) (h : Fin c → ℕ)
    (hfl : ∀ i, f i ≤ b) (hgl : ∀ j, g j ≤ c) (hhl : ∀ k, h k ≤ a)
    (hfs : ∀ i₁ i₂, i₁ < i₂ → f i₁ < f i₂)
    (hgs : ∀ j₁ j₂, j₁ < j₂ → g j₁ < g j₂)
    (hhs : ∀ k₁ k₂, k₁ < k₂ → h k₁ < h k₂)
    (hTF' : ∀ i j k, ¬ (f i ≤ j.val ∧ g j ≤ k.val ∧ h k ≤ i.val))
    (hXY : ∀ i j, j.val < f i → ∃ k, g j ≤ k.val ∧ h k ≤ i.val)
    (hYZ : ∀ j k, k.val < g j → ∃ i, f i ≤ j.val ∧ h k ≤ i.val)
    (hZX : ∀ k i, i.val < h k → ∃ j, f i ≤ j.val ∧ g j ≤ k.val)
    (hba : b ≤ a) (hac : a ≤ c) :
    ∃ (d : ℕ) (_ : 1 ≤ d) (φX : Fin a → Fin (3 * d - 1)) (φY : Fin b → Fin (3 * d - 1))
      (φZ : Fin c → Fin (3 * d - 1)),
      (∀ i j, f i ≤ j.val →
        d ≤ ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) ∧
        ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) < 2 * d) ∧
      (∀ j k, g j ≤ k.val →
        d ≤ ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) ∧
        ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) < 2 * d) ∧
      (∀ k i, h k ≤ i.val →
        d ≤ ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) ∧
        ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) < 2 * d) := by
  classical
  let f' : Fin b → ℕ := fun j' => a - #(Finset.univ.filter (fun i' : Fin a => f ⟨a - 1 - i'.val, by omega⟩ ≤ b - 1 - j'.val))
  let g' : Fin a → ℕ := fun i' => c - #(Finset.univ.filter (fun k' : Fin c => h ⟨c - 1 - k'.val, by omega⟩ ≤ a - 1 - i'.val))
  let h' : Fin c → ℕ := fun k' => b - #(Finset.univ.filter (fun j' : Fin b => g ⟨b - 1 - j'.val, by omega⟩ ≤ c - 1 - k'.val))
  have hf'_iff : ∀ (j' : Fin b) (i' : Fin a), f ⟨a - 1 - i'.val, by omega⟩ ≤ b - 1 - j'.val ↔ f' j' ≤ i'.val :=
    cjk_dual_threshold f hfs
  have hg'_iff : ∀ (i' : Fin a) (k' : Fin c), h ⟨c - 1 - k'.val, by omega⟩ ≤ a - 1 - i'.val ↔ g' i' ≤ k'.val :=
    cjk_dual_threshold h hhs
  have hh'_iff : ∀ (k' : Fin c) (j' : Fin b), g ⟨b - 1 - j'.val, by omega⟩ ≤ c - 1 - k'.val ↔ h' k' ≤ j'.val :=
    cjk_dual_threshold g hgs
  have hf'_le : ∀ j', f' j' ≤ a := fun _ => Nat.sub_le _ _
  have hg'_le : ∀ i', g' i' ≤ c := fun _ => Nat.sub_le _ _
  have hh'_le : ∀ k', h' k' ≤ b := fun _ => Nat.sub_le _ _
  have hf'_sm : ∀ j1 j2 : Fin b, j1 < j2 → f' j1 < f' j2 := by
    intro j1 j2 hlt
    have hle : f' j1 ≤ f' j2 := by
      apply Nat.sub_le_sub_left; apply Finset.card_le_card; intro i' hi'
      have h1 := (Finset.mem_filter.mp hi').2; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    by_contra hnot; have heq : f' j1 = f' j2 := by omega
    have hj1 := j1.isLt; have hj2 := j2.isLt; have hlt' := Fin.lt_def.mp hlt
    have hg_lt' : g ⟨b - 1 - j2.val, by omega⟩ < g ⟨b - 1 - j1.val, by omega⟩ :=
      hgs ⟨b - 1 - j2.val, by omega⟩ ⟨b - 1 - j1.val, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
    have hgj2_lt : g ⟨b - 1 - j2.val, by omega⟩ < c := by have := hgl ⟨b - 1 - j1.val, by omega⟩; omega
    obtain ⟨i, hfi, hhk⟩ := hYZ ⟨b - 1 - j1.val, by omega⟩ ⟨g ⟨b - 1 - j2.val, by omega⟩, hgj2_lt⟩ hg_lt'
    let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
    have hi_inv : (⟨a - 1 - i'.val, by omega⟩ : Fin a) = i := Fin.ext (by dsimp only [i']; omega)
    have h1 : f' j1 ≤ i'.val := (hf'_iff j1 i').mp (by rw [hi_inv]; exact hfi)
    rw [heq] at h1
    have h2 : f i ≤ b - 1 - j2.val := by have := (hf'_iff j2 i').mpr h1; rwa [hi_inv] at this
    exact hTF' i ⟨b - 1 - j2.val, by omega⟩ ⟨g ⟨b - 1 - j2.val, by omega⟩, hgj2_lt⟩ ⟨h2, le_refl _, hhk⟩
  have hg'_sm : ∀ i1 i2 : Fin a, i1 < i2 → g' i1 < g' i2 := by
    intro i1 i2 hlt
    have hle : g' i1 ≤ g' i2 := by
      apply Nat.sub_le_sub_left; apply Finset.card_le_card; intro k' hk'
      have h1 := (Finset.mem_filter.mp hk').2; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    by_contra hnot; have heq : g' i1 = g' i2 := by omega
    have hi1 := i1.isLt; have hi2 := i2.isLt; have hlt' := Fin.lt_def.mp hlt
    have hf_lt' : f ⟨a - 1 - i2.val, by omega⟩ < f ⟨a - 1 - i1.val, by omega⟩ :=
      hfs ⟨a - 1 - i2.val, by omega⟩ ⟨a - 1 - i1.val, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
    have hfi2_lt : f ⟨a - 1 - i2.val, by omega⟩ < b := by have := hfl ⟨a - 1 - i1.val, by omega⟩; omega
    obtain ⟨k, hgk, hhk⟩ := hXY ⟨a - 1 - i1.val, by omega⟩ ⟨f ⟨a - 1 - i2.val, by omega⟩, hfi2_lt⟩ hf_lt'
    let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
    have hk_inv : (⟨c - 1 - k'.val, by omega⟩ : Fin c) = k := Fin.ext (by dsimp only [k']; omega)
    have h1 : g' i1 ≤ k'.val := (hg'_iff i1 k').mp (by rw [hk_inv]; exact hhk)
    rw [heq] at h1
    have h2 : h k ≤ a - 1 - i2.val := by have := (hg'_iff i2 k').mpr h1; rwa [hk_inv] at this
    exact hTF' ⟨a - 1 - i2.val, by omega⟩ ⟨f ⟨a - 1 - i2.val, by omega⟩, hfi2_lt⟩ k ⟨le_refl _, hgk, h2⟩
  have hh'_sm : ∀ k1 k2 : Fin c, k1 < k2 → h' k1 < h' k2 := by
    intro k1 k2 hlt
    have hle : h' k1 ≤ h' k2 := by
      apply Nat.sub_le_sub_left; apply Finset.card_le_card; intro j' hj'
      have h1 := (Finset.mem_filter.mp hj').2; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    by_contra hnot; have heq : h' k1 = h' k2 := by omega
    have hk1 := k1.isLt; have hk2 := k2.isLt; have hlt' := Fin.lt_def.mp hlt
    have hh_lt' : h ⟨c - 1 - k2.val, by omega⟩ < h ⟨c - 1 - k1.val, by omega⟩ :=
      hhs ⟨c - 1 - k2.val, by omega⟩ ⟨c - 1 - k1.val, by omega⟩ (Fin.lt_def.mpr (by dsimp only; omega))
    have hhk2_lt : h ⟨c - 1 - k2.val, by omega⟩ < a := by have := hhl ⟨c - 1 - k1.val, by omega⟩; omega
    obtain ⟨j, hfj, hgj⟩ := hZX ⟨c - 1 - k1.val, by omega⟩ ⟨h ⟨c - 1 - k2.val, by omega⟩, hhk2_lt⟩ hh_lt'
    let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
    have hj_inv : (⟨b - 1 - j'.val, by omega⟩ : Fin b) = j := Fin.ext (by dsimp only [j']; omega)
    have h1 : h' k1 ≤ j'.val := (hh'_iff k1 j').mp (by rw [hj_inv]; exact hgj)
    rw [heq] at h1
    have h2 : g j ≤ c - 1 - k2.val := by have := (hh'_iff k2 j').mpr h1; rwa [hj_inv] at this
    exact hTF' ⟨h ⟨c - 1 - k2.val, by omega⟩, hhk2_lt⟩ j ⟨c - 1 - k2.val, by omega⟩ ⟨hfj, h2, le_refl _⟩
  obtain ⟨d, hd, φY', φX', φZ', h1, h2, h3⟩ := cjk_quotient_ordered hb hba hac f' g' h'
    hf'_le hg'_le hh'_le hf'_sm hg'_sm hh'_sm
    (fun j' i' k' ⟨a1, a2, a3⟩ => hTF' ⟨a - 1 - i'.val, by omega⟩ ⟨b - 1 - j'.val, by omega⟩
      ⟨c - 1 - k'.val, by omega⟩ ⟨(hf'_iff j' i').mpr a1, (hh'_iff k' j').mpr a3, (hg'_iff i' k').mpr a2⟩)
    (fun j' i' hlt => by
      have hna : b - 1 - j'.val < f ⟨a - 1 - i'.val, by omega⟩ := by
        by_contra hle; have := (hf'_iff j' i').mp (by omega); omega
      obtain ⟨k, hgk, hhk⟩ := hXY ⟨a - 1 - i'.val, by omega⟩ ⟨b - 1 - j'.val, by omega⟩ hna
      let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
      have hk_inv : (⟨c - 1 - k'.val, by omega⟩ : Fin c) = k := Fin.ext (by dsimp only [k']; omega)
      refine ⟨k', (hg'_iff i' k').mp (by rw [hk_inv]; exact hhk),
        (hh'_iff k' j').mp (by dsimp only [k']; omega)⟩)
    (fun i' k' hlt => by
      have hna : a - 1 - i'.val < h ⟨c - 1 - k'.val, by omega⟩ := by
        by_contra hle; have := (hg'_iff i' k').mp (by omega); omega
      obtain ⟨j, hfj, hgj⟩ := hZX ⟨c - 1 - k'.val, by omega⟩ ⟨a - 1 - i'.val, by omega⟩ hna
      let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
      have hj_inv : (⟨b - 1 - j'.val, by omega⟩ : Fin b) = j := Fin.ext (by dsimp only [j']; omega)
      refine ⟨j', (hf'_iff j' i').mp (by dsimp only [j']; omega),
        (hh'_iff k' j').mp (by rw [hj_inv]; exact hgj)⟩)
    (fun k' j' hlt => by
      have hna : c - 1 - k'.val < g ⟨b - 1 - j'.val, by omega⟩ := by
        by_contra hle; have := (hh'_iff k' j').mp (by omega); omega
      obtain ⟨i, hfi, hhk⟩ := hYZ ⟨b - 1 - j'.val, by omega⟩ ⟨c - 1 - k'.val, by omega⟩ hna
      let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
      have hi_inv : (⟨a - 1 - i'.val, by omega⟩ : Fin a) = i := Fin.ext (by dsimp only [i']; omega)
      refine ⟨i', (hf'_iff j' i').mp (by rw [hi_inv]; exact hfi),
        (hg'_iff i' k').mp (by dsimp only [i']; omega)⟩)
  refine ⟨d, hd, fun i => φX' ⟨a - 1 - i.val, by omega⟩, fun j => φY' ⟨b - 1 - j.val, by omega⟩,
    fun k => φZ' ⟨c - 1 - k.val, by omega⟩, ?_, ?_, ?_⟩
  · intro i j hij
    let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
    let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
    have hi_inv : (⟨a - 1 - i'.val, by omega⟩ : Fin a) = i := Fin.ext (by dsimp only [i']; omega)
    exact cjk_sym_mod hd _ _ (h1 j' i' ((hf'_iff j' i').mp (by rw [hi_inv]; dsimp only [j']; omega)))
  · intro j k hjk
    let j' : Fin b := ⟨b - 1 - j.val, by omega⟩
    let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
    have hj_inv : (⟨b - 1 - j'.val, by omega⟩ : Fin b) = j := Fin.ext (by dsimp only [j']; omega)
    exact cjk_sym_mod hd _ _ (h3 k' j' ((hh'_iff k' j').mp (by rw [hj_inv]; dsimp only [k']; omega)))
  · intro k i hki
    let k' : Fin c := ⟨c - 1 - k.val, by omega⟩
    let i' : Fin a := ⟨a - 1 - i.val, by omega⟩
    have hk_inv : (⟨c - 1 - k'.val, by omega⟩ : Fin c) = k := Fin.ext (by dsimp only [k']; omega)
    exact cjk_sym_mod hd _ _ (h2 i' k' ((hg'_iff i' k').mp (by rw [hk_inv]; dsimp only [i']; omega)))

lemma cjk_quotient_S3 {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (f : Fin a → ℕ) (g : Fin b → ℕ) (h : Fin c → ℕ)
    (hfl : ∀ i, f i ≤ b) (hgl : ∀ j, g j ≤ c) (hhl : ∀ k, h k ≤ a)
    (hfs : ∀ i₁ i₂, i₁ < i₂ → f i₁ < f i₂)
    (hgs : ∀ j₁ j₂, j₁ < j₂ → g j₁ < g j₂)
    (hhs : ∀ k₁ k₂, k₁ < k₂ → h k₁ < h k₂)
    (hTF' : ∀ i j k, ¬ (f i ≤ j.val ∧ g j ≤ k.val ∧ h k ≤ i.val))
    (hXY : ∀ i j, j.val < f i → ∃ k, g j ≤ k.val ∧ h k ≤ i.val)
    (hYZ : ∀ j k, k.val < g j → ∃ i, f i ≤ j.val ∧ h k ≤ i.val)
    (hZX : ∀ k i, i.val < h k → ∃ j, f i ≤ j.val ∧ g j ≤ k.val) :
    ∃ (d : ℕ) (_ : 1 ≤ d) (φX : Fin a → Fin (3 * d - 1)) (φY : Fin b → Fin (3 * d - 1))
      (φZ : Fin c → Fin (3 * d - 1)),
      (∀ i j, f i ≤ j.val →
        d ≤ ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) ∧
        ((φY j).val + (3 * d - 1) - (φX i).val) % (3 * d - 1) < 2 * d) ∧
      (∀ j k, g j ≤ k.val →
        d ≤ ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) ∧
        ((φZ k).val + (3 * d - 1) - (φY j).val) % (3 * d - 1) < 2 * d) ∧
      (∀ k i, h k ≤ i.val →
        d ≤ ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) ∧
        ((φX i).val + (3 * d - 1) - (φZ k).val) % (3 * d - 1) < 2 * d) := by
  by_cases h1 : a ≤ b
  · by_cases h2 : b ≤ c
    · exact cjk_quotient_ordered ha h1 h2 f g h hfl hgl hhl hfs hgs hhs hTF' hXY hYZ hZX
    · by_cases h3 : a ≤ c
      · obtain ⟨d, hd, φZ, φX, φY, p1, p2, p3⟩ := cjk_quotient_rev hc ha hb h f g hhl hfl hgl hhs hfs hgs
          (fun k i j ⟨x1, x2, x3⟩ => hTF' i j k ⟨x2, x3, x1⟩) hZX
          (fun i j hlt => by obtain ⟨k, q1, q2⟩ := hXY i j hlt; exact ⟨k, q2, q1⟩)
          (fun j k hlt => by obtain ⟨i, q1, q2⟩ := hYZ j k hlt; exact ⟨i, q2, q1⟩) h3 (by omega)
        exact ⟨d, hd, φX, φY, φZ, p2, p3, p1⟩
      · obtain ⟨d, hd, φZ, φX, φY, p1, p2, p3⟩ := cjk_quotient_ordered hc (by omega) h1 h f g
          hhl hfl hgl hhs hfs hgs (fun k i j ⟨x1, x2, x3⟩ => hTF' i j k ⟨x2, x3, x1⟩) hZX
          (fun i j hlt => by obtain ⟨k, q1, q2⟩ := hXY i j hlt; exact ⟨k, q2, q1⟩)
          (fun j k hlt => by obtain ⟨i, q1, q2⟩ := hYZ j k hlt; exact ⟨i, q2, q1⟩)
        exact ⟨d, hd, φX, φY, φZ, p2, p3, p1⟩
  · by_cases h2 : a ≤ c
    · exact cjk_quotient_rev ha hb hc f g h hfl hgl hhl hfs hgs hhs hTF' hXY hYZ hZX (by omega) h2
    · by_cases h3 : b ≤ c
      · obtain ⟨d, hd, φY, φZ, φX, p1, p2, p3⟩ := cjk_quotient_ordered hb h3 (by omega) g h f
          hgl hhl hfl hgs hhs hfs (fun j k i ⟨x1, x2, x3⟩ => hTF' i j k ⟨x3, x1, x2⟩)
          (fun j k hlt => by obtain ⟨i, q1, q2⟩ := hYZ j k hlt; exact ⟨i, q2, q1⟩)
          (fun k i hlt => by obtain ⟨j, q1, q2⟩ := hZX k i hlt; exact ⟨j, q2, q1⟩) hXY
        exact ⟨d, hd, φX, φY, φZ, p3, p1, p2⟩
      · obtain ⟨d, hd, φY, φZ, φX, p1, p2, p3⟩ := cjk_quotient_rev hb hc ha g h f hgl hhl hfl hgs hhs hfs
          (fun j k i ⟨x1, x2, x3⟩ => hTF' i j k ⟨x3, x1, x2⟩)
          (fun j k hlt => by obtain ⟨i, q1, q2⟩ := hYZ j k hlt; exact ⟨i, q2, q1⟩)
          (fun k i hlt => by obtain ⟨j, q1, q2⟩ := hZX k i hlt; exact ⟨j, q2, q1⟩) hXY (by omega) (by omega)
        exact ⟨d, hd, φX, φY, φZ, p3, p1, p2⟩

theorem chen_jin_koh_hom_andrasfai {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (h3col : G.Colorable 3)
    (h3d : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) :
    ∃ (d : ℕ) (_ : 1 ≤ d) (φ : V → Fin (3 * d - 1)),
      ∀ u v : V, G.Adj u v →
        d ≤ ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) ∧
        ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) < 2 * d := by
  classical
  obtain ⟨c3⟩ := h3col
  let col : V → Fin 3 := fun v => c3 v
  have hcol : ∀ u v : V, G.Adj u v → col u ≠ col v := fun u v h => c3.valid h
  obtain ⟨H, hGH, hHTF, hHcol, hHmax⟩ := exists_maximal_threeColorable_triangleFree G hTF col hcol
  -- Sufficient to find And(d) homomorphism for H
  suffices hH : ∃ (d : ℕ) (_ : 1 ≤ d) (φ : V → Fin (3 * d - 1)),
      ∀ u v : V, H.Adj u v →
        d ≤ ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) ∧
        ((φ v).val + (3 * d - 1) - (φ u).val) % (3 * d - 1) < 2 * d by
    obtain ⟨d, hd, φ, hφ⟩ := hH
    exact ⟨d, hd, φ, fun u v huv => hφ u v (hGH huv)⟩
  set n := Fintype.card V
  have hH3d : ∀ v : V, n < 3 * #(Finset.univ.filter (H.Adj v)) := by
    intro v
    have h1 := h3d v
    rw [Set.ncard_eq_toFinset_card'] at h1
    have hsub : (G.neighborSet v).toFinset ⊆ Finset.univ.filter (H.Adj v) := by
      intro w hw; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hGH (Set.mem_toFinset.mp hw)⟩
    have := Finset.card_le_card hsub; omega
  let P : Fin 3 → Finset V := fun c => Finset.univ.filter (fun v => col v = c)
  -- If any color class is empty, H is bipartite -> And(1) = K_2!
  by_cases h0 : P 0 = ∅
  · refine ⟨1, le_refl 1, fun v => if col v = 1 then ⟨0, by decide⟩ else ⟨1, by decide⟩, ?_⟩
    intro u v huv
    have hne := hHcol u v huv
    have hu0 : col u ≠ 0 := fun hc => Finset.notMem_empty u (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have hv0 : col v ≠ 0 := fun hc => Finset.notMem_empty v (h0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    generalize hcu : col u = cu at hne hu0 ⊢; generalize hcv : col v = cv at hne hv0 ⊢
    fin_cases cu <;> fin_cases cv <;> simp_all
  by_cases h1 : P 1 = ∅
  · refine ⟨1, le_refl 1, fun v => if col v = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩, ?_⟩
    intro u v huv
    have hne := hHcol u v huv
    have hu1 : col u ≠ 1 := fun hc => Finset.notMem_empty u (h1 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have hv1 : col v ≠ 1 := fun hc => Finset.notMem_empty v (h1 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    generalize hcu : col u = cu at hne hu1 ⊢; generalize hcv : col v = cv at hne hv1 ⊢
    fin_cases cu <;> fin_cases cv <;> simp_all
  by_cases h2 : P 2 = ∅
  · refine ⟨1, le_refl 1, fun v => if col v = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩, ?_⟩
    intro u v huv
    have hne := hHcol u v huv
    have hu2 : col u ≠ 2 := fun hc => Finset.notMem_empty u (h2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have hv2 : col v ≠ 2 := fun hc => Finset.notMem_empty v (h2 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    generalize hcu : col u = cu at hne hu2 ⊢; generalize hcv : col v = cv at hne hv2 ⊢
    fin_cases cu <;> fin_cases cv <;> simp_all
  have hP_ne : ∀ c : Fin 3, (P c).Nonempty := fun c => by
    fin_cases c
    · exact Finset.nonempty_iff_ne_empty.mpr h0
    · exact Finset.nonempty_iff_ne_empty.mpr h1
    · exact Finset.nonempty_iff_ne_empty.mpr h2
  -- Step 1: No induced 2K_2 between any two distinct color classes (6-line C_6 cap-2 proof!)
  have hno2K2 : ∀ c1 c2 : Fin 3, c1 ≠ c2 → ∀ x1 ∈ P c1, ∀ x2 ∈ P c1, ∀ y1 ∈ P c2, ∀ y2 ∈ P c2,
      H.Adj x1 y1 → H.Adj x2 y2 → ¬ H.Adj x1 y2 → ¬ H.Adj x2 y1 → False := by
    intro c1 c2 hc12 x1 hx1 x2 hx2 y1 hy1 y2 hy2 h11 h22 h12 h21
    have hcx1 : col x1 = c1 := (Finset.mem_filter.mp hx1).2
    have hcx2 : col x2 = c1 := (Finset.mem_filter.mp hx2).2
    have hcy1 : col y1 = c2 := (Finset.mem_filter.mp hy1).2
    have hcy2 : col y2 = c2 := (Finset.mem_filter.mp hy2).2
    obtain ⟨z1, hz1x, hz1y⟩ := hHmax x1 y2 (by rw [hcx1, hcy2]; exact hc12) h12
    obtain ⟨z2, hz2x, hz2y⟩ := hHmax x2 y1 (by rw [hcx2, hcy1]; exact hc12) h21
    let c3' : Fin 3 := 0 - c1 - c2
    have hc3_ne1 : c1 ≠ c3' := by dsimp only [c3']; fin_cases c1 <;> fin_cases c2 <;> first | exact (hc12 rfl).elim | decide
    have hc3_ne2 : c2 ≠ c3' := by dsimp only [c3']; fin_cases c1 <;> fin_cases c2 <;> first | exact (hc12 rfl).elim | decide
    have hc3_eq : ∀ z : V, col z ≠ c1 → col z ≠ c2 → col z = c3' := fun z hz1 hz2 =>
      fin3_third hc12 hc3_ne1 hc3_ne2 hz1 hz2
    have hcz1 : col z1 = c3' := hc3_eq z1 (by rw [← hcx1]; exact hHcol z1 x1 hz1x.symm)
      (by rw [← hcy2]; exact hHcol z1 y2 hz1y.symm)
    have hcz2 : col z2 = c3' := hc3_eq z2 (by rw [← hcx2]; exact hHcol z2 x2 hz2x.symm)
      (by rw [← hcy1]; exact hHcol z2 y1 hz2y.symm)
    let w : Fin 6 → V := ![x1, y1, z2, x2, y2, z1]
    have hw_cap2 : ∀ u : V, #(Finset.univ.filter (fun i : Fin 6 => H.Adj u (w i))) ≤ 2 := by
      intro u
      let b : Fin 6 → ℕ := fun i => if H.Adj u (w i) then 1 else 0
      have hcard : #(Finset.univ.filter (fun i : Fin 6 => H.Adj u (w i))) =
          b 0 + b 1 + b 2 + b 3 + b 4 + b 5 := by rw [Finset.card_filter, Fin.sum_univ_six]
      rw [hcard]
      have hna : ∀ {i j : Fin 6}, H.Adj (w i) (w j) → b i + b j ≤ 1 := by
        intro i j hij; dsimp only [b]
        by_cases hi : H.Adj u (w i) <;> by_cases hj : H.Adj u (w j)
        · exact (not_adj_of_cliqueFree_three hHTF hi hij hj).elim
        all_goals simp [hi, hj]
      have h01 := hna (show H.Adj (w 0) (w 1) from h11)
      have h12' := hna (show H.Adj (w 1) (w 2) from hz2y)
      have h23 := hna (show H.Adj (w 2) (w 3) from hz2x.symm)
      have h34 := hna (show H.Adj (w 3) (w 4) from h22)
      have h45 := hna (show H.Adj (w 4) (w 5) from hz1y)
      have h50 := hna (show H.Adj (w 5) (w 0) from hz1x.symm)
      have hcol_zero : ∀ {i : Fin 6}, col u = col (w i) → b i = 0 := by
        intro i hc; dsimp only [b]; rw [if_neg (fun h => hHcol u (w i) h hc)]
      have hcu : col u = c1 ∨ col u = c2 ∨ col u = c3' := by
        by_cases h1' : col u = c1
        · exact Or.inl h1'
        · by_cases h2' : col u = c2
          · exact Or.inr (Or.inl h2')
          · exact Or.inr (Or.inr (hc3_eq u h1' h2'))
      rcases hcu with hc | hc | hc
      · have : b 0 = 0 := hcol_zero (show col u = col x1 by rw [hc, hcx1])
        have : b 3 = 0 := hcol_zero (show col u = col x2 by rw [hc, hcx2])
        omega
      · have : b 1 = 0 := hcol_zero (show col u = col y1 by rw [hc, hcy1])
        have : b 4 = 0 := hcol_zero (show col u = col y2 by rw [hc, hcy2])
        omega
      · have : b 2 = 0 := hcol_zero (show col u = col z2 by rw [hc, hcz2])
        have : b 5 = 0 := hcol_zero (show col u = col z1 by rw [hc, hcz1])
        omega
    have hsum_le : ∑ i : Fin 6, #(Finset.univ.filter (H.Adj (w i))) ≤ 2 * n := by
      have hswap : ∑ i : Fin 6, #(Finset.univ.filter (H.Adj (w i))) =
          ∑ u : V, #(Finset.univ.filter (fun i : Fin 6 => H.Adj u (w i))) := by
        simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro u _
        apply Finset.sum_congr rfl; intro i _; simp [H.adj_comm]
      rw [hswap]
      calc _ ≤ ∑ _u : V, 2 := Finset.sum_le_sum (fun u _ => hw_cap2 u)
        _ = 2 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_gt : 6 * n < 3 * ∑ i : Fin 6, #(Finset.univ.filter (H.Adj (w i))) := by
      rw [Finset.mul_sum]
      have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 6))) (by simp)
        (fun i _ => hH3d (w i))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
      omega
    omega
  -- Step 2: Total inclusion ordering + opposite monotonicity of neighborhoods on each color class
  have hnbhd_total : ∀ c1 c2 : Fin 3, c1 ≠ c2 → ∀ x1 ∈ P c1, ∀ x2 ∈ P c1,
      (P c2).filter (H.Adj x1) ⊆ (P c2).filter (H.Adj x2) ∨
      (P c2).filter (H.Adj x2) ⊆ (P c2).filter (H.Adj x1) := by
    intro c1 c2 hc12 x1 hx1 x2 hx2
    by_contra hnot; push Not at hnot
    obtain ⟨h1, h2⟩ := hnot
    obtain ⟨y1, hy1, hy1n⟩ := Finset.not_subset.mp h1
    obtain ⟨y2, hy2, hy2n⟩ := Finset.not_subset.mp h2
    have hy1' := Finset.mem_filter.mp hy1; have hy2' := Finset.mem_filter.mp hy2
    exact hno2K2 c1 c2 hc12 x1 hx1 x2 hx2 y1 hy1'.1 y2 hy2'.1 hy1'.2 hy2'.2
      (fun h => hy2n (Finset.mem_filter.mpr ⟨hy2'.1, h⟩))
      (fun h => hy1n (Finset.mem_filter.mpr ⟨hy1'.1, h⟩))
  have hnbhd_eq_iff : ∀ c1 c2 c3' : Fin 3, c1 ≠ c2 → c1 ≠ c3' → c2 ≠ c3' →
      ∀ x1 ∈ P c1, ∀ x2 ∈ P c1,
      (P c2).filter (H.Adj x1) = (P c2).filter (H.Adj x2) →
      (P c3').filter (H.Adj x1) = (P c3').filter (H.Adj x2) := by
    intro c1 c2 c3' h12 h13 h23 x1 hx1 x2 hx2 heq
    have hsub : ∀ u ∈ P c1, ∀ v ∈ P c1, (P c2).filter (H.Adj u) = (P c2).filter (H.Adj v) →
        (P c3').filter (H.Adj u) ⊆ (P c3').filter (H.Adj v) := by
      intro u hu v hv huv z hz
      have hz' := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr; refine ⟨hz'.1, ?_⟩
      by_contra hna
      have hcv : col v = c1 := (Finset.mem_filter.mp hv).2
      have hcz : col z = c3' := (Finset.mem_filter.mp hz'.1).2
      obtain ⟨y, hyv, hyz⟩ := hHmax v z (by rw [hcv, hcz]; exact h13) hna
      have hcy : col y = c2 :=
        fin3_third h13 h12 h23.symm (by rw [← hcv]; exact (hHcol v y hyv).symm)
          (by rw [← hcz]; exact (hHcol z y hyz).symm)
      have hy_in : y ∈ (P c2).filter (H.Adj v) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcy⟩, hyv⟩
      rw [← huv] at hy_in
      exact not_adj_of_cliqueFree_three hHTF (Finset.mem_filter.mp hy_in).2 hyz.symm hz'.2
    exact Finset.Subset.antisymm (hsub x1 hx1 x2 hx2 heq) (hsub x2 hx2 x1 hx1 heq.symm)
  have hnbhd_opp : ∀ c1 c2 c3' : Fin 3, c1 ≠ c2 → c1 ≠ c3' → c2 ≠ c3' →
      ∀ x1 ∈ P c1, ∀ x2 ∈ P c1,
      (P c2).filter (H.Adj x2) ⊂ (P c2).filter (H.Adj x1) →
      (P c3').filter (H.Adj x1) ⊂ (P c3').filter (H.Adj x2) := by
    intro c1 c2 c3' h12 h13 h23 x1 hx1 x2 hx2 hssub
    have hsub3 : (P c3').filter (H.Adj x1) ⊆ (P c3').filter (H.Adj x2) := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      apply Finset.mem_filter.mpr; refine ⟨hz'.1, ?_⟩
      by_contra hna
      obtain ⟨y, hy1, hy2⟩ := Finset.exists_of_ssubset hssub
      have hy1' := Finset.mem_filter.mp hy1
      have hna_y : ¬ H.Adj x2 y := fun h => hy2 (Finset.mem_filter.mpr ⟨hy1'.1, h⟩)
      have hcx2 : col x2 = c1 := (Finset.mem_filter.mp hx2).2
      have hcy : col y = c2 := (Finset.mem_filter.mp hy1'.1).2
      obtain ⟨z', hz'x2, hz'y⟩ := hHmax x2 y (by rw [hcx2, hcy]; exact h12) hna_y
      have hcz' : col z' = c3' :=
        fin3_third h12 h13 h23 (by rw [← hcx2]; exact (hHcol x2 z' hz'x2).symm)
          (by rw [← hcy]; exact (hHcol y z' hz'y).symm)
      have hna_z' : ¬ H.Adj x1 z' := fun h => not_adj_of_cliqueFree_three hHTF hy1'.2 hz'y h
      exact hno2K2 c1 c3' h13 x1 hx1 x2 hx2 z hz'.1 z' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcz'⟩)
        hz'.2 hz'x2 hna_z' hna
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub3, fun heq => ?_⟩
    exact (Finset.ssubset_iff_subset_ne.mp hssub).2 (hnbhd_eq_iff c1 c3' c2 h13 h12 h23.symm x1 hx1 x2 hx2 heq).symm
  -- Step 3: Build decreasing-degree representatives for each color class c -> next color (c + 1)
  let degNext : Fin 3 → V → ℕ := fun c x => #((P (c + 1)).filter (H.Adj x))
  let degSet : Fin 3 → Finset ℕ := fun c => (P c).image (degNext c)
  let sz : Fin 3 → ℕ := fun c => #(degSet c)
  have hsz_pos : ∀ c : Fin 3, 1 ≤ sz c := fun c =>
    Finset.card_pos.mpr ((hP_ne c).image _)
  -- Decreasing enumeration of degSet c via orderIsoOfFin
  let degVal : (c : Fin 3) → Fin (sz c) → ℕ := fun c i =>
    (Finset.orderIsoOfFin (degSet c) rfl ⟨sz c - 1 - i.val, by change sz c - 1 - i.val < sz c; have := i.isLt; omega⟩).val
  have hdegVal_mem : ∀ (c : Fin 3) (i : Fin (sz c)), degVal c i ∈ degSet c := fun c i =>
    (Finset.orderIsoOfFin (degSet c) rfl ⟨sz c - 1 - i.val, by change sz c - 1 - i.val < sz c; have := i.isLt; omega⟩).property
  have hdegVal_strict : ∀ (c : Fin 3) (i j : Fin (sz c)), i < j → degVal c j < degVal c i := by
    intro c i j hij
    have hi := i.isLt; have hj := j.isLt; have hlt' := Fin.lt_def.mp hij
    have hlt : (⟨sz c - 1 - j.val, by omega⟩ : Fin (sz c)) < ⟨sz c - 1 - i.val, by omega⟩ :=
      Fin.lt_def.mpr (by dsimp only; omega)
    exact (Finset.orderIsoOfFin (degSet c) (rfl : #(degSet c) = sz c)).strictMono hlt
  have hex_rep : ∀ (c : Fin 3) (i : Fin (sz c)), ∃ x ∈ P c, degNext c x = degVal c i :=
    fun c i => Finset.mem_image.mp (hdegVal_mem c i)
  let rep : (c : Fin 3) → Fin (sz c) → V := fun c i => (hex_rep c i).choose
  have hrep_mem : ∀ (c : Fin 3) (i : Fin (sz c)), rep c i ∈ P c := fun c i => (hex_rep c i).choose_spec.1
  have hrep_deg : ∀ (c : Fin 3) (i : Fin (sz c)), degNext c (rep c i) = degVal c i :=
    fun c i => (hex_rep c i).choose_spec.2
  -- Every x ∈ P c is a full twin of rep c (idx c x)
  have hex_idx : ∀ (c : Fin 3) (x : V), x ∈ P c → ∃ i : Fin (sz c), degNext c x = degVal c i := by
    intro c x hx
    have hmem : degNext c x ∈ degSet c := Finset.mem_image_of_mem _ hx
    let j : Fin (sz c) := (Finset.orderIsoOfFin (degSet c) (rfl : #(degSet c) = sz c)).symm ⟨degNext c x, hmem⟩
    have hj := j.isLt
    refine ⟨⟨sz c - 1 - j.val, by omega⟩, ?_⟩
    dsimp only [degVal]
    have hsub : (⟨sz c - 1 - (sz c - 1 - j.val), by omega⟩ : Fin (sz c)) = j := Fin.ext (by dsimp only; omega)
    rw [hsub]
    exact (congrArg Subtype.val ((Finset.orderIsoOfFin (degSet c) (rfl : #(degSet c) = sz c)).apply_symm_apply ⟨degNext c x, hmem⟩)).symm
  let idx : (c : Fin 3) → (x : V) → x ∈ P c → Fin (sz c) := fun c x hx => (hex_idx c x hx).choose
  have hidx_deg : ∀ (c : Fin 3) (x : V) (hx : x ∈ P c), degNext c x = degNext c (rep c (idx c x hx)) := by
    intro c x hx; rw [hrep_deg]; exact (hex_idx c x hx).choose_spec
  have hsame_deg_twin : ∀ (c : Fin 3) (x1 x2 : V), x1 ∈ P c → x2 ∈ P c →
      degNext c x1 = degNext c x2 → ∀ w : V, H.Adj x1 w ↔ H.Adj x2 w := by
    intro c x1 x2 hx1 hx2 hdeq w
    have hne1 : c ≠ c + 1 := by fin_cases c <;> decide
    have hne2 : c ≠ c + 2 := by fin_cases c <;> decide
    have hne12 : c + 1 ≠ c + 2 := by fin_cases c <;> decide
    have hN1 : (P (c + 1)).filter (H.Adj x1) = (P (c + 1)).filter (H.Adj x2) := by
      rcases hnbhd_total c (c + 1) hne1 x1 hx1 x2 hx2 with hsub | hsub
      · exact Finset.eq_of_subset_of_card_le hsub (by dsimp only [degNext] at hdeq; omega)
      · exact (Finset.eq_of_subset_of_card_le hsub (by dsimp only [degNext] at hdeq; omega)).symm
    have hN2 : (P (c + 2)).filter (H.Adj x1) = (P (c + 2)).filter (H.Adj x2) :=
      hnbhd_eq_iff c (c + 1) (c + 2) hne1 hne2 hne12 x1 hx1 x2 hx2 hN1
    have hcw : col w = c ∨ col w = c + 1 ∨ col w = c + 2 := by
      generalize col w = cw; fin_cases c <;> fin_cases cw <;> simp
    rcases hcw with hc | hc | hc
    · have h1 : ¬ H.Adj x1 w := fun h => hHcol x1 w h ((Finset.mem_filter.mp hx1).2.trans hc.symm)
      have h2 : ¬ H.Adj x2 w := fun h => hHcol x2 w h ((Finset.mem_filter.mp hx2).2.trans hc.symm)
      exact ⟨fun h => (h1 h).elim, fun h => (h2 h).elim⟩
    · have hwP : w ∈ P (c + 1) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have hiff := Finset.ext_iff.mp hN1 w
      simp only [Finset.mem_filter, hwP, true_and] at hiff; exact hiff
    · have hwP : w ∈ P (c + 2) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
      have hiff := Finset.ext_iff.mp hN2 w
      simp only [Finset.mem_filter, hwP, true_and] at hiff; exact hiff
  -- Monotonicity of adjacency on representatives!
  have hrep_adj_mono : ∀ (c : Fin 3) (i₁ i₂ : Fin (sz c)), i₁ < i₂ →
      ∀ (j : Fin (sz (c + 1))), H.Adj (rep c i₂) (rep (c + 1) j) → H.Adj (rep c i₁) (rep (c + 1) j) := by
    intro c i₁ i₂ hlt j hadj
    have hne1 : c ≠ c + 1 := by fin_cases c <;> decide
    have hdlt : degNext c (rep c i₂) < degNext c (rep c i₁) := by
      rw [hrep_deg, hrep_deg]; exact hdegVal_strict c i₁ i₂ hlt
    have hsub : (P (c + 1)).filter (H.Adj (rep c i₂)) ⊆ (P (c + 1)).filter (H.Adj (rep c i₁)) := by
      rcases hnbhd_total c (c + 1) hne1 (rep c i₁) (hrep_mem c i₁) (rep c i₂) (hrep_mem c i₂) with h | h
      · have := Finset.card_le_card h; dsimp only [degNext] at hdlt; omega
      · exact h
    exact (Finset.mem_filter.mp (hsub (Finset.mem_filter.mpr ⟨hrep_mem (c + 1) j, hadj⟩))).2
  have hrep_adj_mono_right : ∀ (c : Fin 3) (j₁ j₂ : Fin (sz (c + 1))), j₁ < j₂ →
      ∀ (i : Fin (sz c)), H.Adj (rep c i) (rep (c + 1) j₁) → H.Adj (rep c i) (rep (c + 1) j₂) := by
    intro c j₁ j₂ hlt i hadj
    have hne1 : c + 1 ≠ c + 2 := by fin_cases c <;> decide
    have hne2 : c + 1 ≠ c := by fin_cases c <;> decide
    have hne3 : c + 2 ≠ c := by fin_cases c <;> decide
    have hdlt : degNext (c + 1) (rep (c + 1) j₂) < degNext (c + 1) (rep (c + 1) j₁) := by
      rw [hrep_deg, hrep_deg]; exact hdegVal_strict (c + 1) j₁ j₂ hlt
    have hssub : (P (c + 2)).filter (H.Adj (rep (c + 1) j₂)) ⊂ (P (c + 2)).filter (H.Adj (rep (c + 1) j₁)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, fun heq => by have := congrArg Finset.card heq; dsimp only [degNext] at hdlt; rw [show c + 1 + 1 = c + 2 by fin_cases c <;> decide] at hdlt; omega⟩
      rcases hnbhd_total (c + 1) (c + 2) hne1 (rep (c + 1) j₁) (hrep_mem _ j₁) (rep (c + 1) j₂) (hrep_mem _ j₂) with h | h
      · have := Finset.card_le_card h; dsimp only [degNext] at hdlt; rw [show c + 1 + 1 = c + 2 by fin_cases c <;> decide] at hdlt; omega
      · exact h
    have hopp := hnbhd_opp (c + 1) (c + 2) c hne1 hne2 hne3 (rep (c + 1) j₁) (hrep_mem _ j₁)
      (rep (c + 1) j₂) (hrep_mem _ j₂) hssub
    exact (Finset.mem_filter.mp (hopp.1 (Finset.mem_filter.mpr ⟨hrep_mem c i, hadj.symm⟩))).2.symm
  -- Threshold function thr c i := sz (c + 1) - #{j | rep c i ~ rep (c + 1) j}
  let thr : (c : Fin 3) → Fin (sz c) → ℕ := fun c i =>
    sz (c + 1) - #(Finset.univ.filter (fun j : Fin (sz (c + 1)) => H.Adj (rep c i) (rep (c + 1) j)))
  have hthr_iff : ∀ (c : Fin 3) (i : Fin (sz c)) (j : Fin (sz (c + 1))),
      H.Adj (rep c i) (rep (c + 1) j) ↔ thr c i ≤ j.val := by
    intro c i j
    set S := Finset.univ.filter (fun j' : Fin (sz (c + 1)) => H.Adj (rep c i) (rep (c + 1) j'))
    have hS_up : ∀ j₁ j₂ : Fin (sz (c + 1)), j₁ ∈ S → j₁ ≤ j₂ → j₂ ∈ S := by
      intro j₁ j₂ hj1 hle
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact hj1
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrep_adj_mono_right c j₁ j₂ hlt i (Finset.mem_filter.mp hj1).2⟩
    have hS_eq : S = Finset.univ.filter (fun j' : Fin (sz (c + 1)) => sz (c + 1) - #S ≤ j'.val) := by
      have hcard_R : #(Finset.univ.filter (fun j' : Fin (sz (c + 1)) => sz (c + 1) - #S ≤ j'.val)) = #S := by
        have hS_le : #S ≤ sz (c + 1) := by
          calc #S ≤ #(Finset.univ : Finset (Fin (sz (c + 1)))) := Finset.card_le_card (Finset.filter_subset _ _)
            _ = sz (c + 1) := by simp
        refine (Finset.card_bij (fun (j' : Fin (sz (c + 1))) _ => j'.val - (sz (c + 1) - #S)) ?_ ?_ ?_).trans (Finset.card_range #S)
        · intro j' hj'; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj').2; omega)
        · intro j₁ hj₁ j₂ hj₂ heq
          have := (Finset.mem_filter.mp hj₁).2; have := (Finset.mem_filter.mp hj₂).2; exact Fin.ext (by omega)
        · intro m hm; have hm' := Finset.mem_range.mp hm
          exact ⟨⟨sz (c + 1) - #S + m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
      by_cases hsub : S ⊆ Finset.univ.filter (fun j' : Fin (sz (c + 1)) => sz (c + 1) - #S ≤ j'.val)
      · exact Finset.eq_of_subset_of_card_le hsub (by omega)
      · exfalso
        obtain ⟨j₀, hj₀S, hj₀not⟩ := Finset.not_subset.mp hsub
        have hj₀_lt : j₀.val < sz (c + 1) - #S := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀not; omega
        have hge : Finset.univ.filter (fun j' : Fin (sz (c + 1)) => j₀.val ≤ j'.val) ⊆ S :=
          fun j' hj' => hS_up j₀ j' hj₀S (Fin.le_def.mpr (Finset.mem_filter.mp hj').2)
        have hcard_ge : #(Finset.univ.filter (fun j' : Fin (sz (c + 1)) => j₀.val ≤ j'.val)) = sz (c + 1) - j₀.val := by
          refine (Finset.card_bij (fun (j' : Fin (sz (c + 1))) _ => j'.val - j₀.val) ?_ ?_ ?_).trans (Finset.card_range (sz (c + 1) - j₀.val))
          · intro j' hj'; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj').2; omega)
          · intro j₁ hj₁ j₂ hj₂ heq; have := (Finset.mem_filter.mp hj₁).2; have := (Finset.mem_filter.mp hj₂).2; exact Fin.ext (by omega)
          · intro m hm; have hm' := Finset.mem_range.mp hm
            exact ⟨⟨j₀.val + m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
        have := Finset.card_le_card hge; omega
    have hmem := Finset.ext_iff.mp hS_eq j
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem
  have hthr_le : ∀ (c : Fin 3) (i : Fin (sz c)), thr c i ≤ sz (c + 1) := fun _ _ => Nat.sub_le _ _
  have hthr_sm : ∀ (c : Fin 3) (i₁ i₂ : Fin (sz c)), i₁ < i₂ → thr c i₁ < thr c i₂ := by
    intro c i₁ i₂ hlt
    have hdlt : degNext c (rep c i₂) < degNext c (rep c i₁) := by
      rw [hrep_deg, hrep_deg]; exact hdegVal_strict c i₁ i₂ hlt
    have hne1 : c ≠ c + 1 := by fin_cases c <;> decide
    have hssub : (P (c + 1)).filter (H.Adj (rep c i₂)) ⊂ (P (c + 1)).filter (H.Adj (rep c i₁)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, fun heq => by have := congrArg Finset.card heq; dsimp only [degNext] at hdlt; omega⟩
      rcases hnbhd_total c (c + 1) hne1 (rep c i₁) (hrep_mem c i₁) (rep c i₂) (hrep_mem c i₂) with h | h
      · have := Finset.card_le_card h; dsimp only [degNext] at hdlt; omega
      · exact h
    obtain ⟨y, hy1, hy2⟩ := Finset.exists_of_ssubset hssub
    have hy1' := Finset.mem_filter.mp hy1
    let j := idx (c + 1) y hy1'.1
    have htwin := hsame_deg_twin (c + 1) y (rep (c + 1) j) hy1'.1 (hrep_mem _ j) (hidx_deg _ y hy1'.1)
    have hadj1 : H.Adj (rep c i₁) (rep (c + 1) j) := ((htwin (rep c i₁)).mp hy1'.2.symm).symm
    have hna2 : ¬ H.Adj (rep c i₂) (rep (c + 1) j) := fun h =>
      hy2 (Finset.mem_filter.mpr ⟨hy1'.1, ((htwin (rep c i₂)).mpr h.symm).symm⟩)
    rw [hthr_iff] at hadj1 hna2; omega
  -- Helper: lift any valid quotient homomorphism (φ0, φ1, φ2) to H : SimpleGraph V!
  have hlift : ∀ (d : ℕ) (hd : 1 ≤ d)
      (φ0 : Fin (sz 0) → Fin (3 * d - 1)) (φ1 : Fin (sz 1) → Fin (3 * d - 1))
      (φ2 : Fin (sz 2) → Fin (3 * d - 1)),
      (∀ i j, thr 0 i ≤ j.val →
        d ≤ ((φ1 j).val + (3 * d - 1) - (φ0 i).val) % (3 * d - 1) ∧
        ((φ1 j).val + (3 * d - 1) - (φ0 i).val) % (3 * d - 1) < 2 * d) →
      (∀ j k, thr 1 j ≤ k.val →
        d ≤ ((φ2 k).val + (3 * d - 1) - (φ1 j).val) % (3 * d - 1) ∧
        ((φ2 k).val + (3 * d - 1) - (φ1 j).val) % (3 * d - 1) < 2 * d) →
      (∀ k i, thr 2 k ≤ i.val →
        d ≤ ((φ0 i).val + (3 * d - 1) - (φ2 k).val) % (3 * d - 1) ∧
        ((φ0 i).val + (3 * d - 1) - (φ2 k).val) % (3 * d - 1) < 2 * d) →
      ∃ (d' : ℕ) (_ : 1 ≤ d') (φ : V → Fin (3 * d' - 1)),
        ∀ u v : V, H.Adj u v →
          d' ≤ ((φ v).val + (3 * d' - 1) - (φ u).val) % (3 * d' - 1) ∧
          ((φ v).val + (3 * d' - 1) - (φ u).val) % (3 * d' - 1) < 2 * d' := by
    intro d hd φ0 φ1 φ2 h01 h12 h20
    have hsym_mod : ∀ a b : Fin (3 * d - 1),
        (d ≤ (b.val + (3 * d - 1) - a.val) % (3 * d - 1) ∧ (b.val + (3 * d - 1) - a.val) % (3 * d - 1) < 2 * d) →
        (d ≤ (a.val + (3 * d - 1) - b.val) % (3 * d - 1) ∧ (a.val + (3 * d - 1) - b.val) % (3 * d - 1) < 2 * d) := by
      intro a b ⟨hlo, hhi⟩
      have ha := a.isLt; have hb := b.isLt
      by_cases hle : a.val ≤ b.val
      · have h1 : (b.val + (3 * d - 1) - a.val) % (3 * d - 1) = b.val - a.val := by
          rw [show b.val + (3 * d - 1) - a.val = (b.val - a.val) + (3 * d - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h2 : (a.val + (3 * d - 1) - b.val) % (3 * d - 1) = (3 * d - 1) - (b.val - a.val) := by
          rw [show a.val + (3 * d - 1) - b.val = (3 * d - 1) - (b.val - a.val) by omega, Nat.mod_eq_of_lt (by omega)]
        omega
      · have h1 : (b.val + (3 * d - 1) - a.val) % (3 * d - 1) = b.val + (3 * d - 1) - a.val := Nat.mod_eq_of_lt (by omega)
        have h2 : (a.val + (3 * d - 1) - b.val) % (3 * d - 1) = a.val - b.val := by
          rw [show a.val + (3 * d - 1) - b.val = (a.val - b.val) + (3 * d - 1) by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        omega
    let φ : V → Fin (3 * d - 1) := fun v =>
      if h0 : v ∈ P 0 then φ0 (idx 0 v h0)
      else if h1 : v ∈ P 1 then φ1 (idx 1 v h1)
      else if h2 : v ∈ P 2 then φ2 (idx 2 v h2)
      else ⟨0, by omega⟩
    refine ⟨d, hd, φ, ?_⟩
    intro u v huv
    have hmem_col : ∀ w : V, w ∈ P (col w) := fun w => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have hnot_mem : ∀ w : V, ∀ c : Fin 3, col w ≠ c → w ∉ P c := fun w c hne hmem => hne (Finset.mem_filter.mp hmem).2
    have hrep_adj : ∀ c1 c2 : Fin 3, ∀ hu : u ∈ P c1, ∀ hv : v ∈ P c2,
        H.Adj (rep c1 (idx c1 u hu)) (rep c2 (idx c2 v hv)) := by
      intro c1 c2 hu hv
      have h1 := (hsame_deg_twin c1 u (rep c1 (idx c1 u hu)) hu (hrep_mem c1 _) (hidx_deg c1 u hu) v).mp huv
      exact (hsame_deg_twin c2 v (rep c2 (idx c2 v hv)) hv (hrep_mem c2 _) (hidx_deg c2 v hv) _).mp h1.symm |>.symm
    have hne := hHcol u v huv
    have hcu : col u = 0 ∨ col u = 1 ∨ col u = 2 := by generalize col u = cu; fin_cases cu <;> simp
    have hcv : col v = 0 ∨ col v = 1 ∨ col v = 2 := by generalize col v = cv; fin_cases cv <;> simp
    rcases hcu with hu | hu | hu <;> rcases hcv with hv | hv | hv
    · exact (hne (hu.trans hv.symm)).elim
    · have hu0 : u ∈ P 0 := hu ▸ hmem_col u; have hv1 : v ∈ P 1 := hv ▸ hmem_col v
      have hv0 : v ∉ P 0 := hnot_mem v 0 (by rw [hv]; decide)
      simp only [φ, hu0, hv0, hv1, dite_true, dite_false]
      exact h01 _ _ ((hthr_iff 0 _ _).mp (hrep_adj 0 1 hu0 hv1))
    · have hu0 : u ∈ P 0 := hu ▸ hmem_col u; have hv2 : v ∈ P 2 := hv ▸ hmem_col v
      have hv0 : v ∉ P 0 := hnot_mem v 0 (by rw [hv]; decide)
      have hv1 : v ∉ P 1 := hnot_mem v 1 (by rw [hv]; decide)
      simp only [φ, hu0, hv0, hv1, hv2, dite_true, dite_false]
      exact hsym_mod _ _ (h20 _ _ ((hthr_iff 2 _ _).mp (hrep_adj 0 2 hu0 hv2).symm))
    · have hu1 : u ∈ P 1 := hu ▸ hmem_col u; have hv0 : v ∈ P 0 := hv ▸ hmem_col v
      have hu0 : u ∉ P 0 := hnot_mem u 0 (by rw [hu]; decide)
      simp only [φ, hu0, hu1, hv0, dite_true, dite_false]
      exact hsym_mod _ _ (h01 _ _ ((hthr_iff 0 _ _).mp (hrep_adj 1 0 hu1 hv0).symm))
    · exact (hne (hu.trans hv.symm)).elim
    · have hu1 : u ∈ P 1 := hu ▸ hmem_col u; have hv2 : v ∈ P 2 := hv ▸ hmem_col v
      have hu0 : u ∉ P 0 := hnot_mem u 0 (by rw [hu]; decide)
      have hv0 : v ∉ P 0 := hnot_mem v 0 (by rw [hv]; decide)
      have hv1 : v ∉ P 1 := hnot_mem v 1 (by rw [hv]; decide)
      simp only [φ, hu0, hu1, hv0, hv1, hv2, dite_true, dite_false]
      exact h12 _ _ ((hthr_iff 1 _ _).mp (hrep_adj 1 2 hu1 hv2))
    · have hu2 : u ∈ P 2 := hu ▸ hmem_col u; have hv0 : v ∈ P 0 := hv ▸ hmem_col v
      have hu0 : u ∉ P 0 := hnot_mem u 0 (by rw [hu]; decide)
      have hu1 : u ∉ P 1 := hnot_mem u 1 (by rw [hu]; decide)
      simp only [φ, hu0, hu1, hu2, hv0, dite_true, dite_false]
      exact h20 _ _ ((hthr_iff 2 _ _).mp (hrep_adj 2 0 hu2 hv0))
    · have hu2 : u ∈ P 2 := hu ▸ hmem_col u; have hv1 : v ∈ P 1 := hv ▸ hmem_col v
      have hu0 : u ∉ P 0 := hnot_mem u 0 (by rw [hu]; decide)
      have hu1 : u ∉ P 1 := hnot_mem u 1 (by rw [hu]; decide)
      have hv0 : v ∉ P 0 := hnot_mem v 0 (by rw [hv]; decide)
      simp only [φ, hu0, hu1, hu2, hv0, hv1, dite_true, dite_false]
      exact hsym_mod _ _ (h12 _ _ ((hthr_iff 1 _ _).mp (hrep_adj 2 1 hu2 hv1).symm))
    · exact (hne (hu.trans hv.symm)).elim
  -- Step 4: Verify quotient axioms and apply S_3 symmetry to invoke cjk_quotient_ordered!
  have hQ_TF : ∀ (i : Fin (sz 0)) (j : Fin (sz 1)) (k : Fin (sz 2)),
      ¬ (thr 0 i ≤ j.val ∧ thr 1 j ≤ k.val ∧ thr 2 k ≤ i.val) := by
    intro i j k ⟨h1, h2, h3⟩
    exact not_adj_of_cliqueFree_three hHTF ((hthr_iff 0 i j).mpr h1) ((hthr_iff 1 j k).mpr h2)
      ((hthr_iff 2 k i).mpr h3).symm
  have hQ_max01 : ∀ (i : Fin (sz 0)) (j : Fin (sz 1)),
      j.val < thr 0 i → ∃ k : Fin (sz 2), thr 1 j ≤ k.val ∧ thr 2 k ≤ i.val := by
    intro i j hlt
    have hna : ¬ H.Adj (rep 0 i) (rep 1 j) := by rw [hthr_iff 0 i j]; omega
    have hne : col (rep 0 i) ≠ col (rep 1 j) := by
      rw [(Finset.mem_filter.mp (hrep_mem 0 i)).2, (Finset.mem_filter.mp (hrep_mem 1 j)).2]; decide
    obtain ⟨w, hwi, hwj⟩ := hHmax _ _ hne hna
    have hcw : col w = 2 := fin3_third (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
      (by decide : (1 : Fin 3) ≠ 2)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 0 i)).2]; exact (hHcol _ w hwi).symm)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 1 j)).2]; exact (hHcol _ w hwj).symm)
    have hwP : w ∈ P 2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcw⟩
    let k := idx 2 w hwP
    have htwin := hsame_deg_twin 2 w (rep 2 k) hwP (hrep_mem 2 k) (hidx_deg 2 w hwP)
    exact ⟨k, (hthr_iff 1 j k).mp ((htwin _).mp hwj.symm).symm, (hthr_iff 2 k i).mp ((htwin _).mp hwi.symm)⟩
  have hQ_max12 : ∀ (j : Fin (sz 1)) (k : Fin (sz 2)),
      k.val < thr 1 j → ∃ i : Fin (sz 0), thr 0 i ≤ j.val ∧ thr 2 k ≤ i.val := by
    intro j k hlt
    have hna : ¬ H.Adj (rep 1 j) (rep 2 k) := by rw [hthr_iff 1 j k]; omega
    have hne : col (rep 1 j) ≠ col (rep 2 k) := by
      rw [(Finset.mem_filter.mp (hrep_mem 1 j)).2, (Finset.mem_filter.mp (hrep_mem 2 k)).2]; decide
    obtain ⟨w, hwj, hwk⟩ := hHmax _ _ hne hna
    have hcw : col w = 0 := fin3_third (by decide : (1 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 0)
      (by decide : (2 : Fin 3) ≠ 0)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 1 j)).2]; exact (hHcol _ w hwj).symm)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 2 k)).2]; exact (hHcol _ w hwk).symm)
    have hwP : w ∈ P 0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcw⟩
    let i := idx 0 w hwP
    have htwin := hsame_deg_twin 0 w (rep 0 i) hwP (hrep_mem 0 i) (hidx_deg 0 w hwP)
    exact ⟨i, (hthr_iff 0 i j).mp ((htwin _).mp hwj.symm), (hthr_iff 2 k i).mp ((htwin _).mp hwk.symm).symm⟩
  have hQ_max20 : ∀ (k : Fin (sz 2)) (i : Fin (sz 0)),
      i.val < thr 2 k → ∃ j : Fin (sz 1), thr 0 i ≤ j.val ∧ thr 1 j ≤ k.val := by
    intro k i hlt
    have hna : ¬ H.Adj (rep 2 k) (rep 0 i) := by rw [hthr_iff 2 k i]; omega
    have hne : col (rep 2 k) ≠ col (rep 0 i) := by
      rw [(Finset.mem_filter.mp (hrep_mem 2 k)).2, (Finset.mem_filter.mp (hrep_mem 0 i)).2]; decide
    obtain ⟨w, hwk, hwi⟩ := hHmax _ _ hne hna
    have hcw : col w = 1 := fin3_third (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
      (by decide : (0 : Fin 3) ≠ 1)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 2 k)).2]; exact (hHcol _ w hwk).symm)
      (by rw [← (Finset.mem_filter.mp (hrep_mem 0 i)).2]; exact (hHcol _ w hwi).symm)
    have hwP : w ∈ P 1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcw⟩
    let j := idx 1 w hwP
    have htwin := hsame_deg_twin 1 w (rep 1 j) hwP (hrep_mem 1 j) (hidx_deg 1 w hwP)
    exact ⟨j, (hthr_iff 0 i j).mp ((htwin _).mp hwi.symm).symm, (hthr_iff 1 j k).mp ((htwin _).mp hwk.symm)⟩
  obtain ⟨d, hd, φ0, φ1, φ2, h01, h12, h20⟩ := cjk_quotient_S3 (hsz_pos 0) (hsz_pos 1) (hsz_pos 2)
    (thr 0) (thr 1) (thr 2) (hthr_le 0) (hthr_le 1) (hthr_le 2)
    (hthr_sm 0) (hthr_sm 1) (hthr_sm 2) hQ_TF hQ_max01 hQ_max12 hQ_max20
  exact hlift d hd φ0 φ1 φ2 h01 h12 h20

theorem not_colorable_three_of_gt_third {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (h3d : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) :
    ¬ G.Colorable 3 := fun h3col => by
  obtain ⟨d, hd, φ, hφ⟩ := chen_jin_koh_hom_andrasfai G hTF h3col h3d
  exact not_hom_andrasfai G hH (fun H hHTF hHH => five_mul_edges_lt_sq H hHTF hHH) d hd φ hφ

lemma v8_indep_subset_nbhd (J : Finset (Fin 8))
    (hJ_indep : ∀ i ∈ J, ∀ j ∈ J, ¬ (j = i + 1 ∨ j = i + 4 ∨ j = i + 7)) :
    ∃ c : Fin 8, ∀ j ∈ J, j = c + 1 ∨ j = c + 4 ∨ j = c + 7 := by
  by_contra hall
  push Not at hall
  let b : Fin 8 → ℕ := fun i => if i ∈ J then 1 else 0
  have hna : ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) → b i + b j ≤ 1 := by
    intro i j hij; dsimp only [b]
    by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
    · exact (hJ_indep i hi j hj hij).elim
    all_goals simp [hi, hj]
  have hnot_cov : ∀ c : Fin 8, b c + b (c + 2) + b (c + 3) + b (c + 5) + b (c + 6) ≥ 1 := by
    intro c
    obtain ⟨j, hjJ, hjnot⟩ := hall c
    have hj_in : j = c ∨ j = c + 2 ∨ j = c + 3 ∨ j = c + 5 ∨ j = c + 6 := by
      fin_cases c <;> fin_cases j <;> simp at hjnot ⊢
    have hbj : b j = 1 := by dsimp only [b]; simp [hjJ]
    rcases hj_in with rfl | rfl | rfl | rfl | rfl <;> omega
  have hc0 : b 0 + b 2 + b 3 + b 5 + b 6 ≥ 1 := hnot_cov 0
  have hc1 : b 1 + b 3 + b 4 + b 6 + b 7 ≥ 1 := hnot_cov 1
  have hc2 : b 2 + b 4 + b 5 + b 7 + b 0 ≥ 1 := hnot_cov 2
  have hc3 : b 3 + b 5 + b 6 + b 0 + b 1 ≥ 1 := hnot_cov 3
  have hc4 : b 4 + b 6 + b 7 + b 1 + b 2 ≥ 1 := hnot_cov 4
  have hc5 : b 5 + b 7 + b 0 + b 2 + b 3 ≥ 1 := hnot_cov 5
  have hc6 : b 6 + b 0 + b 1 + b 3 + b 4 ≥ 1 := hnot_cov 6
  have hc7 : b 7 + b 1 + b 2 + b 4 + b 5 ≥ 1 := hnot_cov 7
  have := hna 0 1 (by decide); have := hna 1 2 (by decide); have := hna 2 3 (by decide)
  have := hna 3 4 (by decide); have := hna 4 5 (by decide); have := hna 5 6 (by decide)
  have := hna 6 7 (by decide); have := hna 7 0 (by decide)
  have := hna 0 4 (by decide); have := hna 1 5 (by decide)
  have := hna 2 6 (by decide); have := hna 3 7 (by decide)
  have hle1 : ∀ i : Fin 8, b i ≤ 1 := fun i => by dsimp only [b]; split_ifs <;> omega
  have := hle1 0; have := hle1 1; have := hle1 2; have := hle1 3
  have := hle1 4; have := hle1 5; have := hle1 6; have := hle1 7
  omega

lemma exists_maximal_triangleFree {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
      ∀ u v : V, u ≠ v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w := by
  classical
  suffices h : ∀ m : ℕ, ∀ G : SimpleGraph V, G.CliqueFree 3 →
      Fintype.card (Sym2 V) - #G.edgeFinset ≤ m →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.CliqueFree 3 ∧
        ∀ u v : V, u ≠ v → ¬ H.Adj u v → ∃ w : V, H.Adj u w ∧ H.Adj v w from
    h (Fintype.card (Sym2 V) - #G.edgeFinset) G hTF (le_refl _)
  intro m
  induction m with
  | zero =>
    intro G hTF hm
    refine ⟨G, le_refl _, hTF, ?_⟩
    intro u v huv hna
    exfalso
    have hcard : #G.edgeFinset ≤ Fintype.card (Sym2 V) := by
      rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
    have heq : G.edgeFinset = Finset.univ := Finset.eq_univ_of_card _ (by omega)
    have hmem : s(u, v) ∈ G.edgeFinset := by rw [heq]; exact Finset.mem_univ _
    exact hna (SimpleGraph.mem_edgeFinset.mp hmem)
  | succ m ih =>
    intro G hTF hm
    by_cases hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w
    · exact ⟨G, le_refl _, hTF, hmax⟩
    · push Not at hmax
      obtain ⟨u, v, huv, hna, hno_cn⟩ := hmax
      let G' : SimpleGraph V := G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}
      have hGG' : G ≤ G' := le_sup_left
      have hG'_adj : ∀ a b : V, G'.Adj a b ↔ G.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
        intro a b
        simp only [G', SimpleGraph.sup_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff,
          Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
        constructor
        · rintro (h | ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), _⟩)
          · exact Or.inl h
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · rintro (h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact Or.inl h
          · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩
          · exact Or.inr ⟨Or.inr ⟨rfl, rfl⟩, huv.symm⟩
      have hG'_TF : G'.CliqueFree 3 := by
        intro s hs
        obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs.2
        have h1 : G'.Adj a b := hs.1 (by simp) (by simp) hab
        have h2 : G'.Adj b c := hs.1 (by simp) (by simp) hbc
        have h3 : G'.Adj a c := hs.1 (by simp) (by simp) hac
        rw [hG'_adj] at h1 h2 h3
        by_cases g1 : G.Adj a b
        · by_cases g2 : G.Adj b c
          · by_cases g3 : G.Adj a c
            · exact not_adj_of_cliqueFree_three hTF g1 g2 g3
            · rcases h3 with h3 | ⟨ha, hc⟩ | ⟨ha, hc⟩
              · exact g3 h3
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g1 g2.symm
              · rw [ha] at g1; rw [hc] at g2; exact hno_cn b g2.symm g1
          · rcases h2 with h2 | ⟨hb, hc⟩ | ⟨hb, hc⟩
            · exact g2 h2
            · rcases h3 with g3 | ⟨ha, _⟩ | ⟨_, hcu⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g1.symm g3.symm
              · exact hab (ha.trans hb.symm)
              · exact huv (hcu.symm.trans hc)
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨ha, _⟩
              · rw [hb] at g1; rw [hc] at g3; exact hno_cn a g3.symm g1.symm
              · exact huv (hc.symm.trans hcv)
              · exact hab (ha.trans hb.symm)
        · rcases h1 with h1 | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · exact g1 h1
          · rcases h2 with g2 | ⟨hbu, _⟩ | ⟨_, hcu⟩
            · rcases h3 with g3 | ⟨_, hcv⟩ | ⟨hau, _⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g3 g2
              · exact hbc (hb.trans hcv.symm)
              · exact huv (ha.symm.trans hau)
            · exact huv (hb.symm.trans hbu).symm
            · exact hac (ha.trans hcu.symm)
          · rcases h2 with g2 | ⟨_, hcv⟩ | ⟨hbv, _⟩
            · rcases h3 with g3 | ⟨hau, _⟩ | ⟨_, hcu⟩
              · rw [ha] at g3; rw [hb] at g2; exact hno_cn c g2 g3
              · exact huv (hau.symm.trans ha)
              · exact hbc (hb.trans hcu.symm)
            · exact hac (ha.trans hcv.symm)
            · exact huv (hb.symm.trans hbv)
      have hstrict : #G.edgeFinset < #G'.edgeFinset := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro e he
          exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.edgeSet_mono hGG' (SimpleGraph.mem_edgeFinset.mp he))
        · intro heq
          have hmem : s(u, v) ∈ G'.edgeFinset :=
            SimpleGraph.mem_edgeFinset.mpr ((hG'_adj u v).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
          rw [← heq] at hmem
          exact hna (SimpleGraph.mem_edgeFinset.mp hmem)
      have hcard_G' : #G'.edgeFinset ≤ Fintype.card (Sym2 V) := by
        rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)
      have hstep_m : Fintype.card (Sym2 V) - #G'.edgeFinset ≤ m := by omega
      obtain ⟨H, hG'H, hHTF, hHmax⟩ := ih G' hG'_TF (by convert hstep_m)
      exact ⟨H, hGG'.trans hG'H, hHTF, hHmax⟩

lemma fin5_add_1_1 (i : Fin 5) : i + 1 + 1 = i + 2 := by fin_cases i <;> decide

lemma fin5_add_1_4 (i : Fin 5) : i + 1 + 4 = i := by fin_cases i <;> decide

lemma fin5_add_2_1 (i : Fin 5) : i + 2 + 1 = i + 3 := by fin_cases i <;> decide

lemma fin5_add_3_1 (i : Fin 5) : i + 3 + 1 = i + 4 := by fin_cases i <;> decide

lemma fin5_add_4_1 (i : Fin 5) : i + 4 + 1 = i := by fin_cases i <;> decide

lemma fin5_add_4_4 (i : Fin 5) : i + 4 + 4 = i + 3 := by fin_cases i <;> decide

lemma fin5_add_2_4 (i : Fin 5) : i + 2 + 4 = i + 1 := by fin_cases i <;> decide

lemma fin5_add_3_4 (i : Fin 5) : i + 3 + 4 = i + 2 := by fin_cases i <;> decide

lemma fin5_cases_rel (r j : Fin 5) : j = r ∨ j = r + 1 ∨ j = r + 2 ∨ j = r + 3 ∨ j = r + 4 := by fin_cases r <;> fin_cases j <;> decide

lemma fin5_neg_add (k : Fin 5) : -(k + 1) + 1 = -k := by fin_cases k <;> decide

lemma fin5_neg_neg_1 (r : Fin 5) : -(-r + 1) = r + 4 := by fin_cases r <;> decide

lemma fin5_neg_neg_4 (r : Fin 5) : -(-r + 4) = r + 1 := by fin_cases r <;> decide

lemma fin5_neg_neg_2 (r : Fin 5) : -(-r + 2) = r + 3 := by fin_cases r <;> decide

lemma exists_v8_minus_e_of_edges {V : Type} {G : SimpleGraph V}
    (u0 u1 u2 u3 u4 u5 u6 u7 : V)
    (e01 : G.Adj u0 u1) (e12 : G.Adj u1 u2) (e23 : G.Adj u2 u3) (e34 : G.Adj u3 u4)
    (e45 : G.Adj u4 u5) (e56 : G.Adj u5 u6) (e67 : G.Adj u6 u7) (e70 : G.Adj u7 u0)
    (e04 : G.Adj u0 u4) (e15 : G.Adj u1 u5) (e37 : G.Adj u3 u7) :
    ∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j) := by
  refine ⟨fun k => if k = 0 then u0 else if k = 1 then u1 else if k = 2 then u2 else
    if k = 3 then u3 else if k = 4 then u4 else if k = 5 then u5 else if k = 6 then u6 else u7, ?_⟩
  intro i j hij h26 h62
  rcases hij with rfl | rfl | rfl
  · fin_cases i
    · exact e01
    · exact e12
    · exact e23
    · exact e34
    · exact e45
    · exact e56
    · exact e67
    · exact e70
  · fin_cases i
    · exact e04
    · exact e15
    · exact (h26 ⟨rfl, rfl⟩).elim
    · exact e37
    · exact e04.symm
    · exact e15.symm
    · exact (h62 ⟨rfl, rfl⟩).elim
    · exact e37.symm
  · fin_cases i
    · exact e70.symm
    · exact e01.symm
    · exact e12.symm
    · exact e23.symm
    · exact e34.symm
    · exact e45.symm
    · exact e56.symm
    · exact e67.symm

end R2

namespace R2H1R1


open Finset SimpleGraph R2

-- Band, V_8 - e present, no homomorphic image of And(4).
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.CliqueFree 3 →
    (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    (∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard) →
    ¬ G.Colorable 3 →
    (¬ ∃ (o m : Fin 5 → V) (z : V), ∀ i : Fin 5, G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧
      G.Adj (m i) (o (i + 4)) ∧ G.Adj z (m i)) →
    (∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j)) →
    (¬ ∃ φ : Fin 11 → V, ∀ i j : Fin 11, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) →
      G.Adj (φ i) (φ j)) →
    False

-- Band, homomorphic image of And(4) present.
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.CliqueFree 3 →
    (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    (∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard) →
    ¬ G.Colorable 3 →
    (¬ ∃ (o m : Fin 5 → V) (z : V), ∀ i : Fin 5, G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧
      G.Adj (m i) (o (i + 4)) ∧ G.Adj z (m i)) →
    (∃ φ : Fin 11 → V, ∀ i j : Fin 11, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) →
      G.Adj (φ i) (φ j)) →
    False

/-- Band Step 3 (adapted from `colorable_three_of_no_v8_minus_e` of reduction R2, iskamag, PR #1798):
    maximal triangle-free + `5α < 2n` + `35δ > 12n` + no `V_8 - (2, 6)` implies 3-colourable. -/
theorem colorable_three_of_no_v8_minus_e_band {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h5a : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) → 5 * #I < 2 * Fintype.card V)
    (h35d : ∀ x : V, 12 * Fintype.card V < 35 * (G.neighborSet x).ncard)
    (hnoV8 : ¬ ∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j))
    (hshort_walk : ∀ (W : Type) [Fintype W] (H : SimpleGraph W),
      H.CliqueFree 3 → ¬ H.Colorable 2 →
      ∃ L : ℕ, Odd L ∧ 5 ≤ L ∧
        (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → W, g L' = g 0 ∧ ∀ i < L', H.Adj (g i) (g (i + 1))) ∧
        ∃ f : ℕ → W, f L = f 0 ∧ (∀ i < L, H.Adj (f i) (f (i + 1))) ∧
          (∀ i j, i < j → j < L → f i ≠ f j) ∧
          (∀ i j, i + 2 ≤ j → j < L → j - i ≤ L - 2 → ¬ H.Adj (f i) (f j)))
    (hshort_deg2 : ∀ (W : Type) [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      H.CliqueFree 3 → ∀ {L : ℕ}, Odd L → 5 ≤ L →
      (∀ L' < L, Odd L' → ¬ ∃ g : ℕ → W, g L' = g 0 ∧ ∀ i < L', H.Adj (g i) (g (i + 1))) →
      ∀ {f : ℕ → W}, f L = f 0 → (∀ i < L, H.Adj (f i) (f (i + 1))) →
      ∀ w : W, #((Finset.range L).filter (fun i => H.Adj w (f i))) ≤ 2) :
    G.Colorable 3 := by
  classical
  by_contra hnot3
  set n := Fintype.card V
  have hn_pos : 0 < n := by
    by_contra h0
    have hE : IsEmpty V := Fintype.card_eq_zero_iff.mp (by omega)
    exact hnot3 ⟨SimpleGraph.Coloring.mk (fun x => (hE.false x).elim)
      (fun {a _} _ => (hE.false a).elim)⟩
  obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp hn_pos
  have hdeg : ∀ x : V, 12 * n < 35 * #(Finset.univ.filter (G.Adj x)) := by
    intro x
    have h1 := h35d x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have h2 : (G.neighborSet x).toFinset = Finset.univ.filter (G.Adj x) := by ext y; simp
    rwa [h2] at h1
  have hdeg_up : ∀ x : V, 5 * #(Finset.univ.filter (G.Adj x)) < 2 * n := fun x =>
    h5a _ (fun u hu v hv huv => not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hu).2 huv
      (Finset.mem_filter.mp hv).2)
  -- Substep 3a: Pick a shortest odd cycle C of length L in G - N(v₀); force L = 5
  let I : Finset V := Finset.univ.filter (G.Adj v₀)
  have h5I : 5 * #I < 2 * n := hdeg_up v₀
  let S : Set V := {w : V | w ∉ I}
  let H : SimpleGraph S := G.induce S
  have hH_TF : H.CliqueFree 3 := by
    intro t ht
    apply hTF (t.image Subtype.val)
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      exact ht.1 ha hb (fun hab => hxy (congrArg Subtype.val hab))
    · rw [Finset.card_image_of_injective _ Subtype.val_injective, ht.2]
  have hH_not2 : ¬ H.Colorable 2 := by
    rintro ⟨c2⟩
    apply hnot3
    refine ⟨SimpleGraph.Coloring.mk (fun w =>
      if hw : w ∈ I then (2 : Fin 3) else ⟨(c2 ⟨w, hw⟩).val, by have := (c2 ⟨w, hw⟩).isLt; omega⟩) ?_⟩
    intro a b hab
    by_cases ha : a ∈ I <;> by_cases hb : b ∈ I
    · exfalso
      exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp ha).2 hab (Finset.mem_filter.mp hb).2
    · simp only [ha, hb, dite_true, dite_false]
      intro heq
      have hval := congrArg Fin.val heq
      have hlt := (c2 ⟨b, hb⟩).isLt
      dsimp only at hval; omega
    · simp only [ha, hb, dite_true, dite_false]
      intro heq
      have hval := congrArg Fin.val heq
      have hlt := (c2 ⟨a, ha⟩).isLt
      dsimp only at hval; omega
    · simp only [ha, hb, dite_false]
      intro heq
      have hval := congrArg Fin.val heq
      dsimp only at hval
      exact c2.valid (show H.Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab) (Fin.ext hval)
  obtain ⟨L, hL_odd, hL5, hL_min, fH, hfH_loop, hfH_adj, _, _⟩ := hshort_walk S H hH_TF hH_not2
  let f : ℕ → V := fun i => (fH i).val
  have hf_loop : f L = f 0 := congrArg Subtype.val hfH_loop
  have hf_adj : ∀ i < L, G.Adj (f i) (f (i + 1)) := fun i hi => hfH_adj i hi
  have hf_notI : ∀ i : ℕ, f i ∉ I := fun i => (fH i).property
  have hL_eq5 : L = 5 := by
    have hdeg_out : ∀ w : V, w ∉ I → #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ 2 := fun w hw =>
      hshort_deg2 S H hH_TF hL_odd hL5 hL_min hfH_loop hfH_adj ⟨w, hw⟩
    have hdeg_in : ∀ w : V, 2 * #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ L - 1 := by
      intro w
      set T := (Finset.range L).filter (fun i => G.Adj w (f i))
      have hinj : Set.InjOn (fun i : ℕ => (i + 1) % L) (T : Set ℕ) := by
        intro a ha b hb heq
        dsimp only at heq
        have haL := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
        have hbL := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
        by_cases ha1 : a + 1 < L <;> by_cases hb1 : b + 1 < L
        · rw [Nat.mod_eq_of_lt ha1, Nat.mod_eq_of_lt hb1] at heq; omega
        · rw [Nat.mod_eq_of_lt ha1, show b + 1 = L by omega, Nat.mod_self] at heq; omega
        · rw [show a + 1 = L by omega, Nat.mod_self, Nat.mod_eq_of_lt hb1] at heq; omega
        · omega
      have hdisj : Disjoint T (T.image (fun i => (i + 1) % L)) := by
        rw [Finset.disjoint_left]
        intro j hjT hjIm
        obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hjIm
        have hiL := Finset.mem_range.mp (Finset.mem_filter.mp hiT).1
        have hwi := (Finset.mem_filter.mp hiT).2
        have hwj := (Finset.mem_filter.mp hjT).2
        by_cases hi1 : i + 1 < L
        · rw [Nat.mod_eq_of_lt hi1] at hwj
          exact not_adj_of_cliqueFree_three hTF hwi (hf_adj i hiL) hwj
        · rw [show i + 1 = L by omega, Nat.mod_self] at hwj
          have hadj := hf_adj i hiL
          rw [show i + 1 = L by omega, hf_loop] at hadj
          exact not_adj_of_cliqueFree_three hTF hwi hadj hwj
      have hsub : T ∪ T.image (fun i => (i + 1) % L) ⊆ Finset.range L := by
        refine Finset.union_subset (Finset.filter_subset _ _) ?_
        intro j hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
      have h2T : 2 * #T ≤ L := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj, Finset.card_range] at h1
        omega
      obtain ⟨m, hm⟩ := hL_odd
      omega
    have hsum_swap : ∑ i ∈ Finset.range L, #(Finset.univ.filter (G.Adj (f i))) =
        ∑ w : V, #((Finset.range L).filter (fun i => G.Adj w (f i))) := by
      simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro w _
      apply Finset.sum_congr rfl; intro i _; simp [G.adj_comm]
    have hsum_up : 2 * ∑ i ∈ Finset.range L, #(Finset.univ.filter (G.Adj (f i))) ≤
        4 * (n - #I) + (L - 1) * #I := by
      rw [hsum_swap]
      have hpart : ∑ w : V, #((Finset.range L).filter (fun i => G.Adj w (f i))) =
          ∑ w ∈ Finset.univ \ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) +
          ∑ w ∈ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) := by
        rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_of_subset (Finset.subset_univ I)]
      have h1 : ∑ w ∈ Finset.univ \ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ 2 * (n - #I) := by
        calc _ ≤ ∑ _w ∈ Finset.univ \ I, 2 := Finset.sum_le_sum (fun w hw => hdeg_out w (Finset.mem_sdiff.mp hw).2)
          _ = #(Finset.univ \ I) * 2 := by rw [Finset.sum_const, smul_eq_mul]
          _ = 2 * (n - #I) := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ, mul_comm]
      have h2 : 2 * ∑ w ∈ I, #((Finset.range L).filter (fun i => G.Adj w (f i))) ≤ (L - 1) * #I := by
        rw [Finset.mul_sum]
        calc _ ≤ ∑ _w ∈ I, (L - 1) := Finset.sum_le_sum (fun w _ => hdeg_in w)
          _ = (L - 1) * #I := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    have hsum_lo : 12 * n * L < 35 * ∑ i ∈ Finset.range L, #(Finset.univ.filter (G.Adj (f i))) := by
      rw [Finset.mul_sum]
      have hlt := Finset.sum_lt_sum_of_nonempty (s := Finset.range L) (by rw [Finset.nonempty_range_iff]; omega)
        (fun i _ => hdeg (f i))
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm] at hlt
      exact hlt
    have hI_le : #I ≤ n := (Finset.card_le_card (Finset.subset_univ I)).trans (by simp [n])
    have h4n : 4 * (n - #I) + (L - 1) * #I = 4 * n + (L - 5) * #I := by
      zify [hI_le, hL5, show 1 ≤ L by omega]; ring
    rw [h4n] at hsum_up
    have hcomb : 120 * n * L < 700 * n + 35 * (L - 5) * (2 * n) := by
      have hmul : (L - 5) * (5 * #I) ≤ (L - 5) * (2 * n) := Nat.mul_le_mul_left (L - 5) (by omega)
      nlinarith only [hsum_lo, hsum_up, hmul]
    have hLlt : 120 * L < 700 + 70 * (L - 5) := by nlinarith only [hcomb, hn_pos]
    obtain ⟨m, hm⟩ := hL_odd
    omega
  -- Helper: build a V_8 - (2, 6) contradiction from 8 vertices and 11 edges
  have hV8_contra : ∀ (u0 u1 u2 u3 u4 u5 u6 u7 : V),
      G.Adj u0 u1 → G.Adj u1 u2 → G.Adj u2 u3 → G.Adj u3 u4 →
      G.Adj u4 u5 → G.Adj u5 u6 → G.Adj u6 u7 → G.Adj u7 u0 →
      G.Adj u0 u4 → G.Adj u1 u5 → G.Adj u3 u7 → False :=
    fun u0 u1 u2 u3 u4 u5 u6 u7 e01 e12 e23 e34 e45 e56 e67 e70 e04 e15 e37 =>
      hnoV8 (exists_v8_minus_e_of_edges u0 u1 u2 u3 u4 u5 u6 u7 e01 e12 e23 e34 e45 e56 e67 e70 e04 e15 e37)
  -- Shared bound: for any 5-cycle c, the set B of vertices outside A_0 ∪ ... ∪ A_4 has 7 * #B < 2 * n
  have hB_bound_any : ∀ (c : Fin 5 → V), (∀ i : Fin 5, G.Adj (c i) (c (i + 1))) →
      7 * #(Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4))))) < 2 * n := by
    intro c hc_adj
    let B : Finset V := Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4))))
    have hpt : ∀ w : V, (if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i))) ≤ 2 := by
      intro w
      let b : Fin 5 → ℕ := fun i => if G.Adj w (c i) then 1 else 0
      have hcard : #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i))) =
          b 0 + b 1 + b 2 + b 3 + b 4 := by rw [Finset.card_filter, Fin.sum_univ_five]
      rw [hcard]
      have hna : ∀ i : Fin 5, b i + b (i + 1) ≤ 1 := by
        intro i; dsimp only [b]
        by_cases h1 : G.Adj w (c i) <;> by_cases h2 : G.Adj w (c (i + 1))
        · exact (not_adj_of_cliqueFree_three hTF h1 (hc_adj i) h2).elim
        all_goals simp [h1, h2]
      have h01 : b 0 + b 1 ≤ 1 := hna 0
      have h12 : b 1 + b 2 ≤ 1 := hna 1
      have h23 : b 2 + b 3 ≤ 1 := hna 2
      have h34 : b 3 + b 4 ≤ 1 := hna 3
      have h40 : b 4 + b 0 ≤ 1 := hna 4
      by_cases hwB : w ∈ B
      · simp only [hwB, if_true]
        have hnotA : ∀ i : Fin 5, b (i + 1) + b (i + 4) ≤ 1 := by
          intro i; dsimp only [b]
          by_cases h1 : G.Adj w (c (i + 1)) <;> by_cases h2 : G.Adj w (c (i + 4))
          · exfalso; exact (Finset.mem_filter.mp hwB).2 i ⟨h1, h2⟩
          all_goals simp [h1, h2]
        have : b 1 + b 4 ≤ 1 := hnotA 0
        have : b 2 + b 0 ≤ 1 := hnotA 1
        have : b 3 + b 1 ≤ 1 := hnotA 2
        have : b 4 + b 2 ≤ 1 := hnotA 3
        have : b 0 + b 3 ≤ 1 := hnotA 4
        omega
      · simp only [hwB, if_false, zero_add]; omega
    have hsum_le : #B + ∑ i : Fin 5, #(Finset.univ.filter (G.Adj (c i))) ≤ 2 * n := by
      have h1 : ∑ w : V, ((if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i)))) ≤ 2 * n := by
        calc _ ≤ ∑ _w : V, 2 := Finset.sum_le_sum (fun w _ => hpt w)
          _ = 2 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      have h2 : ∑ w : V, ((if w ∈ B then 1 else 0) + #(Finset.univ.filter (fun i : Fin 5 => G.Adj w (c i)))) =
          #B + ∑ i : Fin 5, #(Finset.univ.filter (G.Adj (c i))) := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
        · simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      omega
    have hsum_gt : 60 * n < 35 * ∑ i : Fin 5, #(Finset.univ.filter (G.Adj (c i))) := by
      rw [Finset.mul_sum]
      have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin 5))) (by simp)
        (fun i _ => hdeg (c i))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
      omega
    change 7 * #B < 2 * n
    omega
  -- Helper: for ANY 5-cycle c avoiding N(v₀), prove (P1), (P2) and finish when v₀ hits A_r & avoids A_{r+3}!
  have hfinish : ∀ (c : Fin 5 → V), (∀ i : Fin 5, G.Adj (c i) (c (i + 1))) →
      (∀ i : Fin 5, ¬ G.Adj v₀ (c i)) →
      ∀ (r : Fin 5) (w₀ : V), G.Adj w₀ (c (r + 1)) → G.Adj w₀ (c (r + 4)) → G.Adj v₀ w₀ →
      (∀ w : V, G.Adj w (c (r + 4)) → G.Adj w (c (r + 2)) → ¬ G.Adj v₀ w) → False := by
    intro c hc_adj hv0_c r w₀ hw01 hw04 hv0w0 hno_r3
    let A : Fin 5 → Finset V := fun i => Finset.univ.filter (fun w => G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4)))
    let B : Finset V := Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4))))
    have hB_bound : 7 * #B < 2 * n := hB_bound_any c hc_adj
    -- (P1): No vertex x hits both A i and A (i + 1)
    have hP1 : ∀ (i : Fin 5) (x y1 y2 : V), y1 ∈ A i → y2 ∈ A (i + 1) →
        G.Adj x y1 → G.Adj x y2 → False := by
      intro i x y1 y2 hy1 hy2 hxy1 hxy2
      have ⟨h1a, h1b⟩ := (Finset.mem_filter.mp hy1).2
      have ⟨h2a, h2b⟩ := (Finset.mem_filter.mp hy2).2
      rw [fin5_add_1_1] at h2a
      rw [fin5_add_1_4] at h2b
      have e45 : G.Adj (c (i + 1)) (c (i + 2)) := by have h := hc_adj (i + 1); rwa [fin5_add_1_1] at h
      have e56 : G.Adj (c (i + 2)) (c (i + 3)) := by have h := hc_adj (i + 2); rwa [fin5_add_2_1] at h
      have e67 : G.Adj (c (i + 3)) (c (i + 4)) := by have h := hc_adj (i + 3); rwa [fin5_add_3_1] at h
      have e70 : G.Adj (c (i + 4)) (c i) := by have h := hc_adj (i + 4); rwa [fin5_add_4_1] at h
      exact hV8_contra (c i) y2 x y1 (c (i + 1)) (c (i + 2)) (c (i + 3)) (c (i + 4))
        h2b.symm hxy2.symm hxy1 h1a e45 e56 e67 e70 (hc_adj i) h2a h1b
    -- (P2): No edge (a, b) with a hitting A (i + 4) and A (i + 1) and b hitting A (i + 1)
    have hP2 : ∀ (i : Fin 5) (a b u v' y : V), u ∈ A (i + 4) → v' ∈ A (i + 1) → y ∈ A (i + 1) →
        G.Adj a u → G.Adj a v' → G.Adj a b → G.Adj b y → False := by
      intro i a b u v' y hu hv' hy hau hav' hab hby
      have ⟨hua, hub⟩ := (Finset.mem_filter.mp hu).2
      have ⟨hva, hvb⟩ := (Finset.mem_filter.mp hv').2
      have ⟨hya, hyb⟩ := (Finset.mem_filter.mp hy).2
      rw [fin5_add_4_1] at hua
      rw [fin5_add_4_4] at hub
      rw [fin5_add_1_1] at hva hya
      rw [fin5_add_1_4] at hvb hyb
      have e23 : G.Adj (c (i + 3)) (c (i + 2)) := by have h := (hc_adj (i + 2)).symm; rwa [fin5_add_2_1] at h
      exact hV8_contra (c i) u (c (i + 3)) (c (i + 2)) v' a b y
        hua.symm hub e23 hva.symm hav'.symm hab hby hyb hvb.symm hau.symm hya.symm
    -- Pick common neighbor z₀ of v₀ and c r via maximality
    have hv0_ne : v₀ ≠ c r := by
      intro heq; rw [heq] at hv0_c; exact hv0_c (r + 1) (hc_adj r)
    obtain ⟨z₀, hv0z0, hcrz0⟩ := hmax v₀ (c r) hv0_ne (hv0_c r)
    have hcrA : c r ∈ A r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc_adj r, by
      have h := (hc_adj (r + 4)).symm; rwa [fin5_add_4_1] at h⟩
    have hw0A : w₀ ∈ A r := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw01, hw04⟩
    have hw0A4 : w₀ ∈ A (r + 4 + 1) := by rw [fin5_add_4_1]; exact hw0A
    have hcrA4 : c r ∈ A (r + 4 + 1) := by rw [fin5_add_4_1]; exact hcrA
    -- Both N(v₀) and N(z₀) lie inside N(c (r + 1)) ∪ B!
    have hsub_v0 : Finset.univ.filter (G.Adj v₀) ⊆ Finset.univ.filter (G.Adj (c (r + 1))) ∪ B := by
      intro w hw
      have hv0w := (Finset.mem_filter.mp hw).2
      by_cases hwB : w ∈ B
      · exact Finset.mem_union_right _ hwB
      · have hexA : ∃ j : Fin 5, w ∈ A j := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => hnone j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩)
        obtain ⟨j, hwAj⟩ := hexA
        rcases fin5_cases_rel r j with rfl | rfl | rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hwAj).2.1.symm⟩)
        · exact (hP1 r v₀ w₀ w hw0A hwAj hv0w0 hv0w).elim
        · have h2 := (Finset.mem_filter.mp hwAj).2.2
          rw [fin5_add_2_4] at h2
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.symm⟩)
        · have ⟨h3a, h3b⟩ := (Finset.mem_filter.mp hwAj).2
          rw [fin5_add_3_1] at h3a
          rw [fin5_add_3_4] at h3b
          exact (hno_r3 w h3a h3b hv0w).elim
        · exact (hP1 (r + 4) v₀ w w₀ hwAj hw0A4 hv0w hv0w0).elim
    have hsub_z0 : Finset.univ.filter (G.Adj z₀) ⊆ Finset.univ.filter (G.Adj (c (r + 1))) ∪ B := by
      intro w hw
      have hz0w := (Finset.mem_filter.mp hw).2
      by_cases hwB : w ∈ B
      · exact Finset.mem_union_right _ hwB
      · have hexA : ∃ j : Fin 5, w ∈ A j := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j hj => hnone j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩)
        obtain ⟨j, hwAj⟩ := hexA
        rcases fin5_cases_rel r j with rfl | rfl | rfl | rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hwAj).2.1.symm⟩)
        · exact (hP1 r z₀ (c r) w hcrA hwAj hcrz0.symm hz0w).elim
        · have h2 := (Finset.mem_filter.mp hwAj).2.2
          rw [fin5_add_2_4] at h2
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2.symm⟩)
        · have hwA4 : w ∈ A (r + 4 + 4) := by rw [fin5_add_4_4]; exact hwAj
          exact (hP2 (r + 4) z₀ v₀ w (c r) w₀ hwA4 hcrA4 hw0A4 hz0w hcrz0.symm hv0z0.symm hv0w0).elim
        · exact (hP1 (r + 4) z₀ w (c r) hwAj hcrA4 hz0w hcrz0.symm).elim
    have hdisj_vz : Disjoint (Finset.univ.filter (G.Adj v₀)) (Finset.univ.filter (G.Adj z₀)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      exact not_adj_of_cliqueFree_three hTF hv0z0 (Finset.mem_filter.mp hw2).2 (Finset.mem_filter.mp hw1).2
    have hcard_sum : #(Finset.univ.filter (G.Adj v₀)) + #(Finset.univ.filter (G.Adj z₀)) ≤
        #(Finset.univ.filter (G.Adj (c (r + 1)))) + #B := by
      rw [← Finset.card_union_of_disjoint hdisj_vz]
      exact (Finset.card_le_card (Finset.union_subset hsub_v0 hsub_z0)).trans (Finset.card_union_le _ _)
    have hd_v0 := hdeg v₀
    have hd_z0 := hdeg z₀
    have hd_up := hdeg_up (c (r + 1))
    omega
  -- Instantiate c : Fin 5 -> V from the shortest 5-cycle f
  let c : Fin 5 → V := fun i => f i.val
  have hc_adj : ∀ i : Fin 5, G.Adj (c i) (c (i + 1)) := by
    intro i; fin_cases i
    · exact hf_adj 0 (by omega)
    · exact hf_adj 1 (by omega)
    · exact hf_adj 2 (by omega)
    · exact hf_adj 3 (by omega)
    · have h4 := hf_adj 4 (by omega)
      rw [show 4 + 1 = L by omega, hf_loop] at h4
      exact h4
  have hv0_c : ∀ i : Fin 5, ¬ G.Adj v₀ (c i) := fun i h =>
    hf_notI i.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  -- Either v₀ hits some A_r (then orient c so v₀ avoids A_{r+3}) or N(v₀) ⊆ B (contradicting 7 * #B < 2n)!
  by_cases hex : ∃ (r : Fin 5) (w₀ : V), G.Adj w₀ (c (r + 1)) ∧ G.Adj w₀ (c (r + 4)) ∧ G.Adj v₀ w₀
  · obtain ⟨r, w₀, hw01, hw04, hv0w0⟩ := hex
    by_cases hhit3 : ∃ w₃ : V, G.Adj w₃ (c (r + 4)) ∧ G.Adj w₃ (c (r + 2)) ∧ G.Adj v₀ w₃
    · -- v₀ hits A_{r+3}, so by (P1) it avoids A_{r+2}; reverse c to c'(k) := c(-k)!
      obtain ⟨w₃, hw34, hw32, hv0w3⟩ := hhit3
      let c' : Fin 5 → V := fun k => c (-k)
      have hc'_adj : ∀ k : Fin 5, G.Adj (c' k) (c' (k + 1)) := fun k => by
        dsimp only [c']
        have h := (hc_adj (-(k + 1))).symm
        rwa [fin5_neg_add] at h
      have hv0_c' : ∀ k : Fin 5, ¬ G.Adj v₀ (c' k) := fun k => hv0_c (-k)
      apply hfinish c' hc'_adj hv0_c' (-r) w₀
        (by dsimp only [c']; rwa [fin5_neg_neg_1])
        (by dsimp only [c']; rwa [fin5_neg_neg_4])
        hv0w0
      intro w hw1 hw2 hv0w
      dsimp only [c'] at hw1 hw2
      rw [fin5_neg_neg_4] at hw1
      rw [fin5_neg_neg_2] at hw2
      have e45 : G.Adj (c (r + 3)) (c (r + 4)) := by have h := hc_adj (r + 3); rwa [fin5_add_3_1] at h
      have e56 : G.Adj (c (r + 4)) (c r) := by have h := hc_adj (r + 4); rwa [fin5_add_4_1] at h
      have e70 : G.Adj (c (r + 1)) (c (r + 2)) := by have h := hc_adj (r + 1); rwa [fin5_add_1_1] at h
      have e04 : G.Adj (c (r + 2)) (c (r + 3)) := by have h := hc_adj (r + 2); rwa [fin5_add_2_1] at h
      exact hV8_contra (c (r + 2)) w₃ v₀ w (c (r + 3)) (c (r + 4)) (c r) (c (r + 1))
        hw32.symm hv0w3.symm hv0w hw2 e45 e56 (hc_adj r) e70 e04 hw34 hw1
    · push Not at hhit3
      exact hfinish c hc_adj hv0_c r w₀ hw01 hw04 hv0w0 hhit3
  · -- N(v₀) ⊆ B, contradicting 12n < 35 * d(v₀) ≤ 35 * #B < 10n!
    push Not at hex
    have hB_bound := hB_bound_any c hc_adj
    have hsubB : Finset.univ.filter (G.Adj v₀) ⊆
        Finset.univ.filter (fun w => ∀ i : Fin 5, ¬ (G.Adj w (c (i + 1)) ∧ G.Adj w (c (i + 4)))) := by
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i ⟨h1, h2⟩ => hex i w h1 h2 (Finset.mem_filter.mp hw).2⟩
    have hleB := Finset.card_le_card hsubB
    have hdv0 := hdeg v₀
    omega

/-- The Grötzsch independent-set weight bound as a finite Boolean check (2^11 cases, kernel `decide`):
    weights 3 (outer 5-cycle), 2 (inner vertices), 4 (apex); every independent set weighs at most 10. -/
theorem grotzsch_bool : ∀ s0 s1 s2 s3 s4 t0 t1 t2 t3 t4 u : Bool,
    (!(s0 && s1) && !(s1 && s2) && !(s2 && s3) && !(s3 && s4) && !(s4 && s0) &&
     !(t0 && s1) && !(t0 && s4) && !(t1 && s2) && !(t1 && s0) && !(t2 && s3) && !(t2 && s1) &&
     !(t3 && s4) && !(t3 && s2) && !(t4 && s0) && !(t4 && s3) &&
     !(u && t0) && !(u && t1) && !(u && t2) && !(u && t3) && !(u && t4)) = true →
    3 * (s0.toNat + s1.toNat + s2.toNat + s3.toNat + s4.toNat) +
      2 * (t0.toNat + t1.toNat + t2.toNat + t3.toNat + t4.toNat) + 4 * u.toNat ≤ 10 := by
  decide

/-- Fractional-clique bound for a homomorphic image of the Grötzsch graph (outer 5-cycle `o`, inner `m i ~ o (i ± 1)`,
    apex `z ~ m i`) in a triangle-free graph: `3 ∑ d(o i) + 2 ∑ d(m i) + 4 d(z) ≤ 10 n`. -/
theorem grotzsch_weighted_deg_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) (o m : Fin 5 → V) (z : V)
    (h : ∀ i : Fin 5, G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 4)) ∧
      G.Adj z (m i)) :
    3 * ∑ i, #(univ.filter (G.Adj (o i))) + 2 * ∑ i, #(univ.filter (G.Adj (m i))) +
      4 * #(univ.filter (G.Adj z)) ≤ 10 * Fintype.card V := by
  classical
  have e01 : G.Adj (o 0) (o 1) := (h 0).1
  have e12 : G.Adj (o 1) (o 2) := (h 1).1
  have e23 : G.Adj (o 2) (o 3) := (h 2).1
  have e34 : G.Adj (o 3) (o 4) := (h 3).1
  have e40 : G.Adj (o 4) (o 0) := (h 4).1
  have a01 : G.Adj (m 0) (o 1) := (h 0).2.1
  have a04 : G.Adj (m 0) (o 4) := (h 0).2.2.1
  have a12 : G.Adj (m 1) (o 2) := (h 1).2.1
  have a10 : G.Adj (m 1) (o 0) := (h 1).2.2.1
  have a23 : G.Adj (m 2) (o 3) := (h 2).2.1
  have a21 : G.Adj (m 2) (o 1) := (h 2).2.2.1
  have a34 : G.Adj (m 3) (o 4) := (h 3).2.1
  have a32 : G.Adj (m 3) (o 2) := (h 3).2.2.1
  have a40 : G.Adj (m 4) (o 0) := (h 4).2.1
  have a43 : G.Adj (m 4) (o 3) := (h 4).2.2.1
  have z0 : G.Adj z (m 0) := (h 0).2.2.2
  have z1 : G.Adj z (m 1) := (h 1).2.2.2
  have z2 : G.Adj z (m 2) := (h 2).2.2.2
  have z3 : G.Adj z (m 3) := (h 3).2.2.2
  have z4 : G.Adj z (m 4) := (h 4).2.2.2
  have hx : ∀ x : V, 3 * ∑ i, (if G.Adj (o i) x then 1 else 0) + 2 * ∑ i, (if G.Adj (m i) x then 1 else 0) +
      4 * (if G.Adj z x then 1 else 0) ≤ 10 := by
    intro x
    have hp : ∀ p q : V, G.Adj p q → (decide (G.Adj p x) && decide (G.Adj q x)) = false := by
      intro p q hpq
      by_cases hpx : G.Adj p x <;> by_cases hqx : G.Adj q x
      · exact (hTF {p, q, x} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hpq, hpx, hqx⟩)).elim
      all_goals simp [hpx, hqx]
    have key := grotzsch_bool (decide (G.Adj (o 0) x)) (decide (G.Adj (o 1) x)) (decide (G.Adj (o 2) x))
      (decide (G.Adj (o 3) x)) (decide (G.Adj (o 4) x)) (decide (G.Adj (m 0) x)) (decide (G.Adj (m 1) x))
      (decide (G.Adj (m 2) x)) (decide (G.Adj (m 3) x)) (decide (G.Adj (m 4) x)) (decide (G.Adj z x))
      (by rw [hp _ _ e01, hp _ _ e12, hp _ _ e23, hp _ _ e34, hp _ _ e40, hp _ _ a01, hp _ _ a04, hp _ _ a12,
            hp _ _ a10, hp _ _ a23, hp _ _ a21, hp _ _ a34, hp _ _ a32, hp _ _ a40, hp _ _ a43, hp _ _ z0,
            hp _ _ z1, hp _ _ z2, hp _ _ z3, hp _ _ z4]; rfl)
    have conv : ∀ p : V, (if G.Adj p x then 1 else 0) = (decide (G.Adj p x)).toNat := fun p => by
      by_cases hpx : G.Adj p x <;> simp [hpx]
    simp only [Fin.sum_univ_five, conv]
    exact key
  have hdeg : ∀ p : V, #(univ.filter (G.Adj p)) = ∑ x, (if G.Adj p x then 1 else 0) := fun p => by
    rw [Finset.card_filter]
  have hsum : 3 * ∑ i, #(univ.filter (G.Adj (o i))) + 2 * ∑ i, #(univ.filter (G.Adj (m i))) +
      4 * #(univ.filter (G.Adj z)) = ∑ x : V, (3 * ∑ i, (if G.Adj (o i) x then 1 else 0) +
        2 * ∑ i, (if G.Adj (m i) x then 1 else 0) + 4 * (if G.Adj z x then 1 else 0)) := by
    simp_rw [hdeg]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_comm (f := fun i x => if G.Adj (o i) x then 1 else 0),
      Finset.sum_comm (f := fun i x => if G.Adj (m i) x then 1 else 0)]
  rw [hsum]
  calc _ ≤ ∑ _x : V, 10 := Finset.sum_le_sum (fun x _ => hx x)
    _ = 10 * Fintype.card V := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- In the band `14 δ ≥ 5 n` there is no homomorphic image of the Grötzsch graph (`χ_f = 29/10 > 14/5`). -/
theorem no_grotzsch_band {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard)
    (o m : Fin 5 → V) (z : V)
    (h : ∀ i : Fin 5, G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 4)) ∧
      G.Adj z (m i)) : False := by
  classical
  have hdeg : ∀ x : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj x)) := by
    intro x
    have h1 := h14 x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have h2 : (G.neighborSet x).toFinset = univ.filter (G.Adj x) := by ext y; simp
    rwa [h2] at h1
  have hW := grotzsch_weighted_deg_le G hTF o m z h
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨z⟩
  simp only [Fin.sum_univ_five] at hW
  have d0 := hdeg (o 0); have d1 := hdeg (o 1); have d2 := hdeg (o 2); have d3 := hdeg (o 3)
  have d4 := hdeg (o 4); have d5 := hdeg (m 0); have d6 := hdeg (m 1); have d7 := hdeg (m 2)
  have d8 := hdeg (m 3); have d9 := hdeg (m 4); have d10 := hdeg z
  linarith


theorem main_band (h1 : H1) (h2 : H2)
    (V : Type) [Fintype V] (G : SimpleGraph V)
    (h5a : ∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V)
    (hnot3 : ¬ G.Colorable 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * (G.neighborSet v).ncard)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (hTF : G.CliqueFree 3) : False := by
  classical
  obtain ⟨M, hGM, hMTF, hMmax⟩ := exists_maximal_triangleFree G hTF
  have hMH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (M.induce V').edgeSet.ncard > Fintype.card V ^ 2 := by
    intro V' hV'
    have hG' := hH V' hV'
    have hsub : (G.induce V').edgeSet ⊆ (M.induce V').edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ a b => exact hGM he
    have hle : (G.induce V').edgeSet.ncard ≤ (M.induce V').edgeSet.ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hM14 : ∀ x : V, 5 * Fintype.card V ≤ 14 * (M.neighborSet x).ncard := by
    intro x
    have h1x := h14 x
    have hle : (G.neighborSet x).ncard ≤ (M.neighborSet x).ncard :=
      Set.ncard_le_ncard (fun y hy => hGM hy) (Set.toFinite _)
    omega
  have hMnot3 : ¬ M.Colorable 3 := fun hc => hnot3 (hc.mono_left hGM)
  have hnoG : ¬ ∃ (o m : Fin 5 → V) (z : V), ∀ i : Fin 5, M.Adj (o i) (o (i + 1)) ∧ M.Adj (m i) (o (i + 1)) ∧
      M.Adj (m i) (o (i + 4)) ∧ M.Adj z (m i) :=
    fun ⟨o, m, z, h⟩ => no_grotzsch_band M hMTF hM14 o m z h
  by_cases hV8 : ∃ v : Fin 8 → V, ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
      ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → M.Adj (v i) (v j)
  · by_cases hA4 : ∃ φ : Fin 11 → V, ∀ i j : Fin 11, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) →
        M.Adj (φ i) (φ j)
    · exact h2 V M hMTF hMmax hMH hM14 hMnot3 hnoG hA4
    · exact h1 V M hMTF hMmax hMH hM14 hMnot3 hnoG hV8 hA4
  · have hM5a : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ M.Adj u v) → 5 * #I < 2 * Fintype.card V := by
      intro I hI
      have h1I := h5a (I : Set V)
        (fun u hu v hv _ hG => hI u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv) (hGM hG))
      rwa [Set.ncard_coe_finset] at h1I
    have hM35 : ∀ x : V, 12 * Fintype.card V < 35 * (M.neighborSet x).ncard := by
      intro x
      have h1x := hM14 x
      have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
      omega
    exact hMnot3 (colorable_three_of_no_v8_minus_e_band M hMTF hMmax hM5a hM35 hV8
      (fun _ _ H h1 h2 => exists_shortest_odd_walk_of_nonbip H h1 h2)
      (fun _ _ H _ h1 {_} h2 h3 h4 {_} h5 h6 w => shortest_odd_walk_deg_le_two H h1 h2 h3 h4 h5 h6 w))

end R2H1R1

namespace Erdos128_R2_H1_R1_H1

open Finset SimpleGraph R2

abbrev IsV8MinusE {V : Type} (G : SimpleGraph V) (v : Fin 8 → V) : Prop :=
  ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) →
    ¬ (i = 2 ∧ j = 6) → ¬ (i = 6 ∧ j = 2) → G.Adj (v i) (v j)

abbrev IsFullV8 {V : Type} (G : SimpleGraph V) (v : Fin 8 → V) : Prop :=
  ∀ i j : Fin 8, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) → G.Adj (v i) (v j)

abbrev NoGrotzsch {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ ∃ (o m : Fin 5 → V) (z : V), ∀ i : Fin 5,
    G.Adj (o i) (o (i + 1)) ∧ G.Adj (m i) (o (i + 1)) ∧
    G.Adj (m i) (o (i + 4)) ∧ G.Adj z (m i)

abbrev NoAnd4 {V : Type} (G : SimpleGraph V) : Prop :=
  ¬ ∃ φ : Fin 11 → V, ∀ i j : Fin 11,
    (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) → G.Adj (φ i) (φ j)

private lemma mkGrotzsch {V : Type} (G : SimpleGraph V) (hnoG : NoGrotzsch G)
    (o0 o1 o2 o3 o4 m0 m1 m2 m3 m4 z : V)
    (e01 : G.Adj o0 o1) (e12 : G.Adj o1 o2) (e23 : G.Adj o2 o3) (e34 : G.Adj o3 o4) (e40 : G.Adj o4 o0)
    (a01 : G.Adj m0 o1) (a04 : G.Adj m0 o4)
    (a12 : G.Adj m1 o2) (a10 : G.Adj m1 o0)
    (a23 : G.Adj m2 o3) (a21 : G.Adj m2 o1)
    (a34 : G.Adj m3 o4) (a32 : G.Adj m3 o2)
    (a40 : G.Adj m4 o0) (a43 : G.Adj m4 o3)
    (z0 : G.Adj z m0) (z1 : G.Adj z m1) (z2 : G.Adj z m2) (z3 : G.Adj z m3) (z4 : G.Adj z m4) : False := by
  apply hnoG
  let o : Fin 5 → V := ![o0, o1, o2, o3, o4]
  let m : Fin 5 → V := ![m0, m1, m2, m3, m4]
  refine ⟨o, m, z, fun i => ?_⟩
  fin_cases i
  · exact ⟨e01, a01, a04, z0⟩
  · exact ⟨e12, a12, a10, z1⟩
  · exact ⟨e23, a23, a21, z2⟩
  · exact ⟨e34, a34, a32, z3⟩
  · exact ⟨e40, a40, a43, z4⟩

private lemma mkAnd4 {V : Type} (G : SimpleGraph V) (hnoA : NoAnd4 G)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 : V)
    (e0_1 : G.Adj p0 p1) (e1_2 : G.Adj p1 p2) (e2_3 : G.Adj p2 p3) (e3_4 : G.Adj p3 p4)
    (e4_5 : G.Adj p4 p5) (e5_6 : G.Adj p5 p6) (e6_7 : G.Adj p6 p7) (e7_8 : G.Adj p7 p8)
    (e8_9 : G.Adj p8 p9) (e9_10 : G.Adj p9 p10) (e10_0 : G.Adj p10 p0)
    (e0_4 : G.Adj p0 p4) (e1_5 : G.Adj p1 p5) (e2_6 : G.Adj p2 p6) (e3_7 : G.Adj p3 p7)
    (e4_8 : G.Adj p4 p8) (e5_9 : G.Adj p5 p9) (e6_10 : G.Adj p6 p10) (e7_0 : G.Adj p7 p0)
    (e8_1 : G.Adj p8 p1) (e9_2 : G.Adj p9 p2) (e10_3 : G.Adj p10 p3) : False := by
  apply hnoA
  let φ : Fin 11 → V := ![p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10]
  refine ⟨φ, fun i j hij => ?_⟩
  rcases hij with rfl | rfl | rfl | rfl
  · fin_cases i
    · exact e0_1
    · exact e1_2
    · exact e2_3
    · exact e3_4
    · exact e4_5
    · exact e5_6
    · exact e6_7
    · exact e7_8
    · exact e8_9
    · exact e9_10
    · exact e10_0
  · fin_cases i
    · exact e0_4
    · exact e1_5
    · exact e2_6
    · exact e3_7
    · exact e4_8
    · exact e5_9
    · exact e6_10
    · exact e7_0
    · exact e8_1
    · exact e9_2
    · exact e10_3
  · fin_cases i
    · exact e7_0.symm
    · exact e8_1.symm
    · exact e9_2.symm
    · exact e10_3.symm
    · exact e0_4.symm
    · exact e1_5.symm
    · exact e2_6.symm
    · exact e3_7.symm
    · exact e4_8.symm
    · exact e5_9.symm
    · exact e6_10.symm
  · fin_cases i
    · exact e10_0.symm
    · exact e0_1.symm
    · exact e1_2.symm
    · exact e2_3.symm
    · exact e3_4.symm
    · exact e4_5.symm
    · exact e5_6.symm
    · exact e6_7.symm
    · exact e7_8.symm
    · exact e8_9.symm
    · exact e9_10.symm

private lemma weighted_deg_contra {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    {k : ℕ} (pts : Fin k → V) (wts : Fin k → ℕ) (cap : ℕ)
    (hgt : 14 * cap < 5 * ∑ i : Fin k, wts i)
    (hcap : ∀ w : V, (∑ i : Fin k, if G.Adj w (pts i) then wts i else 0) ≤ cap)
    (hne : Nonempty V) : False := by
  set n := Fintype.card V
  have hn : 0 < n := Fintype.card_pos_iff.mpr hne
  have hsum_le : ∑ w : V, (∑ i : Fin k, if G.Adj w (pts i) then wts i else 0) ≤ cap * n := by
    calc _ ≤ ∑ _w : V, cap := Finset.sum_le_sum (fun w _ => hcap w)
      _ = cap * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hsum_eq : ∑ w : V, (∑ i : Fin k, if G.Adj w (pts i) then wts i else 0) =
      ∑ i : Fin k, wts i * #(univ.filter (G.Adj (pts i))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 2; ext w; simp [G.adj_comm]
  have hsum_ge : 5 * (∑ i : Fin k, wts i) * n ≤
      14 * ∑ i : Fin k, wts i * #(univ.filter (G.Adj (pts i))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum; intro i _
    have hdi := h14 (pts i)
    have hmul := Nat.mul_le_mul_left (wts i) hdi
    have h1 : 5 * wts i * n = wts i * (5 * n) := by ring
    have h2 : 14 * (wts i * #(univ.filter (G.Adj (pts i)))) = wts i * (14 * #(univ.filter (G.Adj (pts i)))) := by ring
    omega
  have hcap_ge : 5 * (∑ i : Fin k, wts i) * n ≤ 14 * cap * n := by
    have : 14 * (cap * n) = 14 * cap * n := by ring
    omega
  have : 5 * (∑ i : Fin k, wts i) ≤ 14 * cap := Nat.le_of_mul_le_mul_right hcap_ge hn
  omega

private lemma decide_not_both {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) {p q w : V} (hpq : G.Adj p q) :
    (decide (G.Adj w p) && decide (G.Adj w q)) = false := by
  by_cases h1 : G.Adj w p <;> by_cases h2 : G.Adj w q
  · exact (not_adj_of_cliqueFree_three hTF h1 hpq h2).elim
  all_goals simp [h1, h2]

private lemma decide_not_triple {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q r w : V} (h : ¬ (G.Adj w p ∧ G.Adj w q ∧ G.Adj w r)) :
    (decide (G.Adj w p) && decide (G.Adj w q) && decide (G.Adj w r)) = false := by
  by_cases h1 : G.Adj w p <;> by_cases h2 : G.Adj w q <;> by_cases h3 : G.Adj w r
  · exact (h ⟨h1, h2, h3⟩).elim
  all_goals simp [h1, h2, h3]

private lemma decide_not_quad {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q r s w : V} (h : ¬ (G.Adj w p ∧ G.Adj w q ∧ G.Adj w r ∧ G.Adj w s)) :
    (decide (G.Adj w p) && decide (G.Adj w q) && decide (G.Adj w r) && decide (G.Adj w s)) = false := by
  by_cases h1 : G.Adj w p <;> by_cases h2 : G.Adj w q <;> by_cases h3 : G.Adj w r <;> by_cases h4 : G.Adj w s
  · exact (h ⟨h1, h2, h3, h4⟩).elim
  all_goals simp [h1, h2, h3, h4]

private lemma adj_term_eq {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj]
    {w u v : V} {a b : ℕ} (hu : u = v) (ha : a = b) :
    (if G.Adj w u then a else 0) = b * (decide (G.Adj w v)).toNat := by
  subst hu; subst ha; by_cases h1 : G.Adj w u <;> simp [h1]

private lemma sum_fin9 (f : Fin 9 → ℕ) :
    ∑ i : Fin 9, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]; rfl

private lemma sum_fin10 (f : Fin 10 → ℕ) :
    ∑ i : Fin 10, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]; rfl

private lemma sum_fin11 (f : Fin 11 → ℕ) :
    ∑ i : Fin 11, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]; rfl

/- Finite Boolean weight-cap lemmas (each ≤ 2^11 cases, checked by kernel `decide`). -/

private theorem bool_hno026_A : ∀ b1 b2 b3 b5 b6 b7 : Bool,
    (!(b1 && b2) && !(b2 && b3) && !(b5 && b6) && !(b6 && b7) && !(b1 && b5) && !(b3 && b7) &&
     !(b1 && b3 && b6) && !(b2 && b5 && b7)) = true →
    b1.toNat + b2.toNat + b3.toNat + b5.toNat + b6.toNat + b7.toNat ≤ 2 := by decide

private theorem bool_hno026_B : ∀ b2 b3 b4 b5 b6 b8 : Bool,
    (!(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) && !(b2 && b8) && !(b6 && b8) &&
     !(b2 && b4 && b6) && !(b3 && b5 && b8)) = true →
    b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat + b8.toNat ≤ 2 := by decide

private theorem bool_upgrade_1a : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b3 && b7) &&
     !(b2 && b8) && !(b6 && b8) &&
     !(b1 && b9) && !(b4 && b9) && !(b7 && b9) && !(b8 && b9) &&
     !(b0 && b10) && !(b3 && b10) && !(b5 && b10) && !(b8 && b10) &&
     !(b0 && b2 && b6) && !(b4 && b2 && b6)) = true →
    1 * b0.toNat + 2 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 1 * b4.toNat + 2 * b5.toNat +
      2 * b6.toNat + 2 * b7.toNat + 1 * b8.toNat + 1 * b9.toNat + 1 * b10.toNat ≤ 6 := by decide

private theorem bool_upgrade_1b : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b3 && b7) &&
     !(b2 && b8) && !(b6 && b8) &&
     !(b0 && b2 && b6) && !(b4 && b2 && b6) && !(b1 && b4 && b7 && b8)) = true →
    2 * b0.toNat + 2 * b1.toNat + 3 * b2.toNat + 1 * b3.toNat + 1 * b4.toNat + 1 * b5.toNat +
      3 * b6.toNat + 2 * b7.toNat + 2 * b8.toNat ≤ 6 := by decide

private theorem bool_edge01_A : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b9) && !(b8 && b10) &&
     !(b9 && b1) && !(b9 && b4) && !(b9 && b7) &&
     !(b10 && b2) && !(b10 && b5) && !(b10 && b0) &&
     !(b3 && b6 && b9 && b10) && !(b2 && b4 && b7 && b8)) = true →
    1 * b0.toNat + 1 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 2 * b4.toNat + 1 * b5.toNat +
      1 * b6.toNat + 1 * b7.toNat + 2 * b8.toNat + 2 * b9.toNat + 2 * b10.toNat ≤ 6 := by decide

private theorem bool_edge01_B : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b9) && !(b8 && b10) &&
     !(b9 && b1) && !(b9 && b4) && !(b9 && b7) &&
     !(b10 && b2) && !(b10 && b5) && !(b10 && b0) &&
     !(b3 && b6 && b9 && b10) && !(b2 && b5 && b7 && b8)) = true →
    1 * b0.toNat + 1 * b1.toNat + 1 * b2.toNat + 1 * b3.toNat + 1 * b4.toNat + 2 * b5.toNat +
      2 * b6.toNat + 2 * b7.toNat + 2 * b8.toNat + 2 * b9.toNat + 2 * b10.toNat ≤ 6 := by decide

private theorem bool_edge04_A : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b9) && !(b8 && b10) &&
     !(b9 && b1) && !(b9 && b4) && !(b9 && b7) &&
     !(b10 && b5) && !(b10 && b0) && !(b10 && b3) &&
     !(b1 && b3 && b6 && b8) && !(b2 && b9 && b10)) = true →
    1 * b0.toNat + 2 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 1 * b4.toNat + 1 * b5.toNat +
      1 * b6.toNat + 1 * b7.toNat + 3 * b8.toNat + 3 * b9.toNat + 3 * b10.toNat ≤ 7 := by decide

private theorem bool_hno101_A : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool,
    (!(b0 && b1) && !(b1 && b2) && !(b2 && b3) && !(b3 && b4) && !(b4 && b5) && !(b5 && b6) &&
     !(b6 && b7) && !(b7 && b0) && !(b0 && b4) && !(b1 && b5) && !(b2 && b6) && !(b3 && b7) &&
     !(b8 && b1) && !(b8 && b7) && !(b9 && b4) && !(b8 && b9) &&
     !(b2 && b4 && b8) && !(b1 && b3 && b6 && b9)) = true →
    1 * b0.toNat + 2 * b1.toNat + 2 * b2.toNat + 2 * b3.toNat + 3 * b4.toNat + 1 * b5.toNat +
      1 * b6.toNat + 1 * b7.toNat + 2 * b8.toNat + 2 * b9.toNat ≤ 6 := by decide

/- Step 1: No vertex hits `{v 0, v 2, v 6}` or `{v 4, v 2, v 6}` in `V_8 - (2, 6)`. -/

private lemma no_026 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) :
    ∀ z : V, ¬ (G.Adj z (v 0) ∧ G.Adj z (v 2) ∧ G.Adj z (v 6)) := by
  rintro z ⟨hz0, hz2, hz6⟩
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide) (by decide) (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide) (by decide) (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide) (by decide) (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide) (by decide) (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide) (by decide) (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide) (by decide) (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide) (by decide) (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide) (by decide) (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide) (by decide) (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide) (by decide) (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide) (by decide) (by decide)
  by_cases hA : (∃ a : V, G.Adj a (v 1) ∧ G.Adj a (v 3) ∧ G.Adj a (v 6)) ∨
                (∃ a : V, G.Adj a (v 2) ∧ G.Adj a (v 5) ∧ G.Adj a (v 7))
  · have hno246 : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 4) ∧ G.Adj b (v 6)) := by
      rintro b ⟨hb2, hb4, hb6⟩
      rcases hA with ⟨a, ha1, ha3, ha6⟩ | ⟨a, ha2, ha5, ha7⟩
      · exact mkGrotzsch G hnoG (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) z a b (v 7) (v 6)
          e01 e12 e23 e34 e04.symm e15.symm e45.symm hz2 hz0 ha3 ha1 hb4 hb2 e70 e37.symm
          e56.symm hz6.symm ha6.symm hb6.symm e67
      · exact mkGrotzsch G hnoG (v 0) (v 4) (v 5) (v 6) (v 7) (v 3) (v 1) b a z (v 2)
          e04 e45 e56 e67 e70 e34 e37 e15 e01.symm hb6 hb4 ha7 ha5 hz0 hz6
          e23 e12.symm hb2.symm ha2.symm hz2.symm
    have hno35z : ∀ b : V, ¬ (G.Adj b (v 3) ∧ G.Adj b (v 5) ∧ G.Adj b z) := by
      rintro b ⟨hb3, hb5, hbz⟩
      rcases hA with ⟨a, ha1, ha3, ha6⟩ | ⟨a, ha2, ha5, ha7⟩
      · exact mkGrotzsch G hnoG (v 0) (v 1) (v 5) (v 6) z (v 2) (v 4) a b (v 7) (v 3)
          e01 e15 e56 hz6.symm hz0 e12.symm hz2.symm e45 e04.symm ha6 ha1 hbz hb5 e70 e67.symm
          e23.symm e34 ha3.symm hb3.symm e37
      · exact mkGrotzsch G hnoG (v 0) (v 7) (v 3) (v 2) z (v 6) (v 4) a b (v 1) (v 5)
          e70.symm e37.symm e23.symm hz2.symm hz0 e67 hz6.symm e34.symm e04.symm ha2 ha7 hbz hb3 e01.symm e12
          e56 e45.symm ha5.symm hb5.symm e15.symm
    let pts : Fin 6 → V := ![v 2, v 3, v 4, v 5, v 6, z]
    let wts : Fin 6 → ℕ := ![1, 1, 1, 1, 1, 1]
    refine weighted_deg_contra G h14 pts wts 2 (by decide) (fun w => ?_) ⟨z⟩
    have key := bool_hno026_B (decide (G.Adj w (v 2))) (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4)))
      (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6))) (decide (G.Adj w z))
      (by rw [decide_not_both G hTF e23, decide_not_both G hTF e34, decide_not_both G hTF e45,
              decide_not_both G hTF e56, decide_not_both G hTF hz2.symm, decide_not_both G hTF hz6.symm,
              decide_not_triple G (hno246 w), decide_not_triple G (hno35z w)]; rfl)
    rw [Fin.sum_univ_six,
      adj_term_eq G (show pts 0 = v 2 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 3 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 4 from rfl) (show wts 2 = 1 from rfl),
      adj_term_eq G (show pts 3 = v 5 from rfl) (show wts 3 = 1 from rfl),
      adj_term_eq G (show pts 4 = v 6 from rfl) (show wts 4 = 1 from rfl),
      adj_term_eq G (show pts 5 = z from rfl) (show wts 5 = 1 from rfl)]
    omega
  · push Not at hA
    let pts : Fin 6 → V := ![v 1, v 2, v 3, v 5, v 6, v 7]
    let wts : Fin 6 → ℕ := ![1, 1, 1, 1, 1, 1]
    refine weighted_deg_contra G h14 pts wts 2 (by decide) (fun w => ?_) ⟨z⟩
    have key := bool_hno026_A (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2))) (decide (G.Adj w (v 3)))
      (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6))) (decide (G.Adj w (v 7)))
      (by rw [decide_not_both G hTF e12, decide_not_both G hTF e23, decide_not_both G hTF e56,
              decide_not_both G hTF e67, decide_not_both G hTF e15, decide_not_both G hTF e37,
              decide_not_triple G (fun ⟨h1, h3, h6⟩ => hA.1 w h1 h3 h6),
              decide_not_triple G (fun ⟨h2, h5, h7⟩ => hA.2 w h2 h5 h7)]; rfl)
    rw [Fin.sum_univ_six,
      adj_term_eq G (show pts 0 = v 1 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 2 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 3 from rfl) (show wts 2 = 1 from rfl),
      adj_term_eq G (show pts 3 = v 5 from rfl) (show wts 3 = 1 from rfl),
      adj_term_eq G (show pts 4 = v 6 from rfl) (show wts 4 = 1 from rfl),
      adj_term_eq G (show pts 5 = v 7 from rfl) (show wts 5 = 1 from rfl)]
    omega

private lemma isV8MinusE_refl4 {V : Type} {G : SimpleGraph V} {v : Fin 8 → V} (hv : IsV8MinusE G v) :
    IsV8MinusE G (fun i => v (4 - i)) := by
  intro i j hij h26 h62
  apply hv (4 - i) (4 - j)
  · rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)
  · intro h; apply h26; fin_cases i <;> fin_cases j <;> simp_all
  · intro h; apply h62; fin_cases i <;> fin_cases j <;> simp_all

private lemma no_426 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) :
    ∀ z : V, ¬ (G.Adj z (v 4) ∧ G.Adj z (v 2) ∧ G.Adj z (v 6)) := by
  intro z ⟨hz4, hz2, hz6⟩
  exact no_026 G hTF h14 hnoG (fun i => v (4 - i)) (isV8MinusE_refl4 hv) z ⟨hz4, hz2, hz6⟩

/- Step 2: Upgrade `V_8 - (2, 6)` to a full `V_8` homomorphism. -/

private lemma upgrade_no_147z {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) (z : V)
    (hz2 : G.Adj z (v 2)) (hz6 : G.Adj z (v 6))
    (hno147z : ∀ w : V, ¬ (G.Adj w (v 1) ∧ G.Adj w (v 4) ∧ G.Adj w (v 7) ∧ G.Adj w z)) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide) (by decide) (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide) (by decide) (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide) (by decide) (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide) (by decide) (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide) (by decide) (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide) (by decide) (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide) (by decide) (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide) (by decide) (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide) (by decide) (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide) (by decide) (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide) (by decide) (by decide)
  have h026 := no_026 G hTF h14 hnoG v hv
  have h426 := no_426 G hTF h14 hnoG v hv
  let pts : Fin 9 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, z]
  let wts : Fin 9 → ℕ := ![2, 2, 3, 1, 1, 1, 3, 2, 2]
  refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨z⟩
  have key := bool_upgrade_1b (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
    (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
    (decide (G.Adj w (v 7))) (decide (G.Adj w z))
    (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
            decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
            decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
            decide_not_both G hTF e15, decide_not_both G hTF e37,
            decide_not_both G hTF hz2.symm, decide_not_both G hTF hz6.symm,
            decide_not_triple G (h026 w), decide_not_triple G (h426 w),
            decide_not_quad G (hno147z w)]; rfl)
  rw [sum_fin9,
    adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 2 from rfl),
    adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
    adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 3 from rfl),
    adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 1 from rfl),
    adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
    adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
    adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 3 from rfl),
    adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 2 from rfl),
    adj_term_eq G (show pts 8 = z from rfl) (show wts 8 = 2 from rfl)]
  omega

private lemma exists_full_v8 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsV8MinusE G v) :
    IsFullV8 G v := by
  have h26 : G.Adj (v 2) (v 6) := by
    by_contra hnot
    have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide) (by decide) (by decide)
    have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide) (by decide) (by decide)
    have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide) (by decide) (by decide)
    have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide) (by decide) (by decide)
    have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide) (by decide) (by decide)
    have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide) (by decide) (by decide)
    have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide) (by decide) (by decide)
    have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide) (by decide) (by decide)
    have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide) (by decide) (by decide)
    have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide) (by decide) (by decide)
    have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide) (by decide) (by decide)
    have hne26 : v 2 ≠ v 6 := by
      intro heq
      rw [← heq] at e56
      exact not_adj_of_cliqueFree_three hTF e12.symm e15 e56.symm
    obtain ⟨z, hz2, hz6⟩ := hmax (v 2) (v 6) hne26 hnot
    by_cases hy1 : ∃ y1 : V, G.Adj y1 (v 1) ∧ G.Adj y1 (v 4) ∧ G.Adj y1 (v 7) ∧ G.Adj y1 z
    · by_cases hy2 : ∃ y2 : V, G.Adj y2 (v 0) ∧ G.Adj y2 (v 3) ∧ G.Adj y2 (v 5) ∧ G.Adj y2 z
      · obtain ⟨y1, h11, h14', h17, h1z⟩ := hy1
        obtain ⟨y2, h20, h23, h25, h2z⟩ := hy2
        have h026 := no_026 G hTF h14 hnoG v hv
        have h426 := no_426 G hTF h14 hnoG v hv
        let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, z, y1, y2]
        let wts : Fin 11 → ℕ := ![1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 1]
        refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨z⟩
        have key := bool_upgrade_1a (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
          (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
          (decide (G.Adj w (v 7))) (decide (G.Adj w z)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
          (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
                  decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
                  decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
                  decide_not_both G hTF e15, decide_not_both G hTF e37,
                  decide_not_both G hTF hz2, decide_not_both G hTF hz6,
                  decide_not_both G hTF h11.symm, decide_not_both G hTF h14'.symm,
                  decide_not_both G hTF h17.symm, decide_not_both G hTF h1z.symm,
                  decide_not_both G hTF h20.symm, decide_not_both G hTF h23.symm,
                  decide_not_both G hTF h25.symm, decide_not_both G hTF h2z.symm,
                  decide_not_triple G (h026 w), decide_not_triple G (h426 w)]; rfl)
        rw [sum_fin11,
          adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
          adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
          adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
          adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
          adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
          adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 2 from rfl),
          adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 2 from rfl),
          adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 2 from rfl),
          adj_term_eq G (show pts 8 = z from rfl) (show wts 8 = 1 from rfl),
          adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 1 from rfl),
          adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 1 from rfl)]
        omega
      · push Not at hy2
        exact upgrade_no_147z G hTF h14 hnoG (fun i => v (4 - i)) (isV8MinusE_refl4 hv) z
          hz2.symm hz6.symm (fun w ⟨h1, h4, h7, hz⟩ => hy2 w h4 h1 h7 hz)
    · push Not at hy1
      exact upgrade_no_147z G hTF h14 hnoG v hv z hz2.symm hz6.symm
        (fun w ⟨h1, h4, h7, hz⟩ => hy1 w h1 h4 h7 hz)
  intro i j hij
  by_cases h1 : i = 2 ∧ j = 6
  · rw [h1.1, h1.2]; exact h26
  · by_cases h2 : i = 6 ∧ j = 2
    · rw [h2.1, h2.2]; exact h26.symm
    · exact hv i j hij h1 h2

/- Full `V_8` symmetries and `U v j` definition. -/

private def Uset {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : Fin 8 → V) (j : Fin 8) : Finset V :=
  univ.filter (fun w => G.Adj w (v (j + 1)) ∧ G.Adj w (v (j + 4)) ∧ G.Adj w (v (j + 7)))

private lemma isFullV8_rot {V : Type} {G : SimpleGraph V} {v : Fin 8 → V}
    (hv : IsFullV8 G v) (s : Fin 8) : IsFullV8 G (fun k => v (s + k)) := by
  intro i j hij
  apply hv (s + i) (s + j)
  rcases hij with rfl | rfl | rfl <;> (fin_cases s <;> fin_cases i <;> decide)

private lemma isFullV8_neg {V : Type} {G : SimpleGraph V} {v : Fin 8 → V}
    (hv : IsFullV8 G v) : IsFullV8 G (fun k => v (-k)) := by
  intro i j hij
  apply hv (-i) (-j)
  rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)

/- Step 3: No vertex hits both `U v i` and `U v j` for an edge `(i, j)` of `V_8`. -/

private lemma no_hit_edge_01 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoA : NoAnd4 G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x y1 y2 : V) (hy1 : y1 ∈ Uset G v 0) (hy2 : y2 ∈ Uset G v 1)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have ⟨h9_1', h9_4', h9_7'⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨h10_2', h10_5', h10_0'⟩ := (Finset.mem_filter.mp hy2).2
  have h9_1 : G.Adj y1 (v 1) := h9_1'
  have h9_4 : G.Adj y1 (v 4) := h9_4'
  have h9_7 : G.Adj y1 (v 7) := h9_7'
  have h10_2 : G.Adj y2 (v 2) := h10_2'
  have h10_5 : G.Adj y2 (v 5) := h10_5'
  have h10_0 : G.Adj y2 (v 0) := h10_0'
  have hno36910 : ∀ w : V, ¬ (G.Adj w (v 3) ∧ G.Adj w (v 6) ∧ G.Adj w y1 ∧ G.Adj w y2) := by
    rintro w ⟨hw3, hw6, hw9, hw10⟩
    exact mkAnd4 G hnoA (v 0) (v 7) (v 6) (v 5) (v 4) (v 3) (v 2) (v 1) y1 w y2
      e70.symm e67.symm e56.symm e45.symm e34.symm e23.symm e12.symm h9_1.symm hw9.symm hw10 h10_0
      e04 e37.symm e26.symm e15.symm h9_4.symm hw3.symm h10_2.symm e01.symm h9_7 hw6 h10_5
  by_cases hA : ∃ a : V, G.Adj a (v 2) ∧ G.Adj a (v 4) ∧ G.Adj a (v 7) ∧ G.Adj a x
  · obtain ⟨a, ha2, ha4, ha7, hax⟩ := hA
    have hnoB : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 5) ∧ G.Adj b (v 7) ∧ G.Adj b x) := by
      rintro b ⟨hb2, hb5, hb7, hbx⟩
      exact mkAnd4 G hnoA (v 0) (v 7) b (v 5) (v 4) a (v 2) (v 1) y1 x y2
        e70.symm hb7.symm hb5 e45.symm ha4.symm ha2 e12.symm h9_1.symm hxy1.symm hxy2 h10_0
        e04 ha7.symm hb2 e15.symm h9_4.symm hax h10_2.symm e01.symm h9_7 hbx.symm h10_5
    let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, y1, y2]
    let wts : Fin 11 → ℕ := ![1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]
    refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨x⟩
    have key := bool_edge01_B (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
      (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
      (decide (G.Adj w (v 7))) (decide (G.Adj w x)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
      (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
              decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
              decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
              decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
              decide_not_both G hTF hxy1, decide_not_both G hTF hxy2,
              decide_not_both G hTF h9_1, decide_not_both G hTF h9_4, decide_not_both G hTF h9_7,
              decide_not_both G hTF h10_2, decide_not_both G hTF h10_5, decide_not_both G hTF h10_0,
              decide_not_quad G (hno36910 w), decide_not_quad G (hnoB w)]; rfl)
    rw [sum_fin11,
      adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 1 from rfl),
      adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 1 from rfl),
      adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
      adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 2 from rfl),
      adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 2 from rfl),
      adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 2 from rfl),
      adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 2 from rfl),
      adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 2 from rfl),
      adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 2 from rfl)]
    omega
  · push Not at hA
    let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, y1, y2]
    let wts : Fin 11 → ℕ := ![1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 2]
    refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun w => ?_) ⟨x⟩
    have key := bool_edge01_A (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
      (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
      (decide (G.Adj w (v 7))) (decide (G.Adj w x)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
      (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
              decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
              decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
              decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
              decide_not_both G hTF hxy1, decide_not_both G hTF hxy2,
              decide_not_both G hTF h9_1, decide_not_both G hTF h9_4, decide_not_both G hTF h9_7,
              decide_not_both G hTF h10_2, decide_not_both G hTF h10_5, decide_not_both G hTF h10_0,
              decide_not_quad G (hno36910 w),
              decide_not_quad G (fun ⟨h2, h4, h7, hx⟩ => hA w h2 h4 h7 hx)]; rfl)
    rw [sum_fin11,
      adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
      adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 1 from rfl),
      adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
      adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
      adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 2 from rfl),
      adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
      adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 1 from rfl),
      adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 1 from rfl),
      adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 2 from rfl),
      adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 2 from rfl),
      adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 2 from rfl)]
    omega

private lemma no_hit_edge_04_caseA {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x y1 y2 : V) (hy1 : y1 ∈ Uset G v 0) (hy2 : y2 ∈ Uset G v 4)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2)
    (hno1 : ∀ w : V, ¬ (G.Adj w (v 1) ∧ G.Adj w (v 3) ∧ G.Adj w (v 6) ∧ G.Adj w x))
    (hno2 : ∀ w : V, ¬ (G.Adj w (v 2) ∧ G.Adj w y1 ∧ G.Adj w y2)) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have ⟨h9_1', h9_4', h9_7'⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨h10_5', h10_0', h10_3'⟩ := (Finset.mem_filter.mp hy2).2
  have h9_1 : G.Adj y1 (v 1) := h9_1'
  have h9_4 : G.Adj y1 (v 4) := h9_4'
  have h9_7 : G.Adj y1 (v 7) := h9_7'
  have h10_5 : G.Adj y2 (v 5) := h10_5'
  have h10_0 : G.Adj y2 (v 0) := h10_0'
  have h10_3 : G.Adj y2 (v 3) := h10_3'
  let pts : Fin 11 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, y1, y2]
  let wts : Fin 11 → ℕ := ![1, 2, 2, 2, 1, 1, 1, 1, 3, 3, 3]
  refine weighted_deg_contra G h14 pts wts 7 (by decide) (fun w => ?_) ⟨x⟩
  have key := bool_edge04_A (decide (G.Adj w (v 0))) (decide (G.Adj w (v 1))) (decide (G.Adj w (v 2)))
    (decide (G.Adj w (v 3))) (decide (G.Adj w (v 4))) (decide (G.Adj w (v 5))) (decide (G.Adj w (v 6)))
    (decide (G.Adj w (v 7))) (decide (G.Adj w x)) (decide (G.Adj w y1)) (decide (G.Adj w y2))
    (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
            decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
            decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
            decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
            decide_not_both G hTF hxy1, decide_not_both G hTF hxy2,
            decide_not_both G hTF h9_1, decide_not_both G hTF h9_4, decide_not_both G hTF h9_7,
            decide_not_both G hTF h10_5, decide_not_both G hTF h10_0, decide_not_both G hTF h10_3,
            decide_not_quad G (hno1 w), decide_not_triple G (hno2 w)]; rfl)
  rw [sum_fin11,
    adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
    adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
    adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
    adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
    adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 1 from rfl),
    adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
    adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 1 from rfl),
    adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 1 from rfl),
    adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 3 from rfl),
    adj_term_eq G (show pts 9 = y1 from rfl) (show wts 9 = 3 from rfl),
    adj_term_eq G (show pts 10 = y2 from rfl) (show wts 10 = 3 from rfl)]
  omega

private lemma no_hit_edge_04 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x y1 y2 : V) (hy1 : y1 ∈ Uset G v 0) (hy2 : y2 ∈ Uset G v 4)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have ⟨h9_1', h9_4', h9_7'⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨h10_5', h10_0', h10_3'⟩ := (Finset.mem_filter.mp hy2).2
  have h9_1 : G.Adj y1 (v 1) := h9_1'
  have h9_4 : G.Adj y1 (v 4) := h9_4'
  have h9_7 : G.Adj y1 (v 7) := h9_7'
  have h10_5 : G.Adj y2 (v 5) := h10_5'
  have h10_0 : G.Adj y2 (v 0) := h10_0'
  have h10_3 : G.Adj y2 (v 3) := h10_3'
  by_cases hA : (∃ a : V, G.Adj a (v 1) ∧ G.Adj a (v 3) ∧ G.Adj a (v 6) ∧ G.Adj a x) ∨
                (∃ a : V, G.Adj a (v 2) ∧ G.Adj a y1 ∧ G.Adj a y2)
  · have hno1 : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 5) ∧ G.Adj b (v 7) ∧ G.Adj b x) := by
      rintro b ⟨hb2, hb5, hb7, hbx⟩
      rcases hA with ⟨a, ha1, ha3, ha6, hax⟩ | ⟨a, ha2, ha9, ha10⟩
      · exact mkGrotzsch G hnoG (v 1) (v 5) y2 x a (v 6) (v 0) b (v 3) y1 (v 7)
          e15 h10_5.symm hxy2.symm hax.symm ha1 e56.symm ha6.symm h10_0.symm e01 hbx hb5
          ha3.symm h10_3.symm h9_1 hxy1.symm e67.symm e70 hb7.symm e37.symm h9_7.symm
      · exact mkGrotzsch G hnoG (v 1) (v 2) b (v 7) y1 a (v 5) (v 3) x (v 0) y2
          e12 hb2.symm hb7 h9_7.symm h9_1 ha2 ha9 hb5.symm e15.symm e37 e23.symm hxy1 hbx.symm
          e01 e70.symm ha10.symm h10_5 h10_3 hxy2.symm h10_0
    have hno2 : ∀ b : V, ¬ (G.Adj b (v 6) ∧ G.Adj b y1 ∧ G.Adj b y2) := by
      rintro b ⟨hb6, hb9, hb10⟩
      rcases hA with ⟨a, ha1, ha3, ha6, hax⟩ | ⟨a, ha2, ha9, ha10⟩
      · exact mkGrotzsch G hnoG (v 1) y1 (v 7) (v 6) a x (v 0) b (v 3) (v 5) y2
          h9_1.symm h9_7 e67.symm ha6.symm ha1 hxy1 hax.symm e70.symm e01 hb6 hb9 ha3.symm e37
          e15.symm e56 hxy2.symm h10_0 hb10.symm h10_3 h10_5
      · exact mkGrotzsch G hnoG (v 1) (v 2) (v 6) (v 7) y1 a (v 5) (v 3) b (v 0) y2
          e12 e26 e67 h9_7.symm h9_1 ha2 ha9 e56 e15.symm e37 e23.symm hb9 hb6 e01 e70.symm
          ha10.symm h10_5 h10_3 hb10.symm h10_0
    have hy1' : y1 ∈ Uset G (fun k => v (-k)) 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h9_7, h9_4, h9_1⟩
    have hy2' : y2 ∈ Uset G (fun k => v (-k)) 4 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨h10_3, h10_0, h10_5⟩
    exact no_hit_edge_04_caseA G hTF h14 (fun k => v (-k)) (isFullV8_neg hv) x y1 y2 hy1' hy2' hxy1 hxy2
      (fun w ⟨h7, h5, h2, hx⟩ => hno1 w ⟨h2, h5, h7, hx⟩)
      (fun w ⟨h6, h9, h10⟩ => hno2 w ⟨h6, h9, h10⟩)
  · push Not at hA
    exact no_hit_edge_04_caseA G hTF h14 v hv x y1 y2 hy1 hy2 hxy1 hxy2
      (fun w ⟨h1, h3, h6, hx⟩ => hA.1 w h1 h3 h6 hx)
      (fun w ⟨h2, h9, h10⟩ => hA.2 w h2 h9 h10)

private lemma no_hit_v8_edge {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G) (hnoA : NoAnd4 G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x : V) (i j : Fin 8) (hij : j = i + 1 ∨ j = i + 4 ∨ j = i + 7)
    (y1 : V) (hy1 : y1 ∈ Uset G v i) (y2 : V) (hy2 : y2 ∈ Uset G v j)
    (hxy1 : G.Adj x y1) (hxy2 : G.Adj x y2) : False := by
  have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hy1).2
  have ⟨b1, b4, b7⟩ := (Finset.mem_filter.mp hy2).2
  rcases hij with rfl | rfl | rfl
  · let v' : Fin 8 → V := fun k => v (i + k)
    have hy1' : y1 ∈ Uset G v' 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (0 + 1) = i + 1 := by fin_cases i <;> decide
      have h4 : i + (0 + 4) = i + 4 := by fin_cases i <;> decide
      have h7 : i + (0 + 7) = i + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨a1, a4, a7⟩
    have hy2' : y2 ∈ Uset G v' 1 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (1 + 1) = i + 1 + 1 := by fin_cases i <;> decide
      have h4 : i + (1 + 4) = i + 1 + 4 := by fin_cases i <;> decide
      have h7 : i + (1 + 7) = i + 1 + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨b1, b4, b7⟩
    exact no_hit_edge_01 G hTF h14 hnoA v' (isFullV8_rot hv i) x y1 y2 hy1' hy2' hxy1 hxy2
  · let v' : Fin 8 → V := fun k => v (i + k)
    have hy1' : y1 ∈ Uset G v' 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (0 + 1) = i + 1 := by fin_cases i <;> decide
      have h4 : i + (0 + 4) = i + 4 := by fin_cases i <;> decide
      have h7 : i + (0 + 7) = i + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨a1, a4, a7⟩
    have hy2' : y2 ∈ Uset G v' 4 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + (4 + 1) = i + 4 + 1 := by fin_cases i <;> decide
      have h4 : i + (4 + 4) = i + 4 + 4 := by fin_cases i <;> decide
      have h7 : i + (4 + 7) = i + 4 + 7 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨b1, b4, b7⟩
    exact no_hit_edge_04 G hTF h14 hnoG v' (isFullV8_rot hv i) x y1 y2 hy1' hy2' hxy1 hxy2
  · let v' : Fin 8 → V := fun k => v (i + (-k))
    have hv' : IsFullV8 G v' := isFullV8_neg (isFullV8_rot hv i)
    have hy1' : y1 ∈ Uset G v' 0 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + -(0 + 1) = i + 7 := by fin_cases i <;> decide
      have h4 : i + -(0 + 4) = i + 4 := by fin_cases i <;> decide
      have h7 : i + -(0 + 7) = i + 1 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨a7, a4, a1⟩
    have hy2' : y2 ∈ Uset G v' 1 := by
      simp only [Uset, Finset.mem_filter, Finset.mem_univ, true_and, v']
      have h1 : i + -(1 + 1) = i + 7 + 7 := by fin_cases i <;> decide
      have h4 : i + -(1 + 4) = i + 7 + 4 := by fin_cases i <;> decide
      have h7 : i + -(1 + 7) = i + 7 + 1 := by fin_cases i <;> decide
      rw [h1, h4, h7]; exact ⟨b7, b4, b1⟩
    exact no_hit_edge_01 G hTF h14 hnoA v' hv' x y1 y2 hy1' hy2' hxy1 hxy2

private lemma uset_disjoint {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3) (v : Fin 8 → V) (hv : IsFullV8 G v)
    {i j : Fin 8} (hij : i ≠ j) : Disjoint (Uset G v i) (Uset G v j) := by
  rw [Finset.disjoint_left]
  intro w hwi hwj
  have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hwi).2
  have ⟨b1, b4, b7⟩ := (Finset.mem_filter.mp hwj).2
  have hna : ∀ p q : Fin 8, (q = p + 1 ∨ q = p + 4 ∨ q = p + 7) → G.Adj w (v p) → G.Adj w (v q) → False :=
    fun p q hpq hp hq => not_adj_of_cliqueFree_three hTF hp (hv p q hpq) hq
  fin_cases i <;> fin_cases j <;> simp at hij
  all_goals first
    | exact hna _ _ (by decide) a1 b1 | exact hna _ _ (by decide) a1 b4 | exact hna _ _ (by decide) a1 b7
    | exact hna _ _ (by decide) a4 b1 | exact hna _ _ (by decide) a4 b4 | exact hna _ _ (by decide) a4 b7
    | exact hna _ _ (by decide) a7 b1

private lemma uset_complete {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G) (hnoA : NoAnd4 G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (i j : Fin 8) (hij : j = i + 1 ∨ j = i + 4 ∨ j = i + 7)
    (y1 : V) (hy1 : y1 ∈ Uset G v i) (y2 : V) (hy2 : y2 ∈ Uset G v j) :
    G.Adj y1 y2 := by
  by_contra hnot
  have hne_ij : i ≠ j := by rcases hij with rfl | rfl | rfl <;> (fin_cases i <;> decide)
  have hne : y1 ≠ y2 := fun heq => by
    rw [heq] at hy1
    exact Finset.disjoint_left.mp (uset_disjoint G hTF v hv hne_ij) hy1 hy2
  obtain ⟨x, hx1, hx2⟩ := hmax y1 y2 hne hnot
  exact no_hit_v8_edge G hTF h14 hnoG hnoA v hv x i j hij y1 hy1 y2 hy2 hx1.symm hx2.symm

/- Step 4: No vertex hits `{v (c + 1), v (c + 7)}` while missing `v (c + 4)`. -/

private lemma no_101_caseA {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x w : V) (hx1 : G.Adj x (v 1)) (hx7 : G.Adj x (v 7)) (hw4 : G.Adj w (v 4)) (hxw : G.Adj x w)
    (hnoA : ∀ u : V, ¬ (G.Adj u (v 2) ∧ G.Adj u (v 4) ∧ G.Adj u x))
    (hnoC : ∀ u : V, ¬ (G.Adj u (v 1) ∧ G.Adj u (v 3) ∧ G.Adj u (v 6) ∧ G.Adj u w)) : False := by
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  let pts : Fin 10 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, x, w]
  let wts : Fin 10 → ℕ := ![1, 2, 2, 2, 3, 1, 1, 1, 2, 2]
  refine weighted_deg_contra G h14 pts wts 6 (by decide) (fun u => ?_) ⟨x⟩
  have key := bool_hno101_A (decide (G.Adj u (v 0))) (decide (G.Adj u (v 1))) (decide (G.Adj u (v 2)))
    (decide (G.Adj u (v 3))) (decide (G.Adj u (v 4))) (decide (G.Adj u (v 5))) (decide (G.Adj u (v 6)))
    (decide (G.Adj u (v 7))) (decide (G.Adj u x)) (decide (G.Adj u w))
    (by rw [decide_not_both G hTF e01, decide_not_both G hTF e12, decide_not_both G hTF e23,
            decide_not_both G hTF e34, decide_not_both G hTF e45, decide_not_both G hTF e56,
            decide_not_both G hTF e67, decide_not_both G hTF e70, decide_not_both G hTF e04,
            decide_not_both G hTF e15, decide_not_both G hTF e26, decide_not_both G hTF e37,
            decide_not_both G hTF hx1, decide_not_both G hTF hx7, decide_not_both G hTF hw4,
            decide_not_both G hTF hxw,
            decide_not_triple G (hnoA u), decide_not_quad G (hnoC u)]; rfl)
  rw [sum_fin10,
    adj_term_eq G (show pts 0 = v 0 from rfl) (show wts 0 = 1 from rfl),
    adj_term_eq G (show pts 1 = v 1 from rfl) (show wts 1 = 2 from rfl),
    adj_term_eq G (show pts 2 = v 2 from rfl) (show wts 2 = 2 from rfl),
    adj_term_eq G (show pts 3 = v 3 from rfl) (show wts 3 = 2 from rfl),
    adj_term_eq G (show pts 4 = v 4 from rfl) (show wts 4 = 3 from rfl),
    adj_term_eq G (show pts 5 = v 5 from rfl) (show wts 5 = 1 from rfl),
    adj_term_eq G (show pts 6 = v 6 from rfl) (show wts 6 = 1 from rfl),
    adj_term_eq G (show pts 7 = v 7 from rfl) (show wts 7 = 1 from rfl),
    adj_term_eq G (show pts 8 = x from rfl) (show wts 8 = 2 from rfl),
    adj_term_eq G (show pts 9 = w from rfl) (show wts 9 = 2 from rfl)]
  omega

private lemma no_101_zero {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (x : V) (hx1 : G.Adj x (v 1)) (hx7 : G.Adj x (v 7)) :
    G.Adj x (v 4) := by
  by_contra hx4
  have e01 : G.Adj (v 0) (v 1) := hv 0 1 (by decide)
  have e12 : G.Adj (v 1) (v 2) := hv 1 2 (by decide)
  have e23 : G.Adj (v 2) (v 3) := hv 2 3 (by decide)
  have e34 : G.Adj (v 3) (v 4) := hv 3 4 (by decide)
  have e45 : G.Adj (v 4) (v 5) := hv 4 5 (by decide)
  have e56 : G.Adj (v 5) (v 6) := hv 5 6 (by decide)
  have e67 : G.Adj (v 6) (v 7) := hv 6 7 (by decide)
  have e70 : G.Adj (v 7) (v 0) := hv 7 0 (by decide)
  have e04 : G.Adj (v 0) (v 4) := hv 0 4 (by decide)
  have e15 : G.Adj (v 1) (v 5) := hv 1 5 (by decide)
  have e26 : G.Adj (v 2) (v 6) := hv 2 6 (by decide)
  have e37 : G.Adj (v 3) (v 7) := hv 3 7 (by decide)
  have hne : x ≠ v 4 := by
    intro heq; rw [heq] at hx1
    exact not_adj_of_cliqueFree_three hTF e04.symm e01 hx1
  obtain ⟨w, hxw, hw4⟩ := hmax x (v 4) hne hx4
  have hw4' : G.Adj w (v 4) := hw4.symm
  by_cases hAC : (∃ a : V, G.Adj a (v 2) ∧ G.Adj a (v 4) ∧ G.Adj a x) ∨
                 (∃ a : V, G.Adj a (v 1) ∧ G.Adj a (v 3) ∧ G.Adj a (v 6) ∧ G.Adj a w)
  · have hnoB : ∀ b : V, ¬ (G.Adj b (v 4) ∧ G.Adj b (v 6) ∧ G.Adj b x) := by
      rintro b ⟨hb4, hb6, hbx⟩
      rcases hAC with ⟨a, ha2, ha4, hax⟩ | ⟨a, ha1, ha3, ha6, haw⟩
      · exact mkGrotzsch G hnoG (v 1) (v 2) (v 6) (v 7) x a (v 5) (v 3) b (v 0) (v 4)
          e12 e26 e67 hx7.symm hx1 ha2 hax e56 e15.symm e37 e23.symm hbx hb6 e01 e70.symm
          ha4.symm e45 e34.symm hb4.symm e04.symm
      · exact mkGrotzsch G hnoG (v 1) x (v 7) (v 6) a w (v 0) b (v 3) (v 5) (v 4)
          hx1.symm hx7 e67.symm ha6.symm ha1 hxw.symm haw.symm e70.symm e01 hb6 hbx ha3.symm e37
          e15.symm e56 hw4'.symm e04.symm hb4.symm e34.symm e45
    have hnoD : ∀ b : V, ¬ (G.Adj b (v 2) ∧ G.Adj b (v 5) ∧ G.Adj b (v 7) ∧ G.Adj b w) := by
      rintro b ⟨hb2, hb5, hb7, hbw⟩
      rcases hAC with ⟨a, ha2, ha4, hax⟩ | ⟨a, ha1, ha3, ha6, haw⟩
      · exact mkGrotzsch G hnoG (v 1) (v 2) b (v 7) x a (v 5) (v 3) w (v 0) (v 4)
          e12 hb2.symm hb7 hx7.symm hx1 ha2 hax hb5.symm e15.symm e37 e23.symm hxw.symm hbw.symm
          e01 e70.symm ha4.symm e45 e34.symm hw4'.symm e04.symm
      · exact mkGrotzsch G hnoG (v 1) (v 5) (v 4) w a (v 6) (v 0) b (v 3) x (v 7)
          e15 e45.symm hw4'.symm haw.symm ha1 e56.symm ha6.symm e04 e01 hbw hb5
          ha3.symm e34 hx1 hxw e67.symm e70 hb7.symm e37.symm hx7.symm
    exact no_101_caseA G hTF h14 (fun k => v (-k)) (isFullV8_neg hv) x w hx7 hx1 hw4' hxw
      (fun u ⟨h6, h4, hx⟩ => hnoB u ⟨h4, h6, hx⟩)
      (fun u ⟨h7, h5, h2, hw⟩ => hnoD u ⟨h2, h5, h7, hw⟩)
  · push Not at hAC
    exact no_101_caseA G hTF h14 v hv x w hx1 hx7 hw4' hxw
      (fun u ⟨h2, h4, hx⟩ => hAC.1 u h2 h4 hx)
      (fun u ⟨h1, h3, h6, hw⟩ => hAC.2 u h1 h3 h6 hw)

private lemma no_101 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    (h14 : ∀ v : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj v)))
    (hnoG : NoGrotzsch G)
    (v : Fin 8 → V) (hv : IsFullV8 G v)
    (c : Fin 8) (x : V) (hx1 : G.Adj x (v (c + 1))) (hx7 : G.Adj x (v (c + 7))) :
    G.Adj x (v (c + 4)) :=
  no_101_zero G hTF hmax h14 hnoG (fun k => v (c + k)) (isFullV8_rot hv c) x hx1 hx7

/- Elementary Mantel bound on any subset `B` of a triangle-free graph. -/

private lemma mantel_on_finset {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hTF : G.CliqueFree 3) (B : Finset V) :
    2 * ∑ x ∈ B, #(B.filter (G.Adj x)) ≤ (#B) ^ 2 := by
  by_cases hne : B.Nonempty
  · obtain ⟨u₀, hu₀B, hu₀max⟩ := Finset.exists_max_image B (fun u => #(B.filter (G.Adj u))) hne
    let I : Finset V := B.filter (G.Adj u₀)
    have hIB : I ⊆ B := Finset.filter_subset _ _
    have hI_le : #I ≤ #B := Finset.card_le_card hIB
    have hsum_split : ∑ x ∈ B, #(B.filter (G.Adj x)) =
        ∑ x ∈ I, #(B.filter (G.Adj x)) + ∑ x ∈ B \ I, #(B.filter (G.Adj x)) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hIB]
    have h1 : ∑ x ∈ I, #(B.filter (G.Adj x)) ≤ #I * (#B - #I) := by
      calc _ ≤ ∑ _x ∈ I, (#B - #I) := by
            apply Finset.sum_le_sum; intro x hx
            have hsub : B.filter (G.Adj x) ⊆ B \ I := by
              intro y hy
              rw [Finset.mem_sdiff]
              refine ⟨(Finset.mem_filter.mp hy).1, fun hyI => ?_⟩
              exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hx).2
                (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hyI).2
            have hle := Finset.card_le_card hsub
            rwa [Finset.card_sdiff_of_subset hIB] at hle
        _ = #I * (#B - #I) := by rw [Finset.sum_const, smul_eq_mul]
    have h2 : ∑ x ∈ B \ I, #(B.filter (G.Adj x)) ≤ #I * (#B - #I) := by
      calc _ ≤ ∑ _x ∈ B \ I, #I := by
            apply Finset.sum_le_sum; intro x hx
            exact hu₀max x (Finset.mem_sdiff.mp hx).1
        _ = #I * (#B - #I) := by rw [Finset.sum_const, Finset.card_sdiff_of_subset hIB, smul_eq_mul, mul_comm]
    have hsq : 4 * (#I * (#B - #I)) ≤ (#B) ^ 2 := by
      zify [hI_le]
      nlinarith [sq_nonneg ((#B : ℤ) - 2 * (#I : ℤ))]
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

/- Step 5: Pick a `∑ #(U v j)`-maximal full `V_8`, prove `B = ∅`, and apply `not_hom_andrasfai`. -/

private lemma main_proof : R2H1R1.H1 := by
  intro V _ G hTF hmax h50 h14 _hnot3 hnoG ⟨v₀, hv₀⟩ hnoA
  classical
  have hdeg : ∀ x : V, 5 * Fintype.card V ≤ 14 * #(univ.filter (G.Adj x)) := by
    intro x
    have h1 := h14 x
    rw [Set.ncard_eq_toFinset_card'] at h1
    have h2 : (G.neighborSet x).toFinset = univ.filter (G.Adj x) := by ext y; simp
    rwa [h2] at h1
  have hv₀_full : IsFullV8 G v₀ := exists_full_v8 G hTF hmax hdeg hnoG v₀ hv₀
  let fullV8s : Finset (Fin 8 → V) := univ.filter (fun v => IsFullV8 G v)
  have hv₀_mem : v₀ ∈ fullV8s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀_full⟩
  obtain ⟨v, hv_mem, hv_max⟩ :=
    Finset.exists_max_image fullV8s (fun w => ∑ j : Fin 8, #(Uset G w j)) ⟨v₀, hv₀_mem⟩
  have hv : IsFullV8 G v := (Finset.mem_filter.mp hv_mem).2
  set n := Fintype.card V
  have hmem_v : ∀ j : Fin 8, v j ∈ Uset G v j := fun j =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hv j (j + 1) (Or.inl rfl), hv j (j + 4) (Or.inr (Or.inl rfl)), hv j (j + 7) (Or.inr (Or.inr rfl))⟩
  have hU_exact : ∀ j : Fin 8, ∀ w ∈ Uset G v j, ∀ i : Fin 8,
      G.Adj w (v i) ↔ (i = j + 1 ∨ i = j + 4 ∨ i = j + 7) := by
    intro j w hw i
    have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hw).2
    constructor
    · intro hwi
      by_contra hnot
      have hna : ∀ p q : Fin 8, (q = p + 1 ∨ q = p + 4 ∨ q = p + 7) →
          G.Adj w (v p) → G.Adj w (v q) → False :=
        fun p q hpq hp hq => not_adj_of_cliqueFree_three hTF hp (hv p q hpq) hq
      fin_cases j <;> fin_cases i <;> simp at hnot
      all_goals first
        | exact hna _ _ (by decide) hwi a1 | exact hna _ _ (by decide) hwi a4
        | exact hna _ _ (by decide) hwi a7
    · rintro (rfl | rfl | rfl) <;> assumption
  -- Classify every vertex `x` via `v8_indep_subset_nbhd`
  have hex_cls : ∀ x : V, ∃ c : Fin 8, ∀ j : Fin 8, (∃ y ∈ Uset G v j, G.Adj x y) →
      j = c + 1 ∨ j = c + 4 ∨ j = c + 7 := by
    intro x
    let J : Finset (Fin 8) := univ.filter (fun j => ∃ y ∈ Uset G v j, G.Adj x y)
    have hJ_indep : ∀ i ∈ J, ∀ j ∈ J, ¬ (j = i + 1 ∨ j = i + 4 ∨ j = i + 7) := by
      intro i hi j hj hij
      obtain ⟨y1, hy1, hxy1⟩ := (Finset.mem_filter.mp hi).2
      obtain ⟨y2, hy2, hxy2⟩ := (Finset.mem_filter.mp hj).2
      exact no_hit_v8_edge G hTF hdeg hnoG hnoA v hv x i j hij y1 hy1 y2 hy2 hxy1 hxy2
    obtain ⟨c, hc⟩ := v8_indep_subset_nbhd J hJ_indep
    exact ⟨c, fun j hj => hc j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩
  let cls : V → Fin 8 := fun x => (hex_cls x).choose
  have hcls_spec : ∀ x : V, ∀ j : Fin 8, ∀ y ∈ Uset G v j, G.Adj x y →
      j = cls x + 1 ∨ j = cls x + 4 ∨ j = cls x + 7 :=
    fun x j y hy hxy => (hex_cls x).choose_spec j ⟨y, hy, hxy⟩
  let B : Finset V := univ.filter (fun x => ∀ j : Fin 8, x ∉ Uset G v j)
  -- Every `x ∈ B` misses either all of `U v (cls x + 1)` or all of `U v (cls x + 7)`
  have hB_miss : ∀ x ∈ B,
      (∀ y ∈ Uset G v (cls x + 1), ¬ G.Adj x y) ∨
      (∀ y ∈ Uset G v (cls x + 7), ¬ G.Adj x y) := by
    intro x hxB
    by_contra hboth
    push Not at hboth
    obtain ⟨⟨y1, hy1, hxy1⟩, ⟨y7, hy7, hxy7⟩⟩ := hboth
    have h17 : cls x + 1 ≠ cls x + 7 := by generalize cls x = c; fin_cases c <;> decide
    set c := cls x
    let v' : Fin 8 → V := fun k => if k = c + 1 then y1 else if k = c + 7 then y7 else v k
    have hv'_memU : ∀ k : Fin 8, v' k ∈ Uset G v k := by
      intro k; dsimp only [v']
      split_ifs with h1 h7
      · subst h1; exact hy1
      · subst h7; exact hy7
      · exact hmem_v k
    have hv'_full : IsFullV8 G v' := fun i j hij =>
      uset_complete G hTF hmax hdeg hnoG hnoA v hv i j hij (v' i) (hv'_memU i) (v' j) (hv'_memU j)
    have hU_sub : ∀ k : Fin 8, Uset G v k ⊆ Uset G v' k := by
      intro k u hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · exact uset_complete G hTF hmax hdeg hnoG hnoA v hv k (k + 1) (Or.inl rfl) u hu (v' (k + 1)) (hv'_memU (k + 1))
      · exact uset_complete G hTF hmax hdeg hnoG hnoA v hv k (k + 4) (Or.inr (Or.inl rfl)) u hu (v' (k + 4)) (hv'_memU (k + 4))
      · exact uset_complete G hTF hmax hdeg hnoG hnoA v hv k (k + 7) (Or.inr (Or.inr rfl)) u hu (v' (k + 7)) (hv'_memU (k + 7))
    have hx_v'1 : G.Adj x (v' (c + 1)) := by dsimp only [v']; rw [if_pos rfl]; exact hxy1
    have hx_v'7 : G.Adj x (v' (c + 7)) := by
      dsimp only [v']; rw [if_neg h17.symm, if_pos rfl]; exact hxy7
    have hx_v'4 : G.Adj x (v' (c + 4)) := no_101 G hTF hmax hdeg hnoG v' hv'_full c x hx_v'1 hx_v'7
    have hx_in' : x ∈ Uset G v' c := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx_v'1, hx_v'4, hx_v'7⟩
    have hx_notin : x ∉ Uset G v c := (Finset.mem_filter.mp hxB).2 c
    have hlt_c : #(Uset G v c) < #(Uset G v' c) :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hU_sub c, fun heq => hx_notin (heq ▸ hx_in')⟩)
    have hsum_lt : ∑ k : Fin 8, #(Uset G v k) < ∑ k : Fin 8, #(Uset G v' k) :=
      Finset.sum_lt_sum (fun k _ => Finset.card_le_card (hU_sub k)) ⟨c, Finset.mem_univ c, hlt_c⟩
    have hv'_le := hv_max v' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'_full⟩)
    omega
  -- Every `w ∈ B` hits at most 2 vertices of `{v 0, ..., v 7}`
  have hB_cap2 : ∀ w ∈ B, #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) ≤ 2 := by
    intro w hwB
    have hsub : univ.filter (fun i : Fin 8 => G.Adj w (v i)) ⊆ ({cls w + 1, cls w + 4, cls w + 7} : Finset (Fin 8)) := by
      intro i hi
      have hwi := (Finset.mem_filter.mp hi).2
      have := hcls_spec w i (v i) (hmem_v i) hwi
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have hne_all : univ.filter (fun i : Fin 8 => G.Adj w (v i)) ≠ ({cls w + 1, cls w + 4, cls w + 7} : Finset (Fin 8)) := by
      intro heq
      have h1 : cls w + 1 ∈ univ.filter (fun i : Fin 8 => G.Adj w (v i)) := by rw [heq]; simp
      have h4 : cls w + 4 ∈ univ.filter (fun i : Fin 8 => G.Adj w (v i)) := by rw [heq]; simp
      have h7 : cls w + 7 ∈ univ.filter (fun i : Fin 8 => G.Adj w (v i)) := by rw [heq]; simp
      exact (Finset.mem_filter.mp hwB).2 (cls w) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h4).2, (Finset.mem_filter.mp h7).2⟩)
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne_all⟩)
    have hcard3 : #({cls w + 1, cls w + 4, cls w + 7} : Finset (Fin 8)) ≤ 3 :=
      (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
    omega
  -- Partition `B` into `E0 c` (misses `U (c + 1)`) and `E2 c` (misses `U (c + 7)`)
  let E0 : Fin 8 → Finset V := fun c =>
    B.filter (fun x => cls x = c ∧ ∀ y ∈ Uset G v (c + 1), ¬ G.Adj x y)
  let E2 : Fin 8 → Finset V := fun c =>
    B.filter (fun x => cls x = c ∧ ∀ y ∈ Uset G v (c + 7), ¬ G.Adj x y)
  -- Sharp 5-weight vertex count for `E2 c`
  have hbound_E2 : ∀ c : Fin 8,
      14 * (#(Uset G v (c + 1)) + #(Uset G v (c + 4))) + 7 * #B + 14 * #(E2 c) ≤ 5 * n := by
    intro c
    have hpt : ∀ w : V,
        (if w ∈ Uset G v (c + 1) then 2 else 0) + (if w ∈ Uset G v (c + 4) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 6)) then 2 else 0) + (if G.Adj w (v (c + 7)) then 2 else 0) +
        (if w ∈ E2 c then 2 else 0) ≤ 5 := by
      intro w
      by_cases hwB : w ∈ B
      · have hnot1 : w ∉ Uset G v (c + 1) := (Finset.mem_filter.mp hwB).2 (c + 1)
        have hnot4 : w ∉ Uset G v (c + 4) := (Finset.mem_filter.mp hwB).2 (c + 4)
        have hcap := hB_cap2 w hwB
        have h67 : G.Adj (v (c + 6)) (v (c + 7)) := hv (c + 6) (c + 7) (Or.inl (by fin_cases c <;> decide))
        by_cases hwE : w ∈ E2 c
        · have ⟨hclsw, hmiss7⟩ := (Finset.mem_filter.mp hwE).2
          have hno7 : ¬ G.Adj w (v (c + 7)) := hmiss7 (v (c + 7)) (hmem_v (c + 7))
          have hno6 : ¬ G.Adj w (v (c + 6)) := by
            intro h6
            have hmem := hcls_spec w (c + 6) (v (c + 6)) (hmem_v (c + 6)) h6
            rw [hclsw] at hmem
            fin_cases c <;> simp at hmem
          simp [hnot1, hnot4, hwB, hwE, hno6, hno7]; omega
        · by_cases h6 : G.Adj w (v (c + 6)) <;> by_cases h7 : G.Adj w (v (c + 7))
          · exact (not_adj_of_cliqueFree_three hTF h6 h67 h7).elim
          all_goals (simp [hnot1, hnot4, hwB, hwE, h6, h7]; omega)
      · have hexU : ∃ k : Fin 8, w ∈ Uset G v k := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
        obtain ⟨k, hwk⟩ := hexU
        have hnotE : w ∉ E2 c := fun h => hwB (Finset.mem_filter.mp h).1
        have hmem_iff : ∀ j : Fin 8, w ∈ Uset G v j ↔ k = j := by
          intro j; constructor
          · intro hwj; by_contra hne
            exact Finset.disjoint_left.mp (uset_disjoint G hTF v hv hne) hwk hwj
          · rintro rfl; exact hwk
        have hdeg3 : #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) = 3 := by
          have heq : univ.filter (fun i : Fin 8 => G.Adj w (v i)) = {k + 1, k + 4, k + 7} := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            exact hU_exact k w hwk i
          rw [heq]; fin_cases k <;> decide
        have h6iff : G.Adj w (v (c + 6)) ↔ (c + 6 = k + 1 ∨ c + 6 = k + 4 ∨ c + 6 = k + 7) :=
          hU_exact k w hwk (c + 6)
        have h7iff : G.Adj w (v (c + 7)) ↔ (c + 7 = k + 1 ∨ c + 7 = k + 4 ∨ c + 7 = k + 7) :=
          hU_exact k w hwk (c + 7)
        simp only [hwB, hnotE, if_false, add_zero, hdeg3, hmem_iff, h6iff, h7iff]
        fin_cases c <;> fin_cases k <;> decide
    have hsum_le : ∑ w : V, ((if w ∈ Uset G v (c + 1) then 2 else 0) + (if w ∈ Uset G v (c + 4) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 6)) then 2 else 0) + (if G.Adj w (v (c + 7)) then 2 else 0) +
        (if w ∈ E2 c then 2 else 0)) ≤ 5 * n := by
      calc _ ≤ ∑ _w : V, 5 := Finset.sum_le_sum (fun w _ => hpt w)
        _ = 5 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, ((if w ∈ Uset G v (c + 1) then 2 else 0) + (if w ∈ Uset G v (c + 4) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 6)) then 2 else 0) + (if G.Adj w (v (c + 7)) then 2 else 0) +
        (if w ∈ E2 c then 2 else 0)) =
        2 * #(Uset G v (c + 1)) + 2 * #(Uset G v (c + 4)) + #B +
        (∑ i : Fin 8, #(univ.filter (G.Adj (v i)))) +
        2 * #(univ.filter (G.Adj (v (c + 6)))) + 2 * #(univ.filter (G.Adj (v (c + 7)))) +
        2 * #(E2 c) := by
      simp_rw [Finset.sum_add_distrib]
      have hconst : ∀ (S : Finset V) (a : ℕ), ∑ w : V, (if w ∈ S then a else 0) = a * #S := by
        intro S a
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_comm]
      have hadj : ∀ (u : V) (a : ℕ), ∑ w : V, (if G.Adj w u then a else 0) = a * #(univ.filter (G.Adj u)) := by
        intro u a
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
      have hswap : ∑ w : V, #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) =
          ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
        simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      rw [hconst, hconst, hconst, one_mul, hswap, hadj, hadj, hconst]
    have h8deg : 40 * n ≤ 14 * ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
      rw [Finset.mul_sum]
      calc 40 * n = ∑ _i : Fin 8, 5 * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hdeg (v i))
    have hd6 := hdeg (v (c + 6))
    have hd7 := hdeg (v (c + 7))
    omega
  -- Symmetric 5-weight vertex count for `E0 c`
  have hbound_E0 : ∀ c : Fin 8,
      14 * (#(Uset G v (c + 4)) + #(Uset G v (c + 7))) + 7 * #B + 14 * #(E0 c) ≤ 5 * n := by
    intro c
    have hpt : ∀ w : V,
        (if w ∈ Uset G v (c + 4) then 2 else 0) + (if w ∈ Uset G v (c + 7) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 1)) then 2 else 0) + (if G.Adj w (v (c + 2)) then 2 else 0) +
        (if w ∈ E0 c then 2 else 0) ≤ 5 := by
      intro w
      by_cases hwB : w ∈ B
      · have hnot4 : w ∉ Uset G v (c + 4) := (Finset.mem_filter.mp hwB).2 (c + 4)
        have hnot7 : w ∉ Uset G v (c + 7) := (Finset.mem_filter.mp hwB).2 (c + 7)
        have hcap := hB_cap2 w hwB
        have h12 : G.Adj (v (c + 1)) (v (c + 2)) := hv (c + 1) (c + 2) (Or.inl (by fin_cases c <;> decide))
        by_cases hwE : w ∈ E0 c
        · have ⟨hclsw, hmiss1⟩ := (Finset.mem_filter.mp hwE).2
          have hno1 : ¬ G.Adj w (v (c + 1)) := hmiss1 (v (c + 1)) (hmem_v (c + 1))
          have hno2 : ¬ G.Adj w (v (c + 2)) := by
            intro h2
            have hmem := hcls_spec w (c + 2) (v (c + 2)) (hmem_v (c + 2)) h2
            rw [hclsw] at hmem
            fin_cases c <;> simp at hmem
          simp [hnot4, hnot7, hwB, hwE, hno1, hno2]; omega
        · by_cases h1 : G.Adj w (v (c + 1)) <;> by_cases h2 : G.Adj w (v (c + 2))
          · exact (not_adj_of_cliqueFree_three hTF h1 h12 h2).elim
          all_goals (simp [hnot4, hnot7, hwB, hwE, h1, h2]; omega)
      · have hexU : ∃ k : Fin 8, w ∈ Uset G v k := by
          by_contra hnone; push Not at hnone
          exact hwB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
        obtain ⟨k, hwk⟩ := hexU
        have hnotE : w ∉ E0 c := fun h => hwB (Finset.mem_filter.mp h).1
        have hmem_iff : ∀ j : Fin 8, w ∈ Uset G v j ↔ k = j := by
          intro j; constructor
          · intro hwj; by_contra hne
            exact Finset.disjoint_left.mp (uset_disjoint G hTF v hv hne) hwk hwj
          · rintro rfl; exact hwk
        have hdeg3 : #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) = 3 := by
          have heq : univ.filter (fun i : Fin 8 => G.Adj w (v i)) = {k + 1, k + 4, k + 7} := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            exact hU_exact k w hwk i
          rw [heq]; fin_cases k <;> decide
        have h1iff : G.Adj w (v (c + 1)) ↔ (c + 1 = k + 1 ∨ c + 1 = k + 4 ∨ c + 1 = k + 7) :=
          hU_exact k w hwk (c + 1)
        have h2iff : G.Adj w (v (c + 2)) ↔ (c + 2 = k + 1 ∨ c + 2 = k + 4 ∨ c + 2 = k + 7) :=
          hU_exact k w hwk (c + 2)
        simp only [hwB, hnotE, if_false, add_zero, hdeg3, hmem_iff, h1iff, h2iff]
        fin_cases c <;> fin_cases k <;> decide
    have hsum_le : ∑ w : V, ((if w ∈ Uset G v (c + 4) then 2 else 0) + (if w ∈ Uset G v (c + 7) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 1)) then 2 else 0) + (if G.Adj w (v (c + 2)) then 2 else 0) +
        (if w ∈ E0 c then 2 else 0)) ≤ 5 * n := by
      calc _ ≤ ∑ _w : V, 5 := Finset.sum_le_sum (fun w _ => hpt w)
        _ = 5 * n := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
    have hsum_eq : ∑ w : V, ((if w ∈ Uset G v (c + 4) then 2 else 0) + (if w ∈ Uset G v (c + 7) then 2 else 0) +
        (if w ∈ B then 1 else 0) + #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) +
        (if G.Adj w (v (c + 1)) then 2 else 0) + (if G.Adj w (v (c + 2)) then 2 else 0) +
        (if w ∈ E0 c then 2 else 0)) =
        2 * #(Uset G v (c + 4)) + 2 * #(Uset G v (c + 7)) + #B +
        (∑ i : Fin 8, #(univ.filter (G.Adj (v i)))) +
        2 * #(univ.filter (G.Adj (v (c + 1)))) + 2 * #(univ.filter (G.Adj (v (c + 2)))) +
        2 * #(E0 c) := by
      simp_rw [Finset.sum_add_distrib]
      have hconst : ∀ (S : Finset V) (a : ℕ), ∑ w : V, (if w ∈ S then a else 0) = a * #S := by
        intro S a
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
          Finset.sum_const, smul_eq_mul, mul_comm]
      have hadj : ∀ (u : V) (a : ℕ), ∑ w : V, (if G.Adj w u then a else 0) = a * #(univ.filter (G.Adj u)) := by
        intro u a
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
        congr 2; ext w; simp [G.adj_comm]
      have hswap : ∑ w : V, #(univ.filter (fun i : Fin 8 => G.Adj w (v i))) =
          ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
        simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
      rw [hconst, hconst, hconst, one_mul, hswap, hadj, hadj, hconst]
    have h8deg : 40 * n ≤ 14 * ∑ i : Fin 8, #(univ.filter (G.Adj (v i))) := by
      rw [Finset.mul_sum]
      calc 40 * n = ∑ _i : Fin 8, 5 * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hdeg (v i))
    have hd1 := hdeg (v (c + 1))
    have hd2 := hdeg (v (c + 2))
    omega
  -- Prove `B = ∅` via Mantel on `G[B]`
  have hB_empty : B = ∅ := by
    by_contra hBne
    have hBpos : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBne
    let Uall : Finset V := univ \ B
    have hUall_bound : ∀ x ∈ B, 14 * #(Uall.filter (G.Adj x)) + 7 * #B < 5 * n := by
      intro x hxB
      set c := cls x
      rcases hB_miss x hxB with hmiss1 | hmiss7
      · have hxE0 : x ∈ E0 c := Finset.mem_filter.mpr ⟨hxB, rfl, hmiss1⟩
        have hpos : 1 ≤ #(E0 c) := Finset.card_pos.mpr ⟨x, hxE0⟩
        have hsub : Uall.filter (G.Adj x) ⊆ Uset G v (c + 4) ∪ Uset G v (c + 7) := by
          intro y hy
          have ⟨hyU, hxy⟩ := Finset.mem_filter.mp hy
          have hy_notB : y ∉ B := (Finset.mem_sdiff.mp hyU).2
          have hexU : ∃ j : Fin 8, y ∈ Uset G v j := by
            by_contra hnone; push Not at hnone
            exact hy_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
          obtain ⟨j, hyj⟩ := hexU
          rcases hcls_spec x j y hyj hxy with rfl | rfl | rfl
          · exact (hmiss1 y hyj hxy).elim
          · exact Finset.mem_union_left _ hyj
          · exact Finset.mem_union_right _ hyj
        have hle : #(Uall.filter (G.Adj x)) ≤ #(Uset G v (c + 4)) + #(Uset G v (c + 7)) :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hb := hbound_E0 c
        omega
      · have hxE2 : x ∈ E2 c := Finset.mem_filter.mpr ⟨hxB, rfl, hmiss7⟩
        have hpos : 1 ≤ #(E2 c) := Finset.card_pos.mpr ⟨x, hxE2⟩
        have hsub : Uall.filter (G.Adj x) ⊆ Uset G v (c + 1) ∪ Uset G v (c + 4) := by
          intro y hy
          have ⟨hyU, hxy⟩ := Finset.mem_filter.mp hy
          have hy_notB : y ∉ B := (Finset.mem_sdiff.mp hyU).2
          have hexU : ∃ j : Fin 8, y ∈ Uset G v j := by
            by_contra hnone; push Not at hnone
            exact hy_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
          obtain ⟨j, hyj⟩ := hexU
          rcases hcls_spec x j y hyj hxy with rfl | rfl | rfl
          · exact Finset.mem_union_left _ hyj
          · exact Finset.mem_union_right _ hyj
          · exact (hmiss7 y hyj hxy).elim
        have hle : #(Uall.filter (G.Adj x)) ≤ #(Uset G v (c + 1)) + #(Uset G v (c + 4)) :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hb := hbound_E2 c
        omega
    have hsum_lt : ∑ x ∈ B, (14 * #(Uall.filter (G.Adj x)) + 7 * #B) < ∑ _x ∈ B, (5 * n) :=
      Finset.sum_lt_sum_of_nonempty hBpos hUall_bound
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.sum_const,
      smul_eq_mul, smul_eq_mul] at hsum_lt
    have hdeg_split : ∀ x ∈ B, #(univ.filter (G.Adj x)) = #(Uall.filter (G.Adj x)) + #(B.filter (G.Adj x)) := by
      intro x _
      have hunion : Uall ∪ B = univ := Finset.sdiff_union_of_subset (Finset.subset_univ B)
      have hdisj : Disjoint Uall B := Finset.sdiff_disjoint
      rw [← hunion, Finset.filter_union,
        Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
    have hdeg_sum : #B * (5 * n) ≤ 14 * ∑ x ∈ B, #(Uall.filter (G.Adj x)) + 14 * ∑ x ∈ B, #(B.filter (G.Adj x)) := by
      calc #B * (5 * n) = ∑ _x ∈ B, 5 * n := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ B, 14 * #(univ.filter (G.Adj x)) := Finset.sum_le_sum (fun x _ => hdeg x)
        _ = ∑ x ∈ B, (14 * #(Uall.filter (G.Adj x)) + 14 * #(B.filter (G.Adj x))) := by
            apply Finset.sum_congr rfl; intro x hx; rw [hdeg_split x hx, mul_add]
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hmantel := mantel_on_finset G hTF B
    have hsq : #B * (7 * #B) = 7 * (#B) ^ 2 := by ring
    omega
  -- Every vertex `x` lies in `Uset G v (cls x)`, so `cls` is a homomorphism `G → V_8`!
  have hall_U : ∀ x : V, x ∈ Uset G v (cls x) := by
    intro x
    have hx_notB : x ∉ B := by rw [hB_empty]; simp
    have hexU : ∃ j : Fin 8, x ∈ Uset G v j := by
      by_contra hnone; push Not at hnone
      exact hx_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnone⟩)
    obtain ⟨j, hxj⟩ := hexU
    have ⟨a1, a4, a7⟩ := (Finset.mem_filter.mp hxj).2
    have h1 := hcls_spec x (j + 1) (v (j + 1)) (hmem_v (j + 1)) a1
    have h4 := hcls_spec x (j + 4) (v (j + 4)) (hmem_v (j + 4)) a4
    have h7 := hcls_spec x (j + 7) (v (j + 7)) (hmem_v (j + 7)) a7
    have heq : j = cls x := by
      generalize cls x = c at h1 h4 h7 ⊢
      fin_cases j <;> fin_cases c <;> simp at h1 h4 h7 ⊢
    rwa [← heq]
  have hcls_hom : ∀ x y : V, G.Adj x y → cls y = cls x + 1 ∨ cls y = cls x + 4 ∨ cls y = cls x + 7 :=
    fun x y hxy => hcls_spec x (cls y) y (hall_U y) hxy
  -- Convert Möbius labeling (`+1, +4, +7`) to consecutive `And(3)` (`+3, +4, +5`) via `3 * cls x`
  let φ : V → Fin 8 := fun x => 3 * cls x
  have hφ : ∀ x y : V, G.Adj x y →
      3 ≤ ((φ y).val + (3 * 3 - 1) - (φ x).val) % (3 * 3 - 1) ∧
      ((φ y).val + (3 * 3 - 1) - (φ x).val) % (3 * 3 - 1) < 2 * 3 := by
    intro x y hxy
    have h := hcls_hom x y hxy
    dsimp only [φ]
    rcases h with h | h | h <;> rw [h] <;> (generalize cls x = a; fin_cases a <;> decide)
  exact not_hom_andrasfai G h50 (fun H hHTF hHH => five_mul_edges_lt_sq H hHTF hHH) 3 (by decide) φ hφ

end Erdos128_R2_H1_R1_H1

namespace Erdos128_R2_H1_R1_H2

/-- Powers of 2 for `Fin 11`. -/
def pow2 (k : Fin 11) : ℕ :=
  match k.1 with
  | 0 => 1 | 1 => 2 | 2 => 4 | 3 => 8 | 4 => 16 | 5 => 32
  | 6 => 64 | 7 => 128 | 8 => 256 | 9 => 512 | _ => 1024

/-- Bit test using kernel-reduced integer division and mod. -/
def hasBit (m : ℕ) (k : Fin 11) : Bool :=
  (m / pow2 k) % 2 == 1

/-- Test whether an 11-bit mask represents an independent set of `And(4)`. -/
def isIndepMask (m : ℕ) : Bool :=
  (List.finRange 11).all fun i =>
    !hasBit m i || (!hasBit m (i + 1) && !hasBit m (i + 4) && !hasBit m (i + 7) && !hasBit m (i + 10))

/-- The 89 bitmasks of independent sets of `And(4)`. -/
def maskOf (a : Fin 89) : ℕ :=
  match a.1 with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 8 | 5 => 16 | 6 => 32 | 7 => 64 | 8 => 128
  | 9 => 256 | 10 => 512 | 11 => 1024 | 12 => 5 | 13 => 9 | 14 => 33 | 15 => 65 | 16 => 257
  | 17 => 513 | 18 => 10 | 19 => 18 | 20 => 66 | 21 => 130 | 22 => 514 | 23 => 1026 | 24 => 20
  | 25 => 36 | 26 => 132 | 27 => 260 | 28 => 1028 | 29 => 40 | 30 => 72 | 31 => 264 | 32 => 520
  | 33 => 80 | 34 => 144 | 35 => 528 | 36 => 1040 | 37 => 160 | 38 => 288 | 39 => 1056 | 40 => 320
  | 41 => 576 | 42 => 640 | 43 => 1152 | 44 => 1280 | 45 => 37 | 46 => 261 | 47 => 41 | 48 => 73
  | 49 => 265 | 50 => 521 | 51 => 289 | 52 => 321 | 53 => 577 | 54 => 74 | 55 => 522 | 56 => 82
  | 57 => 146 | 58 => 530 | 59 => 1042 | 60 => 578 | 61 => 642 | 62 => 1154 | 63 => 148 | 64 => 1044
  | 65 => 164 | 66 => 292 | 67 => 1060 | 68 => 1156 | 69 => 1284 | 70 => 296 | 71 => 328 | 72 => 584
  | 73 => 592 | 74 => 656 | 75 => 1168 | 76 => 1184 | 77 => 1312 | 78 => 293 | 79 => 297 | 80 => 329
  | 81 => 585 | 82 => 586 | 83 => 594 | 84 => 658 | 85 => 1170 | 86 => 1172 | 87 => 1188 | _ => 1316

/-- Inverse lookup from an independent-set bitmask to `Fin 89`. -/
def idxOfMask (m : ℕ) : Fin 89 :=
  match m with
  | 0 => 0 | 1 => 1 | 2 => 2 | 4 => 3 | 8 => 4 | 16 => 5 | 32 => 6 | 64 => 7 | 128 => 8
  | 256 => 9 | 512 => 10 | 1024 => 11 | 5 => 12 | 9 => 13 | 33 => 14 | 65 => 15 | 257 => 16
  | 513 => 17 | 10 => 18 | 18 => 19 | 66 => 20 | 130 => 21 | 514 => 22 | 1026 => 23 | 20 => 24
  | 36 => 25 | 132 => 26 | 260 => 27 | 1028 => 28 | 40 => 29 | 72 => 30 | 264 => 31 | 520 => 32
  | 80 => 33 | 144 => 34 | 528 => 35 | 1040 => 36 | 160 => 37 | 288 => 38 | 1056 => 39 | 320 => 40
  | 576 => 41 | 640 => 42 | 1152 => 43 | 1280 => 44 | 37 => 45 | 261 => 46 | 41 => 47 | 73 => 48
  | 265 => 49 | 521 => 50 | 289 => 51 | 321 => 52 | 577 => 53 | 74 => 54 | 522 => 55 | 82 => 56
  | 146 => 57 | 530 => 58 | 1042 => 59 | 578 => 60 | 642 => 61 | 1154 => 62 | 148 => 63 | 1044 => 64
  | 164 => 65 | 292 => 66 | 1060 => 67 | 1156 => 68 | 1284 => 69 | 296 => 70 | 328 => 71 | 584 => 72
  | 592 => 73 | 656 => 74 | 1168 => 75 | 1184 => 76 | 1312 => 77 | 293 => 78 | 297 => 79 | 329 => 80
  | 585 => 81 | 586 => 82 | 594 => 83 | 658 => 84 | 1170 => 85 | 1172 => 86 | 1188 => 87 | 1316 => 88
  | _ => 0

/-- `+1` cyclic shift on `Fin 89`. -/
def sh1 (a : Fin 89) : Fin 89 :=
  match a.1 with
  | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 5 | 5 => 6 | 6 => 7 | 7 => 8 | 8 => 9
  | 9 => 10 | 10 => 11 | 11 => 1 | 12 => 18 | 13 => 19 | 14 => 20 | 15 => 21 | 16 => 22
  | 17 => 23 | 18 => 24 | 19 => 25 | 20 => 26 | 21 => 27 | 22 => 28 | 23 => 12 | 24 => 29
  | 25 => 30 | 26 => 31 | 27 => 32 | 28 => 13 | 29 => 33 | 30 => 34 | 31 => 35 | 32 => 36
  | 33 => 37 | 34 => 38 | 35 => 39 | 36 => 14 | 37 => 40 | 38 => 41 | 39 => 15 | 40 => 42
  | 41 => 43 | 42 => 44 | 43 => 16 | 44 => 17 | 45 => 54 | 46 => 55 | 47 => 56 | 48 => 57
  | 49 => 58 | 50 => 59 | 51 => 60 | 52 => 61 | 53 => 62 | 54 => 63 | 55 => 64 | 56 => 65
  | 57 => 66 | 58 => 67 | 59 => 45 | 60 => 68 | 61 => 69 | 62 => 46 | 63 => 70 | 64 => 47
  | 65 => 71 | 66 => 72 | 67 => 48 | 68 => 49 | 69 => 50 | 70 => 73 | 71 => 74 | 72 => 75
  | 73 => 76 | 74 => 77 | 75 => 51 | 76 => 52 | 77 => 53 | 78 => 82 | 79 => 83 | 80 => 84
  | 81 => 85 | 82 => 86 | 83 => 87 | 84 => 88 | 85 => 78 | 86 => 79 | 87 => 80 | _ => 81

/-- `-1` cyclic shift on `Fin 89`. -/
def invSh1 (a : Fin 89) : Fin 89 :=
  match a.1 with
  | 0 => 0 | 1 => 11 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7
  | 9 => 8 | 10 => 9 | 11 => 10 | 12 => 23 | 13 => 28 | 14 => 36 | 15 => 39 | 16 => 43
  | 17 => 44 | 18 => 12 | 19 => 13 | 20 => 14 | 21 => 15 | 22 => 16 | 23 => 17 | 24 => 18
  | 25 => 19 | 26 => 20 | 27 => 21 | 28 => 22 | 29 => 24 | 30 => 25 | 31 => 26 | 32 => 27
  | 33 => 29 | 34 => 30 | 35 => 31 | 36 => 32 | 37 => 33 | 38 => 34 | 39 => 35 | 40 => 37
  | 41 => 38 | 42 => 40 | 43 => 41 | 44 => 42 | 45 => 59 | 46 => 62 | 47 => 64 | 48 => 67
  | 49 => 68 | 50 => 69 | 51 => 75 | 52 => 76 | 53 => 77 | 54 => 45 | 55 => 46 | 56 => 47
  | 57 => 48 | 58 => 49 | 59 => 50 | 60 => 51 | 61 => 52 | 62 => 53 | 63 => 54 | 64 => 55
  | 65 => 56 | 66 => 57 | 67 => 58 | 68 => 60 | 69 => 61 | 70 => 63 | 71 => 65 | 72 => 66
  | 73 => 70 | 74 => 71 | 75 => 72 | 76 => 73 | 77 => 74 | 78 => 85 | 79 => 86 | 80 => 87
  | 81 => 88 | 82 => 78 | 83 => 79 | 84 => 80 | 85 => 81 | 86 => 82 | 87 => 83 | _ => 84

def sh (k : Fin 11) (a : Fin 89) : Fin 89 := sh1^[k.1] a
def invSh (k : Fin 11) (a : Fin 89) : Fin 89 := invSh1^[k.1] a

/-- Representatives of the 9 `ℤ/11`-orbits on `Fin 89`. -/
def rep (r : Fin 9) : Fin 89 :=
  match r.1 with
  | 0 => 0 | 1 => 1 | 2 => 12 | 3 => 13 | 4 => 14 | 5 => 45 | 6 => 46 | 7 => 48 | _ => 78

def orbId (a : Fin 89) : Fin 9 :=
  match a.1 with
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 1 | 4 => 1 | 5 => 1 | 6 => 1 | 7 => 1 | 8 => 1
  | 9 => 1 | 10 => 1 | 11 => 1 | 12 => 2 | 13 => 3 | 14 => 4 | 15 => 4 | 16 => 3 | 17 => 2
  | 18 => 2 | 19 => 3 | 20 => 4 | 21 => 4 | 22 => 3 | 23 => 2 | 24 => 2 | 25 => 3 | 26 => 4
  | 27 => 4 | 28 => 3 | 29 => 2 | 30 => 3 | 31 => 4 | 32 => 4 | 33 => 2 | 34 => 3 | 35 => 4
  | 36 => 4 | 37 => 2 | 38 => 3 | 39 => 4 | 40 => 2 | 41 => 3 | 42 => 2 | 43 => 3 | 44 => 2
  | 45 => 5 | 46 => 6 | 47 => 6 | 48 => 7 | 49 => 7 | 50 => 5 | 51 => 7 | 52 => 5 | 53 => 6
  | 54 => 5 | 55 => 6 | 56 => 6 | 57 => 7 | 58 => 7 | 59 => 5 | 60 => 7 | 61 => 5 | 62 => 6
  | 63 => 5 | 64 => 6 | 65 => 6 | 66 => 7 | 67 => 7 | 68 => 7 | 69 => 5 | 70 => 5 | 71 => 6
  | 72 => 7 | 73 => 5 | 74 => 6 | 75 => 7 | 76 => 5 | 77 => 6 | 78 => 8 | 79 => 8 | 80 => 8
  | 81 => 8 | 82 => 8 | 83 => 8 | 84 => 8 | 85 => 8 | 86 => 8 | 87 => 8 | _ => 8

def orbSh (a : Fin 89) : Fin 11 :=
  match a.1 with
  | 0 => 10 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 4 | 6 => 5 | 7 => 6 | 8 => 7
  | 9 => 8 | 10 => 9 | 11 => 10 | 12 => 0 | 13 => 0 | 14 => 0 | 15 => 6 | 16 => 8 | 17 => 9
  | 18 => 1 | 19 => 1 | 20 => 1 | 21 => 7 | 22 => 9 | 23 => 10 | 24 => 2 | 25 => 2 | 26 => 2
  | 27 => 8 | 28 => 10 | 29 => 3 | 30 => 3 | 31 => 3 | 32 => 9 | 33 => 4 | 34 => 4 | 35 => 4
  | 36 => 10 | 37 => 5 | 38 => 5 | 39 => 5 | 40 => 6 | 41 => 6 | 42 => 7 | 43 => 7 | 44 => 8
  | 45 => 0 | 46 => 0 | 47 => 3 | 48 => 0 | 49 => 8 | 50 => 9 | 51 => 5 | 52 => 6 | 53 => 9
  | 54 => 1 | 55 => 1 | 56 => 4 | 57 => 1 | 58 => 9 | 59 => 10 | 60 => 6 | 61 => 7 | 62 => 10
  | 63 => 2 | 64 => 2 | 65 => 5 | 66 => 2 | 67 => 10 | 68 => 7 | 69 => 8 | 70 => 3 | 71 => 6
  | 72 => 3 | 73 => 4 | 74 => 7 | 75 => 4 | 76 => 5 | 77 => 8 | 78 => 0 | 79 => 3 | 80 => 6
  | 81 => 9 | 82 => 1 | 83 => 4 | 84 => 7 | 85 => 10 | 86 => 2 | 87 => 5 | _ => 8

/-- Nonnegative integer multipliers for `k = 0` in the `ℤ/11`-equivariant certificate. -/
def Lval (a : Fin 89) : ℤ :=
  match a.1 with
  | 0 => 4121 | 1 => 3195 | 2 => 2874 | 3 => 2657 | 4 => 2550 | 5 => 2622 | 6 => 2693
  | 7 => 2693 | 8 => 2622 | 9 => 2550 | 10 => 2657 | 11 => 2874 | 12 => 1732 | 13 => 1921
  | 14 => 1791 | 15 => 1791 | 16 => 1921 | 17 => 1732 | 18 => 1322 | 19 => 1672 | 20 => 1470
  | 21 => 1399 | 22 => 1885 | 23 => 1660 | 24 => 1144 | 25 => 1494 | 26 => 1134 | 27 => 1078
  | 28 => 1885 | 29 => 1109 | 30 => 1405 | 31 => 957 | 32 => 1078 | 33 => 1181 | 34 => 1405
  | 35 => 1134 | 36 => 1399 | 37 => 1181 | 38 => 1405 | 39 => 1470 | 40 => 1109 | 41 => 1494
  | 42 => 1144 | 43 => 1672 | 44 => 1322 | 45 => 867 | 46 => 867 | 47 => 1117 | 48 => 918
  | 49 => 732 | 50 => 867 | 51 => 918 | 52 => 1117 | 53 => 867 | 54 => 761 | 55 => 867
  | 56 => 868 | 57 => 670 | 58 => 803 | 59 => 796 | 60 => 883 | 61 => 1081 | 62 => 796
  | 63 => 655 | 64 => 1081 | 65 => 619 | 66 => 421 | 67 => 883 | 68 => 803 | 69 => 867
  | 70 => 477 | 71 => 477 | 72 => 421 | 73 => 619 | 74 => 655 | 75 => 670 | 76 => 868
  | 77 => 761 | 78 => 71 | 79 => 107 | 80 => 107 | 81 => 71 | 82 => 107 | 83 => 179
  | 84 => 250 | 85 => 0 | 86 => 250 | 87 => 179 | _ => 107

def dir (d : Bool) : Fin 11 := if d then 1 else 10

def b2z (b : Bool) : ℤ := if b then 1 else 0

/-- Membership predicate for `V'_j = V_j ∪ Orb1(j) ∪ Orb2(j)`. -/
def inVp (j : Fin 11) (m : ℕ) : Bool :=
  hasBit m (j + 10) && hasBit m (j + 1) && (hasBit m (j + 4) || hasBit m (j + 7))

/-- Necessary condition for a vertex in `S_i` to be adjacent to a vertex in `V'_j`. -/
def canAdjVp (i j : Fin 11) (m : ℕ) : Bool :=
  hasBit m i && !hasBit m (j + 10) && !hasBit m (j + 1) && !(hasBit m (j + 4) && hasBit m (j + 7))

def d1Pred (i : Fin 11) (d : Bool) (a : Fin 89) : Bool :=
  canAdjVp i (i + 2 * dir d) (maskOf a)

def diffPred (i : Fin 11) (d : Bool) (a : Fin 89) : Bool :=
  canAdjVp i (i + 5 * dir d) (maskOf a) && !canAdjVp i (i + 2 * dir d) (maskOf a)

def gCoeff (k : Fin 11) (a : Fin 89) : ℤ :=
  14 * b2z (hasBit (maskOf a) k) - 5

def mTerm (i : Fin 11) (d : Bool) (a b : Fin 89) : ℤ :=
  let u0a := 1 - 2 * b2z (hasBit (maskOf a) i)
  let u0b := 1 - 2 * b2z (hasBit (maskOf b) i)
  let d1a := b2z (d1Pred i d a)
  let d1b := b2z (d1Pred i d b)
  let v2a := u0a - 2 * b2z (inVp (i + 2 * dir d) (maskOf a)) + b2z (diffPred i d a)
  let v2b := u0b - 2 * b2z (inVp (i + 2 * dir d) (maskOf b)) + b2z (diffPred i d b)
  50 * (u0a * d1b + d1a * u0b) + 25 * v2a * v2b - 4

def mInt (a b : Fin 89) : ℤ :=
  ∑ i : Fin 11, (mTerm i true a b + mTerm i false a b)

def symLG (a b : Fin 89) : ℤ :=
  ∑ k : Fin 11, (Lval (invSh k a) * gCoeff k b + gCoeff k a * Lval (invSh k b))

def certMat (a b : Fin 89) : ℤ :=
  20 * mInt a b + symLG a b

/- Finite decidable checks on `Fin 89` and `Fin 2048`. -/

lemma Lval_nonneg (a : Fin 89) : 0 ≤ Lval a := by
  revert a; decide

lemma maskOf_idxOfMask_chunk (q : Fin 32) (r : Fin 64) :
    isIndepMask (64 * q.1 + r.1) = true →
      maskOf (idxOfMask (64 * q.1 + r.1)) = 64 * q.1 + r.1 := by
  fin_cases q <;> (revert r; decide)

lemma maskOf_idxOfMask (m : ℕ) (hm : m < 2048) :
    isIndepMask m = true → maskOf (idxOfMask m) = m := by
  have hdiv : 64 * (m / 64) + m % 64 = m := Nat.div_add_mod m 64
  have hq : m / 64 < 32 := by omega
  have hr : m % 64 < 64 := Nat.mod_lt m (by decide)
  intro h
  have hchk := maskOf_idxOfMask_chunk ⟨m / 64, hq⟩ ⟨m % 64, hr⟩ (by simpa [hdiv] using h)
  simpa [hdiv] using hchk

lemma invSh1_sh1 (a : Fin 89) : invSh1 (sh1 a) = a := by
  revert a; decide

lemma sh1_invSh1 (a : Fin 89) : sh1 (invSh1 a) = a := by
  revert a; decide

lemma sh1_iter_11 (a : Fin 89) : sh1^[11] a = a := by
  revert a; decide

lemma invSh1_iter_11 (a : Fin 89) : invSh1^[11] a = a := by
  revert a; decide

lemma hasBit_sh1 (a : Fin 89) (k : Fin 11) :
    hasBit (maskOf (sh1 a)) (k + 1) = hasBit (maskOf a) k := by
  revert a k; decide

lemma sh_orb (a : Fin 89) : sh (orbSh a) (rep (orbId a)) = a := by
  revert a; decide

lemma size_cert_true (a : Fin 89) :
    (∑ m : Fin 7, gCoeff (Fin.ofNat 11 m.1) a) ≤
    7 * (2 * (b2z (hasBit (maskOf a) 0) + b2z (inVp 2 (maskOf a)) + b2z (inVp 5 (maskOf a))) - 1) := by
  revert a; decide

lemma size_cert_false (a : Fin 89) :
    (∑ m : Fin 7, gCoeff (Fin.ofNat 11 m.1 * 10) a) ≤
    7 * (2 * (b2z (hasBit (maskOf a) 0) + b2z (inVp 9 (maskOf a)) + b2z (inVp 6 (maskOf a))) - 1) := by
  revert a; decide

lemma certMat_rep_0 (b : Fin 89) : certMat (rep 0) b ≤ 0 := by revert b; decide
lemma certMat_rep_1 (b : Fin 89) : certMat (rep 1) b ≤ 0 := by revert b; decide
lemma certMat_rep_2 (b : Fin 89) : certMat (rep 2) b ≤ 0 := by revert b; decide
lemma certMat_rep_3 (b : Fin 89) : certMat (rep 3) b ≤ 0 := by revert b; decide
lemma certMat_rep_4 (b : Fin 89) : certMat (rep 4) b ≤ 0 := by revert b; decide
lemma certMat_rep_5 (b : Fin 89) : certMat (rep 5) b ≤ 0 := by revert b; decide
lemma certMat_rep_6 (b : Fin 89) : certMat (rep 6) b ≤ 0 := by revert b; decide
lemma certMat_rep_7 (b : Fin 89) : certMat (rep 7) b ≤ 0 := by revert b; decide
lemma certMat_rep_8 (b : Fin 89) : certMat (rep 8) b ≤ 0 := by revert b; decide

lemma certMat_rep (r : Fin 9) (b : Fin 89) : certMat (rep r) b ≤ 0 := by
  fin_cases r
  · exact certMat_rep_0 b
  · exact certMat_rep_1 b
  · exact certMat_rep_2 b
  · exact certMat_rep_3 b
  · exact certMat_rep_4 b
  · exact certMat_rep_5 b
  · exact certMat_rep_6 b
  · exact certMat_rep_7 b
  · exact certMat_rep_8 b

/- `ℤ/11`-invariance of `certMat` and `size_cert`. -/

lemma fin11_ofNat_succ (n : ℕ) : Fin.ofNat 11 (n + 1) = Fin.ofNat 11 n + 1 := by
  apply Fin.ext
  change (n + 1) % 11 = (n % 11 + 1 % 11) % 11
  rw [Nat.add_mod]

lemma fin11_ofNat_self (s : Fin 11) : Fin.ofNat 11 s.1 = s := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt s.2

lemma hasBit_sh1_iter (n : ℕ) (a : Fin 89) (k : Fin 11) :
    hasBit (maskOf (sh1^[n] a)) (k + Fin.ofNat 11 n) = hasBit (maskOf a) k := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', fin11_ofNat_succ, ← add_assoc, hasBit_sh1]
    exact ih k

lemma hasBit_sh (s : Fin 11) (a : Fin 89) (k : Fin 11) :
    hasBit (maskOf (sh s a)) (k + s) = hasBit (maskOf a) k := by
  have h := hasBit_sh1_iter s.1 a k
  rwa [fin11_ofNat_self] at h

lemma invSh1_iter_sh1_iter (m n : ℕ) (a : Fin 89) :
    invSh1^[m] (sh1^[n] a) =
      if n ≤ m then invSh1^[m - n] a else sh1^[n - m] a := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    cases m with
    | zero => simp
    | succ m =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply', invSh1_sh1, ih m]
      by_cases h : n ≤ m
      · have h' : n + 1 ≤ m + 1 := by omega
        simp [h, h', Nat.succ_sub_succ]
      · have h' : ¬ n + 1 ≤ m + 1 := by omega
        simp [h, h', Nat.succ_sub_succ]

lemma sh_iter_mod (n : ℕ) (a : Fin 89) : sh1^[n] a = sh1^[n % 11] a := by
  have hdiv : n = n % 11 + 11 * (n / 11) := (Nat.mod_add_div n 11).symm
  conv_lhs => rw [hdiv, Function.iterate_add_apply]
  suffices h : ∀ q (x : Fin 89), sh1^[11 * q] x = x by rw [h]
  intro q x
  induction q generalizing x with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, sh1_iter_11, ih]

lemma invSh_iter_mod (n : ℕ) (a : Fin 89) : invSh1^[n] a = invSh1^[n % 11] a := by
  have hdiv : n = n % 11 + 11 * (n / 11) := (Nat.mod_add_div n 11).symm
  conv_lhs => rw [hdiv, Function.iterate_add_apply]
  suffices h : ∀ q (x : Fin 89), invSh1^[11 * q] x = x by rw [h]
  intro q x
  induction q generalizing x with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, Function.iterate_add_apply, invSh1_iter_11, ih]

lemma sh_invSh_cancel (s : Fin 11) (a : Fin 89) : sh s (invSh s a) = a := by
  have h : ∀ n (x : Fin 89), sh1^[n] (invSh1^[n] x) = x := by
    intro n x
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply', sh1_invSh1, ih]
  exact h s.1 a

lemma invSh_add_sh (k s : Fin 11) (a : Fin 89) :
    invSh (k + s) (sh s a) = invSh k a := by
  unfold invSh sh
  have h1 : (k + s).1 = (k.1 + s.1) % 11 := rfl
  rw [h1, ← invSh_iter_mod (k.1 + s.1), invSh1_iter_sh1_iter]
  simp

lemma inVp_sh (s j : Fin 11) (a : Fin 89) :
    inVp (j + s) (maskOf (sh s a)) = inVp j (maskOf a) := by
  unfold inVp
  rw [add_right_comm j s 10, add_right_comm j s 1, add_right_comm j s 4, add_right_comm j s 7,
    hasBit_sh, hasBit_sh, hasBit_sh, hasBit_sh]

lemma canAdjVp_sh (s i j : Fin 11) (a : Fin 89) :
    canAdjVp (i + s) (j + s) (maskOf (sh s a)) = canAdjVp i j (maskOf a) := by
  unfold canAdjVp
  rw [add_right_comm j s 10, add_right_comm j s 1, add_right_comm j s 4, add_right_comm j s 7,
    hasBit_sh, hasBit_sh, hasBit_sh, hasBit_sh, hasBit_sh]

lemma d1Pred_sh (s i : Fin 11) (d : Bool) (a : Fin 89) :
    d1Pred (i + s) d (sh s a) = d1Pred i d a := by
  unfold d1Pred
  rw [add_right_comm i s (2 * dir d), canAdjVp_sh]

lemma diffPred_sh (s i : Fin 11) (d : Bool) (a : Fin 89) :
    diffPred (i + s) d (sh s a) = diffPred i d a := by
  unfold diffPred
  rw [add_right_comm i s (5 * dir d), add_right_comm i s (2 * dir d), canAdjVp_sh, canAdjVp_sh]

lemma gCoeff_sh (s k : Fin 11) (a : Fin 89) :
    gCoeff (k + s) (sh s a) = gCoeff k a := by
  unfold gCoeff
  rw [hasBit_sh]

lemma mTerm_sh (s i : Fin 11) (d : Bool) (a b : Fin 89) :
    mTerm (i + s) d (sh s a) (sh s b) = mTerm i d a b := by
  unfold mTerm
  rw [add_right_comm i s (2 * dir d)]
  simp only [hasBit_sh, d1Pred_sh, diffPred_sh, inVp_sh]

lemma mInt_sh (s : Fin 11) (a b : Fin 89) :
    mInt (sh s a) (sh s b) = mInt a b := by
  unfold mInt
  symm
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun i => ?_
  change mTerm i true a b + mTerm i false a b =
    mTerm (i + s) true (sh s a) (sh s b) + mTerm (i + s) false (sh s a) (sh s b)
  rw [mTerm_sh, mTerm_sh]

lemma symLG_sh (s : Fin 11) (a b : Fin 89) :
    symLG (sh s a) (sh s b) = symLG a b := by
  unfold symLG
  symm
  refine Fintype.sum_equiv (Equiv.addRight s) _ _ fun k => ?_
  change Lval (invSh k a) * gCoeff k b + gCoeff k a * Lval (invSh k b) =
    Lval (invSh (k + s) (sh s a)) * gCoeff (k + s) (sh s b) +
      gCoeff (k + s) (sh s a) * Lval (invSh (k + s) (sh s b))
  rw [invSh_add_sh, invSh_add_sh, gCoeff_sh, gCoeff_sh]

lemma certMat_sh (s : Fin 11) (a b : Fin 89) :
    certMat (sh s a) (sh s b) = certMat a b := by
  unfold certMat
  rw [mInt_sh, symLG_sh]

lemma certMat_nonpos (a b : Fin 89) : certMat a b ≤ 0 := by
  have ha : sh (orbSh a) (rep (orbId a)) = a := sh_orb a
  have hb : sh (orbSh a) (invSh (orbSh a) b) = b := sh_invSh_cancel (orbSh a) b
  rw [← ha, ← hb, certMat_sh]
  exact certMat_rep (orbId a) (invSh (orbSh a) b)

lemma size_cert_all (i : Fin 11) (d : Bool) (a : Fin 89) :
    (∑ m : Fin 7, gCoeff (i + Fin.ofNat 11 m.1 * dir d) a) ≤
    7 * (2 * (b2z (hasBit (maskOf a) i) +
      b2z (inVp (i + 2 * dir d) (maskOf a)) +
      b2z (inVp (i + 5 * dir d) (maskOf a))) - 1) := by
  set a0 := invSh i a
  have ha : sh i a0 = a := sh_invSh_cancel i a
  rw [← ha]
  have hsum : (∑ m : Fin 7, gCoeff (i + Fin.ofNat 11 m.1 * dir d) (sh i a0)) =
      ∑ m : Fin 7, gCoeff (Fin.ofNat 11 m.1 * dir d) a0 := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_comm i, gCoeff_sh]
  rw [hsum]
  have hb0 : hasBit (maskOf (sh i a0)) i = hasBit (maskOf a0) 0 := by
    simpa using hasBit_sh i a0 0
  have hb1 : inVp (i + 2 * dir d) (maskOf (sh i a0)) = inVp (2 * dir d) (maskOf a0) := by
    rw [add_comm i, inVp_sh]
  have hb2 : inVp (i + 5 * dir d) (maskOf (sh i a0)) = inVp (5 * dir d) (maskOf a0) := by
    rw [add_comm i, inVp_sh]
  rw [hb0, hb1, hb2]
  cases d
  · simpa [dir] using size_cert_false a0
  · simpa [dir] using size_cert_true a0

/- Binary mask decoding on `Fin 11`. -/

lemma pow2_eq (k : Fin 11) : pow2 k = 2 ^ k.1 := by
  fin_cases k <;> rfl

lemma sum_pow2_lt (f : Fin 11 → Bool) :
    (∑ k : Fin 11, if f k then pow2 k else 0) < 2048 := by
  have hle : (∑ k : Fin 11, if f k then pow2 k else 0) ≤ ∑ k : Fin 11, pow2 k := by
    refine Finset.sum_le_sum fun k _ => ?_
    cases f k <;> simp
  have hsum : (∑ k : Fin 11, pow2 k) = 2047 := by decide
  omega

lemma sum_pow2_lo_lt (k : Fin 11) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin 11 => j.1 < k.1), pow2 j) < pow2 k := by
  revert k; decide

lemma hasBit_sum_pow2 (f : Fin 11 → Bool) (k : Fin 11) :
    hasBit (∑ j : Fin 11, if f j then pow2 j else 0) k = f k := by
  let g : Fin 11 → ℕ := fun j => if f j then pow2 j else 0
  let lo : Finset (Fin 11) := Finset.univ.filter fun j => j.1 < k.1
  let hi : Finset (Fin 11) := Finset.univ.filter fun j => k.1 < j.1
  have hsplit : (∑ j : Fin 11, g j) = (∑ j ∈ lo, g j) + g k + ∑ j ∈ hi, g j := by
    have h1 : (Finset.univ : Finset (Fin 11)) = lo ∪ ({k} ∪ hi) := by
      ext j; simp only [lo, hi, Finset.mem_univ, Finset.mem_union, Finset.mem_filter,
        Finset.mem_singleton, true_and, true_iff]
      rcases lt_trichotomy j.1 k.1 with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr h)
    have hd1 : Disjoint lo ({k} ∪ hi) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [lo, hi, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_univ, true_and] at hj1 hj2
      rcases hj2 with rfl | hj2 <;> omega
    have hd2 : Disjoint ({k} : Finset (Fin 11)) hi := by
      rw [Finset.disjoint_singleton_left]
      simp [hi]
    rw [h1, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton, add_assoc]
  have hlo : ∑ j ∈ lo, g j < pow2 k := by
    have hle : ∑ j ∈ lo, g j ≤ ∑ j ∈ lo, pow2 j :=
      Finset.sum_le_sum fun j _ => by dsimp [g]; cases f j <;> simp
    exact lt_of_le_of_lt hle (sum_pow2_lo_lt k)
  have hhi : 2 * pow2 k ∣ ∑ j ∈ hi, g j := by
    refine Finset.dvd_sum fun j hj => ?_
    simp only [hi, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    dsimp [g]
    cases f j
    · simp
    · rw [if_pos rfl, pow2_eq, pow2_eq]
      have hpow : 2 ^ (k.1 + 1) ∣ 2 ^ j.1 := Nat.pow_dvd_pow 2 (by omega)
      simpa [pow_succ, mul_comm] using hpow
  obtain ⟨q, hq⟩ := hhi
  have hpos : 0 < pow2 k := by rw [pow2_eq]; positivity
  rw [show (∑ j : Fin 11, if f j then pow2 j else 0) = (∑ j ∈ lo, g j) + g k + 2 * pow2 k * q from by
    rw [← hq]; exact hsplit]
  unfold hasBit
  have hdiv : ((∑ j ∈ lo, g j) + g k + 2 * pow2 k * q) / pow2 k =
      (if f k then 1 else 0) + 2 * q := by
    have h1 : (∑ j ∈ lo, g j) + g k + 2 * pow2 k * q =
        (∑ j ∈ lo, g j) + ((if f k then 1 else 0) + 2 * q) * pow2 k := by
      dsimp [g]; cases f k <;> simp <;> ring
    rw [h1, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlo, zero_add]
  rw [hdiv]
  cases f k <;> simp

/- Elementary bipartite edge count bound. -/

lemma induce_edgeSet_ncard_le {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A T1 T2 D1 D2 : Finset V)
    (hA_ind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (hT_ind : ∀ u ∈ T1 ∪ T2, ∀ v ∈ T1 ∪ T2, ¬ G.Adj u v)
    (hD1 : ∀ u ∈ A, ∀ v ∈ T1, G.Adj u v → u ∈ D1)
    (hD2 : ∀ u ∈ A, ∀ v ∈ T2, G.Adj u v → u ∈ D2) :
    (G.induce ((A ∪ T1 ∪ T2 : Finset V) : Set V)).edgeSet.ncard ≤
      T1.card * D1.card + T2.card * D2.card := by
  classical
  let W : Finset V := A ∪ T1 ∪ T2
  let emb : Sym2 W ↪ Sym2 V :=
    ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩
  let Eset : Finset (Sym2 W) := (G.induce (W : Set V)).edgeFinset
  have hncard : (G.induce (W : Set V)).edgeSet.ncard = Eset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hncard]
  let img : Finset (Sym2 V) := Eset.map emb
  have hcard_eq : Eset.card = img.card := (Finset.card_map emb).symm
  rw [hcard_eq]
  let B1 : Finset (Sym2 V) := (T1 ×ˢ D1).image fun p => s(p.1, p.2)
  let B2 : Finset (Sym2 V) := (T2 ×ˢ D2).image fun p => s(p.1, p.2)
  have hsub : img ⊆ B1 ∪ B2 := by
    intro e he
    rcases Finset.mem_map.mp he with ⟨e', he', rfl⟩
    rw [SimpleGraph.mem_edgeFinset] at he'
    induction e' using Sym2.ind with
    | _ x y =>
      have hadj : G.Adj x.1 y.1 := he'
      have hxW : x.1 ∈ W := x.2
      have hyW : y.1 ∈ W := y.2
      have hmem : ∀ z ∈ W, z ∈ A ∨ z ∈ T1 ∪ T2 := by
        intro z hz
        simp only [W, Finset.mem_union] at hz ⊢
        tauto
      have hsym : emb s(x, y) = s(x.1, y.1) := rfl
      rw [hsym]
      rcases hmem x.1 hxW with hxA | hxT <;> rcases hmem y.1 hyW with hyA | hyT
      · exact False.elim (hA_ind x.1 hxA y.1 hyA hadj)
      · rcases Finset.mem_union.mp hyT with hy1 | hy2
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(y.1, x.1), ?_, Sym2.eq_swap⟩)
          exact Finset.mem_product.mpr ⟨hy1, hD1 x.1 hxA y.1 hy1 hadj⟩
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(y.1, x.1), ?_, Sym2.eq_swap⟩)
          exact Finset.mem_product.mpr ⟨hy2, hD2 x.1 hxA y.1 hy2 hadj⟩
      · rcases Finset.mem_union.mp hxT with hx1 | hx2
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(x.1, y.1), ?_, rfl⟩)
          exact Finset.mem_product.mpr ⟨hx1, hD1 y.1 hyA x.1 hx1 hadj.symm⟩
        · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x.1, y.1), ?_, rfl⟩)
          exact Finset.mem_product.mpr ⟨hx2, hD2 y.1 hyA x.1 hx2 hadj.symm⟩
      · exact False.elim (hT_ind x.1 hxT y.1 hyT hadj)
  calc
    img.card ≤ (B1 ∪ B2).card := Finset.card_le_card hsub
    _ ≤ B1.card + B2.card := Finset.card_union_le B1 B2
    _ ≤ (T1 ×ˢ D1).card + (T2 ×ˢ D2).card := add_le_add Finset.card_image_le Finset.card_image_le
    _ = T1.card * D1.card + T2.card * D2.card := by rw [Finset.card_product, Finset.card_product]

/- Arithmetic helpers on `Fin 11`. -/

lemma fin11_j1_add1_false (i : Fin 11) : i + 2 * dir false + 1 = i + 10 := by
  fin_cases i <;> decide
lemma fin11_j1_add10_true (i : Fin 11) : i + 2 * dir true + 10 = i + 1 := by
  fin_cases i <;> decide
lemma fin11_j2_add1_false (i : Fin 11) : i + 5 * dir false + 1 = i + 7 := by
  fin_cases i <;> decide
lemma fin11_j2_add10_true (i : Fin 11) : i + 5 * dir true + 10 = i + 4 := by
  fin_cases i <;> decide
lemma fin11_j1_add10_false (i : Fin 11) : i + 2 * dir false + 10 = i + 8 := by
  fin_cases i <;> decide
lemma fin11_j1_add1_true (i : Fin 11) : i + 2 * dir true + 1 = i + 3 := by
  fin_cases i <;> decide
lemma fin11_j2_add10_false (i : Fin 11) : i + 5 * dir false + 10 = i + 5 := by
  fin_cases i <;> decide
lemma fin11_j2_add4_false (i : Fin 11) : i + 5 * dir false + 4 = i + 10 := by
  fin_cases i <;> decide
lemma fin11_j1_add4_false (i : Fin 11) : i + 2 * dir false + 4 = i + 2 := by
  fin_cases i <;> decide
lemma fin11_j2_add7_false (i : Fin 11) : i + 5 * dir false + 7 = i + 2 := by
  fin_cases i <;> decide
lemma fin11_j1_add7_false (i : Fin 11) : i + 2 * dir false + 7 = i + 5 := by
  fin_cases i <;> decide
lemma fin11_j2_add1_true (i : Fin 11) : i + 5 * dir true + 1 = i + 6 := by
  fin_cases i <;> decide
lemma fin11_j1_add4_true (i : Fin 11) : i + 2 * dir true + 4 = i + 6 := by
  fin_cases i <;> decide
lemma fin11_j1_add7_true (i : Fin 11) : i + 2 * dir true + 7 = i + 9 := by
  fin_cases i <;> decide
lemma fin11_j2_add4_true (i : Fin 11) : i + 5 * dir true + 4 = i + 9 := by
  fin_cases i <;> decide
lemma fin11_j2_add7_true (i : Fin 11) : i + 5 * dir true + 7 = i + 1 := by
  fin_cases i <;> decide
lemma fin11_add7_add1 (i : Fin 11) : i + 8 = (i + 7) + 1 := by
  fin_cases i <;> decide
lemma fin11_add3_add1 (i : Fin 11) : i + 4 = (i + 3) + 1 := by
  fin_cases i <;> decide

/- Graph classification and helper lemmas for the Band `And(4)` subcase. -/

lemma no_tri_of_cliqueFree3 {V : Type} {G : SimpleGraph V} (hTF : G.CliqueFree 3)
    {u v w : V} (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) : False := by
  classical
  have hcl : G.IsNClique 3 ({u, v, w} : Finset V) := by
    refine ⟨?_, ?_⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      · exact (hab rfl).elim
      · exact huv
      · exact huw
      · exact huv.symm
      · exact (hab rfl).elim
      · exact hvw
      · exact huw.symm
      · exact hvw.symm
      · exact (hab rfl).elim
    · have hne1 : u ≠ v := G.ne_of_adj huv
      have hne2 : u ≠ w := G.ne_of_adj huw
      have hne3 : v ≠ w := G.ne_of_adj hvw
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hne3]
      · simp [hne1, hne2]
  exact hTF {u, v, w} hcl

lemma card_filter_vType {V : Type} [Fintype V] [DecidableEq V] (vType : V → Fin 89)
    (P : Fin 89 → Bool) :
    ((Finset.univ.filter fun v : V => P (vType v) = true).card : ℤ) =
    ∑ a : Fin 89, b2z (P a) * ((Finset.univ.filter fun v : V => vType v = a).card : ℤ) := by
  have h1 : (Finset.univ.filter fun v : V => P (vType v) = true).card =
      ∑ a : Fin 89, ((Finset.univ.filter fun v : V => vType v = a).filter fun v => P (vType v) = true).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      exact ⟨fun h => ⟨vType v, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
    · intro a _ b _ hab
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
      exact hab (hv1.1.symm.trans hv2.1)
  rw [h1, Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases hPa : P a
  · have hemp : ((Finset.univ.filter fun v : V => vType v = a).filter fun v => P (vType v) = true) = ∅ := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, h⟩; rw [hPa] at h; exact Bool.false_ne_true h
    rw [hemp]; simp [b2z]
  · have hfull : ((Finset.univ.filter fun v : V => vType v = a).filter fun v => P (vType v) = true) =
        (Finset.univ.filter fun v : V => vType v = a) := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
      rintro rfl; exact hPa
    rw [hfull]; simp [b2z]

lemma pair_quad_bound {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (h50 : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (φ : Fin 11 → V)
    (hφ : ∀ i j : Fin 11, (j = i + 1 ∨ j = i + 4 ∨ j = i + 7 ∨ j = i + 10) → G.Adj (φ i) (φ j))
    (vType : V → Fin 89)
    (hadj_iff : ∀ (v : V) (k : Fin 11), G.Adj (φ k) v ↔ hasBit (maskOf (vType v)) k = true)
    (hg_nonneg : ∀ k : Fin 11,
      0 ≤ ∑ a : Fin 89, gCoeff k a * ((Finset.univ.filter fun v : V => vType v = a).card : ℤ))
    (i : Fin 11) (d : Bool) :
    let n := Fintype.card V
    let S := Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true
    let Vp1 := Finset.univ.filter fun v : V => inVp (i + 2 * dir d) (maskOf (vType v)) = true
    let D1 := Finset.univ.filter fun v : V => d1Pred i d (vType v) = true
    let DIFF := Finset.univ.filter fun v : V => diffPred i d (vType v) = true
    4 * (n : ℤ) ^ 2 <
      100 * ((n : ℤ) - 2 * (S.card : ℤ)) * (D1.card : ℤ) +
      25 * ((n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ) + (DIFF.card : ℤ)) ^ 2 := by
  classical
  dsimp only
  set n : ℕ := Fintype.card V
  set j1 : Fin 11 := i + 2 * dir d
  set j2 : Fin 11 := i + 5 * dir d
  set S : Finset V := Finset.univ.filter fun v => hasBit (maskOf (vType v)) i = true
  set Vp1 : Finset V := Finset.univ.filter fun v => inVp j1 (maskOf (vType v)) = true
  set Vp2 : Finset V := Finset.univ.filter fun v => inVp j2 (maskOf (vType v)) = true
  set D1 : Finset V := Finset.univ.filter fun v => d1Pred i d (vType v) = true
  set DIFF : Finset V := Finset.univ.filter fun v => diffPred i d (vType v) = true
  set D2 : Finset V := Finset.univ.filter fun v => canAdjVp i j2 (maskOf (vType v)) = true
  let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
  have hx_nonneg : ∀ a : Fin 89, 0 ≤ x a := fun a => Nat.cast_nonneg _
  have hn_sum : (n : ℤ) = ∑ a : Fin 89, x a := by
    simpa [n, b2z, x] using card_filter_vType vType (fun _ => true)
  -- `S` is independent and has `2 * |S| + 1 < n`.
  have hS_ind : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact no_tri_of_cliqueFree3 hTF ((hadj_iff u i).mpr hu) huv ((hadj_iff v i).mpr hv)
  have hS_small : 2 * S.card + 1 < n := by
    by_contra! hge
    have h50i := h50 (S : Set V) (by rw [Set.ncard_coe_finset]; exact hge)
    have hzero : (G.induce (S : Set V)).edgeSet.ncard = 0 := by
      have hemp : (G.induce (S : Set V)).edgeSet = ∅ := by
        ext e
        simp only [Set.mem_empty_iff_false, iff_false]
        induction e using Sym2.ind with
        | _ a b => intro h; exact hS_ind a.1 a.2 b.1 b.2 h
      rw [hemp, Set.ncard_empty]
    rw [hzero] at h50i
    nlinarith
  -- Disjointness of `S`, `Vp1`, `Vp2`.
  have h_disj_S_j1 : Disjoint S Vp1 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [S, Vp1, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hv1 hv2
    have hvi : G.Adj (φ i) v := (hadj_iff v i).mpr hv1
    cases d
    · have hvj : G.Adj (φ (i + 10)) v := by
        rw [← fin11_j1_add1_false i]; exact (hadj_iff v _).mpr hv2.1.2
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 10) (by simp)) hvj hvi
    · have hvj : G.Adj (φ (i + 1)) v := by
        rw [← fin11_j1_add10_true i]; exact (hadj_iff v _).mpr hv2.1.1
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 1) (by simp)) hvj hvi
  have h_disj_S_j2 : Disjoint S Vp2 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [S, Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hv1 hv2
    have hvi : G.Adj (φ i) v := (hadj_iff v i).mpr hv1
    cases d
    · have hvj : G.Adj (φ (i + 7)) v := by
        rw [← fin11_j2_add1_false i]; exact (hadj_iff v _).mpr hv2.1.2
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 7) (by simp)) hvj hvi
    · have hvj : G.Adj (φ (i + 4)) v := by
        rw [← fin11_j2_add10_true i]; exact (hadj_iff v _).mpr hv2.1.1
      exact no_tri_of_cliqueFree3 hTF (hφ i (i + 4) (by simp)) hvj hvi
  have h_disj_j1_j2 : Disjoint Vp1 Vp2 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Vp1, Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hv1 hv2
    cases d
    · have h1 : G.Adj (φ (i + 8)) v := by
        rw [← fin11_j1_add10_false i]; exact (hadj_iff v _).mpr hv1.1.1
      have h2 : G.Adj (φ (i + 7)) v := by
        rw [← fin11_j2_add1_false i]; exact (hadj_iff v _).mpr hv2.1.2
      have hphi : G.Adj (φ (i + 7)) (φ (i + 8)) := hφ (i + 7) (i + 8) (Or.inl (fin11_add7_add1 i))
      exact no_tri_of_cliqueFree3 hTF hphi h1 h2
    · have h1 : G.Adj (φ (i + 3)) v := by
        rw [← fin11_j1_add1_true i]; exact (hadj_iff v _).mpr hv1.1.2
      have h2 : G.Adj (φ (i + 4)) v := by
        rw [← fin11_j2_add10_true i]; exact (hadj_iff v _).mpr hv2.1.1
      have hphi : G.Adj (φ (i + 3)) (φ (i + 4)) := hφ (i + 3) (i + 4) (Or.inl (fin11_add3_add1 i))
      exact no_tri_of_cliqueFree3 hTF hphi h2 h1
  -- Independence of `Vp1 ∪ Vp2`.
  have hVp_ind : ∀ u ∈ Vp1 ∪ Vp2, ∀ v ∈ Vp1 ∪ Vp2, ¬ G.Adj u v := by
    have hcomm : ∀ u ∈ Vp1, ∀ v ∈ Vp2, ∃ k : Fin 11, G.Adj (φ k) u ∧ G.Adj (φ k) v := by
      intro u hu v hv
      simp only [Vp1, Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp,
        Bool.and_eq_true, Bool.or_eq_true] at hu hv
      cases d
      · have hu10 : G.Adj (φ (i + 10)) u := by
          rw [← fin11_j1_add1_false i]; exact (hadj_iff u _).mpr hu.1.2
        have hv5 : G.Adj (φ (i + 5)) v := by
          rw [← fin11_j2_add10_false i]; exact (hadj_iff v _).mpr hv.1.1
        rcases hv.2 with hv10 | hv2
        · refine ⟨i + 10, hu10, ?_⟩
          rw [← fin11_j2_add4_false i]; exact (hadj_iff v _).mpr hv10
        · rcases hu.2 with hu2 | hu5
          · refine ⟨i + 2, ?_, ?_⟩
            · rw [← fin11_j1_add4_false i]; exact (hadj_iff u _).mpr hu2
            · rw [← fin11_j2_add7_false i]; exact (hadj_iff v _).mpr hv2
          · refine ⟨i + 5, ?_, hv5⟩
            rw [← fin11_j1_add7_false i]; exact (hadj_iff u _).mpr hu5
      · have hu1 : G.Adj (φ (i + 1)) u := by
          rw [← fin11_j1_add10_true i]; exact (hadj_iff u _).mpr hu.1.1
        have hv6 : G.Adj (φ (i + 6)) v := by
          rw [← fin11_j2_add1_true i]; exact (hadj_iff v _).mpr hv.1.2
        rcases hv.2 with hv9 | hv1
        · rcases hu.2 with hu6 | hu9
          · refine ⟨i + 6, ?_, hv6⟩
            rw [← fin11_j1_add4_true i]; exact (hadj_iff u _).mpr hu6
          · refine ⟨i + 9, ?_, ?_⟩
            · rw [← fin11_j1_add7_true i]; exact (hadj_iff u _).mpr hu9
            · rw [← fin11_j2_add4_true i]; exact (hadj_iff v _).mpr hv9
        · refine ⟨i + 1, hu1, ?_⟩
          rw [← fin11_j2_add7_true i]; exact (hadj_iff v _).mpr hv1
    intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu1 | hu2 <;> rcases Finset.mem_union.mp hv with hv1 | hv2
    · simp only [Vp1, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hu1 hv1
      exact no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr hu1.1.2) huv ((hadj_iff v _).mpr hv1.1.2)
    · obtain ⟨k, hku, hkv⟩ := hcomm u hu1 v hv2
      exact no_tri_of_cliqueFree3 hTF hku huv hkv
    · obtain ⟨k, hkv, hku⟩ := hcomm v hv1 u hu2
      exact no_tri_of_cliqueFree3 hTF hku huv hkv
    · simp only [Vp2, Finset.mem_filter, Finset.mem_univ, true_and, inVp, Bool.and_eq_true] at hu2 hv2
      exact no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr hu2.1.2) huv ((hadj_iff v _).mpr hv2.1.2)
  -- Size bound `n ≤ 2 * (|S| + |Vp1| + |Vp2|)`.
  have hsize : n ≤ 2 * (S.card + Vp1.card + Vp2.card) := by
    have hsum_cert :
        (∑ m : Fin 7, ∑ a : Fin 89, gCoeff (i + Fin.ofNat 11 m.1 * dir d) a * x a) ≤
        ∑ a : Fin 89, 7 * (2 * (b2z (hasBit (maskOf a) i) +
          b2z (inVp j1 (maskOf a)) + b2z (inVp j2 (maskOf a))) - 1) * x a := by
      rw [Finset.sum_comm]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (size_cert_all i d a) (hx_nonneg a)
    have hlhs : 0 ≤ ∑ m : Fin 7, ∑ a : Fin 89, gCoeff (i + Fin.ofNat 11 m.1 * dir d) a * x a :=
      Finset.sum_nonneg fun m _ => hg_nonneg _
    have hrhs : (∑ a : Fin 89, 7 * (2 * (b2z (hasBit (maskOf a) i) +
          b2z (inVp j1 (maskOf a)) + b2z (inVp j2 (maskOf a))) - 1) * x a) =
        7 * (2 * ((S.card : ℤ) + (Vp1.card : ℤ) + (Vp2.card : ℤ)) - (n : ℤ)) := by
      have hS := card_filter_vType vType (fun a => hasBit (maskOf a) i)
      have hV1 := card_filter_vType vType (fun a => inVp j1 (maskOf a))
      have hV2 := card_filter_vType vType (fun a => inVp j2 (maskOf a))
      have hlin : ∀ a : Fin 89,
          7 * (2 * (b2z (hasBit (maskOf a) i) + b2z (inVp j1 (maskOf a)) +
            b2z (inVp j2 (maskOf a))) - 1) * x a =
          14 * (b2z (hasBit (maskOf a) i) * x a) +
          14 * (b2z (inVp j1 (maskOf a)) * x a) +
          14 * (b2z (inVp j2 (maskOf a)) * x a) - 7 * x a := fun a => by ring
      simp_rw [hlin, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      change 14 * (∑ a : Fin 89, b2z (hasBit (maskOf a) i) * x a) +
        14 * (∑ a : Fin 89, b2z (inVp j1 (maskOf a)) * x a) +
        14 * (∑ a : Fin 89, b2z (inVp j2 (maskOf a)) * x a) - 7 * (∑ a : Fin 89, x a) = _
      rw [← hS, ← hV1, ← hV2, ← hn_sum]
      ring
    have hge := hlhs.trans (hsum_cert.trans_eq hrhs)
    omega
  -- Adjacency containment in `D1` and `D2`.
  have hadj_vp : ∀ (j : Fin 11) (u : V), u ∈ S →
      ∀ v : V, inVp j (maskOf (vType v)) = true → G.Adj u v →
        canAdjVp i j (maskOf (vType u)) = true := by
    intro j u hu v hv huv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [inVp, Bool.and_eq_true, Bool.or_eq_true] at hv
    unfold canAdjVp
    have hn10 : hasBit (maskOf (vType u)) (j + 10) = false := by
      cases h : hasBit (maskOf (vType u)) (j + 10)
      · rfl
      · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h) huv ((hadj_iff v _).mpr hv.1.1))
    have hn1 : hasBit (maskOf (vType u)) (j + 1) = false := by
      cases h : hasBit (maskOf (vType u)) (j + 1)
      · rfl
      · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h) huv ((hadj_iff v _).mpr hv.1.2))
    have hn47 : (hasBit (maskOf (vType u)) (j + 4) && hasBit (maskOf (vType u)) (j + 7)) = false := by
      cases h4 : hasBit (maskOf (vType u)) (j + 4)
      · simp
      · cases h7 : hasBit (maskOf (vType u)) (j + 7)
        · simp
        · rcases hv.2 with hv4 | hv7
          · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h4) huv ((hadj_iff v _).mpr hv4))
          · exact False.elim (no_tri_of_cliqueFree3 hTF ((hadj_iff u _).mpr h7) huv ((hadj_iff v _).mpr hv7))
    simp [hu, hn10, hn1, hn47]
  -- Pick subsets `T1 ⊆ Vp1` and `T2 ⊆ Vp2` of total size `t = n / 2 - |S|`.
  let t : ℕ := n / 2 - S.card
  let r1 : ℕ := min t Vp1.card
  let r2 : ℕ := t - r1
  have hr1_le : r1 ≤ Vp1.card := min_le_right _ _
  have hr2_le : r2 ≤ Vp2.card := by omega
  obtain ⟨T1, hT1_sub, hT1_card⟩ := Finset.exists_subset_card_eq hr1_le
  obtain ⟨T2, hT2_sub, hT2_card⟩ := Finset.exists_subset_card_eq hr2_le
  have hdisj_ST1 : Disjoint S T1 := Disjoint.mono_right hT1_sub h_disj_S_j1
  have hdisj_ST2 : Disjoint S T2 := Disjoint.mono_right hT2_sub h_disj_S_j2
  have hdisj_T12 : Disjoint T1 T2 := Disjoint.mono hT1_sub hT2_sub h_disj_j1_j2
  have hW_card : (S ∪ T1 ∪ T2).card = n / 2 := by
    have hdisj_ST1_T2 : Disjoint (S ∪ T1) T2 := Finset.disjoint_union_left.mpr ⟨hdisj_ST2, hdisj_T12⟩
    rw [Finset.card_union_of_disjoint hdisj_ST1_T2, Finset.card_union_of_disjoint hdisj_ST1,
      hT1_card, hT2_card]
    omega
  have hW_half : 2 * ((S ∪ T1 ∪ T2 : Finset V) : Set V).ncard + 1 ≥ n := by
    rw [Set.ncard_coe_finset, hW_card]; omega
  have h50W := h50 ((S ∪ T1 ∪ T2 : Finset V) : Set V) hW_half
  have hedge : (G.induce ((S ∪ T1 ∪ T2 : Finset V) : Set V)).edgeSet.ncard ≤
      T1.card * D1.card + T2.card * D2.card := by
    refine induce_edgeSet_ncard_le G S T1 T2 D1 D2 hS_ind ?_ ?_ ?_
    · intro u hu v hv
      exact hVp_ind u (Finset.union_subset_union hT1_sub hT2_sub hu)
        v (Finset.union_subset_union hT1_sub hT2_sub hv)
    · intro u hu v hv huv
      have hv1 := (Finset.mem_filter.mp (hT1_sub hv)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj_vp j1 u hu v hv1 huv⟩
    · intro u hu v hv huv
      have hv2 := (Finset.mem_filter.mp (hT2_sub hv)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hadj_vp j2 u hu v hv2 huv⟩
  have hD2_le : D2.card ≤ D1.card + DIFF.card := by
    have hsub : D2 ⊆ D1 ∪ DIFF := by
      intro v hv
      have hv2 : canAdjVp i j2 (maskOf (vType v)) = true := (Finset.mem_filter.mp hv).2
      cases h1 : canAdjVp i j1 (maskOf (vType v))
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩)
        dsimp only [diffPred]
        rw [show i + 5 * dir d = j2 from rfl, show i + 2 * dir d = j1 from rfl, hv2, h1]
        rfl
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩)
        exact h1
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hgt : n ^ 2 < 50 * (t * D1.card + r2 * DIFF.card) := by
    have hr : r1 + r2 = t := by omega
    have h1 : T1.card * D1.card + T2.card * D2.card ≤ t * D1.card + r2 * DIFF.card := by
      rw [hT1_card, hT2_card]
      calc
        r1 * D1.card + r2 * D2.card
            ≤ r1 * D1.card + r2 * (D1.card + DIFF.card) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left r2 hD2_le) _
        _ = (r1 + r2) * D1.card + r2 * DIFF.card := by ring
        _ = t * D1.card + r2 * DIFF.card := by rw [hr]
    omega
  have hgtZ : (n : ℤ) ^ 2 < 50 * ((t : ℤ) * (D1.card : ℤ) + (r2 : ℤ) * (DIFF.card : ℤ)) := by
    exact_mod_cast hgt
  have htZ : 2 * (t : ℤ) ≤ (n : ℤ) - 2 * (S.card : ℤ) := by omega
  have hr2_bound : 8 * (r2 : ℤ) * (DIFF.card : ℤ) ≤
      ((n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ) + (DIFF.card : ℤ)) ^ 2 := by
    set U : ℤ := (n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ)
    set Y : ℤ := (DIFF.card : ℤ)
    have hY : 0 ≤ Y := Nat.cast_nonneg _
    have hr2_0 : 0 ≤ (r2 : ℤ) := Nat.cast_nonneg _
    by_cases hcase : t ≤ Vp1.card
    · have hr2_zero : (r2 : ℤ) = 0 := by omega
      rw [hr2_zero]; nlinarith
    · have h2r2 : 2 * (r2 : ℤ) ≤ U := by omega
      nlinarith [sq_nonneg (U - Y)]
  have hD1_nonneg : (0 : ℤ) ≤ (D1.card : ℤ) := Nat.cast_nonneg _
  have h100 : 200 * (t : ℤ) * (D1.card : ℤ) ≤ 100 * ((n : ℤ) - 2 * (S.card : ℤ)) * (D1.card : ℤ) := by
    nlinarith
  linarith

lemma mTerm_sum_identity {V : Type} [Fintype V] [DecidableEq V] (vType : V → Fin 89)
    (i : Fin 11) (d : Bool) :
    let n := Fintype.card V
    let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
    let S := Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true
    let Vp1 := Finset.univ.filter fun v : V => inVp (i + 2 * dir d) (maskOf (vType v)) = true
    let D1 := Finset.univ.filter fun v : V => d1Pred i d (vType v) = true
    let DIFF := Finset.univ.filter fun v : V => diffPred i d (vType v) = true
    100 * ((n : ℤ) - 2 * (S.card : ℤ)) * (D1.card : ℤ) +
    25 * ((n : ℤ) - 2 * (S.card : ℤ) - 2 * (Vp1.card : ℤ) + (DIFF.card : ℤ)) ^ 2 - 4 * (n : ℤ) ^ 2 =
    ∑ a : Fin 89, ∑ b : Fin 89, mTerm i d a b * x a * x b := by
  dsimp only
  set n : ℕ := Fintype.card V
  let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
  have hn_sum : (n : ℤ) = ∑ a : Fin 89, x a := by
    simpa [n, b2z, x] using card_filter_vType vType (fun _ => true)
  let u0 : Fin 89 → ℤ := fun a => 1 - 2 * b2z (hasBit (maskOf a) i)
  let d1 : Fin 89 → ℤ := fun a => b2z (d1Pred i d a)
  let v2 : Fin 89 → ℤ := fun a => u0 a - 2 * b2z (inVp (i + 2 * dir d) (maskOf a)) + b2z (diffPred i d a)
  have hU0 : (n : ℤ) - 2 * ((Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true).card : ℤ) =
      ∑ a : Fin 89, u0 a * x a := by
    have hS := card_filter_vType vType (fun a => hasBit (maskOf a) i)
    rw [hn_sum, hS]
    simp only [u0, sub_mul, one_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum, x]
  have hD1 : ((Finset.univ.filter fun v : V => d1Pred i d (vType v) = true).card : ℤ) =
      ∑ a : Fin 89, d1 a * x a := card_filter_vType vType (d1Pred i d)
  have hV2 : (n : ℤ) - 2 * ((Finset.univ.filter fun v : V => hasBit (maskOf (vType v)) i = true).card : ℤ) -
      2 * ((Finset.univ.filter fun v : V => inVp (i + 2 * dir d) (maskOf (vType v)) = true).card : ℤ) +
      ((Finset.univ.filter fun v : V => diffPred i d (vType v) = true).card : ℤ) =
      ∑ a : Fin 89, v2 a * x a := by
    have hVp := card_filter_vType vType (fun a => inVp (i + 2 * dir d) (maskOf a))
    have hDf := card_filter_vType vType (diffPred i d)
    rw [hU0, hVp, hDf]
    simp only [v2, add_mul, sub_mul, mul_assoc, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, x]
  rw [hV2, hU0, hD1, hn_sum]
  have hbilin : ∀ f g : Fin 89 → ℤ,
      (∑ a : Fin 89, f a * x a) * (∑ b : Fin 89, g b * x b) =
      ∑ a : Fin 89, ∑ b : Fin 89, (f a * g b) * x a * x b := by
    intro f g
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => by ring
  have h100 : 100 * (∑ a : Fin 89, u0 a * x a) * (∑ b : Fin 89, d1 b * x b) =
      50 * ((∑ a : Fin 89, u0 a * x a) * (∑ b : Fin 89, d1 b * x b)) +
      50 * ((∑ a : Fin 89, d1 a * x a) * (∑ b : Fin 89, u0 b * x b)) := by
    have hsym : (∑ a : Fin 89, u0 a * x a) * (∑ b : Fin 89, d1 b * x b) =
        (∑ a : Fin 89, d1 a * x a) * (∑ b : Fin 89, u0 b * x b) := mul_comm _ _
    linarith
  rw [h100, sq, sq, hbilin u0 d1, hbilin d1 u0, hbilin v2 v2]
  have h11 : (∑ a : Fin 89, x a) * (∑ b : Fin 89, x b) =
      ∑ a : Fin 89, ∑ b : Fin 89, (1 : ℤ) * x a * x b := by
    simpa using hbilin (fun _ => 1) (fun _ => 1)
  rw [h11]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  dsimp [mTerm, u0, d1, v2]; ring

/- Main proof of `H2`. -/

theorem main_proof : R2H1R1.H2 := by
  classical
  intro V _ G hTF _hmax h50 hδ _h3 _hnoG ⟨φ, hφ⟩
  let vMask : V → ℕ := fun v => ∑ k : Fin 11, if decide (G.Adj (φ k) v) then pow2 k else 0
  have hvMask_lt : ∀ v : V, vMask v < 2048 := fun v => sum_pow2_lt (fun k => decide (G.Adj (φ k) v))
  have hbit_vMask : ∀ (v : V) (k : Fin 11), hasBit (vMask v) k = decide (G.Adj (φ k) v) :=
    fun v k => hasBit_sum_pow2 (fun j => decide (G.Adj (φ j) v)) k
  have hisIndep : ∀ v : V, isIndepMask (vMask v) = true := by
    intro v
    unfold isIndepMask
    rw [List.all_eq_true]
    intro i _
    by_cases hi : G.Adj (φ i) v
    · have hb_i : hasBit (vMask v) i = true := by rw [hbit_vMask]; simp [hi]
      have hnot : ∀ d : Fin 11, (d = 1 ∨ d = 4 ∨ d = 7 ∨ d = 10) →
          hasBit (vMask v) (i + d) = false := by
        intro d hd
        rw [hbit_vMask, decide_eq_false_iff_not]
        intro h2
        have hphi : G.Adj (φ i) (φ (i + d)) := by
          apply hφ i (i + d)
          rcases hd with rfl | rfl | rfl | rfl <;> simp
        exact no_tri_of_cliqueFree3 hTF hphi h2 hi
      rw [hb_i, hnot 1 (by simp), hnot 4 (by simp), hnot 7 (by simp), hnot 10 (by simp)]
      rfl
    · have hb_i : hasBit (vMask v) i = false := by rw [hbit_vMask]; simp [hi]
      rw [hb_i]; rfl
  let vType : V → Fin 89 := fun v => idxOfMask (vMask v)
  have hmask_eq : ∀ v : V, maskOf (vType v) = vMask v := fun v =>
    maskOf_idxOfMask (vMask v) (hvMask_lt v) (hisIndep v)
  have hadj_iff : ∀ (v : V) (k : Fin 11), G.Adj (φ k) v ↔ hasBit (maskOf (vType v)) k = true := by
    intro v k
    rw [hmask_eq, hbit_vMask, decide_eq_true_eq]
  let x : Fin 89 → ℤ := fun a => ((Finset.univ.filter fun v : V => vType v = a).card : ℤ)
  have hx_nonneg : ∀ a : Fin 89, 0 ≤ x a := fun a => Nat.cast_nonneg _
  have hn_sum : (Fintype.card V : ℤ) = ∑ a : Fin 89, x a := by
    simpa [b2z, x] using card_filter_vType vType (fun _ => true)
  have hg_nonneg : ∀ k : Fin 11, 0 ≤ ∑ a : Fin 89, gCoeff k a * x a := by
    intro k
    let Sk : Finset V := Finset.univ.filter fun v => hasBit (maskOf (vType v)) k = true
    have hset : (Sk : Set V) = G.neighborSet (φ k) := by
      ext v
      simp only [Sk, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborSet]
      exact (hadj_iff v k).symm
    have hdeg : 5 * Fintype.card V ≤ 14 * Sk.card := by
      have hcard : (G.neighborSet (φ k)).ncard = Sk.card := by rw [← hset, Set.ncard_coe_finset]
      rw [← hcard]; exact hδ (φ k)
    have h1 : (∑ a : Fin 89, gCoeff k a * x a) = 14 * (Sk.card : ℤ) - 5 * (Fintype.card V : ℤ) := by
      have hS := card_filter_vType vType (fun a => hasBit (maskOf a) k)
      change (∑ a : Fin 89, (14 * b2z (hasBit (maskOf a) k) - 5) * x a) = _
      simp_rw [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
      change 14 * (∑ a : Fin 89, b2z (hasBit (maskOf a) k) * x a) - 5 * (∑ a : Fin 89, x a) = _
      rw [← hS, ← hn_sum]
    rw [h1]
    omega
  have hsum_pos : (0 : ℤ) < ∑ a : Fin 89, ∑ b : Fin 89, mInt a b * x a * x b := by
    have h22 : (0 : ℤ) < ∑ i : Fin 11,
        ((∑ a : Fin 89, ∑ b : Fin 89, mTerm i true a b * x a * x b) +
         (∑ a : Fin 89, ∑ b : Fin 89, mTerm i false a b * x a * x b)) := by
      refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
      have ht := pair_quad_bound G hTF h50 φ hφ vType hadj_iff hg_nonneg i true
      have hf := pair_quad_bound G hTF h50 φ hφ vType hadj_iff hg_nonneg i false
      have hteq := mTerm_sum_identity vType i true
      have hfeq := mTerm_sum_identity vType i false
      dsimp only at ht hf hteq hfeq
      linarith
    refine lt_of_lt_of_eq h22 ?_
    simp_rw [← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold mInt
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hLG_nonneg : (0 : ℤ) ≤ ∑ a : Fin 89, ∑ b : Fin 89, symLG a b * x a * x b := by
    have heq : (∑ a : Fin 89, ∑ b : Fin 89, symLG a b * x a * x b) =
        2 * ∑ k : Fin 11, (∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b) := by
      have hterm : ∀ k : Fin 11,
          2 * ((∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b)) =
          ∑ a : Fin 89, ∑ b : Fin 89,
            (Lval (invSh k a) * gCoeff k b + gCoeff k a * Lval (invSh k b)) * x a * x b := by
        intro k
        have h1 : (∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b) =
            ∑ a : Fin 89, ∑ b : Fin 89, (Lval (invSh k a) * gCoeff k b) * x a * x b := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring
        have h2 : (∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b) =
            ∑ a : Fin 89, ∑ b : Fin 89, (gCoeff k a * Lval (invSh k b)) * x a * x b := by
          rw [mul_comm, Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => by ring
        calc
          2 * ((∑ a : Fin 89, Lval (invSh k a) * x a) * (∑ b : Fin 89, gCoeff k b * x b))
              = (∑ a : Fin 89, ∑ b : Fin 89, (Lval (invSh k a) * gCoeff k b) * x a * x b) +
                (∑ a : Fin 89, ∑ b : Fin 89, (gCoeff k a * Lval (invSh k b)) * x a * x b) := by
                  rw [← h1, ← h2]; ring
          _ = _ := by
                simp only [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [Finset.mul_sum]
      simp_rw [hterm]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      unfold symLG
      simp only [Finset.sum_mul]
    rw [heq]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ => ?_)
    exact mul_nonneg
      (Finset.sum_nonneg fun a _ => mul_nonneg (Lval_nonneg _) (hx_nonneg a))
      (hg_nonneg k)
  have hcomb_pos : (0 : ℤ) < ∑ a : Fin 89, ∑ b : Fin 89, certMat a b * x a * x b := by
    have heq : (∑ a : Fin 89, ∑ b : Fin 89, certMat a b * x a * x b) =
        20 * (∑ a : Fin 89, ∑ b : Fin 89, mInt a b * x a * x b) +
        (∑ a : Fin 89, ∑ b : Fin 89, symLG a b * x a * x b) := by
      simp only [certMat, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [heq]
    linarith
  have hcomb_nonpos : (∑ a : Fin 89, ∑ b : Fin 89, certMat a b * x a * x b) ≤ 0 := by
    refine Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => ?_
    have hxy : 0 ≤ x a * x b := mul_nonneg (hx_nonneg a) (hx_nonneg b)
    have hmul : certMat a b * (x a * x b) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (certMat_nonpos a b) hxy
    linarith
  linarith

end Erdos128_R2_H1_R1_H2

theorem OMA.solution : OMA.R_Erdos128_erdos_128_R1_H2_R1_H2_R1.H2 := by
  intro V _ G hTF _h3e _h5e _h38 h14 h5a
  by_contra hH
  push Not at hH
  by_cases h3 : G.Colorable 3
  · exact R2.not_colorable_three_of_gt_third G hTF hH
      (fun v => by
        have hv := h14 v
        have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
        omega) h3
  · exact R2H1R1.main_band Erdos128_R2_H1_R1_H1.main_proof Erdos128_R2_H1_R1_H2.main_proof
      V G h5a h3 h14 hH hTF
