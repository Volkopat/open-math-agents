import OMAStatements.S_oeis_a126236

namespace OMA

open OMA.S_oeis_a126236
open CodeTree
open Classical

private lemma multiset_exists_min_weight (F : Multiset CodeTree) (hF : F ≠ 0) :
    ∃ a ∈ F, ∀ t ∈ F, a.weight ≤ t.weight := by
  classical
  have hne : F.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    exact hF
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image F.toFinset CodeTree.weight hne
  exact ⟨a, Multiset.mem_toFinset.mp ha, fun t ht => hmin t (Multiset.mem_toFinset.mpr ht)⟩

private lemma exists_huffman_of_pos :
    ∀ (m : ℕ) (F : Multiset CodeTree), F.card = m → 1 ≤ m →
      ∃ T : CodeTree, Relation.ReflTransGen HuffmanStep F {T} := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro F hcard hm
    by_cases hm1 : m = 1
    · subst hm1
      obtain ⟨T, rfl⟩ := Multiset.card_eq_one.mp hcard
      exact ⟨T, Relation.ReflTransGen.refl⟩
    · have hm2 : 2 ≤ m := by omega
      have hF0 : F ≠ 0 := by
        intro h
        rw [h, Multiset.card_zero] at hcard
        omega
      obtain ⟨a, haF, ha_min⟩ := multiset_exists_min_weight F hF0
      set F₁ := F.erase a
      have hF₁_card : F₁.card = m - 1 := by
        rw [Multiset.card_erase_of_mem haF, hcard, Nat.pred_eq_sub_one]
      have hF₁0 : F₁ ≠ 0 := by
        intro h
        rw [h, Multiset.card_zero] at hF₁_card
        omega
      obtain ⟨b, hbF₁, hb_min⟩ := multiset_exists_min_weight F₁ hF₁0
      set F₂ := F₁.erase b
      have hF₂_eq : F = a ::ₘ b ::ₘ F₂ := by
        rw [Multiset.cons_erase hbF₁, Multiset.cons_erase haF]
      have ha_le : ∀ t ∈ F₂, a.weight ≤ t.weight := fun t ht =>
        ha_min t (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase ht))
      have hb_le : ∀ t ∈ F₂, b.weight ≤ t.weight := fun t ht =>
        hb_min t (Multiset.mem_of_mem_erase ht)
      have hstep : HuffmanStep F ({node a b} + F₂) := by
        rw [hF₂_eq]
        exact HuffmanStep.merge F₂ a b ha_le hb_le
      have hcard' : ({node a b} + F₂).card = m - 1 := by
        rw [Multiset.card_add, Multiset.card_singleton, Multiset.card_erase_of_mem hbF₁, hF₁_card,
            Nat.pred_eq_sub_one]
        omega
      obtain ⟨T, hT⟩ := ih (m - 1) (by omega) ({node a b} + F₂) hcard' (by omega)
      exact ⟨T, Relation.ReflTransGen.head hstep hT⟩

private lemma huffman_singleton_eq {t T : CodeTree}
    (h : Relation.ReflTransGen HuffmanStep {t} {T}) : t = T := by
  rcases Relation.ReflTransGen.cases_head h with heq | hstep
  · exact Multiset.singleton_inj.mp heq
  · rcases hstep with ⟨F', hst, _⟩
    generalize hsrc : ({t} : Multiset CodeTree) = src at hst
    cases hst with
    | merge G a b _ _ =>
      have hc := congrArg Multiset.card hsrc
      simp only [Multiset.card_singleton, Multiset.card_cons] at hc
      omega

private lemma huffman_unique_pair {x y : CodeTree} {R F' : Multiset CodeTree}
    (hx : ∀ t ∈ R, x.weight < t.weight)
    (hy : ∀ t ∈ R, y.weight < t.weight)
    (hstep : HuffmanStep (x ::ₘ y ::ₘ R) F') :
    F' = {node x y} + R ∨ F' = {node y x} + R := by
  generalize heq : x ::ₘ y ::ₘ R = src at hstep
  cases hstep with
  | merge G a b ha hb =>
    have ha_mem : a ∈ x ::ₘ y ::ₘ R := by
      rw [heq]; exact Multiset.mem_cons_self a (b ::ₘ G)
    have hb_mem : b ∈ x ::ₘ y ::ₘ R := by
      rw [heq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self b G)
    have hxy_mem : x ∈ a ::ₘ b ::ₘ G ∧ y ∈ a ::ₘ b ::ₘ G := by
      rw [← heq]
      exact ⟨Multiset.mem_cons_self x (y ::ₘ R),
             Multiset.mem_cons_of_mem (Multiset.mem_cons_self y R)⟩
    rcases Multiset.mem_cons.mp ha_mem with hax | ha'
    · subst hax
      have hG : b ::ₘ G = y ::ₘ R := by
        have h1 := congrArg (Multiset.erase · a) heq
        simpa [Multiset.erase_cons_head] using h1.symm
      have hb_mem2 : b ∈ y ::ₘ R := by rw [← hG]; exact Multiset.mem_cons_self b G
      rcases Multiset.mem_cons.mp hb_mem2 with hby | hbR
      · subst hby
        left
        have hGR : G = R := by
          have h1 := congrArg (Multiset.erase · b) hG
          simpa [Multiset.erase_cons_head] using h1
        rw [hGR]
      · exfalso
        have hyG : y ∈ G := by
          have := Multiset.mem_cons.mp (by rw [hG]; exact Multiset.mem_cons_self y R)
          rcases this with hyb | hyG
          · rw [← hyb] at hbR
            exact absurd (hy y hbR) (lt_irrefl _)
          · exact hyG
        exact absurd (hb y hyG) (not_le_of_gt (hy b hbR))
    · rcases Multiset.mem_cons.mp ha' with hay | haR
      · subst hay
        have hG : b ::ₘ G = x ::ₘ R := by
          have h1 : (a ::ₘ b ::ₘ G).erase a = (a ::ₘ x ::ₘ R).erase a := by
            rw [← heq, Multiset.cons_swap x a R]
          simpa [Multiset.erase_cons_head] using h1
        have hb_mem2 : b ∈ x ::ₘ R := by rw [← hG]; exact Multiset.mem_cons_self b G
        rcases Multiset.mem_cons.mp hb_mem2 with hbx | hbR
        · subst hbx
          right
          have hGR : G = R := by
            have h1 := congrArg (Multiset.erase · b) hG
            simpa [Multiset.erase_cons_head] using h1
          rw [hGR]
        · exfalso
          have hxG : x ∈ G := by
            have := Multiset.mem_cons.mp (by rw [hG]; exact Multiset.mem_cons_self x R)
            rcases this with hxb | hxG
            · rw [← hxb] at hbR
              exact absurd (hx x hbR) (lt_irrefl _)
            · exact hxG
          exact absurd (hb x hxG) (not_le_of_gt (hx b hbR))
      · exfalso
        rcases Multiset.mem_cons.mp hxy_mem.1 with hxa | hx'
        · exact absurd (hx a haR) (by rw [hxa]; exact lt_irrefl _)
        · rcases Multiset.mem_cons.mp hx' with hxb | hxG
          · rcases Multiset.mem_cons.mp hxy_mem.2 with hya | hy'
            · exact absurd (hy a haR) (by rw [hya]; exact lt_irrefl _)
            · rcases Multiset.mem_cons.mp hy' with hyb | hyG
              · have hba : b ≠ a := by
                  intro h; have := hx a haR; rw [hxb, h] at this; exact lt_irrefl _ this
                have hb_eq1 : Multiset.count b (x ::ₘ y ::ₘ R) = 2 + Multiset.count b R := by
                  simp [Multiset.count_cons, hxb, hyb]; omega
                have hb_eq2 : Multiset.count b (a ::ₘ b ::ₘ G) = 1 + Multiset.count b G := by
                  simp [Multiset.count_cons, hba]; omega
                have hc := congrArg (Multiset.count b) heq
                have hbG : b ∈ G := Multiset.count_pos.mp (by omega)
                have h1 := ha b hbG
                have h2 := hx a haR
                rw [hxb] at h2
                omega
              · exact absurd (ha y hyG) (not_le_of_gt (hy a haR))
          · exact absurd (ha x hxG) (not_le_of_gt (hx a haR))

private def IsPhase1Tree (j : ℕ) (t : CodeTree) : Prop :=
  t.weight = 3 * j ∧ t.maxCodewordLength ≤ Nat.log 2 j + 1 ∧
    (∀ m, j = 2 ^ m → t.maxCodewordLength = m + 1)

private lemma phase1_reach (n : ℕ) (k : ℕ) (hk : 1 ≤ k) (hn_lo : 3 * 2 ^ (k - 1) ≤ n)
    (T : CodeTree) (hT : IsHuffmanTree n T) :
    ∀ r ≤ 2 ^ (k - 1),
      ∃ (merged : Multiset CodeTree),
        merged.card = r ∧
        (∀ j ∈ Finset.Ico (r + 1) (2 * r + 1),
          ∃ t ∈ merged, IsPhase1Tree j t) ∧
        (∀ t ∈ merged, ∃ j ∈ Finset.Ico (r + 1) (2 * r + 1), IsPhase1Tree j t) ∧
        (∀ j ∈ Finset.Ico (r + 1) (2 * r + 1),
          (merged.filter (fun t => t.weight = 3 * j)).card = 1) ∧
        Relation.ReflTransGen HuffmanStep
          (merged + ((Finset.Icc (3 * r + 1) n).val.map leaf)) {T} := by
  intro r hr
  induction r with
  | zero =>
    refine ⟨0, rfl, ?_, ?_, ?_, ?_⟩
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      omega
    · intro t ht
      simp at ht
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      omega
    · simpa [IsHuffmanTree, initialForest] using hT
  | succ r ih =>
    obtain ⟨merged, hcard, hmem, hall, huniq, hreach⟩ := ih (by omega)
    have hr_bound : 3 * (r + 1) ≤ n :=
      le_trans (Nat.mul_le_mul_left 3 hr) hn_lo
    set leaves := (Finset.Icc (3 * r + 1) n).val.map leaf
    set leaves₁ := (Finset.Icc (3 * r + 3) n).val.map leaf
    have hleaves_split : leaves = leaf (3 * r + 1) ::ₘ leaf (3 * r + 2) ::ₘ leaves₁ := by
      have hsub : Finset.Icc (3 * r + 1) n =
          insert (3 * r + 1) (insert (3 * r + 2) (Finset.Icc (3 * r + 3) n)) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hnot1 : 3 * r + 1 ∉ insert (3 * r + 2) (Finset.Icc (3 * r + 3) n) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hnot2 : 3 * r + 2 ∉ Finset.Icc (3 * r + 3) n := by
        simp only [Finset.mem_Icc]
        omega
      rw [show leaves = (Finset.Icc (3 * r + 1) n).val.map leaf from rfl, hsub,
          Finset.insert_val_of_notMem hnot1, Finset.insert_val_of_notMem hnot2,
          Multiset.map_cons, Multiset.map_cons]
    set R₁ := merged + leaves₁
    have hR₁_gt : ∀ t ∈ R₁, (leaf (3 * r + 2)).weight < t.weight := by
      intro t ht
      rcases Multiset.mem_add.mp ht with htM | htL
      · obtain ⟨j, hj, hjt⟩ := hall t htM
        simp only [Finset.mem_Ico] at hj
        simp only [weight, hjt.1]
        omega
      · simp only [leaves₁, Multiset.mem_map, Finset.mem_val, Finset.mem_Icc] at htL
        obtain ⟨i, hi, rfl⟩ := htL
        simp only [weight]
        omega
    have hR₁_gt1 : ∀ t ∈ R₁, (leaf (3 * r + 1)).weight < t.weight := by
      intro t ht
      have := hR₁_gt t ht
      simp only [weight] at this ⊢
      omega
    have hstep1_cases : ∃ F₁, HuffmanStep (merged + leaves) F₁ ∧
        Relation.ReflTransGen HuffmanStep F₁ {T} := by
      rcases Relation.ReflTransGen.cases_head hreach with heq | h
      · exfalso
        have hc := congrArg Multiset.card heq
        rw [Multiset.card_add, hleaves_split, Multiset.card_cons, Multiset.card_cons,
            Multiset.card_singleton] at hc
        omega
      · exact h
    obtain ⟨F₁, hstep1, hreach1⟩ := hstep1_cases
    have hF₁_eq : F₁ = {node (leaf (3 * r + 1)) (leaf (3 * r + 2))} + R₁ ∨
        F₁ = {node (leaf (3 * r + 2)) (leaf (3 * r + 1))} + R₁ := by
      apply huffman_unique_pair hR₁_gt1 hR₁_gt
      have : merged + leaves = leaf (3 * r + 1) ::ₘ leaf (3 * r + 2) ::ₘ R₁ := by
        rw [hleaves_split]
        simp only [R₁, Multiset.add_cons, Multiset.cons_add, add_comm, add_left_comm, add_assoc]
      rw [← this]
      exact hstep1
    have hF₁_form : ∃ u, IsPhase1Tree (2 * r + 1) u ∧
        u ::ₘ merged + leaves₁ = F₁ := by
      have hu_prop : ∀ a b, (a = leaf (3 * r + 1) ∧ b = leaf (3 * r + 2)) ∨
          (a = leaf (3 * r + 2) ∧ b = leaf (3 * r + 1)) →
          IsPhase1Tree (2 * r + 1) (node a b) := by
        intro a b hab
        have hm_zero : ∀ m, 2 * r + 1 = 2 ^ m → m = 0 := by
          intro m hm
          rcases m with _ | m
          · rfl
          · exfalso; rw [Nat.pow_succ] at hm; omega
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨by simp [weight]; omega, by simp [maxCodewordLength], ?_⟩
          intro m hm
          rw [hm_zero m hm]
          simp [maxCodewordLength]
        · refine ⟨by simp [weight]; omega, by simp [maxCodewordLength], ?_⟩
          intro m hm
          rw [hm_zero m hm]
          simp [maxCodewordLength]
      rcases hF₁_eq with rfl | rfl
      · refine ⟨node (leaf (3 * r + 1)) (leaf (3 * r + 2)), hu_prop _ _ (Or.inl ⟨rfl, rfl⟩), ?_⟩
        simp only [R₁, Multiset.singleton_add, Multiset.cons_add]
      · refine ⟨node (leaf (3 * r + 2)) (leaf (3 * r + 1)), hu_prop _ _ (Or.inr ⟨rfl, rfl⟩), ?_⟩
        simp only [R₁, Multiset.singleton_add, Multiset.cons_add]
    obtain ⟨u, hu_p1, hu_eq⟩ := hF₁_form
    rw [← hu_eq] at hreach1
    -- Step 2: leaf (3*r + 3) and t_{r+1} merge
    have hstep2_exist : ∃ t_rp1 ∈ u ::ₘ merged, IsPhase1Tree (r + 1) t_rp1 ∧
        (∀ s ∈ (u ::ₘ merged).erase t_rp1, ∃ j ∈ Finset.Ico (r + 2) (2 * r + 2), IsPhase1Tree j s) ∧
        ((u ::ₘ merged).erase t_rp1).card = r ∧
        (∀ j ∈ Finset.Ico (r + 2) (2 * r + 2),
          (((u ::ₘ merged).erase t_rp1).filter (fun t => t.weight = 3 * j)).card = 1) := by
      by_cases hr0 : r = 0
      · subst hr0
        have hm0 : merged = 0 := Multiset.card_eq_zero.mp hcard
        subst hm0
        refine ⟨u, Multiset.mem_cons_self _ _, hu_p1, ?_, ?_, ?_⟩
        · intro s hs; rw [Multiset.erase_cons_head] at hs; simp at hs
        · rw [Multiset.erase_cons_head]; simp
        · intro j hj; simp only [Finset.mem_Ico] at hj; omega
      · obtain ⟨t_rp1, ht_rp1_mem, ht_rp1_p1⟩ := hmem (r + 1) (by simp only [Finset.mem_Ico]; omega)
        have hu_ne : u ≠ t_rp1 := by
          intro hus
          have h1 := hu_p1.1
          have h2 := ht_rp1_p1.1
          rw [hus] at h1
          omega
        have her_eq : (u ::ₘ merged).erase t_rp1 = u ::ₘ merged.erase t_rp1 :=
          Multiset.erase_cons_tail _ hu_ne
        refine ⟨t_rp1, Multiset.mem_cons_of_mem ht_rp1_mem, ht_rp1_p1, ?_, ?_, ?_⟩
        · intro s hs
          rw [her_eq] at hs
          rcases Multiset.mem_cons.mp hs with rfl | hsM'
          · exact ⟨2 * r + 1, by simp only [Finset.mem_Ico]; omega, hu_p1⟩
          · obtain ⟨j, hj, hjt⟩ := hall s (Multiset.mem_of_mem_erase hsM')
            simp only [Finset.mem_Ico] at hj
            have hj_ne : j ≠ r + 1 := by
              intro hjeq; subst hjeq
              have hflt := huniq (r + 1) (by simp only [Finset.mem_Ico]; omega)
              have hcard_er : (merged.filter (fun t => t.weight = 3 * (r + 1))).erase t_rp1 =
                  (merged.erase t_rp1).filter (fun t => t.weight = 3 * (r + 1)) := by
                ext y
                by_cases hy : y = t_rp1
                · subst hy; simp [Multiset.count_filter, ht_rp1_p1.1]
                · simp [Multiset.count_filter, Multiset.count_erase_of_ne hy]
              have hcz : ((merged.filter (fun t => t.weight = 3 * (r + 1))).erase t_rp1).card = 0 := by
                rw [Multiset.card_erase_of_mem (Multiset.mem_filter.mpr ⟨ht_rp1_mem, ht_rp1_p1.1⟩),
                    hflt, Nat.pred_eq_sub_one]
              rw [hcard_er, Multiset.card_eq_zero] at hcz
              have : s ∈ (0 : Multiset CodeTree) := by rw [← hcz]; exact Multiset.mem_filter.mpr ⟨hsM', hjt.1⟩
              simp at this
            exact ⟨j, by simp only [Finset.mem_Ico]; omega, hjt⟩
        · rw [her_eq, Multiset.card_cons, Multiset.card_erase_of_mem ht_rp1_mem, hcard,
              Nat.pred_eq_sub_one]
          omega
        · intro j hj
          simp only [Finset.mem_Ico] at hj
          rw [her_eq, Multiset.filter_cons]
          split_ifs with h1
          · have hzero : ((merged.erase t_rp1).filter (fun t => t.weight = 3 * j)).card = 0 := by
              rw [Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_notMem]
              intro t ht
              have := Multiset.mem_filter.mp ht
              obtain ⟨j', hj', htp⟩ := hall t (Multiset.mem_of_mem_erase this.1)
              simp only [Finset.mem_Ico] at hj'
              rw [htp.1] at this
              rw [hu_p1.1] at h1
              omega
            simp [Multiset.card_add, hzero]
          · have hj_lt : j < 2 * r + 1 := by rw [hu_p1.1] at h1; omega
            have hflt := huniq j (by simp only [Finset.mem_Ico]; omega)
            have her_f : (merged.erase t_rp1).filter (fun t => t.weight = 3 * j) =
                merged.filter (fun t => t.weight = 3 * j) := by
              ext y
              by_cases hy : y = t_rp1
              · subst hy; simp [Multiset.count_filter, ht_rp1_p1.1, show 3 * (r + 1) ≠ 3 * j by omega]
              · simp [Multiset.count_filter, Multiset.count_erase_of_ne hy]
            simp [her_f, hflt]
    obtain ⟨t_rp1, ht_rp1_mem, ht_rp1_p1, hrest_all, hrest_card, hrest_uniq⟩ := hstep2_exist
    set rest := (u ::ₘ merged).erase t_rp1
    set leaves₂ := (Finset.Icc (3 * (r + 1) + 1) n).val.map leaf
    have hleaves₁_split : leaves₁ = leaf (3 * r + 3) ::ₘ leaves₂ := by
      have hsub : Finset.Icc (3 * r + 3) n =
          insert (3 * r + 3) (Finset.Icc (3 * (r + 1) + 1) n) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hnot : 3 * r + 3 ∉ Finset.Icc (3 * (r + 1) + 1) n := by
        simp only [Finset.mem_Icc]
        omega
      rw [show leaves₁ = (Finset.Icc (3 * r + 3) n).val.map leaf from rfl, hsub,
          Finset.insert_val_of_notMem hnot, Multiset.map_cons]
    set R₂ := rest + leaves₂
    have hF₁_split : u ::ₘ merged + leaves₁ = t_rp1 ::ₘ leaf (3 * r + 3) ::ₘ R₂ := by
      have hm_eq : u ::ₘ merged = t_rp1 ::ₘ rest := (Multiset.cons_erase ht_rp1_mem).symm
      rw [hleaves₁_split, hm_eq, Multiset.cons_add, Multiset.add_cons, Multiset.cons_swap]
    have hR₂_gt : ∀ s ∈ R₂, 3 * (r + 1) < s.weight := by
      intro s hs
      rcases Multiset.mem_add.mp hs with hsM | hsL
      · obtain ⟨j, hj, hjt⟩ := hrest_all s hsM
        simp only [Finset.mem_Ico] at hj
        rw [hjt.1]; omega
      · simp only [leaves₂, Multiset.mem_map, Finset.mem_val, Finset.mem_Icc] at hsL
        obtain ⟨i, hi, rfl⟩ := hsL
        simp only [weight]; omega
    have hR₂_gt1 : ∀ s ∈ R₂, t_rp1.weight < s.weight := by
      intro s hs
      rw [ht_rp1_p1.1]
      exact hR₂_gt s hs
    have hR₂_gt2 : ∀ s ∈ R₂, (leaf (3 * r + 3)).weight < s.weight := by
      intro s hs
      simp only [weight]
      have := hR₂_gt s hs
      omega
    have hstep2_cases : ∃ F₂, HuffmanStep (t_rp1 ::ₘ leaf (3 * r + 3) ::ₘ R₂) F₂ ∧
        Relation.ReflTransGen HuffmanStep F₂ {T} := by
      rw [hF₁_split] at hreach1
      rcases Relation.ReflTransGen.cases_head hreach1 with heq | h
      · exfalso
        have hc := congrArg Multiset.card heq
        simp only [Multiset.card_cons, Multiset.card_singleton] at hc
        omega
      · exact h
    obtain ⟨F₂, hstep2, hreach2⟩ := hstep2_cases
    have hF₂_eq : F₂ = {node t_rp1 (leaf (3 * r + 3))} + R₂ ∨
        F₂ = {node (leaf (3 * r + 3)) t_rp1} + R₂ :=
      huffman_unique_pair hR₂_gt1 hR₂_gt2 hstep2
    have hv_prop : ∀ a b, (a = t_rp1 ∧ b = leaf (3 * r + 3)) ∨
        (a = leaf (3 * r + 3) ∧ b = t_rp1) →
        IsPhase1Tree (2 * (r + 1)) (node a b) := by
      intro a b hab
      have hlog : Nat.log 2 (2 * (r + 1)) = Nat.log 2 (r + 1) + 1 := by
        rw [Nat.mul_comm 2 (r + 1), Nat.log_mul_base (by norm_num) (by omega)]
      have hmax_le : max t_rp1.maxCodewordLength 0 + 1 ≤ Nat.log 2 (2 * (r + 1)) + 1 := by
        rw [Nat.max_zero, hlog]
        exact Nat.add_le_add_right ht_rp1_p1.2.1 1
      have hpow : ∀ m, 2 * (r + 1) = 2 ^ m →
          max t_rp1.maxCodewordLength 0 + 1 = m + 1 := by
        intro m hm
        have hm1 : 1 ≤ m := by
          rcases m with _ | m
          · simp at hm
          · omega
        have hr1_pow : r + 1 = 2 ^ (m - 1) := by
          rcases m with _ | m
          · simp at hm
          · simp only [Nat.succ_sub_one]
            rw [Nat.pow_succ] at hm
            omega
        rw [Nat.max_zero, ht_rp1_p1.2.2 (m - 1) hr1_pow, Nat.sub_add_cancel hm1]
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨?_, hmax_le, hpow⟩
        simp only [weight, ht_rp1_p1.1]
        omega
      · refine ⟨?_, ?_, ?_⟩
        · simp only [weight, ht_rp1_p1.1]
          omega
        · simpa [maxCodewordLength, Nat.max_comm] using hmax_le
        · intro m hm
          simpa [maxCodewordLength, Nat.max_comm] using hpow m hm
    have hF₂_form : ∃ v, IsPhase1Tree (2 * (r + 1)) v ∧
        (v ::ₘ rest) + leaves₂ = F₂ := by
      rcases hF₂_eq with rfl | rfl
      · refine ⟨node t_rp1 (leaf (3 * r + 3)), hv_prop _ _ (Or.inl ⟨rfl, rfl⟩), ?_⟩
        simp only [R₂, Multiset.singleton_add, Multiset.cons_add]
      · refine ⟨node (leaf (3 * r + 3)) t_rp1, hv_prop _ _ (Or.inr ⟨rfl, rfl⟩), ?_⟩
        simp only [R₂, Multiset.singleton_add, Multiset.cons_add]
    obtain ⟨v, hv_p1, hv_eq⟩ := hF₂_form
    rw [← hv_eq] at hreach2
    refine ⟨v ::ₘ rest, ?_, ?_, ?_, ?_, hreach2⟩
    · rw [Multiset.card_cons, hrest_card]
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      by_cases hj2 : j = 2 * r + 2
      · rw [hj2]
        exact ⟨v, Multiset.mem_cons_self v _, by simpa [Nat.mul_add] using hv_p1⟩
      · by_cases hj1 : j = 2 * r + 1
        · subst hj1
          have hne_u : u ≠ t_rp1 := by
            intro hus
            have h1 := hu_p1.1
            have h2 := ht_rp1_p1.1
            rw [hus] at h1
            omega
          exact ⟨u, Multiset.mem_cons_of_mem ((Multiset.mem_erase_of_ne hne_u).mpr
            (Multiset.mem_cons_self _ _)), hu_p1⟩
        · obtain ⟨t, ht, htp⟩ := hmem j (by simp only [Finset.mem_Ico]; omega)
          have ht_ne : t ≠ t_rp1 := by
            intro heq; subst heq
            have : 3 * j = 3 * (r + 1) := by rw [← htp.1, ht_rp1_p1.1]
            omega
          exact ⟨t, Multiset.mem_cons_of_mem ((Multiset.mem_erase_of_ne ht_ne).mpr
            (Multiset.mem_cons_of_mem ht)), htp⟩
    · intro t ht
      rcases Multiset.mem_cons.mp ht with rfl | ht'
      · exact ⟨2 * r + 2, by simp only [Finset.mem_Ico]; omega, by simpa [Nat.mul_add] using hv_p1⟩
      · obtain ⟨j, hj, htp⟩ := hrest_all t ht'
        simp only [Finset.mem_Ico] at hj
        exact ⟨j, by simp only [Finset.mem_Ico]; omega, htp⟩
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      have hv_w : v.weight = 3 * (2 * r + 2) := by rw [hv_p1.1]; omega
      rw [Multiset.filter_cons]
      split_ifs with h1
      · have hzero : (rest.filter (fun t => t.weight = 3 * j)).card = 0 := by
          rw [Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_notMem]
          intro t ht
          have := Multiset.mem_filter.mp ht
          obtain ⟨j', hj', htp⟩ := hrest_all t this.1
          simp only [Finset.mem_Ico] at hj'
          rw [htp.1] at this
          rw [hv_w] at h1
          omega
        simp [hzero]
      · have hj_lt : j < 2 * r + 2 := by rw [hv_w] at h1; omega
        simp [hrest_uniq j (by simp only [Finset.mem_Ico]; omega)]

private def Phase2Inv (D : ℕ) (F : Multiset CodeTree) : Prop :=
  1 ≤ F.card ∧
  (∃ t_max ∈ F, t_max.maxCodewordLength = D ∧
    ∀ s ∈ F.erase t_max, s.maxCodewordLength < D ∧ s.weight < t_max.weight) ∧
  (∀ s ∈ F, ∀ t ∈ F, s.weight < 2 * t.weight)

private def RoundInv (D M : ℕ) (t_max : CodeTree) (O N : Multiset CodeTree) : Prop :=
  0 < M ∧
  (∀ s ∈ O, M ≤ s.weight ∧ s.weight < 2 * M) ∧
  (∀ s ∈ N, 2 * M ≤ s.weight ∧ s.weight < 4 * M) ∧
  (∀ s ∈ O, s.maxCodewordLength ≤ D) ∧
  (∀ s ∈ N, s.maxCodewordLength ≤ D) ∧
  (∀ s ∈ N, ∀ x ∈ O, s.weight ≤ 2 * x.weight) ∧
  t_max ∈ O ∧ t_max.maxCodewordLength = D ∧
  (∀ s ∈ O.erase t_max, s.maxCodewordLength < D ∧ s.weight < t_max.weight)

private lemma huffman_pick_from_O {O N F' : Multiset CodeTree} {M : ℕ}
    (hO_w : ∀ s ∈ O, s.weight < 2 * M)
    (hN_w : ∀ s ∈ N, 2 * M ≤ s.weight)
    (hO_card : 2 ≤ O.card)
    (hstep : HuffmanStep (O + N) F') :
    ∃ a b R, O = a ::ₘ b ::ₘ R ∧ F' = {node a b} + (R + N) ∧
      (∀ t ∈ R, a.weight ≤ t.weight ∧ b.weight ≤ t.weight) ∧
      (∀ t ∈ N, a.weight ≤ t.weight ∧ b.weight ≤ t.weight) := by
  generalize heq : O + N = src at hstep
  cases hstep with
  | merge G a b ha hb =>
    have hdisj : ∀ x ∈ O, x ∉ N := fun x hxO hxN =>
      absurd (hO_w x hxO) (not_lt_of_ge (hN_w x hxN))
    have ha_O : a ∈ O := by
      by_contra haO
      have haN : a ∈ N := by
        have ha_mem : a ∈ O + N := by rw [heq]; exact Multiset.mem_cons_self a (b ::ₘ G)
        exact (Multiset.mem_add.mp ha_mem).resolve_left haO
      have hO_le : O ≤ b ::ₘ G := by
        rw [Multiset.le_iff_count]
        intro x
        have hc := congrArg (Multiset.count x) heq
        rw [Multiset.count_add, Multiset.count_cons, Multiset.count_cons] at hc
        by_cases hxa : x = a
        · subst hxa
          simp [Multiset.count_eq_zero.mpr haO]
        · simp only [if_neg hxa, add_zero] at hc
          rw [Multiset.count_cons]
          omega
      have hex : ∃ x ∈ O.erase b, True := by
        have hpos : 0 < (O.erase b).card := by
          by_cases hbO : b ∈ O
          · rw [Multiset.card_erase_of_mem hbO, Nat.pred_eq_sub_one]; omega
          · rw [Multiset.erase_of_notMem hbO]; omega
        obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
        exact ⟨x, hx, trivial⟩
      obtain ⟨x, hx, _⟩ := hex
      have hxG : x ∈ G := by
        have hle : O.erase b ≤ G := by
          rw [Multiset.le_iff_count]
          intro y
          have h1 := (Multiset.le_iff_count.mp hO_le) y
          by_cases hyb : y = b
          · subst hyb; simp [Multiset.count_erase_self, Multiset.count_cons] at h1 ⊢; omega
          · simp [Multiset.count_erase_of_ne hyb, Multiset.count_cons, hyb] at h1 ⊢; omega
        exact Multiset.mem_of_le hle hx
      have hxO : x ∈ O := Multiset.mem_of_mem_erase hx
      exact absurd (ha x hxG) (not_le_of_gt (lt_of_lt_of_le (hO_w x hxO) (hN_w a haN)))
    have hO1 : O = a ::ₘ O.erase a := (Multiset.cons_erase ha_O).symm
    have heq1 : b ::ₘ G = O.erase a + N := by
      have h1 : (a ::ₘ b ::ₘ G).erase a = (a ::ₘ (O.erase a + N)).erase a := by
        rw [← heq, ← Multiset.cons_add, ← hO1]
      simpa [Multiset.erase_cons_head] using h1
    have hb_O1 : b ∈ O.erase a := by
      by_contra hbO1
      have hbN : b ∈ N := by
        have hb_mem : b ∈ O.erase a + N := by rw [← heq1]; exact Multiset.mem_cons_self b G
        exact (Multiset.mem_add.mp hb_mem).resolve_left hbO1
      have hpos : 0 < (O.erase a).card := by
        rw [Multiset.card_erase_of_mem ha_O, Nat.pred_eq_sub_one]; omega
      obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hpos
      have hxO : x ∈ O := Multiset.mem_of_mem_erase hx
      have hxG : x ∈ G := by
        have hle : O.erase a ≤ G := by
          rw [Multiset.le_iff_count]
          intro y
          have hc := congrArg (Multiset.count y) heq1
          simp only [Multiset.count_add, Multiset.count_cons] at hc
          by_cases hyb : y = b
          · subst hyb; simp [Multiset.count_eq_zero.mpr hbO1]
          · simp only [if_neg hyb, add_zero] at hc; omega
        exact Multiset.mem_of_le hle hx
      exact absurd (hb x hxG) (not_le_of_gt (lt_of_lt_of_le (hO_w x hxO) (hN_w b hbN)))
    set R := (O.erase a).erase b
    have hO2 : O = a ::ₘ b ::ₘ R := by rw [hO1, Multiset.cons_erase hb_O1]
    have hG : G = R + N := by
      have h1 : (b ::ₘ G).erase b = (b ::ₘ (R + N)).erase b := by
        rw [heq1, ← Multiset.cons_erase hb_O1, Multiset.cons_add]
      simpa [Multiset.erase_cons_head] using h1
    refine ⟨a, b, R, hO2, by rw [hG], ?_, ?_⟩
    · intro t ht
      rw [hG] at ha hb
      exact ⟨ha t (Multiset.mem_add.mpr (Or.inl ht)), hb t (Multiset.mem_add.mpr (Or.inl ht))⟩
    · intro t ht
      rw [hG] at ha hb
      exact ⟨ha t (Multiset.mem_add.mpr (Or.inr ht)), hb t (Multiset.mem_add.mpr (Or.inr ht))⟩

private lemma huffman_pick_one_O {t_max : CodeTree} {N F' : Multiset CodeTree} {M : ℕ}
    (ht_w : t_max.weight < 2 * M)
    (hN_w : ∀ s ∈ N, 2 * M ≤ s.weight)
    (hN_pos : 1 ≤ N.card)
    (hstep : HuffmanStep ({t_max} + N) F') :
    ∃ b ∈ N, (F' = {node t_max b} + N.erase b ∨ F' = {node b t_max} + N.erase b) ∧
      (∀ s ∈ N.erase b, b.weight ≤ s.weight) := by
  generalize heq : ({t_max} + N : Multiset CodeTree) = src at hstep
  cases hstep with
  | merge G a b ha hb =>
    have hdisj : t_max ∉ N := fun htN => absurd ht_w (not_lt_of_ge (hN_w t_max htN))
    have ha_or_b : a = t_max ∨ b = t_max := by
      by_contra hno
      push_neg at hno
      have ht_mem : t_max ∈ a ::ₘ b ::ₘ G := by
        rw [← heq]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self t_max))
      have htG : t_max ∈ G := by
        rcases Multiset.mem_cons.mp ht_mem with h1 | ht'
        · exact absurd h1.symm hno.1
        · rcases Multiset.mem_cons.mp ht' with h2 | htG
          · exact absurd h2.symm hno.2
          · exact htG
      have ha_mem : a ∈ {t_max} + N := by rw [heq]; exact Multiset.mem_cons_self a (b ::ₘ G)
      have haN : a ∈ N := by
        rcases Multiset.mem_add.mp ha_mem with h1 | h2
        · exact absurd (Multiset.mem_singleton.mp h1) hno.1
        · exact h2
      exact absurd (ha t_max htG) (not_le_of_gt (lt_of_lt_of_le ht_w (hN_w a haN)))
    rcases ha_or_b with rfl | rfl
    · have hG_eq : b ::ₘ G = N := by
        have h1 : (a ::ₘ b ::ₘ G).erase a = ({a} + N).erase a := by rw [heq]
        simpa [Multiset.singleton_add, Multiset.erase_cons_head] using h1
      have hbN : b ∈ N := by rw [← hG_eq]; exact Multiset.mem_cons_self b G
      have hG : G = N.erase b := by rw [← hG_eq, Multiset.erase_cons_head]
      refine ⟨b, hbN, Or.inl (by rw [hG]), fun s hs => hb s (by rw [hG]; exact hs)⟩
    · have hG_eq : a ::ₘ G = N := by
        have h1 : (b ::ₘ a ::ₘ G).erase b = ({b} + N).erase b := by
          rw [Multiset.cons_swap, heq]
        simpa [Multiset.singleton_add, Multiset.erase_cons_head] using h1
      have haN : a ∈ N := by rw [← hG_eq]; exact Multiset.mem_cons_self a G
      have hG : G = N.erase a := by rw [← hG_eq, Multiset.erase_cons_head]
      refine ⟨a, haN, Or.inr (by rw [hG]), fun s hs => ha s (by rw [hG]; exact hs)⟩

private lemma round_step (D M : ℕ) (T : CodeTree) :
    ∀ (k : ℕ) (t_max : CodeTree) (O N : Multiset CodeTree),
      O.card = k →
      1 ≤ k →
      2 ≤ O.card + N.card →
      RoundInv D M t_max O N →
      Relation.ReflTransGen HuffmanStep (O + N) {T} →
      ∃ F' : Multiset CodeTree,
        F'.card = O.card / 2 + N.card ∧
        Phase2Inv (D + 1) F' ∧
        Relation.ReflTransGen HuffmanStep F' {T} := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t_max O N hk hk1 hcard hinv hreach
    rcases hinv with ⟨hM, hO_w, hN_w, hO_d, hN_d, hN_le, htO, ht_d, hO_lt⟩
    have hstep_cases : ∃ F₁, HuffmanStep (O + N) F₁ ∧
        Relation.ReflTransGen HuffmanStep F₁ {T} := by
      rcases Relation.ReflTransGen.cases_head hreach with heq | h
      · exfalso
        have hc := congrArg Multiset.card heq
        rw [Multiset.card_add, Multiset.card_singleton] at hc
        omega
      · exact h
    obtain ⟨F₁, hstep, hreach1⟩ := hstep_cases
    by_cases hk2 : k = 1
    · subst hk2
      have hO_eq : O = {t_max} := by
        obtain ⟨x, hx⟩ := Multiset.card_eq_one.mp hk
        rw [hx] at htO
        rw [hx, Multiset.mem_singleton.mp htO]
      subst hO_eq
      have hN_pos : 1 ≤ N.card := by simp only [Multiset.card_singleton] at hcard; omega
      obtain ⟨b, hbN, hF₁_or, hb_min⟩ :=
        huffman_pick_one_O (hO_w t_max (Multiset.mem_singleton_self t_max)).2
          (fun s hs => (hN_w s hs).1) hN_pos hstep
      have hnode_eq : ∀ u v, (u = t_max ∧ v = b) ∨ (u = b ∧ v = t_max) →
          (node u v).maxCodewordLength = D + 1 ∧
          (∀ s ∈ ({node u v} + N.erase b).erase (node u v),
            s.maxCodewordLength < D + 1 ∧ s.weight < (node u v).weight) ∧
          (∀ s ∈ {node u v} + N.erase b, ∀ t ∈ {node u v} + N.erase b, s.weight < 2 * t.weight) := by
        intro u v huv
        have hb_w := hN_w b hbN
        have ht_w := hO_w t_max (Multiset.mem_singleton_self t_max)
        have hlen : (node u v).maxCodewordLength = D + 1 := by
          rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · rw [hu, hv]; simp only [maxCodewordLength, ht_d]; have := hN_d b hbN; omega
          · rw [hu, hv]; simp only [maxCodewordLength, ht_d]; have := hN_d b hbN; omega
        have hw_uv : (node u v).weight = t_max.weight + b.weight := by
          rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · rw [hu, hv]; simp [weight]
          · rw [hu, hv]; simp [weight, add_comm]
        refine ⟨hlen, ?_, ?_⟩
        · intro s hs
          rw [Multiset.singleton_add, Multiset.erase_cons_head] at hs
          have hsN := Multiset.mem_of_mem_erase hs
          refine ⟨by have := hN_d s hsN; omega, ?_⟩
          have hs_le := hN_le s hsN t_max (Multiset.mem_singleton_self t_max)
          rw [hw_uv]
          omega
        · intro s hs t ht
          have hbound : ∀ x ∈ {node u v} + N.erase b,
              b.weight ≤ x.weight ∧ x.weight < 2 * b.weight := by
            intro x hx
            rcases Multiset.mem_add.mp hx with hx1 | hx2
            · rw [Multiset.mem_singleton.mp hx1, hw_uv]
              omega
            · have hxN := Multiset.mem_of_mem_erase hx2
              refine ⟨hb_min x hx2, ?_⟩
              have hx_w := hN_w x hxN
              omega
          have hs_b := hbound s hs
          have ht_b := hbound t ht
          omega
      rcases hF₁_or with rfl | rfl
      · obtain ⟨hlen, hlt, hw2⟩ := hnode_eq t_max b (Or.inl ⟨rfl, rfl⟩)
        refine ⟨{node t_max b} + N.erase b, ?_, ?_, hreach1⟩
        · rw [Multiset.card_singleton, Multiset.card_add, Multiset.card_singleton,
              Multiset.card_erase_of_mem hbN, Nat.pred_eq_sub_one]
          omega
        · refine ⟨?_, ⟨node t_max b, Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _)),
            hlen, hlt⟩, hw2⟩
          rw [Multiset.card_add, Multiset.card_singleton]; omega
      · obtain ⟨hlen, hlt, hw2⟩ := hnode_eq b t_max (Or.inr ⟨rfl, rfl⟩)
        refine ⟨{node b t_max} + N.erase b, ?_, ?_, hreach1⟩
        · rw [Multiset.card_singleton, Multiset.card_add, Multiset.card_singleton,
              Multiset.card_erase_of_mem hbN, Nat.pred_eq_sub_one]
          omega
        · refine ⟨?_, ⟨node b t_max, Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _)),
            hlen, hlt⟩, hw2⟩
          rw [Multiset.card_add, Multiset.card_singleton]; omega
    · have hk_ge2 : 2 ≤ O.card := by omega
      obtain ⟨a, b, R, hO_eq, hF₁_eq, hR_le, hN_le_ab⟩ :=
        huffman_pick_from_O (fun s hs => (hO_w s hs).2) (fun s hs => (hN_w s hs).1) hk_ge2 hstep
      rw [hF₁_eq] at hreach1
      by_cases hk2_eq : k = 2
      · have hR0 : R = 0 := by
          have hc := congrArg Multiset.card hO_eq
          simp only [Multiset.card_cons] at hc
          rw [hk, hk2_eq] at hc
          exact Multiset.card_eq_zero.mp (by omega)
        subst hR0
        have ht_ab : (a = t_max ∧ b ∈ O.erase t_max) ∨ (b = t_max ∧ a ∈ O.erase t_max) := by
          rw [hO_eq] at htO ⊢
          rcases Multiset.mem_cons.mp htO with rfl | hb_eq
          · left; exact ⟨rfl, by rw [Multiset.erase_cons_head]; simp⟩
          · right
            obtain rfl := Multiset.mem_singleton.mp hb_eq
            exact ⟨rfl, by rw [Multiset.cons_swap, Multiset.erase_cons_head]; simp⟩
        have ha_w := hO_w a (by rw [hO_eq]; exact Multiset.mem_cons_self _ _)
        have hb_w := hO_w b (by rw [hO_eq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
        have ha_d := hO_d a (by rw [hO_eq]; exact Multiset.mem_cons_self _ _)
        have hb_d := hO_d b (by rw [hO_eq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
        have hlen : (node a b).maxCodewordLength = D + 1 := by
          rcases ht_ab with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · simp only [maxCodewordLength, ht_d]; omega
          · simp only [maxCodewordLength, ht_d]; omega
        refine ⟨{node a b} + N, ?_, ?_, ?_⟩
        · rw [hk, hk2_eq, Multiset.card_add, Multiset.card_singleton]
        · refine ⟨by rw [Multiset.card_add, Multiset.card_singleton]; omega,
            ⟨node a b, Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _)), hlen, ?_⟩, ?_⟩
          · intro s hs
            rw [Multiset.singleton_add, Multiset.erase_cons_head] at hs
            refine ⟨by have := hN_d s hs; omega, ?_⟩
            simp only [weight]
            rcases ht_ab with ⟨rfl, hb_er⟩ | ⟨rfl, ha_er⟩
            · have hs_le := hN_le s hs b (by rw [hO_eq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _))
              have hlt := (hO_lt b hb_er).2
              omega
            · have hs_le := hN_le s hs a (by rw [hO_eq]; exact Multiset.mem_cons_self _ _)
              have hlt := (hO_lt a ha_er).2
              omega
          · intro s hs t ht
            have hbound : ∀ x ∈ {node a b} + N, 2 * M ≤ x.weight ∧ x.weight < 4 * M := by
              intro x hx
              rcases Multiset.mem_add.mp hx with hx1 | hxN
              · rw [Multiset.mem_singleton.mp hx1, weight]; omega
              · exact hN_w x hxN
            have := hbound s hs
            have := hbound t ht
            omega
        · simpa using hreach1
      · have hR_card : R.card = k - 2 := by
          have hc := congrArg Multiset.card hO_eq
          simp only [Multiset.card_cons] at hc
          omega
        have hR_pos : 1 ≤ R.card := by omega
        have htR : t_max ∈ R := by
          have hmem : t_max ∈ a ::ₘ b ::ₘ R := by rw [← hO_eq]; exact htO
          rcases Multiset.mem_cons.mp hmem with rfl | ht'
          · exfalso
            obtain ⟨x, hxR⟩ := Multiset.card_pos_iff_exists_mem.mp hR_pos
            have hx_er : x ∈ O.erase t_max := by
              rw [hO_eq, Multiset.erase_cons_head]
              exact Multiset.mem_cons_of_mem hxR
            exact absurd (hO_lt x hx_er).2 (not_lt_of_ge (hR_le x hxR).1)
          · rcases Multiset.mem_cons.mp ht' with rfl | htR
            · exfalso
              obtain ⟨x, hxR⟩ := Multiset.card_pos_iff_exists_mem.mp hR_pos
              have hx_er : x ∈ O.erase t_max := by
                rw [hO_eq, Multiset.cons_swap, Multiset.erase_cons_head]
                exact Multiset.mem_cons_of_mem hxR
              exact absurd (hO_lt x hx_er).2 (not_lt_of_ge (hR_le x hxR).2)
            · exact htR
        have haO : a ∈ O := by rw [hO_eq]; exact Multiset.mem_cons_self _ _
        have hbO : b ∈ O := by rw [hO_eq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
        have hinv' : RoundInv D M t_max R ({node a b} + N) := by
          refine ⟨hM, ?_, ?_, ?_, ?_, ?_, htR, ht_d, ?_⟩
          · intro s hsR; exact hO_w s (by rw [hO_eq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hsR))
          · intro s hsN'
            rcases Multiset.mem_add.mp hsN' with hs1 | hsN
            · rw [Multiset.mem_singleton.mp hs1, weight]
              have := hO_w a haO; have := hO_w b hbO; omega
            · exact hN_w s hsN
          · intro s hsR; exact hO_d s (by rw [hO_eq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hsR))
          · intro s hsN'
            rcases Multiset.mem_add.mp hsN' with hs1 | hsN
            · rw [Multiset.mem_singleton.mp hs1, maxCodewordLength]
              have ha_ne : a ≠ t_max := by
                intro heq; rw [heq] at hR_le
                obtain ⟨x, hxR⟩ := Multiset.card_pos_iff_exists_mem.mp hR_pos
                have hx_er : x ∈ O.erase t_max := by
                  rw [hO_eq, ← heq, Multiset.erase_cons_head]; exact Multiset.mem_cons_of_mem hxR
                exact absurd (hO_lt x hx_er).2 (not_lt_of_ge (hR_le x hxR).1)
              have hb_ne : b ≠ t_max := by
                intro heq; rw [heq] at hR_le
                obtain ⟨x, hxR⟩ := Multiset.card_pos_iff_exists_mem.mp hR_pos
                have hx_er : x ∈ O.erase t_max := by
                  rw [hO_eq, ← heq, Multiset.cons_swap, Multiset.erase_cons_head]; exact Multiset.mem_cons_of_mem hxR
                exact absurd (hO_lt x hx_er).2 (not_lt_of_ge (hR_le x hxR).2)
              have ha_d_lt := (hO_lt a ((Multiset.mem_erase_of_ne ha_ne).mpr haO)).1
              have hb_d_lt := (hO_lt b ((Multiset.mem_erase_of_ne hb_ne).mpr hbO)).1
              omega
            · exact hN_d s hsN
          · intro s hsN' x hxR
            rcases Multiset.mem_add.mp hsN' with hs1 | hsN
            · rw [Multiset.mem_singleton.mp hs1, weight]
              have := hR_le x hxR; omega
            · exact hN_le s hsN x (by rw [hO_eq]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hxR))
          · intro s hsR_er
            apply hO_lt s
            rw [hO_eq]
            have : s ∈ (a ::ₘ b ::ₘ R).erase t_max := by
              rw [Multiset.erase_cons_tail _ (by
                intro heq
                rw [heq] at hR_le
                obtain ⟨x, hxR⟩ := Multiset.card_pos_iff_exists_mem.mp hR_pos
                have hx_er : x ∈ O.erase t_max := by
                  rw [hO_eq, ← heq, Multiset.erase_cons_head]
                  exact Multiset.mem_cons_of_mem hxR
                exact absurd (hO_lt x hx_er).2 (not_lt_of_ge (hR_le x hxR).1))]
              rw [Multiset.erase_cons_tail _ (by
                intro heq
                rw [heq] at hR_le
                obtain ⟨x, hxR⟩ := Multiset.card_pos_iff_exists_mem.mp hR_pos
                have hx_er : x ∈ O.erase t_max := by
                  rw [hO_eq, ← heq, Multiset.cons_swap, Multiset.erase_cons_head]
                  exact Multiset.mem_cons_of_mem hxR
                exact absurd (hO_lt x hx_er).2 (not_lt_of_ge (hR_le x hxR).2))]
              exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hsR_er)
            exact this
        have hreach1' : Relation.ReflTransGen HuffmanStep (R + ({node a b} + N)) {T} := by
          simpa [add_comm, add_left_comm, add_assoc] using hreach1
        obtain ⟨F', hF'_card, hF'_inv, hF'_reach⟩ :=
          ih (k - 2) (by omega) t_max R ({node a b} + N) hR_card (by omega)
            (by rw [Multiset.card_add, Multiset.card_singleton]; omega) hinv' hreach1'
        refine ⟨F', ?_, hF'_inv, hF'_reach⟩
        rw [hF'_card, hR_card, hk, Multiset.card_add, Multiset.card_singleton]
        omega

private lemma phase2_eval (T : CodeTree) :
    ∀ (m D : ℕ) (F : Multiset CodeTree),
      F.card = m →
      Phase2Inv D F →
      Relation.ReflTransGen HuffmanStep F {T} →
      T.maxCodewordLength = D + Nat.log 2 m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro D F hm hinv hreach
    rcases hinv with ⟨hm1, ⟨t_max, htF, ht_d, hF_lt⟩, hF_w2⟩
    by_cases hm_eq : m = 1
    · subst hm_eq
      obtain ⟨x, rfl⟩ := Multiset.card_eq_one.mp hm
      rw [Multiset.mem_singleton.mp htF] at ht_d
      rw [← huffman_singleton_eq hreach, ht_d]
      simp
    · have hm2 : 2 ≤ m := by omega
      have hF0 : F ≠ 0 := by
        intro h; rw [h, Multiset.card_zero] at hm; omega
      obtain ⟨w_min, hwF, hw_min⟩ := multiset_exists_min_weight F hF0
      have hM_pos : 0 < w_min.weight := by
        have := hF_w2 w_min hwF w_min hwF
        omega
      have hRinv : RoundInv D w_min.weight t_max F 0 := by
        refine ⟨hM_pos, ?_, by simp, ?_, by simp, by simp, htF, ht_d, hF_lt⟩
        · intro s hs; exact ⟨hw_min s hs, hF_w2 s hs w_min hwF⟩
        · intro s hs
          by_cases hst : s = t_max
          · subst hst; omega
          · have hmem : s ∈ F.erase t_max := (Multiset.mem_erase_of_ne hst).mpr hs
            exact le_of_lt (hF_lt s hmem).1
      obtain ⟨F', hF'_card, hF'_inv, hF'_reach⟩ :=
        round_step D w_min.weight T m t_max F 0 hm (by omega) (by rw [Multiset.card_zero, add_zero]; omega)
          hRinv (by simpa using hreach)
      rw [Multiset.card_zero, add_zero, hm] at hF'_card
      have hres := ih (m / 2) (Nat.div_lt_self (by omega) (by norm_num)) (D + 1) F' hF'_card hF'_inv hF'_reach
      have hlog : Nat.log 2 m = Nat.log 2 (m / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by norm_num) hm2
      rw [hres, hlog]
      omega

private lemma floor_logb_nat (n : ℕ) (hn : 1 ≤ n) :
    ⌊Real.logb 2 (n : ℝ)⌋ = (Nat.log 2 n : ℤ) := by
  rw [Int.floor_eq_iff]
  constructor
  · exact_mod_cast (by
      have h : (2 : ℝ) ^ (Nat.log 2 n : ℕ) ≤ n := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have h2 : ((Nat.log 2 n : ℤ) : ℝ) ≤ Real.logb 2 (n : ℝ) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast (by omega : 0 < n))]
        simpa [Real.rpow_natCast] using h
      exact h2)
  · have h : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    have h2 : Real.logb 2 (n : ℝ) < ((Nat.log 2 n : ℤ) + 1 : ℝ) := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by exact_mod_cast (by omega : 0 < n))]
      have : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by exact_mod_cast h
      simpa [← Real.rpow_natCast] using this
    exact h2

private lemma floor_logb_two_thirds (n : ℕ) (hn : 2 ≤ n) :
    ⌊Real.logb 2 ((2 * (n : ℝ)) / 3)⌋ = (Nat.log 2 (2 * n / 3) : ℤ) := by
  rw [Int.floor_eq_iff]
  set q := 2 * n / 3
  have hq : 1 ≤ q := by omega
  have hlo : (q : ℝ) ≤ 2 * (n : ℝ) / 3 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast Nat.div_mul_le_self (2 * n) 3
  have hhi : 2 * (n : ℝ) / 3 < (q : ℝ) + 1 := by
    rw [div_lt_iff₀ (by norm_num)]
    have : 2 * n < (q + 1) * 3 := by omega
    exact_mod_cast this
  constructor
  · have h1 : (2 : ℝ) ^ Nat.log 2 q ≤ 2 * (n : ℝ) / 3 := by
      have hp : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
      have hp' : (2 : ℝ) ^ Nat.log 2 q ≤ (q : ℝ) := by exact_mod_cast hp
      exact le_trans hp' hlo
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
    simpa [Real.rpow_natCast] using h1
  · have hp : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
    have hp_le : q + 1 ≤ 2 ^ (Nat.log 2 q + 1) := hp
    have h2 : 2 * (n : ℝ) / 3 < (2 : ℝ) ^ (Nat.log 2 q + 1) :=
      lt_of_lt_of_le hhi (by exact_mod_cast hp_le)
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)]
    simpa [← Real.rpow_natCast] using h2

end OMA

theorem OMA.solution : type_of% @OMA.S_oeis_a126236.main := by
  open OMA.S_oeis_a126236 OMA.S_oeis_a126236.CodeTree in
  classical
  intro n hn
  refine ⟨?_, ?_⟩
  · apply OMA.exists_huffman_of_pos n (initialForest n)
    · simp [initialForest]
    · omega
  · intro T hT
    by_cases hn2 : n = 2
    · subst hn2
      have hinit : initialForest 2 = leaf 1 ::ₘ leaf 2 ::ₘ 0 := by
        have hcc : Finset.Icc 1 2 = insert 1 {2} := by decide
        rw [initialForest, hcc, Finset.insert_val_of_notMem (by decide), Multiset.map_cons]
        simp
      rw [IsHuffmanTree, hinit] at hT
      have hstep_cases : ∃ F₁, HuffmanStep (leaf 1 ::ₘ leaf 2 ::ₘ 0) F₁ ∧
          Relation.ReflTransGen HuffmanStep F₁ {T} := by
        rcases Relation.ReflTransGen.cases_head hT with heq | h
        · exfalso
          have hc := congrArg Multiset.card heq
          simp at hc
        · exact h
      obtain ⟨F₁, hstep, hreach1⟩ := hstep_cases
      have hF₁ : F₁ = {node (leaf 1) (leaf 2)} ∨ F₁ = {node (leaf 2) (leaf 1)} := by
        rcases OMA.huffman_unique_pair (by simp) (by simp) hstep with h1 | h1
        · left; simpa using h1
        · right; simpa using h1
      have hlen : T.maxCodewordLength = 1 := by
        rcases hF₁ with rfl | rfl
        · rw [← OMA.huffman_singleton_eq hreach1]; rfl
        · rw [← OMA.huffman_singleton_eq hreach1]; rfl
      rw [hlen, OMA.floor_logb_nat 2 (by omega), OMA.floor_logb_two_thirds 2 (by omega)]
      norm_num
    · have hn3 : 3 ≤ n := by omega
      set k := Nat.log 2 (2 * n / 3)
      have hk1 : 1 ≤ k := by
        have : 2 ≤ 2 * n / 3 := by omega
        exact Nat.le_log_of_pow_le (by norm_num) (by simpa using this)
      have h2k : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [← Nat.sub_add_cancel hk1, Nat.pow_succ]
        omega
      have hk_lo : 3 * 2 ^ (k - 1) ≤ n := by
        have hp : 2 ^ k ≤ 2 * n / 3 := Nat.pow_log_le_self 2 (by omega)
        have h1 : 3 * 2 ^ k ≤ 2 * n := by omega
        omega
      have hk_hi : n < 3 * 2 ^ k := by
        have hp : 2 * n / 3 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (2 * n / 3)
        have h1 : 2 * n < 3 * 2 ^ (k + 1) := by omega
        rw [Nat.pow_succ] at h1
        omega
      obtain ⟨merged, hm_card, hm_mem, hm_all, hm_uniq, hreach⟩ :=
        OMA.phase1_reach n k hk1 hk_lo T hT (2 ^ (k - 1)) le_rfl
      set leaves := (Finset.Icc (3 * 2 ^ (k - 1) + 1) n).val.map leaf
      set F := merged + leaves
      have hF_card : F.card = n - 2 ^ k := by
        have hl_card : leaves.card = n - 3 * 2 ^ (k - 1) := by
          simp [leaves]
        rw [Multiset.card_add, hm_card, hl_card]
        omega
      obtain ⟨t_max, ht_mem, ht_p1⟩ :=
        hm_mem (2 ^ k) (by
          simp only [Finset.mem_Ico]
          have hpos : 0 < 2 ^ (k - 1) := pow_pos (by norm_num) _
          omega)
      have hF_inv : OMA.Phase2Inv (k + 1) F := by
        refine ⟨by omega, ⟨t_max, Multiset.mem_add.mpr (Or.inl ht_mem), ht_p1.2.2 k rfl, ?_⟩, ?_⟩
        · intro s hs
          have hs' : s ∈ merged.erase t_max + leaves := by
            simpa [F, Multiset.erase_add_left_pos _ ht_mem] using hs
          rcases Multiset.mem_add.mp hs' with hsM | hsL
          · have hsM0 : s ∈ merged := Multiset.mem_of_mem_erase hsM
            obtain ⟨j, hj, hjp⟩ := hm_all s hsM0
            simp only [Finset.mem_Ico] at hj
            have hj_ne : j ≠ 2 ^ k := by
              intro hjeq
              subst hjeq
              have hflt := hm_uniq (2 ^ k) (by simp only [Finset.mem_Ico]; omega)
              have hcard_er : (merged.filter (fun t => t.weight = 3 * 2 ^ k)).erase t_max =
                  (merged.erase t_max).filter (fun t => t.weight = 3 * 2 ^ k) := by
                ext y
                by_cases hy : y = t_max
                · subst hy; simp [Multiset.count_filter, ht_p1.1]
                · simp [Multiset.count_filter, Multiset.count_erase_of_ne hy]
              have hzero : ((merged.filter (fun t => t.weight = 3 * 2 ^ k)).erase t_max).card = 0 := by
                rw [Multiset.card_erase_of_mem (Multiset.mem_filter.mpr ⟨ht_mem, ht_p1.1⟩),
                    hflt, Nat.pred_eq_sub_one]
              rw [hcard_er, Multiset.card_eq_zero] at hzero
              have : s ∈ (0 : Multiset CodeTree) := by
                rw [← hzero]
                exact Multiset.mem_filter.mpr ⟨hsM, hjp.1⟩
              simp at this
            have hj_lt : j < 2 ^ k := by omega
            have hlog_lt : Nat.log 2 j < k := (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr hj_lt
            refine ⟨by have := hjp.2.1; omega, ?_⟩
            rw [hjp.1, ht_p1.1]; omega
          · simp only [leaves, Multiset.mem_map, Finset.mem_val, Finset.mem_Icc] at hsL
            obtain ⟨i, hi, rfl⟩ := hsL
            refine ⟨by simp [maxCodewordLength], ?_⟩
            simp only [weight, ht_p1.1]; omega
        · intro s hs t ht
          have hbound : ∀ x ∈ F, 3 * 2 ^ (k - 1) + 1 ≤ x.weight ∧ x.weight ≤ 3 * 2 ^ k := by
            intro x hx
            rcases Multiset.mem_add.mp hx with hxM | hxL
            · obtain ⟨j, hj, hjp⟩ := hm_all x hxM
              simp only [Finset.mem_Ico] at hj
              rw [hjp.1]
              omega
            · simp only [leaves, Multiset.mem_map, Finset.mem_val, Finset.mem_Icc] at hxL
              obtain ⟨i, hi, rfl⟩ := hxL
              simp only [weight]
              omega
          have hs_b := hbound s hs
          have ht_b := hbound t ht
          omega
      have hlen := OMA.phase2_eval T (n - 2 ^ k) (k + 1) F hF_card hF_inv hreach
      have hlog_eq : Nat.log 2 (n - 2 ^ k) + 1 = Nat.log 2 n := by
        have nat_log2_eq : ∀ x m, 2 ^ m ≤ x → x < 2 ^ (m + 1) → Nat.log 2 x = m := fun x m h1 h2 =>
          le_antisymm (Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) h2))
            (Nat.le_log_of_pow_le (by norm_num) h1)
        by_cases hcmp : n < 2 ^ (k + 1)
        · have hlog_n : Nat.log 2 n = k := nat_log2_eq n k (by omega) hcmp
          have hlog_m : Nat.log 2 (n - 2 ^ k) = k - 1 := by
            apply nat_log2_eq
            · omega
            · rw [Nat.sub_add_cancel hk1]
              omega
          rw [hlog_n, hlog_m, Nat.sub_add_cancel hk1]
        · have hlog_n : Nat.log 2 n = k + 1 := by
            apply nat_log2_eq
            · omega
            · have : 3 * 2 ^ k < 2 ^ (k + 2) := by
                rw [Nat.pow_succ 2 (k + 1), Nat.pow_succ 2 k]
                omega
              omega
          have hlog_m : Nat.log 2 (n - 2 ^ k) = k := by
            apply nat_log2_eq
            · have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
              omega
            · have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
              omega
          rw [hlog_n, hlog_m]
      rw [hlen, OMA.floor_logb_nat n (by omega), OMA.floor_logb_two_thirds n (by omega)]
      norm_cast
      omega
