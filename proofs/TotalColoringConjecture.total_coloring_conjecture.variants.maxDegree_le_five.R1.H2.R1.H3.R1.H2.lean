import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R1

/-! Proof of Kostochka Section 5 Palette Theorem (`H2`): any pair of degree-≤ 2 simple graphs `S, F`
on a finite type `U` with vertex marking `t : U → Bool` satisfying `inside`, `three`, and `square`
admits a proper 3-vertex-coloring of `S` and a proper 3-edge-coloring of `F` avoiding vertex colors
at marked vertices. -/

namespace TotalColoringH2

open SimpleGraph
open scoped Classical

lemma extend_colored {U : Type*} [Fintype U] (S : SimpleGraph U)
    (sd : ∀ v, S.degree v ≤ 2) :
    ∀ (n : ℕ) (colored : Finset U), (Finset.univ \ colored).card ≤ n →
    ∀ (c₀ : U → Fin 3), (∀ x ∈ colored, ∀ y ∈ colored, S.Adj x y → c₀ x ≠ c₀ y) →
    ∃ c : U → Fin 3, (∀ x ∈ colored, c x = c₀ x) ∧ (∀ x y, S.Adj x y → c x ≠ c y)
  | 0, colored, hcard, c₀, hprop => by
    have hempty : Finset.univ \ colored = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have hall : ∀ x : U, x ∈ colored := fun x => by
      by_contra hx
      have : x ∈ Finset.univ \ colored := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
      rw [hempty] at this
      exact Finset.notMem_empty x this
    exact ⟨c₀, fun _ _ => rfl, fun x y hadj => hprop x (hall x) y (hall y) hadj⟩
  | n + 1, colored, hcard, c₀, hprop => by
    by_cases hempty : (Finset.univ \ colored) = ∅
    · have hall : ∀ x : U, x ∈ colored := fun x => by
        by_contra hx
        have : x ∈ Finset.univ \ colored := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
        rw [hempty] at this
        exact Finset.notMem_empty x this
      exact ⟨c₀, fun _ _ => rfl, fun x y hadj => hprop x (hall x) y (hall y) hadj⟩
    · obtain ⟨x, hxmem⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hx : x ∉ colored := (Finset.mem_sdiff.mp hxmem).2
      let used : Finset (Fin 3) := (S.neighborFinset x ∩ colored).image c₀
      have hcard_used : used.card < (Finset.univ : Finset (Fin 3)).card := by
        calc used.card
            ≤ (S.neighborFinset x ∩ colored).card := Finset.card_image_le
          _ ≤ (S.neighborFinset x).card := Finset.card_le_card Finset.inter_subset_left
          _ = S.degree x := S.card_neighborFinset_eq_degree x
          _ ≤ 2 := sd x
          _ < 3 := by decide
          _ = (Finset.univ : Finset (Fin 3)).card := by simp
      obtain ⟨α, _, hα⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_used
      let c₁ : U → Fin 3 := Function.update c₀ x α
      let colored₁ : Finset U := insert x colored
      have hcard₁ : (Finset.univ \ colored₁).card ≤ n := by
        have hss : Finset.univ \ colored₁ = (Finset.univ \ colored).erase x := by
          ext z; simp [colored₁]
        rw [hss, Finset.card_erase_of_mem hxmem]
        omega
      have hprop₁ : ∀ a ∈ colored₁, ∀ b ∈ colored₁, S.Adj a b → c₁ a ≠ c₁ b := by
        intro a ha b hb hadj
        rcases Finset.mem_insert.mp ha with rfl | ha' <;>
          rcases Finset.mem_insert.mp hb with rfl | hb'
        · exact absurd hadj (S.loopless.irrefl _)
        · have hb_used : c₀ b ∈ used := Finset.mem_image.mpr
            ⟨b, Finset.mem_inter.mpr ⟨(S.mem_neighborFinset _ _).mpr hadj, hb'⟩, rfl⟩
          have hne : b ≠ a := fun h => hx (h ▸ hb')
          simp only [c₁, Function.update_self, Function.update_of_ne hne]
          exact fun h => hα (h ▸ hb_used)
        · have ha_used : c₀ a ∈ used := Finset.mem_image.mpr
            ⟨a, Finset.mem_inter.mpr ⟨(S.mem_neighborFinset _ _).mpr hadj.symm, ha'⟩, rfl⟩
          have hne : a ≠ b := fun h => hx (h ▸ ha')
          simp only [c₁, Function.update_self, Function.update_of_ne hne]
          exact fun h => hα (h.symm ▸ ha_used)
        · have hne_a : a ≠ x := fun h => hx (h ▸ ha')
          have hne_b : b ≠ x := fun h => hx (h ▸ hb')
          simp only [c₁, Function.update_of_ne hne_a, Function.update_of_ne hne_b]
          exact hprop a ha' b hb' hadj
      obtain ⟨c, hc_ext, hc_prop⟩ := extend_colored S sd n colored₁ hcard₁ c₁ hprop₁
      refine ⟨c, fun y hy => ?_, hc_prop⟩
      rw [hc_ext y (Finset.mem_insert_of_mem hy)]
      exact Function.update_of_ne (fun h : y = x => hx (h ▸ hy)) α c₀

lemma extend_unmarked {U : Type*} [Fintype U] (S : SimpleGraph U)
    (sd : ∀ v, S.degree v ≤ 2) (t : U → Bool)
    (cT : {v : U // t v = true} → Fin 3)
    (hcT : ∀ x y, S.Adj x.val y.val → cT x ≠ cT y) :
    ∃ c : U → Fin 3, (∀ v (hv : t v = true), c v = cT ⟨v, hv⟩) ∧
      (∀ x y, S.Adj x y → c x ≠ c y) := by
  let colored : Finset U := Finset.univ.filter (fun v => t v = true)
  let c₀ : U → Fin 3 := fun v => if hv : t v = true then cT ⟨v, hv⟩ else 0
  have hprop : ∀ x ∈ colored, ∀ y ∈ colored, S.Adj x y → c₀ x ≠ c₀ y := by
    intro x hx y hy hadj
    have htx : t x = true := (Finset.mem_filter.mp hx).2
    have hty : t y = true := (Finset.mem_filter.mp hy).2
    simp only [c₀, dif_pos htx, dif_pos hty]
    exact hcT ⟨x, htx⟩ ⟨y, hty⟩ hadj
  obtain ⟨c, hc_ext, hc_prop⟩ :=
    extend_colored S sd (Finset.univ \ colored).card colored (le_refl _) c₀ hprop
  refine ⟨c, fun v hv => ?_, hc_prop⟩
  rw [hc_ext v (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩)]
  simp only [c₀, dif_pos hv]

section BrooksThree

private lemma walk_stay_in_set {V : Type*} {H : SimpleGraph V} (S : Set V)
    (hclosed : ∀ x ∈ S, ∀ y, H.Adj x y → y ∈ S) {u v : V} (p : H.Walk u v) (hu : u ∈ S) :
    v ∈ S := by
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hclosed _ hu _ hadj)

private lemma ind_degree_le {V : Type*} [Fintype V] (H : SimpleGraph V) (d : ℕ)
    (hdeg : ∀ v, H.degree v ≤ d) (S : Set V) [Fintype S] (x : S) :
    (H.induce S).degree x ≤ d := by
  calc (H.induce S).degree x
      = ((H.induce S).neighborFinset x).card :=
        ((H.induce S).card_neighborFinset_eq_degree x).symm
    _ ≤ (H.neighborFinset x.val).card := by
        refine Finset.card_le_card_of_injOn Subtype.val (fun y hy => ?_)
          (fun a _ b _ h => Subtype.ext h)
        have hadj : (H.induce S).Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
        exact (H.mem_neighborFinset _ _).mpr hadj
    _ = H.degree x.val := H.card_neighborFinset_eq_degree x.val
    _ ≤ d := hdeg x.val

private lemma ind_cliqueFree {V : Type*} {H : SimpleGraph V} (hnk4 : H.CliqueFree 4)
    (S : Set V) : (H.induce S).CliqueFree 4 := by
  intro t ht
  apply hnk4 (t.map ⟨Subtype.val, Subtype.val_injective⟩)
  refine ⟨fun x hx y hy hxy => ?_, ?_⟩
  · simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Function.Embedding.coeFn_mk] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact ht.1 hx' hy' (fun h => hxy (congrArg Subtype.val h))
  · rw [Finset.card_map]; exact ht.2

private def perm_pair (x₁ y₁ x₂ y₂ : Fin 3) (_h₁ : x₁ ≠ y₁) (_h₂ : x₂ ≠ y₂) :
    Fin 3 ≃ Fin 3 :=
  let σ₁ := Equiv.swap x₂ x₁
  let σ₂ := Equiv.swap (σ₁ y₂) y₁
  σ₁.trans σ₂

private lemma perm_pair_fst (x₁ y₁ x₂ y₂ : Fin 3) (h₁ : x₁ ≠ y₁) (h₂ : x₂ ≠ y₂) :
    perm_pair x₁ y₁ x₂ y₂ h₁ h₂ x₂ = x₁ := by
  simp only [perm_pair, Equiv.trans_apply, Equiv.swap_apply_left]
  have hne : x₁ ≠ Equiv.swap x₂ x₁ y₂ := by
    intro heq
    have := congrArg (Equiv.swap x₂ x₁) heq
    simp only [Equiv.swap_apply_right, Equiv.swap_apply_self] at this
    exact h₂ this
  exact Equiv.swap_apply_of_ne_of_ne hne h₁

private lemma perm_pair_snd (x₁ y₁ x₂ y₂ : Fin 3) (h₁ : x₁ ≠ y₁) (h₂ : x₂ ≠ y₂) :
    perm_pair x₁ y₁ x₂ y₂ h₁ h₂ y₂ = y₁ := by
  simp only [perm_pair, Equiv.trans_apply, Equiv.swap_apply_left]

private lemma walk_lift_subset {V : Type*} {H : SimpleGraph V} {S T : Set V}
    (hST : T ⊆ S) :
    ∀ {a' b' : S} (q : (H.induce S).Walk a' b'),
    (∀ z ∈ q.support, z.val ∈ T) →
    ∀ (ha : a'.val ∈ T) (hb : b'.val ∈ T),
    (H.induce T).Reachable ⟨a'.val, ha⟩ ⟨b'.val, hb⟩
  | _, _, .nil, _, ha, hb => by
    have : (⟨_, ha⟩ : T) = ⟨_, hb⟩ := Subtype.ext rfl
    rw [this]
  | a', _, .cons hadj q', hqT, ha, hb => by
    have hv_mem : _ ∈ T := hqT _ (List.mem_cons_of_mem _ q'.start_mem_support)
    have hadj' : (H.induce T).Adj ⟨a'.val, ha⟩ ⟨_, hv_mem⟩ := hadj
    exact hadj'.reachable.trans (walk_lift_subset hST q'
      (fun z hz => hqT z (List.mem_cons_of_mem _ hz)) hv_mem hb)

private lemma color_with_root {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hdeg : ∀ w, H.degree w ≤ 3) :
    ∀ (m : ℕ) (R : Finset V), R.card ≤ m →
    ∀ (root : V), root ∈ R → (H.induce (R : Set V)).Connected →
    ∀ (c₀ : V → Fin 3),
    (∀ x ∉ R, ∀ y ∉ R, H.Adj x y → c₀ x ≠ c₀ y) →
    ((∃ x y : V, x ≠ y ∧ x ∉ R ∧ y ∉ R ∧ H.Adj root x ∧ H.Adj root y ∧ c₀ x = c₀ y) ∨
      H.degree root ≤ 2) →
    ∃ c : V → Fin 3, (∀ x ∉ R, c x = c₀ x) ∧ (∀ x y, H.Adj x y → c x ≠ c y)
  | 0, R, hcard, root, hroot, _, _, _, _ => by
    have hpos : 0 < R.card := Finset.card_pos.mpr ⟨root, hroot⟩
    omega
  | m + 1, R, hcard, root, hroot, hconn, c₀, hc₀_prop, hinv => by
    by_cases hR1 : R.card = 1
    · have hR_eq : R = {root} := Finset.card_eq_one.mp hR1 |>.elim fun z hz => by
        rw [hz] at hroot
        rw [hz, Finset.mem_singleton.mp hroot]
      let used : Finset (Fin 3) := (H.neighborFinset root).image c₀
      have hcard_used : used.card ≤ 2 := by
        rcases hinv with ⟨x, y, hxy, _, _, hadjx, hadjy, hcxy⟩ | hdeg2
        · have hx_mem : x ∈ H.neighborFinset root := (H.mem_neighborFinset _ _).mpr hadjx
          have hy_mem : y ∈ H.neighborFinset root := (H.mem_neighborFinset _ _).mpr hadjy
          have himg : used = ((H.neighborFinset root).erase y).image c₀ := by
            ext α
            simp only [used, Finset.mem_image]
            constructor
            · rintro ⟨z, hz, rfl⟩
              by_cases hzy : z = y
              · exact ⟨x, Finset.mem_erase.mpr ⟨hxy, hx_mem⟩, by rw [hzy, hcxy]⟩
              · exact ⟨z, Finset.mem_erase.mpr ⟨hzy, hz⟩, rfl⟩
            · rintro ⟨z, hz, rfl⟩
              exact ⟨z, Finset.erase_subset _ _ hz, rfl⟩
          rw [himg]
          calc (((H.neighborFinset root).erase y).image c₀).card
              ≤ ((H.neighborFinset root).erase y).card := Finset.card_image_le
            _ = (H.neighborFinset root).card - 1 := Finset.card_erase_of_mem hy_mem
            _ = H.degree root - 1 := by rw [H.card_neighborFinset_eq_degree]
            _ ≤ 2 := by have := hdeg root; omega
        · calc used.card
              ≤ (H.neighborFinset root).card := Finset.card_image_le
            _ = H.degree root := H.card_neighborFinset_eq_degree root
            _ ≤ 2 := hdeg2
      have hlt : used.card < (Finset.univ : Finset (Fin 3)).card := by
        simp; omega
      obtain ⟨α, _, hα⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      let c := Function.update c₀ root α
      refine ⟨c, fun x hx => ?_, fun x y hadj => ?_⟩
      · have hne : x ≠ root := fun h => hx (hR_eq ▸ Finset.mem_singleton.mpr h)
        exact Function.update_of_ne hne α c₀
      · by_cases hxr : x = root
        · subst hxr
          have hyne : y ≠ x := hadj.ne.symm
          have hy_used : c₀ y ∈ used :=
            Finset.mem_image.mpr ⟨y, (H.mem_neighborFinset _ _).mpr hadj, rfl⟩
          simp only [c, Function.update_self, Function.update_of_ne hyne]
          exact fun h => hα (h ▸ hy_used)
        · by_cases hyr : y = root
          · subst hyr
            have hx_used : c₀ x ∈ used :=
              Finset.mem_image.mpr ⟨x, (H.mem_neighborFinset _ _).mpr hadj.symm, rfl⟩
            simp only [c, Function.update_self, Function.update_of_ne hxr]
            exact fun h => hα (h.symm ▸ hx_used)
          · have hx_not : x ∉ R := fun h => hxr (Finset.mem_singleton.mp (hR_eq ▸ h))
            have hy_not : y ∉ R := fun h => hyr (Finset.mem_singleton.mp (hR_eq ▸ h))
            simp only [c, Function.update_of_ne hxr, Function.update_of_ne hyr]
            exact hc₀_prop x hx_not y hy_not hadj
    · have hR2 : 1 < R.card := by
        have := Finset.card_pos.mpr ⟨root, hroot⟩; omega
      have hreach : ∀ (z : V) (hz : z ∈ R), ∃ n,
          ∃ p : (H.induce (R : Set V)).Walk ⟨root, hroot⟩ ⟨z, hz⟩, p.length = n :=
        fun z hz => by
          obtain ⟨p⟩ := hconn.preconnected ⟨root, hroot⟩ ⟨z, hz⟩
          exact ⟨p.length, p, rfl⟩
      let distR (z : V) : ℕ :=
        if hz : z ∈ R then Nat.find (hreach z hz) else 0
      have hdist_spec : ∀ (z : V) (hz : z ∈ R),
          ∃ p : (H.induce (R : Set V)).Walk ⟨root, hroot⟩ ⟨z, hz⟩, p.length = distR z := by
        intro z hz
        simp only [distR, dif_pos hz]
        exact Nat.find_spec (hreach z hz)
      have hdist_min : ∀ (z : V) (hz : z ∈ R)
          (p : (H.induce (R : Set V)).Walk ⟨root, hroot⟩ ⟨z, hz⟩), distR z ≤ p.length := by
        intro z hz p
        simp only [distR, dif_pos hz]
        exact Nat.find_min' (hreach z hz) ⟨p, rfl⟩
      obtain ⟨w, hw, hw_max⟩ := Finset.exists_max_image R distR ⟨root, hroot⟩
      have hw_ne_root : w ≠ root := by
        obtain ⟨z₀, hz₀, hz₀ne⟩ := Finset.exists_mem_ne hR2 root
        obtain ⟨pz, hpz⟩ := hdist_spec z₀ hz₀
        have hpz_pos : 0 < pz.length := by
          cases pz with
          | nil => exact absurd rfl hz₀ne
          | cons _ _ => simp
        have hdw_pos : 0 < distR w := by
          calc 0 < pz.length := hpz_pos
            _ = distR z₀ := hpz
            _ ≤ distR w := hw_max z₀ hz₀
        have h0 : distR root ≤ 0 := hdist_min root hroot Walk.nil
        intro hweq
        rw [hweq] at hdw_pos
        omega
      obtain ⟨pw, hpw⟩ := hdist_spec w hw
      have hpw_pos : 0 < pw.length := by
        cases pw with
        | nil => exact absurd rfl hw_ne_root.symm
        | cons _ _ => simp
      obtain ⟨u, hu_mem, hadj_wu⟩ : ∃ u ∈ R.erase w, H.Adj w u := by
        have hrev_len : 0 < pw.reverse.length := by simp [hpw_pos]
        cases hrev : pw.reverse with
        | nil => simp [hrev] at hrev_len
        | @cons _ v _ hadjv _ =>
          have hne_vw : v.val ≠ w := fun h => hadjv.ne (Subtype.ext h.symm)
          exact ⟨v.val, Finset.mem_erase.mpr ⟨hne_vw, v.2⟩, hadjv⟩
      have hroot' : root ∈ R.erase w := Finset.mem_erase.mpr ⟨hw_ne_root.symm, hroot⟩
      have hconn' : (H.induce (R.erase w : Set V)).Connected := by
        have : Nonempty (R.erase w : Set V) := ⟨⟨root, hroot'⟩⟩
        refine ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => ?_⟩
        have hfrom : ∀ (z : V) (hz : z ∈ R.erase w),
            (H.induce (R.erase w : Set V)).Reachable ⟨root, hroot'⟩ ⟨z, hz⟩ := by
          intro z hz
          have hzR : z ∈ R := Finset.mem_of_mem_erase hz
          have hzw : z ≠ w := (Finset.mem_erase.mp hz).1
          obtain ⟨qz, hqz⟩ := hdist_spec z hzR
          have hw_not : ∀ v ∈ qz.support, v.val ≠ w := by
            intro v hv hveq
            have hv_mem : ⟨w, hw⟩ ∈ qz.support := (Subtype.ext hveq : v = ⟨w, hw⟩) ▸ hv
            have hlt := qz.length_takeUntil_lt_length hv_mem (fun h => hzw (congrArg Subtype.val h).symm)
            have hmin := hdist_min w hw (qz.takeUntil ⟨w, hw⟩ hv_mem)
            have hle := hw_max z hzR
            omega
          exact walk_lift_subset (Finset.erase_subset w R) qz
            (fun v hv => Finset.mem_erase.mpr ⟨hw_not v hv, v.2⟩) hroot' hz
        exact (hfrom a ha).symm.trans (hfrom b hb)
      let used_w : Finset (Fin 3) := (H.neighborFinset w ∩ (Finset.univ \ R)).image c₀
      have hsub_u : H.neighborFinset w ∩ (Finset.univ \ R) ⊆ (H.neighborFinset w).erase u := by
        intro z hz
        obtain ⟨hzn, hzs⟩ := Finset.mem_inter.mp hz
        have hzu : z ≠ u := fun h => (Finset.mem_sdiff.mp hzs).2 (h ▸ Finset.mem_of_mem_erase hu_mem)
        exact Finset.mem_erase.mpr ⟨hzu, hzn⟩
      have hcard_used_w : used_w.card < (Finset.univ : Finset (Fin 3)).card := by
        have hu_n : u ∈ H.neighborFinset w := (H.mem_neighborFinset _ _).mpr hadj_wu
        calc used_w.card
            ≤ (H.neighborFinset w ∩ (Finset.univ \ R)).card := Finset.card_image_le
          _ ≤ ((H.neighborFinset w).erase u).card := Finset.card_le_card hsub_u
          _ = (H.neighborFinset w).card - 1 := Finset.card_erase_of_mem hu_n
          _ = H.degree w - 1 := by rw [H.card_neighborFinset_eq_degree]
          _ ≤ 2 := by have := hdeg w; omega
          _ < 3 := by decide
          _ = (Finset.univ : Finset (Fin 3)).card := by simp
      obtain ⟨α, _, hα⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_used_w
      let c₁ : V → Fin 3 := Function.update c₀ w α
      let R' : Finset V := R.erase w
      have hcard' : R'.card ≤ m := by
        rw [Finset.card_erase_of_mem hw]; omega
      have hc₁_prop : ∀ x ∉ R', ∀ y ∉ R', H.Adj x y → c₁ x ≠ c₁ y := by
        intro x hx y hy hadj
        have hx' : x = w ∨ x ∉ R := by
          by_cases hxw : x = w
          · exact Or.inl hxw
          · exact Or.inr fun h => hx (Finset.mem_erase.mpr ⟨hxw, h⟩)
        have hy' : y = w ∨ y ∉ R := by
          by_cases hyw : y = w
          · exact Or.inl hyw
          · exact Or.inr fun h => hy (Finset.mem_erase.mpr ⟨hyw, h⟩)
        rcases hx' with rfl | hxR <;> rcases hy' with rfl | hyR
        · exact absurd hadj (H.loopless.irrefl _)
        · have hy_used : c₀ y ∈ used_w := Finset.mem_image.mpr
            ⟨y, Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr hadj,
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyR⟩⟩, rfl⟩
          have hyne : y ≠ x := fun h => hyR (h ▸ hw)
          simp only [c₁, Function.update_self, Function.update_of_ne hyne]
          exact fun h => hα (h ▸ hy_used)
        · have hx_used : c₀ x ∈ used_w := Finset.mem_image.mpr
            ⟨x, Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr hadj.symm,
              Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxR⟩⟩, rfl⟩
          have hxne : x ≠ y := fun h => hxR (h ▸ hw)
          simp only [c₁, Function.update_self, Function.update_of_ne hxne]
          exact fun h => hα (h.symm ▸ hx_used)
        · have hxne : x ≠ w := fun h => hxR (h ▸ hw)
          have hyne : y ≠ w := fun h => hyR (h ▸ hw)
          simp only [c₁, Function.update_of_ne hxne, Function.update_of_ne hyne]
          exact hc₀_prop x hxR y hyR hadj
      have hinv' : (∃ x y : V, x ≠ y ∧ x ∉ R' ∧ y ∉ R' ∧ H.Adj root x ∧ H.Adj root y ∧ c₁ x = c₁ y) ∨
          H.degree root ≤ 2 := by
        rcases hinv with ⟨x, y, hxy, hxR, hyR, hadjx, hadjy, hcxy⟩ | hdeg2
        · left
          have hxne : x ≠ w := fun h => hxR (h ▸ hw)
          have hyne : y ≠ w := fun h => hyR (h ▸ hw)
          refine ⟨x, y, hxy, fun h => hxR (Finset.mem_of_mem_erase h),
            fun h => hyR (Finset.mem_of_mem_erase h), hadjx, hadjy, ?_⟩
          simp only [c₁, Function.update_of_ne hxne, Function.update_of_ne hyne, hcxy]
        · exact Or.inr hdeg2
      obtain ⟨c, hc_ext, hc_prop⟩ :=
        color_with_root H hdeg m R' hcard' root hroot' hconn' c₁ hc₁_prop hinv'
      refine ⟨c, fun x hx => ?_, hc_prop⟩
      have hxne : x ≠ w := fun h => hx (h ▸ hw)
      have hx' : x ∉ R' := fun h => hx (Finset.mem_of_mem_erase h)
      rw [hc_ext x hx']
      exact Function.update_of_ne hxne α c₀

private def IsTwoCut {V : Type*} [Fintype V] (H : SimpleGraph V) (a b : V) (C : Finset V) : Prop :=
  a ≠ b ∧ a ∉ C ∧ b ∉ C ∧ C.Nonempty ∧ (insert a (insert b C) ≠ Finset.univ) ∧
    (H.induce (C : Set V)).Connected ∧
    (∀ x ∈ C, ∀ y, y ∉ C → y ≠ a → y ≠ b → ¬ H.Adj x y)

private lemma two_cut_neighbors_C_and_D {V : Type*} [Fintype V] (H : SimpleGraph V)
    (h2conn : ∀ u : V, (H.induce {w | w ≠ u}).Connected)
    {a b : V} {C : Finset V} (hcut : IsTwoCut H a b C) :
    (H.neighborFinset a ∩ C).Nonempty ∧
    (H.neighborFinset a ∩ (Finset.univ \ insert a (insert b C))).Nonempty := by
  obtain ⟨_, _, hbC, hCne, hCuniv, _, hCiso⟩ := hcut
  let D : Finset V := Finset.univ \ insert a (insert b C)
  have hDne : D.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hCuniv
    ext z; simp only [Finset.mem_univ, iff_true]
    by_contra hz
    exact Finset.notMem_empty z (h ▸ Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩)
  constructor
  · by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨c₀, hc₀⟩ := hCne
    obtain ⟨d₀, hd₀⟩ := hDne
    have hc₀b : c₀ ≠ b := fun h' => hbC (h' ▸ hc₀)
    have hd₀_nmem := (Finset.mem_sdiff.mp hd₀).2
    have hd₀b : d₀ ≠ b := fun h' =>
      hd₀_nmem (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h')))
    obtain ⟨p⟩ := (h2conn b).preconnected ⟨c₀, hc₀b⟩ ⟨d₀, hd₀b⟩
    have hclosed : ∀ x : {w : V // w ≠ b}, x.val ∈ C →
        ∀ y : {w : V // w ≠ b}, (H.induce {w | w ≠ b}).Adj x y → y.val ∈ C := by
      intro x hx y hadj
      by_contra hyC
      by_cases hya : y.val = a
      · have : x.val ∈ H.neighborFinset a ∩ C := Finset.mem_inter.mpr
          ⟨(H.mem_neighborFinset _ _).mpr (hya ▸ hadj.symm), hx⟩
        rw [h] at this
        exact Finset.notMem_empty _ this
      · exact hCiso x.val hx y.val hyC hya y.2 hadj
    have hd₀C : d₀ ∈ C := walk_stay_in_set {x : {w : V // w ≠ b} | x.val ∈ C} hclosed p hc₀
    exact hd₀_nmem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hd₀C))
  · by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨c₀, hc₀⟩ := hCne
    obtain ⟨d₀, hd₀⟩ := hDne
    have hc₀b : c₀ ≠ b := fun h' => hbC (h' ▸ hc₀)
    have hd₀_nmem := (Finset.mem_sdiff.mp hd₀).2
    have hd₀b : d₀ ≠ b := fun h' =>
      hd₀_nmem (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h')))
    obtain ⟨p⟩ := (h2conn b).preconnected ⟨d₀, hd₀b⟩ ⟨c₀, hc₀b⟩
    have hclosed : ∀ x : {w : V // w ≠ b}, x.val ∈ D →
        ∀ y : {w : V // w ≠ b}, (H.induce {w | w ≠ b}).Adj x y → y.val ∈ D := by
      intro x hx y hadj
      have hxD := (Finset.mem_sdiff.mp hx).2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y.val, fun hy_ins => ?_⟩
      rcases Finset.mem_insert.mp hy_ins with hya | hy_ins2
      · have : x.val ∈ H.neighborFinset a ∩ D := Finset.mem_inter.mpr
          ⟨(H.mem_neighborFinset _ _).mpr (hya ▸ hadj.symm), hx⟩
        rw [h] at this
        exact Finset.notMem_empty _ this
      · rcases Finset.mem_insert.mp hy_ins2 with hyb | hyC
        · exact y.2 hyb
        · have hx_notC : x.val ∉ C :=
            fun h' => hxD (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h'))
          have hx_nea : x.val ≠ a := fun h' => hxD (Finset.mem_insert.mpr (Or.inl h'))
          exact hCiso y.val hyC x.val hx_notC hx_nea x.2 hadj.symm
    have hc₀D : c₀ ∈ D := walk_stay_in_set {x : {w : V // w ≠ b} | x.val ∈ D} hclosed p hd₀
    exact (Finset.mem_sdiff.mp hc₀D).2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc₀))

private lemma two_neighbors_in_min_cut {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hreg : ∀ v, H.degree v = 3)
    (h2conn : ∀ u : V, (H.induce {w | w ≠ u}).Connected)
    {a b : V} {C : Finset V} (hcut : IsTwoCut H a b C)
    (hmin : ∀ C' a' b', IsTwoCut H a' b' C' → C.card ≤ C'.card) :
    2 ≤ (H.neighborFinset a ∩ C).card := by
  obtain ⟨haC_ne, _⟩ := two_cut_neighbors_C_and_D H h2conn hcut
  obtain ⟨hab, haC, hbC, hCne, _, _, hCiso⟩ := hcut
  have hC2 : 2 ≤ C.card := by
    by_contra hlt
    have hC1 : C.card = 1 := by have := hCne.card_pos; omega
    obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp hC1
    have hc₀C : c₀ ∈ C := hc₀ ▸ Finset.mem_singleton_self c₀
    have hsub : H.neighborFinset c₀ ⊆ {a, b} := by
      intro y hy
      have hadj : H.Adj c₀ y := (H.mem_neighborFinset _ _).mp hy
      by_cases hyC : y ∈ C
      · rw [hc₀, Finset.mem_singleton] at hyC
        exact absurd (hyC ▸ hadj) (H.loopless.irrefl _)
      · by_cases hya : y = a
        · simp [hya]
        · by_cases hyb : y = b
          · simp [hyb]
          · exact absurd hadj (hCiso c₀ hc₀C y hyC hya hyb)
    have hdegc₀ : H.degree c₀ ≤ 2 := by
      calc H.degree c₀ = (H.neighborFinset c₀).card := (H.card_neighborFinset_eq_degree c₀).symm
        _ ≤ ({a, b} : Finset V).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have := hreg c₀
    omega
  by_contra hlt
  have haC_eq1 : (H.neighborFinset a ∩ C).card = 1 := by have := haC_ne.card_pos; omega
  obtain ⟨a', ha'eq⟩ := Finset.card_eq_one.mp haC_eq1
  have ha'_mem : a' ∈ H.neighborFinset a ∩ C := ha'eq ▸ Finset.mem_singleton_self a'
  have ha'C : a' ∈ C := (Finset.mem_inter.mp ha'_mem).2
  have hC_erase_ne : (C.erase a').Nonempty := by
    have : 1 ≤ (C.erase a').card := by rw [Finset.card_erase_of_mem ha'C]; omega
    exact Finset.card_pos.mp this
  obtain ⟨x₀, hx₀⟩ := hC_erase_ne
  let C' : Finset V := (C.erase a').filter (fun z =>
    ∃ hz : z ∈ C.erase a', (H.induce (C.erase a' : Set V)).Reachable ⟨x₀, hx₀⟩ ⟨z, hz⟩)
  have hC'sub : C' ⊆ C.erase a' := Finset.filter_subset _ _
  have hC'subC : C' ⊆ C := hC'sub.trans (Finset.erase_subset _ _)
  have ha'b : a' ≠ b := fun h => hbC (h ▸ ha'C)
  have ha'C' : a' ∉ C' := fun h => (Finset.mem_erase.mp (hC'sub h)).1 rfl
  have hbC' : b ∉ C' := fun h => hbC (hC'subC h)
  have hx₀C' : x₀ ∈ C' := Finset.mem_filter.mpr ⟨hx₀, hx₀, Reachable.refl _⟩
  have hC'ne : C'.Nonempty := ⟨x₀, hx₀C'⟩
  have hC'univ : insert a' (insert b C') ≠ Finset.univ := by
    intro h
    have ha_in : a ∈ insert a' (insert b C') := h ▸ Finset.mem_univ a
    rcases Finset.mem_insert.mp ha_in with rfl | ha_in2
    · exact haC ha'C
    · rcases Finset.mem_insert.mp ha_in2 with rfl | ha_in3
      · exact hab rfl
      · exact haC (hC'subC ha_in3)
  have hC'conn : (H.induce (C' : Set V)).Connected := by
    have : Nonempty (C' : Set V) := ⟨⟨x₀, hx₀C'⟩⟩
    refine ⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_⟩
    have hfrom : ∀ (z : V) (hz : z ∈ C'),
        (H.induce (C' : Set V)).Reachable ⟨x₀, hx₀C'⟩ ⟨z, hz⟩ := by
      intro z hz
      obtain ⟨hz_er, hz_reach⟩ := (Finset.mem_filter.mp hz).2
      obtain ⟨q⟩ := hz_reach
      refine walk_lift_subset hC'sub q ?_ hx₀C' hz
      intro y hy
      exact Finset.mem_filter.mpr ⟨y.2, y.2, ⟨q.takeUntil y hy⟩⟩
    exact (hfrom u hu).symm.trans (hfrom v hv)
  have hC'iso : ∀ x ∈ C', ∀ y, y ∉ C' → y ≠ a' → y ≠ b → ¬ H.Adj x y := by
    intro x hx y hyC' hya' hyb hadj
    have hx_er : x ∈ C.erase a' := hC'sub hx
    have hx_reach : (H.induce (C.erase a' : Set V)).Reachable ⟨x₀, hx₀⟩ ⟨x, hx_er⟩ :=
      (Finset.mem_filter.mp hx).2.2
    by_cases hyC : y ∈ C
    · have hy_er : y ∈ C.erase a' := Finset.mem_erase.mpr ⟨hya', hyC⟩
      have hadj' : (H.induce (C.erase a' : Set V)).Adj ⟨x, hx_er⟩ ⟨y, hy_er⟩ := hadj
      exact hyC' (Finset.mem_filter.mpr ⟨hy_er, hy_er, hx_reach.trans hadj'.reachable⟩)
    · have hya : y = a := by
        by_contra hya
        exact hCiso x (hC'subC hx) y hyC hya hyb hadj
      rw [hya] at hadj
      have hx_inter : x ∈ H.neighborFinset a ∩ C :=
        Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr hadj.symm, hC'subC hx⟩
      rw [ha'eq, Finset.mem_singleton] at hx_inter
      exact (Finset.mem_erase.mp hx_er).1 hx_inter
  have hmin' := hmin C' a' b ⟨ha'b, ha'C', hbC', hC'ne, hC'univ, hC'conn, hC'iso⟩
  have hlt' : C'.card < C.card := by
    calc C'.card ≤ (C.erase a').card := Finset.card_le_card hC'sub
      _ = C.card - 1 := Finset.card_erase_of_mem ha'C
      _ < C.card := Nat.sub_lt hCne.card_pos zero_lt_one
  omega

private def contractGraph {V : Type*} (H : SimpleGraph V) (a b : V) (D : Finset V) :
    SimpleGraph (Option (D : Set V)) where
  Adj x y := match x, y with
    | none, none => False
    | none, some z => H.Adj a z.val ∨ H.Adj b z.val
    | some z, none => H.Adj a z.val ∨ H.Adj b z.val
    | some z₁, some z₂ => H.Adj z₁.val z₂.val
  symm := ⟨fun x y h => by cases x <;> cases y <;> simp_all [H.adj_comm]⟩
  loopless := ⟨fun x h => by cases x <;> simp_all⟩

private lemma contractGraph_deg_none {V : Type*} [Fintype V] (H : SimpleGraph V)
    {a b : V} {D : Finset V}
    (haD1 : (H.neighborFinset a ∩ D).card = 1)
    (hbD1 : (H.neighborFinset b ∩ D).card = 1) :
    (contractGraph H a b D).degree none ≤ 2 := by
  let H₂ := contractGraph H a b D
  have hsub : H₂.neighborFinset none ⊆
      ((H.neighborFinset a ∩ D ∪ H.neighborFinset b ∩ D).attach.map
        ⟨fun z => some ⟨z.val, (Finset.mem_union.mp z.2).elim
          (fun h => (Finset.mem_inter.mp h).2)
          (fun h => (Finset.mem_inter.mp h).2)⟩,
          fun _ _ h => by dsimp at h; injection h with h1; injection h1 with h2; exact Subtype.ext h2⟩) := by
    intro y hy
    cases y with
    | none =>
      rw [H₂.mem_neighborFinset] at hy
      simp [H₂, contractGraph] at hy
    | some z =>
      have hadj : H.Adj a z.val ∨ H.Adj b z.val := (H₂.mem_neighborFinset _ _).mp hy
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
      rcases hadj with ha_z | hb_z
      · exact ⟨z.val, Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr ha_z, z.2⟩), rfl⟩
      · exact ⟨z.val, Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr hb_z, z.2⟩), rfl⟩
  calc H₂.degree none = (H₂.neighborFinset none).card :=
        (H₂.card_neighborFinset_eq_degree none).symm
    _ ≤ _ := Finset.card_le_card hsub
    _ = (H.neighborFinset a ∩ D ∪ H.neighborFinset b ∩ D).card := by
        rw [Finset.card_map, Finset.card_attach]
    _ ≤ (H.neighborFinset a ∩ D).card + (H.neighborFinset b ∩ D).card :=
        Finset.card_union_le _ _
    _ = 2 := by omega

private lemma contractGraph_deg {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hdeg : ∀ v, H.degree v ≤ 3) {a b : V} {C : Finset V}
    (_haC : a ∉ C) (_hbC : b ∉ C)
    (haD1 : (H.neighborFinset a ∩ (Finset.univ \ insert a (insert b C))).card = 1)
    (hbD1 : (H.neighborFinset b ∩ (Finset.univ \ insert a (insert b C))).card = 1) :
    ∀ x : Option ((Finset.univ \ insert a (insert b C) : Finset V) : Set V),
      (contractGraph H a b _).degree x ≤ 3 := by
  let D := Finset.univ \ insert a (insert b C)
  let H₂ := contractGraph H a b D
  intro x
  cases x with
  | none => exact (contractGraph_deg_none H haD1 hbD1).trans (by decide)
  | some z =>
    let f : Option (D : Set V) → V := fun y => match y with
      | none => if H.Adj a z.val then a else b
      | some w => w.val
    have hsub : (H₂.neighborFinset (some z)).image f ⊆ H.neighborFinset z.val := by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
      have hadj := (H₂.mem_neighborFinset _ _).mp hy
      cases y with
      | none =>
        dsimp [f]
        split_ifs with haz
        · exact (H.mem_neighborFinset _ _).mpr haz.symm
        · exact (H.mem_neighborFinset _ _).mpr (hadj.resolve_left haz).symm
      | some w' => exact (H.mem_neighborFinset _ _).mpr hadj
    have hinj : Set.InjOn f (H₂.neighborFinset (some z)) := by
      intro y₁ _ y₂ _ heq
      match y₁, y₂ with
      | none, none => rfl
      | none, some w₂ =>
        exfalso; dsimp [f] at heq
        split_ifs at heq
        · exact (Finset.mem_sdiff.mp (Finset.mem_coe.mp w₂.2)).2
            (heq ▸ Finset.mem_insert_self a _)
        · exact (Finset.mem_sdiff.mp (Finset.mem_coe.mp w₂.2)).2
            (heq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b C))
      | some w₁, none =>
        exfalso; dsimp [f] at heq
        split_ifs at heq
        · exact (Finset.mem_sdiff.mp (Finset.mem_coe.mp w₁.2)).2
            (heq.symm ▸ Finset.mem_insert_self a _)
        · exact (Finset.mem_sdiff.mp (Finset.mem_coe.mp w₁.2)).2
            (heq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b C))
      | some w₁, some w₂ => congr 1; exact Subtype.ext heq
    calc H₂.degree (some z) = (H₂.neighborFinset (some z)).card :=
          (H₂.card_neighborFinset_eq_degree (some z)).symm
      _ = ((H₂.neighborFinset (some z)).image f).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (H.neighborFinset z.val).card := Finset.card_le_card hsub
      _ = H.degree z.val := H.card_neighborFinset_eq_degree z.val
      _ ≤ 3 := hdeg z.val

private lemma contractGraph_cliqueFree {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hnk4 : H.CliqueFree 4) {a b : V} {D : Finset V}
    (haD1 : (H.neighborFinset a ∩ D).card = 1)
    (hbD1 : (H.neighborFinset b ∩ D).card = 1) :
    (contractGraph H a b D).CliqueFree 4 := by
  let H₂ := contractGraph H a b D
  intro t ht
  by_cases hnone : none ∈ t
  · have hsub : t.erase none ⊆ H₂.neighborFinset none := fun y hy =>
      (H₂.mem_neighborFinset _ _).mpr
        (ht.1 hnone (Finset.erase_subset _ _ hy) (Finset.mem_erase.mp hy).1.symm)
    have hdeg3 : 3 ≤ H₂.degree none := by
      calc 3 = t.card - 1 := by rw [ht.2]
        _ = (t.erase none).card := (Finset.card_erase_of_mem hnone).symm
        _ ≤ (H₂.neighborFinset none).card := Finset.card_le_card hsub
        _ = H₂.degree none := H₂.card_neighborFinset_eq_degree none
    have hdeg2 : (contractGraph H a b D).degree none ≤ 2 :=
      contractGraph_deg_none H haD1 hbD1
    have hdeg3' : 3 ≤ (contractGraph H a b D).degree none := hdeg3
    omega
  · let f : Option (D : Set V) → V := fun y => match y with | none => a | some z => z.val
    have hinj : Set.InjOn f t := fun y₁ hy₁ y₂ hy₂ heq => by
      cases y₁ with
      | none => exact absurd hy₁ hnone
      | some z₁ =>
        cases y₂ with
        | none => exact absurd hy₂ hnone
        | some z₂ => congr 1; exact Subtype.ext heq
    apply hnk4 (t.image f)
    refine ⟨fun x hx y hy hxy => ?_, ?_⟩
    · obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y₂, hy₂, rfl⟩ := Finset.mem_image.mp hy
      cases y₁ with
      | none => exact absurd hy₁ hnone
      | some z₁ =>
        cases y₂ with
        | none => exact absurd hy₂ hnone
        | some z₂ =>
          have hadj := ht.1 hy₁ hy₂ (fun h => hxy (congrArg f h))
          exact hadj
    · rw [Finset.card_image_of_injOn hinj, ht.2]

private def addEdgeGraph {V : Type*} (H : SimpleGraph V) (a b : V) (hab : a ≠ b)
    (S : Set V) : SimpleGraph S where
  Adj x y := H.Adj x.val y.val ∨ (x.val = a ∧ y.val = b) ∨ (x.val = b ∧ y.val = a)
  symm := ⟨fun _ _ h => by
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨fun x h => by
    rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact H.loopless.irrefl x.val h
    · exact hab h
    · exact hab h.symm⟩

private lemma addEdgeGraph_deg_endpoint {V : Type*} [Fintype V] (H : SimpleGraph V)
    {a b : V} (hab : a ≠ b) {D : Finset V}
    {u v : V} (_huv : u ≠ v) (hu_or : (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    (hu_in : u ∈ ((insert a (insert b D) : Finset V) : Set V))
    (hv_in : v ∈ ((insert a (insert b D) : Finset V) : Set V))
    (huD1 : (H.neighborFinset u ∩ D).card = 1) :
    (addEdgeGraph H a b hab ((insert a (insert b D) : Finset V) : Set V)).degree ⟨u, hu_in⟩ ≤ 2 := by
  let S : Finset V := insert a (insert b D)
  let H₂ := addEdgeGraph H a b hab (S : Set V)
  let emb : ↥(H.neighborFinset u ∩ D) ↪ ↥((insert a (insert b D) : Finset V) : Set V) :=
    ⟨fun z => ⟨z.val, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_inter.mp z.2).2)⟩,
      fun _ _ h => by dsimp at h; injection h with h2; exact Subtype.ext h2⟩
  have hsub : H₂.neighborFinset ⟨u, hu_in⟩ ⊆
      insert ⟨v, hv_in⟩ ((H.neighborFinset u ∩ D).attach.map emb) := by
    intro y hy
    have hadj := (H₂.mem_neighborFinset _ _).mp hy
    rcases hadj with h | ⟨hua, hyb⟩ | ⟨hub, hya⟩
    · rcases Finset.mem_insert.mp y.2 with hya | hy2
      · by_cases hyv : y.val = v
        · have : y = ⟨v, hv_in⟩ := Subtype.ext hyv
          rw [this]; exact Finset.mem_insert_self _ _
        · exfalso
          rcases hu_or with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact H.loopless.irrefl _ (hya ▸ h)
          · exact hyv hya
      · rcases Finset.mem_insert.mp hy2 with hyb | hyD
        · by_cases hyv : y.val = v
          · have : y = ⟨v, hv_in⟩ := Subtype.ext hyv
            rw [this]; exact Finset.mem_insert_self _ _
          · exfalso
            rcases hu_or with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hyv hyb
            · exact H.loopless.irrefl _ (hyb ▸ h)
        · refine Finset.mem_insert_of_mem ?_
          simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
          exact ⟨y.val, Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr h, hyD⟩, Subtype.ext rfl⟩
    · have hyv : y.val = v := by
        rcases hu_or with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hyb
        · exact absurd hua.symm hab
      have : y = ⟨v, hv_in⟩ := Subtype.ext hyv
      rw [this]; exact Finset.mem_insert_self _ _
    · have hyv : y.val = v := by
        rcases hu_or with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact absurd hub hab
        · exact hya
      have : y = ⟨v, hv_in⟩ := Subtype.ext hyv
      rw [this]; exact Finset.mem_insert_self _ _
  calc H₂.degree ⟨u, hu_in⟩ = (H₂.neighborFinset ⟨u, hu_in⟩).card :=
        (H₂.card_neighborFinset_eq_degree _).symm
    _ ≤ (insert ⟨v, hv_in⟩ ((H.neighborFinset u ∩ D).attach.map emb)).card :=
        Finset.card_le_card hsub
    _ ≤ ((H.neighborFinset u ∩ D).attach.map emb).card + 1 := Finset.card_insert_le _ _
    _ = (H.neighborFinset u ∩ D).card + 1 := by rw [Finset.card_map, Finset.card_attach]
    _ = 2 := by omega

lemma brooks_three :
    ∀ (n : ℕ) (V : Type*) [Fintype V],
    Fintype.card V ≤ n →
    ∀ (H : SimpleGraph V),
    (∀ v, H.degree v ≤ 3) →
    H.CliqueFree 4 →
    ∃ c : V → Fin 3, ∀ x y, H.Adj x y → c x ≠ c y
  | n, V, _, hcard, H, hdeg, hnk4 => by
    by_cases hle3 : Fintype.card V ≤ 3
    · let e := Fintype.equivFin V
      refine ⟨fun v => ⟨(e v).val, lt_of_lt_of_le (e v).isLt hle3⟩, fun x y hadj heq => ?_⟩
      exact hadj.ne (e.injective (Fin.ext (Fin.mk.inj heq)))
    have hge4 : 4 ≤ Fintype.card V := by omega
    have hnpos : 0 < n := by omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hnpos)
    have hneV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    -- Case 0: H is disconnected
    by_cases hconn : H.Connected
    swap
    · have hnotpre : ¬ H.Preconnected := fun h => hconn ⟨h⟩
      simp only [Preconnected, not_forall] at hnotpre
      obtain ⟨u, v, huv⟩ := hnotpre
      let C : Finset V := Finset.univ.filter (fun w => H.Reachable u w)
      have huC : u ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ u, Reachable.refl u⟩
      have hvC : v ∉ C := fun h => huv (Finset.mem_filter.mp h).2
      let V₁ := ↥(C : Set V)
      let V₂ := ↥((Finset.univ \ C : Finset V) : Set V)
      have hcard₁ : Fintype.card V₁ ≤ m := by
        have hlt : Fintype.card V₁ < Fintype.card V := by
          apply Fintype.card_lt_of_injective_of_notMem (f := Subtype.val) (b := v)
            Subtype.val_injective
          rintro ⟨⟨z, hz⟩, hzeq⟩
          exact hvC (hzeq ▸ hz)
        omega
      have hcard₂ : Fintype.card V₂ ≤ m := by
        have hlt : Fintype.card V₂ < Fintype.card V := by
          apply Fintype.card_lt_of_injective_of_notMem (f := Subtype.val) (b := u)
            Subtype.val_injective
          rintro ⟨⟨z, hz⟩, hzeq⟩
          dsimp at hzeq
          exact (Finset.mem_sdiff.mp hz).2 (hzeq.symm ▸ huC)
        omega
      obtain ⟨c₁, hc₁⟩ := brooks_three m V₁ hcard₁ (H.induce (C : Set V))
        (ind_degree_le H 3 hdeg (C : Set V)) (ind_cliqueFree hnk4 _)
      obtain ⟨c₂, hc₂⟩ := brooks_three m V₂ hcard₂ (H.induce ((Finset.univ \ C : Finset V) : Set V))
        (ind_degree_le H 3 hdeg ((Finset.univ \ C : Finset V) : Set V)) (ind_cliqueFree hnk4 _)
      refine ⟨fun w => if hw : w ∈ C then c₁ ⟨w, hw⟩ else
          c₂ ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩, fun x y hadj => ?_⟩
      by_cases hx : x ∈ C <;> by_cases hy : y ∈ C
      · simp only [dif_pos hx, dif_pos hy]
        exact hc₁ ⟨x, hx⟩ ⟨y, hy⟩ hadj
      · exfalso
        exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y,
          (Finset.mem_filter.mp hx).2.trans hadj.reachable⟩)
      · exfalso
        exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x,
          (Finset.mem_filter.mp hy).2.trans hadj.symm.reachable⟩)
      · simp only [dif_neg hx, dif_neg hy]
        exact hc₂ _ _ hadj
    -- Case 1: ∃ v, H.degree v ≤ 2
    by_cases hdeg2 : ∃ v : V, H.degree v ≤ 2
    · obtain ⟨v, hv⟩ := hdeg2
      have hconnR : (H.induce ((Finset.univ : Finset V) : Set V)).Connected := by
        have : Nonempty ((Finset.univ : Finset V) : Set V) := ⟨⟨v, Finset.mem_univ v⟩⟩
        refine ⟨fun ⟨a, _⟩ ⟨b, _⟩ => ?_⟩
        obtain ⟨p⟩ := hconn.preconnected a b
        have hwalk : ∀ {x y : V} (q : H.Walk x y),
            (H.induce ((Finset.univ : Finset V) : Set V)).Reachable
              ⟨x, Finset.mem_univ x⟩ ⟨y, Finset.mem_univ y⟩ := by
          intro x y q
          induction q with
          | nil => exact Reachable.refl _
          | @cons u' v' _ hadj' _ ih =>
            have hadjU : (H.induce ((Finset.univ : Finset V) : Set V)).Adj
                ⟨u', Finset.mem_univ u'⟩ ⟨v', Finset.mem_univ v'⟩ := hadj'
            exact hadjU.reachable.trans ih
        exact hwalk p
      obtain ⟨c, _, hc_prop⟩ := color_with_root H hdeg (Fintype.card V) Finset.univ
        (by simp) v (Finset.mem_univ v) hconnR (fun _ => 0) (fun x hx => absurd (Finset.mem_univ x) hx)
        (Or.inr hv)
      exact ⟨c, hc_prop⟩
    have hreg : ∀ v, H.degree v = 3 := fun v => by
      have h1 := hdeg v
      have h2 : ¬ H.degree v ≤ 2 := fun h => hdeg2 ⟨v, h⟩
      omega
    -- Case 2: cut-vertex exists
    by_cases h2conn : ∀ u : V, (H.induce {w : V | w ≠ u}).Connected
    swap
    · push Not at h2conn
      obtain ⟨u, hu_not⟩ := h2conn
      have hne_sub : Nonempty {w : V | w ≠ u} := by
        have hpos : 0 < (Finset.univ.erase u).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ]; omega
        obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
        exact ⟨⟨w, (Finset.mem_erase.mp hw).1⟩⟩
      have hnotpre : ¬ (H.induce {w : V | w ≠ u}).Preconnected := fun h => hu_not ⟨h⟩
      simp only [Preconnected, not_forall] at hnotpre
      obtain ⟨x₀, y₀, hxy₀⟩ := hnotpre
      let A : Finset V := Finset.univ.filter (fun w =>
        ∃ hw : w ≠ u, (H.induce {z : V | z ≠ u}).Reachable x₀ ⟨w, hw⟩)
      let B : Finset V := Finset.univ.filter (fun w => w ≠ u ∧ w ∉ A)
      have hx₀A : x₀.val ∈ A := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, x₀.2, Reachable.refl x₀⟩
      have hy₀B : y₀.val ∈ B := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, y₀.2, fun h => hxy₀ (Finset.mem_filter.mp h).2.2⟩
      let V₁ := ↥((insert u A : Finset V) : Set V)
      let V₂ := ↥((insert u B : Finset V) : Set V)
      have hcard₁ : Fintype.card V₁ ≤ m := by
        have hlt : Fintype.card V₁ < Fintype.card V := by
          apply Fintype.card_lt_of_injective_of_notMem (f := Subtype.val) (b := y₀.val)
            Subtype.val_injective
          rintro ⟨⟨z, hz⟩, hzeq⟩
          dsimp at hzeq
          rw [hzeq] at hz
          rcases Finset.mem_insert.mp hz with h1 | h2
          · exact (Finset.mem_filter.mp hy₀B).2.1 h1
          · exact (Finset.mem_filter.mp hy₀B).2.2 h2
        omega
      have hcard₂ : Fintype.card V₂ ≤ m := by
        have hlt : Fintype.card V₂ < Fintype.card V := by
          apply Fintype.card_lt_of_injective_of_notMem (f := Subtype.val) (b := x₀.val)
            Subtype.val_injective
          rintro ⟨⟨z, hz⟩, hzeq⟩
          dsimp at hzeq
          rw [hzeq] at hz
          rcases Finset.mem_insert.mp hz with h1 | h2
          · exact x₀.2 h1
          · exact (Finset.mem_filter.mp h2).2.2 hx₀A
        omega
      obtain ⟨c₁, hc₁⟩ := brooks_three m V₁ hcard₁ (H.induce ((insert u A : Finset V) : Set V))
        (ind_degree_le H 3 hdeg ((insert u A : Finset V) : Set V)) (ind_cliqueFree hnk4 _)
      obtain ⟨c₂, hc₂⟩ := brooks_three m V₂ hcard₂ (H.induce ((insert u B : Finset V) : Set V))
        (ind_degree_le H 3 hdeg ((insert u B : Finset V) : Set V)) (ind_cliqueFree hnk4 _)
      let σ := Equiv.swap (c₂ ⟨u, Finset.mem_insert_self u B⟩) (c₁ ⟨u, Finset.mem_insert_self u A⟩)
      refine ⟨fun w => if hw : w ∈ insert u A then c₁ ⟨w, hw⟩ else
          σ (c₂ ⟨w, by
            by_cases hwu : w = u
            · subst hwu; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
                ⟨Finset.mem_univ w, hwu, fun h => hw (Finset.mem_insert_of_mem h)⟩)⟩),
        fun x y hadj => ?_⟩
      by_cases hx : x ∈ insert u A <;> by_cases hy : y ∈ insert u A
      · simp only [dif_pos hx, dif_pos hy]
        exact hc₁ ⟨x, hx⟩ ⟨y, hy⟩ hadj
      · have hxu : x = u := by
          by_contra hxu
          have hxA : x ∈ A := (Finset.mem_insert.mp hx).resolve_left hxu
          have hyu : y ≠ u := fun h => hy (h ▸ Finset.mem_insert_self u A)
          have hreach : (H.induce {z : V | z ≠ u}).Reachable x₀ ⟨y, hyu⟩ :=
            (Finset.mem_filter.mp hxA).2.2.trans
              (SimpleGraph.Adj.reachable (hadj : (H.induce {z : V | z ≠ u}).Adj ⟨x, hxu⟩ ⟨y, hyu⟩))
          exact hy (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hyu, hreach⟩))
        simp only [dif_pos hx, dif_neg hy]
        have heq_u : c₁ ⟨x, hx⟩ = σ (c₂ ⟨u, Finset.mem_insert_self u B⟩) := by
          have : (⟨x, hx⟩ : V₁) = ⟨u, Finset.mem_insert_self u A⟩ := Subtype.ext hxu
          rw [this]; exact (Equiv.swap_apply_left _ _).symm
        rw [heq_u]
        have hy_B : y ∈ insert u B := by
          by_cases hyu : y = u
          · exact hyu ▸ Finset.mem_insert_self u B
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
              ⟨Finset.mem_univ y, hyu, fun h => hy (Finset.mem_insert_of_mem h)⟩)
        have hadj' : (H.induce ((insert u B : Finset V) : Set V)).Adj
            ⟨u, Finset.mem_insert_self u B⟩ ⟨y, hy_B⟩ := hxu ▸ hadj
        intro h
        exact hc₂ ⟨u, Finset.mem_insert_self u B⟩ ⟨y, hy_B⟩ hadj' (σ.injective h)
      · have hyu : y = u := by
          by_contra hyu
          have hyA : y ∈ A := (Finset.mem_insert.mp hy).resolve_left hyu
          have hxu : x ≠ u := fun h => hx (h ▸ Finset.mem_insert_self u A)
          have hreach : (H.induce {z : V | z ≠ u}).Reachable x₀ ⟨x, hxu⟩ :=
            (Finset.mem_filter.mp hyA).2.2.trans
              (SimpleGraph.Adj.reachable (hadj.symm : (H.induce {z : V | z ≠ u}).Adj ⟨y, hyu⟩ ⟨x, hxu⟩))
          exact hx (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxu, hreach⟩))
        simp only [dif_neg hx, dif_pos hy]
        have heq_u : c₁ ⟨y, hy⟩ = σ (c₂ ⟨u, Finset.mem_insert_self u B⟩) := by
          have : (⟨y, hy⟩ : V₁) = ⟨u, Finset.mem_insert_self u A⟩ := Subtype.ext hyu
          rw [this]; exact (Equiv.swap_apply_left _ _).symm
        rw [heq_u]
        have hx_B : x ∈ insert u B := by
          by_cases hxu : x = u
          · exact hxu ▸ Finset.mem_insert_self u B
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
              ⟨Finset.mem_univ x, hxu, fun h => hx (Finset.mem_insert_of_mem h)⟩)
        have hadj' : (H.induce ((insert u B : Finset V) : Set V)).Adj
            ⟨x, hx_B⟩ ⟨u, Finset.mem_insert_self u B⟩ := hyu ▸ hadj
        intro h
        exact hc₂ ⟨x, hx_B⟩ ⟨u, Finset.mem_insert_self u B⟩ hadj' (σ.injective h)
      · simp only [dif_neg hx, dif_neg hy]
        have hx_B : x ∈ insert u B := by
          by_cases hxu : x = u
          · exact hxu ▸ Finset.mem_insert_self u B
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
              ⟨Finset.mem_univ x, hxu, fun h => hx (Finset.mem_insert_of_mem h)⟩)
        have hy_B : y ∈ insert u B := by
          by_cases hyu : y = u
          · exact hyu ▸ Finset.mem_insert_self u B
          · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr
              ⟨Finset.mem_univ y, hyu, fun h => hy (Finset.mem_insert_of_mem h)⟩)
        intro h
        exact hc₂ ⟨x, hx_B⟩ ⟨y, hy_B⟩ hadj (σ.injective h)
    -- Case 3: 2-vertex cut exists
    by_cases h3conn : ∀ a b : V, a ≠ b → (H.induce {w : V | w ≠ a ∧ w ≠ b}).Connected
    swap
    · push Not at h3conn
      obtain ⟨a₀, b₀, hab₀, hnot⟩ := h3conn
      have hne_sub : Nonempty {w : V | w ≠ a₀ ∧ w ≠ b₀} := by
        have h1 : (Finset.univ.erase a₀).card = Fintype.card V - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ a₀), Finset.card_univ]
        have h2 : ((Finset.univ.erase a₀).erase b₀).card ≥ (Finset.univ.erase a₀).card - 1 :=
          Finset.pred_card_le_card_erase
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < ((Finset.univ.erase a₀).erase b₀).card)
        exact ⟨⟨w, (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1, (Finset.mem_erase.mp hw).1⟩⟩
      have hnotpre : ¬ (H.induce {w : V | w ≠ a₀ ∧ w ≠ b₀}).Preconnected := fun h => hnot ⟨h⟩
      simp only [Preconnected, not_forall] at hnotpre
      obtain ⟨x₀, y₀, hxy₀⟩ := hnotpre
      let C₀ : Finset V := Finset.univ.filter (fun w =>
        ∃ hw : w ≠ a₀ ∧ w ≠ b₀, (H.induce {z : V | z ≠ a₀ ∧ z ≠ b₀}).Reachable x₀ ⟨w, hw⟩)
      have hC₀cut : IsTwoCut H a₀ b₀ C₀ := by
        have hx₀C₀ : x₀.val ∈ C₀ :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, x₀.2, Reachable.refl x₀⟩
        refine ⟨hab₀, fun h => (Finset.mem_filter.mp h).2.1.1 rfl,
          fun h => (Finset.mem_filter.mp h).2.1.2 rfl, ⟨x₀.val, hx₀C₀⟩,
          fun h => ?_, ?_, fun x hx y hy hy_a hy_b hadj => ?_⟩
        · have hy₀_in : y₀.val ∈ insert a₀ (insert b₀ C₀) := h ▸ Finset.mem_univ y₀.val
          rcases Finset.mem_insert.mp hy₀_in with h1 | hy₀_in2
          · exact y₀.2.1 h1
          · rcases Finset.mem_insert.mp hy₀_in2 with h2 | h3
            · exact y₀.2.2 h2
            · exact hxy₀ (Finset.mem_filter.mp h3).2.2
        · have : Nonempty (C₀ : Set V) := ⟨⟨x₀.val, hx₀C₀⟩⟩
          refine ⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_⟩
          have hfrom : ∀ (z : V) (hz : z ∈ C₀),
              (H.induce (C₀ : Set V)).Reachable ⟨x₀.val, hx₀C₀⟩ ⟨z, hz⟩ := by
            intro z hz
            obtain ⟨_, hz_reach⟩ := (Finset.mem_filter.mp hz).2
            obtain ⟨q⟩ := hz_reach
            refine walk_lift_subset (fun w hw => (Finset.mem_filter.mp hw).2.1) q ?_ hx₀C₀ hz
            intro w hw
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.2, ⟨q.takeUntil w hw⟩⟩
          exact (hfrom u hu).symm.trans (hfrom v hv)
        · have hx_reach := (Finset.mem_filter.mp hx).2
          have hadj' : (H.induce {z : V | z ≠ a₀ ∧ z ≠ b₀}).Adj ⟨x, hx_reach.1⟩ ⟨y, hy_a, hy_b⟩ :=
            hadj
          exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, ⟨hy_a, hy_b⟩,
            hx_reach.2.trans hadj'.reachable⟩)
      let S_cuts : Finset (Finset V) :=
        Finset.univ.filter (fun C => ∃ a b : V, IsTwoCut H a b C)
      have hS_ne : S_cuts.Nonempty := ⟨C₀, Finset.mem_filter.mpr ⟨Finset.mem_univ C₀, a₀, b₀, hC₀cut⟩⟩
      obtain ⟨C, hC_mem, hC_min⟩ := Finset.exists_min_image S_cuts Finset.card hS_ne
      obtain ⟨a, b, hcut⟩ := (Finset.mem_filter.mp hC_mem).2
      have hmin_prop : ∀ C' a' b', IsTwoCut H a' b' C' → C.card ≤ C'.card := fun C' a' b' hc' =>
        hC_min C' (Finset.mem_filter.mpr ⟨Finset.mem_univ C', a', b', hc'⟩)
      have h2a : 2 ≤ (H.neighborFinset a ∩ C).card :=
        two_neighbors_in_min_cut H hreg h2conn hcut hmin_prop
      have hcut_symm : IsTwoCut H b a C := by
        obtain ⟨hab, haC, hbC, hCne, hCuniv, hCconn, hCiso⟩ := hcut
        refine ⟨hab.symm, hbC, haC, hCne, ?_, hCconn, fun x hx y hy hyb hya => hCiso x hx y hy hya hyb⟩
        rw [Finset.insert_comm]; exact hCuniv
      have h2b : 2 ≤ (H.neighborFinset b ∩ C).card :=
        two_neighbors_in_min_cut H hreg h2conn hcut_symm hmin_prop
      let D : Finset V := Finset.univ \ insert a (insert b C)
      obtain ⟨_, haD_ne⟩ := two_cut_neighbors_C_and_D H h2conn hcut
      obtain ⟨_, hbD_ne⟩ := two_cut_neighbors_C_and_D H h2conn hcut_symm
      change (H.neighborFinset a ∩ D).Nonempty at haD_ne
      have hD_eq : Finset.univ \ insert b (insert a C) = D := by
        simp only [D, Finset.insert_comm a b C]
      rw [hD_eq] at hbD_ne
      obtain ⟨hab, haC, hbC, hCne, hCuniv, hCconn, hCiso⟩ := hcut
      have hdisj_CD : Disjoint C D := Finset.disjoint_left.mpr fun z hzC hzD =>
        (Finset.mem_sdiff.mp hzD).2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hzC))
      have hna_le3 : (H.neighborFinset a).card = 3 := by rw [H.card_neighborFinset_eq_degree, hreg a]
      have hnb_le3 : (H.neighborFinset b).card = 3 := by rw [H.card_neighborFinset_eq_degree, hreg b]
      have hnot_adj_ab : ¬ H.Adj a b := by
        intro hadj
        have hb_mem : b ∈ H.neighborFinset a := (H.mem_neighborFinset _ _).mpr hadj
        have hb_notC : b ∉ H.neighborFinset a ∩ C := fun h => hbC (Finset.mem_inter.mp h).2
        have hb_notD : b ∉ H.neighborFinset a ∩ D := fun h =>
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).2).2
            (Finset.mem_insert_of_mem (Finset.mem_insert_self b C))
        have hsub : insert b (H.neighborFinset a ∩ C ∪ H.neighborFinset a ∩ D) ⊆
            H.neighborFinset a := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz2
          · exact hb_mem
          · rcases Finset.mem_union.mp hz2 with hzC | hzD
            · exact (Finset.mem_inter.mp hzC).1
            · exact (Finset.mem_inter.mp hzD).1
        have hdisj1 : Disjoint (H.neighborFinset a ∩ C) (H.neighborFinset a ∩ D) :=
          hdisj_CD.mono Finset.inter_subset_right Finset.inter_subset_right
        have hcard_ge4 : 4 ≤ (H.neighborFinset a).card := by
          calc 4 ≤ 1 + ((H.neighborFinset a ∩ C).card + (H.neighborFinset a ∩ D).card) := by
                have := haD_ne.card_pos; omega
            _ = (insert b (H.neighborFinset a ∩ C ∪ H.neighborFinset a ∩ D)).card := by
                rw [Finset.card_insert_of_notMem (Finset.notMem_union.mpr ⟨hb_notC, hb_notD⟩),
                  Finset.card_union_of_disjoint hdisj1]; omega
            _ ≤ (H.neighborFinset a).card := Finset.card_le_card hsub
        omega
      have haD_eq1 : (H.neighborFinset a ∩ D).card = 1 := by
        have hdisj1 : Disjoint (H.neighborFinset a ∩ C) (H.neighborFinset a ∩ D) :=
          hdisj_CD.mono Finset.inter_subset_right Finset.inter_subset_right
        have hle : (H.neighborFinset a ∩ C).card + (H.neighborFinset a ∩ D).card ≤ 3 := by
          rw [← Finset.card_union_of_disjoint hdisj1, ← hna_le3]
          exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
        have := haD_ne.card_pos
        omega
      have hbD_eq1 : (H.neighborFinset b ∩ D).card = 1 := by
        have hdisj1 : Disjoint (H.neighborFinset b ∩ C) (H.neighborFinset b ∩ D) :=
          hdisj_CD.mono Finset.inter_subset_right Finset.inter_subset_right
        have hle : (H.neighborFinset b ∩ C).card + (H.neighborFinset b ∩ D).card ≤ 3 := by
          rw [← Finset.card_union_of_disjoint hdisj1, ← hnb_le3]
          exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
        have := hbD_ne.card_pos
        omega
      have hDne : D.Nonempty := by
        obtain ⟨d, hd⟩ := haD_ne
        exact ⟨d, (Finset.mem_inter.mp hd).2⟩
      let V₁ := ↥((insert a (insert b C) : Finset V) : Set V)
      have hcard₁ : Fintype.card V₁ ≤ m := by
        obtain ⟨d₀, hd₀⟩ := hDne
        have hlt : Fintype.card V₁ < Fintype.card V := by
          apply Fintype.card_lt_of_injective_of_notMem (f := Subtype.val) (b := d₀)
            Subtype.val_injective
          rintro ⟨⟨z, hz⟩, hzeq⟩
          exact (Finset.mem_sdiff.mp hd₀).2 (hzeq ▸ hz)
        omega
      obtain ⟨c₁, hc₁⟩ := brooks_three m V₁ hcard₁
        (H.induce ((insert a (insert b C) : Finset V) : Set V))
        (ind_degree_le H 3 hdeg ((insert a (insert b C) : Finset V) : Set V)) (ind_cliqueFree hnk4 _)
      have ha_in1 : a ∈ insert a (insert b C) := Finset.mem_insert_self a _
      have hb_in1 : b ∈ insert a (insert b C) := Finset.mem_insert_of_mem (Finset.mem_insert_self b C)
      have hC2 : 2 ≤ C.card := by
        have hle : (H.neighborFinset a ∩ C).card ≤ C.card :=
          Finset.card_le_card Finset.inter_subset_right
        omega
      have hDcard : D.card = Fintype.card V - (insert a (insert b C)).card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      have hinscard : (insert a (insert b C)).card = C.card + 2 := by
        rw [Finset.card_insert_of_notMem (fun h => by
            rcases Finset.mem_insert.mp h with rfl | h'
            · exact hab rfl
            · exact haC h'),
          Finset.card_insert_of_notMem hbC]
      by_cases hc₁ab : c₁ ⟨a, ha_in1⟩ = c₁ ⟨b, hb_in1⟩
      · let V₂ := Option (D : Set V)
        have hcard₂ : Fintype.card V₂ ≤ m := by
          have hV₂ : Fintype.card V₂ = D.card + 1 := by
            simp [V₂]
          omega
        obtain ⟨c₂, hc₂⟩ := brooks_three m V₂ hcard₂ (contractGraph H a b D)
          (contractGraph_deg H hdeg haC hbC haD_eq1 hbD_eq1)
          (contractGraph_cliqueFree H hnk4 haD_eq1 hbD_eq1)
        let σ := Equiv.swap (c₂ none) (c₁ ⟨a, ha_in1⟩)
        refine ⟨fun w => if hw : w ∈ insert a (insert b C) then c₁ ⟨w, hw⟩ else
            σ (c₂ (some ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩)),
          fun x y hadj => ?_⟩
        by_cases hx : x ∈ insert a (insert b C) <;> by_cases hy : y ∈ insert a (insert b C)
        · simp only [dif_pos hx, dif_pos hy]
          exact hc₁ ⟨x, hx⟩ ⟨y, hy⟩ hadj
        · simp only [dif_pos hx, dif_neg hy]
          have hxy_ab : x = a ∨ x = b := by
            rcases Finset.mem_insert.mp hx with hxa | hx2
            · exact Or.inl hxa
            · rcases Finset.mem_insert.mp hx2 with hxb | hxC
              · exact Or.inr hxb
              · exfalso
                exact hCiso x hxC y (fun h => hy (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
                  (fun h => hy (h ▸ ha_in1)) (fun h => hy (h ▸ hb_in1)) hadj
          have hcx : c₁ ⟨x, hx⟩ = σ (c₂ none) := by
            rcases hxy_ab with hxa | hxb
            · have : (⟨x, hx⟩ : V₁) = ⟨a, ha_in1⟩ := Subtype.ext hxa
              rw [this]; exact (Equiv.swap_apply_left _ _).symm
            · have : (⟨x, hx⟩ : V₁) = ⟨b, hb_in1⟩ := Subtype.ext hxb
              rw [this, ← hc₁ab]; exact (Equiv.swap_apply_left _ _).symm
          rw [hcx]
          have hadj₂ : (contractGraph H a b D).Adj none
              (some ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩⟩) := by
            rcases hxy_ab with hxa | hxb
            · exact Or.inl (hxa ▸ hadj)
            · exact Or.inr (hxb ▸ hadj)
          intro h
          exact hc₂ none _ hadj₂ (σ.injective h)
        · simp only [dif_neg hx, dif_pos hy]
          have hyx_ab : y = a ∨ y = b := by
            rcases Finset.mem_insert.mp hy with hya | hy2
            · exact Or.inl hya
            · rcases Finset.mem_insert.mp hy2 with hyb | hyC
              · exact Or.inr hyb
              · exfalso
                exact hCiso y hyC x (fun h => hx (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
                  (fun h => hx (h ▸ ha_in1)) (fun h => hx (h ▸ hb_in1)) hadj.symm
          have hcy : c₁ ⟨y, hy⟩ = σ (c₂ none) := by
            rcases hyx_ab with hya | hyb
            · have : (⟨y, hy⟩ : V₁) = ⟨a, ha_in1⟩ := Subtype.ext hya
              rw [this]; exact (Equiv.swap_apply_left _ _).symm
            · have : (⟨y, hy⟩ : V₁) = ⟨b, hb_in1⟩ := Subtype.ext hyb
              rw [this, ← hc₁ab]; exact (Equiv.swap_apply_left _ _).symm
          rw [hcy]
          have hadj₂ : (contractGraph H a b D).Adj
              (some ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩) none := by
            rcases hyx_ab with hya | hyb
            · exact Or.inl (hya ▸ hadj.symm)
            · exact Or.inr (hyb ▸ hadj.symm)
          intro h
          exact hc₂ _ none hadj₂ (σ.injective h)
        · simp only [dif_neg hx, dif_neg hy]
          intro h
          exact hc₂ (some ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩)
            (some ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩⟩) hadj (σ.injective h)
      · let S₂ : Finset V := insert a (insert b D)
        let V₂ := ↥(S₂ : Set V)
        have ha_notD : a ∉ D := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_self a _)
        have hb_notD : b ∉ D := fun h =>
          (Finset.mem_sdiff.mp h).2 (Finset.mem_insert_of_mem (Finset.mem_insert_self b C))
        have hcard₂ : Fintype.card V₂ ≤ m := by
          have hV₂ : Fintype.card V₂ = D.card + 2 := by
            have h1 : a ∉ insert b D := fun h => by
              rcases Finset.mem_insert.mp h with h' | h'
              · exact hab h'
              · exact ha_notD h'
            calc Fintype.card V₂ = S₂.card := Fintype.card_coe S₂
              _ = (insert b D).card + 1 := Finset.card_insert_of_notMem h1
              _ = D.card + 2 := by rw [Finset.card_insert_of_notMem hb_notD]
          omega
        let H₂ := addEdgeGraph H a b hab (S₂ : Set V)
        have ha_in2 : a ∈ S₂ := Finset.mem_insert_self a _
        have hb_in2 : b ∈ S₂ := Finset.mem_insert_of_mem (Finset.mem_insert_self b D)
        have hdeg_a2 : H₂.degree ⟨a, ha_in2⟩ ≤ 2 :=
          addEdgeGraph_deg_endpoint H hab hab (Or.inl ⟨rfl, rfl⟩) ha_in2 hb_in2 haD_eq1
        have hdeg_b2 : H₂.degree ⟨b, hb_in2⟩ ≤ 2 :=
          addEdgeGraph_deg_endpoint H hab hab.symm (Or.inr ⟨rfl, rfl⟩) hb_in2 ha_in2 hbD_eq1
        have hdeg₂ : ∀ x : V₂, H₂.degree x ≤ 3 := by
          intro x
          by_cases hxa : x.val = a
          · have : x = ⟨a, ha_in2⟩ := Subtype.ext hxa; rw [this]; omega
          · by_cases hxb : x.val = b
            · have : x = ⟨b, hb_in2⟩ := Subtype.ext hxb; rw [this]; omega
            · calc H₂.degree x = (H₂.neighborFinset x).card :=
                    (H₂.card_neighborFinset_eq_degree x).symm
                _ ≤ (H.neighborFinset x.val).card := by
                    refine Finset.card_le_card_of_injOn Subtype.val (fun y hy => ?_)
                      (fun u _ v _ h => Subtype.ext h)
                    have hadj := (H₂.mem_neighborFinset _ _).mp hy
                    rcases hadj with h | ⟨h1, _⟩ | ⟨h1, _⟩
                    · exact (H.mem_neighborFinset _ _).mpr h
                    · exact absurd h1 hxa
                    · exact absurd h1 hxb
                _ = H.degree x.val := H.card_neighborFinset_eq_degree x.val
                _ ≤ 3 := hdeg x.val
        have hnk4₂ : H₂.CliqueFree 4 := by
          intro t ht
          by_cases hat : ⟨a, ha_in2⟩ ∈ t
          · have hsub : t.erase ⟨a, ha_in2⟩ ⊆ H₂.neighborFinset ⟨a, ha_in2⟩ := fun y hy =>
              (H₂.mem_neighborFinset _ _).mpr
                (ht.1 hat (Finset.erase_subset _ _ hy) (Finset.mem_erase.mp hy).1.symm)
            have h3 : 3 ≤ H₂.degree ⟨a, ha_in2⟩ := by
              calc 3 = t.card - 1 := by rw [ht.2]
                _ = (t.erase ⟨a, ha_in2⟩).card := (Finset.card_erase_of_mem hat).symm
                _ ≤ (H₂.neighborFinset ⟨a, ha_in2⟩).card := Finset.card_le_card hsub
                _ = H₂.degree ⟨a, ha_in2⟩ := H₂.card_neighborFinset_eq_degree _
            omega
          · by_cases hbt : ⟨b, hb_in2⟩ ∈ t
            · have hsub : t.erase ⟨b, hb_in2⟩ ⊆ H₂.neighborFinset ⟨b, hb_in2⟩ := fun y hy =>
                (H₂.mem_neighborFinset _ _).mpr
                  (ht.1 hbt (Finset.erase_subset _ _ hy) (Finset.mem_erase.mp hy).1.symm)
              have h3 : 3 ≤ H₂.degree ⟨b, hb_in2⟩ := by
                calc 3 = t.card - 1 := by rw [ht.2]
                  _ = (t.erase ⟨b, hb_in2⟩).card := (Finset.card_erase_of_mem hbt).symm
                  _ ≤ (H₂.neighborFinset ⟨b, hb_in2⟩).card := Finset.card_le_card hsub
                  _ = H₂.degree ⟨b, hb_in2⟩ := H₂.card_neighborFinset_eq_degree _
              omega
            · apply hnk4 (t.map ⟨Subtype.val, Subtype.val_injective⟩)
              refine ⟨fun x hx y hy hxy => ?_, by rw [Finset.card_map]; exact ht.2⟩
              simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe,
                Function.Embedding.coeFn_mk] at hx hy
              obtain ⟨x', hx', rfl⟩ := hx
              obtain ⟨y', hy', rfl⟩ := hy
              have hadj := ht.1 hx' hy' (fun h => hxy (congrArg Subtype.val h))
              rcases hadj with h | ⟨h1, _⟩ | ⟨h1, _⟩
              · exact h
              · exact absurd (Subtype.ext h1 : x' = ⟨a, ha_in2⟩) fun h => hat (h ▸ hx')
              · exact absurd (Subtype.ext h1 : x' = ⟨b, hb_in2⟩) fun h => hbt (h ▸ hx')
        obtain ⟨c₂, hc₂⟩ := brooks_three m V₂ hcard₂ H₂ hdeg₂ hnk4₂
        have hc₂ab : c₂ ⟨a, ha_in2⟩ ≠ c₂ ⟨b, hb_in2⟩ :=
          hc₂ ⟨a, ha_in2⟩ ⟨b, hb_in2⟩ (Or.inr (Or.inl ⟨rfl, rfl⟩))
        let σ := perm_pair (c₁ ⟨a, ha_in1⟩) (c₁ ⟨b, hb_in1⟩)
          (c₂ ⟨a, ha_in2⟩) (c₂ ⟨b, hb_in2⟩) hc₁ab hc₂ab
        refine ⟨fun w => if hw : w ∈ insert a (insert b C) then c₁ ⟨w, hw⟩ else
            σ (c₂ ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩))⟩),
          fun x y hadj => ?_⟩
        by_cases hx : x ∈ insert a (insert b C) <;> by_cases hy : y ∈ insert a (insert b C)
        · simp only [dif_pos hx, dif_pos hy]
          exact hc₁ ⟨x, hx⟩ ⟨y, hy⟩ hadj
        · simp only [dif_pos hx, dif_neg hy]
          have hxy_ab : x = a ∨ x = b := by
            rcases Finset.mem_insert.mp hx with rfl | hx2
            · exact Or.inl rfl
            · rcases Finset.mem_insert.mp hx2 with rfl | hxC
              · exact Or.inr rfl
              · exfalso
                exact hCiso x hxC y (fun h => hy (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
                  (fun h => hy (h ▸ ha_in1)) (fun h => hy (h ▸ hb_in1)) hadj
          have hcx : c₁ ⟨x, hx⟩ = σ (c₂ ⟨x, by
              rcases hxy_ab with rfl | rfl <;> [exact ha_in2; exact hb_in2]⟩) := by
            rcases hxy_ab with rfl | rfl
            · exact (perm_pair_fst _ _ _ _ hc₁ab hc₂ab).symm
            · exact (perm_pair_snd _ _ _ _ hc₁ab hc₂ab).symm
          rw [hcx]
          intro h
          exact hc₂ _ _ (Or.inl hadj) (σ.injective h)
        · simp only [dif_neg hx, dif_pos hy]
          have hyx_ab : y = a ∨ y = b := by
            rcases Finset.mem_insert.mp hy with rfl | hy2
            · exact Or.inl rfl
            · rcases Finset.mem_insert.mp hy2 with rfl | hyC
              · exact Or.inr rfl
              · exfalso
                exact hCiso y hyC x (fun h => hx (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h)))
                  (fun h => hx (h ▸ ha_in1)) (fun h => hx (h ▸ hb_in1)) hadj.symm
          have hcy : c₁ ⟨y, hy⟩ = σ (c₂ ⟨y, by
              rcases hyx_ab with rfl | rfl <;> [exact ha_in2; exact hb_in2]⟩) := by
            rcases hyx_ab with rfl | rfl
            · exact (perm_pair_fst _ _ _ _ hc₁ab hc₂ab).symm
            · exact (perm_pair_snd _ _ _ _ hc₁ab hc₂ab).symm
          rw [hcy]
          intro h
          exact hc₂ _ _ (Or.inl hadj) (σ.injective h)
        · simp only [dif_neg hx, dif_neg hy]
          intro h
          exact hc₂ _ _ (Or.inl hadj) (σ.injective h)
    -- Case 4: 3-connected, 3-regular, CliqueFree 4
    obtain ⟨v⟩ := hneV
    have hdeg_v : (H.neighborFinset v).card = 3 := by rw [H.card_neighborFinset_eq_degree, hreg v]
    have hnot_clique : ¬ H.IsClique ((insert v (H.neighborFinset v) : Finset V) : Set V) := by
      intro hcl
      have hv_not : v ∉ H.neighborFinset v :=
        fun h => H.loopless.irrefl v ((H.mem_neighborFinset _ _).mp h)
      apply hnk4 (insert v (H.neighborFinset v))
      refine ⟨hcl, ?_⟩
      rw [Finset.card_insert_of_notMem hv_not, hdeg_v]
    simp only [IsClique, Set.Pairwise, Finset.coe_insert, Set.mem_insert_iff,
      Finset.mem_coe, not_forall] at hnot_clique
    obtain ⟨x, hx, y, hy, hxy, hnot_adj⟩ := hnot_clique
    have hx_n : x ∈ H.neighborFinset v := by
      rcases hx with rfl | hx'
      · exfalso
        rcases hy with rfl | hy'
        · exact hxy rfl
        · exact hnot_adj ((H.mem_neighborFinset _ _).mp hy')
      · exact hx'
    have hy_n : y ∈ H.neighborFinset v := by
      rcases hy with rfl | hy'
      · exfalso
        exact hnot_adj ((H.mem_neighborFinset _ _).mp hx_n).symm
      · exact hy'
    let R : Finset V := (Finset.univ.erase x).erase y
    have hconnR : (H.induce (R : Set V)).Connected := by
      have hset : (R : Set V) = {w : V | w ≠ x ∧ w ≠ y} := by
        ext w; simp [R]
      rw [hset]
      exact h3conn x y hxy
    have hvx : v ≠ x := fun h => H.loopless.irrefl v (h ▸ (H.mem_neighborFinset v x).mp hx_n)
    have hvy : v ≠ y := fun h => H.loopless.irrefl v (h ▸ (H.mem_neighborFinset v y).mp hy_n)
    have hvR : v ∈ R := Finset.mem_erase.mpr ⟨hvy, Finset.mem_erase.mpr ⟨hvx, Finset.mem_univ v⟩⟩
    have hxR : x ∉ R := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
    have hyR : y ∉ R := fun h => (Finset.mem_erase.mp h).1 rfl
    have hinv : (∃ x' y' : V, x' ≠ y' ∧ x' ∉ R ∧ y' ∉ R ∧ H.Adj v x' ∧ H.Adj v y' ∧
        (fun _ : V => (0 : Fin 3)) x' = (fun _ : V => (0 : Fin 3)) y') ∨ H.degree v ≤ 2 :=
      Or.inl ⟨x, y, hxy, hxR, hyR, (H.mem_neighborFinset _ _).mp hx_n,
        (H.mem_neighborFinset _ _).mp hy_n, rfl⟩
    obtain ⟨c, _, hc_prop⟩ := color_with_root H hdeg (Fintype.card V) R (Finset.card_le_univ R)
      v hvR hconnR (fun _ => 0) (fun a ha b hb hadj => by
        have ha' : a = x ∨ a = y := by
          by_contra h; push Not at h
          exact ha (Finset.mem_erase.mpr ⟨h.2, Finset.mem_erase.mpr ⟨h.1, Finset.mem_univ a⟩⟩)
        have hb' : b = x ∨ b = y := by
          by_contra h; push Not at h
          exact hb (Finset.mem_erase.mpr ⟨h.2, Finset.mem_erase.mpr ⟨h.1, Finset.mem_univ b⟩⟩)
        rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
        · exact absurd hadj (H.loopless.irrefl _)
        · exact absurd hadj hnot_adj
        · exact absurd hadj.symm hnot_adj
        · exact absurd hadj (H.loopless.irrefl _)) hinv
    exact ⟨c, hc_prop⟩

end BrooksThree

def IsTT {U : Type*} (t : U → Bool) (e : Sym2 U) : Prop :=
  ∀ v ∈ e, t v = true

def LF {U : Type*} (F : SimpleGraph U) : SimpleGraph F.edgeSet where
  Adj e f := e ≠ f ∧ ∃ v : U, v ∈ e.val ∧ v ∈ f.val
  symm := ⟨fun _ _ h => ⟨h.1.symm, let ⟨v, hv1, hv2⟩ := h.2; ⟨v, hv2, hv1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma LF_degree_le_two {U : Type*} [Fintype U] (F : SimpleGraph U)
    (fd : ∀ v, F.degree v ≤ 2) (e : F.edgeSet) : (LF F).degree e ≤ 2 := by
  have he_mem : e.val ∈ F.edgeSet := e.2
  induction hval : e.val using Sym2.ind with
  | _ u v =>
    have huv : F.Adj u v := by simpa [hval] using he_mem
    have huv_ne : u ≠ v := huv.ne
    let A := ((LF F).neighborFinset e).filter (fun f => u ∈ f.val)
    let B := ((LF F).neighborFinset e).filter (fun f => v ∈ f.val)
    have hAB : (LF F).neighborFinset e ⊆ A ∪ B := by
      intro f hf
      have hadj := ((LF F).mem_neighborFinset _ _).mp hf
      obtain ⟨w, hwe, hwf⟩ := hadj.2
      rw [hval, Sym2.mem_iff] at hwe
      rcases hwe with rfl | rfl
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf, hwf⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hf, hwf⟩)
    have hcard_one : ∀ (x y : U) (hxy : F.Adj x y) (S : Finset F.edgeSet),
        S = ((LF F).neighborFinset e).filter (fun f => x ∈ f.val) →
        e.val = s(x, y) → S.card ≤ 1 := by
      intro x y hxy S hS hxy_eq
      rw [hS, Finset.card_le_one]
      intro f₁ hf₁ f₂ hf₂
      obtain ⟨hf₁n, hx₁⟩ := Finset.mem_filter.mp hf₁
      obtain ⟨hf₂n, hx₂⟩ := Finset.mem_filter.mp hf₂
      have hf₁_ne : f₁ ≠ e := (((LF F).mem_neighborFinset _ _).mp hf₁n).1.symm
      have hf₂_ne : f₂ ≠ e := (((LF F).mem_neighborFinset _ _).mp hf₂n).1.symm
      obtain ⟨w₁, hw₁adj, hw₁eq⟩ : ∃ w₁, F.Adj x w₁ ∧ f₁.val = s(x, w₁) := by
        have hf₁mem := f₁.2
        induction hf₁val : f₁.val using Sym2.ind with
        | _ a b =>
          have hab : F.Adj a b := by simpa [hf₁val] using hf₁mem
          rw [hf₁val, Sym2.mem_iff] at hx₁
          rcases hx₁ with rfl | rfl
          · exact ⟨b, hab, rfl⟩
          · exact ⟨a, hab.symm, Sym2.eq_swap⟩
      obtain ⟨w₂, hw₂adj, hw₂eq⟩ : ∃ w₂, F.Adj x w₂ ∧ f₂.val = s(x, w₂) := by
        have hf₂mem := f₂.2
        induction hf₂val : f₂.val using Sym2.ind with
        | _ a b =>
          have hab : F.Adj a b := by simpa [hf₂val] using hf₂mem
          rw [hf₂val, Sym2.mem_iff] at hx₂
          rcases hx₂ with rfl | rfl
          · exact ⟨b, hab, rfl⟩
          · exact ⟨a, hab.symm, Sym2.eq_swap⟩
      have hw₁y : w₁ ≠ y := fun h => hf₁_ne (Subtype.ext (by rw [hw₁eq, h, hxy_eq]))
      have hw₂y : w₂ ≠ y := fun h => hf₂_ne (Subtype.ext (by rw [hw₂eq, h, hxy_eq]))
      have hw₁₂ : w₁ = w₂ := by
        by_contra hne
        have hsub : ({y, w₁, w₂} : Finset U) ⊆ F.neighborFinset x := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl <;> exact (F.mem_neighborFinset _ _).mpr (by assumption)
        have hc1 : y ∉ ({w₁, w₂} : Finset U) := by simp [hw₁y.symm, hw₂y.symm]
        have hc2 : w₁ ∉ ({w₂} : Finset U) := by simp [hne]
        have h3 : 3 ≤ F.degree x := by
          calc 3 = ({y, w₁, w₂} : Finset U).card := by
                rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
                  Finset.card_singleton]
            _ ≤ (F.neighborFinset x).card := Finset.card_le_card hsub
            _ = F.degree x := F.card_neighborFinset_eq_degree x
        have := fd x
        omega
      exact Subtype.ext (by rw [hw₁eq, hw₂eq, hw₁₂])
    have hA : A.card ≤ 1 := hcard_one u v huv A rfl hval
    have hB : B.card ≤ 1 := hcard_one v u huv.symm B rfl (hval.trans Sym2.eq_swap)
    calc (LF F).degree e = ((LF F).neighborFinset e).card :=
          ((LF F).card_neighborFinset_eq_degree e).symm
      _ ≤ (A ∪ B).card := Finset.card_le_card hAB
      _ ≤ A.card + B.card := Finset.card_union_le A B
      _ ≤ 2 := by omega

structure AltWalk {U : Type*} (F : SimpleGraph U) (t : U → Bool) (u v v' u' : U) where
  m : ℕ
  hm : 1 ≤ m
  zs : List U
  hlen : zs.length = 2 * m + 1
  hnodup : zs.Nodup
  hstart : zs[0]'(by omega) = v
  hend : zs[2 * m]'(by omega) = v'
  hadj_u : F.Adj u v
  hadj_u' : F.Adj v' u'
  htu : t u = true
  htu' : t u' = true
  hne_edge : s(u, v) ≠ s(v', u')
  hadj_zs : ∀ (i : ℕ) (hi : i + 1 < zs.length), F.Adj zs[i] zs[i + 1]
  ht_even : ∀ (j : ℕ) (hj : 2 * j < zs.length), t zs[2 * j] = true
  ht_odd : ∀ (j : ℕ) (hj : 2 * j + 1 < zs.length), t zs[2 * j + 1] = false

def AltWalk.reverse {U : Type*} {F : SimpleGraph U} {t : U → Bool} {u v v' u' : U}
    (w : AltWalk F t u v v' u') : AltWalk F t u' v' v u where
  m := w.m
  hm := w.hm
  zs := w.zs.reverse
  hlen := by rw [List.length_reverse, w.hlen]
  hnodup := List.nodup_reverse.mpr w.hnodup
  hstart := by
    have hm := w.hm
    have hlen := w.hlen
    have hrev : w.zs.reverse.length = w.zs.length := List.length_reverse
    rw [List.getElem_reverse (by omega)]
    have hidx : w.zs.length - 1 - 0 = 2 * w.m := by omega
    simp only [hidx]
    exact w.hend
  hend := by
    have hm := w.hm
    have hlen := w.hlen
    have hrev : w.zs.reverse.length = w.zs.length := List.length_reverse
    rw [List.getElem_reverse (by omega)]
    have hidx : w.zs.length - 1 - 2 * w.m = 0 := by omega
    simp only [hidx]
    exact w.hstart
  hadj_u := w.hadj_u'.symm
  hadj_u' := w.hadj_u.symm
  htu := w.htu'
  htu' := w.htu
  hne_edge := fun h => w.hne_edge (by rw [Sym2.eq_swap, ← h, Sym2.eq_swap])
  hadj_zs := fun i hi => by
    have hlen := w.hlen
    rw [List.length_reverse] at hi
    rw [List.getElem_reverse (by omega), List.getElem_reverse (by omega)]
    have h1 : w.zs.length - 1 - i = (w.zs.length - 1 - (i + 1)) + 1 := by omega
    simp only [h1]
    exact (w.hadj_zs (w.zs.length - 1 - (i + 1)) (by omega)).symm
  ht_even := fun j hj => by
    have hlen := w.hlen
    have hrev : w.zs.reverse.length = w.zs.length := List.length_reverse
    rw [List.getElem_reverse (by omega)]
    have h1 : w.zs.length - 1 - 2 * j = 2 * (w.m - j) := by omega
    simp only [h1]
    exact w.ht_even (w.m - j) (by omega)
  ht_odd := fun j hj => by
    have hm := w.hm
    have hlen := w.hlen
    have hrev : w.zs.reverse.length = w.zs.length := List.length_reverse
    rw [List.getElem_reverse (by omega)]
    have h1 : w.zs.length - 1 - (2 * j + 1) = 2 * (w.m - 1 - j) + 1 := by omega
    simp only [h1]
    exact w.ht_odd (w.m - 1 - j) (by omega)

def M_aux {U : Type*} (F : SimpleGraph U) (t : U → Bool) :
    SimpleGraph {x : U // t x = true} where
  Adj x y := x ≠ y ∧ ∃ v v', Nonempty (AltWalk F t x.val v v' y.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, let ⟨v, v', ⟨w⟩⟩ := h.2; ⟨v', v, ⟨w.reverse⟩⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma M_aux_degree_le_one {U : Type*} [Fintype U] (F : SimpleGraph U) (t : U → Bool)
    (fd : ∀ v, F.degree v ≤ 2)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (x : {x : U // t x = true}) :
    (M_aux F t).degree x ≤ 1 := by
  rw [← (M_aux F t).card_neighborFinset_eq_degree x, Finset.card_le_one]
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨_, v₁, v₁', ⟨w₁⟩⟩ := ((M_aux F t).mem_neighborFinset _ _).mp hy₁
  obtain ⟨_, v₂, v₂', ⟨w₂⟩⟩ := ((M_aux F t).mem_neighborFinset _ _).mp hy₂
  have hm₁ := w₁.hm
  have hl₁ := w₁.hlen
  have hm₂ := w₂.hm
  have hl₂ := w₂.hlen
  have hv_eq : v₁ = v₂ := by
    by_contra hne
    have hv₁t : t v₁ = true := by rw [← w₁.hstart]; exact w₁.ht_even 0 (by omega)
    have hv₂t : t v₂ = true := by rw [← w₂.hstart]; exact w₂.ht_even 0 (by omega)
    exact three v₁ x.val v₂ hne w₁.hadj_u.symm w₂.hadj_u ⟨hv₁t, x.2, hv₂t⟩
  have hprefix : ∀ i : ℕ, i ≤ 2 * w₁.m → i ≤ 2 * w₂.m →
      ∀ (hi₁ : i < w₁.zs.length) (hi₂ : i < w₂.zs.length), w₁.zs[i] = w₂.zs[i] := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi₁m hi₂m hi₁ hi₂
      match i with
      | 0 => rw [w₁.hstart, w₂.hstart, hv_eq]
      | 1 =>
        have hprev : w₁.zs[0] = w₂.zs[0] := ih 0 (by omega) (by omega) (by omega) (by omega) (by omega)
        have hadj₁ : F.Adj w₁.zs[0] w₁.zs[1] := w₁.hadj_zs 0 hi₁
        have hadj₂ : F.Adj w₁.zs[0] w₂.zs[1] := by rw [hprev]; exact w₂.hadj_zs 0 hi₂
        have h1ne : w₁.zs[1] ≠ x.val := by
          intro h
          have ht1 := w₁.ht_odd 0 (by omega)
          rw [h, x.2] at ht1
          cases ht1
        have h2ne : w₂.zs[1] ≠ x.val := by
          intro h
          have ht2 := w₂.ht_odd 0 (by omega)
          rw [h, x.2] at ht2
          cases ht2
        have hxadj : F.Adj w₁.zs[0] x.val := by rw [w₁.hstart]; exact w₁.hadj_u.symm
        by_contra hne
        have hsub : ({x.val, w₁.zs[1], w₂.zs[1]} : Finset U) ⊆ F.neighborFinset w₁.zs[0] := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact (F.mem_neighborFinset _ _).mpr hxadj
          · exact (F.mem_neighborFinset _ _).mpr hadj₁
          · exact (F.mem_neighborFinset _ _).mpr hadj₂
        have hc1 : x.val ∉ ({w₁.zs[1], w₂.zs[1]} : Finset U) := by simp [h1ne.symm, h2ne.symm]
        have hc2 : w₁.zs[1] ∉ ({w₂.zs[1]} : Finset U) := by simp [hne]
        have h3 : 3 ≤ F.degree w₁.zs[0] := by
          calc 3 = ({x.val, w₁.zs[1], w₂.zs[1]} : Finset U).card := by
                rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
                  Finset.card_singleton]
            _ ≤ (F.neighborFinset w₁.zs[0]).card := Finset.card_le_card hsub
            _ = F.degree w₁.zs[0] := F.card_neighborFinset_eq_degree _
        have := fd w₁.zs[0]
        omega
      | k + 2 =>
        have hprev_eq : w₁.zs[k] = w₂.zs[k] :=
          ih k (by omega) (by omega) (by omega) (by omega) (by omega)
        have hmid_eq : w₁.zs[k + 1] = w₂.zs[k + 1] :=
          ih (k + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hadj₁ : F.Adj w₁.zs[k + 1] w₁.zs[k + 2] := w₁.hadj_zs (k + 1) hi₁
        have hadj₂ : F.Adj w₁.zs[k + 1] w₂.zs[k + 2] := by
          rw [hmid_eq]; exact w₂.hadj_zs (k + 1) hi₂
        have hadj_prev : F.Adj w₁.zs[k + 1] w₁.zs[k] := (w₁.hadj_zs k (by omega)).symm
        have h1ne : w₁.zs[k + 2] ≠ w₁.zs[k] := by
          intro h
          have hinj := w₁.hnodup.getElem_inj_iff.mp h
          omega
        have h2ne : w₂.zs[k + 2] ≠ w₁.zs[k] := by
          intro h
          rw [hprev_eq] at h
          have hinj := w₂.hnodup.getElem_inj_iff.mp h
          omega
        by_contra hne
        have hsub : ({w₁.zs[k], w₁.zs[k + 2], w₂.zs[k + 2]} : Finset U) ⊆
            F.neighborFinset w₁.zs[k + 1] := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact (F.mem_neighborFinset _ _).mpr hadj_prev
          · exact (F.mem_neighborFinset _ _).mpr hadj₁
          · exact (F.mem_neighborFinset _ _).mpr hadj₂
        have hc1 : w₁.zs[k] ∉ ({w₁.zs[k + 2], w₂.zs[k + 2]} : Finset U) := by
          simp [h1ne.symm, h2ne.symm]
        have hc2 : w₁.zs[k + 2] ∉ ({w₂.zs[k + 2]} : Finset U) := by simp [hne]
        have h3 : 3 ≤ F.degree w₁.zs[k + 1] := by
          calc 3 = ({w₁.zs[k], w₁.zs[k + 2], w₂.zs[k + 2]} : Finset U).card := by
                rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
                  Finset.card_singleton]
            _ ≤ (F.neighborFinset w₁.zs[k + 1]).card := Finset.card_le_card hsub
            _ = F.degree w₁.zs[k + 1] := F.card_neighborFinset_eq_degree _
        have := fd w₁.zs[k + 1]
        omega
  have hm_eq : w₁.m = w₂.m := by
    by_contra hne
    have hlt : w₁.m < w₂.m ∨ w₂.m < w₁.m := Nat.lt_or_gt.mp hne
    have aux : ∀ (u₁ u₂ : U) (a₁ a₁' b₁ b₂' : U)
        (wa : AltWalk F t x.val a₁ a₁' u₁) (wb : AltWalk F t x.val b₁ b₂' u₂),
        wa.m < wb.m →
        (∀ i ≤ 2 * wa.m, ∀ (hi₁ : i < wa.zs.length) (hi₂ : i < wb.zs.length),
          wa.zs[i] = wb.zs[i]) → False := by
      intro u₁ _ a₁ a₁' b₁ b₂' wa wb hlt' hpre
      have hma := wa.hm
      have hla := wa.hlen
      have hlb := wb.hlen
      have heq := hpre (2 * wa.m) (le_refl _) (by omega) (by omega)
      have hp1 : F.Adj (wb.zs[2 * wa.m]'(by omega)) (wb.zs[2 * wa.m - 1]'(by omega)) := by
        have := wb.hadj_zs (2 * wa.m - 1) (by omega)
        have hidx : 2 * wa.m - 1 + 1 = 2 * wa.m := by omega
        simp only [hidx] at this
        exact this.symm
      have hp2 : F.Adj (wb.zs[2 * wa.m]'(by omega)) (wb.zs[2 * wa.m + 1]'(by omega)) :=
        wb.hadj_zs (2 * wa.m) (by omega)
      have hp3 : F.Adj (wb.zs[2 * wa.m]'(by omega)) u₁ := by
        rw [← heq, wa.hend]; exact wa.hadj_u'
      have h12 : wb.zs[2 * wa.m - 1]'(by omega) ≠ wb.zs[2 * wa.m + 1]'(by omega) := fun h => by
        have := wb.hnodup.getElem_inj_iff.mp h; omega
      have h13 : wb.zs[2 * wa.m - 1]'(by omega) ≠ u₁ := fun h => by
        have ht := wb.ht_odd (wa.m - 1) (by omega)
        have hidx : 2 * (wa.m - 1) + 1 = 2 * wa.m - 1 := by omega
        simp only [hidx] at ht
        rw [h, wa.htu'] at ht
        cases ht
      have h23 : wb.zs[2 * wa.m + 1]'(by omega) ≠ u₁ := fun h => by
        have ht := wb.ht_odd wa.m (by omega)
        rw [h, wa.htu'] at ht
        cases ht
      have hsub : ({wb.zs[2 * wa.m - 1]'(by omega), wb.zs[2 * wa.m + 1]'(by omega), u₁} : Finset U) ⊆
          F.neighborFinset (wb.zs[2 * wa.m]'(by omega)) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> exact (F.mem_neighborFinset _ _).mpr (by assumption)
      have hc1 : wb.zs[2 * wa.m - 1]'(by omega) ∉
          ({wb.zs[2 * wa.m + 1]'(by omega), u₁} : Finset U) := by
        simp [h12, h13]
      have hc2 : wb.zs[2 * wa.m + 1]'(by omega) ∉ ({u₁} : Finset U) := by simp [h23]
      have h3 : 3 ≤ F.degree (wb.zs[2 * wa.m]'(by omega)) := by
        calc 3 = ({wb.zs[2 * wa.m - 1]'(by omega), wb.zs[2 * wa.m + 1]'(by omega), u₁} :
              Finset U).card := by
              rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
                Finset.card_singleton]
          _ ≤ (F.neighborFinset _).card := Finset.card_le_card hsub
          _ = F.degree _ := F.card_neighborFinset_eq_degree _
      have := fd (wb.zs[2 * wa.m]'(by omega))
      omega
    rcases hlt with h12 | h21
    · exact aux y₁.val y₂.val v₁ v₁' v₂ v₂' w₁ w₂ h12 (fun i hi hi1 hi2 => hprefix i hi (by omega) hi1 hi2)
    · exact aux y₂.val y₁.val v₂ v₂' v₁ v₁' w₂ w₁ h21 (fun i hi hi1 hi2 => (hprefix i (by omega) hi hi2 hi1).symm)
  have hv'_eq : v₁' = v₂' := by
    rw [← w₁.hend, ← w₂.hend]
    have hidx : 2 * w₁.m = 2 * w₂.m := by rw [hm_eq]
    have hpre := hprefix (2 * w₁.m) (le_refl _) (by omega) (by omega) (by omega)
    simp only [hidx] at hpre ⊢
    exact hpre
  have hy_eq : y₁.val = y₂.val := by
    by_contra hne
    have hprev_eq : w₁.zs[2 * w₁.m - 1]'(by omega) = w₂.zs[2 * w₂.m - 1]'(by omega) := by
      have hpre := hprefix (2 * w₁.m - 1) (by omega) (by omega) (by omega) (by omega)
      have hidx : 2 * w₂.m - 1 = 2 * w₁.m - 1 := by rw [hm_eq]
      simp only [hidx]
      exact hpre
    have hp_adj : F.Adj v₁' (w₁.zs[2 * w₁.m - 1]'(by omega)) := by
      have h := w₁.hadj_zs (2 * w₁.m - 1) (by omega)
      have hidx : 2 * w₁.m - 1 + 1 = 2 * w₁.m := by omega
      simp only [hidx, w₁.hend] at h
      exact h.symm
    have h1_adj : F.Adj v₁' y₁.val := w₁.hadj_u'
    have h2_adj : F.Adj v₁' y₂.val := by rw [hv'_eq]; exact w₂.hadj_u'
    have hp_ne1 : w₁.zs[2 * w₁.m - 1]'(by omega) ≠ y₁.val := fun h => by
      have ht := w₁.ht_odd (w₁.m - 1) (by omega)
      have hidx : 2 * (w₁.m - 1) + 1 = 2 * w₁.m - 1 := by omega
      simp only [hidx] at ht
      rw [h, y₁.2] at ht
      cases ht
    have hp_ne2 : w₁.zs[2 * w₁.m - 1]'(by omega) ≠ y₂.val := fun h => by
      rw [hprev_eq] at h
      have ht := w₂.ht_odd (w₂.m - 1) (by omega)
      have hidx : 2 * (w₂.m - 1) + 1 = 2 * w₂.m - 1 := by omega
      simp only [hidx] at ht
      rw [h, y₂.2] at ht
      cases ht
    have hsub : ({w₁.zs[2 * w₁.m - 1]'(by omega), y₁.val, y₂.val} : Finset U) ⊆
        F.neighborFinset v₁' := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl <;> exact (F.mem_neighborFinset _ _).mpr (by assumption)
    have hc1 : w₁.zs[2 * w₁.m - 1]'(by omega) ∉ ({y₁.val, y₂.val} : Finset U) :=
      by simp [hp_ne1, hp_ne2]
    have hc2 : y₁.val ∉ ({y₂.val} : Finset U) := by simp [hne]
    have h3 : 3 ≤ F.degree v₁' := by
      calc 3 = ({w₁.zs[2 * w₁.m - 1]'(by omega), y₁.val, y₂.val} : Finset U).card := by
            rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
              Finset.card_singleton]
        _ ≤ (F.neighborFinset v₁').card := Finset.card_le_card hsub
        _ = F.degree v₁' := F.card_neighborFinset_eq_degree v₁'
    have := fd v₁'
    omega
  exact Subtype.ext hy_eq

section DecomposeDeg2

private def IsSGPath {V : Type*} (G : SimpleGraph V) (l : List V) : Prop :=
  l.Nodup ∧ l ≠ [] ∧ ∀ (i : ℕ) (hi : i + 1 < l.length), G.Adj l[i] l[i + 1]

private lemma sg_three_neighbors_absurd {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 2) {x y₁ y₂ y₃ : V}
    (h12 : y₁ ≠ y₂) (h13 : y₁ ≠ y₃) (h23 : y₂ ≠ y₃)
    (ha1 : G.Adj x y₁) (ha2 : G.Adj x y₂) (ha3 : G.Adj x y₃) : False := by
  have hsub : ({y₁, y₂, y₃} : Finset V) ⊆ G.neighborFinset x := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> exact (G.mem_neighborFinset _ _).mpr (by assumption)
  have hc1 : y₁ ∉ ({y₂, y₃} : Finset V) := by simp [h12, h13]
  have hc2 : y₂ ∉ ({y₃} : Finset V) := by simp [h23]
  have h3 : 3 ≤ G.degree x := by
    calc 3 = ({y₁, y₂, y₃} : Finset V).card := by
          rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
            Finset.card_singleton]
      _ ≤ (G.neighborFinset x).card := Finset.card_le_card hsub
      _ = G.degree x := G.card_neighborFinset_eq_degree x
  have := hdeg x
  omega

private lemma sg_internal_adj {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 2) {l : List V} (hp : IsSGPath G l)
    {j : ℕ} (hj0 : 0 < j) (hj1 : j + 1 < l.length) {w : V} (hw : G.Adj l[j] w) :
    w = l[j - 1] ∨ w = l[j + 1] := by
  by_contra hnot
  push Not at hnot
  have h12 : l[j - 1] ≠ l[j + 1] := by
    intro heq
    have hinj := hp.1.getElem_inj_iff.mp heq
    omega
  have ha1 : G.Adj l[j] l[j - 1] := by
    have h := hp.2.2 (j - 1) (by omega)
    have hidx : j - 1 + 1 = j := by omega
    simp only [hidx] at h
    exact h.symm
  exact sg_three_neighbors_absurd G hdeg h12 hnot.1.symm hnot.2.symm ha1 (hp.2.2 j hj1) hw

private lemma sg_append_isPath {V : Type*} (G : SimpleGraph V) {l : List V} (hp : IsSGPath G l)
    {w : V} (hw : w ∉ l)
    (hk : G.Adj (l[l.length - 1]'(Nat.sub_lt (List.length_pos_of_ne_nil hp.2.1) zero_lt_one)) w) :
    IsSGPath G (l ++ [w]) := by
  refine ⟨List.nodup_append.mpr ⟨hp.1, List.nodup_singleton w, fun a ha b hb => ?_⟩, by simp, ?_⟩
  · simp only [List.mem_singleton] at hb
    subst hb
    intro heq
    subst heq
    exact hw ha
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    by_cases hi' : i + 1 < l.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left hi']
      exact hp.2.2 i hi'
    · have hpos : 0 < l.length := List.length_pos_of_ne_nil hp.2.1
      have hieq : i = l.length - 1 := by omega
      subst hieq
      rw [List.getElem_append_left (by omega)]
      have hidx : l.length - 1 + 1 = l.length := by omega
      simp only [hidx, List.getElem_append_right (le_refl l.length), Nat.sub_self,
        List.getElem_singleton]
      exact hk

private lemma sg_exists_max_isPath {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (P : List V → Prop) (h1 : ∃ l, P l ∧ IsSGPath G l) :
    ∃ l, P l ∧ IsSGPath G l ∧ ∀ l', P l' → IsSGPath G l' → l'.length ≤ l.length := by
  let S : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter
    (fun n => ∃ l, P l ∧ IsSGPath G l ∧ l.length = n)
  obtain ⟨l₀, hl₀P, hl₀path⟩ := h1
  have hl₀le : l₀.length ≤ Fintype.card V := hl₀path.1.length_le_card
  have hS_ne : S.Nonempty := ⟨l₀.length, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), l₀, hl₀P, hl₀path, rfl⟩⟩
  let m := S.max' hS_ne
  have hm_mem : m ∈ S := Finset.max'_mem S hS_ne
  obtain ⟨l, hlP, hlpath, hllen⟩ := (Finset.mem_filter.mp hm_mem).2
  refine ⟨l, hlP, hlpath, fun l' hl'P hl'path => ?_⟩
  have hl'le : l'.length ≤ Fintype.card V := hl'path.1.length_le_card
  have hl'mem : l'.length ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), l', hl'P, hl'path, rfl⟩
  have hmax := Finset.le_max' S l'.length hl'mem
  omega

private lemma sg_extract_component {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 2) :
    ∃ (l : List V) (isCyc : Bool), l.Nodup ∧ l ≠ [] ∧
      (isCyc = true → 3 ≤ l.length) ∧
      (∀ x ∈ l, ∀ y ∉ l, ¬ G.Adj x y) ∧
      (isCyc = false → ∀ (i : ℕ) (hi : i + 1 < l.length), G.Adj l[i] l[i + 1]) ∧
      (isCyc = false → ∀ (i j : ℕ) (hi : i < j) (hj : j < l.length), G.Adj l[i] l[j] → i + 1 = j) ∧
      (isCyc = true → ∀ (i : Fin l.length),
        G.Adj l[i.val] (l[(i.val + 1) % l.length]'(Nat.mod_lt _ (Fin.pos i)))) := by
  -- Case 1: isolated vertex
  by_cases hdeg0 : ∃ v₀ : V, G.degree v₀ = 0
  · obtain ⟨v₀, hv₀⟩ := hdeg0
    have hno : ∀ y, ¬ G.Adj v₀ y := fun y hadj => by
      have hmem : y ∈ G.neighborFinset v₀ := (G.mem_neighborFinset _ _).mpr hadj
      have hpos : 0 < (G.neighborFinset v₀).card := Finset.card_pos.mpr ⟨y, hmem⟩
      rw [G.card_neighborFinset_eq_degree, hv₀] at hpos
      omega
    refine ⟨[v₀], false, List.nodup_singleton v₀, by simp, (fun h => by cases h), ?_, ?_, ?_,
      (fun h => by cases h)⟩
    · intro x hx y _
      simp only [List.mem_singleton] at hx
      subst hx
      exact hno y
    · intro _ i hi
      simp at hi
    · intro _ i j hi hj _
      simp at hj; omega
  -- Now every vertex has degree 1 or 2
  have hdeg1 : ∀ v, 1 ≤ G.degree v := fun v => by
    have : G.degree v ≠ 0 := fun h => hdeg0 ⟨v, h⟩
    omega
  -- Case 2: degree-1 vertex exists (path component)
  by_cases hhas1 : ∃ v₀ : V, G.degree v₀ = 1
  · obtain ⟨v₀, hv₀⟩ := hhas1
    have hcard1 : (G.neighborFinset v₀).card = 1 := by rw [G.card_neighborFinset_eq_degree, hv₀]
    obtain ⟨v₁, hv₁eq⟩ := Finset.card_eq_one.mp hcard1
    have hv₁adj : G.Adj v₀ v₁ := (G.mem_neighborFinset _ _).mp (hv₁eq ▸ Finset.mem_singleton_self v₁)
    have hv₀uniq : ∀ z, G.Adj v₀ z → z = v₁ := fun z hadj => by
      have hmem : z ∈ G.neighborFinset v₀ := (G.mem_neighborFinset _ _).mpr hadj
      rw [hv₁eq, Finset.mem_singleton] at hmem
      exact hmem
    obtain ⟨l, hlhead, hlpath, hlmax⟩ := sg_exists_max_isPath G (fun l => l.head? = some v₀)
      ⟨[v₀], rfl, List.nodup_singleton v₀, by simp, fun _ hi => by simp at hi⟩
    have hpos : 0 < l.length := List.length_pos_of_ne_nil hlpath.2.1
    have hl0 : l[0] = v₀ := by
      cases l with
      | nil => exact absurd rfl hlpath.2.1
      | cons a t => simp at hlhead; exact hlhead
    have hu_out : ∀ w ∉ l, ¬ G.Adj l[l.length - 1] w := by
      intro w hw hadj
      have hp' := sg_append_isPath G hlpath hw hadj
      have hh' : (l ++ [w]).head? = some v₀ := by
        rw [List.head?_append_of_ne_nil (l₁ := l) (l₂ := [w]) hlpath.2.1]; exact hlhead
      have hle := hlmax (l ++ [w]) hh' hp'
      rw [List.length_append, List.length_singleton] at hle
      omega
    have hlen2 : 2 ≤ l.length := by
      by_contra hlt
      have hlen1 : l.length = 1 := by omega
      have hv₁_not : v₁ ∉ l := by
        intro hv₁mem
        obtain ⟨j, _, hj⟩ := List.getElem_of_mem hv₁mem
        have hj0 : j = 0 := by omega
        subst hj0
        rw [hl0] at hj
        exact hv₁adj.ne hj
      have h0 := hu_out v₁ hv₁_not
      have idx0 : l.length - 1 = 0 := by omega
      simp only [idx0, hl0] at h0
      exact h0 hv₁adj
    have hl1 : l[1] = v₁ := hv₀uniq l[1] (by
      have h := hlpath.2.2 0 (by omega)
      simp only [Nat.zero_add, hl0] at h
      exact h)
    refine ⟨l, false, hlpath.1, hlpath.2.1, (fun h => by cases h), ?_, fun _ => hlpath.2.2, ?_,
      (fun h => by cases h)⟩
    · intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      by_cases hi0 : i = 0
      · subst hi0; rw [hl0]
        intro hadj
        have := hv₀uniq y hadj
        subst this
        exact hy (hl1 ▸ List.getElem_mem _)
      · by_cases hilast : i = l.length - 1
        · subst hilast; exact hu_out y hy
        · intro hadj
          rcases sg_internal_adj G hdeg hlpath (by omega) (by omega) hadj with hy_eq | hy_eq
          · exact hy (hy_eq ▸ List.getElem_mem _)
          · exact hy (hy_eq ▸ List.getElem_mem _)
    · intro _ i j hij hj hadj
      by_cases hi0 : i = 0
      · subst hi0
        rw [hl0] at hadj
        have hlj := hv₀uniq l[j] hadj
        rw [← hl1] at hlj
        have hinj := hlpath.1.getElem_inj_iff.mp hlj
        omega
      · rcases sg_internal_adj G hdeg hlpath (by omega) (by omega) hadj with h | h
        · have hinj := hlpath.1.getElem_inj_iff.mp h; omega
        · have hinj := hlpath.1.getElem_inj_iff.mp h; omega
  -- Case 3: every vertex has degree 2 (cycle component)
  · have hdeg2 : ∀ v, G.degree v = 2 := fun v => by
      have h1 := hdeg1 v
      have h2 := hdeg v
      have hne : G.degree v ≠ 1 := fun h => hhas1 ⟨v, h⟩
      omega
    let x₀ : V := Classical.arbitrary V
    obtain ⟨l, _, hlpath, hlmax⟩ := sg_exists_max_isPath G (fun _ => True)
      ⟨[x₀], trivial, List.nodup_singleton x₀, by simp, fun _ hi => by simp at hi⟩
    have hpos : 0 < l.length := List.length_pos_of_ne_nil hlpath.2.1
    have hu_out : ∀ w ∉ l, ¬ G.Adj l[l.length - 1] w := by
      intro w hw hadj
      have hp' := sg_append_isPath G hlpath hw hadj
      have hle := hlmax (l ++ [w]) trivial hp'
      rw [List.length_append, List.length_singleton] at hle
      omega
    have hcard_last : (G.neighborFinset l[l.length - 1]).card = 2 := by
      rw [G.card_neighborFinset_eq_degree, hdeg2]
    obtain ⟨u₁, u₂, hu12, hnu⟩ := Finset.card_eq_two.mp hcard_last
    have hu1_adj : G.Adj l[l.length - 1] u₁ := (G.mem_neighborFinset _ _).mp
      (hnu ▸ Finset.mem_insert_self u₁ {u₂})
    have hu2_adj : G.Adj l[l.length - 1] u₂ := (G.mem_neighborFinset _ _).mp
      (hnu ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u₂))
    have hu1_in : u₁ ∈ l := by by_contra h; exact hu_out u₁ h hu1_adj
    have hu2_in : u₂ ∈ l := by by_contra h; exact hu_out u₂ h hu2_adj
    have hlen3 : 3 ≤ l.length := by
      obtain ⟨j₁, hj₁, rfl⟩ := List.getElem_of_mem hu1_in
      obtain ⟨j₂, hj₂, rfl⟩ := List.getElem_of_mem hu2_in
      have hj1ne : j₁ ≠ l.length - 1 := fun h => by
        simp only [h] at hu1_adj; exact G.loopless.irrefl _ hu1_adj
      have hj2ne : j₂ ≠ l.length - 1 := fun h => by
        simp only [h] at hu2_adj; exact G.loopless.irrefl _ hu2_adj
      have hj12 : j₁ ≠ j₂ := fun h => hu12 (by subst h; rfl)
      omega
    have hclose : G.Adj l[l.length - 1] l[0] := by
      have hex_other : ∃ w, w ≠ l[l.length - 2] ∧ w ∈ l ∧ G.Adj l[l.length - 1] w := by
        by_cases h1 : u₁ = l[l.length - 2]
        · exact ⟨u₂, fun h2 => hu12 (h1.trans h2.symm), hu2_in, hu2_adj⟩
        · exact ⟨u₁, h1, hu1_in, hu1_adj⟩
      obtain ⟨w, hwne, hwin, hadj⟩ := hex_other
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hwin
      have hjlast : j ≠ l.length - 1 := fun h => by
        simp only [h] at hadj; exact G.loopless.irrefl _ hadj
      have hjprev : j ≠ l.length - 2 := fun h => hwne (by subst h; rfl)
      by_cases hj0 : j = 0
      · subst hj0; exact hadj
      · exfalso
        rcases sg_internal_adj G hdeg hlpath (by omega) (by omega) hadj.symm with h | h
        · have hinj := hlpath.1.getElem_inj_iff.mp h; omega
        · have hinj := hlpath.1.getElem_inj_iff.mp h; omega
    have hcyc : ∀ (i : Fin l.length),
        G.Adj l[i.val] (l[(i.val + 1) % l.length]'(Nat.mod_lt _ (Fin.pos i))) := by
      intro i
      by_cases hi : i.val + 1 < l.length
      · simp only [Nat.mod_eq_of_lt hi]; exact hlpath.2.2 i.val hi
      · have hieq : i.val = l.length - 1 := by omega
        have hmod : (l.length - 1 + 1) % l.length = 0 := by
          have : l.length - 1 + 1 = l.length := by omega
          rw [this, Nat.mod_self]
        simp only [hieq, hmod]; exact hclose
    have hpred_eq : ∀ (i : Fin l.length),
        (((i.val + l.length - 1) % l.length) + 1) % l.length = i.val := by
      intro i
      by_cases hi0 : i.val = 0
      · simp only [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : l.length - 1 < l.length)]
        have : l.length - 1 + 1 = l.length := by omega
        rw [this, Nat.mod_self]
      · have hval : i.val + l.length - 1 = (i.val - 1) + l.length := by omega
        rw [hval, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - 1 < l.length)]
        have : i.val - 1 + 1 = i.val := by omega
        rw [this, Nat.mod_eq_of_lt i.isLt]
    have hsucc_ne_pred : ∀ (i : Fin l.length),
        (i.val + 1) % l.length ≠ (i.val + l.length - 1) % l.length := by
      intro i
      by_cases hi0 : i.val = 0
      · simp only [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < l.length),
          Nat.mod_eq_of_lt (by omega : l.length - 1 < l.length)]
        omega
      · have hval : i.val + l.length - 1 = (i.val - 1) + l.length := by omega
        rw [hval, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - 1 < l.length)]
        by_cases hilast : i.val + 1 < l.length
        · rw [Nat.mod_eq_of_lt hilast]; omega
        · have : i.val + 1 = l.length := by omega
          rw [this, Nat.mod_self]; omega
    refine ⟨l, true, hlpath.1, hlpath.2.1, fun _ => hlen3, ?_, (fun h => by cases h),
      (fun h => by cases h), fun _ => hcyc⟩
    intro x hx y hy hadj
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    let s : Fin l.length := ⟨(i + 1) % l.length, Nat.mod_lt _ (by omega)⟩
    let p : Fin l.length := ⟨(i + l.length - 1) % l.length, Nat.mod_lt _ (by omega)⟩
    have hks : G.Adj l[i] l[s.val] := hcyc ⟨i, hi⟩
    have hkp : G.Adj l[i] l[p.val] := by
      have := (hcyc p).symm
      dsimp [p] at this
      simp only [hpred_eq ⟨i, hi⟩] at this
      exact this
    have hsp : l[s.val] ≠ l[p.val] := fun heq =>
      hsucc_ne_pred ⟨i, hi⟩ (hlpath.1.getElem_inj_iff.mp heq)
    have hsy : l[s.val] ≠ y := fun h => hy (h ▸ List.getElem_mem _)
    have hpy : l[p.val] ≠ y := fun h => hy (h ▸ List.getElem_mem _)
    exact sg_three_neighbors_absurd G hdeg hsp hsy hpy hks hkp hadj

private lemma decompose_graph_deg2_aux :
    ∀ (n : ℕ) (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≤ n →
    ∀ (G : SimpleGraph V), (∀ v, G.degree v ≤ 2) →
    ∃ P : List (List V × Bool), (P.map (fun p => p.1.toFinset)).Pairwise Disjoint ∧
      (∀ x, ∃ p ∈ P, x ∈ p.1) ∧
      ∀ p ∈ P, p.1.Nodup ∧ p.1 ≠ [] ∧
        (p.2 = true → 3 ≤ p.1.length) ∧
        (∀ x ∈ p.1, ∀ y ∉ p.1, ¬ G.Adj x y) ∧
        (p.2 = false → ∀ (i : ℕ) (hi : i + 1 < p.1.length), G.Adj p.1[i] p.1[i + 1]) ∧
        (p.2 = false → ∀ (i j : ℕ) (hi : i < j) (hj : j < p.1.length),
          G.Adj p.1[i] p.1[j] → i + 1 = j) ∧
        (p.2 = true → ∀ (i : Fin p.1.length),
          G.Adj p.1[i.val] (p.1[(i.val + 1) % p.1.length]'(Nat.mod_lt _ (Fin.pos i))))
  | 0, V, _, _, hcard, G, _ => by
    have hempty : IsEmpty V := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
    exact ⟨[], List.Pairwise.nil, fun x => hempty.elim x, fun _ hp => by simp at hp⟩
  | n + 1, V, _, _, hcard, G, hdeg => by
    by_cases hempty : IsEmpty V
    · exact ⟨[], List.Pairwise.nil, fun x => hempty.elim x, fun _ hp => by simp at hp⟩
    · have : Nonempty V := not_isEmpty_iff.mp hempty
      obtain ⟨l, isCyc, hnodup, hne, hcyc3, hout, hpath_adj, hpath_no, hcyc_adj⟩ :=
        sg_extract_component G hdeg
      let V' := {z : V // z ∉ l}
      let G' := G.induce {z : V | z ∉ l}
      have hcard' : Fintype.card V' ≤ n := by
        obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil l hne
        have hlt : Fintype.card V' < Fintype.card V := by
          apply Fintype.card_lt_of_injective_of_notMem (f := Subtype.val) (b := x₀)
            Subtype.val_injective
          rintro ⟨⟨z, hz⟩, hzeq⟩
          dsimp at hzeq
          exact hz (hzeq ▸ hx₀)
        omega
      have hdeg' : ∀ x : V', G'.degree x ≤ 2 := fun x => by
        calc G'.degree x = (G'.neighborFinset x).card := (G'.card_neighborFinset_eq_degree x).symm
          _ ≤ (G.neighborFinset x.val).card := by
              refine Finset.card_le_card_of_injOn Subtype.val (fun y hy => ?_)
                (fun _ _ _ _ h => Subtype.ext h)
              exact (G.mem_neighborFinset _ _).mpr ((G'.mem_neighborFinset _ _).mp hy)
          _ = G.degree x.val := G.card_neighborFinset_eq_degree x.val
          _ ≤ 2 := hdeg x.val
      obtain ⟨P', hP'disj, hP'cov, hP'prop⟩ := decompose_graph_deg2_aux n V' hcard' G' hdeg'
      let lift (p : List V' × Bool) : List V × Bool := (p.1.map Subtype.val, p.2)
      refine ⟨(l, isCyc) :: P'.map lift, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.pairwise_cons]
        refine ⟨?_, ?_⟩
        · intro s hs
          rw [List.mem_map] at hs
          rcases hs with ⟨p, hp, rfl⟩
          rw [List.mem_map] at hp
          rcases hp with ⟨⟨l', c'⟩, _, rfl⟩
          rw [Finset.disjoint_left]
          intro z hzl hzl'
          simp only [List.mem_toFinset] at hzl hzl'
          obtain ⟨w, _, rfl⟩ := List.mem_map.mp hzl'
          exact w.2 hzl
        · rw [List.map_map]
          have hcomp : (fun p : List V × Bool => p.1.toFinset) ∘ lift =
              (fun s : Finset V' => s.map ⟨Subtype.val, Subtype.val_injective⟩) ∘
              (fun p : List V' × Bool => p.1.toFinset) := by
            ext p z; simp [lift]
          rw [hcomp, ← List.map_map]
          refine hP'disj.map _ (fun a b hab => Finset.disjoint_left.mpr fun z hza hzb => ?_)
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hza hzb
          obtain ⟨a', ha', rfl⟩ := hza
          obtain ⟨b', hb', heq⟩ := hzb
          rw [← Subtype.val_inj.mp heq] at ha'
          exact Finset.disjoint_left.mp hab ha' hb'
      · intro x
        by_cases hx : x ∈ l
        · exact ⟨(l, isCyc), by simp, hx⟩
        · obtain ⟨p', hp'mem, hxp'⟩ := hP'cov ⟨x, hx⟩
          exact ⟨lift p', List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p', hp'mem, rfl⟩),
            List.mem_map.mpr ⟨⟨x, hx⟩, hxp', rfl⟩⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact ⟨hnodup, hne, hcyc3, hout, hpath_adj, hpath_no, hcyc_adj⟩
        · obtain ⟨p', hp'mem, rfl⟩ := List.mem_map.mp hp'
          obtain ⟨hp'nodup, hp'ne, hp'cyc3, hp'out, hp'path, hp'no, hp'cyc⟩ := hP'prop p' hp'mem
          refine ⟨hp'nodup.map Subtype.val_injective, fun h => hp'ne (List.map_eq_nil_iff.mp h),
            fun hc => by simp only [lift, List.length_map]; exact hp'cyc3 hc, ?_, ?_, ?_, ?_⟩
          · intro x hx y hy hadj
            obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
            by_cases hyl : y ∈ l
            · exact hout y hyl x'.val x'.2 hadj.symm
            · exact hp'out x' hx' ⟨y, hyl⟩ (fun hmem => hy (List.mem_map.mpr ⟨⟨y, hyl⟩, hmem, rfl⟩)) hadj
          · intro hc i hi
            simp only [lift, List.length_map] at hi
            simp only [lift, List.getElem_map]
            exact hp'path hc i hi
          · intro hc i j hij hj hadj
            simp only [lift, List.length_map] at hj
            simp only [lift, List.getElem_map] at hadj
            exact hp'no hc i j hij hj hadj
          · intro hc i
            have hlen : (lift p').1.length = p'.1.length := List.length_map _
            have hi' : i.val < p'.1.length := by rw [← hlen]; exact i.isLt
            simp only [lift, List.getElem_map, hlen]
            exact hp'cyc hc ⟨i.val, hi'⟩

lemma decompose_graph_deg2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 2) :
    ∃ P : List (List V × Bool), (P.map (fun p => p.1.toFinset)).Pairwise Disjoint ∧
      (∀ x, ∃ p ∈ P, x ∈ p.1) ∧
      ∀ p ∈ P, p.1.Nodup ∧ p.1 ≠ [] ∧
        (p.2 = true → 3 ≤ p.1.length) ∧
        (∀ x ∈ p.1, ∀ y ∉ p.1, ¬ G.Adj x y) ∧
        (p.2 = false → ∀ (i : ℕ) (hi : i + 1 < p.1.length), G.Adj p.1[i] p.1[i + 1]) ∧
        (p.2 = false → ∀ (i j : ℕ) (hi : i < j) (hj : j < p.1.length),
          G.Adj p.1[i] p.1[j] → i + 1 = j) ∧
        (p.2 = true → ∀ (i : Fin p.1.length),
          G.Adj p.1[i.val] (p.1[(i.val + 1) % p.1.length]'(Nat.mod_lt _ (Fin.pos i)))) :=
  decompose_graph_deg2_aux (Fintype.card V) V (le_refl _) G hdeg

end DecomposeDeg2

section ListColorFin3

noncomputable def edgeAllowed {U : Type*} (c : U → Fin 3) (t : U → Bool) (e : Sym2 U) : Finset (Fin 3) :=
  Finset.univ.filter (fun α => ∀ v : U, t v = true → v ∈ e → α ≠ c v)

lemma list_color_path {V : Type*} :
    ∀ (es : List V) (L : V → Finset (Fin 3)),
    es.Nodup →
    (∀ i (hi : i < es.length), 1 ≤ (L es[i]).card) →
    (∀ i (hi : i + 1 < es.length), 2 ≤ (L es[i + 1]).card) →
    ∃ h : V → Fin 3, (∀ x ∈ es, h x ∈ L x) ∧
      (∀ i (hi : i + 1 < es.length), h es[i] ≠ h es[i + 1])
  | [], _, _, _, _ => ⟨fun _ => 0, fun _ hx => by simp at hx, fun _ hi => by simp at hi⟩
  | [e], L, _, h1, _ => by
    have hpos : 0 < (L e).card := h1 0 (by simp)
    obtain ⟨α, hα⟩ := Finset.card_pos.mp hpos
    refine ⟨fun _ => α, fun x hx => ?_, fun _ hi => by simp at hi⟩
    simp only [List.mem_singleton] at hx
    subst hx; exact hα
  | e :: f :: t, L, hnodup, h1, h2 => by
    have hpos : 0 < (L e).card := h1 0 (by simp)
    obtain ⟨α, hα⟩ := Finset.card_pos.mp hpos
    let L' : V → Finset (Fin 3) := fun x => if x = f then (L f).erase α else L x
    have hnodup' : (f :: t).Nodup := (List.nodup_cons.mp hnodup).2
    have hne_ef : e ≠ f := fun h => (List.nodup_cons.mp hnodup).1 (h ▸ List.mem_cons_self)
    have h1' : ∀ i (hi : i < (f :: t).length), 1 ≤ (L' (f :: t)[i]).card := by
      intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero, L', if_pos rfl]
        have hf2 : 2 ≤ (L f).card := h2 0 (by simp)
        have : (L f).card - 1 ≤ ((L f).erase α).card := Finset.pred_card_le_card_erase
        omega
      | succ k =>
        have hne : (f :: t)[k + 1] ≠ f := fun h => by
          change (f :: t)[k + 1] = (f :: t)[0]'(by simp) at h
          have := hnodup'.getElem_inj_iff.mp h
          omega
        simp only [L', if_neg hne]
        have hk := h2 (k + 1) (by simpa using hi)
        simp only [List.getElem_cons_succ] at hk ⊢
        exact Nat.le_trans (by decide) hk
    have h2' : ∀ i (hi : i + 1 < (f :: t).length), 2 ≤ (L' (f :: t)[i + 1]).card := by
      intro i hi
      have hne : (f :: t)[i + 1] ≠ f := fun h => by
        change (f :: t)[i + 1] = (f :: t)[0]'(by simp) at h
        have := hnodup'.getElem_inj_iff.mp h
        omega
      simp only [L', if_neg hne]
      exact h2 (i + 1) (by simpa using hi)
    obtain ⟨h', hh'L, hh'adj⟩ := list_color_path (f :: t) L' hnodup' h1' h2'
    refine ⟨fun x => if x = e then α else h' x, fun x hx => ?_, fun i hi => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hxt
      · simp [hα]
      · have hne_xe : x ≠ e := fun h => (List.nodup_cons.mp hnodup).1 (h ▸ hxt)
        simp only [if_neg hne_xe]
        have hxL' := hh'L x hxt
        by_cases hxf : x = f
        · subst hxf; simp only [L', if_pos rfl] at hxL'; exact Finset.erase_subset _ _ hxL'
        · simp only [L', if_neg hxf] at hxL'; exact hxL'
    · cases i with
      | zero =>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, if_neg hne_ef.symm]
        have hfL' := hh'L f List.mem_cons_self
        simp only [L', if_pos rfl] at hfL'
        exact (Finset.mem_erase.mp hfL').1.symm
      | succ k =>
        have hne1 : (e :: f :: t)[k + 1] ≠ e := fun h => by
          change (e :: f :: t)[k + 1] = (e :: f :: t)[0]'(by simp) at h
          have := hnodup.getElem_inj_iff.mp h
          omega
        have hne2 : (e :: f :: t)[k + 2] ≠ e := fun h => by
          change (e :: f :: t)[k + 2] = (e :: f :: t)[0]'(by simp) at h
          have := hnodup.getElem_inj_iff.mp h
          omega
        simp only [if_neg hne1, if_neg hne2]
        exact hh'adj k (by simpa using hi)

lemma list_color_even_cycle {V : Type*} (es : List V) (L : V → Finset (Fin 3))
    (hnodup : es.Nodup) (m : ℕ) (hm : 1 ≤ m) (hlen : es.length = 2 * m)
    (hcard : ∀ x ∈ es, (L x).card = 2) :
    ∃ h : V → Fin 3, (∀ x ∈ es, h x ∈ L x) ∧
      ∀ (i : Fin es.length), h es[i.val] ≠ h (es[(i.val + 1) % es.length]'(Nat.mod_lt _ (Fin.pos i))) := by
  by_cases hsame : ∀ (i : Fin es.length), L es[i.val] = L (es[0]'(by omega))
  · have h0card : (L (es[0]'(by omega))).card = 2 := hcard _ (List.getElem_mem _)
    obtain ⟨α, β, hαβ, hL0⟩ := Finset.card_eq_two.mp h0card
    have hα : α ∈ L (es[0]'(by omega)) := hL0 ▸ Finset.mem_insert_self α {β}
    have hβ : β ∈ L (es[0]'(by omega)) := hL0 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self β)
    let h : V → Fin 3 := fun x => if es.idxOf x % 2 = 0 then α else β
    refine ⟨h, fun x hx => ?_, fun i => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      rw [hsame ⟨j, hj⟩]
      dsimp [h]
      split_ifs
      · exact hα
      · exact hβ
    · have h1 : es.idxOf es[i.val] = i.val := hnodup.idxOf_getElem i.val i.isLt
      have h2 : es.idxOf (es[(i.val + 1) % es.length]'(Nat.mod_lt _ (Fin.pos i))) =
          (i.val + 1) % es.length := hnodup.idxOf_getElem _ (Nat.mod_lt _ (Fin.pos i))
      dsimp [h]
      rw [h1, h2]
      have hpar : (i.val + 1) % es.length % 2 ≠ i.val % 2 := by
        have hlen' : es.length = 2 * m := hlen
        simp only [hlen']
        by_cases hi : i.val + 1 < 2 * m
        · rw [Nat.mod_eq_of_lt hi]; omega
        · have hieq : i.val + 1 = 2 * m := by have := i.isLt; omega
          rw [hieq, Nat.mod_self]; omega
      split_ifs with hA hB
      · exfalso; exact hpar (hB.trans hA.symm)
      · exact hαβ
      · exact hαβ.symm
      · exfalso; apply hpar; omega
  · have hex_diff : ∃ i : Fin es.length,
        L es[i.val] ≠ L (es[(i.val + 1) % es.length]'(Nat.mod_lt _ (Fin.pos i))) := by
      by_contra h
      push Not at h
      apply hsame
      have hall : ∀ (idx : ℕ) (hidx : idx < es.length), L es[idx] = L (es[0]'(by omega)) := by
        intro idx
        induction idx with
        | zero => intro _; rfl
        | succ j ih =>
          intro hj
          have hj_step := h ⟨j, by omega⟩
          simp only [Nat.mod_eq_of_lt hj] at hj_step
          exact hj_step.symm.trans (ih (by omega))
      intro i
      exact hall i.val i.isLt
    obtain ⟨i, hi_diff⟩ := hex_diff
    let r := (i.val + 1) % es.length
    let es' := es.rotate r
    have hnodup' : es'.Nodup := List.nodup_rotate.mpr hnodup
    have hlen' : es'.length = es.length := by simp [es']
    have hcard' : ∀ x ∈ es', (L x).card = 2 := fun x hx => hcard x (List.mem_rotate.mp hx)
    have hr_lt : r < es.length := Nat.mod_lt _ (Fin.pos i)
    have h0_eq : es'[0]'(by omega) = es[r] := by
      simp only [es', List.getElem_rotate, Nat.zero_add, Nat.mod_eq_of_lt hr_lt]
    have hlast_eq : es'[es'.length - 1]'(by omega) = es[i.val] := by
      simp only [es', List.getElem_rotate, hlen']
      congr 1
      by_cases hilast : i.val + 1 < es.length
      · have hr : r = i.val + 1 := Nat.mod_eq_of_lt hilast
        rw [hr]
        have hsum : es.length - 1 + (i.val + 1) = i.val + es.length := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      · have hieq : i.val = es.length - 1 := by omega
        have hr : r = 0 := by
          dsimp [r]; rw [hieq]
          have hsum : es.length - 1 + 1 = es.length := by omega
          rw [hsum, Nat.mod_self]
        rw [hr, Nat.add_zero, Nat.mod_eq_of_lt (by omega), hieq]
    have hdiff' : L (es'[0]'(by omega)) ≠ L (es'[es'.length - 1]'(by omega)) := by
      rw [h0_eq, hlast_eq]; exact hi_diff.symm
    have hex_alpha : ∃ α ∈ L (es'[0]'(by omega)), α ∉ L (es'[es'.length - 1]'(by omega)) := by
      by_contra h
      push Not at h
      have hsub : L (es'[0]'(by omega)) ⊆ L (es'[es'.length - 1]'(by omega)) := h
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [hcard' _ (List.getElem_mem _), hcard' _ (List.getElem_mem _)])
      exact hdiff' heq
    obtain ⟨α, hα0, hαlast⟩ := hex_alpha
    let L' : V → Finset (Fin 3) := fun x => if x = es'[0]'(by omega) then {α} else L x
    have h1' : ∀ j (hj : j < es'.length), 1 ≤ (L' (es'[j]'hj)).card := by
      intro j hj
      dsimp [L']
      split_ifs
      · simp
      · rw [hcard' _ (List.getElem_mem _)]; decide
    have h2' : ∀ j (hj : j + 1 < es'.length), 2 ≤ (L' (es'[j + 1]'hj)).card := by
      intro j hj
      have hne : es'[j + 1]'hj ≠ es'[0]'(by omega) := fun h => by
        have := hnodup'.getElem_inj_iff.mp h
        omega
      simp only [L', if_neg hne]
      rw [hcard' _ (List.getElem_mem _)]
    obtain ⟨h, hhL', hhadj⟩ := list_color_path es' L' hnodup' h1' h2'
    have hhL : ∀ x ∈ es', h x ∈ L x := by
      intro x hx
      have := hhL' x hx
      dsimp [L'] at this
      split_ifs at this with hxeq
      · subst hxeq; rw [Finset.mem_singleton.mp this]; exact hα0
      · exact this
    refine ⟨h, fun x hx => hhL x (List.mem_rotate.mpr hx), fun k => ?_⟩
    have hcyc_rot : ∀ (j : Fin es'.length),
        h (es'[j.val]'j.isLt) ≠ h (es'[(j.val + 1) % es'.length]'(Nat.mod_lt _ (Fin.pos j))) := by
      intro j
      by_cases hj : j.val + 1 < es'.length
      · simp only [Nat.mod_eq_of_lt hj]
        exact hhadj j.val hj
      · have hjeq : j.val = es'.length - 1 := by omega
        have hmod : (j.val + 1) % es'.length = 0 := by
          have : j.val + 1 = es'.length := by omega
          rw [this, Nat.mod_self]
        have hmod_eq : es'[(j.val + 1) % es'.length]'(Nat.mod_lt _ (Fin.pos j)) = es'[0]'(by omega) := by
          congr 1
        have hjeq' : es'[j.val]'j.isLt = es'[es'.length - 1]'(by omega) := by
          congr 1
        rw [hmod_eq, hjeq']
        intro heq
        have hlast_mem : h (es'[es'.length - 1]'(by omega)) ∈ L (es'[es'.length - 1]'(by omega)) :=
          hhL _ (List.getElem_mem _)
        have h0_mem : h (es'[0]'(by omega)) ∈ ({α} : Finset (Fin 3)) := by
          have := hhL' _ (List.getElem_mem (by omega : 0 < es'.length))
          simpa [L'] using this
        rw [Finset.mem_singleton.mp h0_mem] at heq
        rw [heq] at hlast_mem
        exact hαlast hlast_mem
    let j0 : ℕ := (k.val + es.length - r) % es.length
    have hj0_lt : j0 < es'.length := by rw [hlen']; exact Nat.mod_lt _ (Fin.pos k)
    have hrot_id : ∀ (a : ℕ) (ha : a < es.length),
        es'[((a + es.length - r) % es.length)]'(by rw [hlen']; exact Nat.mod_lt _ (Fin.pos k)) =
        es[a] := by
      intro a ha
      simp only [es', List.getElem_rotate]
      congr 1
      rw [Nat.mod_add_mod]
      by_cases har : r ≤ a
      · have hsum : a + es.length - r + r = a + es.length := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
      · have hsum : a + es.length - r + r = a + es.length := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
    have hj1_eq : (j0 + 1) % es'.length = ((k.val + 1) % es.length + es.length - r) % es.length := by
      rw [hlen']
      dsimp [j0]
      rw [Nat.mod_add_mod]
      by_cases hkr : r ≤ k.val
      · have hsum : k.val + es.length - r + 1 = (k.val + 1) + es.length - r := by omega
        by_cases hk1 : k.val + 1 < es.length
        · rw [Nat.mod_eq_of_lt hk1, hsum]
        · have hkeq : k.val + 1 = es.length := by omega
          rw [hkeq, Nat.mod_self, Nat.zero_add]
          have h1 : k.val + es.length - r + 1 = (es.length - r) + es.length := by omega
          rw [h1, Nat.add_mod_right]
      · have hsum : k.val + es.length - r + 1 = (k.val + 1 + es.length - r) := by omega
        by_cases hk1 : k.val + 1 < es.length
        · rw [Nat.mod_eq_of_lt hk1, hsum]
        · have hkeq : k.val + 1 = es.length := by omega
          rw [hkeq, Nat.mod_self, Nat.zero_add]
          have h1 : k.val + es.length - r + 1 = (es.length - r) + es.length := by omega
          rw [h1, Nat.add_mod_right]
    have he0 := hrot_id k.val k.isLt
    have he1 := hrot_id ((k.val + 1) % es.length) (Nat.mod_lt _ (Fin.pos k))
    have hc := hcyc_rot ⟨j0, hj0_lt⟩
    dsimp at hc
    rw [he0] at hc
    have he1' : es'[(j0 + 1) % es'.length]'(Nat.mod_lt _ (Fin.pos ⟨j0, hj0_lt⟩)) =
        es[(k.val + 1) % es.length]'(Nat.mod_lt _ (Fin.pos k)) := by
      simp only [hj1_eq]
      exact he1
    rw [he1'] at hc
    exact hc

lemma list_color_even_chain {U : Type*} (F : SimpleGraph U) (t : U → Bool)
    (c : U → Fin 3) :
    ∀ (m : ℕ) (_hm : 1 ≤ m) (es : List F.edgeSet) (zs : List U),
    es.Nodup →
    ∀ (hlen_e : es.length = 2 * m) (hlen_z : zs.length = 2 * m + 1),
    (∀ (i : ℕ) (hi : i < 2 * m),
      (es[i]'(by omega)).val = s(zs[i]'(by omega), zs[i + 1]'(by omega))) →
    (∀ (j : ℕ) (hj : 2 * j < 2 * m + 1), t (zs[2 * j]'(by omega)) = true) →
    (∀ (j : ℕ) (hj : 2 * j + 1 < 2 * m + 1), t (zs[2 * j + 1]'(by omega)) = false) →
    ∀ (αL αR : Fin 3),
    αL ∈ edgeAllowed c t (es[0]'(by omega)).val →
    αR ∈ edgeAllowed c t (es[2 * m - 1]'(by omega)).val →
    (αL ≠ αR ∨ ∃ (_ : 2 ≤ m), c (zs[2]'(by omega)) = αL) →
    ∃ h : F.edgeSet → Fin 3,
      h (es[0]'(by omega)) = αL ∧
      h (es[2 * m - 1]'(by omega)) = αR ∧
      (∀ x ∈ es, h x ∈ edgeAllowed c t x.val) ∧
      (∀ (i : ℕ) (hi : i + 1 < 2 * m), h (es[i]'(by omega)) ≠ h (es[i + 1]'(by omega)))
  | 0, hm, _, _, _, _, _, _, _, _, _, _, _, _, _ => by omega
  | 1, _, es, zs, hnodup, hlen_e, _, _, _, _, αL, αR, hαL, hαR, hcond => by
    have hne_cond : αL ≠ αR := by
      rcases hcond with h | ⟨h2, _⟩
      · exact h
      · omega
    have hne_e : (es[0]'(by omega)) ≠ (es[1]'(by omega)) := fun h => by
      have := hnodup.getElem_inj_iff.mp h; omega
    refine ⟨fun e => if e = es[0]'(by omega) then αL else αR,
      if_pos rfl, if_neg hne_e.symm, fun x hx => ?_, fun i hi => ?_⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hj2 : j = 0 ∨ j = 1 := by omega
      rcases hj2 with rfl | rfl
      · dsimp only; rw [if_pos rfl]; exact hαL
      · dsimp only; rw [if_neg hne_e.symm]; exact hαR
    · have hi0 : i = 0 := by omega
      subst hi0
      dsimp only; rw [if_pos rfl, if_neg hne_e.symm]
      exact hne_cond
  | k + 2, _, es, zs, hnodup, hlen_e, hlen_z, hes_val, ht_even, ht_odd,
      αL, αR, hαL, hαR, hcond => by
    have ht1 : t (zs[1]'(by omega)) = false := ht_odd 0 (by omega)
    have ht2 : t (zs[2]'(by omega)) = true := ht_even 1 (by omega)
    have ht3 : t (zs[3]'(by omega)) = false := ht_odd 1 (by omega)
    have he1_val : (es[1]'(by omega)).val = s(zs[1]'(by omega), zs[2]'(by omega)) :=
      hes_val 1 (by omega)
    have he2_val : (es[2]'(by omega)).val = s(zs[2]'(by omega), zs[3]'(by omega)) :=
      hes_val 2 (by omega)
    have hL1_eq : edgeAllowed c t (es[1]'(by omega)).val =
        Finset.univ.erase (c (zs[2]'(by omega))) := by
      ext γ
      simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        he1_val, Sym2.mem_iff]
      constructor
      · intro h
        exact ⟨h _ ht2 (Or.inr rfl), trivial⟩
      · rintro ⟨hγ, _⟩ v htv (rfl | rfl)
        · rw [ht1] at htv; cases htv
        · exact hγ
    have hL2_eq : edgeAllowed c t (es[2]'(by omega)).val =
        Finset.univ.erase (c (zs[2]'(by omega))) := by
      ext γ
      simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        he2_val, Sym2.mem_iff]
      constructor
      · intro h
        exact ⟨h _ ht2 (Or.inl rfl), trivial⟩
      · rintro ⟨hγ, _⟩ v htv (rfl | rfl)
        · exact hγ
        · rw [ht3] at htv; cases htv
    by_cases hc2 : c (zs[2]'(by omega)) = αL
    · -- Color es.tail.reverse greedily starting from es[2*(k+2)-1] with {αR}
      let revTail := es.tail.reverse
      have hlen_tail : es.tail.length = 2 * (k + 2) - 1 := by
        rw [List.length_tail, hlen_e]
      have hlen_rev : revTail.length = 2 * (k + 2) - 1 := by
        rw [List.length_reverse, hlen_tail]
      have hnodup_rev : revTail.Nodup := List.nodup_reverse.mpr hnodup.tail
      have hrev0 : revTail[0]'(by omega) = es[2 * (k + 2) - 1]'(by omega) := by
        simp only [revTail, List.getElem_reverse, List.getElem_tail, hlen_tail]
        congr 1
      have hrevlast : revTail[revTail.length - 1]'(by omega) = es[1]'(by omega) := by
        simp only [revTail, List.getElem_reverse, List.getElem_tail, hlen_rev, hlen_tail]
        congr 1; omega
      let L' : F.edgeSet → Finset (Fin 3) := fun e =>
        if e = es[2 * (k + 2) - 1]'(by omega) then {αR} else edgeAllowed c t e.val
      have hcard_ge2 : ∀ i (hi : i < 2 * (k + 2)),
          i ≥ 1 → 2 ≤ (edgeAllowed c t (es[i]'(by omega)).val).card := by
        intro i hi hi1
        have hval := hes_val i hi
        by_cases heven : i % 2 = 0
        · have ht_i : t (zs[i]'(by omega)) = true := by
            have := ht_even (i / 2) (by omega)
            have hmul : 2 * (i / 2) = i := by omega
            simpa [hmul] using this
          have ht_next : t (zs[i + 1]'(by omega)) = false := by
            have := ht_odd (i / 2) (by omega)
            have hmul : 2 * (i / 2) + 1 = i + 1 := by omega
            simpa [hmul] using this
          have hsub : (Finset.univ.erase (c (zs[i]'(by omega)))) ⊆
              edgeAllowed c t (es[i]'(by omega)).val := by
            intro γ hγ
            simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and, hval, Sym2.mem_iff]
            rintro v htv (rfl | rfl)
            · exact (Finset.mem_erase.mp hγ).1
            · rw [ht_next] at htv; cases htv
          have hc2' : (Finset.univ.erase (c (zs[i]'(by omega)))).card = 2 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; decide
          exact hc2'.symm.le.trans (Finset.card_le_card hsub)
        · have ht_i : t (zs[i]'(by omega)) = false := by
            have := ht_odd ((i - 1) / 2) (by omega)
            have hmul : 2 * ((i - 1) / 2) + 1 = i := by omega
            simpa [hmul] using this
          have ht_next : t (zs[i + 1]'(by omega)) = true := by
            have := ht_even ((i + 1) / 2) (by omega)
            have hmul : 2 * ((i + 1) / 2) = i + 1 := by omega
            simpa [hmul] using this
          have hsub : (Finset.univ.erase (c (zs[i + 1]'(by omega)))) ⊆
              edgeAllowed c t (es[i]'(by omega)).val := by
            intro γ hγ
            simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and, hval, Sym2.mem_iff]
            rintro v htv (rfl | rfl)
            · rw [ht_i] at htv; cases htv
            · exact (Finset.mem_erase.mp hγ).1
          have hc2' : (Finset.univ.erase (c (zs[i + 1]'(by omega)))).card = 2 := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; decide
          exact hc2'.symm.le.trans (Finset.card_le_card hsub)
      have h1' : ∀ j (hj : j < revTail.length), 1 ≤ (L' (revTail[j]'hj)).card := by
        intro j hj
        dsimp [L']
        split_ifs
        · simp
        · have hidx_eq : revTail[j]'hj = es[2 * (k + 2) - 1 - j]'(by omega) := by
            simp only [revTail, List.getElem_reverse, List.getElem_tail, hlen_tail]
            congr 1; omega
          rw [hidx_eq]
          exact Nat.le_trans (by decide) (hcard_ge2 (2 * (k + 2) - 1 - j) (by omega) (by omega))
      have h2' : ∀ j (hj : j + 1 < revTail.length), 2 ≤ (L' (revTail[j + 1]'hj)).card := by
        intro j hj
        have hne : revTail[j + 1]'hj ≠ es[2 * (k + 2) - 1]'(by omega) := by
          rw [← hrev0]
          intro h
          have := hnodup_rev.getElem_inj_iff.mp h
          omega
        simp only [L', if_neg hne]
        have hidx_eq : revTail[j + 1]'hj = es[2 * (k + 2) - 1 - (j + 1)]'(by omega) := by
          simp only [revTail, List.getElem_reverse, List.getElem_tail, hlen_tail]
          congr 1; omega
        rw [hidx_eq]
        exact hcard_ge2 (2 * (k + 2) - 1 - (j + 1)) (by omega) (by omega)
      obtain ⟨h', hh'L, hh'adj⟩ := list_color_path revTail L' hnodup_rev h1' h2'
      refine ⟨fun e => if e = es[0]'(by omega) then αL else h' e,
        if_pos rfl, ?_, fun x hx => ?_, fun i hi => ?_⟩
      · have hne : es[2 * (k + 2) - 1]'(by omega) ≠ es[0]'(by omega) := fun h => by
          have := hnodup.getElem_inj_iff.mp h; omega
        dsimp only; rw [if_neg hne]
        have hmem := hh'L _ (hrev0 ▸ List.getElem_mem (by omega : 0 < revTail.length))
        simp only [L', if_pos rfl] at hmem
        exact Finset.mem_singleton.mp hmem
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        cases j with
        | zero => dsimp only; rw [if_pos rfl]; exact hαL
        | succ j' =>
          have hne : es[j' + 1]'(by omega) ≠ es[0]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          dsimp only; rw [if_neg hne]
          have hmem_rev : es[j' + 1]'(by omega) ∈ revTail := by
            rw [List.mem_reverse]
            have : es[j' + 1]'(by omega) = es.tail[j']'(by rw [hlen_tail]; omega) :=
              (List.getElem_tail (by rw [hlen_tail]; omega)).symm
            rw [this]; exact List.getElem_mem _
          have hmem := hh'L _ hmem_rev
          dsimp [L'] at hmem
          split_ifs at hmem with heq
          · rw [Finset.mem_singleton.mp hmem, heq]; exact hαR
          · exact hmem
      · cases i with
        | zero =>
          have hne : es[1]'(by omega) ≠ es[0]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          dsimp only; rw [if_pos rfl, if_neg hne]
          have hmem1_rev : es[1]'(by omega) ∈ revTail := hrevlast ▸ List.getElem_mem _
          have hmem1 := hh'L _ hmem1_rev
          have hne_last : es[1]'(by omega) ≠ es[2 * (k + 2) - 1]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          simp only [L', if_neg hne_last] at hmem1
          rw [hL1_eq, hc2] at hmem1
          exact (Finset.mem_erase.mp hmem1).1.symm
        | succ j' =>
          have hne1 : es[j' + 1]'(by omega) ≠ es[0]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          have hne2 : es[j' + 2]'(by omega) ≠ es[0]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          dsimp only; rw [if_neg hne1, if_neg hne2]
          let rIdx := 2 * (k + 2) - 1 - (j' + 2)
          have hrIdx_lt : rIdx + 1 < revTail.length := by omega
          have hre0 : revTail[rIdx]'(by omega) = es[j' + 2]'(by omega) := by
            simp only [revTail, List.getElem_reverse, List.getElem_tail, hlen_tail]
            congr 1; omega
          have hre1 : revTail[rIdx + 1]'hrIdx_lt = es[j' + 1]'(by omega) := by
            simp only [revTail, List.getElem_reverse, List.getElem_tail, hlen_tail]
            congr 1; omega
          have hadj_rev := hh'adj rIdx hrIdx_lt
          rw [hre0, hre1] at hadj_rev
          exact hadj_rev.symm
    · -- c zs[2] ≠ αL, so αL ≠ αR holds
      have hne_cond : αL ≠ αR := by
        rcases hcond with h | ⟨_, hcz⟩
        · exact h
        · exact absurd hcz hc2
      have hcard_er : ((Finset.univ.erase (c (zs[2]'(by omega)))).erase αL).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hc2, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin 3]
      obtain ⟨β, hβmem⟩ := Finset.card_pos.mp (by rw [hcard_er]; omega)
      have hβαL : β ≠ αL := (Finset.mem_erase.mp hβmem).1
      have hβc2 : β ≠ c (zs[2]'(by omega)) := (Finset.mem_erase.mp (Finset.mem_erase.mp hβmem).2).1
      let es' := es.drop 2
      let zs' := zs.drop 2
      have hlen_e' : es'.length = 2 * (k + 1) := by rw [List.length_drop, hlen_e]; omega
      have hlen_z' : zs'.length = 2 * (k + 1) + 1 := by rw [List.length_drop, hlen_z]; omega
      have hnodup' : es'.Nodup := hnodup.sublist (List.drop_sublist _ _)
      have hes'_val : ∀ i (hi : i < 2 * (k + 1)),
          (es'[i]'(by omega)).val = s(zs'[i]'(by omega), zs'[i + 1]'(by omega)) := by
        intro i hi
        simp only [es', zs', List.getElem_drop]
        have h := hes_val (2 + i) (by omega)
        have h1 : 2 + i + 1 = 2 + (i + 1) := by omega
        simpa [h1] using h
      have ht'_even : ∀ j (hj : 2 * j < 2 * (k + 1) + 1), t (zs'[2 * j]'(by omega)) = true := by
        intro j hj
        simp only [zs', List.getElem_drop]
        have h := ht_even (1 + j) (by omega)
        have h1 : 2 * (1 + j) = 2 + 2 * j := by omega
        simpa [h1] using h
      have ht'_odd : ∀ j (hj : 2 * j + 1 < 2 * (k + 1) + 1), t (zs'[2 * j + 1]'(by omega)) = false := by
        intro j hj
        simp only [zs', List.getElem_drop]
        have h := ht_odd (1 + j) (by omega)
        have h1 : 2 * (1 + j) + 1 = 2 + (2 * j + 1) := by omega
        simpa [h1] using h
      have hαL' : αL ∈ edgeAllowed c t (es'[0]'(by omega)).val := by
        have h0 : es'[0]'(by omega) = es[2]'(by omega) := by simp [es']
        rw [h0, hL2_eq]
        exact Finset.mem_erase.mpr ⟨Ne.symm hc2, Finset.mem_univ _⟩
      have hαR' : αR ∈ edgeAllowed c t (es'[2 * (k + 1) - 1]'(by omega)).val := by
        have hlast : es'[2 * (k + 1) - 1]'(by omega) = es[2 * (k + 2) - 1]'(by omega) := by
          simp only [es', List.getElem_drop]; congr 1; omega
        rw [hlast]; exact hαR
      obtain ⟨h', hh'0, hh'last, hh'L, hh'adj⟩ :=
        list_color_even_chain F t c (k + 1) (by omega) es' zs' hnodup' hlen_e' hlen_z'
          hes'_val ht'_even ht'_odd αL αR hαL' hαR' (Or.inl hne_cond)
      have hne_01 : es[0]'(by omega) ≠ es[1]'(by omega) := fun h => by
        have := hnodup.getElem_inj_iff.mp h; omega
      refine ⟨fun e => if e = es[0]'(by omega) then αL else
          if e = es[1]'(by omega) then β else h' e,
        if_pos rfl, ?_, fun x hx => ?_, fun i hi => ?_⟩
      · have hne0 : es[2 * (k + 2) - 1]'(by omega) ≠ es[0]'(by omega) := fun h => by
          have := hnodup.getElem_inj_iff.mp h; omega
        have hne1 : es[2 * (k + 2) - 1]'(by omega) ≠ es[1]'(by omega) := fun h => by
          have := hnodup.getElem_inj_iff.mp h; omega
        dsimp only; rw [if_neg hne0, if_neg hne1]
        have hlast : es'[2 * (k + 1) - 1]'(by omega) = es[2 * (k + 2) - 1]'(by omega) := by
          simp only [es', List.getElem_drop]; congr 1; omega
        rw [← hlast]; exact hh'last
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
        match j with
        | 0 => dsimp only; rw [if_pos rfl]; exact hαL
        | 1 =>
          dsimp only; rw [if_neg hne_01.symm, if_pos rfl, hL1_eq]
          exact Finset.mem_erase.mpr ⟨hβc2, Finset.mem_univ _⟩
        | j' + 2 =>
          have hne0 : es[j' + 2]'(by omega) ≠ es[0]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          have hne1 : es[j' + 2]'(by omega) ≠ es[1]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          dsimp only; rw [if_neg hne0, if_neg hne1]
          have hmem' : es[j' + 2]'(by omega) ∈ es' := by
            have : es[j' + 2]'(by omega) = es'[j']'(by rw [hlen_e']; omega) := by
              simp only [es', List.getElem_drop]; congr 1; omega
            rw [this]; exact List.getElem_mem _
          exact hh'L _ hmem'
      · match i with
        | 0 =>
          dsimp only; rw [if_pos rfl, if_neg hne_01.symm, if_pos rfl]
          exact hβαL.symm
        | 1 =>
          have hne0 : es[2]'(by omega) ≠ es[0]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          have hne1 : es[2]'(by omega) ≠ es[1]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          dsimp only; rw [if_neg hne_01.symm, if_pos rfl, if_neg hne0, if_neg hne1]
          have h0 : es'[0]'(by omega) = es[2]'(by omega) := by simp [es']
          rw [← h0, hh'0]
          exact hβαL
        | j' + 2 =>
          have hne0a : es[j' + 2]'(by omega) ≠ es[0]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          have hne1a : es[j' + 2]'(by omega) ≠ es[1]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          have hne0b : es[j' + 3]'(by omega) ≠ es[0]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          have hne1b : es[j' + 3]'(by omega) ≠ es[1]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          dsimp only; rw [if_neg hne0a, if_neg hne1a, if_neg hne0b, if_neg hne1b]
          have ha : es[j' + 2]'(by omega) = es'[j']'(by omega) := by
            simp only [es', List.getElem_drop]; congr 1; omega
          have hb : es[j' + 3]'(by omega) = es'[j' + 1]'(by omega) := by
            simp only [es', List.getElem_drop]; congr 1; omega
          rw [ha, hb]
          exact hh'adj j' (by omega)

end ListColorFin3

/- Step 2 wrapper: list_color_LF coloring F.edgeSet from vertex coloring c of S. -/

section ListColorLF

private lemma sg_cycle_adj_iff {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hdeg : ∀ v, G.degree v ≤ 2) {l : List V} (hnodup : l.Nodup) (hlen3 : 3 ≤ l.length)
    (hcyc : ∀ (i : Fin l.length),
      G.Adj l[i.val] (l[(i.val + 1) % l.length]'(Nat.mod_lt _ (Fin.pos i))))
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hadj : G.Adj l[i] l[j]) :
    j = (i + 1) % l.length ∨ i = (j + 1) % l.length := by
  let sIdx : ℕ := (i + 1) % l.length
  let pIdx : ℕ := (i + l.length - 1) % l.length
  have hs_lt : sIdx < l.length := Nat.mod_lt _ (by omega)
  have hp_lt : pIdx < l.length := Nat.mod_lt _ (by omega)
  have hp_succ : (pIdx + 1) % l.length = i := by
    dsimp [pIdx]
    rw [Nat.mod_add_mod]
    by_cases hi0 : i = 0
    · simp only [hi0, Nat.zero_add]
      have h1 : l.length - 1 + 1 = l.length := by omega
      rw [h1, Nat.mod_self]
    · have h1 : i + l.length - 1 + 1 = i + l.length := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  have hs_adj : G.Adj l[i] l[sIdx] := hcyc ⟨i, hi⟩
  have hp_adj : G.Adj l[i] l[pIdx] := by
    have h := (hcyc ⟨pIdx, hp_lt⟩).symm
    dsimp at h
    have hidx : l[(pIdx + 1) % l.length]'(Nat.mod_lt _ (by omega)) = l[i] := by
      congr 1
    rwa [hidx] at h
  have hsp_idx : sIdx ≠ pIdx := by
    dsimp [sIdx, pIdx]
    by_cases hi0 : i = 0
    · simp only [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < l.length),
        Nat.mod_eq_of_lt (by omega : l.length - 1 < l.length)]
      omega
    · have h1 : i + l.length - 1 = (i - 1) + l.length := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < l.length)]
      by_cases hil : i + 1 < l.length
      · rw [Nat.mod_eq_of_lt hil]; omega
      · have : i + 1 = l.length := by omega
        rw [this, Nat.mod_self]; omega
  have hsp : l[sIdx] ≠ l[pIdx] := fun h => hsp_idx (hnodup.getElem_inj_iff.mp h)
  by_cases hjs : j = sIdx
  · exact Or.inl hjs
  · by_cases hjp : j = pIdx
    · exact Or.inr (hjp ▸ hp_succ.symm)
    · exfalso
      have hjs' : l[sIdx] ≠ l[j] := fun h => hjs (hnodup.getElem_inj_iff.mp h).symm
      have hjp' : l[pIdx] ≠ l[j] := fun h => hjp (hnodup.getElem_inj_iff.mp h).symm
      have hsub : ({l[sIdx], l[pIdx], l[j]} : Finset V) ⊆ G.neighborFinset l[i] := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> exact (G.mem_neighborFinset _ _).mpr (by assumption)
      have hc1 : l[sIdx] ∉ ({l[pIdx], l[j]} : Finset V) := by simp [hsp, hjs']
      have hc2 : l[pIdx] ∉ ({l[j]} : Finset V) := by simp [hjp']
      have h3 : 3 ≤ G.degree l[i] := by
        calc 3 = ({l[sIdx], l[pIdx], l[j]} : Finset V).card := by
              rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
                Finset.card_singleton]
          _ ≤ (G.neighborFinset l[i]).card := Finset.card_le_card hsub
          _ = G.degree l[i] := G.card_neighborFinset_eq_degree _
      have := hdeg l[i]
      omega

private lemma exists_otherEnd {U : Type*} (F : SimpleGraph U) (e : F.edgeSet) (u : U)
    (hu : u ∈ e.val) : ∃ v : U, F.Adj u v ∧ e.val = s(u, v) := by
  have he := e.2
  induction hval : e.val using Sym2.ind with
  | _ a b =>
    have hab : F.Adj a b := by simpa [hval] using he
    rw [hval, Sym2.mem_iff] at hu
    rcases hu with rfl | rfl
    · exact ⟨b, hab, rfl⟩
    · exact ⟨a, hab.symm, Sym2.eq_swap⟩

private noncomputable def otherVertex {U : Type*} (F : SimpleGraph U) (e : F.edgeSet) (u : U) : U :=
  if h : u ∈ e.val then Classical.choose (exists_otherEnd F e u h) else u

private lemma otherVertex_spec {U : Type*} (F : SimpleGraph U) (e : F.edgeSet) (u : U)
    (hu : u ∈ e.val) :
    F.Adj u (otherVertex F e u) ∧ e.val = s(u, otherVertex F e u) := by
  simp only [otherVertex, dif_pos hu]
  exact Classical.choose_spec (exists_otherEnd F e u hu)

private lemma sym2_mem_and_eq_other {U : Type*} {F : SimpleGraph U} {e : F.edgeSet} {u v w : U}
    (huv : e.val = s(u, v)) (hw : w ∈ e.val) (hwu : w ≠ u) : w = v := by
  rw [huv, Sym2.mem_iff] at hw
  exact hw.resolve_left hwu

private lemma three_edges_at_vertex_absurd {U : Type*} [Fintype U] (F : SimpleGraph U)
    (fd : ∀ v, F.degree v ≤ 2) {e₁ e₂ e₃ : F.edgeSet}
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    {v : U} (hv1 : v ∈ e₁.val) (hv2 : v ∈ e₂.val) (hv3 : v ∈ e₃.val) : False := by
  obtain ⟨u₁, hu₁adj, hu₁eq⟩ := exists_otherEnd F e₁ v hv1
  obtain ⟨u₂, hu₂adj, hu₂eq⟩ := exists_otherEnd F e₂ v hv2
  obtain ⟨u₃, hu₃adj, hu₃eq⟩ := exists_otherEnd F e₃ v hv3
  have h12u : u₁ ≠ u₂ := fun h => h12 (Subtype.ext (by rw [hu₁eq, hu₂eq, h]))
  have h13u : u₁ ≠ u₃ := fun h => h13 (Subtype.ext (by rw [hu₁eq, hu₃eq, h]))
  have h23u : u₂ ≠ u₃ := fun h => h23 (Subtype.ext (by rw [hu₂eq, hu₃eq, h]))
  have hsub : ({u₁, u₂, u₃} : Finset U) ⊆ F.neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> exact (F.mem_neighborFinset _ _).mpr (by assumption)
  have hc1 : u₁ ∉ ({u₂, u₃} : Finset U) := by simp [h12u, h13u]
  have hc2 : u₂ ∉ ({u₃} : Finset U) := by simp [h23u]
  have h3 : 3 ≤ F.degree v := by
    calc 3 = ({u₁, u₂, u₃} : Finset U).card := by
          rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
            Finset.card_singleton]
      _ ≤ (F.neighborFinset v).card := Finset.card_le_card hsub
      _ = F.degree v := F.card_neighborFinset_eq_degree v
  have := fd v
  omega

private noncomputable def traceEdges {U : Type*} (F : SimpleGraph U) :
    U → List F.edgeSet → List U
  | u, [] => [u]
  | u, e :: rest => u :: traceEdges F (otherVertex F e u) rest

private lemma traceEdges_length {U : Type*} (F : SimpleGraph U) (u : U) (es : List F.edgeSet) :
    (traceEdges F u es).length = es.length + 1 := by
  induction es generalizing u with
  | nil => simp [traceEdges]
  | cons e rest ih => simp [traceEdges, ih]

private lemma traceEdges_head {U : Type*} (F : SimpleGraph U) (u : U) (es : List F.edgeSet) :
    (traceEdges F u es)[0]'(by rw [traceEdges_length]; omega) = u := by
  cases es <;> rfl

private lemma traceEdges_spec {U : Type*} [Fintype U] (F : SimpleGraph U)
    (fd : ∀ v, F.degree v ≤ 2) :
    ∀ (es : List F.edgeSet) (u : U), es.Nodup →
    (∀ (h : es ≠ []), u ∈ (es[0]'(List.length_pos_of_ne_nil h)).val) →
    (∀ (h : 2 ≤ es.length), u ∉ es[1].val) →
    (∀ (i : ℕ) (hi : i + 1 < es.length), (LF F).Adj es[i] es[i + 1]) →
    ∀ (i : ℕ) (hi : i < es.length),
      es[i].val = s((traceEdges F u es)[i]'(by rw [traceEdges_length]; omega),
        (traceEdges F u es)[i + 1]'(by rw [traceEdges_length]; omega)) ∧
      F.Adj ((traceEdges F u es)[i]'(by rw [traceEdges_length]; omega))
        ((traceEdges F u es)[i + 1]'(by rw [traceEdges_length]; omega))
  | [], _, _, _, _, _, i, hi => by simp at hi
  | [e], u, _, hu0, _, _, i, hi => by
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    have hue : u ∈ e.val := hu0 (by simp)
    obtain ⟨hadj, heq⟩ := otherVertex_spec F e u hue
    simp only [traceEdges, List.getElem_cons_zero, List.getElem_cons_succ]
    exact ⟨heq, hadj⟩
  | e₀ :: e₁ :: rest, u, hnodup, hu0, hu1, hadj, i, hi => by
    have hue0 : u ∈ e₀.val := hu0 (by simp)
    have hun1 : u ∉ e₁.val := hu1 (by simp)
    obtain ⟨hadj0, heq0⟩ := otherVertex_spec F e₀ u hue0
    let w := otherVertex F e₀ u
    have hw_in_e1 : w ∈ e₁.val := by
      obtain ⟨_, y, hy0, hy1⟩ := hadj 0 (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hy0 hy1
      have hyw : y = w := sym2_mem_and_eq_other heq0 hy0 (fun h => hun1 (h ▸ hy1))
      exact hyw ▸ hy1
    have hw_not_e2 : ∀ (h2 : 2 ≤ (e₁ :: rest).length), w ∉ (e₁ :: rest)[1].val := by
      intro h2 hwin
      cases rest with
      | nil => simp at h2
      | cons e₂ rest' =>
        simp only [List.getElem_cons_succ] at hwin
        have hw0 : w ∈ e₀.val := by rw [heq0]; exact Sym2.mem_mk_right u w
        have hnodup0 := List.nodup_cons.mp hnodup
        have hnodup1 := List.nodup_cons.mp hnodup0.2
        have h01 : e₀ ≠ e₁ := fun h => hnodup0.1 (h ▸ List.mem_cons_self)
        have h02 : e₀ ≠ e₂ := fun h => hnodup0.1 (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
        have h12 : e₁ ≠ e₂ := fun h => hnodup1.1 (h ▸ List.mem_cons_self)
        exact three_edges_at_vertex_absurd F fd h01 h02 h12 hw0 hw_in_e1 hwin
    cases i with
    | zero =>
      simp only [traceEdges, List.getElem_cons_zero, List.getElem_cons_succ]
      exact ⟨heq0, hadj0⟩
    | succ j =>
      have hih := traceEdges_spec F fd (e₁ :: rest) w (List.nodup_cons.mp hnodup).2
        (fun _ => hw_in_e1) hw_not_e2 (fun k hk => hadj (k + 1) (by simpa using hk))
        j (by simpa using hi)
      simpa [traceEdges] using hih

private noncomputable def hTT {U : Type*} {F : SimpleGraph U} (t : U → Bool) (c : U → Fin 3)
    (e : F.edgeSet) : Fin 3 :=
  if h : (edgeAllowed c t e.val).Nonempty then Classical.choose h else 0

private lemma tt_edge_allowed_card_eq_one {U : Type*} (S F : SimpleGraph U) (t : U → Bool)
    (c : U → Fin 3)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (hcS : ∀ x y, S.Adj x y → c x ≠ c y)
    (e : F.edgeSet) (he : IsTT t e.val) :
    (edgeAllowed c t e.val).card = 1 ∧ hTT t c e ∈ edgeAllowed c t e.val := by
  have hemem := e.2
  have he_ex : ∃ u v : U, e.val = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e.val
  obtain ⟨u, v, hval⟩ := he_ex
  have huv : F.Adj u v := by simpa [hval] using hemem
  have htu : t u = true := he u (by rw [hval]; exact Sym2.mem_mk_left u v)
  have htv : t v = true := he v (by rw [hval]; exact Sym2.mem_mk_right u v)
  have hcuv : c u ≠ c v := hcS u v (inside u v huv htu htv)
  have heq : edgeAllowed c t e.val = (Finset.univ.erase (c u)).erase (c v) := by
    ext α
    simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, hval, Sym2.mem_iff]
    constructor
    · intro h
      exact ⟨h v htv (Or.inr rfl), h u htu (Or.inl rfl), trivial⟩
    · rintro ⟨hv, hu, _⟩ w _ (rfl | rfl)
      · exact hu
      · exact hv
  have hcard : (edgeAllowed c t e.val).card = 1 := by
    rw [heq, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hcuv.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin 3]
  have hne : (edgeAllowed c t e.val).Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  refine ⟨hcard, ?_⟩
  simp only [hTT, dif_pos hne]
  exact Classical.choose_spec hne

private lemma tt_edges_not_adj {U : Type*} (F : SimpleGraph U) (t : U → Bool)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    {e f : F.edgeSet} (he : IsTT t e.val) (hf : IsTT t f.val) : ¬ (LF F).Adj e f := by
  rintro ⟨hne, y, hye, hyf⟩
  obtain ⟨x, hxadj, hxeq⟩ := exists_otherEnd F e y hye
  obtain ⟨z, hzadj, hzeq⟩ := exists_otherEnd F f y hyf
  have hxz : x ≠ z := fun h => hne (Subtype.ext (by rw [hxeq, hzeq, h]))
  have htx : t x = true := he x (by rw [hxeq]; exact Sym2.mem_mk_right y x)
  have hty : t y = true := he y hye
  have htz : t z = true := hf z (by rw [hzeq]; exact Sym2.mem_mk_right y z)
  exact three x y z hxz hxadj.symm hzadj ⟨htx, hty, htz⟩

private lemma non_tt_edge_card_ge_two {U : Type*} {F : SimpleGraph U} (t : U → Bool) (c : U → Fin 3)
    (e : F.edgeSet) (he : ¬ IsTT t e.val) : 2 ≤ (edgeAllowed c t e.val).card := by
  have he_ex : ∃ u v : U, e.val = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e.val
  obtain ⟨u, v, hval⟩ := he_ex
  have huv_false : t u = false ∨ t v = false := by
    by_contra h
    push Not at h
    apply he
    intro w hw
    rw [hval, Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · exact Bool.eq_true_of_not_eq_false h.1
    · exact Bool.eq_true_of_not_eq_false h.2
  rcases huv_false with hu | hv
  · have hsub : Finset.univ.erase (c v) ⊆ edgeAllowed c t e.val := by
      intro α hα
      simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and, hval, Sym2.mem_iff]
      rintro w htw (rfl | rfl)
      · rw [hu] at htw; cases htw
      · exact (Finset.mem_erase.mp hα).1
    have hc : (Finset.univ.erase (c v)).card = 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin 3]
    exact hc.symm.le.trans (Finset.card_le_card hsub)
  · have hsub : Finset.univ.erase (c u) ⊆ edgeAllowed c t e.val := by
      intro α hα
      simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and, hval, Sym2.mem_iff]
      rintro w htw (rfl | rfl)
      · exact (Finset.mem_erase.mp hα).1
      · rw [hv] at htw; cases htw
    have hc : (Finset.univ.erase (c u)).card = 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin 3]
    exact hc.symm.le.trans (Finset.card_le_card hsub)

private lemma non_tt_at_most_one_tt_neighbor {U : Type*} (F : SimpleGraph U) (t : U → Bool)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    {e f₁ f₂ : F.edgeSet} (he : ¬ IsTT t e.val)
    (hf₁ : IsTT t f₁.val) (hf₂ : IsTT t f₂.val)
    (ha₁ : (LF F).Adj e f₁) (ha₂ : (LF F).Adj e f₂) : f₁ = f₂ := by
  obtain ⟨_, w₁, hw₁e, hw₁f⟩ := ha₁
  obtain ⟨_, w₂, hw₂e, hw₂f⟩ := ha₂
  have htw₁ : t w₁ = true := hf₁ w₁ hw₁f
  have htw₂ : t w₂ = true := hf₂ w₂ hw₂f
  have hw_eq : w₁ = w₂ := by
    by_contra hne
    apply he
    intro z hz
    induction hval : e.val using Sym2.ind with
    | _ a b =>
      rw [hval, Sym2.mem_iff] at hw₁e hw₂e hz
      rcases hw₁e with rfl | rfl <;> rcases hw₂e with rfl | rfl
      · exact absurd rfl hne
      · rcases hz with rfl | rfl <;> assumption
      · rcases hz with rfl | rfl <;> assumption
      · exact absurd rfl hne
  by_contra hfne
  exact tt_edges_not_adj F t three hf₁ hf₂ ⟨hfne, w₁, hw₁f, hw_eq ▸ hw₂f⟩

private lemma erase_hTT_mem_other {U : Type*} (S F : SimpleGraph U) (t : U → Bool)
    (c : U → Fin 3)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (hcS : ∀ x y, S.Adj x y → c x ≠ c y)
    {e f : F.edgeSet} (he : ¬ IsTT t e.val) (hf : IsTT t f.val)
    {w u : U} (hfwu : f.val = s(w, u)) (hue : u ∈ e.val) :
    c w ∈ (edgeAllowed c t e.val).erase (hTT t c f) ∧
    ∀ α ∈ (edgeAllowed c t e.val).erase (hTT t c f), α = c w := by
  have hwu_adj : F.Adj w u := by simpa [hfwu] using f.2
  have htw : t w = true := hf w (by rw [hfwu]; exact Sym2.mem_mk_left w u)
  have htu : t u = true := hf u (by rw [hfwu]; exact Sym2.mem_mk_right w u)
  have hcwu : c w ≠ c u := hcS w u (inside w u hwu_adj htw htu)
  have htt := (tt_edge_allowed_card_eq_one S F t c inside hcS f hf).2
  simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and] at htt
  have hne_w : hTT t c f ≠ c w := htt w htw (by rw [hfwu]; exact Sym2.mem_mk_left w u)
  have hne_u : hTT t c f ≠ c u := htt u htu (by rw [hfwu]; exact Sym2.mem_mk_right w u)
  obtain ⟨v, _, heuv⟩ := exists_otherEnd F e u hue
  have htv : t v = false := by
    by_contra h
    have htv' : t v = true := by cases hv : t v <;> simp_all
    apply he
    intro z hz
    rw [heuv, Sym2.mem_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  have he_eq : edgeAllowed c t e.val = Finset.univ.erase (c u) := by
    ext α
    simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, heuv, Sym2.mem_iff]
    constructor
    · intro h; exact ⟨h u htu (Or.inl rfl), trivial⟩
    · rintro ⟨hα, _⟩ z htz (rfl | rfl)
      · exact hα
      · rw [htv] at htz; cases htz
  constructor
  · rw [he_eq]
    exact Finset.mem_erase.mpr ⟨hne_w.symm, Finset.mem_erase.mpr ⟨hcwu, Finset.mem_univ _⟩⟩
  · intro α hα
    rw [he_eq] at hα
    have h1 := (Finset.mem_erase.mp hα).1
    have h2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hα).2).1
    generalize hcw : c w = x at h1 hcwu
    generalize hcu : c u = y at h2 hcwu
    generalize htf : hTT t c f = z at h1 h2
    fin_cases α <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all

private noncomputable def L_avoid {U : Type*} {F : SimpleGraph U} (t : U → Bool)
    (c : U → Fin 3) (e : F.edgeSet) : Finset (Fin 3) :=
  (edgeAllowed c t e.val).filter (fun α =>
    ∀ f : F.edgeSet, IsTT t f.val → (LF F).Adj e f → α ≠ hTT t c f)

private lemma l_avoid_sub {U : Type*} {F : SimpleGraph U} (t : U → Bool) (c : U → Fin 3)
    (e : F.edgeSet) (α : Fin 3) (h : α ∈ L_avoid t c e) : α ∈ edgeAllowed c t e.val :=
  (Finset.mem_filter.mp h).1

private lemma l_avoid_tt {U : Type*} {F : SimpleGraph U} (t : U → Bool) (c : U → Fin 3)
    (e : F.edgeSet) (α : Fin 3) (h : α ∈ L_avoid t c e)
    (f : F.edgeSet) (hf : IsTT t f.val) (ha : (LF F).Adj e f) : α ≠ hTT t c f :=
  (Finset.mem_filter.mp h).2 f hf ha

private lemma l_avoid_card_ge_one {U : Type*} (F : SimpleGraph U) (t : U → Bool)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (c : U → Fin 3) (e : F.edgeSet) (he : ¬ IsTT t e.val) :
    1 ≤ (L_avoid t c e).card := by
  by_cases hex : ∃ f : F.edgeSet, IsTT t f.val ∧ (LF F).Adj e f
  · obtain ⟨f₀, hf₀, ha₀⟩ := hex
    have hsub : (edgeAllowed c t e.val).erase (hTT t c f₀) ⊆ L_avoid t c e := by
      intro α hα
      refine Finset.mem_filter.mpr ⟨Finset.erase_subset _ _ hα, fun f hf ha => ?_⟩
      have hfeq := non_tt_at_most_one_tt_neighbor F t three he hf₀ hf ha₀ ha
      subst hfeq
      exact (Finset.mem_erase.mp hα).1
    have h2 := non_tt_edge_card_ge_two t c e he
    have h1 : 1 ≤ ((edgeAllowed c t e.val).erase (hTT t c f₀)).card := by
      have := Finset.pred_card_le_card_erase (s := edgeAllowed c t e.val) (a := hTT t c f₀)
      omega
    exact h1.trans (Finset.card_le_card hsub)
  · push Not at hex
    have heq : L_avoid t c e = edgeAllowed c t e.val := by
      ext α
      simp only [L_avoid, Finset.mem_filter, and_iff_left_iff_imp]
      intro _ f hf ha
      exact absurd ha (hex f hf)
    rw [heq]
    exact Nat.le_trans (by decide) (non_tt_edge_card_ge_two t c e he)

private lemma no_tt_deg2_lf {U : Type*} [Fintype U] (F : SimpleGraph U) (t : U → Bool)
    (fd : ∀ v, F.degree v ≤ 2) {e e₁ e₂ : F.edgeSet} (h12 : e₁ ≠ e₂)
    (ha₁ : (LF F).Adj e e₁) (ha₂ : (LF F).Adj e e₂) (hn₁ : ¬ IsTT t e₁.val) (hn₂ : ¬ IsTT t e₂.val) :
    ∀ f : F.edgeSet, IsTT t f.val → ¬ (LF F).Adj e f := by
  intro f hf haf
  have hf1 : f ≠ e₁ := fun h => hn₁ (h ▸ hf)
  have hf2 : f ≠ e₂ := fun h => hn₂ (h ▸ hf)
  have hsub : ({e₁, e₂, f} : Finset F.edgeSet) ⊆ (LF F).neighborFinset e := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> exact ((LF F).mem_neighborFinset _ _).mpr (by assumption)
  have hc1 : e₁ ∉ ({e₂, f} : Finset F.edgeSet) := by simp [h12, hf1.symm]
  have hc2 : e₂ ∉ ({f} : Finset F.edgeSet) := by simp [hf2.symm]
  have h3 : 3 ≤ (LF F).degree e := by
    calc 3 = ({e₁, e₂, f} : Finset F.edgeSet).card := by
          rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
            Finset.card_singleton]
      _ ≤ ((LF F).neighborFinset e).card := Finset.card_le_card hsub
      _ = (LF F).degree e := (LF F).card_neighborFinset_eq_degree e
  have := LF_degree_le_two F fd e
  omega

private lemma color_E'_cycle {U : Type*} [Fintype U] (F : SimpleGraph U) (t : U → Bool)
    (fd : ∀ v, F.degree v ≤ 2)
    (c : U → Fin 3)
    (es : List F.edgeSet) (hnodup : es.Nodup) (hlen3 : 3 ≤ es.length)
    (hnonTT : ∀ e ∈ es, ¬ IsTT t e.val)
    (hcadj : ∀ (i : Fin es.length),
      (LF F).Adj es[i.val] (es[(i.val + 1) % es.length]'(Nat.mod_lt _ (Fin.pos i)))) :
    ∃ h : F.edgeSet → Fin 3,
      (∀ e ∈ es, h e ∈ edgeAllowed c t e.val) ∧
      (∀ e ∈ es, ∀ f : F.edgeSet, IsTT t f.val → (LF F).Adj e f → h e ≠ hTT t c f) ∧
      (∀ e ∈ es, ∀ f ∈ es, (LF F).Adj e f → h e ≠ h f) := by
    have hno_tt : ∀ e ∈ es, ∀ f : F.edgeSet, IsTT t f.val → ¬ (LF F).Adj e f := by
      intro e he f hf
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      let sIdx := (i + 1) % es.length
      let pIdx := (i + es.length - 1) % es.length
      have hp_succ : (pIdx + 1) % es.length = i := by
        dsimp [pIdx]
        rw [Nat.mod_add_mod]
        by_cases hi0 : i = 0
        · simp only [hi0, Nat.zero_add]
          have h1 : es.length - 1 + 1 = es.length := by omega
          rw [h1, Nat.mod_self]
        · have h1 : i + es.length - 1 + 1 = i + es.length := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      have ha1 : (LF F).Adj es[i] (es[sIdx]'(Nat.mod_lt _ (by omega))) := hcadj ⟨i, hi⟩
      have ha2 : (LF F).Adj es[i] (es[pIdx]'(Nat.mod_lt _ (by omega))) := by
        have h := (hcadj ⟨pIdx, Nat.mod_lt _ (by omega)⟩).symm
        dsimp at h
        have hidx : es[(pIdx + 1) % es.length]'(Nat.mod_lt _ (by omega)) = es[i] := by congr 1
        rwa [hidx] at h
      have hsp_idx : sIdx ≠ pIdx := by
        dsimp [sIdx, pIdx]
        by_cases hi0 : i = 0
        · simp only [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < es.length),
            Nat.mod_eq_of_lt (by omega : es.length - 1 < es.length)]
          omega
        · have h1 : i + es.length - 1 = (i - 1) + es.length := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i - 1 < es.length)]
          by_cases hil : i + 1 < es.length
          · rw [Nat.mod_eq_of_lt hil]; omega
          · have : i + 1 = es.length := by omega
            rw [this, Nat.mod_self]; omega
      have hne12 : es[sIdx]'(Nat.mod_lt _ (by omega)) ≠ es[pIdx]'(Nat.mod_lt _ (by omega)) :=
        fun h => hsp_idx (hnodup.getElem_inj_iff.mp h)
      exact no_tt_deg2_lf F t fd hne12 ha1 ha2
        (hnonTT _ (List.getElem_mem _)) (hnonTT _ (List.getElem_mem _)) f hf
    have hcyc_prop : ∀ h : F.edgeSet → Fin 3,
        (∀ i : Fin es.length, h es[i.val] ≠ h (es[(i.val + 1) % es.length]'(Nat.mod_lt _ (Fin.pos i)))) →
        ∀ e ∈ es, ∀ f ∈ es, (LF F).Adj e f → h e ≠ h f := by
      intro h hadj_c e he f hf hadj
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
      rcases sg_cycle_adj_iff (LF F) (LF_degree_le_two F fd) hnodup hlen3 hcadj hi hj hadj with
        hjs | his
      · subst hjs; exact hadj_c ⟨i, hi⟩
      · have := (hadj_c ⟨j, hj⟩).symm
        have hidx : es[(j + 1) % es.length]'(Nat.mod_lt _ (Fin.pos ⟨j, hj⟩)) = es[i] := by
          congr 1; exact his.symm
        rwa [hidx] at this
    by_cases h3 : ∃ i : Fin es.length, (edgeAllowed c t es[i.val].val).card = 3
    · obtain ⟨i₀, hi₀⟩ := h3
      let r := (i₀.val + 1) % es.length
      let es' := es.rotate r
      have hlen' : es'.length = es.length := by simp [es']
      have hnodup' : es'.Nodup := List.nodup_rotate.mpr hnodup
      let p := es'.dropLast
      have hplen : p.length = es.length - 1 := by simp [p, es']
      have hpnodup : p.Nodup := hnodup'.sublist (List.dropLast_sublist _)
      have h1p : ∀ k (hk : k < p.length), 1 ≤ (edgeAllowed c t p[k].val).card := fun k hk =>
        Nat.le_trans (by decide) (non_tt_edge_card_ge_two t c p[k]
          (hnonTT _ (List.mem_rotate.mp ((List.dropLast_sublist _).mem (List.getElem_mem hk)))))
      have h2p : ∀ k (hk : k + 1 < p.length), 2 ≤ (edgeAllowed c t p[k + 1].val).card := fun k hk =>
        non_tt_edge_card_ge_two t c p[k + 1]
          (hnonTT _ (List.mem_rotate.mp ((List.dropLast_sublist _).mem (List.getElem_mem hk))))
      obtain ⟨h', hh'L, hh'adj⟩ := list_color_path p (fun e => edgeAllowed c t e.val)
        hpnodup h1p h2p
      let used : Finset (Fin 3) := {h' (p[0]'(by omega)), h' (p[p.length - 1]'(by omega))}
      have hcard_lt : used.card < (Finset.univ : Finset (Fin 3)).card := by
        calc used.card ≤ 2 := Finset.card_le_two
          _ < 3 := by decide
          _ = (Finset.univ : Finset (Fin 3)).card := by rw [Finset.card_univ, Fintype.card_fin 3]
      obtain ⟨α, _, hαnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
      have hα_mem : α ∈ edgeAllowed c t es[i₀.val].val := by
        have huniv : edgeAllowed c t es[i₀.val].val = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [hi₀, Fintype.card_fin 3])
        rw [huniv]; exact Finset.mem_univ α
      have hr_lt : r < es.length := Nat.mod_lt _ (by omega)
      have hlast_eq : es'[es'.length - 1]'(by omega) = es[i₀.val] := by
        simp only [es', List.getElem_rotate, hlen']
        congr 1
        by_cases hilast : i₀.val + 1 < es.length
        · have hr : r = i₀.val + 1 := Nat.mod_eq_of_lt hilast
          rw [hr]
          have hsum : es.length - 1 + (i₀.val + 1) = i₀.val + es.length := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i₀.isLt]
        · have hieq : i₀.val = es.length - 1 := by omega
          have hr : r = 0 := by
            dsimp [r]; rw [hieq]
            have h1 : es.length - 1 + 1 = es.length := by omega
            rw [h1, Nat.mod_self]
          rw [hr, Nat.add_zero, Nat.mod_eq_of_lt (by omega), hieq]
      let h : F.edgeSet → Fin 3 := fun e => if e = es[i₀.val] then α else h' e
      refine ⟨h, fun e he => ?_, fun e he f hf ha => absurd ha (hno_tt e he f hf),
        hcyc_prop h (fun k => ?_)⟩
      · dsimp [h]
        split_ifs with heq
        · subst heq; exact hα_mem
        · have hmem' : e ∈ es' := List.mem_rotate.mpr he
          have hmem_p : e ∈ p := by
            obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hmem'
            have hlt : idx < es'.length - 1 := by
              by_contra hge
              have hieq : idx = es'.length - 1 := by omega
              apply heq
              rw [← hlast_eq]; congr 1
            have : es'[idx]'hidx = p[idx]'(by rw [hplen, ← hlen']; exact hlt) := by
              simp [p, List.getElem_dropLast]
            rw [this]; exact List.getElem_mem _
          exact hh'L e hmem_p
      · -- Check cyclic adjacency for h
        have hrot_id : ∀ (a : ℕ) (ha : a < es.length),
            es'[((a + es.length - r) % es.length)]'(by rw [hlen']; exact Nat.mod_lt _ (by omega)) =
            es[a] := by
          intro a ha
          simp only [es', List.getElem_rotate]
          congr 1
          rw [Nat.mod_add_mod]
          have hsum : a + es.length - r + r = a + es.length := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
        let j0 : ℕ := (k.val + es.length - r) % es.length
        have hj0_lt : j0 < es'.length := by rw [hlen']; exact Nat.mod_lt _ (Fin.pos k)
        have he0 : es[k.val] = es'[j0]'hj0_lt := (hrot_id k.val k.isLt).symm
        have hj1_eq : (j0 + 1) % es'.length = ((k.val + 1) % es.length + es.length - r) % es.length := by
          rw [hlen']; dsimp [j0]; rw [Nat.mod_add_mod]
          by_cases hk1 : k.val + 1 < es.length
          · rw [Nat.mod_eq_of_lt hk1]; congr 1; omega
          · have hkeq : k.val + 1 = es.length := by omega
            rw [hkeq, Nat.mod_self, Nat.zero_add]
            have h1 : k.val + es.length - r + 1 = (es.length - r) + es.length := by omega
            rw [h1, Nat.add_mod_right]
        have he1 : es[(k.val + 1) % es.length]'(Nat.mod_lt _ (Fin.pos k)) =
            es'[(j0 + 1) % es'.length]'(Nat.mod_lt _ (by omega)) := by
          have := hrot_id ((k.val + 1) % es.length) (Nat.mod_lt _ (Fin.pos k))
          rw [← this]; congr 1; exact hj1_eq.symm
        rw [he0, he1]
        by_cases hjlast : j0 = es'.length - 1
        · have hj1_0 : (j0 + 1) % es'.length = 0 := by
            have h1 : j0 + 1 = es'.length := by omega
            rw [h1, Nat.mod_self]
          have hA : es'[j0]'hj0_lt = es[i₀.val] := by
            rw [← hlast_eq]; congr 1
          have hB : es'[(j0 + 1) % es'.length]'(Nat.mod_lt _ (by omega)) = p[0]'(by omega) := by
            have : es'[(j0 + 1) % es'.length]'(Nat.mod_lt _ (by omega)) = es'[0]'(by omega) := by
              congr 1
            rw [this]; simp [p, List.getElem_dropLast]
          have hB_ne : p[0]'(by omega) ≠ es[i₀.val] := by
            rw [← hlast_eq]
            have : p[0]'(by omega) = es'[0]'(by omega) := by simp [p, List.getElem_dropLast]
            rw [this]; intro h; have := hnodup'.getElem_inj_iff.mp h; omega
          rw [hA, hB]
          dsimp [h]
          rw [if_pos rfl, if_neg hB_ne]
          intro heq
          apply hαnot
          rw [heq]
          exact Finset.mem_insert_self _ _
        · by_cases hjprev : j0 = es'.length - 2
          · have hj1_last : (j0 + 1) % es'.length = es'.length - 1 := by
              rw [Nat.mod_eq_of_lt (by omega)]; omega
            have hA : es'[j0]'hj0_lt = p[p.length - 1]'(by omega) := by
              simp [p, List.getElem_dropLast, hplen]; congr 1; omega
            have hB : es'[(j0 + 1) % es'.length]'(Nat.mod_lt _ (by omega)) = es[i₀.val] := by
              rw [← hlast_eq]; congr 1
            have hA_ne : p[p.length - 1]'(by omega) ≠ es[i₀.val] := by
              rw [← hlast_eq]
              have : p[p.length - 1]'(by omega) = es'[es'.length - 2]'(by omega) := by
                simp [p, List.getElem_dropLast, hplen, hlen']; congr 1
              rw [this]; intro h; have := hnodup'.getElem_inj_iff.mp h; omega
            rw [hA, hB]
            dsimp [h]
            rw [if_neg hA_ne, if_pos rfl]
            intro heq
            apply hαnot
            rw [← heq]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · have hj1_lt : j0 + 1 < es'.length - 1 := by omega
            have hj_mod : (j0 + 1) % es'.length = j0 + 1 := Nat.mod_eq_of_lt (by omega)
            have hA : es'[j0]'hj0_lt = p[j0]'(by rw [hplen, ← hlen']; omega) := by
              simp [p, List.getElem_dropLast]
            have hB : es'[(j0 + 1) % es'.length]'(Nat.mod_lt _ (by omega)) =
                p[j0 + 1]'(by rw [hplen, ← hlen']; omega) := by
              have : es'[(j0 + 1) % es'.length]'(Nat.mod_lt _ (by omega)) =
                  es'[j0 + 1]'(by omega) := by congr 1
              rw [this]; simp [p, List.getElem_dropLast]
            have hA_ne : p[j0]'(by rw [hplen, ← hlen']; omega) ≠ es[i₀.val] := by
              rw [← hlast_eq]
              have : p[j0]'(by rw [hplen, ← hlen']; omega) = es'[j0]'hj0_lt := by
                simp [p, List.getElem_dropLast]
              rw [this]; intro h; have := hnodup'.getElem_inj_iff.mp h; omega
            have hB_ne : p[j0 + 1]'(by rw [hplen, ← hlen']; omega) ≠ es[i₀.val] := by
              rw [← hlast_eq]
              have : p[j0 + 1]'(by rw [hplen, ← hlen']; omega) = es'[j0 + 1]'(by omega) := by
                simp [p, List.getElem_dropLast]
              rw [this]; intro h; have := hnodup'.getElem_inj_iff.mp h; omega
            rw [hA, hB]
            dsimp [h]
            rw [if_neg hA_ne, if_neg hB_ne]
            exact hh'adj j0 (by rw [hplen, ← hlen']; omega)
    · -- All edges in es have card = 2 -> es.length is even -> list_color_even_cycle
      push Not at h3
      have hcard2 : ∀ e ∈ es, (edgeAllowed c t e.val).card = 2 := by
        intro e he
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
        have hge := non_tt_edge_card_ge_two t c es[i] (hnonTT _ he)
        have hle : (edgeAllowed c t es[i].val).card ≤ 3 :=
          (Finset.card_le_univ _).trans (by rw [Fintype.card_fin 3])
        have hne3 := h3 ⟨i, hi⟩
        dsimp at hne3
        omega
      let z : Fin es.length → U := fun i =>
        Classical.choose (hcadj ⟨(i.val + es.length - 1) % es.length, Nat.mod_lt _ (Fin.pos i)⟩).2
      have hz_mem_prev : ∀ i : Fin es.length,
          z i ∈ (es[(i.val + es.length - 1) % es.length]'(Nat.mod_lt _ (Fin.pos i))).val :=
        fun i => (Classical.choose_spec
          (hcadj ⟨(i.val + es.length - 1) % es.length, Nat.mod_lt _ (Fin.pos i)⟩).2).1
      have hz_mem_curr : ∀ i : Fin es.length, z i ∈ es[i.val].val := by
        intro i
        have h := (Classical.choose_spec
          (hcadj ⟨(i.val + es.length - 1) % es.length, Nat.mod_lt _ (Fin.pos i)⟩).2).2
        have hp_succ : (((i.val + es.length - 1) % es.length) + 1) % es.length = i.val := by
          rw [Nat.mod_add_mod]
          by_cases hi0 : i.val = 0
          · simp only [hi0, Nat.zero_add]
            have h1 : es.length - 1 + 1 = es.length := by omega
            rw [h1, Nat.mod_self]
          · have h1 : i.val + es.length - 1 + 1 = i.val + es.length := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
        refine Eq.mp (congrArg (fun e : F.edgeSet => z i ∈ e.val) ?_) h
        congr 2
      have hz_ne_next : ∀ i : Fin es.length,
          z i ≠ z ⟨(i.val + 1) % es.length, Nat.mod_lt _ (Fin.pos i)⟩ := by
        intro i heq
        let pIdx := (i.val + es.length - 1) % es.length
        let sIdx := (i.val + 1) % es.length
        have hp_lt : pIdx < es.length := Nat.mod_lt _ (Fin.pos i)
        have hs_lt : sIdx < es.length := Nat.mod_lt _ (Fin.pos i)
        have hm1 : z i ∈ (es[pIdx]'hp_lt).val := hz_mem_prev i
        have hm2 : z i ∈ es[i.val].val := hz_mem_curr i
        have hm3 : z i ∈ (es[sIdx]'hs_lt).val := by
          rw [heq]; exact hz_mem_curr ⟨sIdx, hs_lt⟩
        have hpi : pIdx ≠ i.val := by
          dsimp [pIdx]
          by_cases hi0 : i.val = 0
          · simp only [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : es.length - 1 < es.length)]
            omega
          · have h1 : i.val + es.length - 1 = (i.val - 1) + es.length := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - 1 < es.length)]; omega
        have his : i.val ≠ sIdx := by
          dsimp [sIdx]
          by_cases hil : i.val + 1 < es.length
          · rw [Nat.mod_eq_of_lt hil]; omega
          · have : i.val + 1 = es.length := by omega
            rw [this, Nat.mod_self]; omega
        have hps : pIdx ≠ sIdx := by
          dsimp [pIdx, sIdx]
          by_cases hi0 : i.val = 0
          · simp only [hi0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < es.length),
              Nat.mod_eq_of_lt (by omega : es.length - 1 < es.length)]
            omega
          · have h1 : i.val + es.length - 1 = (i.val - 1) + es.length := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i.val - 1 < es.length)]
            by_cases hil : i.val + 1 < es.length
            · rw [Nat.mod_eq_of_lt hil]; omega
            · have : i.val + 1 = es.length := by omega
              rw [this, Nat.mod_self]; omega
        exact three_edges_at_vertex_absurd F fd
          (fun h => hpi (hnodup.getElem_inj_iff.mp h))
          (fun h => hps (hnodup.getElem_inj_iff.mp h))
          (fun h => his (hnodup.getElem_inj_iff.mp h))
          hm1 hm2 hm3
      have hz_flip : ∀ i : Fin es.length,
          t (z ⟨(i.val + 1) % es.length, Nat.mod_lt _ (Fin.pos i)⟩) = !(t (z i)) := by
        intro i
        let j : Fin es.length := ⟨(i.val + 1) % es.length, Nat.mod_lt _ (Fin.pos i)⟩
        have h1 : z i ∈ es[i.val].val := hz_mem_curr i
        have h2 : z j ∈ es[i.val].val := by
          have hj := hz_mem_prev j
          have hidx_eq : (j.val + es.length - 1) % es.length = i.val := by
            dsimp [j]
            have hadd : (i.val + 1) % es.length + es.length - 1 =
                (i.val + 1) % es.length + (es.length - 1) := by omega
            rw [hadd, Nat.mod_add_mod]
            have hsum : i.val + 1 + (es.length - 1) = i.val + es.length := by omega
            rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
          have hcongr : (es[(j.val + es.length - 1) % es.length]'(Nat.mod_lt _ (Fin.pos j))).val =
              es[i.val].val := by congr 2
          rwa [hcongr] at hj
        have hne_zij : z i ≠ z j := hz_ne_next i
        have he_eq : es[i.val].val = s(z i, z j) := by
          obtain ⟨w, _, hw⟩ := exists_otherEnd F es[i.val] (z i) h1
          have hw_eq := sym2_mem_and_eq_other hw h2 hne_zij.symm
          rwa [← hw_eq] at hw
        by_cases hti : t (z i) = true <;> by_cases htj : t (z j) = true
        · exfalso
          apply hnonTT _ (List.getElem_mem _)
          intro w hw
          rw [he_eq, Sym2.mem_iff] at hw
          rcases hw with rfl | rfl <;> assumption
        · have htj' : t (z j) = false := Bool.eq_false_iff.mpr htj
          rw [hti, htj']; rfl
        · have hti' : t (z i) = false := Bool.eq_false_iff.mpr hti
          rw [hti', htj]; rfl
        · exfalso
          have hti' : t (z i) = false := Bool.eq_false_iff.mpr hti
          have htj' : t (z j) = false := Bool.eq_false_iff.mpr htj
          have huniv : edgeAllowed c t es[i.val].val = Finset.univ := by
            ext α
            simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and, iff_true,
              he_eq, Sym2.mem_iff]
            rintro w htw (rfl | rfl)
            · rw [hti'] at htw; cases htw
            · rw [htj'] at htw; cases htw
          have hc3 := hcard2 _ (List.getElem_mem i.isLt)
          rw [huniv, Finset.card_univ, Fintype.card_fin 3] at hc3
          omega
      have hz_pow : ∀ k : ℕ,
          t (z ⟨k % es.length, Nat.mod_lt _ (by omega)⟩) =
          if k % 2 = 0 then t (z ⟨0, by omega⟩) else !(t (z ⟨0, by omega⟩)) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hstep := hz_flip ⟨k % es.length, Nat.mod_lt _ (by omega)⟩
          have hidx_eq : ((k % es.length + 1) % es.length) = (k + 1) % es.length := by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have hcongr : z ⟨(k % es.length + 1) % es.length, Nat.mod_lt _ (by omega)⟩ =
              z ⟨(k + 1) % es.length, Nat.mod_lt _ (by omega)⟩ :=
            congrArg z (Fin.ext hidx_eq)
          rw [hcongr] at hstep
          rw [hstep, ih]
          by_cases hk2 : k % 2 = 0
          · have hk12 : (k + 1) % 2 ≠ 0 := by omega
            simp [hk2, hk12]
          · have hk12 : (k + 1) % 2 = 0 := by omega
            simp [hk2, hk12]
      have heven : es.length % 2 = 0 := by
        have h := hz_pow es.length
        have hmod : es.length % es.length = 0 := Nat.mod_self _
        have hcongr : z ⟨es.length % es.length, Nat.mod_lt _ (by omega)⟩ = z ⟨0, by omega⟩ :=
          congrArg z (Fin.ext hmod)
        rw [hcongr] at h
        by_contra hodd
        rw [if_neg hodd] at h
        generalize hz0 : t (z ⟨0, by omega⟩) = b at h
        cases b <;> cases h
      let m := es.length / 2
      have hm : 1 ≤ m := by have hlen3' := hlen3; dsimp [m]; omega
      have hlen_m : es.length = 2 * m := by omega
      obtain ⟨h, hhL, hhadj⟩ := list_color_even_cycle es (fun e => edgeAllowed c t e.val)
        hnodup m hm hlen_m hcard2
      exact ⟨h, hhL, fun e he f hf ha => absurd ha (hno_tt e he f hf), hcyc_prop h hhadj⟩

private lemma color_E'_path {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (fd : ∀ v, F.degree v ≤ 2)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (c : U → Fin 3) (hcS : ∀ x y, S.Adj x y → c x ≠ c y)
    (halt : ∀ (u v v' u' : U) (w : AltWalk F t u v v' u'),
      c u ≠ c u' ∨ ∃ (_ : 2 ≤ w.m),
        c (w.zs[2]'(by have := w.hlen; omega)) = c u ∨
        c (w.zs[2 * w.m - 2]'(by have := w.hlen; omega)) = c u')
    (es : List F.edgeSet) (hnodup : es.Nodup) (hne : es ≠ [])
    (hnonTT : ∀ e ∈ es, ¬ IsTT t e.val)
    (hpadj : ∀ (i : ℕ) (hi : i + 1 < es.length), (LF F).Adj es[i] es[i + 1])
    (hpno : ∀ (i j : ℕ) (hi : i < j) (hj : j < es.length), (LF F).Adj es[i] es[j] → i + 1 = j) :
    ∃ h : F.edgeSet → Fin 3,
      (∀ e ∈ es, h e ∈ edgeAllowed c t e.val) ∧
      (∀ e ∈ es, ∀ f : F.edgeSet, IsTT t f.val → (LF F).Adj e f → h e ≠ hTT t c f) ∧
      (∀ e ∈ es, ∀ f ∈ es, (LF F).Adj e f → h e ≠ h f) := by
    let Lav := @L_avoid U F t c
    have hLav_sub := @l_avoid_sub U F t c
    have hLav_tt := @l_avoid_tt U F t c
    have hLav_card1 : ∀ e ∈ es, 1 ≤ (Lav e).card := fun e he =>
      l_avoid_card_ge_one F t three c e (hnonTT e he)
    have hpath_prop : ∀ h : F.edgeSet → Fin 3,
        (∀ i (hi : i + 1 < es.length), h es[i] ≠ h es[i + 1]) →
        ∀ e ∈ es, ∀ f ∈ es, (LF F).Adj e f → h e ≠ h f := by
      intro h hadj_p e he f hf hadj
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
      rcases Nat.lt_trichotomy i j with hij | rfl | hji
      · have heq := hpno i j hij hj hadj
        subst heq; exact hadj_p i hj
      · exact absurd hadj ((LF F).loopless.irrefl _)
      · have heq := hpno j i hji hi hadj.symm
        subst heq; exact (hadj_p j hi).symm
    have hLav_internal : ∀ (i : ℕ) (hi0 : 0 < i) (hi1 : i + 1 < es.length),
        2 ≤ (Lav es[i]).card := by
      intro i hi0 hi1
      have hne12 : es[i - 1] ≠ es[i + 1] := fun h => by
        have := hnodup.getElem_inj_iff.mp h; omega
      have ha1 : (LF F).Adj es[i] es[i - 1] := by
        have h := (hpadj (i - 1) (by omega)).symm
        have hidx : i - 1 + 1 = i := by omega
        have hcongr : es[i - 1 + 1] = es[i] := by congr 1
        rwa [hcongr] at h
      have ha2 : (LF F).Adj es[i] es[i + 1] := hpadj i hi1
      have hnott := no_tt_deg2_lf F t fd hne12 ha1 ha2
        (hnonTT _ (List.getElem_mem _)) (hnonTT _ (List.getElem_mem _))
      have heq : Lav es[i] = edgeAllowed c t es[i].val := by
        ext α
        simp only [Lav, L_avoid, Finset.mem_filter, and_iff_left_iff_imp]
        intro _ f hf ha
        exact absurd ha (hnott f hf)
      rw [heq]
      exact non_tt_edge_card_ge_two t c es[i] (hnonTT _ (List.getElem_mem _))
    by_cases hlen1 : es.length = 1
    · obtain ⟨α, hα⟩ := Finset.card_pos.mp (hLav_card1 (es[0]'(by omega)) (List.getElem_mem _))
      refine ⟨fun _ => α, fun e he => hLav_sub e α ?_,
        fun e he f hf ha => ?_, hpath_prop (fun _ => α) (fun _ hi => by omega)⟩
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
        have hi0 : i = 0 := by omega
        subst hi0; exact hα
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
        have hi0 : i = 0 := by omega
        subst hi0; exact hLav_tt _ α hα f hf ha
    · have hlen2 : 2 ≤ es.length := by
        have hpos : 0 < es.length := List.length_pos_of_ne_nil hne
        omega
      by_cases hex_end : ∃ f : F.edgeSet, IsTT t f.val ∧ (LF F).Adj (es[es.length - 1]'(by omega)) f
      swap
      · have h2p : ∀ i (hi : i + 1 < es.length), 2 ≤ (Lav es[i + 1]).card := by
          intro i hi
          by_cases hilast : i + 1 + 1 < es.length
          · exact hLav_internal (i + 1) (by omega) hilast
          · have hieq : i + 1 = es.length - 1 := by omega
            have hcongr : es[i + 1] = es[es.length - 1]'(by omega) := by congr 1
            rw [hcongr]
            have heq : Lav (es[es.length - 1]'(by omega)) =
                edgeAllowed c t (es[es.length - 1]'(by omega)).val := by
              ext α
              simp only [Lav, L_avoid, Finset.mem_filter, and_iff_left_iff_imp]
              intro _ f hf ha
              exact absurd ⟨f, hf, ha⟩ hex_end
            rw [heq]
            exact non_tt_edge_card_ge_two t c _ (hnonTT _ (List.getElem_mem _))
        obtain ⟨h, hhL, hhadj⟩ := list_color_path es Lav hnodup
          (fun i hi => hLav_card1 es[i] (List.getElem_mem _)) h2p
        exact ⟨h, fun e he => hLav_sub e _ (hhL e he),
          fun e he f hf ha => hLav_tt e _ (hhL e he) f hf ha, hpath_prop h hhadj⟩
      by_cases hex_start : ∃ f : F.edgeSet, IsTT t f.val ∧ (LF F).Adj (es[0]'(by omega)) f
      swap
      · let es_rev := es.reverse
        have hnodup_rev : es_rev.Nodup := List.nodup_reverse.mpr hnodup
        have hlen_rev : es_rev.length = es.length := List.length_reverse
        have h1p : ∀ i (hi : i < es_rev.length), 1 ≤ (Lav (es_rev[i]'hi)).card :=
          fun i hi => hLav_card1 _ (List.mem_reverse.mp (List.getElem_mem hi))
        have h2p : ∀ i (hi : i + 1 < es_rev.length), 2 ≤ (Lav (es_rev[i + 1]'hi)).card := by
          intro i hi
          have hidx_eq : es_rev[i + 1]'hi = es[es.length - 1 - (i + 1)]'(by omega) := by
            simp only [es_rev, List.getElem_reverse]
          rw [hidx_eq]
          by_cases hi0 : es.length - 1 - (i + 1) = 0
          · have hcongr : es[es.length - 1 - (i + 1)]'(by omega) = es[0]'(by omega) := by congr 1
            rw [hcongr]
            have heq : Lav (es[0]'(by omega)) =
                edgeAllowed c t (es[0]'(by omega)).val := by
              ext α
              simp only [Lav, L_avoid, Finset.mem_filter, and_iff_left_iff_imp]
              intro _ f hf ha
              exact absurd ⟨f, hf, ha⟩ hex_start
            rw [heq]
            exact non_tt_edge_card_ge_two t c _ (hnonTT _ (List.getElem_mem _))
          · exact hLav_internal (es.length - 1 - (i + 1)) (by omega) (by omega)
        obtain ⟨h, hhL, hhadj⟩ := list_color_path es_rev Lav hnodup_rev h1p h2p
        refine ⟨h, fun e he => hLav_sub e _ (hhL e (List.mem_reverse.mpr he)),
          fun e he f hf ha => hLav_tt e _ (hhL e (List.mem_reverse.mpr he)) f hf ha,
          hpath_prop h (fun i hi => ?_)⟩
        let j := es.length - 1 - (i + 1)
        have hj_lt : j + 1 < es_rev.length := by omega
        have hre0 : es_rev[j]'(by omega) = es[i + 1] := by
          simp only [es_rev, List.getElem_reverse]; congr 1; omega
        have hre1 : es_rev[j + 1]'hj_lt = es[i] := by
          simp only [es_rev, List.getElem_reverse]; congr 1; omega
        have hadj_rev := hhadj j hj_lt
        rw [hre0, hre1] at hadj_rev
        exact hadj_rev.symm
      -- Both es[0] and es[last] have TT neighbors!
      obtain ⟨f_start, hf_start_tt, hf_start_adj⟩ := hex_start
      obtain ⟨f_end, hf_end_tt, hf_end_adj⟩ := hex_end
      have hcard_le2_of_tt : ∀ (e f : F.edgeSet), ¬ IsTT t e.val → IsTT t f.val →
          (LF F).Adj e f → (edgeAllowed c t e.val).card ≤ 2 := by
        intro e f _ hf ⟨_, w, hwe, hwf⟩
        have htw : t w = true := hf w hwf
        have hsub : edgeAllowed c t e.val ⊆ Finset.univ.erase (c w) := by
          intro α hα
          simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and] at hα
          exact Finset.mem_erase.mpr ⟨hα w htw hwe, Finset.mem_univ _⟩
        calc (edgeAllowed c t e.val).card ≤ (Finset.univ.erase (c w)).card := Finset.card_le_card hsub
          _ = 2 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin 3]
      by_cases h3 : ∃ j : Fin es.length, (edgeAllowed c t es[j.val].val).card = 3
      · obtain ⟨j, hj3⟩ := h3
        have hj0 : 0 < j.val := by
          by_contra h0
          have hjeq : j.val = 0 := by omega
          have hle2 := hcard_le2_of_tt _ _ (hnonTT _ (List.getElem_mem _)) hf_start_tt hf_start_adj
          have hcongr : es[j.val] = es[0]'(by omega) := by congr 1
          rw [hcongr] at hj3; omega
        have hjlast : j.val + 1 < es.length := by
          by_contra hlast
          have hjeq : j.val = es.length - 1 := by omega
          have hle2 := hcard_le2_of_tt _ _ (hnonTT _ (List.getElem_mem _)) hf_end_tt hf_end_adj
          have hcongr : es[j.val] = es[es.length - 1]'(by omega) := by congr 1
          rw [hcongr] at hj3; omega
        let left := es.take j.val
        let right := (es.drop (j.val + 1)).reverse
        have hlen_left : left.length = j.val := by simp [left]
        have hnodup_left : left.Nodup := hnodup.sublist (List.take_sublist _ _)
        have h1_left : ∀ i (hi : i < left.length), 1 ≤ (Lav (left[i]'hi)).card :=
          fun i hi => hLav_card1 _ ((List.take_sublist _ _).mem (List.getElem_mem hi))
        have h2_left : ∀ i (hi : i + 1 < left.length), 2 ≤ (Lav (left[i + 1]'hi)).card := by
          intro i hi
          have hidx_eq : left[i + 1]'hi = es[i + 1]'(by omega) := by simp [left]
          rw [hidx_eq]
          exact hLav_internal (i + 1) (by omega) (by omega)
        obtain ⟨hL, hhL_mem, hhL_adj⟩ := list_color_path left Lav hnodup_left h1_left h2_left
        have hlen_right : right.length = es.length - (j.val + 1) := by
          simp [right, List.length_reverse, List.length_drop]
        have hnodup_right : right.Nodup :=
          List.nodup_reverse.mpr (hnodup.sublist (List.drop_sublist _ _))
        have h1_right : ∀ i (hi : i < right.length), 1 ≤ (Lav (right[i]'hi)).card :=
          fun i hi => hLav_card1 _ ((List.drop_sublist _ _).mem (List.mem_reverse.mp (List.getElem_mem hi)))
        have h2_right : ∀ i (hi : i + 1 < right.length), 2 ≤ (Lav (right[i + 1]'hi)).card := by
          intro i hi
          have hidx_eq : right[i + 1]'hi = es[es.length - 1 - (i + 1)]'(by omega) := by
            simp only [right, List.getElem_reverse, List.getElem_drop, List.length_drop]
            congr 1; omega
          rw [hidx_eq]
          exact hLav_internal (es.length - 1 - (i + 1)) (by omega) (by omega)
        obtain ⟨hR, hhR_mem, hhR_adj⟩ := list_color_path right Lav hnodup_right h1_right h2_right
        let used : Finset (Fin 3) := {hL (es[j.val - 1]'(by omega)), hR (es[j.val + 1]'(by omega))}
        have hcard_lt : used.card < (Finset.univ : Finset (Fin 3)).card := by
          calc used.card ≤ 2 := Finset.card_le_two
            _ < 3 := by decide
            _ = (Finset.univ : Finset (Fin 3)).card := by rw [Finset.card_univ, Fintype.card_fin 3]
        obtain ⟨α_mid, _, hαmid_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
        have hLav_mid : Lav es[j.val] = Finset.univ := by
          have huniv : edgeAllowed c t es[j.val].val = Finset.univ :=
            Finset.eq_univ_of_card _ (by rw [hj3, Fintype.card_fin 3])
          ext α
          simp only [Lav, L_avoid, huniv, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          intro f hf ha
          have hne12 : (es[j.val - 1]'(by omega)) ≠ (es[j.val + 1]'(by omega)) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          have ha1 : (LF F).Adj es[j.val] (es[j.val - 1]'(by omega)) := by
            have h := (hpadj (j.val - 1) (by omega)).symm
            have hcongr : es[j.val - 1 + 1]'(by omega) = es[j.val] := by congr 1; omega
            rwa [hcongr] at h
          exact absurd ha (no_tt_deg2_lf F t fd hne12 ha1 (hpadj j.val hjlast)
            (hnonTT _ (List.getElem_mem _)) (hnonTT _ (List.getElem_mem _)) f hf)
        let h : F.edgeSet → Fin 3 := fun e =>
          @ite _ (e ∈ left) (Classical.propDecidable _) (hL e)
            (@ite _ (e = es[j.val]'j.isLt) (Classical.propDecidable _) α_mid (hR e))
        have h_eq_left : ∀ i (hi : i < j.val), h (es[i]'(by omega)) = hL (es[i]'(by omega)) := by
          intro i hi
          have hmem : es[i]'(by omega) ∈ left := by
            have : es[i]'(by omega) = left[i]'(by rw [hlen_left]; exact hi) := by simp [left]
            rw [this]; exact List.getElem_mem _
          dsimp only [h]; rw [if_pos hmem]
        have h_eq_mid : h (es[j.val]'j.isLt) = α_mid := by
          have hnotL : es[j.val]'j.isLt ∉ left := by
            intro hm
            obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hm
            have hi' : i < j.val := by rw [← hlen_left]; exact hi
            simp only [left, List.getElem_take] at heq
            have := hnodup.getElem_inj_iff.mp heq; omega
          dsimp only [h]; rw [if_neg hnotL, if_pos rfl]
        have h_eq_right : ∀ i (hi1 : j.val + 1 ≤ i) (hi2 : i < es.length),
            h (es[i]'(by omega)) = hR (es[i]'(by omega)) := by
          intro i hi1 hi2
          have hnotL : es[i]'(by omega) ∉ left := by
            intro hm
            obtain ⟨k, hk, heq⟩ := List.getElem_of_mem hm
            have hk' : k < j.val := by rw [← hlen_left]; exact hk
            simp only [left, List.getElem_take] at heq
            have := hnodup.getElem_inj_iff.mp heq; omega
          have hneM : es[i]'(by omega) ≠ es[j.val]'j.isLt := fun heq => by
            have := hnodup.getElem_inj_iff.mp heq; omega
          dsimp only [h]; rw [if_neg hnotL, if_neg hneM]
        have hh_Lav : ∀ e ∈ es, h e ∈ Lav e := by
          intro e he
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
          rcases Nat.lt_trichotomy i j.val with hij | rfl | hji
          · rw [h_eq_left i hij]
            have hmem : es[i] ∈ left := by
              have : es[i] = left[i]'(by rw [hlen_left]; exact hij) := by simp [left]
              rw [this]; exact List.getElem_mem _
            exact hhL_mem _ hmem
          · rw [h_eq_mid, hLav_mid]; exact Finset.mem_univ _
          · rw [h_eq_right i (by omega) hi]
            have hmem : es[i] ∈ right := by
              rw [List.mem_reverse]
              have hidx_eq : (j.val + 1) + (i - (j.val + 1)) = i := by omega
              have hdrop_len : i - (j.val + 1) < (es.drop (j.val + 1)).length := by
                rw [List.length_drop]; omega
              have hmem_eq : es[i] = (es.drop (j.val + 1))[i - (j.val + 1)]'hdrop_len := by
                simp only [List.getElem_drop]; congr 1; omega
              rw [hmem_eq]; exact List.getElem_mem _
            exact hhR_mem _ hmem
        refine ⟨h, fun e he => hLav_sub e _ (hh_Lav e he),
          fun e he f hf ha => hLav_tt e _ (hh_Lav e he) f hf ha, hpath_prop h (fun i hi => ?_)⟩
        by_cases hil : i + 1 < j.val
        · rw [h_eq_left i (by omega), h_eq_left (i + 1) hil]
          have ha_l := hhL_adj i (by rw [hlen_left]; exact hil)
          have he0 : left[i]'(by rw [hlen_left]; omega) = es[i]'(by omega) := by simp [left]
          have he1 : left[i + 1]'(by rw [hlen_left]; exact hil) = es[i + 1]'(by omega) := by simp [left]
          rwa [he0, he1] at ha_l
        · by_cases him : i + 1 = j.val
          · have hcongr : es[i]'(by omega) = es[j.val - 1]'(by omega) := by congr 1; omega
            have hcongr2 : es[i + 1]'(by omega) = es[j.val] := by congr 1
            rw [h_eq_left i (by omega), hcongr, hcongr2, h_eq_mid]
            intro heq; apply hαmid_not; rw [← heq]; exact Finset.mem_insert_self _ _
          · by_cases hij : i = j.val
            · have hcongr1 : es[i]'(by omega) = es[j.val] := by congr 1
              have hcongr2 : es[i + 1]'(by omega) = es[j.val + 1]'(by omega) := by congr 1; omega
              rw [hcongr1, h_eq_mid, h_eq_right (i + 1) (by omega) hi, hcongr2]
              intro heq; apply hαmid_not; rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            · rw [h_eq_right i (by omega) (by omega), h_eq_right (i + 1) (by omega) hi]
              let rIdx := es.length - 1 - (i + 1)
              have hr_lt : rIdx + 1 < right.length := by omega
              have hre0 : right[rIdx]'(by omega) = es[i + 1] := by
                simp only [right, List.getElem_reverse, List.getElem_drop, List.length_drop]
                congr 1; omega
              have hre1 : right[rIdx + 1]'hr_lt = es[i] := by
                simp only [right, List.getElem_reverse, List.getElem_drop, List.length_drop]
                congr 1; omega
              have har := hhR_adj rIdx hr_lt
              rw [hre0, hre1] at har
              exact har.symm
      · -- All edges in es have card = 2 -> even chain!
        push Not at h3
        have hcard2 : ∀ e ∈ es, (edgeAllowed c t e.val).card = 2 := by
          intro e he
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
          have hge := non_tt_edge_card_ge_two t c es[i] (hnonTT _ he)
          have hle : (edgeAllowed c t es[i].val).card ≤ 3 :=
            (Finset.card_le_univ _).trans (by rw [Fintype.card_fin 3])
          have hne3 : (edgeAllowed c t es[i].val).card ≠ 3 := h3 ⟨i, hi⟩
          omega
        have h01 := hpadj 0 (by omega)
        let z1 := Classical.choose h01.2
        have hz1_0 : z1 ∈ (es[0]'(by omega)).val := (Classical.choose_spec h01.2).1
        have hz1_1 : z1 ∈ (es[1]'(by omega)).val := (Classical.choose_spec h01.2).2
        let z0 := otherVertex F (es[0]'(by omega)) z1
        have hz0_spec := otherVertex_spec F (es[0]'(by omega)) z1 hz1_0
        have hz0_in_0 : z0 ∈ (es[0]'(by omega)).val := by
          rw [hz0_spec.2]; exact Sym2.mem_mk_right z1 z0
        have hz0_not_1 : z0 ∉ (es[1]'(by omega)).val := by
          intro hz01
          have hne01 : es[0]'(by omega) ≠ es[1]'(by omega) := fun h => by
            have := hnodup.getElem_inj_iff.mp h; omega
          have heq : (es[0]'(by omega)).val = (es[1]'(by omega)).val := by
            have hz0_ne_z1 : z0 ≠ z1 := hz0_spec.1.ne.symm
            have he0_eq : (es[0]'(by omega)).val = s(z1, z0) := hz0_spec.2
            rw [he0_eq]
            induction hval : (es[1]'(by omega)).val using Sym2.ind with
            | _ a b =>
              rw [hval, Sym2.mem_iff] at hz1_1 hz01
              rcases hz1_1 with rfl | rfl <;> rcases hz01 with h0a | h0b
              · exact absurd h0a hz0_ne_z1
              · rw [h0b]
              · rw [h0a]; exact Sym2.eq_swap
              · exact absurd h0b hz0_ne_z1
          exact hne01 (Subtype.ext heq)
        let zs := traceEdges F z0 es
        have hlen_z : zs.length = es.length + 1 := traceEdges_length F z0 es
        have hzs0 : zs[0]'(by omega) = z0 := traceEdges_head F z0 es
        have hz_spec : ∀ i (hi : i < es.length),
            es[i].val = s(zs[i]'(by omega), zs[i + 1]'(by omega)) ∧
            F.Adj (zs[i]'(by omega)) (zs[i + 1]'(by omega)) :=
          traceEdges_spec F fd es z0 hnodup
            (fun _ => hz0_in_0) (fun _ => hz0_not_1) hpadj
        have hz0_fstart : zs[0]'(by omega) ∈ f_start.val := by
          obtain ⟨hfs_ne, w, hw0, hwf⟩ := hf_start_adj
          have hw_not_z1 : w ≠ zs[1]'(by omega) := by
            intro hweq
            have hz1_fs : zs[1]'(by omega) ∈ f_start.val := hweq ▸ hwf
            have hz1_e0 : zs[1]'(by omega) ∈ (es[0]'(by omega)).val := by
              rw [(hz_spec 0 (by omega)).1]; exact Sym2.mem_mk_right _ _
            have hz1_e1 : zs[1]'(by omega) ∈ (es[1]'(by omega)).val := by
              rw [(hz_spec 1 (by omega)).1]; exact Sym2.mem_mk_left _ _
            have hfe0 : f_start ≠ es[0]'(by omega) := hfs_ne.symm
            have hfe1 : f_start ≠ es[1]'(by omega) := fun h =>
              hnonTT _ (List.getElem_mem _) (h ▸ hf_start_tt)
            have he01 : es[0]'(by omega) ≠ es[1]'(by omega) := fun h => by
              have := hnodup.getElem_inj_iff.mp h; omega
            exact three_edges_at_vertex_absurd F fd hfe0 hfe1 he01 hz1_fs hz1_e0 hz1_e1
          have hw_eq : w = zs[0]'(by omega) := by
            rw [(hz_spec 0 (by omega)).1, Sym2.mem_iff] at hw0
            exact hw0.resolve_right hw_not_z1
          exact hw_eq ▸ hwf
        have hzlast_fend : zs[es.length]'(by omega) ∈ f_end.val := by
          obtain ⟨hfe_ne, w, hwl, hwf⟩ := hf_end_adj
          have hw_not_prev : w ≠ zs[es.length - 1]'(by omega) := by
            intro hweq
            have hp_fe : zs[es.length - 1]'(by omega) ∈ f_end.val := hweq ▸ hwf
            have hp_last : zs[es.length - 1]'(by omega) ∈ (es[es.length - 1]'(by omega)).val := by
              have h := (hz_spec (es.length - 1) (by omega)).1
              have hcongr : zs[es.length - 1 + 1]'(by omega) = zs[es.length]'(by omega) := by
                congr 1; omega
              rw [h]; exact Sym2.mem_mk_left _ _
            have hp_prev : zs[es.length - 1]'(by omega) ∈ (es[es.length - 2]'(by omega)).val := by
              have h := (hz_spec (es.length - 2) (by omega)).1
              have hcongr : zs[es.length - 2 + 1]'(by omega) = zs[es.length - 1]'(by omega) := by
                congr 1; omega
              rw [h, hcongr]; exact Sym2.mem_mk_right _ _
            have hfe_last : f_end ≠ es[es.length - 1]'(by omega) := hfe_ne.symm
            have hfe_prev : f_end ≠ es[es.length - 2]'(by omega) := fun h =>
              hnonTT _ (List.getElem_mem _) (h ▸ hf_end_tt)
            have hl_p : es[es.length - 1]'(by omega) ≠ es[es.length - 2]'(by omega) := fun h => by
              have := hnodup.getElem_inj_iff.mp h; omega
            exact three_edges_at_vertex_absurd F fd hfe_last hfe_prev hl_p hp_fe hp_last hp_prev
          have hw_eq : w = zs[es.length]'(by omega) := by
            have h := (hz_spec (es.length - 1) (by omega)).1
            have hcongr : zs[es.length - 1 + 1]'(by omega) = zs[es.length]'(by omega) := by
              congr 1; omega
            rw [h, hcongr, Sym2.mem_iff] at hwl
            exact hwl.resolve_left hw_not_prev
          exact hw_eq ▸ hwf
        have ht0 : t (zs[0]'(by omega)) = true := hf_start_tt _ hz0_fstart
        have htlast : t (zs[es.length]'(by omega)) = true := hf_end_tt _ hzlast_fend
        have hz_flip : ∀ i (hi : i < es.length),
            t (zs[i + 1]'(by omega)) = !(t (zs[i]'(by omega))) := by
          intro i hi
          have he_eq := (hz_spec i hi).1
          by_cases hti : t (zs[i]'(by omega)) = true <;>
            by_cases hti1 : t (zs[i + 1]'(by omega)) = true
          · exfalso; apply hnonTT _ (List.getElem_mem hi)
            intro w hw; rw [he_eq, Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
          · have hfalse : t (zs[i + 1]'(by omega)) = false := Bool.eq_false_iff.mpr hti1
            rw [hti, hfalse]; rfl
          · have hfalse : t (zs[i]'(by omega)) = false := Bool.eq_false_iff.mpr hti
            rw [hfalse, hti1]; rfl
          · exfalso
            have hf1 : t (zs[i]'(by omega)) = false := Bool.eq_false_iff.mpr hti
            have hf2 : t (zs[i + 1]'(by omega)) = false := Bool.eq_false_iff.mpr hti1
            have huniv : edgeAllowed c t es[i].val = Finset.univ := by
              ext α
              simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and, iff_true,
                he_eq, Sym2.mem_iff]
              rintro w htw (rfl | rfl)
              · rw [hf1] at htw; cases htw
              · rw [hf2] at htw; cases htw
            have hc2 := hcard2 _ (List.getElem_mem hi)
            rw [huniv, Finset.card_univ, Fintype.card_fin 3] at hc2
            omega
        have hz_par : ∀ i (hi : i ≤ es.length),
            t (zs[i]'(by omega)) = if i % 2 = 0 then true else false := by
          intro i
          induction i with
          | zero => intro _; simp [ht0]
          | succ k ih =>
            intro hk
            rw [hz_flip k (by omega), ih (by omega)]
            by_cases hk2 : k % 2 = 0
            · have hk12 : (k + 1) % 2 ≠ 0 := by omega
              simp [hk2, hk12]
            · have hk12 : (k + 1) % 2 = 0 := by omega
              simp [hk2, hk12]
        have heven : es.length % 2 = 0 := by
          have h := hz_par es.length (le_refl _)
          rw [htlast] at h
          by_contra hodd
          rw [if_neg hodd] at h
          cases h
        let m := es.length / 2
        have hm : 1 ≤ m := by omega
        have hlen_e : es.length = 2 * m := by omega
        have hlen_zm : zs.length = 2 * m + 1 := by omega
        have hes_val : ∀ (i : ℕ) (hi : i < 2 * m),
            es[i].val = s(zs[i]'(by omega), zs[i + 1]'(by omega)) := fun i hi =>
          (hz_spec i (by omega)).1
        have ht_even : ∀ (j : ℕ) (hj : 2 * j < 2 * m + 1), t (zs[2 * j]'(by omega)) = true := by
          intro j hj
          rw [hz_par (2 * j) (by omega)]
          simp
        have ht_odd : ∀ (j : ℕ) (hj : 2 * j + 1 < 2 * m + 1), t (zs[2 * j + 1]'(by omega)) = false := by
          intro j hj
          rw [hz_par (2 * j + 1) (by omega)]
          rw [if_neg (show (2 * j + 1) % 2 ≠ 0 by omega)]
        have hznodup : zs.Nodup := by
          rw [List.nodup_iff_injective_getElem]
          intro ⟨i, hi⟩ ⟨j, hj⟩ heq
          dsimp at heq
          suffices hij : i = j by exact Fin.ext hij
          by_contra hne_ij
          wlog hij : i < j generalizing i j
          · exact this j hj i hi heq.symm (fun h => hne_ij h.symm) (by omega)
          let eL : ℕ → F.edgeSet := fun a =>
            if a = 0 then f_start else if ha' : a - 1 < es.length then es[a - 1] else f_start
          let eR : ℕ → F.edgeSet := fun a =>
            if ha : a < es.length then es[a] else f_end
          have heL_ne_eR : ∀ a (ha : a ≤ es.length), eL a ≠ eR a := by
            intro a ha
            by_cases ha0 : a = 0
            · subst ha0
              have heL0 : eL 0 = f_start := by simp [eL]
              have heR0 : eR 0 = es[0]'(by omega) := by simp [eR, show 0 < es.length by omega]
              rw [heL0, heR0]
              exact fun h => hnonTT _ (List.getElem_mem _) (h ▸ hf_start_tt)
            · have heLa : eL a = es[a - 1]'(by omega) := by
                simp [eL, ha0, show a - 1 < es.length by omega]
              by_cases hal : a < es.length
              · have heRa : eR a = es[a] := by simp [eR, hal]
                rw [heLa, heRa]
                exact fun h => by have := hnodup.getElem_inj_iff.mp h; omega
              · have heRa : eR a = f_end := by simp [eR, hal]
                rw [heLa, heRa]
                exact fun h => hnonTT _ (List.getElem_mem _) (h.symm ▸ hf_end_tt)
          have heL_mem : ∀ a (ha : a ≤ es.length), zs[a]'(by omega) ∈ (eL a).val := by
            intro a ha
            by_cases ha0 : a = 0
            · subst ha0; simp [eL, hz0_fstart]
            · have heLa : eL a = es[a - 1]'(by omega) := by
                simp [eL, ha0, show a - 1 < es.length by omega]
              rw [heLa]
              have h := (hz_spec (a - 1) (by omega)).1
              have hcongr : zs[a - 1 + 1]'(by omega) = zs[a]'(by omega) := by congr 1; omega
              rw [h, hcongr]; exact Sym2.mem_mk_right _ _
          have heR_mem : ∀ a (ha : a ≤ es.length), zs[a]'(by omega) ∈ (eR a).val := by
            intro a ha
            dsimp [eR]
            split_ifs with hal
            · rw [(hz_spec a hal).1]; exact Sym2.mem_mk_left _ _
            · have hcongr : zs[a]'(by omega) = zs[es.length]'(by omega) := by congr 1; omega
              rw [hcongr]; exact hzlast_fend
          have hmem_pair : ∀ (x : F.edgeSet), zs[i]'(by omega) ∈ x.val → x = eL i ∨ x = eR i := by
            intro x hx
            by_contra hnot
            push Not at hnot
            exact three_edges_at_vertex_absurd F fd (heL_ne_eR i (by omega)) hnot.1.symm hnot.2.symm
              (heL_mem i (by omega)) (heR_mem i (by omega)) hx
          have hL_j : eL j = eL i ∨ eL j = eR i := hmem_pair (eL j) (heq ▸ heL_mem j (by omega))
          have hR_j : eR j = eL i ∨ eR j = eR i := hmem_pair (eR j) (heq ▸ heR_mem j (by omega))
          have hi_lt : i < es.length := by omega
          by_cases hj_last : j = es.length
          · subst hj_last
            by_cases hi_prev : i = es.length - 1
            · subst hi_prev
              have hadj_last := (hz_spec (es.length - 1) (by omega)).2
              have hcongr : zs[es.length - 1 + 1]'(by omega) = zs[es.length]'(by omega) := by
                congr 1; omega
              rw [hcongr, ← heq] at hadj_last
              exact F.loopless.irrefl _ hadj_last
            · have heLj_eq : eL es.length = es[es.length - 1]'(by omega) := by
                simp only [eL, show es.length ≠ 0 by omega, ↓reduceIte,
                  show es.length - 1 < es.length by omega, dif_pos]
              rw [heLj_eq] at hL_j
              rcases hL_j with h | h
              · by_cases hi0 : i = 0
                · simp only [eL, hi0, ↓reduceIte] at h
                  exact hnonTT _ (List.getElem_mem _) (h ▸ hf_start_tt)
                · simp only [eL, hi0, ↓reduceIte, show i - 1 < es.length by omega, dif_pos] at h
                  have := hnodup.getElem_inj_iff.mp h; omega
              · simp only [eR, hi_lt, dif_pos] at h
                have := hnodup.getElem_inj_iff.mp h; omega
          · have heRj_eq : eR j = es[j]'(by omega) := by simp [eR, show j < es.length by omega]
            rw [heRj_eq] at hR_j
            rcases hR_j with h | h
            · by_cases hi0 : i = 0
              · simp only [eL, hi0, ↓reduceIte] at h
                exact hnonTT _ (List.getElem_mem _) (h ▸ hf_start_tt)
              · simp only [eL, hi0, ↓reduceIte, show i - 1 < es.length by omega, dif_pos] at h
                have := hnodup.getElem_inj_iff.mp h; omega
            · simp only [eR, hi_lt, dif_pos] at h
              have := hnodup.getElem_inj_iff.mp h; omega
        let u := otherVertex F f_start (zs[0]'(by omega))
        have hu_spec := otherVertex_spec F f_start (zs[0]'(by omega)) hz0_fstart
        have htu : t u = true := hf_start_tt u (by rw [hu_spec.2]; exact Sym2.mem_mk_right _ _)
        let u' := otherVertex F f_end (zs[2 * m]'(by omega))
        have hu'_spec := otherVertex_spec F f_end (zs[2 * m]'(by omega))
          (by have hcongr : zs[2 * m]'(by omega) = zs[es.length]'(by omega) := by congr 1; omega
              rw [hcongr]; exact hzlast_fend)
        have htu' : t u' = true := hf_end_tt u' (by rw [hu'_spec.2]; exact Sym2.mem_mk_right _ _)
        have hcu_er := erase_hTT_mem_other S F t c inside hcS (hnonTT _ (List.getElem_mem _))
          hf_start_tt (hu_spec.2.trans Sym2.eq_swap)
          (by rw [(hz_spec 0 (by omega)).1]; exact Sym2.mem_mk_left _ _)
        have hcu'_er := erase_hTT_mem_other S F t c inside hcS (hnonTT _ (List.getElem_mem _))
          hf_end_tt (hu'_spec.2.trans Sym2.eq_swap)
          (by have h := (hz_spec (2 * m - 1) (by omega)).1
              have hcongr : zs[2 * m - 1 + 1]'(by omega) = zs[2 * m]'(by omega) := by congr 1; omega
              rw [h, hcongr]; exact Sym2.mem_mk_right _ _)
        have hcu_mem : c u ∈ edgeAllowed c t (es[0]'(by omega)).val :=
          Finset.erase_subset _ _ hcu_er.1
        have hcu'_mem : c u' ∈ edgeAllowed c t (es[2 * m - 1]'(by omega)).val :=
          Finset.erase_subset _ _ hcu'_er.1
        have hcheck_all : ∀ (h : F.edgeSet → Fin 3),
            h (es[0]'(by omega)) = c u →
            h (es[2 * m - 1]'(by omega)) = c u' →
            (∀ x ∈ es, h x ∈ edgeAllowed c t x.val) →
            (∀ i (hi : i + 1 < 2 * m), h (es[i]'(by omega)) ≠ h (es[i + 1]'(by omega))) →
            ∃ h₀ : F.edgeSet → Fin 3,
              (∀ e ∈ es, h₀ e ∈ edgeAllowed c t e.val) ∧
              (∀ e ∈ es, ∀ f : F.edgeSet, IsTT t f.val → (LF F).Adj e f → h₀ e ≠ hTT t c f) ∧
              (∀ e ∈ es, ∀ f ∈ es, (LF F).Adj e f → h₀ e ≠ h₀ f) := by
          intro h h0 hlast hL hadj_h
          refine ⟨h, hL, fun e he f hf ha => ?_, hpath_prop h (fun i hi => hadj_h i (by omega))⟩
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
          by_cases hi0 : i = 0
          · subst hi0
            have hfeq := non_tt_at_most_one_tt_neighbor F t three
              (hnonTT _ (List.getElem_mem _)) hf_start_tt hf hf_start_adj ha
            subst hfeq
            rw [h0]
            exact (Finset.mem_erase.mp hcu_er.1).1
          · by_cases hilast : i = es.length - 1
            · have hcongr : es[i] = es[2 * m - 1]'(by omega) := by congr 1; omega
              rw [hcongr] at ha ⊢
              have hfeq := non_tt_at_most_one_tt_neighbor F t three
                (hnonTT _ (List.getElem_mem _)) hf_end_tt hf
                (by convert hf_end_adj using 2; omega) ha
              subst hfeq
              rw [hlast]
              exact (Finset.mem_erase.mp hcu'_er.1).1
            · exfalso
              have hne12 : es[i - 1] ≠ es[i + 1] := fun h => by
                have := hnodup.getElem_inj_iff.mp h; omega
              have ha1 : (LF F).Adj es[i] es[i - 1] := by
                have h1 := (hpadj (i - 1) (by omega)).symm
                have hcongr : es[i - 1 + 1] = es[i] := by congr 1; omega
                rwa [hcongr] at h1
              exact no_tt_deg2_lf F t fd hne12 ha1 (hpadj i (by omega))
                (hnonTT _ (List.getElem_mem _)) (hnonTT _ (List.getElem_mem _)) f hf ha
        by_cases hfeq : f_start = f_end
        · have hz0_ne_end : zs[0]'(by omega) ≠ zs[2 * m]'(by omega) := fun h => by
            have := hznodup.getElem_inj_iff.mp h; omega
          have hz_end_fs : zs[2 * m]'(by omega) ∈ f_start.val := by
            rw [hfeq]
            have hcongr : zs[2 * m]'(by omega) = zs[es.length]'(by omega) := by congr 1; omega
            rw [hcongr]; exact hzlast_fend
          have hu_eq : u = zs[2 * m]'(by omega) :=
            (sym2_mem_and_eq_other hu_spec.2 hz_end_fs hz0_ne_end.symm).symm
          have hu'_eq : u' = zs[0]'(by omega) := by
            have hz0_fe : zs[0]'(by omega) ∈ f_end.val := hfeq ▸ hz0_fstart
            exact (sym2_mem_and_eq_other hu'_spec.2 hz0_fe hz0_ne_end).symm
          have hcu_ne : c u ≠ c u' := by
            rw [hu_eq, hu'_eq]
            exact hcS _ _ (inside _ _ (by rw [← hu_eq]; exact hu_spec.1.symm)
              (ht_even m (by omega)) ht0)
          obtain ⟨h, h0, hlast, hL, hadj_h⟩ := list_color_even_chain F t c m hm es zs hnodup
            hlen_e hlen_zm hes_val (fun j hj => ht_even j (by omega)) (fun j hj => ht_odd j (by omega))
            (c u) (c u') hcu_mem hcu'_mem (Or.inl hcu_ne)
          exact hcheck_all h h0 hlast hL hadj_h
        · have hne_edge : s(u, zs[0]'(by omega)) ≠ s(zs[2 * m]'(by omega), u') := by
            intro h
            apply hfeq
            apply Subtype.ext
            rw [hu_spec.2, hu'_spec.2, Sym2.eq_swap, h]
          let w : AltWalk F t u (zs[0]'(by omega)) (zs[2 * m]'(by omega)) u' := {
            m := m
            hm := hm
            zs := zs
            hlen := hlen_zm
            hnodup := hznodup
            hstart := rfl
            hend := rfl
            hadj_u := hu_spec.1.symm
            hadj_u' := hu'_spec.1
            htu := htu
            htu' := htu'
            hne_edge := hne_edge
            hadj_zs := fun i hi => (hz_spec i (by omega)).2
            ht_even := fun j hj => ht_even j (by omega)
            ht_odd := fun j hj => ht_odd j (by omega)
          }
          rcases halt u (zs[0]'(by omega)) (zs[2 * m]'(by omega)) u' w with
            hcu_ne | ⟨hm2, hmid | hmid_rev⟩
          · obtain ⟨h, h0, hlast, hL, hadj_h⟩ := list_color_even_chain F t c m hm es zs hnodup
              hlen_e hlen_zm hes_val (fun j hj => ht_even j (by omega)) (fun j hj => ht_odd j (by omega))
              (c u) (c u') hcu_mem hcu'_mem (Or.inl hcu_ne)
            exact hcheck_all h h0 hlast hL hadj_h
          · obtain ⟨h, h0, hlast, hL, hadj_h⟩ := list_color_even_chain F t c m hm es zs hnodup
              hlen_e hlen_zm hes_val (fun j hj => ht_even j (by omega)) (fun j hj => ht_odd j (by omega))
              (c u) (c u') hcu_mem hcu'_mem
              (Or.inr ⟨hm2, hmid⟩)
            exact hcheck_all h h0 hlast hL hadj_h
          · let es_rev := es.reverse
            let zs_rev := zs.reverse
            have hnodup_rev : es_rev.Nodup := List.nodup_reverse.mpr hnodup
            have hlen_er : es_rev.length = 2 * m := by simp [es_rev, hlen_e]
            have hlen_zr : zs_rev.length = 2 * m + 1 := by simp [zs_rev, hlen_zm]
            have hes_val_r : ∀ i (hi : i < 2 * m),
                (es_rev[i]'(by omega)).val = s(zs_rev[i]'(by omega), zs_rev[i + 1]'(by omega)) := by
              intro i hi
              simp only [es_rev, zs_rev, List.getElem_reverse]
              have h := hes_val (2 * m - 1 - i) (by omega)
              have h1 : es.length - 1 - i = 2 * m - 1 - i := by omega
              have h2 : zs.length - 1 - i = 2 * m - 1 - i + 1 := by omega
              have h3 : zs.length - 1 - (i + 1) = 2 * m - 1 - i := by omega
              have hc1 : es[es.length - 1 - i]'(by omega) = es[2 * m - 1 - i]'(by omega) := by
                congr 1
              have hc2 : zs[zs.length - 1 - i]'(by omega) = zs[2 * m - 1 - i + 1]'(by omega) := by
                congr 1
              have hc3 : zs[zs.length - 1 - (i + 1)]'(by omega) = zs[2 * m - 1 - i]'(by omega) := by
                congr 1
              rw [hc1, hc2, hc3, h, Sym2.eq_swap]
            have ht_even_r : ∀ j (hj : 2 * j < 2 * m + 1),
                t (zs_rev[2 * j]'(by omega)) = true := by
              intro j hj
              simp only [zs_rev, List.getElem_reverse]
              have h := ht_even (m - j) (by omega)
              have h1 : zs.length - 1 - 2 * j = 2 * (m - j) := by omega
              have hc : zs[zs.length - 1 - 2 * j]'(by omega) = zs[2 * (m - j)]'(by omega) := by
                congr 1
              rwa [hc]
            have ht_odd_r : ∀ j (hj : 2 * j + 1 < 2 * m + 1),
                t (zs_rev[2 * j + 1]'(by omega)) = false := by
              intro j hj
              simp only [zs_rev, List.getElem_reverse]
              have h := ht_odd (m - 1 - j) (by omega)
              have h1 : zs.length - 1 - (2 * j + 1) = 2 * (m - 1 - j) + 1 := by omega
              have hc : zs[zs.length - 1 - (2 * j + 1)]'(by omega) =
                  zs[2 * (m - 1 - j) + 1]'(by omega) := by congr 1
              rwa [hc]
            have hαL_r : c u' ∈ edgeAllowed c t (es_rev[0]'(by omega)).val := by
              have hcongr : es_rev[0]'(by omega) = es[2 * m - 1]'(by omega) := by
                simp only [es_rev, List.getElem_reverse]; congr 1; omega
              rw [hcongr]; exact hcu'_mem
            have hαR_r : c u ∈ edgeAllowed c t (es_rev[2 * m - 1]'(by omega)).val := by
              have hcongr : es_rev[2 * m - 1]'(by omega) = es[0]'(by omega) := by
                simp only [es_rev, List.getElem_reverse]; congr 1; omega
              rw [hcongr]; exact hcu_mem
            have hmid_r : c (zs_rev[2]'(by omega)) = c u' := by
              have hcongr : zs_rev[2]'(by omega) = zs[2 * m - 2]'(by omega) := by
                simp only [zs_rev, List.getElem_reverse]; congr 1; omega
              rw [hcongr]; exact hmid_rev
            obtain ⟨h, h0r, hlastr, hLr, hadj_r⟩ := list_color_even_chain F t c m hm es_rev zs_rev
              hnodup_rev hlen_er hlen_zr hes_val_r
              (fun j hj => ht_even_r j (by omega)) (fun j hj => ht_odd_r j (by omega)) (c u') (c u)
              hαL_r hαR_r (Or.inr ⟨hm2, hmid_r⟩)
            have h0 : h (es[0]'(by omega)) = c u := by
              have hcongr : es[0]'(by omega) = es_rev[2 * m - 1]'(by omega) := by
                simp only [es_rev, List.getElem_reverse]; congr 1; omega
              rwa [hcongr]
            have hlast : h (es[2 * m - 1]'(by omega)) = c u' := by
              have hcongr : es[2 * m - 1]'(by omega) = es_rev[0]'(by omega) := by
                simp only [es_rev, List.getElem_reverse]; congr 1; omega
              rwa [hcongr]
            have hL : ∀ x ∈ es, h x ∈ edgeAllowed c t x.val := fun x hx =>
              hLr x (List.mem_reverse.mpr hx)
            have hadj_h : ∀ i (hi : i + 1 < 2 * m),
                h (es[i]'(by omega)) ≠ h (es[i + 1]'(by omega)) := by
              intro i hi
              let j := 2 * m - 1 - (i + 1)
              have h1 : es_rev[j]'(by omega) = es[i + 1]'(by omega) := by
                simp only [es_rev, List.getElem_reverse]; congr 1; omega
              have h2 : es_rev[j + 1]'(by omega) = es[i]'(by omega) := by
                simp only [es_rev, List.getElem_reverse]; congr 1; omega
              have har := hadj_r j (by omega)
              rw [h1, h2] at har
              exact har.symm
            exact hcheck_all h h0 hlast hL hadj_h

private lemma color_E'_component {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (fd : ∀ v, F.degree v ≤ 2)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (c : U → Fin 3) (hcS : ∀ x y, S.Adj x y → c x ≠ c y)
    (halt : ∀ (u v v' u' : U) (w : AltWalk F t u v v' u'),
      c u ≠ c u' ∨ ∃ (_ : 2 ≤ w.m),
        c (w.zs[2]'(by have := w.hlen; omega)) = c u ∨
        c (w.zs[2 * w.m - 2]'(by have := w.hlen; omega)) = c u')
    (es : List F.edgeSet) (isCyc : Bool)
    (hnodup : es.Nodup) (hne : es ≠ [])
    (hnonTT : ∀ e ∈ es, ¬ IsTT t e.val)
    (hcyc3 : isCyc = true → 3 ≤ es.length)
    (hpath_adj : isCyc = false → ∀ (i : ℕ) (hi : i + 1 < es.length), (LF F).Adj es[i] es[i + 1])
    (hpath_no : isCyc = false → ∀ (i j : ℕ) (hi : i < j) (hj : j < es.length),
      (LF F).Adj es[i] es[j] → i + 1 = j)
    (hcyc_adj : isCyc = true → ∀ (i : Fin es.length),
      (LF F).Adj es[i.val] (es[(i.val + 1) % es.length]'(Nat.mod_lt _ (Fin.pos i)))) :
    ∃ h : F.edgeSet → Fin 3,
      (∀ e ∈ es, h e ∈ edgeAllowed c t e.val) ∧
      (∀ e ∈ es, ∀ f : F.edgeSet, IsTT t f.val → (LF F).Adj e f → h e ≠ hTT t c f) ∧
      (∀ e ∈ es, ∀ f ∈ es, (LF F).Adj e f → h e ≠ h f) := by
  cases hisCyc : isCyc with
  | true =>
    exact color_E'_cycle F t fd c es hnodup (hcyc3 hisCyc) hnonTT (hcyc_adj hisCyc)
  | false =>
    exact color_E'_path S F t fd inside three c hcS halt es hnodup hne hnonTT
      (hpath_adj hisCyc) (hpath_no hisCyc)

lemma list_color_LF {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (fd : ∀ v, F.degree v ≤ 2)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (c : U → Fin 3)
    (hcS : ∀ x y, S.Adj x y → c x ≠ c y)
    (halt : ∀ (u v v' u' : U) (w : AltWalk F t u v v' u'),
      c u ≠ c u' ∨ ∃ (_ : 2 ≤ w.m),
        c (w.zs[2]'(by have := w.hlen; omega)) = c u ∨
        c (w.zs[2 * w.m - 2]'(by have := w.hlen; omega)) = c u') :
    ∃ h : F.edgeSet → Fin 3,
      (∀ e f, e ≠ f → (∃ v : U, v ∈ e.val ∧ v ∈ f.val) → h e ≠ h f) ∧
      (∀ v e, t v = true → v ∈ e.val → h e ≠ c v) := by
  let E' : Set F.edgeSet := {e | ¬ IsTT t e.val}
  let G' : SimpleGraph E' := (LF F).induce E'
  have hdeg' : ∀ x : E', G'.degree x ≤ 2 := fun x => by
    calc G'.degree x = (G'.neighborFinset x).card := (G'.card_neighborFinset_eq_degree x).symm
      _ ≤ ((LF F).neighborFinset x.val).card := by
          refine Finset.card_le_card_of_injOn Subtype.val (fun y hy => ?_)
            (fun _ _ _ _ h => Subtype.ext h)
          exact ((LF F).mem_neighborFinset _ _).mpr ((G'.mem_neighborFinset _ _).mp hy)
      _ = (LF F).degree x.val := (LF F).card_neighborFinset_eq_degree x.val
      _ ≤ 2 := LF_degree_le_two F fd x.val
  obtain ⟨P, hPdisj, hPcov, hPprop⟩ := decompose_graph_deg2 G' hdeg'
  have hcomp_exists : ∀ p : List E' × Bool, p ∈ P →
      ∃ h : F.edgeSet → Fin 3,
        (∀ e ∈ p.1.map Subtype.val, h e ∈ edgeAllowed c t e.val) ∧
        (∀ e ∈ p.1.map Subtype.val, ∀ f : F.edgeSet, IsTT t f.val → (LF F).Adj e f → h e ≠ hTT t c f) ∧
        (∀ e ∈ p.1.map Subtype.val, ∀ f ∈ p.1.map Subtype.val, (LF F).Adj e f → h e ≠ h f) := by
    intro p hp
    obtain ⟨hnodup, hne, hcyc3, _, hpath_adj, hpath_no, hcyc_adj⟩ := hPprop p hp
    refine color_E'_component S F t fd inside three c hcS halt (p.1.map Subtype.val) p.2
      (hnodup.map Subtype.val_injective) (fun h => hne (List.map_eq_nil_iff.mp h))
      (fun e he => by obtain ⟨e', _, rfl⟩ := List.mem_map.mp he; exact e'.2)
      (fun hc => by simp only [List.length_map]; exact hcyc3 hc)
      (fun hc i hi => by
        simp only [List.length_map] at hi
        simp only [List.getElem_map]
        exact hpath_adj hc i hi)
      (fun hc i j hij hj hadj => by
        simp only [List.length_map] at hj
        simp only [List.getElem_map] at hadj
        exact hpath_no hc i j hij hj hadj)
      (fun hc i => by
        have hlen : (p.1.map Subtype.val).length = p.1.length := List.length_map _
        have hi' : i.val < p.1.length := by rw [← hlen]; exact i.isLt
        simp only [List.getElem_map, hlen]
        exact hcyc_adj hc ⟨i.val, hi'⟩)
  let h_comp : (p : List E' × Bool) → F.edgeSet → Fin 3 := fun p =>
    if hp : p ∈ P then Classical.choose (hcomp_exists p hp) else fun _ => 0
  let compOf : E' → List E' × Bool := fun x => Classical.choose (hPcov x)
  have hcompOf_mem : ∀ x : E', compOf x ∈ P ∧ x ∈ (compOf x).1 := fun x =>
    Classical.choose_spec (hPcov x)
  let h : F.edgeSet → Fin 3 := fun e =>
    if he : IsTT t e.val then hTT t c e else h_comp (compOf ⟨e, he⟩) e
  have h_allowed : ∀ e : F.edgeSet, h e ∈ edgeAllowed c t e.val := by
    intro e
    by_cases he : IsTT t e.val
    · simp only [h, dif_pos he]
      exact (tt_edge_allowed_card_eq_one S F t c inside hcS e he).2
    · simp only [h, dif_neg he]
      have hc := hcompOf_mem ⟨e, he⟩
      simp only [h_comp, dif_pos hc.1]
      exact (Classical.choose_spec (hcomp_exists (compOf ⟨e, he⟩) hc.1)).1 e
        (List.mem_map.mpr ⟨⟨e, he⟩, hc.2, rfl⟩)
  refine ⟨h, fun e f hne hv => ?_, fun v e htv hve => ?_⟩
  · have hadj : (LF F).Adj e f := ⟨hne, hv⟩
    by_cases he : IsTT t e.val <;> by_cases hf : IsTT t f.val
    · exact absurd hadj (tt_edges_not_adj F t three he hf)
    · have hc := hcompOf_mem ⟨f, hf⟩
      simp only [h, dif_pos he, dif_neg hf, h_comp, dif_pos hc.1]
      exact ((Classical.choose_spec (hcomp_exists (compOf ⟨f, hf⟩) hc.1)).2.1 f
        (List.mem_map.mpr ⟨⟨f, hf⟩, hc.2, rfl⟩) e he hadj.symm).symm
    · have hc := hcompOf_mem ⟨e, he⟩
      simp only [h, dif_neg he, dif_pos hf, h_comp, dif_pos hc.1]
      exact (Classical.choose_spec (hcomp_exists (compOf ⟨e, he⟩) hc.1)).2.1 e
        (List.mem_map.mpr ⟨⟨e, he⟩, hc.2, rfl⟩) f hf hadj
    · have hce := hcompOf_mem ⟨e, he⟩
      have hcf := hcompOf_mem ⟨f, hf⟩
      have hf_in_ce : ⟨f, hf⟩ ∈ (compOf ⟨e, he⟩).1 := by
        by_contra hnot
        exact (hPprop (compOf ⟨e, he⟩) hce.1).2.2.2.1 ⟨e, he⟩ hce.2 ⟨f, hf⟩ hnot hadj
      have hp_eq : compOf ⟨e, he⟩ = compOf ⟨f, hf⟩ := by
        by_contra hpne
        obtain ⟨i, hi, heqi⟩ := List.getElem_of_mem hce.1
        obtain ⟨j, hj, heqj⟩ := List.getElem_of_mem hcf.1
        have hij : i ≠ j := fun h => hpne (by subst h; exact heqi.symm.trans heqj)
        have hdisj : Disjoint (P[i].1.toFinset) (P[j].1.toFinset) := by
          rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
          · have hp := List.pairwise_iff_getElem.mp hPdisj i j (by simpa using hi)
              (by simpa using hj) hlt
            simpa only [List.getElem_map] using hp
          · have hp := List.pairwise_iff_getElem.mp hPdisj j i (by simpa using hj)
              (by simpa using hi) hlt
            simpa only [List.getElem_map] using hp.symm
        have hx_i : ⟨f, hf⟩ ∈ P[i].1.toFinset := by rw [List.mem_toFinset, heqi]; exact hf_in_ce
        have hx_j : ⟨f, hf⟩ ∈ P[j].1.toFinset := by rw [List.mem_toFinset, heqj]; exact hcf.2
        exact (Finset.disjoint_left.mp hdisj hx_i) hx_j
      simp only [h, dif_neg he, dif_neg hf, ← hp_eq, h_comp, dif_pos hce.1]
      exact (Classical.choose_spec (hcomp_exists (compOf ⟨e, he⟩) hce.1)).2.2
        e (List.mem_map.mpr ⟨⟨e, he⟩, hce.2, rfl⟩)
        f (List.mem_map.mpr ⟨⟨f, hf⟩, hf_in_ce, rfl⟩) hadj
  · have hmem := h_allowed e
    simp only [edgeAllowed, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem v htv hve

end ListColorLF

/- Step 4: Resolve K4 components in (S|_T) ⊔ M_aux via square, and prove H2. -/

section Step4

private lemma altWalk_unique_zs {U : Type*} [Fintype U] (F : SimpleGraph U) (t : U → Bool)
    (fd : ∀ v, F.degree v ≤ 2)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    {x₁ x₂ y₁ y₂ v₁ v₁' v₂ v₂' : U} (hx : x₁ = x₂)
    (w₁ : AltWalk F t x₁ v₁ v₁' y₁) (w₂ : AltWalk F t x₂ v₂ v₂' y₂) :
    w₁.m = w₂.m ∧
      ∀ (i : ℕ) (_hi : i ≤ 2 * w₁.m) (hi₁ : i < w₁.zs.length) (hi₂ : i < w₂.zs.length),
        w₁.zs[i] = w₂.zs[i] := by
  subst hx
  have hm₁ := w₁.hm
  have hl₁ := w₁.hlen
  have hm₂ := w₂.hm
  have hl₂ := w₂.hlen
  have hv_eq : v₁ = v₂ := by
    by_contra hne
    have hv₁t : t v₁ = true := by rw [← w₁.hstart]; exact w₁.ht_even 0 (by omega)
    have hv₂t : t v₂ = true := by rw [← w₂.hstart]; exact w₂.ht_even 0 (by omega)
    exact three v₁ x₁ v₂ hne w₁.hadj_u.symm w₂.hadj_u ⟨hv₁t, w₁.htu, hv₂t⟩
  have hprefix : ∀ i : ℕ, i ≤ 2 * w₁.m → i ≤ 2 * w₂.m →
      ∀ (hi₁ : i < w₁.zs.length) (hi₂ : i < w₂.zs.length), w₁.zs[i] = w₂.zs[i] := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi₁m hi₂m hi₁ hi₂
      match i with
      | 0 => rw [w₁.hstart, w₂.hstart, hv_eq]
      | 1 =>
        have hprev : w₁.zs[0] = w₂.zs[0] := ih 0 (by omega) (by omega) (by omega) (by omega) (by omega)
        have hadj₁ : F.Adj w₁.zs[0] w₁.zs[1] := w₁.hadj_zs 0 hi₁
        have hadj₂ : F.Adj w₁.zs[0] w₂.zs[1] := by rw [hprev]; exact w₂.hadj_zs 0 hi₂
        have h1ne : w₁.zs[1] ≠ x₁ := by
          intro h
          have ht1 := w₁.ht_odd 0 (by omega)
          rw [h, w₁.htu] at ht1
          cases ht1
        have h2ne : w₂.zs[1] ≠ x₁ := by
          intro h
          have ht2 := w₂.ht_odd 0 (by omega)
          rw [h, w₁.htu] at ht2
          cases ht2
        have hxadj : F.Adj w₁.zs[0] x₁ := by rw [w₁.hstart]; exact w₁.hadj_u.symm
        by_contra hne
        have hsub : ({x₁, w₁.zs[1], w₂.zs[1]} : Finset U) ⊆ F.neighborFinset w₁.zs[0] := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact (F.mem_neighborFinset _ _).mpr hxadj
          · exact (F.mem_neighborFinset _ _).mpr hadj₁
          · exact (F.mem_neighborFinset _ _).mpr hadj₂
        have hc1 : x₁ ∉ ({w₁.zs[1], w₂.zs[1]} : Finset U) := by simp [h1ne.symm, h2ne.symm]
        have hc2 : w₁.zs[1] ∉ ({w₂.zs[1]} : Finset U) := by simp [hne]
        have h3 : 3 ≤ F.degree w₁.zs[0] := by
          calc 3 = ({x₁, w₁.zs[1], w₂.zs[1]} : Finset U).card := by
                rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
                  Finset.card_singleton]
            _ ≤ (F.neighborFinset w₁.zs[0]).card := Finset.card_le_card hsub
            _ = F.degree w₁.zs[0] := F.card_neighborFinset_eq_degree _
        have := fd w₁.zs[0]
        omega
      | k + 2 =>
        have hprev_eq : w₁.zs[k] = w₂.zs[k] :=
          ih k (by omega) (by omega) (by omega) (by omega) (by omega)
        have hmid_eq : w₁.zs[k + 1] = w₂.zs[k + 1] :=
          ih (k + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
        have hadj₁ : F.Adj w₁.zs[k + 1] w₁.zs[k + 2] := w₁.hadj_zs (k + 1) hi₁
        have hadj₂ : F.Adj w₁.zs[k + 1] w₂.zs[k + 2] := by
          rw [hmid_eq]; exact w₂.hadj_zs (k + 1) hi₂
        have hadj_prev : F.Adj w₁.zs[k + 1] w₁.zs[k] := (w₁.hadj_zs k (by omega)).symm
        have h1ne : w₁.zs[k + 2] ≠ w₁.zs[k] := by
          intro h
          have hinj := w₁.hnodup.getElem_inj_iff.mp h
          omega
        have h2ne : w₂.zs[k + 2] ≠ w₁.zs[k] := by
          intro h
          rw [hprev_eq] at h
          have hinj := w₂.hnodup.getElem_inj_iff.mp h
          omega
        by_contra hne
        have hsub : ({w₁.zs[k], w₁.zs[k + 2], w₂.zs[k + 2]} : Finset U) ⊆
            F.neighborFinset w₁.zs[k + 1] := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl | rfl
          · exact (F.mem_neighborFinset _ _).mpr hadj_prev
          · exact (F.mem_neighborFinset _ _).mpr hadj₁
          · exact (F.mem_neighborFinset _ _).mpr hadj₂
        have hc1 : w₁.zs[k] ∉ ({w₁.zs[k + 2], w₂.zs[k + 2]} : Finset U) := by
          simp [h1ne.symm, h2ne.symm]
        have hc2 : w₁.zs[k + 2] ∉ ({w₂.zs[k + 2]} : Finset U) := by simp [hne]
        have h3 : 3 ≤ F.degree w₁.zs[k + 1] := by
          calc 3 = ({w₁.zs[k], w₁.zs[k + 2], w₂.zs[k + 2]} : Finset U).card := by
                rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
                  Finset.card_singleton]
            _ ≤ (F.neighborFinset w₁.zs[k + 1]).card := Finset.card_le_card hsub
            _ = F.degree w₁.zs[k + 1] := F.card_neighborFinset_eq_degree _
        have := fd w₁.zs[k + 1]
        omega
  have hm_eq : w₁.m = w₂.m := by
    by_contra hne
    have hlt : w₁.m < w₂.m ∨ w₂.m < w₁.m := Nat.lt_or_gt.mp hne
    have aux : ∀ (u₁ u₂ : U) (a₁ a₁' b₁ b₂' : U)
        (wa : AltWalk F t x₁ a₁ a₁' u₁) (wb : AltWalk F t x₁ b₁ b₂' u₂),
        wa.m < wb.m →
        (∀ i ≤ 2 * wa.m, ∀ (hi₁ : i < wa.zs.length) (hi₂ : i < wb.zs.length),
          wa.zs[i] = wb.zs[i]) → False := by
      intro u₁ _ a₁ a₁' b₁ b₂' wa wb hlt' hpre
      have hma := wa.hm
      have hla := wa.hlen
      have hlb := wb.hlen
      have heq := hpre (2 * wa.m) (le_refl _) (by omega) (by omega)
      have hp1 : F.Adj (wb.zs[2 * wa.m]'(by omega)) (wb.zs[2 * wa.m - 1]'(by omega)) := by
        have := wb.hadj_zs (2 * wa.m - 1) (by omega)
        have hidx : 2 * wa.m - 1 + 1 = 2 * wa.m := by omega
        simp only [hidx] at this
        exact this.symm
      have hp2 : F.Adj (wb.zs[2 * wa.m]'(by omega)) (wb.zs[2 * wa.m + 1]'(by omega)) :=
        wb.hadj_zs (2 * wa.m) (by omega)
      have hp3 : F.Adj (wb.zs[2 * wa.m]'(by omega)) u₁ := by
        rw [← heq, wa.hend]; exact wa.hadj_u'
      have h12 : wb.zs[2 * wa.m - 1]'(by omega) ≠ wb.zs[2 * wa.m + 1]'(by omega) := fun h => by
        have := wb.hnodup.getElem_inj_iff.mp h; omega
      have h13 : wb.zs[2 * wa.m - 1]'(by omega) ≠ u₁ := fun h => by
        have ht := wb.ht_odd (wa.m - 1) (by omega)
        have hidx : 2 * (wa.m - 1) + 1 = 2 * wa.m - 1 := by omega
        simp only [hidx] at ht
        rw [h, wa.htu'] at ht
        cases ht
      have h23 : wb.zs[2 * wa.m + 1]'(by omega) ≠ u₁ := fun h => by
        have ht := wb.ht_odd wa.m (by omega)
        rw [h, wa.htu'] at ht
        cases ht
      have hsub : ({wb.zs[2 * wa.m - 1]'(by omega), wb.zs[2 * wa.m + 1]'(by omega), u₁} : Finset U) ⊆
          F.neighborFinset (wb.zs[2 * wa.m]'(by omega)) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> exact (F.mem_neighborFinset _ _).mpr (by assumption)
      have hc1 : wb.zs[2 * wa.m - 1]'(by omega) ∉
          ({wb.zs[2 * wa.m + 1]'(by omega), u₁} : Finset U) := by
        simp [h12, h13]
      have hc2 : wb.zs[2 * wa.m + 1]'(by omega) ∉ ({u₁} : Finset U) := by simp [h23]
      have h3 : 3 ≤ F.degree (wb.zs[2 * wa.m]'(by omega)) := by
        calc 3 = ({wb.zs[2 * wa.m - 1]'(by omega), wb.zs[2 * wa.m + 1]'(by omega), u₁} :
              Finset U).card := by
              rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
                Finset.card_singleton]
          _ ≤ (F.neighborFinset _).card := Finset.card_le_card hsub
          _ = F.degree _ := F.card_neighborFinset_eq_degree _
      have := fd (wb.zs[2 * wa.m]'(by omega))
      omega
    rcases hlt with h12 | h21
    · exact aux y₁ y₂ v₁ v₁' v₂ v₂' w₁ w₂ h12 (fun i hi hi1 hi2 => hprefix i hi (by omega) hi1 hi2)
    · exact aux y₂ y₁ v₂ v₂' v₁ v₁' w₂ w₁ h21 (fun i hi hi1 hi2 => (hprefix i (by omega) hi hi2 hi1).symm)
  exact ⟨hm_eq, fun i hi hi₁ hi₂ => hprefix i hi (hm_eq ▸ hi) hi₁ hi₂⟩

private structure K4Witness {U : Type*} (S F : SimpleGraph U) (t : U → Bool)
    (K : Finset {v : U // t v = true}) where
  s : Fin 4 ↪ {v : U // t v = true}
  v₀ : U
  v₂' : U
  w : AltWalk F t (s 0).val v₀ v₂' (s 2).val
  hmem : ∀ x : {v : U // t v = true}, x ∈ K ↔ x = s 0 ∨ x = s 1 ∨ x = s 2 ∨ x = s 3
  hS : ∀ i : Fin 4, (S.induce {v : U | t v = true}).Adj (s i) (s (i + 1))
  hnS02 : ¬ (S.induce {v : U | t v = true}).Adj (s 0) (s 2)
  hnS13 : ¬ (S.induce {v : U | t v = true}).Adj (s 1) (s 3)
  hM02 : (M_aux F t).Adj (s 0) (s 2)
  hM13 : (M_aux F t).Adj (s 1) (s 3)
  hm2 : 2 ≤ w.m

private lemma k4_component_witness {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (square : ∀ s : Fin 4 ↪ U, (∀ i, t (s i) = true) → (∀ i, S.Adj (s i) (s (i+1))) →
      (∀ i, F.Adj (s i) (s (i+1)) ∨ F.Adj (s i) (s (i+3))) →
      ∀ x y, t x = false → t y = false → F.Adj (s 0) x → F.Adj (s 2) x →
        F.Adj (s 1) y → F.Adj (s 3) y → False)
    (K : Finset {v : U // t v = true})
    (hKcard : K.card = 4)
    (hKclique : ((S.induce {v : U | t v = true}) ⊔ M_aux F t).IsClique (K : Set {v : U // t v = true})) :
    Nonempty (K4Witness S F t K) := by
  let T := {v : U // t v = true}
  let S_T : SimpleGraph T := S.induce {v : U | t v = true}
  let M : SimpleGraph T := M_aux F t
  let G_T : SimpleGraph T := S_T ⊔ M
  have hS_deg : ∀ x : T, S_T.degree x ≤ 2 := ind_degree_le S 2 sd {v : U | t v = true}
  have hM_deg : ∀ x : T, M.degree x ≤ 1 := M_aux_degree_le_one F t fd three
  have hK_deg : ∀ x ∈ K, S_T.degree x = 2 ∧ M.degree x = 1 ∧
      S_T.neighborFinset x ⊆ K.erase x ∧ M.neighborFinset x ⊆ K.erase x ∧
      Disjoint (S_T.neighborFinset x) (M.neighborFinset x) ∧
      G_T.neighborFinset x = K.erase x := by
    intro x hx
    have hsub : K.erase x ⊆ G_T.neighborFinset x := by
      intro y hy
      obtain ⟨hyx, hyK⟩ := Finset.mem_erase.mp hy
      exact (G_T.mem_neighborFinset _ _).mpr (hKclique hx hyK hyx.symm)
    have hgunion : G_T.neighborFinset x = S_T.neighborFinset x ∪ M.neighborFinset x := by
      ext y
      simp only [G_T, SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, Finset.mem_union]
    have h3 : 3 ≤ G_T.degree x := by
      calc 3 = (K.erase x).card := by rw [Finset.card_erase_of_mem hx, hKcard]
        _ ≤ (G_T.neighborFinset x).card := Finset.card_le_card hsub
        _ = G_T.degree x := G_T.card_neighborFinset_eq_degree x
    have hsum : G_T.degree x ≤ S_T.degree x + M.degree x := by
      calc G_T.degree x = (G_T.neighborFinset x).card := (G_T.card_neighborFinset_eq_degree x).symm
        _ = (S_T.neighborFinset x ∪ M.neighborFinset x).card := by rw [hgunion]
        _ ≤ (S_T.neighborFinset x).card + (M.neighborFinset x).card := Finset.card_union_le _ _
        _ = S_T.degree x + M.degree x := by
            rw [S_T.card_neighborFinset_eq_degree x, M.card_neighborFinset_eq_degree x]
    have hSx := hS_deg x
    have hMx := hM_deg x
    have hS2 : S_T.degree x = 2 := by omega
    have hM1 : M.degree x = 1 := by omega
    have hG3 : G_T.degree x = 3 := by omega
    have hG_eq : G_T.neighborFinset x = K.erase x :=
      (Finset.eq_of_subset_of_card_le hsub (by
        rw [G_T.card_neighborFinset_eq_degree x, hG3, Finset.card_erase_of_mem hx, hKcard])).symm
    have hS_sub : S_T.neighborFinset x ⊆ K.erase x := by
      rw [← hG_eq, hgunion]; exact Finset.subset_union_left
    have hM_sub : M.neighborFinset x ⊆ K.erase x := by
      rw [← hG_eq, hgunion]; exact Finset.subset_union_right
    have hdisj : Disjoint (S_T.neighborFinset x) (M.neighborFinset x) := by
      by_contra hnot
      have hcard_lt : (S_T.neighborFinset x ∪ M.neighborFinset x).card <
          (S_T.neighborFinset x).card + (M.neighborFinset x).card := by
        have hsum_inter := Finset.card_union_add_card_inter (S_T.neighborFinset x) (M.neighborFinset x)
        have hpos : 0 < (S_T.neighborFinset x ∩ M.neighborFinset x).card := by
          rw [Finset.card_pos]
          exact Finset.not_disjoint_iff_nonempty_inter.mp hnot
        omega
      rw [← hgunion, G_T.card_neighborFinset_eq_degree x, hG3,
        S_T.card_neighborFinset_eq_degree x, M.card_neighborFinset_eq_degree x, hS2, hM1] at hcard_lt
      omega
    exact ⟨hS2, hM1, hS_sub, hM_sub, hdisj, hG_eq⟩
  obtain ⟨a, haK⟩ := Finset.card_pos.mp (by omega : 0 < K.card)
  obtain ⟨haS, _, haSsub, _, _, _⟩ := hK_deg a haK
  have haS_card : (S_T.neighborFinset a).card = 2 := by
    rw [S_T.card_neighborFinset_eq_degree a, haS]
  obtain ⟨b, d, hbd, hSa_eq⟩ := Finset.card_eq_two.mp haS_card
  have hbKa : b ∈ K.erase a := haSsub (hSa_eq ▸ Finset.mem_insert_self _ _)
  have hdKa : d ∈ K.erase a := haSsub (hSa_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hba : b ≠ a := (Finset.mem_erase.mp hbKa).1
  have hda : d ≠ a := (Finset.mem_erase.mp hdKa).1
  have hbK : b ∈ K := (Finset.mem_erase.mp hbKa).2
  have hdK : d ∈ K := (Finset.mem_erase.mp hdKa).2
  have hrem_card : (((K.erase a).erase b).erase d).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hbd.symm, hdKa⟩),
      Finset.card_erase_of_mem hbKa, Finset.card_erase_of_mem haK, hKcard]
  obtain ⟨c, hc_mem⟩ := Finset.card_eq_one.mp hrem_card
  have hc_in : c ∈ ((K.erase a).erase b).erase d := hc_mem ▸ Finset.mem_singleton_self c
  have hcd : c ≠ d := (Finset.mem_erase.mp hc_in).1
  have hcb : c ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hc_in).2).1
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hc_in).2).2).1
  have hcK : c ∈ K := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hc_in).2).2).2
  have hK_eq : K = {a, b, c, d} := by
    refine (Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    · have h1 : a ∉ ({b, c, d} : Finset T) := by simp [hba.symm, hca.symm, hda.symm]
      have h2 : b ∉ ({c, d} : Finset T) := by simp [hcb.symm, hbd]
      have h3 : c ∉ ({d} : Finset T) := by simp [hcd]
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_singleton, hKcard]
  have hab_adj : S_T.Adj a b := (S_T.mem_neighborFinset _ _).mp (hSa_eq ▸ Finset.mem_insert_self _ _)
  have had_adj : S_T.Adj a d := (S_T.mem_neighborFinset _ _).mp
    (hSa_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hac_not : ¬ S_T.Adj a c := by
    intro h
    have hmem : c ∈ S_T.neighborFinset a := (S_T.mem_neighborFinset _ _).mpr h
    rw [hSa_eq] at hmem
    simp [hcb, hcd] at hmem
  obtain ⟨hcS, _, hcSsub, _, _, _⟩ := hK_deg c hcK
  have hcS_sub : S_T.neighborFinset c ⊆ {b, d} := by
    intro z hz
    have hzk := hcSsub hz
    rw [hK_eq] at hzk
    have hza : z ≠ a := fun h => hac_not ((S_T.mem_neighborFinset _ _).mp (h ▸ hz)).symm
    have hzc : z ≠ c := (Finset.mem_erase.mp hzk).1
    have hzm := (Finset.mem_erase.mp hzk).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzm ⊢
    rcases hzm with rfl | rfl | rfl | rfl
    · exact absurd rfl hza
    · exact Or.inl rfl
    · exact absurd rfl hzc
    · exact Or.inr rfl
  have hcS_eq : S_T.neighborFinset c = {b, d} :=
    Finset.eq_of_subset_of_card_le hcS_sub (by
      rw [Finset.card_pair hbd, S_T.card_neighborFinset_eq_degree c, hcS])
  have hcb_adj : S_T.Adj c b := (S_T.mem_neighborFinset _ _).mp (hcS_eq ▸ Finset.mem_insert_self _ _)
  have hcd_adj : S_T.Adj c d := (S_T.mem_neighborFinset _ _).mp
    (hcS_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨hbS, _, _, _, _, _⟩ := hK_deg b hbK
  have hbS_sub : {a, c} ⊆ S_T.neighborFinset b := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (S_T.mem_neighborFinset _ _).mpr hab_adj.symm
    · exact (S_T.mem_neighborFinset _ _).mpr hcb_adj.symm
  have hbS_eq : S_T.neighborFinset b = {a, c} :=
    (Finset.eq_of_subset_of_card_le hbS_sub (by
      rw [S_T.card_neighborFinset_eq_degree b, hbS, Finset.card_pair hca.symm])).symm
  have hbd_not : ¬ S_T.Adj b d := by
    intro h
    have hmem : d ∈ S_T.neighborFinset b := (S_T.mem_neighborFinset _ _).mpr h
    rw [hbS_eq] at hmem
    simp [hda, hcd.symm] at hmem
  have hMac : M.Adj a c := (hKclique haK hcK hca.symm).resolve_left hac_not
  have hMbd : M.Adj b d := (hKclique hbK hdK hbd).resolve_left hbd_not
  let sFun : Fin 4 → T := fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d
  have hsInj : Function.Injective sFun := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [sFun] at hij ⊢
    all_goals first | exact absurd hij hba.symm | exact absurd hij hca.symm |
      exact absurd hij hda.symm | exact absurd hij hba | exact absurd hij hcb.symm |
      exact absurd hij hbd | exact absurd hij hca | exact absurd hij hcb |
      exact absurd hij hcd | exact absurd hij hda | exact absurd hij hbd.symm |
      exact absurd hij hcd.symm
  let s : Fin 4 ↪ T := ⟨sFun, hsInj⟩
  have hS_cyc : ∀ i : Fin 4, S_T.Adj (s i) (s (i + 1)) := by
    intro i; fin_cases i
    · exact hab_adj
    · exact hcb_adj.symm
    · exact hcd_adj
    · exact had_adj.symm
  obtain ⟨_, v₀, v₂', ⟨w₀₂⟩⟩ := id hMac
  obtain ⟨_, v₁, v₃', ⟨w₁₃⟩⟩ := id hMbd
  have hv₀_in : v₀ = b.val ∨ v₀ = d.val := by
    have hSv₀ : S.Adj a.val v₀ := inside a.val v₀ w₀₂.hadj_u a.2
      (by rw [← w₀₂.hstart]; exact w₀₂.ht_even 0 (by have := w₀₂.hlen; omega))
    have hmem : (⟨v₀, by rw [← w₀₂.hstart]; exact w₀₂.ht_even 0 (by have := w₀₂.hlen; omega)⟩ : T) ∈
        S_T.neighborFinset a := (S_T.mem_neighborFinset _ _).mpr hSv₀
    rw [hSa_eq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
    exact hmem
  have hv₂'_in : v₂' = b.val ∨ v₂' = d.val := by
    have hSv₂' : S.Adj v₂' c.val := inside v₂' c.val w₀₂.hadj_u'
      (by rw [← w₀₂.hend]; exact w₀₂.ht_even w₀₂.m (by have := w₀₂.hlen; omega)) c.2
    have hmem : (⟨v₂', by rw [← w₀₂.hend]; exact w₀₂.ht_even w₀₂.m (by have := w₀₂.hlen; omega)⟩ : T) ∈
        S_T.neighborFinset c := (S_T.mem_neighborFinset _ _).mpr hSv₂'.symm
    rw [hcS_eq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
    exact hmem
  have hv₀_ne_v₂' : v₀ ≠ v₂' := fun h => by
    have hl := w₀₂.hlen
    have hm := w₀₂.hm
    have h0' : w₀₂.zs[0]'(by omega) = v₀ := w₀₂.hstart
    have hend' : w₀₂.zs[2 * w₀₂.m]'(by omega) = v₂' := w₀₂.hend
    have heq_zs : w₀₂.zs[0]'(by omega) = w₀₂.zs[2 * w₀₂.m]'(by omega) :=
      h0'.trans (h.trans hend'.symm)
    have := w₀₂.hnodup.getElem_inj_iff.mp heq_zs
    omega
  have hv₁_in : v₁ = a.val ∨ v₁ = c.val := by
    have hSv₁ : S.Adj b.val v₁ := inside b.val v₁ w₁₃.hadj_u b.2
      (by rw [← w₁₃.hstart]; exact w₁₃.ht_even 0 (by have := w₁₃.hlen; omega))
    have hmem : (⟨v₁, by rw [← w₁₃.hstart]; exact w₁₃.ht_even 0 (by have := w₁₃.hlen; omega)⟩ : T) ∈
        S_T.neighborFinset b := (S_T.mem_neighborFinset _ _).mpr hSv₁
    rw [hbS_eq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
    exact hmem
  have hv₃'_in : v₃' = a.val ∨ v₃' = c.val := by
    have hSv₃' : S.Adj v₃' d.val := inside v₃' d.val w₁₃.hadj_u'
      (by rw [← w₁₃.hend]; exact w₁₃.ht_even w₁₃.m (by have := w₁₃.hlen; omega)) d.2
    have hmem : (⟨v₃', by rw [← w₁₃.hend]; exact w₁₃.ht_even w₁₃.m (by have := w₁₃.hlen; omega)⟩ : T) ∈
        S_T.neighborFinset d := (S_T.mem_neighborFinset _ _).mpr hSv₃'.symm
    obtain ⟨hdS, _, _, _, _, _⟩ := hK_deg d hdK
    have hdS_sub : {a, c} ⊆ S_T.neighborFinset d := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (S_T.mem_neighborFinset _ _).mpr had_adj.symm
      · exact (S_T.mem_neighborFinset _ _).mpr hcd_adj.symm
    have hdS_eq : S_T.neighborFinset d = {a, c} :=
      (Finset.eq_of_subset_of_card_le hdS_sub (by
        rw [S_T.card_neighborFinset_eq_degree d, hdS, Finset.card_pair hca.symm])).symm
    rw [hdS_eq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.ext_iff] at hmem
    exact hmem
  have hv₁_ne_v₃' : v₁ ≠ v₃' := fun h => by
    have hl := w₁₃.hlen
    have hm := w₁₃.hm
    have h0' : w₁₃.zs[0]'(by omega) = v₁ := w₁₃.hstart
    have hend' : w₁₃.zs[2 * w₁₃.m]'(by omega) = v₃' := w₁₃.hend
    have heq_zs : w₁₃.zs[0]'(by omega) = w₁₃.zs[2 * w₁₃.m]'(by omega) :=
      h0'.trans (h.trans hend'.symm)
    have := w₁₃.hnodup.getElem_inj_iff.mp heq_zs
    omega
  have hF_cond : ∀ i : Fin 4, F.Adj (s i).val (s (i + 1)).val ∨ F.Adj (s i).val (s (i + 3)).val := by
    intro i
    fin_cases i
    · rcases hv₀_in with h | h
      · exact Or.inl (h ▸ w₀₂.hadj_u)
      · exact Or.inr (h ▸ w₀₂.hadj_u)
    · rcases hv₁_in with h | h
      · exact Or.inr (h ▸ w₁₃.hadj_u)
      · exact Or.inl (h ▸ w₁₃.hadj_u)
    · rcases hv₂'_in with h | h
      · exact Or.inr (h ▸ w₀₂.hadj_u'.symm)
      · exact Or.inl (h ▸ w₀₂.hadj_u'.symm)
    · rcases hv₃'_in with h | h
      · exact Or.inl (h ▸ w₁₃.hadj_u'.symm)
      · exact Or.inr (h ▸ w₁₃.hadj_u'.symm)
  have hm_ge2 : 2 ≤ w₀₂.m ∨ 2 ≤ w₁₃.m := by
    by_contra hnot
    push Not at hnot
    have hm02 : w₀₂.m = 1 := by have := w₀₂.hm; omega
    have hm13 : w₁₃.m = 1 := by have := w₁₃.hm; omega
    let x := w₁₃.zs[1]'(by have := w₁₃.hlen; omega)
    let y := w₀₂.zs[1]'(by have := w₀₂.hlen; omega)
    have htx : t x = false := w₁₃.ht_odd 0 (by have := w₁₃.hlen; omega)
    have hty : t y = false := w₀₂.ht_odd 0 (by have := w₀₂.hlen; omega)
    have hfx1 : F.Adj v₁ x := by
      have h := w₁₃.hadj_zs 0 (by have := w₁₃.hlen; omega)
      rwa [w₁₃.hstart] at h
    have hfx2 : F.Adj v₃' x := by
      have h := w₁₃.hadj_zs 1 (by have := w₁₃.hlen; omega)
      have hcongr : w₁₃.zs[1 + 1]'(by have := w₁₃.hlen; omega) =
          w₁₃.zs[2 * w₁₃.m]'(by have := w₁₃.hlen; omega) := by congr 1; omega
      rw [hcongr, w₁₃.hend] at h
      exact h.symm
    have hfy1 : F.Adj v₀ y := by
      have h := w₀₂.hadj_zs 0 (by have := w₀₂.hlen; omega)
      rwa [w₀₂.hstart] at h
    have hfy2 : F.Adj v₂' y := by
      have h := w₀₂.hadj_zs 1 (by have := w₀₂.hlen; omega)
      have hcongr : w₀₂.zs[1 + 1]'(by have := w₀₂.hlen; omega) =
          w₀₂.zs[2 * w₀₂.m]'(by have := w₀₂.hlen; omega) := by congr 1; omega
      rw [hcongr, w₀₂.hend] at h
      exact h.symm
    have hfa : F.Adj a.val x := by
      rcases hv₁_in with h1 | h1 <;> rcases hv₃'_in with h3 | h3
      · exact absurd (h1.trans h3.symm) hv₁_ne_v₃'
      · exact h1 ▸ hfx1
      · exact h3 ▸ hfx2
      · exact absurd (h1.trans h3.symm) hv₁_ne_v₃'
    have hfc : F.Adj c.val x := by
      rcases hv₁_in with h1 | h1 <;> rcases hv₃'_in with h3 | h3
      · exact absurd (h1.trans h3.symm) hv₁_ne_v₃'
      · exact h3 ▸ hfx2
      · exact h1 ▸ hfx1
      · exact absurd (h1.trans h3.symm) hv₁_ne_v₃'
    have hfb : F.Adj b.val y := by
      rcases hv₀_in with h0 | h0 <;> rcases hv₂'_in with h2 | h2
      · exact absurd (h0.trans h2.symm) hv₀_ne_v₂'
      · exact h0 ▸ hfy1
      · exact h2 ▸ hfy2
      · exact absurd (h0.trans h2.symm) hv₀_ne_v₂'
    have hfd : F.Adj d.val y := by
      rcases hv₀_in with h0 | h0 <;> rcases hv₂'_in with h2 | h2
      · exact absurd (h0.trans h2.symm) hv₀_ne_v₂'
      · exact h2 ▸ hfy2
      · exact h0 ▸ hfy1
      · exact absurd (h0.trans h2.symm) hv₀_ne_v₂'
    exact square (s.trans ⟨Subtype.val, Subtype.val_injective⟩)
      (fun i => (s i).2) (fun i => hS_cyc i) hF_cond x y htx hty hfa hfc hfb hfd
  rcases hm_ge2 with hm02 | hm13
  · exact ⟨{
      s := s
      v₀ := v₀
      v₂' := v₂'
      w := w₀₂
      hmem := fun x => by
        rw [hK_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton, s, sFun, Function.Embedding.coeFn_mk]
      hS := hS_cyc
      hnS02 := hac_not
      hnS13 := hbd_not
      hM02 := hMac
      hM13 := hMbd
      hm2 := hm02
    }⟩
  · let s' : Fin 4 ↪ T := ⟨fun i => s (i + 1), fun i j h => by
      have := s.injective h; exact add_right_cancel this⟩
    exact ⟨{
      s := s'
      v₀ := v₁
      v₂' := v₃'
      w := w₁₃
      hmem := fun x => by
        rw [hK_eq]
        simp only [Finset.mem_insert, Finset.mem_singleton, s', s, sFun, Function.Embedding.coeFn_mk]
        constructor
        · rintro (rfl | rfl | rfl | rfl)
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
        · rintro (rfl | rfl | rfl | rfl)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
          · exact Or.inl rfl
      hS := fun i => hS_cyc (i + 1)
      hnS02 := hbd_not
      hnS13 := fun h => hac_not h.symm
      hM02 := hMbd
      hM13 := hMac.symm
      hm2 := hm13
    }⟩

private lemma fin3_add_ne (α : Fin 3) : α ≠ α + 1 ∧ α ≠ α + 2 ∧ α + 1 ≠ α + 2 := by
  fin_cases α <;> decide

private lemma k4_mem_of_adj {T : Type*} [DecidableEq T]
    (G_T : SimpleGraph T)
    (hadj_card : ∀ x : T, ∀ s : Finset T, (∀ y ∈ s, G_T.Adj x y) → s.card ≤ 3)
    (K : Finset T) (hKc : K.card = 4) (hKcl : G_T.IsClique (K : Set T))
    {x y : T} (hx : x ∈ K) (hadj : G_T.Adj x y) : y ∈ K := by
  by_contra hyK
  have hsub : ∀ z ∈ insert y (K.erase x), G_T.Adj x z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz'
    · exact hadj
    · obtain ⟨hzx, hzK⟩ := Finset.mem_erase.mp hz'
      exact hKcl hx hzK hzx.symm
  have hy_not : y ∉ K.erase x := fun h => hyK (Finset.mem_erase.mp h).2
  have h4 : (insert y (K.erase x)).card = 4 := by
    rw [Finset.card_insert_of_notMem hy_not, Finset.card_erase_of_mem hx, hKc]
  have := hadj_card x (insert y (K.erase x)) hsub
  omega

private lemma k4_card_eq_four_insert {T : Type*} [DecidableEq T]
    (G_T : SimpleGraph T)
    (hadj_card : ∀ x : T, ∀ s : Finset T, (∀ y ∈ s, G_T.Adj x y) → s.card ≤ 3)
    (K : Finset T) (hKc : K.card = 4) (hKcl : G_T.IsClique (K : Set T))
    {x : T} (hx : x ∈ K) (N : Finset T) (hN : ∀ z : T, z ∈ N ↔ G_T.Adj x z) :
    (insert x N).card = 4 ∧
    G_T.IsClique ((insert x N : Finset T) : Set T) ∧
    (∀ z : T, z ∈ insert x N ↔ z ∈ K) := by
  have heq : ∀ z : T, z ∈ insert x N ↔ z ∈ K := by
    intro z
    rw [Finset.mem_insert, hN z]
    constructor
    · rintro (rfl | hadj)
      · exact hx
      · exact k4_mem_of_adj G_T hadj_card K hKc hKcl hx hadj
    · intro hz
      by_cases hzx : z = x
      · exact Or.inl hzx
      · exact Or.inr (hKcl hx hz (Ne.symm hzx))
  have hset : insert x N = K := Finset.ext heq
  exact ⟨hset ▸ hKc, hset ▸ hKcl, heq⟩

private lemma z2_not_inK4_helper {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (u₀ u₂ v₀ v₂' : U) (w : AltWalk F t u₀ v₀ v₂' u₂) (hm2 : 2 ≤ w.m) :
    ¬ ∃ K : Finset {v : U // t v = true}, K.card = 4 ∧
      ((S.induce {v : U | t v = true}) ⊔ M_aux F t).IsClique (K : Set {v : U // t v = true}) ∧
      (⟨w.zs[2]'(by have := w.hlen; omega), w.ht_even 1 (by have := w.hlen; omega)⟩ :
        {v : U // t v = true}) ∈ K := by
  let T := {v : U // t v = true}
  let S_T : SimpleGraph T := S.induce {v : U | t v = true}
  let M : SimpleGraph T := M_aux F t
  let G_T : SimpleGraph T := S_T ⊔ M
  have hS_deg : ∀ x : T, S_T.degree x ≤ 2 := ind_degree_le S 2 sd {v : U | t v = true}
  have hM_deg : ∀ x : T, M.degree x ≤ 1 := M_aux_degree_le_one F t fd three
  have hGT_deg : ∀ x : T, G_T.degree x ≤ 3 := fun x => by
    have hgunion : G_T.neighborFinset x = S_T.neighborFinset x ∪ M.neighborFinset x := by
      ext y; simp only [G_T, SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, Finset.mem_union]
    calc G_T.degree x = (G_T.neighborFinset x).card := (G_T.card_neighborFinset_eq_degree x).symm
      _ = (S_T.neighborFinset x ∪ M.neighborFinset x).card := by rw [hgunion]
      _ ≤ (S_T.neighborFinset x).card + (M.neighborFinset x).card := Finset.card_union_le _ _
      _ = S_T.degree x + M.degree x := by
          rw [S_T.card_neighborFinset_eq_degree x, M.card_neighborFinset_eq_degree x]
      _ ≤ 3 := by have := hS_deg x; have := hM_deg x; omega
  rintro ⟨K, hKc, hKcl, hzK⟩
  let z₂T : T := ⟨w.zs[2]'(by have := w.hlen; omega), w.ht_even 1 (by have := w.hlen; omega)⟩
  have hM0 : M.degree z₂T = 0 := by
    by_contra hpos
    have hcard_pos : 0 < (M.neighborFinset z₂T).card := by
      rw [M.card_neighborFinset_eq_degree z₂T]; omega
    obtain ⟨y', hy'⟩ := Finset.card_pos.mp hcard_pos
    obtain ⟨_, v, _, ⟨w'⟩⟩ := (M.mem_neighborFinset _ _).mp hy'
    have htv : t v = true := by rw [← w'.hstart]; exact w'.ht_even 0 (by have := w'.hlen; omega)
    have hfz1 : F.Adj z₂T.val (w.zs[1]'(by have := w.hlen; omega)) :=
      (w.hadj_zs 1 (by have := w.hlen; omega)).symm
    have hfz3 : F.Adj z₂T.val (w.zs[3]'(by have := w.hlen; omega)) :=
      w.hadj_zs 2 (by have := w.hlen; omega)
    have h13 : w.zs[1]'(by have := w.hlen; omega) ≠ w.zs[3]'(by have := w.hlen; omega) := fun h => by
      have := w.hnodup.getElem_inj_iff.mp h; omega
    have hv1 : v ≠ w.zs[1]'(by have := w.hlen; omega) := fun h => by
      have hf := w.ht_odd 0 (by have := w.hlen; omega)
      rw [← h, htv] at hf; cases hf
    have hv3 : v ≠ w.zs[3]'(by have := w.hlen; omega) := fun h => by
      have hf := w.ht_odd 1 (by have := w.hlen; omega)
      rw [← h, htv] at hf; cases hf
    have hsub : ({v, w.zs[1]'(by have := w.hlen; omega), w.zs[3]'(by have := w.hlen; omega)} : Finset U) ⊆
        F.neighborFinset z₂T.val := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact (F.mem_neighborFinset _ _).mpr w'.hadj_u
      · exact (F.mem_neighborFinset _ _).mpr hfz1
      · exact (F.mem_neighborFinset _ _).mpr hfz3
    have hc1 : v ∉ ({w.zs[1]'(by have := w.hlen; omega), w.zs[3]'(by have := w.hlen; omega)} : Finset U) := by
      simp [hv1, hv3]
    have hc2 : w.zs[1]'(by have := w.hlen; omega) ∉ ({w.zs[3]'(by have := w.hlen; omega)} : Finset U) := by
      simp [h13]
    have h3 : 3 ≤ F.degree z₂T.val := by
      calc 3 = ({v, w.zs[1]'(by have := w.hlen; omega), w.zs[3]'(by have := w.hlen; omega)} : Finset U).card := by
            rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
              Finset.card_singleton]
        _ ≤ (F.neighborFinset z₂T.val).card := Finset.card_le_card hsub
        _ = F.degree z₂T.val := F.card_neighborFinset_eq_degree _
    have := fd z₂T.val
    omega
  have hgunion : G_T.neighborFinset z₂T = S_T.neighborFinset z₂T ∪ M.neighborFinset z₂T := by
    ext y; simp only [G_T, SimpleGraph.mem_neighborFinset, SimpleGraph.sup_adj, Finset.mem_union]
  have hG3 : 3 ≤ G_T.degree z₂T := by
    have hsub : K.erase z₂T ⊆ G_T.neighborFinset z₂T := fun y hy =>
      let ⟨hyz, hyK⟩ := Finset.mem_erase.mp hy
      (G_T.mem_neighborFinset _ _).mpr (hKcl hzK hyK hyz.symm)
    calc 3 = (K.erase z₂T).card := by rw [Finset.card_erase_of_mem hzK, hKc]
      _ ≤ (G_T.neighborFinset z₂T).card := Finset.card_le_card hsub
      _ = G_T.degree z₂T := G_T.card_neighborFinset_eq_degree z₂T
  have hle : G_T.degree z₂T ≤ S_T.degree z₂T + M.degree z₂T := by
    calc G_T.degree z₂T = (G_T.neighborFinset z₂T).card := (G_T.card_neighborFinset_eq_degree z₂T).symm
      _ = (S_T.neighborFinset z₂T ∪ M.neighborFinset z₂T).card := by rw [hgunion]
      _ ≤ (S_T.neighborFinset z₂T).card + (M.neighborFinset z₂T).card := Finset.card_union_le _ _
      _ = S_T.degree z₂T + M.degree z₂T := by
          rw [S_T.card_neighborFinset_eq_degree z₂T, M.card_neighborFinset_eq_degree z₂T]
  have := hS_deg z₂T
  omega

private lemma colorK_S_proper {U : Type*} (S F : SimpleGraph U) (t : U → Bool)
    {K : Finset {v : U // t v = true}} (W : K4Witness S F t K) (α : Fin 3)
    {x y : {v : U // t v = true}} (hx : x ∈ K) (hy : y ∈ K)
    (hadj : (S.induce {v : U | t v = true}).Adj x y) :
    (if x = W.s 0 ∨ x = W.s 2 then α else if x = W.s 1 then α + 1 else α + 2) ≠
    (if y = W.s 0 ∨ y = W.s 2 then α else if y = W.s 1 then α + 1 else α + 2) := by
  have hne3 := fin3_add_ne α
  by_cases hx02 : x = W.s 0 ∨ x = W.s 2 <;> by_cases hy02 : y = W.s 0 ∨ y = W.s 2
  · exfalso
    rcases hx02 with rfl | rfl <;> rcases hy02 with h | h
    · exact (S.induce _).loopless.irrefl _ (h ▸ hadj)
    · rw [h] at hadj; exact W.hnS02 hadj
    · rw [h] at hadj; exact W.hnS02 hadj.symm
    · exact (S.induce _).loopless.irrefl _ (h ▸ hadj)
  · rw [if_pos hx02, if_neg hy02]
    split_ifs
    · exact hne3.1
    · exact hne3.2.1
  · rw [if_neg hx02, if_pos hy02]
    split_ifs
    · exact hne3.1.symm
    · exact hne3.2.1.symm
  · exfalso
    have hx13 : x = W.s 1 ∨ x = W.s 3 := by
      rcases (W.hmem x).mp hx with h | h | h | h
      · exact absurd (Or.inl h) hx02
      · exact Or.inl h
      · exact absurd (Or.inr h) hx02
      · exact Or.inr h
    have hy13 : y = W.s 1 ∨ y = W.s 3 := by
      rcases (W.hmem y).mp hy with h | h | h | h
      · exact absurd (Or.inl h) hy02
      · exact Or.inl h
      · exact absurd (Or.inr h) hy02
      · exact Or.inr h
    rcases hx13 with rfl | rfl <;> rcases hy13 with h | h
    · exact (S.induce _).loopless.irrefl _ (h ▸ hadj)
    · rw [h] at hadj; exact W.hnS13 hadj
    · rw [h] at hadj; exact W.hnS13 hadj.symm
    · exact (S.induce _).loopless.irrefl _ (h ▸ hadj)

end Step4

private abbrev TVert {U : Type*} (t : U → Bool) := {v : U // t v = true}

private def G_T_graph {U : Type*} (S F : SimpleGraph U) (t : U → Bool) :
    SimpleGraph (TVert t) :=
  (S.induce {v : U | t v = true}) ⊔ M_aux F t

private def inK4 {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (x : TVert t) : Prop :=
  ∃ K : Finset (TVert t), K.card = 4 ∧ (G_T_graph S F t).IsClique (K : Set (TVert t)) ∧ x ∈ K

private lemma G_T_deg_le_three {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true)) :
    ∀ x : TVert t, (G_T_graph S F t).degree x ≤ 3 := by
  intro x
  have hS_deg : (S.induce {v : U | t v = true}).degree x ≤ 2 :=
    ind_degree_le S 2 sd {v : U | t v = true} x
  have hM_deg : (M_aux F t).degree x ≤ 1 := M_aux_degree_le_one F t fd three x
  have hgunion : (G_T_graph S F t).neighborFinset x =
      (S.induce {v : U | t v = true}).neighborFinset x ∪ (M_aux F t).neighborFinset x := by
    ext y
    rw [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    rfl
  calc (G_T_graph S F t).degree x
      = ((G_T_graph S F t).neighborFinset x).card :=
        ((G_T_graph S F t).card_neighborFinset_eq_degree x).symm
    _ = ((S.induce {v : U | t v = true}).neighborFinset x ∪ (M_aux F t).neighborFinset x).card := by
        rw [hgunion]
    _ ≤ ((S.induce {v : U | t v = true}).neighborFinset x).card +
        ((M_aux F t).neighborFinset x).card := Finset.card_union_le _ _
    _ = (S.induce {v : U | t v = true}).degree x + (M_aux F t).degree x := by
        rw [(S.induce {v : U | t v = true}).card_neighborFinset_eq_degree x,
          (M_aux F t).card_neighborFinset_eq_degree x]
    _ ≤ 3 := by omega

private lemma brooks_for_T_good {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true)) :
    ∃ c_good : {x : TVert t | ¬ inK4 S F t x} → Fin 3,
      ∀ x y, ((G_T_graph S F t).induce {x : TVert t | ¬ inK4 S F t x}).Adj x y →
        c_good x ≠ c_good y := by
  have hGT_deg := G_T_deg_le_three S F t sd fd three
  let T_good : Set (TVert t) := {x : TVert t | ¬ inK4 S F t x}
  have hgood_deg : ∀ x : T_good, ((G_T_graph S F t).induce T_good).degree x ≤ 3 :=
    ind_degree_le (G_T_graph S F t) 3 hGT_deg T_good
  have hgood_kf : ((G_T_graph S F t).induce T_good).CliqueFree 4 := by
    intro Q hQ
    have hKcl : (G_T_graph S F t).IsClique
        ((Q.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset (TVert t)) : Set (TVert t)) := by
      intro a ha b hb hab
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Function.Embedding.coeFn_mk] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      exact hQ.1 ha' hb' (fun h => hab (congrArg Subtype.val h))
    have hKc : (Q.map ⟨Subtype.val, Subtype.val_injective⟩).card = 4 := by
      rw [Finset.card_map]; exact hQ.2
    obtain ⟨q, hq⟩ := Finset.card_pos.mp (by have := hQ.2; omega : 0 < Q.card)
    exact q.2 ⟨Q.map ⟨Subtype.val, Subtype.val_injective⟩, hKc, hKcl,
      Finset.mem_map.mpr ⟨q, hq, rfl⟩⟩
  exact brooks_three (Fintype.card T_good) T_good (le_refl _) ((G_T_graph S F t).induce T_good)
    hgood_deg hgood_kf

private lemma z2_not_inK4 {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (u₀ u₂ v₀ v₂' : U) (w : AltWalk F t u₀ v₀ v₂' u₂) (hm2 : 2 ≤ w.m) :
    ¬ inK4 S F t ⟨w.zs[2]'(by have := w.hlen; have := hm2; omega),
      w.ht_even 1 (by have := w.hlen; have := hm2; omega)⟩ :=
  z2_not_inK4_helper S F t sd fd three u₀ u₂ v₀ v₂' w hm2

private noncomputable def k4Wit {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (square : ∀ s : Fin 4 ↪ U,
      (∀ i : Fin 4, t (s i) = true) →
      (∀ i : Fin 4, S.Adj (s i) (s (i + 1))) →
      (∀ i : Fin 4, F.Adj (s i) (s (i + 1)) ∨ F.Adj (s i) (s (i + 3))) →
      ∀ x y : U, t x = false → t y = false →
      F.Adj (s 0) x → F.Adj (s 2) x → F.Adj (s 1) y → F.Adj (s 3) y → False)
    (K : Finset (TVert t))
    (hK : K.card = 4 ∧ (G_T_graph S F t).IsClique (K : Set (TVert t))) :
    K4Witness S F t K :=
  Classical.choice (k4_component_witness S F t sd fd inside three square K hK.1 hK.2)

private noncomputable def colorKFn {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (square : ∀ s : Fin 4 ↪ U,
      (∀ i : Fin 4, t (s i) = true) →
      (∀ i : Fin 4, S.Adj (s i) (s (i + 1))) →
      (∀ i : Fin 4, F.Adj (s i) (s (i + 1)) ∨ F.Adj (s i) (s (i + 3))) →
      ∀ x y : U, t x = false → t y = false →
      F.Adj (s 0) x → F.Adj (s 2) x → F.Adj (s 1) y → F.Adj (s 3) y → False)
    (c_good : {x : TVert t | ¬ inK4 S F t x} → Fin 3)
    (K : Finset (TVert t)) : TVert t → Fin 3 :=
  if hK : K.card = 4 ∧ (G_T_graph S F t).IsClique (K : Set (TVert t)) then
    let W := k4Wit S F t sd fd inside three square K hK
    let z₂T : TVert t := ⟨W.w.zs[2]'(by have := W.w.hlen; have := W.hm2; omega),
      W.w.ht_even 1 (by have := W.w.hlen; have := W.hm2; omega)⟩
    let α := c_good ⟨z₂T, z2_not_inK4 S F t sd fd three _ _ _ _ W.w W.hm2⟩
    fun x => if x = W.s 0 ∨ x = W.s 2 then α else if x = W.s 1 then α + 1 else α + 2
  else fun _ => 0

private lemma colorKFn_S_proper {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (square : ∀ s : Fin 4 ↪ U,
      (∀ i : Fin 4, t (s i) = true) →
      (∀ i : Fin 4, S.Adj (s i) (s (i + 1))) →
      (∀ i : Fin 4, F.Adj (s i) (s (i + 1)) ∨ F.Adj (s i) (s (i + 3))) →
      ∀ x y : U, t x = false → t y = false →
      F.Adj (s 0) x → F.Adj (s 2) x → F.Adj (s 1) y → F.Adj (s 3) y → False)
    (c_good : {x : TVert t | ¬ inK4 S F t x} → Fin 3)
    (K : Finset (TVert t))
    (hK : K.card = 4 ∧ (G_T_graph S F t).IsClique (K : Set (TVert t)))
    {x y : TVert t} (hx : x ∈ K) (hy : y ∈ K)
    (hadj : (S.induce {v : U | t v = true}).Adj x y) :
    colorKFn S F t sd fd inside three square c_good K x ≠
    colorKFn S F t sd fd inside three square c_good K y := by
  dsimp only [colorKFn]
  rw [dif_pos hK]
  exact colorK_S_proper S F t _ _ hx hy hadj

private lemma colorKFn_s0 {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (square : ∀ s : Fin 4 ↪ U,
      (∀ i : Fin 4, t (s i) = true) →
      (∀ i : Fin 4, S.Adj (s i) (s (i + 1))) →
      (∀ i : Fin 4, F.Adj (s i) (s (i + 1)) ∨ F.Adj (s i) (s (i + 3))) →
      ∀ x y : U, t x = false → t y = false →
      F.Adj (s 0) x → F.Adj (s 2) x → F.Adj (s 1) y → F.Adj (s 3) y → False)
    (c_good : {x : TVert t | ¬ inK4 S F t x} → Fin 3)
    (K : Finset (TVert t))
    (hK : K.card = 4 ∧ (G_T_graph S F t).IsClique (K : Set (TVert t))) :
    let W := k4Wit S F t sd fd inside three square K hK
    let z₂T : TVert t := ⟨W.w.zs[2]'(by have := W.w.hlen; have := W.hm2; omega),
      W.w.ht_even 1 (by have := W.w.hlen; have := W.hm2; omega)⟩
    colorKFn S F t sd fd inside three square c_good K (W.s 0) =
    c_good ⟨z₂T, z2_not_inK4 S F t sd fd three _ _ _ _ W.w W.hm2⟩ := by
  dsimp only [colorKFn]
  rw [dif_pos hK, if_pos (Or.inl rfl)]

private lemma colorKFn_s13 {U : Type*} [Fintype U] (S F : SimpleGraph U) (t : U → Bool)
    (sd : ∀ v, S.degree v ≤ 2) (fd : ∀ v, F.degree v ≤ 2)
    (inside : ∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y)
    (three : ∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true))
    (square : ∀ s : Fin 4 ↪ U,
      (∀ i : Fin 4, t (s i) = true) →
      (∀ i : Fin 4, S.Adj (s i) (s (i + 1))) →
      (∀ i : Fin 4, F.Adj (s i) (s (i + 1)) ∨ F.Adj (s i) (s (i + 3))) →
      ∀ x y : U, t x = false → t y = false →
      F.Adj (s 0) x → F.Adj (s 2) x → F.Adj (s 1) y → F.Adj (s 3) y → False)
    (c_good : {x : TVert t | ¬ inK4 S F t x} → Fin 3)
    (K : Finset (TVert t))
    (hK : K.card = 4 ∧ (G_T_graph S F t).IsClique (K : Set (TVert t))) :
    let W := k4Wit S F t sd fd inside three square K hK
    colorKFn S F t sd fd inside three square c_good K (W.s 1) ≠
    colorKFn S F t sd fd inside three square c_good K (W.s 3) := by
  dsimp only [colorKFn]
  rw [dif_pos hK]
  set W := k4Wit S F t sd fd inside three square K hK
  have h10 : W.s 1 ≠ W.s 0 := fun h => absurd (W.s.injective h) (by decide)
  have h12 : W.s 1 ≠ W.s 2 := fun h => absurd (W.s.injective h) (by decide)
  have h30 : W.s 3 ≠ W.s 0 := fun h => absurd (W.s.injective h) (by decide)
  have h32 : W.s 3 ≠ W.s 2 := fun h => absurd (W.s.injective h) (by decide)
  have h31 : W.s 3 ≠ W.s 1 := fun h => absurd (W.s.injective h) (by decide)
  rw [if_neg (fun h => h.elim h10 h12), if_pos rfl,
    if_neg (fun h => h.elim h30 h32), if_neg h31]
  exact (fin3_add_ne _).2.2

theorem solve_H2 :
    OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R1.H2 := by
  intro U _ S F t sd fd inside three square
  have hGT_deg := G_T_deg_le_three S F t sd fd three
  have hM_deg : ∀ x : TVert t, (M_aux F t).degree x ≤ 1 := M_aux_degree_le_one F t fd three
  have hGT_adj_card : ∀ x : TVert t, ∀ s : Finset (TVert t),
      (∀ y ∈ s, (G_T_graph S F t).Adj x y) → s.card ≤ 3 := by
    intro x s hs
    calc s.card ≤ ((G_T_graph S F t).neighborFinset x).card :=
          Finset.card_le_card (fun y hy => ((G_T_graph S F t).mem_neighborFinset _ _).mpr (hs y hy))
      _ = (G_T_graph S F t).degree x := (G_T_graph S F t).card_neighborFinset_eq_degree x
      _ ≤ 3 := hGT_deg x
  have hk4_closed : ∀ x y : TVert t, inK4 S F t x → (G_T_graph S F t).Adj x y → inK4 S F t y := by
    rintro x y ⟨K, hKc, hKcl, hx⟩ hadj
    exact ⟨K, hKc, hKcl, k4_mem_of_adj (G_T_graph S F t) hGT_adj_card K hKc hKcl hx hadj⟩
  obtain ⟨c_good, hc_good⟩ := brooks_for_T_good S F t sd fd three
  let K_of : TVert t → Finset (TVert t) := fun x => insert x ((G_T_graph S F t).neighborFinset x)
  have hK_of_prop : ∀ x : TVert t, inK4 S F t x →
      (K_of x).card = 4 ∧ (G_T_graph S F t).IsClique ((K_of x) : Set (TVert t)) ∧ x ∈ K_of x := by
    rintro x ⟨K, hKc, hKcl, hx⟩
    have h := k4_card_eq_four_insert (G_T_graph S F t) hGT_adj_card K hKc hKcl hx
      ((G_T_graph S F t).neighborFinset x) (fun z => (G_T_graph S F t).mem_neighborFinset x z)
    exact ⟨h.1, h.2.1, (h.2.2 x).mpr hx⟩
  have hK_of_same : ∀ {x y : TVert t}, inK4 S F t x → (G_T_graph S F t).Adj x y →
      K_of y = K_of x := by
    intro x y hx hadj
    obtain ⟨hKc, hKcl, hxK⟩ := hK_of_prop x hx
    have hyK := k4_mem_of_adj (G_T_graph S F t) hGT_adj_card (K_of x) hKc hKcl hxK hadj
    exact Finset.ext (k4_card_eq_four_insert (G_T_graph S F t) hGT_adj_card (K_of x) hKc hKcl hyK
      ((G_T_graph S F t).neighborFinset y) (fun z => (G_T_graph S F t).mem_neighborFinset y z)).2.2
  let cT : TVert t → Fin 3 := fun x =>
    if hx : inK4 S F t x then colorKFn S F t sd fd inside three square c_good (K_of x) x
    else c_good ⟨x, hx⟩
  have hcT_prop : ∀ x y : TVert t, S.Adj x.val y.val → cT x ≠ cT y := by
    intro x y hadj
    have hadjG : (G_T_graph S F t).Adj x y := Or.inl hadj
    by_cases hx : inK4 S F t x
    · have hy : inK4 S F t y := hk4_closed x y hx hadjG
      have hKe : K_of y = K_of x := hK_of_same hx hadjG
      have hKp := hK_of_prop x hx
      simp only [cT, dif_pos hx, dif_pos hy, hKe]
      exact colorKFn_S_proper S F t sd fd inside three square c_good (K_of x)
        ⟨hKp.1, hKp.2.1⟩ hKp.2.2 (hKe ▸ (hK_of_prop y hy).2.2) hadj
    · have hy : ¬ inK4 S F t y := fun h => hx (hk4_closed y x h hadjG.symm)
      simp only [cT, dif_neg hx, dif_neg hy]
      exact hc_good ⟨x, hx⟩ ⟨y, hy⟩ hadjG
  obtain ⟨c, hc_ext, hcS⟩ := extend_unmarked S sd t cT hcT_prop
  have halt : ∀ (u v v' u' : U) (w : AltWalk F t u v v' u'),
      c u ≠ c u' ∨ ∃ (_ : 2 ≤ w.m),
        c (w.zs[2]'(by have := w.hlen; omega)) = c u ∨
        c (w.zs[2 * w.m - 2]'(by have := w.hlen; omega)) = c u' := by
    intro u v v' u' w
    have hne_u : u ≠ u' := by
      intro heq
      subst heq
      have hvv' : v ≠ v' := fun h => w.hne_edge (by rw [h, Sym2.eq_swap])
      have htv : t v = true := by rw [← w.hstart]; exact w.ht_even 0 (by have := w.hlen; omega)
      have htv' : t v' = true := by rw [← w.hend]; exact w.ht_even w.m (by have := w.hlen; omega)
      exact three v u v' hvv' w.hadj_u.symm w.hadj_u'.symm ⟨htv, w.htu, htv'⟩
    let uT : TVert t := ⟨u, w.htu⟩
    let u'T : TVert t := ⟨u', w.htu'⟩
    have hadjM : (M_aux F t).Adj uT u'T := ⟨fun h => hne_u (congrArg Subtype.val h), v, v', ⟨w⟩⟩
    have hadjG : (G_T_graph S F t).Adj uT u'T := Or.inr hadjM
    rw [hc_ext u w.htu, hc_ext u' w.htu']
    change cT uT ≠ cT u'T ∨ ∃ (_ : 2 ≤ w.m), _
    by_cases hu : inK4 S F t uT
    · have hu' : inK4 S F t u'T := hk4_closed uT u'T hu hadjG
      have hKe : K_of u'T = K_of uT := hK_of_same hu hadjG
      have hKp := hK_of_prop uT hu
      let hKpair : (K_of uT).card = 4 ∧ (G_T_graph S F t).IsClique ((K_of uT) : Set (TVert t)) :=
        ⟨hKp.1, hKp.2.1⟩
      set K := K_of uT
      set W := k4Wit S F t sd fd inside three square K hKpair
      have hM_uniq : ∀ {a b c' : TVert t}, (M_aux F t).Adj a b → (M_aux F t).Adj a c' → b = c' := by
        intro a b c' hab hac
        have h1 : b ∈ (M_aux F t).neighborFinset a := ((M_aux F t).mem_neighborFinset _ _).mpr hab
        have h2 : c' ∈ (M_aux F t).neighborFinset a := ((M_aux F t).mem_neighborFinset _ _).mpr hac
        have hle1 := hM_deg a
        rw [← (M_aux F t).card_neighborFinset_eq_degree a, Finset.card_le_one] at hle1
        exact hle1 b h1 c' h2
      have hcu_val : cT uT = colorKFn S F t sd fd inside three square c_good K uT := by
        simp only [cT, dif_pos hu, K]
      have hcu'_val : cT u'T = colorKFn S F t sd fd inside three square c_good K u'T := by
        simp only [cT, dif_pos hu', hKe, K]
      have hu_mem : uT ∈ K := hKp.2.2
      rcases (W.hmem uT).mp hu_mem with h0 | h1 | h2 | h3
      · obtain ⟨hm_eq, hz_eq⟩ := altWalk_unique_zs F t fd three
          (congrArg Subtype.val h0) w W.w
        have hm2 : 2 ≤ w.m := hm_eq ▸ W.hm2
        refine Or.inr ⟨hm2, Or.inl ?_⟩
        let z₂T : TVert t := ⟨W.w.zs[2]'(by have := W.w.hlen; have := W.hm2; omega),
          W.w.ht_even 1 (by have := W.w.hlen; have := W.hm2; omega)⟩
        have hz2_eq : w.zs[2]'(by have := w.hlen; omega) = z₂T.val :=
          hz_eq 2 (by omega) (by have := w.hlen; omega) (by have := W.w.hlen; omega)
        rw [hz2_eq, hc_ext z₂T.val z₂T.2]
        change cT z₂T = cT uT
        have hnotK4 : ¬ inK4 S F t z₂T := z2_not_inK4 S F t sd fd three _ _ _ _ W.w W.hm2
        have hc_z2 : cT z₂T = c_good ⟨z₂T, hnotK4⟩ := by simp only [cT, dif_neg hnotK4]
        rw [hc_z2, hcu_val, h0]
        exact (colorKFn_s0 S F t sd fd inside three square c_good K hKpair).symm
      · have hu'eq : u'T = W.s 3 := hM_uniq (h1 ▸ hadjM) W.hM13
        left
        rw [hcu_val, hcu'_val, h1, hu'eq]
        exact colorKFn_s13 S F t sd fd inside three square c_good K hKpair
      · have hu'eq : u'T = W.s 0 := hM_uniq (h2 ▸ hadjM) W.hM02.symm
        obtain ⟨hm_eq, hz_eq⟩ := altWalk_unique_zs F t fd three
          (congrArg Subtype.val hu'eq) w.reverse W.w
        have hm2 : 2 ≤ w.m := by change 2 ≤ w.reverse.m; rw [hm_eq]; exact W.hm2
        refine Or.inr ⟨hm2, Or.inr ?_⟩
        let z₂T : TVert t := ⟨W.w.zs[2]'(by have := W.w.hlen; have := W.hm2; omega),
          W.w.ht_even 1 (by have := W.w.hlen; have := W.hm2; omega)⟩
        have hz2_eq : w.zs[2 * w.m - 2]'(by have := w.hlen; omega) = z₂T.val := by
          have hmr : 2 ≤ w.reverse.m := hm2
          have h := hz_eq 2 (by omega)
            (by have := w.reverse.hlen; have := hmr; omega)
            (by have := W.w.hlen; have := W.hm2; omega)
          have hrev : (w.reverse).zs[2]'(by have := w.reverse.hlen; have := hmr; omega) =
              w.zs[2 * w.m - 2]'(by have := w.hlen; omega) := by
            simp only [AltWalk.reverse, List.getElem_reverse]
            congr 1; have := w.hlen; omega
          exact hrev ▸ h
        rw [hz2_eq, hc_ext z₂T.val z₂T.2]
        change cT z₂T = cT u'T
        have hnotK4 : ¬ inK4 S F t z₂T := z2_not_inK4 S F t sd fd three _ _ _ _ W.w W.hm2
        have hc_z2 : cT z₂T = c_good ⟨z₂T, hnotK4⟩ := by simp only [cT, dif_neg hnotK4]
        rw [hc_z2, hcu'_val, hu'eq]
        exact (colorKFn_s0 S F t sd fd inside three square c_good K hKpair).symm
      · have hu'eq : u'T = W.s 1 := hM_uniq (h3 ▸ hadjM) W.hM13.symm
        left
        rw [hcu_val, hcu'_val, h3, hu'eq]
        exact (colorKFn_s13 S F t sd fd inside three square c_good K hKpair).symm
    · have hu' : ¬ inK4 S F t u'T := fun h => hu (hk4_closed u'T uT h hadjG.symm)
      left
      simp only [cT, dif_neg hu, dif_neg hu']
      exact hc_good ⟨uT, hu⟩ ⟨u'T, hu'⟩ hadjG
  obtain ⟨h, hh_edge, hh_inc⟩ :=
    list_color_LF S F t fd inside three c hcS halt
  exact ⟨c, h, hcS, hh_edge, hh_inc⟩

end TotalColoringH2

theorem OMA.solution : OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R1.H2 := by
  exact TotalColoringH2.solve_H2
