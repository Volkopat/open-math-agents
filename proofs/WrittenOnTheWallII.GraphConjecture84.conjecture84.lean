import FormalConjectures.WrittenOnTheWallII.GraphConjecture84

-- Credit: @alueke20 (Gebendorfer cut-vertex reduction + diametral-prefix bound)

namespace OMA_Conj84

open SimpleGraph Walk Finset

universe u

section SecA

variable {α : Type u} {G : SimpleGraph α}

private lemma rad_ge_ex [Fintype α] [Nonempty α] (hG : G.Connected) (u : α) :
    ∃ v : α, G.radius.toNat ≤ G.dist u v := by
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite u
  have hle : (G.radius.toNat : ℕ∞) ≤ (G.dist u v : ℕ∞) := by
    rw [ENat.natCast_toNat (G.radius_ne_top_iff.mpr hG), (hG.preconnected u v).coe_dist_eq_edist]
    exact hv ▸ G.radius_le_eccent
  exact ⟨v, Nat.cast_le.mp hle⟩

private lemma center_ex [Fintype α] [Nonempty α] (hG : G.Connected) :
    ∃ c : α, ∀ v : α, G.dist c v ≤ G.radius.toNat := by
  obtain ⟨c, hc⟩ := G.exists_eccent_eq_radius
  refine ⟨c, fun v => ?_⟩
  have hle : G.edist c v ≤ G.radius := hc ▸ G.edist_le_eccent
  rw [← (hG.preconnected c v).coe_dist_eq_edist,
    ← ENat.natCast_toNat (G.radius_ne_top_iff.mpr hG), Nat.cast_le] at hle
  exact hle

private lemma rad_le [Fintype α] [Nonempty α] (hG : G.Connected) {k : ℕ}
    (hk : ∃ c : α, ∀ v : α, G.dist c v ≤ k) : G.radius.toNat ≤ k := by
  obtain ⟨c, hc⟩ := hk
  have hecc : G.eccent c ≤ (k : ℕ∞) := by
    rw [G.eccent_le_iff]; intro v
    rw [← (hG.preconnected c v).coe_dist_eq_edist]; exact Nat.cast_le.mpr (hc v)
  have hle := G.radius_le_eccent.trans hecc
  rwa [← ENat.natCast_toNat (G.radius_ne_top_iff.mpr hG), Nat.cast_le] at hle

private lemma rad_le_diam [Fintype α] [Nonempty α] (hG : G.Connected) : G.radius.toNat ≤ G.diam := by
  have hle : G.radius ≤ G.ediam := G.radius_le_ediam
  rwa [← ENat.natCast_toNat (G.radius_ne_top_iff.mpr hG),
    ← ENat.natCast_toNat (G.connected_iff_ediam_ne_top.mp hG), Nat.cast_le] at hle

private lemma dist_le_diam [Fintype α] [Nonempty α] (hG : G.Connected) (u v : α) :
    G.dist u v ≤ G.diam := by
  have hle : G.edist u v ≤ G.ediam := G.edist_le_ediam
  rwa [← (hG.preconnected u v).coe_dist_eq_edist,
    ← ENat.natCast_toNat (G.connected_iff_ediam_ne_top.mp hG), Nat.cast_le] at hle

private lemma wdist_sub {u v : α} (p : G.Walk u v) (k : ℕ) :
    ∀ i, i + k ≤ p.length →
      G.dist (p.getVert i) (p.getVert (i + k)) ≤ k ∧ G.Reachable (p.getVert i) (p.getVert (i + k)) := by
  induction k with
  | zero => intro i _; simp
  | succ k ih =>
    intro i hik
    have h1 := ih i (by omega)
    have ha : G.Adj (p.getVert (i + k)) (p.getVert (i + k + 1)) := p.adj_getVert_succ (by omega)
    have ht := ha.reachable.dist_triangle_right (p.getVert i)
    have hs := dist_eq_one_iff_adj.mpr ha
    exact ⟨by simpa [add_assoc] using ht.trans (by omega),
      by simpa [add_assoc] using h1.2.trans ha.reachable⟩

private lemma wdist_eq {u v : α} (p : G.Walk u v) (hp : p.length = G.dist u v)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) : G.dist (p.getVert i) (p.getVert j) = j - i := by
  have h1 := wdist_sub p i 0 (by omega); simp only [zero_add, getVert_zero] at h1
  have h2 := (wdist_sub p (j - i) i (by omega)).1
  have h3 := wdist_sub p (p.length - j) j (by omega)
  have hji : i + (j - i) = j := by omega
  have hjl : j + (p.length - j) = p.length := by omega
  rw [hji] at h2; rw [hjl, getVert_length] at h3
  have ht1 := h1.2.dist_triangle_left (p.getVert j)
  have ht2 := h3.2.dist_triangle_right u
  omega

private lemma wdist_add [DecidableEq α] {u v w : α} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hw : w ∈ p.support) : G.dist u w + G.dist w v = G.dist u v := by
  have hl : (p.takeUntil w hw).length + (p.dropUntil w hw).length = p.length := by
    rw [← length_append, p.take_spec hw]
  have h1 := G.dist_le (p.takeUntil w hw)
  have h2 := G.dist_le (p.dropUntil w hw)
  have h3 := (p.takeUntil w hw).reachable.dist_triangle_left v
  omega

private lemma dist_le_lit [Fintype α] [DecidableEq α] (hG : G.Connected) (u v : α) :
    G.dist u v + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, hp, hl⟩ := hG.exists_path_of_dist u v
  have hle := card_le_largestInducedTreeSize (Walk.induce_support_isTree_of_length_eq_dist p hl)
  rwa [List.toFinset_card_of_nodup hp.support_nodup, length_support, hl] at hle

private lemma rad_le_lit [Fintype α] [DecidableEq α] [Nonempty α] (hG : G.Connected) :
    G.radius.toNat + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨u, v, huv⟩ := G.exists_dist_eq_diam
  have := rad_le_diam hG; have := dist_le_lit hG u v; omega

private lemma tree_img [DecidableEq α] {S : Set α} {t : Finset S}
    (ht : ((G.induce S).induce (t : Set S)).IsTree) :
    (G.induce ((t.image Subtype.val : Finset α) : Set α)).IsTree := by
  classical
  let e : (G.induce S).induce (t : Set S) ≃g G.induce ((t.image Subtype.val : Finset α) : Set α) :=
    { toFun := fun x => ⟨x.1.1, mem_coe.mpr (mem_image_of_mem _ (mem_coe.mp x.2))⟩
      invFun := fun y => let h := mem_image.mp (mem_coe.mp y.2); ⟨h.choose, mem_coe.mpr h.choose_spec.1⟩
      left_inv := fun x => Subtype.ext (Subtype.ext
        (mem_image.mp (mem_coe.mp (mem_coe.mpr (mem_image_of_mem Subtype.val (mem_coe.mp x.2))))).choose_spec.2)
      right_inv := fun y => Subtype.ext (mem_image.mp (mem_coe.mp y.2)).choose_spec.2
      map_rel_iff' := Iff.rfl }
  exact (Iso.isTree_iff e).mp ht

private lemma lit_induce_le [Fintype α] [DecidableEq α] (S : Set α) [Fintype S] [DecidableEq S] :
    largestInducedTreeSize (G.induce S) ≤ largestInducedTreeSize G := by
  classical
  unfold largestInducedTreeSize
  set A : Set ℕ := { n | ∃ s : Finset S, s.card = n ∧ ((G.induce S).induce (s : Set S)).IsTree }
  by_cases hA : A.Nonempty
  · refine csSup_le hA ?_
    rintro n ⟨t, rfl, ht⟩
    rw [← card_image_of_injective t Subtype.val_injective]
    exact card_le_largestInducedTreeSize (tree_img ht)
  · rw [Set.not_nonempty_iff_eq_empty.mp hA]; simp

private lemma dist_le_ind (S : Set α) {u v : S} (hr : (G.induce S).Reachable u v) :
    G.dist u.1 v.1 ≤ (G.induce S).dist u v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  exact (G.dist_le (p.map (Embedding.induce S).toHom)).trans (by rw [length_map, hp])

private lemma tree_path_len (hT : G.IsTree) {u v : α} {p : G.Walk u v} (hp : p.IsPath) :
    p.length = G.dist u v := by
  obtain ⟨q, hq, hl⟩ := hT.1.exists_path_of_dist u v
  have heq := (hT.existsUnique_path u v).unique hp hq
  subst heq; exact hl

private lemma tree_single [DecidableEq α] (a : α) :
    (G.induce (({a} : Finset α) : Set α)).IsTree := by
  have h : ({a} : Finset α) = (Walk.nil : G.Walk a a).support.toFinset := by simp
  rw [h]; exact Walk.induce_support_isTree_of_length_eq_dist (Walk.nil : G.Walk a a) (by simp)

private lemma reach_mono {S T : Set α} (h : S ⊆ T) {u v : S}
    (r : (G.induce S).Reachable u v) : (G.induce T).Reachable ⟨u.1, h u.2⟩ ⟨v.1, h v.2⟩ := by
  obtain ⟨p⟩ := r
  let f : G.induce S →g G.induce T := ⟨fun x => ⟨x.1, h x.2⟩, fun e => e⟩
  exact ⟨p.map f⟩

end SecA

section SecB

private lemma two_rad_sub_two {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β]
    (H : SimpleGraph β) (hH : H.Connected) :
    2 * H.radius.toNat - 2 ≤ largestInducedTreeSize H := by
  classical
  set r := H.radius.toNat
  by_cases hr3 : r ≤ 3
  · have := rad_le_lit hH; omega
  · set k := r - 3; set D := H.diam
    have := rad_le_diam hH
    obtain ⟨x0, y, hxy⟩ := H.exists_dist_eq_diam
    obtain ⟨P, -, hP⟩ := hH.exists_path_of_dist x0 y
    have hPD : P.length = D := hP.trans hxy
    let x := P.getVert
    have hx0 : x 0 = x0 := getVert_zero P
    have hxD : x D = y := by simpa [x, hPD] using getVert_length P
    have hxd : ∀ i j, i ≤ j → j ≤ D → H.dist (x i) (x j) = j - i :=
      fun i j hij hj => wdist_eq P hP hij (by omega)
    let S : Set β := { u | ∃ j < k, H.dist (x j) u ≤ 1 }
    have hxn : ∀ i, k + 1 ≤ i → i ≤ D → x i ∉ S := fun i hi1 hiD ⟨j, hjk, hdj⟩ => by
      have := hxd j i (by omega) hiD; omega
    have hyS : y ∉ S := hxD ▸ hxn D (by omega) le_rfl
    have hxk1S : x (k + 1) ∉ S := hxn (k + 1) le_rfl (by omega)
    have hxkS : x k ∈ S := ⟨k - 1, by omega, by
      have ha : H.Adj (x (k - 1)) (x k) := by
        simpa [x, show k - 1 + 1 = k by omega] using P.adj_getVert_succ (by omega : k - 1 < P.length)
      simp [dist_eq_one_iff_adj.mpr ha]⟩
    let C : Set β := { z | ∃ hz : z ∉ S, (H.induce Sᶜ).Reachable ⟨y, hyS⟩ ⟨z, hz⟩ }
    have hxk1C : x (k + 1) ∈ C := by
      have hsr : ∀ d, k + 1 + d ≤ D → ∀ h : x (k + 1 + d) ∉ S,
          (H.induce Sᶜ).Reachable ⟨x (k + 1), hxk1S⟩ ⟨x (k + 1 + d), h⟩ := by
        intro d; induction d with
        | zero => intro _ _; exact Reachable.refl _
        | succ d ih =>
          intro hd hts
          have hp := hxn (k + 1 + d) (by omega) (by omega)
          have ha : (H.induce Sᶜ).Adj ⟨x (k + 1 + d), hp⟩ ⟨x (k + 1 + (d + 1)), hts⟩ :=
            induce_adj.mpr (by simpa [add_assoc] using P.adj_getVert_succ (by omega : k + 1 + d < P.length))
          exact (ih (by omega) hp).trans ha.reachable
      refine ⟨hxk1S, ?_⟩
      obtain ⟨q⟩ := (hsr (D - (k + 1)) (by omega)
        (by simpa [show k + 1 + (D - (k + 1)) = D by omega, hxD] using hyS)).symm
      exact ⟨q.copy (Subtype.ext (by simp [x, show k + 1 + (D - (k + 1)) = D by omega, hxD])) rfl⟩
    have hnC : ∀ z, z ∉ C → H.dist (x k) z ≤ k + 2 := by
      intro z hzC
      by_cases hzS : z ∈ S
      · obtain ⟨j, hjk, hdz⟩ := hzS
        have := hH.dist_triangle (u := x k) (v := x j) (w := z)
        have hkj := hxd j k (by omega) (by omega); rw [H.dist_comm] at hkj; omega
      · obtain ⟨q, -, hq⟩ := hH.exists_path_of_dist y z
        have hex : ∃ u ∈ q.support, u ∈ S := by
          by_contra hn; push Not at hn; exact hzC ⟨hzS, ⟨q.induce Sᶜ hn⟩⟩
        obtain ⟨u, huq, j, hjk, hju⟩ := hex
        have := wdist_add q hq huq; have := dist_le_diam hH y z
        have hj0 : H.dist x0 (x j) = j := by simpa [hx0] using hxd 0 j (Nat.zero_le j) (by omega)
        have := hH.dist_triangle (u := x0) (v := x j) (w := y)
        have := hH.dist_triangle (u := x j) (v := u) (w := y)
        have := hH.dist_triangle (u := x k) (v := x j) (w := z)
        have := hH.dist_triangle (u := x j) (v := u) (w := z)
        have hkj := hxd j k (by omega) (by omega)
        have h1 : H.dist (x k) (x j) = H.dist (x j) (x k) := H.dist_comm
        have h2 : H.dist y u = H.dist u y := H.dist_comm
        omega
    obtain ⟨w, hwd⟩ := rad_ge_ex hH (x k)
    have hwC : w ∈ C := by by_contra hn; have := hnC w hn; omega
    let S' : Set β := insert (x k) C
    have hrC : (H.induce S').Reachable ⟨x (k + 1), Set.mem_insert_of_mem _ hxk1C⟩
        ⟨w, Set.mem_insert_of_mem _ hwC⟩ := by
      obtain ⟨hx1S, hr1⟩ := hxk1C; obtain ⟨hwS, hr2⟩ := hwC; obtain ⟨p⟩ := hr1.symm.trans hr2
      have hps : ∀ u ∈ (p.map (Embedding.induce Sᶜ).toHom).support, u ∈ S' := by
        intro u hu; rw [Walk.support_map, List.mem_map] at hu; obtain ⟨v, hv, rfl⟩ := hu
        exact Set.mem_insert_of_mem _ ⟨v.2, hr1.trans (p.takeUntil v hv).reachable⟩
      exact ⟨(p.map (Embedding.induce Sᶜ).toHom).induce S' hps⟩
    have hrw : (H.induce S').Reachable ⟨x k, Set.mem_insert _ _⟩ ⟨w, Set.mem_insert_of_mem _ hwC⟩ :=
      (Adj.reachable (induce_adj.mpr (P.adj_getVert_succ (by omega : k < P.length)))).trans hrC
    obtain ⟨Q, -, hQl⟩ := hrw.exists_path_of_dist
    have hQr : H.dist (x k) w ≤ (H.induce S').dist ⟨x k, Set.mem_insert _ _⟩
        ⟨w, Set.mem_insert_of_mem _ hwC⟩ := dist_le_ind S' hrw
    let T0 : Finset β := Q.support.toFinset.image Subtype.val
    have hT0t : (H.induce (T0 : Set β)).IsTree := tree_img (Walk.induce_support_isTree_of_length_eq_dist Q hQl)
    have hT0c : r + 1 ≤ T0.card := by
      rw [card_image_of_injective _ Subtype.val_injective,
        List.toFinset_card_of_nodup (Q.isPath_of_length_eq_dist hQl).support_nodup, length_support]; omega
    have hxkT0 : x k ∈ T0 := mem_image_of_mem _ (List.mem_toFinset.mpr Q.start_mem_support)
    have hT0sub : ∀ v ∈ T0, v = x k ∨ v ∈ C := fun v hv => by
      obtain ⟨v', _, rfl⟩ := mem_image.mp hv; exact Set.mem_insert_iff.mp v'.2
    have hbuild : ∀ m ≤ k, ∃ T : Finset β, (H.induce (T : Set β)).IsTree ∧ T0.card + m ≤ T.card ∧
        x (k - m) ∈ T ∧ (∀ v ∈ T, v ∈ T0 ∨ ∃ j, k - m ≤ j ∧ j < k ∧ v = x j) := by
      intro m; induction m with
      | zero => intro _; exact ⟨T0, hT0t, by omega, hxkT0, fun _ hv => Or.inl hv⟩
      | succ m ih =>
        intro hm
        obtain ⟨T, hTt, hTc, haT, hTs⟩ := ih (by omega)
        let z := x (k - (m + 1)); let a := x (k - m)
        have hza : H.Adj z a := by
          have : k - (m + 1) + 1 = k - m := by omega
          simpa [z, a, this] using P.adj_getVert_succ (by omega : k - (m + 1) < P.length)
        have hzS : z ∈ S := ⟨k - (m + 1), by omega, by simp [z]⟩
        have hzz : z = x (k - (m + 1)) := rfl
        have hznT : z ∉ T := fun hzT => by
          rcases hTs z hzT with hz0 | ⟨j, _, _, hzj⟩
          · rcases hT0sub z hz0 with hzx | hzC
            · have := hxd (k - (m + 1)) k (by omega) (by omega); rw [← hzz, hzx, dist_self] at this; omega
            · exact hzC.1 hzS
          · have := hxd (k - (m + 1)) j (by omega) (by omega); rw [← hzz, hzj, dist_self] at this; omega
        have huniq : ∀ ⦃b : β⦄, b ∈ T → H.Adj z b → b = a := fun b hb hzb => by
          have hbS : b ∈ S := ⟨k - (m + 1), by omega, by rw [← hzz, dist_eq_one_iff_adj.mpr hzb]⟩
          rcases hTs b hb with hb0 | ⟨j, _, _, hbj⟩
          · rcases hT0sub b hb0 with hbx | hbC
            · have := hxd (k - (m + 1)) k (by omega) (by omega)
              rw [← hzz, ← hbx, dist_eq_one_iff_adj.mpr hzb] at this
              have hm0 : m = 0 := by omega
              subst hm0; simpa [a] using hbx
            · exact absurd hbS hbC.1
          · have := hxd (k - (m + 1)) j (by omega) (by omega)
            rw [← hzz, ← hbj, dist_eq_one_iff_adj.mpr hzb] at this
            have hjk : j = k - m := by omega
            rw [hbj, hjk]
        refine ⟨insert z T, hTt.induce_insert_of_unique_adj hznT haT hza huniq,
          by rw [card_insert_of_notMem hznT]; omega, mem_insert_self z T, fun v hv => ?_⟩
        rcases mem_insert.mp hv with rfl | hvT
        · exact Or.inr ⟨k - (m + 1), le_rfl, by omega, rfl⟩
        · rcases hTs v hvT with hv0 | ⟨j, hj1, hj2, hvj⟩
          · exact Or.inl hv0
          · exact Or.inr ⟨j, by omega, hj2, hvj⟩
    obtain ⟨T, hTt, hTc, -⟩ := hbuild k le_rfl
    have := card_le_largestInducedTreeSize hTt; omega

end SecB

section SecC

private theorem tree_two_rad : ∀ n : ℕ, ∀ {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β],
    Fintype.card β = n → ∀ (T : SimpleGraph β), T.IsTree → 2 * T.radius.toNat ≤ Fintype.card β := by
  intro n; induction n using Nat.strong_induction_on with
  | h n ih =>
    intro β _ _ _ hn T hT
    classical
    by_cases hn2 : n ≤ 2
    · obtain ⟨x, y, hxy⟩ := T.exists_dist_eq_diam
      obtain ⟨P, hPp, hPl⟩ := hT.1.exists_path_of_dist x y
      have := rad_le_diam hT.1; have := hPp.length_lt; omega
    · have hn3 : 3 ≤ Fintype.card β := by omega
      obtain ⟨x0, y, hxy⟩ := T.exists_dist_eq_diam
      obtain ⟨P, hPp, hPl⟩ := hT.1.exists_path_of_dist x0 y
      set D := T.diam
      have hPD : P.length = D := hPl.trans hxy
      have hD2 : 2 ≤ D := by
        by_contra hD1
        have hDr : T.radius.toNat ≤ 1 := by have := rad_le_diam hT.1; omega
        obtain ⟨c, hc⟩ := center_ex hT.1
        have hne1 : ((univ : Finset β).erase c).card ≥ 2 := by
          rw [card_erase_of_mem (mem_univ c), card_univ]; omega
        obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hne1
        rw [mem_erase] at ha hb
        have hca : T.Adj c a := dist_eq_one_iff_adj.mp (by
          have := (hT.1 c a).pos_dist_of_ne ha.1.symm; have := hc a; omega)
        have hcb : T.Adj c b := dist_eq_one_iff_adj.mp (by
          have := (hT.1 c b).pos_dist_of_ne hb.1.symm; have := hc b; omega)
        have hab' : T.Adj a b := dist_eq_one_iff_adj.mp (by
          have := (hT.1 a b).pos_dist_of_ne hab; have := dist_le_diam hT.1 a b; omega)
        exact hT.2 (Walk.cons hca (Walk.cons hab' (Walk.cons hcb.symm .nil))) (by
          simp [isCycle_def, isTrail_def, hab, ha.1, hb.1, hb.1.symm])
      let S : Set β := { v | ∃ u w, u ≠ w ∧ T.Adj v u ∧ T.Adj v w }
      have h1S : P.getVert 1 ∈ S := ⟨P.getVert 0, P.getVert 2, fun heq => by
        have := wdist_eq P hPl (Nat.zero_le 2) (by omega); rw [heq, dist_self] at this; omega,
        (P.adj_getVert_succ (by omega : 0 < P.length)).symm, P.adj_getVert_succ (by omega : 1 < P.length)⟩
      have hend_nS : ∀ {a b : β} (Q : T.Walk a b), Q.IsPath → Q.length = D → a ∉ S := by
        intro a b Q hQp hQl ⟨u, w, huw, hau, haw⟩
        have : ∃ z, z ≠ Q.getVert 1 ∧ T.Adj z a := by
          by_cases h : u = Q.getVert 1
          · exact ⟨w, fun h' => huw (h.trans h'.symm), haw.symm⟩
          · exact ⟨u, h, hau.symm⟩
        obtain ⟨z, hz1, hza⟩ := this
        have hzQ : z ∉ Q.support := fun hzs => by
          obtain ⟨j, hje, hj⟩ := Q.mem_support_iff_exists_getVert.mp hzs
          have := wdist_eq Q (tree_path_len hT hQp) (Nat.zero_le j) hj
          rw [getVert_zero, hje, dist_eq_one_iff_adj.mpr hza.symm] at this
          have hj1 : j = 1 := by omega
          exact hz1 (by rw [← hje, hj1])
        have hl1 : (Walk.cons hza Q).length = T.dist z b :=
          tree_path_len hT ((cons_isPath_iff hza Q).mpr ⟨hQp, hzQ⟩)
        have := dist_le_diam hT.1 z b
        simp only [length_cons] at hl1; omega
      have hx0S := hend_nS P hPp hPD
      have hyS := hend_nS P.reverse hPp.reverse (by simp [hPD])
      have hxy_ne : x0 ≠ y := fun h => by rw [h, dist_self] at hxy; omega
      let SF : Finset β := univ.filter (· ∈ S)
      have hSF_sub : SF ⊆ (univ.erase x0).erase y := fun v hv => by
        simp only [SF, mem_filter, mem_univ, true_and] at hv
        simp only [mem_erase, mem_univ, and_true]
        exact ⟨fun h => hyS (h ▸ hv), fun h => hx0S (h ▸ hv)⟩
      have hcardS : Fintype.card S + 2 ≤ n := by
        have hc := card_le_card hSF_sub
        have hSF : Fintype.card S = SF.card := by
          have := (Fintype.card_of_subtype (p := (· ∈ S)) SF (fun _ => by simp [SF])).symm
          simpa using this
        rw [card_erase_of_mem (mem_erase.mpr ⟨hxy_ne.symm, mem_univ _⟩),
          card_erase_of_mem (mem_univ x0), card_univ] at hc
        omega
      have : Nonempty S := ⟨⟨P.getVert 1, h1S⟩⟩
      have hTS : (T.induce S).IsTree := by
        refine ⟨Connected.mk fun a b => ?_, hT.2.induce S⟩
        obtain ⟨q, hqp, -⟩ := hT.1.exists_path_of_dist a.1 b.1
        refine ⟨q.induce S fun v hv => ?_⟩
        by_cases hva : v = a.1; · exact hva ▸ a.2
        by_cases hvb : v = b.1; · exact hvb ▸ b.2
        obtain ⟨j, hje, hj⟩ := q.mem_support_iff_exists_getVert.mp hv
        have hj1 : 1 ≤ j := Nat.pos_of_ne_zero fun h => hva (by rw [← hje, h, getVert_zero])
        have hj2 : j < q.length := lt_of_le_of_ne hj fun h => hvb (by rw [← hje, h, getVert_length])
        rw [← hje]
        exact ⟨q.getVert (j - 1), q.getVert (j + 1), fun h => by
          have := wdist_eq q (tree_path_len hT hqp) (by omega : j - 1 ≤ j + 1) (by omega)
          rw [h, dist_self] at this; omega,
          by simpa [show j - 1 + 1 = j by omega] using (q.adj_getVert_succ (by omega : j - 1 < q.length)).symm,
          q.adj_getVert_succ hj2⟩
      have hnear : ∀ v : β, ∃ w ∈ S, T.dist w v ≤ 1 := by
        intro v
        by_cases hvS : v ∈ S; · exact ⟨v, hvS, by simp⟩
        have hbne : ((univ : Finset β).erase v).Nonempty := by
          rw [← card_pos, card_erase_of_mem (mem_univ v), card_univ]; omega
        obtain ⟨b, hb⟩ := hbne; rw [mem_erase] at hb
        obtain ⟨w, hvw⟩ : ∃ w, T.Adj v w := by
          obtain ⟨p0⟩ := hT.1 v b
          cases p0 with | nil => exact absurd rfl hb.1.symm | cons h _ => exact ⟨_, h⟩
        have hzne : (((univ : Finset β).erase v).erase w).Nonempty := by
          rw [← card_pos]
          by_cases hw_mem : w ∈ (univ : Finset β).erase v
          · rw [card_erase_of_mem hw_mem, card_erase_of_mem (mem_univ v), card_univ]; omega
          · rw [erase_eq_of_notMem hw_mem, card_erase_of_mem (mem_univ v), card_univ]; omega
        obtain ⟨z, hz⟩ := hzne
        simp only [mem_erase, mem_univ, and_true] at hz
        obtain ⟨q, hqp, hql⟩ := hT.1.exists_path_of_dist v z
        have hql2 : 2 ≤ q.length := by
          by_contra hlt
          have := (hT.1 v z).pos_dist_of_ne hz.2.symm
          have hq1 : q.length = 1 := by omega
          have hadj1 : T.Adj v z := by
            simpa [getVert_zero, show q.getVert 1 = z by simpa [hq1] using getVert_length q] using
              q.adj_getVert_succ (by omega : 0 < q.length)
          exact hvS ⟨w, z, hz.1.symm, hvw, hadj1⟩
        have hq1w : q.getVert 1 = w := by
          by_contra hne
          exact hvS ⟨q.getVert 1, w, hne, by simpa [getVert_zero] using q.adj_getVert_succ (by omega : 0 < q.length), hvw⟩
        have hwS : w ∈ S := by
          rw [← hq1w]
          exact ⟨q.getVert 0, q.getVert 2, fun h => by
            have := wdist_eq q hql (Nat.zero_le 2) (by omega); rw [h, dist_self] at this; omega,
            (by simpa using (q.adj_getVert_succ (by omega : 0 < q.length)).symm),
            q.adj_getVert_succ (by omega : 1 < q.length)⟩
        exact ⟨w, hwS, by rw [dist_eq_one_iff_adj.mpr hvw.symm]⟩
      have hih := ih (Fintype.card S) (by omega) rfl (T.induce S) hTS
      obtain ⟨c, hc⟩ := center_ex hTS.1
      have hr : T.radius.toNat ≤ (T.induce S).radius.toNat + 1 := rad_le hT.1 ⟨c.1, fun v => by
        obtain ⟨w, hwS, hdw⟩ := hnear v
        have htri := (hT.1 w v).dist_triangle_right c.1
        have hdi : T.dist c.1 w ≤ (T.induce S).dist c ⟨w, hwS⟩ := dist_le_ind S (hTS.1 c ⟨w, hwS⟩)
        have hcw := hc ⟨w, hwS⟩
        omega⟩
      omega

private lemma tree_two_rad_lit {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β]
    (T : SimpleGraph β) (hT : T.IsTree) : 2 * T.radius.toNat ≤ largestInducedTreeSize T := by
  have h1 := tree_two_rad (Fintype.card β) rfl T hT
  have h2 := card_le_largestInducedTreeSize (s := (Finset.univ : Finset β))
    (by rw [coe_univ]; exact (Iso.isTree_iff T.induceUnivIso).mpr hT)
  simp only [Finset.card_univ] at h2; omega

end SecC

section SecD

variable {α : Type u} {G : SimpleGraph α}

private def Cut (G : SimpleGraph α) (c : α) : Prop :=
  ¬ (G.induce {x : α | x ≠ c}).Preconnected

private def HasCut (G : SimpleGraph α) : Prop := ∃ c : α, Cut G c

private noncomputable def comp [Fintype α] [DecidableEq α] (G : SimpleGraph α) (c a : α)
    (ha : a ≠ c) : Finset α := by
  classical
  exact univ.filter fun x => ∃ hx : x ≠ c, (G.induce {u | u ≠ c}).Reachable ⟨a, ha⟩ ⟨x, hx⟩

private lemma mem_comp [Fintype α] [DecidableEq α] {c a : α} (ha : a ≠ c) {x : α} :
    x ∈ comp G c a ha ↔ ∃ hx : x ≠ c, (G.induce {u | u ≠ c}).Reachable ⟨a, ha⟩ ⟨x, hx⟩ := by
  classical simp [comp]

private lemma ne_comp [Fintype α] [DecidableEq α] {c a x : α} {ha : a ≠ c}
    (hx : x ∈ comp G c a ha) : x ≠ c := ((mem_comp ha).mp hx).1

private lemma nmem_comp [Fintype α] [DecidableEq α] (c a : α) (ha : a ≠ c) :
    c ∉ comp G c a ha := fun h => ne_comp h rfl

private lemma self_comp [Fintype α] [DecidableEq α] (c a : α) (ha : a ≠ c) :
    a ∈ comp G c a ha := (mem_comp ha).mpr ⟨ha, Reachable.refl _⟩

private lemma adj_comp [Fintype α] [DecidableEq α] {c a x y : α} {ha : a ≠ c}
    (hx : x ∈ comp G c a ha) (hy : y ≠ c) (h : G.Adj x y) : y ∈ comp G c a ha :=
  (mem_comp ha).mpr ⟨hy, ((mem_comp ha).mp hx).2.trans (Adj.reachable (by simpa using h))⟩

private lemma eq_comp [Fintype α] [DecidableEq α] {c a b : α} {ha : a ≠ c}
    (hb : b ≠ c) (hm : b ∈ comp G c a ha) : comp G c b hb = comp G c a ha := by
  obtain ⟨_, hr⟩ := (mem_comp ha).mp hm; ext x; simp only [mem_comp]
  exact ⟨fun ⟨hx, h⟩ => ⟨hx, hr.trans h⟩, fun ⟨hx, h⟩ => ⟨hx, hr.symm.trans h⟩⟩

private lemma disj_comp [Fintype α] [DecidableEq α] {c a b : α} {ha : a ≠ c}
    (hb : b ≠ c) (hn : b ∉ comp G c a ha) : Disjoint (comp G c b hb) (comp G c a ha) :=
  disjoint_left.mpr fun _ hxb hxa =>
    let hx := ne_comp hxb
    hn ((eq_comp hx hxb |>.symm.trans (eq_comp hx hxa)) ▸ self_comp c b hb)

private lemma cut_ex [Fintype α] [DecidableEq α] {c a : α} (hc : Cut G c) (ha : a ≠ c) :
    ∃ b : α, b ≠ c ∧ b ∉ comp G c a ha := by
  by_contra h; push Not at h; apply hc; intro u v
  exact ((mem_comp ha).mp (h u.1 u.2)).2.symm.trans ((mem_comp ha).mp (h v.1 v.2)).2

private lemma supp_eq_tail {u v : α} (p : G.Walk u v) {z : α} (hz : z ∈ p.support) :
    z = u ∨ z ∈ p.support.tail := by cases p <;> simpa using hz

private lemma sep_supp [Fintype α] [DecidableEq α] {c a x y : α} {ha : a ≠ c}
    (hx : x ∈ comp G c a ha) (hy : y ∉ comp G c a ha) (p : G.Walk x y) : c ∈ p.support := by
  by_contra hc; apply hy
  induction p with
  | nil => exact hx
  | cons h t ih =>
    have hc' : c ∉ t.support := fun hm => hc (by simp [hm])
    exact ih (adj_comp hx (fun hvc => hc' (hvc ▸ t.start_mem_support)) h) hy hc'

private lemma sep_dist [Fintype α] [DecidableEq α] (hG : G.Connected) {c a x y : α} {ha : a ≠ c}
    (hx : x ∈ comp G c a ha) (hy : y ∉ comp G c a ha) : G.dist x y = G.dist x c + G.dist c y := by
  obtain ⟨p, -, hl⟩ := hG.exists_path_of_dist x y
  exact (wdist_add p hl (sep_supp hx hy p)).symm

private lemma path_avoid [Fintype α] [DecidableEq α] {c a x y : α} {ha : a ≠ c}
    (hx : x ∉ comp G c a ha) (hy : y ∉ comp G c a ha) {p : G.Walk x y} (hp : p.IsPath) :
    ∀ u ∈ p.support, u ∉ comp G c a ha := by
  intro u hu huA
  have hc1 : c ∈ (p.takeUntil u hu).support := by
    simpa [support_reverse] using sep_supp huA hx (p.takeUntil u hu).reverse
  have hc2 := sep_supp huA hy (p.dropUntil u hu)
  have hc2' : c ∈ (p.dropUntil u hu).support.tail := by
    rcases supp_eq_tail (p.dropUntil u hu) hc2 with rfl | hm
    · exact absurd rfl (ne_comp huA).symm
    · exact hm
  have hnd : ((p.takeUntil u hu).support ++ (p.dropUntil u hu).support.tail).Nodup := by
    rw [← support_append, p.take_spec hu]; exact hp.support_nodup
  exact (List.nodup_append.mp hnd).2.2 c hc1 c hc2' rfl

private lemma avoid_path [Fintype α] [DecidableEq α] (hG : G.Connected) {c a x y : α} {ha : a ≠ c}
    (hx : x ∉ comp G c a ha) (hy : y ∉ comp G c a ha) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length = G.dist x y ∧ ∀ u ∈ p.support, u ∉ comp G c a ha := by
  obtain ⟨p, hp, hl⟩ := hG.exists_path_of_dist x y
  exact ⟨p, hp, hl, path_avoid hx hy hp⟩

private lemma ncut_reach {v c : α} (hcv : c ≠ v)
    (hr : ∀ x : α, x ≠ v → ∃ q : G.Walk x c, v ∉ q.support) : ¬ Cut G v := by
  have hl : ∀ {a b} (ha : a ≠ v) (hb : b ≠ v) (q : G.Walk a b),
      v ∉ q.support → (G.induce {u | u ≠ v}).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := fun ha hb q hq => by
    induction q with
    | nil => exact Reachable.refl _
    | @cons u w _ h t ih =>
      have hw : w ≠ v := fun hwv => hq (by rw [support_cons, List.mem_cons]; exact Or.inr (hwv ▸ t.start_mem_support))
      exact (Adj.reachable (by simpa using h)).trans (ih hw hb fun hv => hq (by simp [hv]))
  intro hc; apply hc; intro x y
  obtain ⟨px, hpx⟩ := hr x.1 x.2; obtain ⟨py, hpy⟩ := hr y.1 y.2
  exact (hl x.2 hcv px hpx).trans (hl y.2 hcv py hpy).symm

private lemma snd_supp {u v : α} (p : G.Walk u v) (hp : ¬ p.Nil) : p.snd ∈ p.support := by
  cases p with
  | nil => exact absurd Walk.Nil.nil hp
  | cons _ t => simp [t.start_mem_support]

private lemma pen_supp {u v : α} (p : G.Walk u v) (hp : ¬ p.Nil) : p.penultimate ∈ p.support := by
  induction p with
  | nil => exact absurd Walk.Nil.nil hp
  | @cons a _ _ _ t ih =>
    cases t with | nil => simp [penultimate] | cons _ _ => exact List.mem_cons_of_mem a (ih (by simp))

private lemma ncut_uniq (hG : G.Connected) {v c : α} (hvc : G.Adj v c)
    (hu : ∀ u, G.Adj v u → u = c) : ¬ Cut G v := by
  classical
  refine ncut_reach hvc.ne.symm fun x hxv => ?_
  obtain ⟨p, hp, -⟩ := hG.exists_path_of_dist x c
  refine ⟨p, fun hv => ?_⟩
  let q := p.takeUntil v hv
  have hqn : ¬ q.Nil := fun hn => hxv (Nil.eq hn)
  have hc1 : c ∈ q.support := (hu _ (adj_penultimate hqn).symm) ▸ pen_supp q hqn
  have hc2' : c ∈ (p.dropUntil v hv).support.tail := by
    rcases supp_eq_tail (p.dropUntil v hv) (end_mem_support _) with h | hm
    · exact absurd h.symm hvc.ne
    · exact hm
  have hnd : (q.support ++ (p.dropUntil v hv).support.tail).Nodup := by
    rw [← support_append, p.take_spec hv]; exact hp.support_nodup
  exact (List.nodup_append.mp hnd).2.2 c hc1 c hc2' rfl

private lemma cut_uniq [Fintype α] [DecidableEq α] (hc : 3 ≤ Fintype.card α) {v c : α}
    (hvc : G.Adj v c) (hu : ∀ u, G.Adj v u → u = c) : Cut G c := by
  classical
  have hne : (univ \ ({v, c} : Finset α)).Nonempty := by
    rw [← card_pos, card_sdiff]; have := card_le_two (a := v) (b := c); simp [card_univ]; omega
  obtain ⟨z, hz⟩ := hne
  simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, not_or, true_and] at hz
  intro hp; obtain ⟨p⟩ := hp ⟨v, hvc.ne⟩ ⟨z, hz.2⟩
  cases p with
  | nil => exact hz.1 rfl
  | @cons _ b _ h _ => exact b.2 (hu b.1 h)

private def Pend [Fintype α] [DecidableEq α] (G : SimpleGraph α) (c : α) (A : Finset α) : Prop :=
  ∃ a, ∃ ha : a ≠ c, A = comp G c a ha ∧ (∃ b, b ≠ c ∧ b ∉ A) ∧ A.card = A.sup (G.dist c)

private lemma getVert_ne_start {u v : α} (p : G.Walk u v) (hp : p.IsPath) {i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ p.length) : p.getVert i ≠ u := by
  cases p with
  | nil => simp at hi2; omega
  | cons h t =>
    cases i with
    | zero => omega
    | succ i =>
      intro hm; exact (cons_isPath_iff h t |>.mp hp).2 (hm ▸ t.getVert_mem_support i)

private lemma comp_getVert_mem [Fintype α] [DecidableEq α] {c a v : α} {ha : a ≠ c}
    (hv : v ∈ comp G c a ha) {P : G.Walk c v} (hP : P.IsPath) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i ≤ P.length) : P.getVert i ∈ comp G c a ha := by
  by_contra hn
  let w := P.getVert i; have hws := P.getVert_mem_support i
  have hcd : c ∈ (P.dropUntil w hws).support := by
    simpa [support_reverse] using sep_supp hv hn (P.dropUntil w hws).reverse
  have hcw : c ≠ w := (getVert_ne_start P hP hi1 hi2).symm
  have hct : c ∈ (P.dropUntil w hws).support.tail := by
    rcases supp_eq_tail (P.dropUntil w hws) hcd with heq | hm
    · exact absurd heq hcw
    · exact hm
  have hnd : ((P.takeUntil w hws).support ++ (P.dropUntil w hws).support.tail).Nodup := by
    rw [← support_append, P.take_spec hws]; exact hP.support_nodup
  exact (List.nodup_append.mp hnd).2.2 c (start_mem_support _) c hct rfl

private lemma comp_sup_le_card [Fintype α] [DecidableEq α] (hG : G.Connected) {c a : α}
    (ha : a ≠ c) : (comp G c a ha).sup (G.dist c) ≤ (comp G c a ha).card := by
  obtain ⟨v, hvA, hve⟩ := exists_mem_eq_sup (comp G c a ha) ⟨a, self_comp c a ha⟩ (G.dist c)
  have hse : (comp G c a ha).sup (G.dist c) = G.dist c v := hve
  rw [hse]
  obtain ⟨P, hP, hPl⟩ := hG.exists_path_of_dist c v
  set h := G.dist c v
  have hsub : (Icc 1 h).image P.getVert ⊆ comp G c a ha := fun u hu => by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu; simp only [mem_Icc] at hi
    exact comp_getVert_mem hvA hP hi.1 (by omega)
  have hinj : Set.InjOn P.getVert (Icc 1 h : Set ℕ) := fun i hi j hj hij => by
    simp only [coe_Icc, Set.mem_Icc] at hi hj
    have h1 : G.dist c (P.getVert i) = i := by
      simpa [getVert_zero] using wdist_eq P hPl (Nat.zero_le i) (by omega)
    have h2 : G.dist c (P.getVert j) = j := by
      simpa [getVert_zero] using wdist_eq P hPl (Nat.zero_le j) (by omega)
    rw [← h1, ← h2, hij]
  calc h = (Icc 1 h).card := by simp
    _ = ((Icc 1 h).image P.getVert).card := (card_image_of_injOn hinj).symm
    _ ≤ (comp G c a ha).card := card_le_card hsub

private lemma pend_ex [Fintype α] [DecidableEq α] (hG : G.Connected) {c : α} {A : Finset α}
    (hp : Pend G c A) : 1 ≤ A.sup (G.dist c) ∧ ∃ v ∈ A, G.dist c v = A.sup (G.dist c) := by
  obtain ⟨a, ha, rfl, -, -⟩ := hp
  obtain ⟨v, hvA, hve⟩ := exists_mem_eq_sup _ ⟨a, self_comp c a ha⟩ (G.dist c)
  have hda := Nat.succ_le_of_lt ((hG c a).pos_dist_of_ne ha.symm)
  exact ⟨le_trans hda (le_sup (self_comp c a ha)), v, hvA, hve.symm⟩

private lemma pend_spec [Fintype α] [DecidableEq α] (hG : G.Connected) {c : α} {A : Finset α}
    (hp : Pend G c A) {v : α} (hvA : v ∈ A) (hv_dist : G.dist c v = A.sup (G.dist c))
    (P : G.Walk c v) (hPp : P.IsPath) (hPl : P.length = A.sup (G.dist c)) :
    (∀ i, 1 ≤ i → i ≤ A.sup (G.dist c) → P.getVert i ∈ A) ∧
    A = (Icc 1 (A.sup (G.dist c))).image P.getVert ∧
    (∀ i, 1 ≤ i → i ≤ A.sup (G.dist c) → ∀ u, G.Adj (P.getVert i) u →
      u = P.getVert (i - 1) ∨ (i < A.sup (G.dist c) ∧ u = P.getVert (i + 1))) ∧
    (∀ u, G.Adj v u → u = P.getVert (A.sup (G.dist c) - 1)) ∧
    (∀ u ∈ A, G.dist c u ≤ A.sup (G.dist c) ∧ G.dist u v = A.sup (G.dist c) - G.dist c u ∧
      (G.dist c u = A.sup (G.dist c) ↔ u = v)) ∧
    (∀ {w : α} (cyc : G.Walk w w), cyc.IsCycle → ∀ u ∈ A, u ∉ cyc.support) ∧
    ¬ Cut G v := by
  obtain ⟨a, ha, rfl, hb, hcard⟩ := hp
  set A := comp G c a ha; set h := A.sup (G.dist c)
  have h1 : 1 ≤ h := (pend_ex hG ⟨a, ha, rfl, hb, hcard⟩).1
  have hpd : P.length = G.dist c v := by rw [hPl, hv_dist]
  have hmem : ∀ i, 1 ≤ i → i ≤ h → P.getVert i ∈ A := fun i hi1 hi2 =>
    comp_getVert_mem hvA hPp hi1 (by omega)
  have hinj : Set.InjOn P.getVert (Icc 1 h : Set ℕ) := fun i hi j hj hij => by
    simp only [coe_Icc, Set.mem_Icc] at hi hj
    have h1' : G.dist c (P.getVert i) = i := by
      simpa [getVert_zero] using wdist_eq P hpd (Nat.zero_le i) (by omega)
    have h2' : G.dist c (P.getVert j) = j := by
      simpa [getVert_zero] using wdist_eq P hpd (Nat.zero_le j) (by omega)
    rw [← h1', ← h2', hij]
  have himg : A = (Icc 1 h).image P.getVert := by
    symm; refine eq_of_subset_of_card_le (fun u hu => by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hu; simp only [mem_Icc] at hi; exact hmem i hi.1 hi.2) ?_
    rw [card_image_of_injOn hinj, Nat.card_Icc, Nat.add_sub_cancel, hcard]
  have hadj : ∀ i, 1 ≤ i → i ≤ h → ∀ u, G.Adj (P.getVert i) u →
      u = P.getVert (i - 1) ∨ (i < h ∧ u = P.getVert (i + 1)) := by
    intro i hi1 hi2 u had
    by_cases huc : u = c
    · rw [huc] at had
      have := dist_eq_one_iff_adj.mpr had.symm
      have hdi : G.dist c (P.getVert i) = i := by
        simpa [getVert_zero] using wdist_eq P hpd (Nat.zero_le i) (by omega)
      have hi_eq : i = 1 := by omega
      left; simp [huc, hi_eq, getVert_zero]
    · have huA : u ∈ A := adj_comp (hmem i hi1 hi2) huc had
      rw [himg] at huA
      obtain ⟨j, hj, rfl⟩ := mem_image.mp huA; simp only [mem_Icc] at hj
      have hd1 := dist_eq_one_iff_adj.mpr had
      by_cases hij : i ≤ j
      · have := wdist_eq P hpd hij (by omega); have hj_eq : j = i + 1 := by omega
        right; exact ⟨by omega, by subst hj_eq; rfl⟩
      · have := wdist_eq P hpd (le_of_not_ge hij) (by omega); rw [dist_comm] at hd1
        have hj_eq : j = i - 1 := by omega
        left; subst hj_eq; rfl
  have hleaf_eq : P.getVert h = v := by simpa [hPl] using P.getVert_length
  have hleaf : ∀ u, G.Adj v u → u = P.getVert (h - 1) := fun u hu => by
    rw [← hleaf_eq] at hu
    rcases hadj h h1 le_rfl u hu with h' | ⟨hlt, _⟩
    · exact h'
    · exact absurd hlt (lt_irrefl h)
  have hdist : ∀ u ∈ A, G.dist c u ≤ h ∧ G.dist u v = h - G.dist c u ∧ (G.dist c u = h ↔ u = v) := by
    intro u hu; rw [himg] at hu; obtain ⟨i, hi, rfl⟩ := mem_image.mp hu; simp only [mem_Icc] at hi
    have hci : G.dist c (P.getVert i) = i := by
      simpa [getVert_zero] using wdist_eq P hpd (Nat.zero_le i) (by omega)
    have hiv := wdist_eq P hpd (by omega : i ≤ P.length) le_rfl
    rw [getVert_length, hPl] at hiv
    refine ⟨by omega, by omega, ⟨fun h' => by rw [show i = h by omega, hleaf_eq], fun h' => by rw [h', hv_dist]⟩⟩
  have hnocyc : ∀ {w : α} (cyc : G.Walk w w), cyc.IsCycle → ∀ u ∈ A, u ∉ cyc.support := by
    intro w cyc hcyc u hu
    have hdown : ∀ d < h, P.getVert (h - d) ∉ cyc.support := fun d hd => by
      induction d with
      | zero =>
        simp only [Nat.sub_zero]; rw [hleaf_eq]; intro hvs
        let c' := cyc.rotate v hvs; have hc' := hcyc.rotate hvs
        exact hc'.snd_ne_penultimate
          ((hleaf _ (c'.adj_snd hc'.not_nil)).trans (hleaf _ (c'.adj_penultimate hc'.not_nil).symm).symm)
      | succ d ih =>
        intro hys
        have h1' : h - d = h - (d + 1) + 1 := by omega
        have hnxt : P.getVert (h - (d + 1) + 1) ∉ cyc.support := h1' ▸ ih (by omega)
        let y := P.getVert (h - (d + 1)); let c' := cyc.rotate y hys; have hc' := hcyc.rotate hys
        have hs := (cyc.mem_support_rotate_iff y hys).mp (snd_supp c' hc'.not_nil)
        have hp' := (cyc.mem_support_rotate_iff y hys).mp (pen_supp c' hc'.not_nil)
        have hse : c'.snd = P.getVert (h - (d + 1) - 1) := by
          rcases hadj (h - (d + 1)) (by omega) (by omega) c'.snd (c'.adj_snd hc'.not_nil) with h' | ⟨_, h'⟩
          · exact h'
          · exact absurd (h' ▸ hs) hnxt
        have hpe : c'.penultimate = P.getVert (h - (d + 1) - 1) := by
          rcases hadj (h - (d + 1)) (by omega) (by omega) c'.penultimate (c'.adj_penultimate hc'.not_nil).symm with
            h' | ⟨_, h'⟩
          · exact h'
          · exact absurd (h' ▸ hp') hnxt
        exact hc'.snd_ne_penultimate (hse.trans hpe.symm)
    rw [himg] at hu; obtain ⟨i, hi, rfl⟩ := mem_image.mp hu; simp only [mem_Icc] at hi
    have h' := hdown (h - i) (by omega)
    rwa [show h - (h - i) = i by omega] at h'
  have hv_nc : ¬ Cut G v := by
    have hadj_v : G.Adj v (P.getVert (h - 1)) := by
      have hs := P.adj_getVert_succ (by omega : h - 1 < P.length)
      rw [show h - 1 + 1 = h by omega, hleaf_eq] at hs; exact hs.symm
    exact ncut_uniq hG hadj_v hleaf
  exact ⟨hmem, himg, hadj, hleaf, hdist, hnocyc, hv_nc⟩

private lemma pend_nocyc [Fintype α] [DecidableEq α] (hG : G.Connected) {c : α} {A : Finset α}
    (hp : Pend G c A) {w : α} {cyc : G.Walk w w} (hc : cyc.IsCycle) : ∀ u ∈ A, u ∉ cyc.support := by
  obtain ⟨_, v, hvA, hv⟩ := pend_ex hG hp
  obtain ⟨P, hP, hl⟩ := hG.exists_path_of_dist c v
  exact (pend_spec hG hp hvA hv P hP (hl.trans hv)).2.2.2.2.2.1 cyc hc

private lemma pend_leaf_nc [Fintype α] [DecidableEq α] (hG : G.Connected) {c : α} {A : Finset α}
    (hp : Pend G c A) {v : α} (hvA : v ∈ A) (hv : G.dist c v = A.sup (G.dist c)) : ¬ Cut G v := by
  obtain ⟨P, hP, hl⟩ := hG.exists_path_of_dist c v
  exact (pend_spec hG hp hvA hv P hP (hl.trans hv)).2.2.2.2.2.2

end SecD

section SecE

variable {α : Type u} {G : SimpleGraph α}

private lemma mem_comp_walk [Fintype α] [DecidableEq α] {c a x y : α} {ha : a ≠ c}
    (hx : x ∈ comp G c a ha) (p : G.Walk x y) (hc : c ∉ p.support) : y ∈ comp G c a ha := by
  by_contra hy; exact hc (sep_supp hx hy p)

private lemma induce_conn_dist (S : Set α) (hne : S.Nonempty)
    (hp : ∀ a ∈ S, ∀ b ∈ S, ∃ p : G.Walk a b, p.length = G.dist a b ∧ ∀ u ∈ p.support, u ∈ S) :
    (G.induce S).Connected ∧ ∀ u v : S, (G.induce S).dist u v = G.dist u.1 v.1 := by
  have : Nonempty S := ⟨⟨hne.some, hne.some_mem⟩⟩
  have hc : (G.induce S).Connected := Connected.mk fun u v => by
    obtain ⟨p, -, hps⟩ := hp u.1 u.2 v.1 v.2; exact ⟨p.induce S hps⟩
  refine ⟨hc, fun u v => le_antisymm ?_ (dist_le_ind S (hc u v))⟩
  obtain ⟨p, hl, hps⟩ := hp u.1 u.2 v.1 v.2
  have hlen : ∀ {a b : α} (q : G.Walk a b) (hq : ∀ x ∈ q.support, x ∈ S), (q.induce S hq).length = q.length := by
    intro _ _ q hq; induction q with | nil => rfl | cons _ _ ih => exact congrArg (· + 1) (ih _)
  exact ((G.induce S).dist_le (p.induce S hps)).trans (by rw [hlen, hl])

private lemma max_tree {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β]
    (H : SimpleGraph β) : ∃ t : Finset β, (H.induce (t : Set β)).IsTree ∧ t.card = largestInducedTreeSize H := by
  classical
  obtain ⟨s, -, hsT, hmax⟩ := exists_maximum_induced_tree_containing H ∅
    ⟨{Classical.arbitrary β}, empty_subset _, tree_single _⟩
  refine ⟨s, hsT, le_antisymm (card_le_largestInducedTreeSize hsT) ?_⟩
  unfold largestInducedTreeSize
  exact csSup_le ⟨1, {Classical.arbitrary β}, card_singleton _, tree_single _⟩
    fun _ ⟨_, hn, ht⟩ => hn ▸ hmax _ (empty_subset _) ht

private lemma adj_cut [Fintype α] [DecidableEq α] (hG : G.Connected) {c a : α} (ha : a ≠ c) :
    ∃ u ∈ comp G c a ha, G.Adj u c := by
  obtain ⟨z, hzn, u, hu, had⟩ := hG.exists_adj_finset_compl ⟨a, self_comp c a ha⟩
    (fun he => nmem_comp c a ha (he ▸ mem_univ c))
  have hzc : z = c := by_contra fun h => hzn (adj_comp hu h had.symm)
  exact ⟨u, hu, hzc ▸ had.symm⟩

private lemma card_ne [Fintype α] [DecidableEq α] (v : α) :
    Fintype.card {x : α | x ≠ v} = Fintype.card α - 1 := by
  classical
  have h : Fintype.card {x : α | x ≠ v} = (univ.erase v).card := by
    rw [← Fintype.card_coe (univ.erase v)]
    exact Fintype.card_congr ⟨fun x => ⟨x.1, mem_erase.mpr ⟨x.2, mem_univ _⟩⟩,
      fun x => ⟨x.1, (mem_erase.mp x.2).1⟩, fun _ => rfl, fun _ => rfl⟩
  rw [h, card_erase_of_mem (mem_univ v), card_univ]

private lemma comp_laminar [Fintype α] [DecidableEq α] (hG : G.Connected) {r0 c1 c2 a1 a2 : α}
    {ha1 : a1 ≠ c1} {ha2 : a2 ≠ c2} (hr1 : r0 ∉ comp G c1 a1 ha1) (hr2 : r0 ∉ comp G c2 a2 ha2) :
    Disjoint (comp G c1 a1 ha1) (comp G c2 a2 ha2) ∨
      comp G c1 a1 ha1 ⊆ comp G c2 a2 ha2 ∨ comp G c2 a2 ha2 ⊆ comp G c1 a1 ha1 := by
  by_cases hd : Disjoint (comp G c1 a1 ha1) (comp G c2 a2 ha2); · exact Or.inl hd
  right; obtain ⟨z, hz1, hz2⟩ := not_disjoint_iff.mp hd
  have hsub : ∀ {c1 c2 a1 a2 : α} {ha1 : a1 ≠ c1} {ha2 : a2 ≠ c2} {z : α},
      z ∈ comp G c1 a1 ha1 → z ∈ comp G c2 a2 ha2 → c2 ∉ comp G c1 a1 ha1 →
      comp G c1 a1 ha1 ⊆ comp G c2 a2 ha2 := by
    intro c1 c2 a1 a2 ha1 ha2 z hz1 hz2 hc2 x hx1
    have hn1 := ne_comp hz1; have hn2 := ne_comp hz2
    rw [← eq_comp hn1 hz1] at hx1 hc2; rw [← eq_comp hn2 hz2]
    obtain ⟨_, ⟨q⟩⟩ := (mem_comp hn1).mp hx1
    let q' := q.map (Embedding.induce {u | u ≠ c1}).toHom
    refine mem_comp_walk (self_comp c2 z hn2) q' fun hmem => ?_
    have hmem' : c2 ∈ q'.support := hmem
    rw [Walk.support_map, List.mem_map] at hmem'
    obtain ⟨w, hw, hw2⟩ := hmem'
    exact hc2 (hw2 ▸ (mem_comp hn1).mpr ⟨w.2, (q.takeUntil w hw).reachable⟩)
  by_cases hc2 : c2 ∈ comp G c1 a1 ha1
  · right; refine hsub hz2 hz1 fun hc1 => ?_
    obtain ⟨p, -, -, hp⟩ := avoid_path hG (nmem_comp c2 a2 ha2) hr2
    exact hr1 (mem_comp_walk hc2 p fun hm => hp c1 hm hc1)
  · exact Or.inl (hsub hz1 hz2 hc2)

private lemma tree_union_pend [Fintype α] [DecidableEq α] (hG : G.Connected) {a : α} {A T : Finset α}
    (hp : Pend G a A) (hT : (G.induce (T : Set α)).IsTree) (haT : a ∈ T) (hdisj : Disjoint T A) :
    (G.induce ((T ∪ A : Finset α) : Set α)).IsTree := by
  obtain ⟨h1, v, hvA, hvd⟩ := pend_ex hG hp
  obtain ⟨P, hPp, hPl⟩ := hG.exists_path_of_dist a v
  have hs := pend_spec hG hp hvA hvd P hPp (hPl.trans hvd)
  set h := A.sup (G.dist a)
  let S : ℕ → Finset α := fun k => T ∪ (Icc 1 k).image P.getVert
  have hb : ∀ k ≤ h, (G.induce ((S k : Finset α) : Set α)).IsTree := fun k => by
    induction k with
    | zero =>
      intro _
      have h0 : S 0 = T := by simp [S]
      rwa [h0]
    | succ k ih =>
      intro hk
      let u := P.getVert (k + 1); let prev := P.getVert k
      have hSk1 : S (k + 1) = insert u (S k) := by
        ext x; simp only [S, mem_insert, mem_union, mem_image, mem_Icc]
        constructor
        · rintro (h' | ⟨j, ⟨hj1, hj2⟩, rfl⟩)
          · exact Or.inr (Or.inl h')
          · by_cases hj : j = k + 1
            · exact Or.inl (by rw [hj])
            · exact Or.inr (Or.inr ⟨j, ⟨hj1, by omega⟩, rfl⟩)
        · rintro (rfl | h' | ⟨j, ⟨hj1, hj2⟩, rfl⟩)
          · exact Or.inr ⟨k + 1, ⟨by omega, le_rfl⟩, rfl⟩
          · exact Or.inl h'
          · exact Or.inr ⟨j, ⟨hj1, by omega⟩, rfl⟩
      have huA : u ∈ A := hs.1 (k + 1) (by omega) hk
      have hun : u ∉ S k := by
        simp only [S, mem_union, mem_image, mem_Icc]
        rintro (huT | ⟨j, ⟨hj1, hj2⟩, hju⟩)
        · exact disjoint_left.mp hdisj huT huA
        · have hd1 : G.dist a u = k + 1 := by simpa [u, getVert_zero] using wdist_eq P hPl (Nat.zero_le (k + 1)) (by omega)
          have hd2 : G.dist a (P.getVert j) = j := by simpa [getVert_zero] using wdist_eq P hPl (Nat.zero_le j) (by omega)
          rw [hju] at hd2; omega
      have hpm : prev ∈ S k := by
        simp only [S, mem_union, mem_image, mem_Icc]
        cases k with
        | zero => left; simpa [prev, P.getVert_zero] using haT
        | succ k' => right; exact ⟨k' + 1, ⟨by omega, le_rfl⟩, rfl⟩
      have had : G.Adj u prev := (P.adj_getVert_succ (by omega : k < P.length)).symm
      have hunq : ∀ ⦃y⦄, y ∈ S k → G.Adj u y → y = prev := fun y hyS hyu => by
        rcases hs.2.2.1 (k + 1) (by omega) hk y hyu with hl | ⟨hlt, hr⟩
        · simpa [prev] using hl
        · exfalso; have hyA : y ∈ A := hr ▸ hs.1 (k + 2) (by omega) (by omega)
          simp only [S, mem_union, mem_image, mem_Icc] at hyS
          rcases hyS with hyT | ⟨j, ⟨hj1, hj2⟩, hjy⟩
          · exact disjoint_left.mp hdisj hyT hyA
          · have hd1 : G.dist a y = k + 2 := by rw [hr]; simpa [getVert_zero] using wdist_eq P hPl (Nat.zero_le (k + 2)) (by omega)
            have hd2 : G.dist a (P.getVert j) = j := by simpa [getVert_zero] using wdist_eq P hPl (Nat.zero_le j) (by omega)
            rw [hjy] at hd2; omega
      rw [hSk1]; exact (ih (by omega)).induce_insert_of_unique_adj hun hpm had hunq
  have hSh : S h = T ∪ A := by simp only [S]; rw [← hs.2.1]
  rw [← hSh]; exact hb h le_rfl

private lemma tree_biUnion [Fintype α] [DecidableEq α] (hG : G.Connected) {T0 : Finset α}
    (hT0 : (G.induce (T0 : Set α)).IsTree) (Am : α → Finset α)
    (hp : ∀ v ∈ T0, Pend G v (Am v)) (hdb : ∀ v ∈ T0, Disjoint T0 (Am v))
    (hdp : ∀ v ∈ T0, ∀ w ∈ T0, v ≠ w → Disjoint (Am v) (Am w)) :
    (G.induce ((T0 ∪ T0.biUnion Am : Finset α) : Set α)).IsTree ∧
      (T0 ∪ T0.biUnion Am).card = T0.card + ∑ v ∈ T0, (Am v).card := by
  classical
  have hb : ∀ S : Finset α, S ⊆ T0 → (G.induce ((T0 ∪ S.biUnion Am : Finset α) : Set α)).IsTree := fun S => by
    induction S using Finset.induction_on with
    | empty =>
      intro _
      have h0 : T0 ∪ (∅ : Finset α).biUnion Am = T0 := by simp
      rwa [h0]
    | @insert v S' hvn ih =>
      intro hs
      have hv : v ∈ T0 := hs (mem_insert_self v S')
      have hs' : S' ⊆ T0 := fun x hx => hs (mem_insert_of_mem hx)
      have hd : Disjoint (T0 ∪ S'.biUnion Am) (Am v) := by
        rw [disjoint_union_left]
        refine ⟨hdb v hv, disjoint_left.mpr fun x hx hxv => ?_⟩
        obtain ⟨w, hw, hxw⟩ := mem_biUnion.mp hx
        exact disjoint_left.mp (hdp w (hs' hw) v hv (fun hwe => hvn (hwe ▸ hw))) hxw hxv
      have huni : T0 ∪ (insert v S').biUnion Am = (T0 ∪ S'.biUnion Am) ∪ Am v := by
        rw [biUnion_insert, union_left_comm, union_assoc]; ext x; simp only [mem_union]; tauto
      rw [huni]; exact tree_union_pend hG (hp v hv) (ih hs') (mem_union_left _ hv) hd
  have hd0 : Disjoint T0 (T0.biUnion Am) := disjoint_left.mpr fun x hxT hxU => by
    obtain ⟨v, hv, hxv⟩ := mem_biUnion.mp hxU; exact disjoint_left.mp (hdb v hv) hxT hxv
  refine ⟨hb T0 Subset.rfl, ?_⟩
  rw [card_union_of_disjoint hd0, card_biUnion (fun v hv w hw hvw => hdp v hv w hw hvw)]

private lemma witness {α : Type u} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (hG : G.Connected) (hcut : HasCut G)
    (hr3 : 3 ≤ G.radius.toNat) (hsmall : largestInducedTreeSize G < 2 * G.radius.toNat)
    (ih : ∀ {β : Type u} [Fintype β] [DecidableEq β], Fintype.card β < Fintype.card α →
      ∀ (H : SimpleGraph β), H.Connected → HasCut H → 2 * H.radius.toNat ≤ largestInducedTreeSize H)
    (v : α) (hvnc : ¬ Cut G v) :
    ∃ w : α, w ≠ v ∧ G.dist w v = G.radius.toNat ∧ ∀ y : α, y ≠ v → G.dist w y ≤ G.radius.toNat - 1 := by
  classical
  have : Nonempty α := hG.nonempty
  set r := G.radius.toNat
  have h4 : 4 ≤ Fintype.card α := by
    obtain ⟨x0, y0, hxy⟩ := G.exists_dist_eq_diam
    obtain ⟨p, hp, hl⟩ := hG.exists_path_of_dist x0 y0
    have := rad_le_diam hG; have := hp.length_lt; omega
  let Sv : Set α := {x | x ≠ v}; let Gv := G.induce Sv
  have hlt : Fintype.card Sv < Fintype.card α :=
    Fintype.card_subtype_lt (p := fun x => x ≠ v) (x := v) fun h => h rfl
  have hcard_Sv : Fintype.card Sv = Fintype.card α - 1 := card_ne v
  have hne_Sv : ∃ z : α, z ≠ v := by
    obtain ⟨z⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card Sv); exact ⟨z.1, z.2⟩
  have : Nonempty Sv := ⟨⟨hne_Sv.choose, hne_Sv.choose_spec⟩⟩
  have hGv : Gv.Connected := Connected.mk (not_not.mp hvnc)
  have hGv_sm : largestInducedTreeSize Gv < 2 * r := lt_of_le_of_lt (lit_induce_le Sv) hsmall
  have hGv_le : Gv.radius.toNat ≤ r - 1 := by
    by_contra hge; have hge' : r ≤ Gv.radius.toNat := by omega
    rcases Nat.lt_or_eq_of_le hge' with hgt | heq
    · have := two_rad_sub_two Gv hGv; omega
    · by_cases hcv : HasCut Gv
      · have := ih hlt Gv hGv hcv; omega
      · obtain ⟨c, hcc⟩ := hcut
        have hvcn : v ≠ c := fun h => hvnc (h ▸ hcc)
        let cv : Sv := ⟨c, hvcn.symm⟩
        have hc_pre : (Gv.induce {u | u ≠ cv}).Preconnected := not_not.mp fun hc => hcv ⟨cv, hc⟩
        have hnp : ¬ (G.induce {x | x ≠ c}).Preconnected := hcc
        simp only [Preconnected, not_forall] at hnp
        obtain ⟨a, b, hab⟩ := hnp
        let f : (Gv.induce {u | u ≠ cv}) →g (G.induce {x | x ≠ c}) :=
          ⟨fun u => ⟨u.1.1, fun h => u.2 (Subtype.ext h)⟩, fun e => e⟩
        have hrg : ∀ {x y : {x : α | x ≠ c}} (hx : x.1 ≠ v) (hy : y.1 ≠ v),
            (Gv.induce {u | u ≠ cv}).Reachable
              ⟨⟨x.1, hx⟩, fun h => x.2 (congrArg Subtype.val h)⟩
              ⟨⟨y.1, hy⟩, fun h => y.2 (congrArg Subtype.val h)⟩ →
            (G.induce {x | x ≠ c}).Reachable x y := fun _ _ ⟨q⟩ => ⟨q.map f⟩
        have hvab : a.1 = v ∨ b.1 = v := by
          by_contra hn; push Not at hn; exact hab (hrg hn.1 hn.2 (hc_pre _ _))
        have hstep : ∀ {a0 b0 : {x : α | x ≠ c}}, a0.1 = v →
            ¬ (G.induce {x | x ≠ c}).Reachable a0 b0 → ∀ u, G.Adj v u → u = c := fun {a0 b0} ha0 hnot u had => by
          by_contra huc
          have hbv : b0.1 ≠ v := fun hbv => hnot (by rw [Subtype.ext (ha0.trans hbv.symm)])
          have h1 : (G.induce {x | x ≠ c}).Reachable a0 ⟨u, huc⟩ :=
            Adj.reachable (by simpa [ha0] using had)
          exact hnot (h1.trans (hrg had.ne.symm hbv (hc_pre _ _)))
        have huniq : ∀ u, G.Adj v u → u = c := by
          rcases hvab with h1 | h1
          · exact hstep h1 hab
          · exact hstep h1 (fun r => hab r.symm)
        have hvc : G.Adj v c := by
          obtain ⟨p⟩ := hG v c
          cases p with | nil => exact absurd rfl hvcn | cons h _ => exact (huniq _ h) ▸ h
        have hne_c : ∃ u : α, u ≠ v ∧ u ≠ c ∧ G.Adj c u := by
          have hns : ¬ (univ.erase v ⊆ {c}) := fun hs => by
            have := card_le_card hs; rw [card_erase_of_mem (mem_univ v), card_univ, card_singleton] at this; omega
          obtain ⟨b0, hb0, hbc⟩ := not_subset.mp hns
          simp only [mem_erase, mem_univ, mem_singleton, and_true] at hb0 hbc
          obtain ⟨q⟩ := hGv cv ⟨b0, hb0⟩
          have hst : ∀ {x y : Sv}, x ≠ y → Gv.Walk x y → ∃ w : Sv, w ≠ x ∧ Gv.Adj x w := fun hxy p => by
            cases p with | nil => exact absurd rfl hxy | cons h _ => exact ⟨_, h.ne.symm, h⟩
          obtain ⟨w, hwc, hcw⟩ := hst (fun h => hbc (congrArg Subtype.val h).symm) q
          exact ⟨w.1, w.2, fun hwe => hwc (Subtype.ext hwe), hcw⟩
        obtain ⟨u, huv, huc, hcu⟩ := hne_c
        let Su : Set α := {x | x ≠ u}; let Gu := G.induce Su
        have hltu : Fintype.card Su < Fintype.card α :=
          Fintype.card_subtype_lt (p := fun x => x ≠ u) (x := u) fun h => h rfl
        have hcard_Su : Fintype.card Su = Fintype.card α - 1 := card_ne u
        have hSu3 : 3 ≤ Fintype.card Su := by omega
        let g : (Gv.induce {w : Sv | w ≠ ⟨u, huv⟩}) →g Gu :=
          ⟨fun m => ⟨m.1.1, fun h => m.2 (Subtype.ext h)⟩, fun e => e⟩
        have hpre_u : ∀ x : Su, x.1 ≠ v → Gu.Reachable ⟨c, huc.symm⟩ x := fun x hxv => by
          obtain ⟨q⟩ := not_not.mp (fun hc => hcv ⟨⟨u, huv⟩, hc⟩)
            ⟨cv, fun h => huc (congrArg Subtype.val h).symm⟩
            ⟨⟨x.1, hxv⟩, fun h => x.2 (congrArg Subtype.val h)⟩
          exact ⟨q.map g⟩
        have hGu : Gu.Connected := by
          have : Nonempty Su := ⟨⟨c, huc.symm⟩⟩
          refine Connected.mk fun x y => ?_
          have hr : ∀ z : Su, Gu.Reachable ⟨c, huc.symm⟩ z := fun z => by
            by_cases hzv : z.1 = v
            · rw [show z = ⟨v, huv.symm⟩ from Subtype.ext hzv]
              exact Adj.reachable (show Gu.Adj ⟨c, huc.symm⟩ ⟨v, huv.symm⟩ from hvc.symm)
            · exact hpre_u z hzv
          exact (hr x).symm.trans (hr y)
        have hcut_u : Cut Gu ⟨c, huc.symm⟩ :=
          cut_uniq (G := Gu) hSu3 (v := ⟨v, huv.symm⟩) (c := ⟨c, huc.symm⟩)
            (show Gu.Adj ⟨v, huv.symm⟩ ⟨c, huc.symm⟩ from hvc) fun w hw => Subtype.ext (huniq w.1 hw)
        have hGu_sm : largestInducedTreeSize Gu < 2 * r := lt_of_le_of_lt (lit_induce_le Su) hsmall
        have hGu_rad : Gu.radius.toNat ≤ r - 1 := by have := ih hltu Gu hGu ⟨⟨c, huc.symm⟩, hcut_u⟩; omega
        have : Nonempty Su := hGu.nonempty
        obtain ⟨⟨w, hwu⟩, hwr⟩ := center_ex hGu
        have hwall : ∀ y, y ≠ u → G.dist w y ≤ r - 1 := fun y hyu => by
          have h1 : G.dist w y ≤ Gu.dist ⟨w, hwu⟩ ⟨y, hyu⟩ := dist_le_ind Su (hGu ⟨w, hwu⟩ ⟨y, hyu⟩)
          have h2 : Gu.dist ⟨w, hwu⟩ ⟨y, hyu⟩ ≤ Gu.radius.toNat := hwr ⟨y, hyu⟩
          omega
        have hwuge : r ≤ G.dist w u := by
          obtain ⟨y, hy⟩ := rad_ge_ex hG w
          by_cases hyu : y = u; · rwa [hyu] at hy
          · have := hwall y hyu; omega
        have hwv : w ≠ v := fun hwv_eq => by
          have := dist_eq_one_iff_adj.mpr hvc; have := dist_eq_one_iff_adj.mpr hcu
          have := (hG c u).dist_triangle_right v; rw [← hwv_eq] at *; omega
        have hwnv : w ∉ comp G c v hvcn := fun hw => hwv <| by
          obtain ⟨_, ⟨p⟩⟩ := (mem_comp hvcn).mp hw
          have hs : ∀ {a b : {y : α | y ≠ c}}, (G.induce {y | y ≠ c}).Walk a b → a.1 = v → b.1 = v := fun q => by
            induction q with | nil => exact fun h => h | @cons _ n _ h _ _ =>
              intro hm; exact absurd (huniq n.1 (by simpa [hm] using h)) n.2
          exact hs p rfl
        have hsep := sep_dist hG (self_comp c v hvcn) hwnv
        have hvw : G.dist v w ≤ r - 1 := by rw [dist_comm]; exact hwall v huv.symm
        have := dist_eq_one_iff_adj.mpr hvc; have := dist_eq_one_iff_adj.mpr hcu
        have := (hG c u).dist_triangle_right w; have : G.dist w c = G.dist c w := dist_comm; omega
  have : Nonempty Sv := hGv.nonempty
  obtain ⟨⟨w, hwv⟩, hwr⟩ := center_ex hGv
  have hwall : ∀ y, y ≠ v → G.dist w y ≤ r - 1 := fun y hyv => by
    have h1 : G.dist w y ≤ Gv.dist ⟨w, hwv⟩ ⟨y, hyv⟩ := dist_le_ind Sv (hGv ⟨w, hwv⟩ ⟨y, hyv⟩)
    have h2 : Gv.dist ⟨w, hwv⟩ ⟨y, hyv⟩ ≤ Gv.radius.toNat := hwr ⟨y, hyv⟩
    omega
  have hwvge : r ≤ G.dist w v := by
    obtain ⟨y, hy⟩ := rad_ge_ex hG w
    by_cases hyv : y = v; · rwa [hyv] at hy
    · have := hwall y hyv; omega
  obtain ⟨u, hvu⟩ : ∃ u, G.Adj v u := by
    obtain ⟨p⟩ := hG v w; cases p with | nil => exact absurd rfl hwv.symm | cons h _ => exact ⟨_, h⟩
  have := (hG u v).dist_triangle_right w; have := dist_eq_one_iff_adj.mpr hvu.symm
  have := hwall u hvu.ne.symm
  exact ⟨w, hwv, by omega, hwall⟩

private lemma nonpend_lt {α : Type u} [Fintype α] [DecidableEq α] (G : SimpleGraph α) (hG : G.Connected)
    (hr1 : 1 ≤ G.radius.toNat)
    (hwit : ∀ v, ¬ Cut G v → ∃ w, w ≠ v ∧ G.dist w v = G.radius.toNat ∧ ∀ y, y ≠ v → G.dist w y ≤ G.radius.toNat - 1)
    {c a : α} (ha : a ≠ c) (hb : ∃ b, b ≠ c ∧ b ∉ comp G c a ha) (hnp : ¬ Pend G c (comp G c a ha)) :
    (univ \ comp G c a ha).sup (G.dist c) < (comp G c a ha).sup (G.dist c) := by
  classical
  set r := G.radius.toNat; set A := comp G c a ha; set hA := A.sup (G.dist c)
  set Ac := univ \ A; set h' := Ac.sup (G.dist c)
  have hlt : hA < A.card := lt_of_le_of_ne (comp_sup_le_card hG ha) fun h => hnp ⟨a, ha, rfl, hb, h.symm⟩
  obtain ⟨v, hvA, hve⟩ := exists_mem_eq_sup A ⟨a, self_comp c a ha⟩ (G.dist c)
  have hv_d : G.dist c v = hA := hve.symm
  have hAc_ne : Ac.Nonempty := by obtain ⟨b, -, hn⟩ := hb; exact ⟨b, mem_sdiff.mpr ⟨mem_univ b, hn⟩⟩
  obtain ⟨ys, hys_Ac, hys_e⟩ := exists_mem_eq_sup Ac hAc_ne (G.dist c)
  have hys_d : G.dist c ys = h' := hys_e.symm
  have hys_nA : ys ∉ A := (mem_sdiff.mp hys_Ac).2
  have hvnc : ¬ Cut G v := ncut_reach (ne_comp hvA).symm fun x hxv => by
    by_cases hxA : x ∈ A
    · obtain ⟨q, -, hql⟩ := hG.exists_path_of_dist c x
      refine ⟨q.reverse, fun hvs => ?_⟩
      rw [support_reverse, List.mem_reverse] at hvs
      have := wdist_add q hql hvs; have := le_sup (f := G.dist c) hxA
      exact hxv ((hG v x).dist_eq_zero_iff.mp (by omega)).symm
    · obtain ⟨q, -, -, hqa⟩ := avoid_path hG hxA (nmem_comp c a ha)
      exact ⟨q, fun hvs => hqa v hvs hvA⟩
  obtain ⟨P, hPp, hPl⟩ := hG.exists_path_of_dist c v
  have hPl' : P.length = hA := hPl.trans hv_d
  have hU_ne : (A \ P.support.toFinset).Nonempty := by
    have hs : A ∩ P.support.toFinset ⊆ P.support.toFinset.erase c := fun x hx => by
      rw [mem_inter] at hx; exact mem_erase.mpr ⟨fun h => nmem_comp c a ha (h ▸ hx.1), hx.2⟩
    have hci : (A ∩ P.support.toFinset).card ≤ hA := by
      calc (A ∩ P.support.toFinset).card ≤ (P.support.toFinset.erase c).card := card_le_card hs
        _ = P.support.toFinset.card - 1 := card_erase_of_mem (List.mem_toFinset.mpr P.start_mem_support)
        _ = hA := by rw [List.toFinset_card_of_nodup hPp.support_nodup, P.length_support, hPl']; omega
    have := card_sdiff_add_card_inter A P.support.toFinset
    exact card_pos.mp (by omega)
  obtain ⟨z, hzU, hzmax⟩ := exists_mem_eq_sup _ hU_ne (G.dist c)
  have hzA := (mem_sdiff.mp hzU).1; have hznP := (mem_sdiff.mp hzU).2
  have hzv : z ≠ v := fun h => hznP (List.mem_toFinset.mpr (h ▸ P.end_mem_support))
  have hznc : ¬ Cut G z := ncut_reach (ne_comp hzA).symm fun x hxz => by
    by_cases hxA : x ∈ A
    · by_cases hxP : x ∈ P.support
      · refine ⟨(P.takeUntil x hxP).reverse, fun hzs => hznP (List.mem_toFinset.mpr ?_)⟩
        rw [support_reverse, List.mem_reverse] at hzs
        rw [← P.take_spec hxP, support_append, List.mem_append]; exact Or.inl hzs
      · obtain ⟨q, -, hql⟩ := hG.exists_path_of_dist c x
        refine ⟨q.reverse, fun hzs => ?_⟩
        rw [support_reverse, List.mem_reverse] at hzs
        have := wdist_add q hql hzs
        have := le_sup (f := G.dist c) (mem_sdiff.mpr ⟨hxA, fun hm => hxP (List.mem_toFinset.mp hm)⟩)
        exact hxz ((hG z x).dist_eq_zero_iff.mp (by omega)).symm
    · obtain ⟨q, -, -, hqa⟩ := avoid_path hG hxA (nmem_comp c a ha)
      exact ⟨q, fun hzs => hqa z hzs hzA⟩
  obtain ⟨wv, -, hwvv, hwva⟩ := hwit v hvnc
  by_cases hwvA : wv ∈ A
  · have hsep := sep_dist hG hwvA hys_nA; have hwy := hwva ys (fun h => hys_nA (h ▸ hvA))
    have htri := (hG c v).dist_triangle_right wv; omega
  · have hsv := sep_dist hG hvA hwvA; have hsz := sep_dist hG hzA hwvA
    have hwz := hwva z hzv
    have : G.dist v wv = G.dist wv v := dist_comm; have : G.dist c wv = G.dist wv c := dist_comm
    have : G.dist z wv = G.dist wv z := dist_comm; have : G.dist v c = G.dist c v := dist_comm
    have : G.dist z c = G.dist c z := dist_comm
    have hdz : G.dist c z < hA := by omega
    obtain ⟨wz, -, hwzz, hwza⟩ := hwit z hznc
    have hwzA : wz ∈ A := by_contra fun hn => by
      have h1 := sep_dist hG hzA hn; have h2 := sep_dist hG hvA hn; have h3 := hwza v hzv.symm
      have : G.dist z wz = G.dist wz z := dist_comm; have : G.dist c wz = G.dist wz c := dist_comm
      have : G.dist v wz = G.dist wz v := dist_comm; omega
    have hsy := sep_dist hG hwzA hys_nA; have hwy := hwza ys (fun h => hys_nA (h ▸ hzA))
    have htz := (hG c z).dist_triangle_right wz; omega

private lemma cor1 {α : Type u} [Fintype α] [DecidableEq α] (G : SimpleGraph α) (hG : G.Connected)
    (hr1 : 1 ≤ G.radius.toNat)
    (hwit : ∀ v, ¬ Cut G v → ∃ w, w ≠ v ∧ G.dist w v = G.radius.toNat ∧ ∀ y, y ≠ v → G.dist w y ≤ G.radius.toNat - 1)
    {c a1 a2 : α} (ha1 : a1 ≠ c) (ha2 : a2 ≠ c) (h12 : a2 ∉ comp G c a1 ha1) :
    Pend G c (comp G c a1 ha1) ∨ Pend G c (comp G c a2 ha2) := by
  by_contra hn; push Not at hn
  have ha21 : a1 ∉ comp G c a2 ha2 := fun h => h12 (by rw [eq_comp ha1 h]; exact self_comp c a2 ha2)
  have := nonpend_lt G hG hr1 hwit ha1 ⟨a2, ha2, h12⟩ hn.1
  have := nonpend_lt G hG hr1 hwit ha2 ⟨a1, ha1, ha21⟩ hn.2
  have hd := disj_comp ha2 h12
  have hl1 : (comp G c a2 ha2).sup (G.dist c) ≤ (univ \ comp G c a1 ha1).sup (G.dist c) :=
    sup_mono fun x hx => mem_sdiff.mpr ⟨mem_univ x, disjoint_left.mp hd hx⟩
  have hl2 : (comp G c a1 ha1).sup (G.dist c) ≤ (univ \ comp G c a2 ha2).sup (G.dist c) :=
    sup_mono fun x hx => mem_sdiff.mpr ⟨mem_univ x, disjoint_right.mp hd hx⟩
  omega

private lemma pend_uniq {α : Type u} [Fintype α] [DecidableEq α] (G : SimpleGraph α) (hG : G.Connected)
    (hsmall : largestInducedTreeSize G < 2 * G.radius.toNat)
    (hwit : ∀ v, ¬ Cut G v → ∃ w, w ≠ v ∧ G.dist w v = G.radius.toNat ∧ ∀ y, y ≠ v → G.dist w y ≤ G.radius.toNat - 1)
    {a : α} {A1 A2 : Finset α} (hp1 : Pend G a A1) (hp2 : Pend G a A2) : A1 = A2 := by
  classical
  have : Nonempty α := hG.nonempty; set r := G.radius.toNat
  by_contra hne
  wlog hle : A2.card ≤ A1.card generalizing A1 A2
  · exact this hp2 hp1 (Ne.symm hne) (le_of_not_ge hle)
  obtain ⟨a1, ha1, rfl, -, hc1⟩ := hp1; obtain ⟨a2, ha2, rfl, -, hc2⟩ := hp2
  set A1 := comp G a a1 ha1; set A2 := comp G a a2 ha2
  have ha2_n1 : a2 ∉ A1 := fun hm => hne (eq_comp ha2 hm).symm
  have hd12 : Disjoint A1 A2 := (disj_comp ha2 ha2_n1).symm
  have hp1' : Pend G a A1 := ⟨a1, ha1, rfl, ⟨a2, ha2, ha2_n1⟩, hc1⟩
  have hp2' : Pend G a A2 := ⟨a2, ha2, rfl, ⟨a1, ha1, disjoint_left.mp hd12 (self_comp a a1 ha1)⟩, hc2⟩
  obtain ⟨_, x1, hx1A, hx1d⟩ := pend_ex hG hp1'; obtain ⟨_, x2, hx2A, hx2d⟩ := pend_ex hG hp2'
  obtain ⟨P1, hP1p, hP1l⟩ := hG.exists_path_of_dist a x1; obtain ⟨P2, hP2p, hP2l⟩ := hG.exists_path_of_dist a x2
  set L1 := A1.card; set L2 := A2.card
  have hs1 := pend_spec hG hp1' hx1A hx1d P1 hP1p (hP1l.trans hx1d)
  have hs2 := pend_spec hG hp2' hx2A hx2d P2 hP2p (hP2l.trans hx2d)
  obtain ⟨w, -, hwx2, hwall⟩ := hwit x2 hs2.2.2.2.2.2.2
  have hx12 : x1 ≠ x2 := fun h => disjoint_left.mp hd12 hx1A (h ▸ hx2A)
  by_cases hw1 : w ∈ A1
  · have hale : ∀ y, y ∉ A1 → G.dist a y ≤ L2 := fun y hy => by
      by_cases hyx : y = x2; · rw [hyx, hx2d, ← hc2]
      · have := sep_dist hG hw1 hy; have := sep_dist hG hw1 (disjoint_right.mp hd12 hx2A)
        have := hwall y hyx; omega
    set m := (L1 - L2) / 2; set p := P1.getVert m
    have hbd : ∀ y, G.dist p y ≤ (L1 + L2 + 1) / 2 := fun y => by
      by_cases hyA : y ∈ A1
      · obtain ⟨i, hi, hy_eq⟩ := mem_image.mp (hs1.2.1 ▸ hyA); simp only [mem_Icc] at hi
        have : i ≤ L1 := by omega
        rw [← hy_eq]
        by_cases hmi : m ≤ i
        · have : G.dist p (P1.getVert i) = i - m := wdist_eq P1 hP1l hmi (by omega : i ≤ P1.length)
          omega
        · have : G.dist (P1.getVert i) p = m - i := wdist_eq P1 hP1l (le_of_not_ge hmi) (by omega : m ≤ P1.length)
          rw [dist_comm] at this; omega
      · by_cases hm0 : m = 0
        · have : p = a := by simp [p, hm0, getVert_zero]
          rw [this]; have := hale y hyA; omega
        · have : G.dist p y = G.dist p a + G.dist a y :=
            sep_dist hG (hs1.1 m (by omega) (by omega : m ≤ A1.sup (G.dist a))) hyA
          have hdp : G.dist a p = m := by simpa [p, getVert_zero] using wdist_eq P1 hP1l (Nat.zero_le m) (by omega : m ≤ P1.length)
          have : G.dist p a = G.dist a p := dist_comm; have := hale y hyA; omega
    have := rad_le hG ⟨p, hbd⟩
    have hd_a1 : Disjoint ({a} : Finset α) A1 := disjoint_singleton_left.mpr (nmem_comp a a1 ha1)
    have hTa1 := tree_union_pend hG hp1' (tree_single a) (mem_singleton_self a) hd_a1
    have hd_a12 : Disjoint ({a} ∪ A1) A2 :=
      disjoint_union_left.mpr ⟨disjoint_singleton_left.mpr (nmem_comp a a2 ha2), hd12⟩
    have hTa12 := tree_union_pend hG hp2' hTa1 (mem_union_left _ (mem_singleton_self a)) hd_a12
    have hlt := card_le_largestInducedTreeSize hTa12
    rw [card_union_of_disjoint hd_a12, card_union_of_disjoint hd_a1, card_singleton] at hlt
    omega
  · by_cases hw2 : w ∈ A2
    · have := hs2.2.2.2.2.1 w hw2
      have := Nat.succ_le_of_lt ((hG a w).pos_dist_of_ne (ne_comp hw2).symm)
      have : G.dist w a = G.dist a w := dist_comm
      have := sep_dist hG hw2 (disjoint_left.mp hd12 hx1A); have := hwall x1 hx12; omega
    · have := sep_dist hG hx1A hw1; have := sep_dist hG hx2A hw2; have := hwall x1 hx12
      have : G.dist x1 w = G.dist w x1 := dist_comm; have : G.dist x2 w = G.dist w x2 := dist_comm
      have : G.dist x1 a = G.dist a x1 := dist_comm; have : G.dist x2 a = G.dist a x2 := dist_comm
      have : G.dist a w = G.dist w a := dist_comm; omega

private theorem cut_main :
    ∀ n : ℕ, ∀ {α : Type u} [Fintype α] [DecidableEq α], Fintype.card α = n →
      ∀ (G : SimpleGraph α), G.Connected → HasCut G → 2 * G.radius.toNat ≤ largestInducedTreeSize G := by
  intro n; induction n using Nat.strong_induction_on with
  | h n ih =>
    intro α _ _ hn G hG hcut
    classical
    have : Nonempty α := hG.nonempty; set r := G.radius.toNat
    by_contra hsm; push Not at hsm
    have hr3 : 3 ≤ r := by
      by_contra hr2
      rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with hr0 | hr1 | hr2'
      · omega
      · have := rad_le_lit hG; omega
      · obtain ⟨c, hcc⟩ := hcut; obtain ⟨x, hx⟩ := rad_ge_ex hG c
        have hxc : x ≠ c := fun h => by rw [h, dist_self] at hx; omega
        obtain ⟨b, hbc, hbn⟩ := cut_ex hcc hxc
        have := sep_dist hG (self_comp c x hxc) hbn
        have := Nat.succ_le_of_lt ((hG c b).pos_dist_of_ne hbc.symm)
        have : G.dist x c = G.dist c x := dist_comm
        have := dist_le_lit hG x b; omega
    by_cases hacyc : G.IsAcyclic
    · exact absurd (tree_two_rad_lit G ⟨hG, hacyc⟩) (by omega)
    obtain ⟨w0, cyc, hcyc⟩ : ∃ w0, ∃ cyc : G.Walk w0 w0, cyc.IsCycle := by simpa [IsAcyclic] using hacyc
    have ihc : ∀ {β : Type u} [Fintype β] [DecidableEq β], Fintype.card β < Fintype.card α →
        ∀ (H : SimpleGraph β), H.Connected → HasCut H → 2 * H.radius.toNat ≤ largestInducedTreeSize H :=
      fun {β} _ _ hlt H hH hc => ih (Fintype.card β) (hn ▸ hlt) rfl H hH hc
    have hwit := witness G hG hcut hr3 hsm ihc
    have hcor1 : ∀ {c a1 a2 : α} (ha1 : a1 ≠ c) (ha2 : a2 ≠ c), a2 ∉ comp G c a1 ha1 →
        Pend G c (comp G c a1 ha1) ∨ Pend G c (comp G c a2 ha2) :=
      fun ha1 ha2 h12 => cor1 G hG (by omega) hwit ha1 ha2 h12
    have huniq : ∀ {a : α} {A1 A2 : Finset α}, Pend G a A1 → Pend G a A2 → A1 = A2 :=
      fun hp1 hp2 => pend_uniq G hG hsm hwit hp1 hp2
    let Ps : Finset α := univ.filter fun x => ∃ c A, Pend G c A ∧ x ∈ A
    let B : Finset α := univ \ Ps
    have hw0B : w0 ∈ B := mem_sdiff.mpr ⟨mem_univ _, by
      simp only [Ps, mem_filter, mem_univ, true_and]
      rintro ⟨c, A, hp, hm⟩; exact pend_nocyc hG hp hcyc w0 hm cyc.start_mem_support⟩
    have hB3 : 3 ≤ B.card := by
      have hs : cyc.support.tail.toFinset ⊆ B := fun u hu => mem_sdiff.mpr ⟨mem_univ _, by
        simp only [Ps, mem_filter, mem_univ, true_and]; rintro ⟨c, A, hp, hm⟩
        exact pend_nocyc hG hp hcyc u hm (List.mem_of_mem_tail (List.mem_toFinset.mp hu))⟩
      have hl : cyc.support.tail.length = cyc.length := by simp [cyc.length_support]
      have hct : 3 ≤ cyc.support.tail.toFinset.card := by
        rw [List.toFinset_card_of_nodup hcyc.support_nodup, hl]; exact hcyc.three_le_length
      exact le_trans hct (card_le_card hs)
    have h4 : 4 ≤ Fintype.card α := by
      obtain ⟨x0, y0, hxy⟩ := G.exists_dist_eq_diam; obtain ⟨p, hp, hl⟩ := hG.exists_path_of_dist x0 y0
      have := rad_le_diam hG; have := hp.length_lt; omega
    have hPne : Ps.Nonempty := by
      obtain ⟨c, hcc⟩ := hcut
      obtain ⟨a, ha⟩ := card_pos.mp (by rw [card_erase_of_mem (mem_univ c), card_univ]; omega : 0 < (univ.erase c).card)
      rw [mem_erase] at ha
      obtain ⟨b, hb, hbn⟩ := cut_ex hcc ha.1
      rcases hcor1 ha.1 hb hbn with hp1 | hp2
      · exact ⟨a, mem_filter.mpr ⟨mem_univ a, c, _, hp1, self_comp c a ha.1⟩⟩
      · exact ⟨b, mem_filter.mpr ⟨mem_univ b, c, _, hp2, self_comp c b hb⟩⟩
    have hroot : ∀ x ∈ Ps, ∃ c ∈ B, ∃ A, Pend G c A ∧ x ∈ A := fun x hxP => by
      let Fx : Finset (Finset α) := univ.filter fun A => x ∈ A ∧ ∃ c, Pend G c A
      have hne : Fx.Nonempty := by
        obtain ⟨c, A, hp, hxA⟩ := (mem_filter.mp hxP).2; exact ⟨A, mem_filter.mpr ⟨mem_univ _, hxA, c, hp⟩⟩
      obtain ⟨A, hAF, hAs⟩ := exists_mem_eq_sup Fx hne Finset.card
      obtain ⟨hxA, c, hpA⟩ := (mem_filter.mp hAF).2
      refine ⟨c, ?_, A, hpA, hxA⟩
      by_contra hcnB
      have hcP : c ∈ Ps := by_contra fun h => hcnB (mem_sdiff.mpr ⟨mem_univ _, h⟩)
      obtain ⟨c', A', hpA', hcA'⟩ := (mem_filter.mp hcP).2
      obtain ⟨a, ha, hAe, -, -⟩ := id hpA; obtain ⟨a', ha', hAe', -, -⟩ := id hpA'
      set A0 := comp G c a ha; set A0' := comp G c' a' ha'
      have hw1 : w0 ∉ A0 := by rw [← hAe]; exact fun h => pend_nocyc hG hpA hcyc w0 h cyc.start_mem_support
      have hw2 : w0 ∉ A0' := by rw [← hAe']; exact fun h => pend_nocyc hG hpA' hcyc w0 h cyc.start_mem_support
      have hcA0' : c ∈ A0' := hAe' ▸ hcA'
      have hc'n : c' ∉ A0 := fun hm => by
        obtain ⟨q, -, -, hqa⟩ := avoid_path hG (nmem_comp c' a' ha') hw2
        exact hqa c (sep_supp hm hw1 q) hcA0'
      obtain ⟨u, huA0, had⟩ := adj_cut hG ha
      have huA0' : u ∈ A0' := adj_comp hcA0' (fun h => hc'n (h ▸ huA0)) had.symm
      rcases comp_laminar hG hw1 hw2 with hd | hs12 | hs21
      · exact disjoint_left.mp hd huA0 huA0'
      · have hAF' : A0' ∈ Fx := mem_filter.mpr ⟨mem_univ _, hs12 (by change x ∈ A0; rw [← hAe]; exact hxA), c', hAe' ▸ hpA'⟩
        have hle := le_sup (f := Finset.card) hAF'
        have hlt := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs12, fun h => nmem_comp c a ha (h ▸ (show c ∈ comp G c' a' ha' from hcA0'))⟩)
        change A0.card < A0'.card at hlt; rw [← hAe] at hlt; omega
      · exact nmem_comp c a ha (hs21 hcA0')
    let Am : α → Finset α := fun a => if h : a ∈ B ∧ ∃ A, Pend G a A then h.2.choose else ∅
    let L : α → ℕ := fun a => (Am a).card
    have hAm_eq : ∀ {a A}, a ∈ B → Pend G a A → A = Am a := fun {a A} haB hp => by
      have hc : a ∈ B ∧ ∃ A', Pend G a A' := ⟨haB, A, hp⟩
      simp only [Am, dif_pos hc]; exact huniq hp hc.2.choose_spec
    have hAm_p : ∀ {a}, a ∈ B → 1 ≤ L a → Pend G a (Am a) := fun {a} haB h1 => by
      by_cases hex : ∃ A, Pend G a A
      · have hc : a ∈ B ∧ ∃ A, Pend G a A := ⟨haB, hex⟩; simpa [Am, dif_pos hc] using hc.2.choose_spec
      · exfalso; have h0 : (Am a).card = 0 := by simp [Am, hex]
        have h1' : 1 ≤ (Am a).card := h1; omega
    have hAm_dp : ∀ {a1 a2}, a1 ∈ B → a2 ∈ B → a1 ≠ a2 → Disjoint (Am a1) (Am a2) := fun {a1 a2} ha1 ha2 hne => by
      by_contra hn; obtain ⟨z, hz1, hz2⟩ := not_disjoint_iff.mp hn
      have hp1 := hAm_p ha1 (card_pos.mpr ⟨z, hz1⟩); have hp2 := hAm_p ha2 (card_pos.mpr ⟨z, hz2⟩)
      obtain ⟨u1, hu1, heq1, -, -⟩ := id hp1; obtain ⟨u2, hu2, heq2, -, -⟩ := id hp2
      have hw1 : w0 ∉ Am a1 := fun h => pend_nocyc hG hp1 hcyc w0 h cyc.start_mem_support
      have hw2 : w0 ∉ Am a2 := fun h => pend_nocyc hG hp2 hcyc w0 h cyc.start_mem_support
      rw [heq1] at hz1 hw1; rw [heq2] at hz2 hw2
      rcases comp_laminar hG hw1 hw2 with hd | hs12 | hs21
      · exact disjoint_left.mp hd hz1 hz2
      · obtain ⟨u, huA, had⟩ := adj_cut hG hu1
        exact (fun hm => (mem_sdiff.mp ha1).2 (mem_filter.mpr ⟨mem_univ _, a2, Am a2, hp2, heq2 ▸ hm⟩))
          (adj_comp (hs12 huA) hne had)
      · obtain ⟨u, huA, had⟩ := adj_cut hG hu2
        exact (fun hm => (mem_sdiff.mp ha2).2 (mem_filter.mpr ⟨mem_univ _, a1, Am a1, hp1, heq1 ▸ hm⟩))
          (adj_comp (hs21 huA) hne.symm had)
    have hPeq : Ps = B.biUnion Am := by
      ext x; simp only [mem_biUnion]
      exact ⟨fun hx => by obtain ⟨c, hcB, A, hp, hxA⟩ := hroot x hx; exact ⟨c, hcB, hAm_eq hcB hp ▸ hxA⟩,
        fun ⟨c, hcB, hxA⟩ => mem_filter.mpr ⟨mem_univ _, c, Am c, hAm_p hcB (card_pos.mpr ⟨x, hxA⟩), hxA⟩⟩
    have hAm_dB : ∀ {a}, a ∈ B → Disjoint B (Am a) := fun haB => disjoint_left.mpr fun x hxB hxA =>
      (mem_sdiff.mp hxB).2 (hPeq ▸ mem_biUnion.mpr ⟨_, haB, hxA⟩)
    let xl : α → α := fun a => if h : Pend G a (Am a) then (pend_ex hG h).2.choose else a
    have hnp0 : ∀ {a}, L a = 0 → ¬ Pend G a (Am a) := fun {a} h0 hp => by
      have := (pend_ex hG hp).1; have := hp.choose_spec.choose_spec.2.2; change (Am a).card = 0 at h0; omega
    have hxl0 : ∀ {a}, L a = 0 → xl a = a := fun {a} h0 => by simp [xl, dif_neg (hnp0 h0)]
    have hxl_spec : ∀ {a}, a ∈ B → 1 ≤ L a → xl a ∈ Am a ∧ G.dist a (xl a) = L a ∧
        (∀ y ∈ Am a, G.dist a y ≤ L a ∧ G.dist y (xl a) = L a - G.dist a y) ∧ ¬ Cut G (xl a) := by
      intro a haB hl
      have hp := hAm_p haB hl; simp only [xl, dif_pos hp]
      set x := (pend_ex hG hp).2.choose
      have hxA := (pend_ex hG hp).2.choose_spec.1; have hxd := (pend_ex hG hp).2.choose_spec.2
      obtain ⟨P, hPp, hPl⟩ := hG.exists_path_of_dist a x
      have hce : (Am a).sup (G.dist a) = L a := hp.choose_spec.choose_spec.2.2.symm
      have hs := pend_spec hG hp hxA hxd P hPp (hPl.trans hxd)
      refine ⟨hxA, by rw [hxd, hce], fun y hy => ?_, pend_leaf_nc hG hp hxA hxd⟩
      have hys := hs.2.2.2.2.1 y hy; exact ⟨hys.1.trans_eq hce, by rw [← hce]; exact hys.2.1⟩
    have hxl_nm : ∀ {a b}, a ∈ B → b ∈ B → a ≠ b → xl a ∉ Am b := fun {a b} ha hb hab => by
      by_cases h1 : 1 ≤ L a
      · exact disjoint_left.mp (hAm_dp ha hb hab) (hxl_spec ha h1).1
      · rw [hxl0 (by omega)]; exact disjoint_left.mp (hAm_dB hb) ha
    have hxl_ne : ∀ {a b}, a ∈ B → b ∈ B → a ≠ b → xl a ≠ xl b := fun {a b} ha hb hab heq => by
      by_cases hb1 : 1 ≤ L b
      · exact hxl_nm ha hb hab (heq ▸ (hxl_spec hb hb1).1)
      · have hxb := hxl0 (a := b) (by omega)
        by_cases ha1 : 1 ≤ L a
        · exact disjoint_left.mp (hAm_dB ha) (by rw [heq, hxb]; exact hb) (hxl_spec ha ha1).1
        · exact hab ((hxl0 (a := a) (by omega)).symm.trans (heq.trans hxb))
    have hxl_nc : ∀ {a}, a ∈ B → ¬ Cut G (xl a) := fun {a} haB => by
      by_cases h1 : 1 ≤ L a
      · exact (hxl_spec haB h1).2.2.2
      · have h0 : L a = 0 := by omega
        rw [hxl0 h0]; intro hca
        obtain ⟨u, hu⟩ := card_pos.mp (by rw [card_erase_of_mem haB]; omega : 0 < (B.erase a).card)
        rw [mem_erase] at hu
        obtain ⟨v, hva, hvn⟩ := cut_ex hca hu.1
        rcases hcor1 hu.1 hva hvn with hp1 | hp2
        · exact hnp0 h0 ((hAm_eq haB hp1) ▸ hp1)
        · exact hnp0 h0 ((hAm_eq haB hp2) ▸ hp2)
    have hdl_out : ∀ {a}, a ∈ B → ∀ z, z ∉ Am a → G.dist z (xl a) = G.dist z a + L a := fun {a} haB z hz => by
      by_cases h1 : 1 ≤ L a
      · obtain ⟨hxA, hdx, -, -⟩ := hxl_spec haB h1
        obtain ⟨u, hu, heq, -, -⟩ := hAm_p haB h1
        rw [heq] at hxA hz
        have := sep_dist hG hxA hz
        have : G.dist z (xl a) = G.dist (xl a) z := dist_comm; have : G.dist z a = G.dist a z := dist_comm
        have : G.dist (xl a) a = G.dist a (xl a) := dist_comm; omega
      · have h0 : L a = 0 := by omega
        rw [hxl0 h0, h0, add_zero]
    let GB := G.induce (B : Set α)
    have hGBcd : GB.Connected ∧ ∀ u v : B, GB.dist u v = G.dist u.1 v.1 :=
      induce_conn_dist (B : Set α) ⟨w0, hw0B⟩ fun x hx y hy => by
        obtain ⟨p, hp, hl⟩ := hG.exists_path_of_dist x y
        refine ⟨p, hl, fun u hu => ?_⟩
        by_contra huB
        have huP : u ∈ Ps := by_contra fun h => huB (mem_coe.mpr (mem_sdiff.mpr ⟨mem_univ _, h⟩))
        rw [hPeq, mem_biUnion] at huP; obtain ⟨a, haB, huA⟩ := huP
        obtain ⟨a0, ha0, heq, -, -⟩ := hAm_p haB (card_pos.mpr ⟨u, huA⟩)
        exact path_avoid (heq ▸ disjoint_left.mp (hAm_dB haB) hx) (heq ▸ disjoint_left.mp (hAm_dB haB) hy)
          hp u hu (heq ▸ huA)
    have hGB := hGBcd.1; have hGBd := hGBcd.2
    obtain ⟨as, hasB, hasmin⟩ := exists_min_image B L ⟨w0, hw0B⟩
    set L0 := L as
    have hLadj : ∀ {a u}, a ∈ B → u ∈ B → L a = L0 → G.Adj a u → L u = L0 := fun {a u} haB huB hLa had => by
      have hau := had.ne
      obtain ⟨w, -, hwleaf, hwall⟩ := hwit (xl a) (hxl_nc haB)
      have hxne := hxl_ne huB haB hau.symm
      by_cases hwa : w ∈ Am a
      · exfalso
        have hl1 := card_pos.mpr ⟨w, hwa⟩
        have hsw := (hxl_spec haB hl1).2.2.1 w hwa
        have haw := Nat.succ_le_of_lt ((hG a w).pos_dist_of_ne fun h => disjoint_left.mp (hAm_dB haB) haB (h ▸ hwa))
        have hxun := hxl_nm huB haB hau.symm
        obtain ⟨u0, hu0, heq, -, -⟩ := hAm_p haB hl1
        have := sep_dist hG (heq ▸ hwa) (heq ▸ hxun)
        have := hdl_out huB a (disjoint_left.mp (hAm_dB huB) haB)
        have := dist_eq_one_iff_adj.mpr had; have := hwall (xl u) hxne
        have : G.dist a w = G.dist w a := dist_comm; have := hasmin u huB; omega
      · by_cases hwu : w ∈ Am u
        · exfalso
          have hlu := card_pos.mpr ⟨w, hwu⟩
          have hne_s : (B \ {a, u}).Nonempty := card_pos.mp <| by
            have := card_le_two (a := a) (b := u)
            have := card_sdiff_add_card_inter B {a, u}
            have := card_le_card (inter_subset_right (s₁ := B) (s₂ := {a, u}))
            omega
          obtain ⟨b, hb⟩ := hne_s
          rw [mem_sdiff, mem_insert, mem_singleton, not_or] at hb
          obtain ⟨hbB, hba, hbu⟩ := hb
          obtain ⟨u0, hu0, hequ, -, -⟩ := hAm_p huB hlu
          have := sep_dist hG (hequ ▸ hwu) (hequ ▸ hxl_nm haB huB hau)
          have := sep_dist hG (hequ ▸ hwu) (hequ ▸ hxl_nm hbB huB hbu)
          have := hdl_out haB u (disjoint_left.mp (hAm_dB haB) huB)
          have := hdl_out hbB u (disjoint_left.mp (hAm_dB hbB) huB)
          have := dist_eq_one_iff_adj.mpr had.symm
          have := Nat.succ_le_of_lt ((hG u b).pos_dist_of_ne (Ne.symm hbu))
          have := hwall (xl b) (hxl_ne hbB haB hba); have := hasmin b hbB; omega
        · have := hdl_out haB w hwa; have := hdl_out huB w hwu
          have := hwall (xl u) hxne; have := (hG u a).dist_triangle_right w
          have := dist_eq_one_iff_adj.mpr had.symm; have := hasmin u huB; omega
    have hLunif : ∀ v ∈ B, L v = L0 := fun v hvB => by
      obtain ⟨q⟩ := hGB ⟨as, hasB⟩ ⟨v, hvB⟩
      have hw : ∀ {x y : B}, GB.Walk x y → L x.1 = L0 → L y.1 = L0 := fun p => by
        induction p with | nil => exact fun h => h | @cons x m _ h _ ih => exact fun hx => ih (hLadj x.2 m.2 hx h)
      exact hw q rfl
    have hL0 : 1 ≤ L0 := by
      obtain ⟨x0, hx0⟩ := hPne; rw [hPeq, mem_biUnion] at hx0; obtain ⟨v0, hv0B, hx0A⟩ := hx0
      have hpos : 0 < L v0 := card_pos.mpr ⟨x0, hx0A⟩; rwa [hLunif v0 hv0B] at hpos
    let rB := GB.radius.toNat; have : Nonempty B := hGB.nonempty
    obtain ⟨cB, hcBr⟩ := center_ex hGB
    have hrb : ∀ y, G.dist cB.1 y ≤ rB + L0 := fun y => by
      by_cases hyB : y ∈ B
      · have h1 : GB.dist cB ⟨y, hyB⟩ ≤ rB := hcBr ⟨y, hyB⟩
        have h2 : GB.dist cB ⟨y, hyB⟩ = G.dist cB.1 y := hGBd cB ⟨y, hyB⟩; omega
      · have hyP : y ∈ Ps := by_contra fun h => hyB (mem_sdiff.mpr ⟨mem_univ _, h⟩)
        rw [hPeq, mem_biUnion] at hyP; obtain ⟨v, hvB, hyA⟩ := hyP
        have h1 : GB.dist cB ⟨v, hvB⟩ ≤ rB := hcBr ⟨v, hvB⟩
        have h2 : GB.dist cB ⟨v, hvB⟩ = G.dist cB.1 v := hGBd cB ⟨v, hvB⟩
        have := (hxl_spec hvB (card_pos.mpr ⟨y, hyA⟩)).2.2.1 y hyA
        have := (hG v y).dist_triangle_right cB.1; have := hLunif v hvB; omega
    have hrl : r ≤ rB + L0 := rad_le hG ⟨cB.1, hrb⟩
    have hrB1 : 1 ≤ rB := by
      by_contra h0; have : B ⊆ {cB.1} := fun b hbB => by
        have h1 : GB.dist cB ⟨b, hbB⟩ ≤ rB := hcBr ⟨b, hbB⟩
        have h2 : GB.dist cB ⟨b, hbB⟩ = G.dist cB.1 b := hGBd cB ⟨b, hbB⟩
        exact mem_singleton.mpr ((hG cB.1 b).dist_eq_zero_iff.mp (by omega)).symm
      have := card_le_card this; rw [card_singleton] at this; omega
    obtain ⟨TB, hTBt, hTBc⟩ := max_tree GB
    let T0 : Finset α := TB.image Subtype.val
    have hT0s : T0 ⊆ B := fun _ hx => by obtain ⟨⟨y, hy⟩, -, rfl⟩ := mem_image.mp hx; exact hy
    have hT0c : T0.card = TB.card := card_image_of_injective TB Subtype.val_injective
    have hTf := tree_biUnion hG (tree_img hTBt) Am
      (fun v hv => hAm_p (hT0s hv) (by rw [hLunif v (hT0s hv)]; exact hL0))
      (fun v hv => disjoint_of_subset_left hT0s (hAm_dB (hT0s hv)))
      (fun v hv w hw hvw => hAm_dp (hT0s hv) (hT0s hw) hvw)
    have hsum : (∑ v ∈ T0, (Am v).card) = T0.card * L0 := by
      rw [sum_congr rfl fun v hv => hLunif v (hT0s hv), sum_const, smul_eq_mul]
    have hTc : (T0 ∪ T0.biUnion Am).card = T0.card * (L0 + 1) := by
      rw [hTf.2, hsum, mul_add, mul_one, add_comm]
    have htl := card_le_largestInducedTreeSize hTf.1
    have hT0r : rB + 1 ≤ T0.card := by
      have : rB + 1 ≤ largestInducedTreeSize GB := rad_le_lit hGB; omega
    have hmul : 2 * (rB + L0) ≤ T0.card * (L0 + 1) := by
      have h1 := Nat.mul_le_mul_right (L0 + 1) hT0r
      rcases (by omega : rB = 1 ∨ 2 ≤ rB) with hr1' | hr2'
      · rw [hr1'] at h1 ⊢; simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at h1 ⊢; omega
      · rcases (by omega : L0 = 1 ∨ 2 ≤ L0) with hL1' | hL2'
        · rw [hL1'] at h1 ⊢; simp only [Nat.mul_add, Nat.mul_one] at h1 ⊢; omega
        · have ha := Nat.mul_le_mul_right L0 hr2'
          have hb := Nat.mul_le_mul_left rB hL2'
          have hmul_ex : (rB + 1) * (L0 + 1) = rB * L0 + rB + L0 + 1 := by
            simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]; omega
          omega
    have htl' : T0.card * (L0 + 1) ≤ largestInducedTreeSize G := hTc ▸ htl
    omega

end SecE

end OMA_Conj84

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture84.conjecture84 := by
  intro α _ _ _ G _ h hδ
  by_cases h2 : 2 ≤ G.minDegree
  · have h1 := OMA_Conj84.rad_le_lit h
    have hp : (0 : ℝ) < G.minDegree := by exact_mod_cast hδ
    rw [div_le_iff₀ hp]
    have : (G.radius.toNat : ℝ) + 1 ≤ SimpleGraph.largestInducedTreeSize G := by exact_mod_cast h1
    have : (2 : ℝ) ≤ G.minDegree := by exact_mod_cast h2
    have : (0 : ℝ) ≤ SimpleGraph.largestInducedTreeSize G := by positivity
    nlinarith
  · have hδ1 : G.minDegree = 1 := by omega
    have hm : 2 * G.radius.toNat ≤ SimpleGraph.largestInducedTreeSize G := by
      by_cases hc : Fintype.card α ≤ 2
      · obtain ⟨x, y, _⟩ := G.exists_dist_eq_diam
        obtain ⟨p, hp, hl⟩ := h.exists_path_of_dist x y
        have := OMA_Conj84.rad_le_diam h; have := hp.length_lt; have := OMA_Conj84.rad_le_lit h; omega
      · obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
        obtain ⟨c, hvc, hu⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp (by rw [← hv, hδ1])
        exact OMA_Conj84.cut_main (Fintype.card α) rfl G h
          ⟨c, OMA_Conj84.cut_uniq (by omega) hvc hu⟩
    rw [hδ1]; simp only [Nat.cast_one, div_one]; exact_mod_cast hm
