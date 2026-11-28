import OMAReductions.R_Erdos719_erdos_719_R1

/-!
An edge and triangle partition with the Erdős–Goodman–Pósa bound.
At a minimum-degree vertex, pair up as many neighbors as possible along edges.
-/

open Finset

private def budget (n : ℕ) : ℕ := (n / 2) * ((n + 1) / 2)

private theorem budget_succ (n : ℕ) : budget n + (n + 1) / 2 = budget (n + 1) := by
  unfold budget
  by_cases h : n % 2 = 0
  · rw [show (n + 1) / 2 = n / 2 by omega,
        show (n + 1 + 1) / 2 = n / 2 + 1 by omega]
    ring
  · rw [show (n + 1) / 2 = n / 2 + 1 by omega,
        show (n + 1 + 1) / 2 = n / 2 + 1 by omega]
    ring

private theorem card_pair (x y : α) [DecidableEq α] (h : x ≠ y) :
    ({x, y} : Finset α).card = 2 :=
  card_eq_two.mpr ⟨x, y, h, rfl⟩

private theorem other_endpoint {V : Type*} [DecidableEq V] {e : Finset V} {v : V}
    (he : e.card = 2) (hv : v ∈ e) : ∃ x ∈ e, v ≠ x := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp he
  rcases (mem_insert.mp hv) with rfl | hv
  · exact ⟨b, mem_insert_of_mem (mem_singleton_self _), hab⟩
  · have hvb : v = b := mem_singleton.mp hv
    subst v
    exact ⟨a, mem_insert_self _ _, hab.symm⟩

private theorem localPartition {V : Type*} [DecidableEq V] (n : ℕ) :
    ∀ (A : Finset V) (H : Finset (Finset V)), A.card = n →
      H.IsUniform 2 → (∀ e ∈ H, e ⊆ A) →
      ∃ D : Finset (Finset V), H.IsCompleteHypergraphDecomposition 2 D ∧ D.card ≤ budget n := by
  classical
  induction n with
  | zero =>
    intro A H hA hc hsub
    have hH : H = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      have hs := card_le_card (hsub e he)
      have ht := hc e he
      omega
    subst H
    exact ⟨∅, by simp [Finset.IsCompleteHypergraphDecomposition, Set.Pairwise], by simp⟩
  | succ n ih =>
    intro A H hA hc hsub
    have hAne : A.Nonempty := card_pos.mp (by omega : 0 < A.card)
    let neigh (x : V) := A.filter (fun y => ({x, y} : Finset V) ∈ H)
    have neighA (x : V) : neigh x ⊆ A := filter_subset ..
    have noLoop (x : V) : x ∉ neigh x := by
      intro hx
      have hsing := hc _ (mem_filter.mp hx).2
      simp at hsing
    obtain ⟨v, hv, hmin⟩ := exists_min_image A (fun x => (neigh x).card) hAne
    let N := neigh v
    let available := H.filter (· ⊆ N)
    let matchings : Finset (Finset (Finset V)) := available.powerset.filter
      (fun M => (M : Set (Finset V)).Pairwise Disjoint)
    have hne : matchings.Nonempty := ⟨∅, by simp [matchings, Set.Pairwise]⟩
    obtain ⟨M, hm, hmmax⟩ := exists_max_image matchings (fun M : Finset (Finset V) => M.card) hne
    obtain ⟨hmavail, hmDisj⟩ := mem_filter.mp (show M ∈ matchings from hm)
    have hmSub (e) (he : e ∈ M) : e ∈ H ∧ e ⊆ N :=
      mem_filter.mp (mem_powerset.mp hmavail he)
    let U := M.biUnion id
    have hUN : U ⊆ N := by
      intro x hx
      obtain ⟨e, he, hxe⟩ := mem_biUnion.mp hx
      exact (hmSub e he).2 hxe
    have hUcard : U.card = 2 * M.card := by
      change (M.biUnion (fun e => e)).card = _
      rw [card_biUnion hmDisj]
      have hvals : (∑ e ∈ M, e.card) = ∑ _e ∈ M, 2 :=
        sum_congr rfl fun e he => hc e (hmSub e he).1
      rw [hvals]
      simp [mul_comm]
    have maximal (e : Finset V) (he : e ∈ available) (hdis : Disjoint e U)
        (hene : e.Nonempty) : False := by
      have henM : e ∉ M := by
        intro h
        obtain ⟨x, hx⟩ := hene
        exact disjoint_left.mp hdis hx (mem_biUnion.mpr ⟨e, h, hx⟩)
      have hnew : insert e M ∈ matchings := by
        apply mem_filter.mpr
        refine ⟨mem_powerset.mpr (insert_subset he (mem_powerset.mp hmavail)), ?_⟩
        intro a ha b hb hab
        change a ∈ insert e M at ha
        change b ∈ insert e M at hb
        rcases mem_insert.mp ha with rfl | haM
        · rcases mem_insert.mp hb with rfl | hbM
          · exact (hab rfl).elim
          · exact disjoint_left.mpr fun x hxe hxb =>
              disjoint_left.mp hdis hxe (mem_biUnion.mpr ⟨b, hbM, hxb⟩)
        · rcases mem_insert.mp hb with rfl | hbM
          · apply Disjoint.symm
            exact disjoint_left.mpr fun x hxe hxa =>
              disjoint_left.mp hdis hxe (mem_biUnion.mpr ⟨a, haM, hxa⟩)
          · exact hmDisj haM hbM hab
      have hle := hmmax (insert e M) hnew
      rw [card_insert_of_notMem henM] at hle
      omega
    have hNM : N.card ≤ M.card + (n + 1) / 2 := by
      have hNle : N.card ≤ A.card := card_le_card (neighA v)
      by_cases hall : N ⊆ U
      · have hNU := card_le_card hall
        omega
      · obtain ⟨x, hxN, hxU⟩ := not_subset.mp hall
        have hint : N ∩ neigh x ⊆ U := by
          intro y hy
          obtain ⟨hyN, hyx⟩ := mem_inter.mp hy
          by_contra hyU
          have he : ({x, y} : Finset V) ∈ available :=
            mem_filter.mpr ⟨(mem_filter.mp hyx).2, insert_subset hxN (singleton_subset_iff.mpr hyN)⟩
          exact maximal _ he (by simp [hxU, hyU]) (by simp)
        have hI := card_le_card hint
        have hAll := card_le_card
          (union_subset (neighA v) (neighA x) : N ∪ neigh x ⊆ A)
        have heq := card_union_add_card_inter N (neigh x)
        have hminx := hmin x (neighA v hxN)
        change N.card ≤ (neigh x).card at hminx
        omega
    let P := M ∪ (N \ U).image (fun x => ({x} : Finset V))
    have parts (p : Finset V) (hp : p ∈ P) :
        p ⊆ N ∧ (p.card = 1 ∨ p.card = 2 ∧ p ∈ H) := by
      rcases mem_union.mp hp with hm | hs
      · exact ⟨(hmSub p hm).2, Or.inr ⟨hc p (hmSub p hm).1, (hmSub p hm).1⟩⟩
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
        exact ⟨singleton_subset_iff.mpr (mem_sdiff.mp hx).1, Or.inl (card_singleton _)⟩
    have piecesCover : N ⊆ P.biUnion id := by
      intro x hx
      by_cases hu : x ∈ U
      · obtain ⟨m, hm, hxm⟩ := mem_biUnion.mp hu
        exact mem_biUnion.mpr ⟨m, mem_union.mpr (Or.inl hm), hxm⟩
      · exact mem_biUnion.mpr ⟨{x}, mem_union.mpr (Or.inr
          (mem_image.mpr ⟨x, mem_sdiff.mpr ⟨hx, hu⟩, rfl⟩)), mem_singleton_self x⟩
    have piecesDisj : (P : Set (Finset V)).Pairwise Disjoint := by
      intro a ha b hb hab
      rcases mem_union.mp ha with ha | ha
      · rcases mem_union.mp hb with hb | hb
        · exact hmDisj ha hb hab
        · obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
          exact disjoint_left.mpr fun z hz hz' => by
            have hzEq : z = x := mem_singleton.mp hz'
            subst z
            exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨a, ha, hz⟩)
      · obtain ⟨x, hx, rfl⟩ := mem_image.mp ha
        rcases mem_union.mp hb with hb | hb
        · exact disjoint_left.mpr fun z hz hz' => by
            have hzEq : z = x := mem_singleton.mp hz
            subst z
            exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨b, hb, hz'⟩)
        · obtain ⟨y, _, rfl⟩ := mem_image.mp hb
          exact disjoint_left.mpr fun z hz hz' =>
            hab (by rw [← mem_singleton.mp hz, ← mem_singleton.mp hz'])
    let S := P.image (insert v)
    let Y := S.biUnion (fun p => p.powersetCard 2)
    have star (p : Finset V) (hp : p ∈ P) : (insert v p).card = 2 ∨ (insert v p).card = 3 := by
      rw [card_insert_of_notMem (fun hvp => noLoop v ((parts p hp).1 hvp))]
      rcases (parts p hp).2 with h | ⟨h, _⟩ <;> omega
    have hY : Y ⊆ H := by
      intro e he
      obtain ⟨s, hs, he⟩ := mem_biUnion.mp he
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
      obtain ⟨hsube, hcard⟩ := mem_powersetCard.mp he
      by_cases hvE : v ∈ e
      · obtain ⟨x, hx, hxv⟩ := other_endpoint hcard hvE
        have hxp : x ∈ p := (mem_insert.mp (hsube hx)).resolve_left (Ne.symm hxv)
        have hEq : ({v, x} : Finset V) = e :=
          eq_of_subset_of_card_le (insert_subset hvE (singleton_subset_iff.mpr hx))
            (by rw [card_pair v x hxv, hcard])
        simpa only [hEq] using (mem_filter.mp ((parts p hp).1 hxp)).2
      · have heP : e ⊆ p := fun x hx => (mem_insert.mp (hsube hx)).resolve_left
          (fun h => hvE (h ▸ hx))
        rcases (parts p hp).2 with h | ⟨h, hH⟩
        · have := card_le_card heP
          omega
        · rwa [eq_of_subset_of_card_le heP (h.trans hcard.symm).le]
    have containsV (e : Finset V) (he : e ∈ H) (hvE : v ∈ e) : e ∈ Y := by
      have heCard := hc e he
      obtain ⟨x, hx, hxv⟩ := other_endpoint heCard hvE
      have heq : ({v, x} : Finset V) = e :=
        eq_of_subset_of_card_le (insert_subset hvE (singleton_subset_iff.mpr hx))
          (by rw [card_pair v x hxv, heCard])
      have hxN : x ∈ N := mem_filter.mpr ⟨hsub e he hx, heq ▸ he⟩
      obtain ⟨p, hp, hxp⟩ := mem_biUnion.mp (piecesCover hxN)
      exact mem_biUnion.mpr ⟨insert v p, mem_image_of_mem _ hp, mem_powersetCard.mpr
        ⟨heq ▸ insert_subset (mem_insert_self v p) (singleton_subset_iff.mpr (mem_insert_of_mem hxp)), heCard⟩⟩
    have starsDisj : (S : Set (Finset V)).Pairwise
        (fun a b => Disjoint (a.powersetCard 2) (b.powersetCard 2)) := by
      intro a ha b hb hab
      obtain ⟨p, hp, rfl⟩ := mem_image.mp ha
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hb
      have hpq : p ≠ q := fun he => hab (congrArg (insert v) he)
      apply disjoint_left.mpr
      intro e he₁ he₂
      obtain ⟨hs₁, hc₁⟩ := mem_powersetCard.mp he₁
      have hs₂ := (mem_powersetCard.mp he₂).1
      have heSingle : e ⊆ {v} := by
        intro x hx
        by_contra h
        have hxv : x ≠ v := by simpa using h
        exact disjoint_left.mp (piecesDisj hp hq hpq)
          ((mem_insert.mp (hs₁ hx)).resolve_left hxv)
          ((mem_insert.mp (hs₂ hx)).resolve_left hxv)
      have := card_le_card heSingle
      simp [hc₁] at this
    have hScard : S.card ≤ (n + 1) / 2 := by
      have hSP : S.card ≤ P.card := card_image_le
      have hP : P.card ≤ M.card + ((N \ U).image (fun x => ({x} : Finset V))).card :=
        card_union_le _ _
      have hsingle : ((N \ U).image (fun x => ({x} : Finset V))).card ≤ (N \ U).card := card_image_le
      have hU := card_sdiff_of_subset hUN
      have hUNle := card_le_card hUN
      omega
    let H' := H \ Y
    let A' := A.erase v
    have hA' : A'.card = n := by simp [A', card_erase_of_mem hv, hA]
    have hH' e (he : e ∈ H') : e ⊆ A' := by
      obtain ⟨he, hne⟩ := mem_sdiff.mp he
      intro x hx
      apply mem_erase.mpr
      refine ⟨fun h => hne (containsV e he (h ▸ hx)), hsub e he hx⟩
    obtain ⟨D, hD, hDcard⟩ := ih A' H' hA' (fun e he => hc e (mem_sdiff.mp he).1) hH'
    refine ⟨S ∪ D, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro s hs
      rcases mem_union.mp hs with hs | hs
      · obtain ⟨p, hp, rfl⟩ := mem_image.mp hs
        exact star p hp
      · exact hD.1 s hs
    · rw [union_biUnion]
      change H = Y ∪ D.biUnion (fun s => s.powersetCard 2)
      rw [← hD.2.1]
      ext e
      simp only [mem_union, H', mem_sdiff]
      exact ⟨fun he => or_iff_not_imp_left.mpr (fun hn => ⟨he, hn⟩),
        fun he => he.elim (fun he => hY he) And.left⟩
    · intro s hs t ht hst
      rcases mem_union.mp hs with hs | hs <;> rcases mem_union.mp ht with ht | ht
      · exact starsDisj hs ht hst
      · exact disjoint_left.mpr fun e hes het => by
          have hE : e ∈ H' := hD.2.1 ▸ mem_biUnion.mpr ⟨t, ht, het⟩
          exact (mem_sdiff.mp hE).2 (mem_biUnion.mpr ⟨s, hs, hes⟩)
      · exact (disjoint_left.mpr fun e het hes => by
          have hE : e ∈ H' := hD.2.1 ▸ mem_biUnion.mpr ⟨s, hs, hes⟩
          exact (mem_sdiff.mp hE).2 (mem_biUnion.mpr ⟨t, ht, het⟩)).symm
      · exact hD.2.2 hs ht hst
    · calc
        (S ∪ D).card ≤ S.card + D.card := card_union_le _ _
        _ ≤ budget n + (n + 1) / 2 := by omega
        _ = budget (n + 1) := budget_succ n

private theorem extremal_ge_budget (n : ℕ) :
    budget n ≤ Hypergraph.cliqueExtremalNumber n 2 3 := by
  classical
  cases n with
  | zero => simp [budget]
  | succ n =>
    let cut : Fin (n + 1) := ⟨(n + 1) / 2, by omega⟩
    let left : Finset (Fin (n + 1)) := Iio cut
    let right : Finset (Fin (n + 1)) := univ \ left
    let edge (xy : Fin (n + 1) × Fin (n + 1)) : Finset (Fin (n + 1)) := {xy.1, xy.2}
    let E := (left ×ˢ right).image edge
    have hleft : left.card = (n + 1) / 2 := Fin.card_Iio cut
    have hright : right.card = (n + 1 + 1) / 2 := by
      simp [right, card_sdiff_of_subset (subset_univ left), hleft]
      omega
    have endpoint (p : Fin (n + 1) × Fin (n + 1)) (hp : p ∈ left ×ˢ right) :
        p.1 ∈ left ∧ p.2 ∉ left := by
      obtain ⟨h1, h2⟩ := mem_product.mp hp
      exact ⟨h1, (mem_sdiff.mp h2).2⟩
    have ec (e) (he : e ∈ E) : e.card = 2 := by
      obtain ⟨p, hp, rfl⟩ := mem_image.mp he
      have h := endpoint p hp
      exact card_pair _ _ (fun he => h.2 (he ▸ h.1))
    have ecard : E.card = budget (n + 1) := by
      rw [card_image_of_injOn]
      · rw [card_product, hleft, hright]
        rfl
      · intro p hp q hq he
        have hp' := endpoint p hp
        have hq' := endpoint q hq
        change ({p.1, p.2} : Finset (Fin (n + 1))) = {q.1, q.2} at he
        have h1 : p.1 = q.1 := by
          have ht : p.1 ∈ ({q.1, q.2} : Finset (Fin (n + 1))) := he ▸ mem_insert_self _ _
          exact (mem_insert.mp ht).resolve_right
            (fun heq => hq'.2 (mem_singleton.mp heq ▸ hp'.1))
        have h2 : p.2 = q.2 := by
          have ht : p.2 ∈ ({q.1, q.2} : Finset (Fin (n + 1))) := he ▸ mem_insert_of_mem (mem_singleton_self _)
          exact mem_singleton.mp ((mem_insert.mp ht).resolve_left (fun heq => hp'.2 (heq.symm ▸ hq'.1)))
        exact Prod.ext h1 h2
    have opposite (x y : Fin (n + 1)) (hne : x ≠ y) (he : ({x, y} : Finset _) ∈ E) :
        x ∈ left ↔ y ∉ left := by
      obtain ⟨p, hp, h⟩ := mem_image.mp he
      obtain ⟨h1, h2⟩ := endpoint p hp
      change ({p.1, p.2} : Finset (Fin (n + 1))) = {x, y} at h
      have hx : x = p.1 ∨ x = p.2 := by
        have mem : x ∈ ({p.1, p.2} : Finset (Fin (n + 1))) := h.symm ▸ mem_insert_self _ _
        simpa using mem
      have hy : y = p.1 ∨ y = p.2 := by
        have mem : y ∈ ({p.1, p.2} : Finset (Fin (n + 1))) :=
          h.symm ▸ mem_insert_of_mem (mem_singleton_self _)
        simpa using mem
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp_all
    have noTriangle : ¬ E.ContainsCompleteHypergraph 2 3 := by
      rintro ⟨s, hcard, h⟩
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hcard
      have xy := opposite x y hxy (h (mem_powersetCard.mpr
        ⟨by simp, card_pair x y hxy⟩))
      have xz := opposite x z hxz (h (mem_powersetCard.mpr
        ⟨by simp, card_pair x z hxz⟩))
      have yz := opposite y z hyz (h (mem_powersetCard.mpr
        ⟨insert_subset (by simp) (singleton_subset_iff.mpr (by simp)), card_pair y z hyz⟩))
      tauto
    unfold Hypergraph.cliqueExtremalNumber Hypergraph.extremalNumber
    rw [← ecard]
    apply le_sup (f := Finset.card)
    simp only [mem_filter]
    exact ⟨mem_powerset.mpr (fun e he =>
      mem_powersetCard.mpr ⟨subset_univ e, ec e he⟩), noTriangle⟩

theorem OMA.solution : OMA.R_Erdos719_erdos_719_R1.H1 := by
  intro n H hH
  classical
  obtain ⟨D, hD, hcard⟩ :=
    localPartition n (univ : Finset (Fin n)) H (by simp) hH (fun e _ => subset_univ e)
  exact ⟨D, hD, hcard.trans (extremal_ge_budget n)⟩

