import OMAReductions.R_opg_forcing_a_2_regular_minor_R1

/-!
Proof of `opg-forcing-a-2-regular-minor.R1.H2`: every connected 2-regular graph `H` on `Fin t`
is a minor of every graph `G` containing a cycle `c` of length at least `t`, obtained by
enumerating `H` along its unique cycle and contracting the tail arc of `c` into the last branch set.
-/

-- Problem: opg-forcing-a-2-regular-minor.R1.H2
-- Upstream: reductions/opg-forcing-a-2-regular-minor.R1.lean
-- Credit: @ppleskov

namespace OMA.P_opg_forcing_2reg_R1_H2

open SimpleGraph Finset OMA.S_opg_forcing_a_2_regular_minor

private lemma exists_other_nbr {t : ℕ} (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (hreg : H.IsRegularOfDegree 2) (p x : Fin t) (hpx : H.Adj p x) :
    ∃ y : Fin t, H.Adj x y ∧ y ≠ p ∧ ∀ z : Fin t, H.Adj x z → z = p ∨ z = y := by
  have hp_mem : p ∈ H.neighborFinset x := (mem_neighborFinset H x p).mpr hpx.symm
  have hcard_er : ((H.neighborFinset x).erase p).card = 1 := by
    rw [card_erase_of_mem hp_mem, card_neighborFinset_eq_degree, hreg x]
  obtain ⟨y, hy_eq⟩ := Finset.card_eq_one.mp hcard_er
  have hy_mem : y ∈ (H.neighborFinset x).erase p := by rw [hy_eq]; exact mem_singleton_self y
  obtain ⟨hyp, hy_nbr⟩ := mem_erase.mp hy_mem
  refine ⟨y, (mem_neighborFinset H x y).mp hy_nbr, hyp, fun z hz => ?_⟩
  by_cases hzp : z = p
  · exact Or.inl hzp
  · right
    have hz_er : z ∈ (H.neighborFinset x).erase p :=
      mem_erase.mpr ⟨hzp, (mem_neighborFinset H x z).mpr hz⟩
    rw [hy_eq, mem_singleton] at hz_er
    exact hz_er

private lemma connected_two_regular_cycle_order {t : ℕ}
    (H : SimpleGraph (Fin t)) [DecidableRel H.Adj]
    (hreg : H.IsRegularOfDegree 2) (hconn : H.Connected) :
    3 ≤ t ∧ ∃ σ : Fin t ≃ Fin t,
      ∀ i j : Fin t, H.Adj (σ i) (σ j) → (i.val + 1) % t = j.val ∨ (j.val + 1) % t = i.val := by
  classical
  have ht3 : 3 ≤ t := by
    obtain ⟨v⟩ := hconn.nonempty
    have hnot : v ∉ H.neighborFinset v := by simp
    have hcard : (insert v (H.neighborFinset v)).card = 3 := by
      rw [card_insert_of_notMem hnot, card_neighborFinset_eq_degree, hreg v]
    have hle := card_le_univ (insert v (H.neighborFinset v))
    rw [hcard, Fintype.card_fin] at hle
    exact hle
  let v₀ : Fin t := ⟨0, by omega⟩
  have hv₀_deg : (H.neighborFinset v₀).Nonempty := by
    rw [← Finset.card_pos, card_neighborFinset_eq_degree, hreg v₀]; omega
  obtain ⟨v₁, hv₁_mem⟩ := hv₀_deg
  have hv₀₁ : H.Adj v₀ v₁ := (mem_neighborFinset H v₀ v₁).mp hv₁_mem
  let step : Fin t × Fin t → Fin t × Fin t := fun p =>
    if h : H.Adj p.1 p.2 then (p.2, Classical.choose (exists_other_nbr H hreg p.1 p.2 h))
    else (p.2, p.1)
  let pair : ℕ → Fin t × Fin t := fun k => Nat.rec (v₀, v₁) (fun _ p => step p) k
  let w : ℕ → Fin t := fun k => (pair k).1
  have hpair_adj : ∀ k, H.Adj (pair k).1 (pair k).2 := by
    intro k
    induction k with
    | zero => exact hv₀₁
    | succ k ih =>
      show H.Adj (step (pair k)).1 (step (pair k)).2
      simp only [step, dif_pos ih]
      exact (Classical.choose_spec (exists_other_nbr H hreg (pair k).1 (pair k).2 ih)).1
  have hpair_snd : ∀ k, (pair k).2 = w (k + 1) := by
    intro k
    have ih := hpair_adj k
    change (pair k).2 = (step (pair k)).1
    simp only [step, dif_pos ih]
  have hw_adj : ∀ k, H.Adj (w k) (w (k + 1)) := by
    intro k
    rw [← hpair_snd k]
    exact hpair_adj k
  have hw_nb : ∀ k, w (k + 2) ≠ w k ∧ ∀ z, H.Adj (w (k + 1)) z → z = w k ∨ z = w (k + 2) := by
    intro k
    have hadj := hpair_adj k
    have hspec := Classical.choose_spec (exists_other_nbr H hreg (pair k).1 (pair k).2 hadj)
    have hw2 : w (k + 2) = Classical.choose (exists_other_nbr H hreg (pair k).1 (pair k).2 hadj) := by
      rw [← hpair_snd (k + 1)]
      change (step (pair k)).2 = _
      simp only [step, dif_pos hadj]
    have hw1 : w (k + 1) = (pair k).2 := (hpair_snd k).symm
    rw [hw2, hw1]
    exact ⟨hspec.2.1, hspec.2.2⟩
  -- By pigeonhole on `Fin (t + 1) → Fin t`, `w` has a repeat.
  have hrep : ∃ b : ℕ, ∃ a < b, w a = w b := by
    by_contra! hno
    have hinj : Function.Injective (fun i : Fin (t + 1) => w i.val) := by
      intro i j hij
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · exact (hno j.val i.val hlt hij).elim
      · exact Fin.ext heq
      · exact (hno i.val j.val hgt hij.symm).elim
    have hle := Fintype.card_le_of_injective _ hinj
    simp at hle
  let L : ℕ := Nat.find hrep
  obtain ⟨a₀, ha₀_lt, ha₀_eq⟩ := Nat.find_spec hrep
  change a₀ < L at ha₀_lt
  change w a₀ = w L at ha₀_eq
  have hmin : ∀ i j, i < j → j < L → w i ≠ w j := by
    intro i j hij hjL heq
    exact Nat.find_min hrep hjL ⟨i, hij, heq⟩
  have ha₀_zero : a₀ = 0 := by
    by_contra ha_pos
    have ha1 : 1 ≤ a₀ := Nat.pos_of_ne_zero ha_pos
    have hL1 : 1 ≤ L := by omega
    have hadj_L : H.Adj (w a₀) (w (L - 1)) := by
      rw [ha₀_eq]
      have := hw_adj (L - 1)
      rw [Nat.sub_add_cancel hL1] at this
      exact this.symm
    have hcases := (hw_nb (a₀ - 1)).2 (w (L - 1)) (by rwa [Nat.sub_add_cancel ha1])
    rcases hcases with h1 | h2
    · exact hmin (a₀ - 1) (L - 1) (by omega) (by omega) h1.symm
    · rw [show a₀ - 1 + 2 = a₀ + 1 by omega] at h2
      by_cases hcmp : a₀ + 1 = L - 1
      · have hL2 : L = a₀ + 2 := by omega
        rw [hL2] at ha₀_eq
        exact (hw_nb a₀).1 ha₀_eq.symm
      · rcases lt_or_gt_of_ne hcmp with hlt | hgt
        · exact hmin (a₀ + 1) (L - 1) hlt (by omega) h2.symm
        · have hL1' : L = a₀ + 1 := by omega
          rw [hL1'] at ha₀_eq
          exact (hw_adj a₀).ne ha₀_eq
  subst ha₀_zero
  have hL3 : 3 ≤ L := by
    by_contra! hlt
    have hL0 : L ≠ 0 := by omega
    have hL1 : L ≠ 1 := by
      intro h1; rw [h1] at ha₀_eq; exact (hw_adj 0).ne ha₀_eq
    have hL2 : L ≠ 2 := by
      intro h2; rw [h2] at ha₀_eq; exact (hw_nb 0).1 ha₀_eq.symm
    omega
  -- The image `S = {w k | k < L}` is closed under `H.Adj`.
  have hclosed : ∀ k < L, ∀ z : Fin t, H.Adj (w k) z →
      z = w ((k + 1) % L) ∨ z = w ((k + L - 1) % L) := by
    intro k hk z hz
    by_cases hk0 : k = 0
    · subst hk0
      have hnbr1 : H.Adj (w 0) (w 1) := hw_adj 0
      have hnbr2 : H.Adj (w 0) (w (L - 1)) := by
        rw [ha₀_eq]
        have := hw_adj (L - 1)
        rw [Nat.sub_add_cancel (by omega : 1 ≤ L)] at this
        exact this.symm
      have hne12 : w 1 ≠ w (L - 1) := hmin 1 (L - 1) (by omega) (by omega)
      have hsub : ({w 1, w (L - 1)} : Finset (Fin t)) ⊆ H.neighborFinset (w 0) := by
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (mem_neighborFinset H _ _).mpr hnbr1
        · exact (mem_neighborFinset H _ _).mpr hnbr2
      have hcard_eq : ({w 1, w (L - 1)} : Finset (Fin t)).card = (H.neighborFinset (w 0)).card := by
        rw [card_pair hne12, card_neighborFinset_eq_degree, hreg (w 0)]
      have heq_set : ({w 1, w (L - 1)} : Finset (Fin t)) = H.neighborFinset (w 0) :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm)
      have hz_mem : z ∈ ({w 1, w (L - 1)} : Finset (Fin t)) := by
        rw [heq_set]; exact (mem_neighborFinset H _ _).mpr hz
      simp only [mem_insert, mem_singleton] at hz_mem
      rw [Nat.mod_eq_of_lt (by omega : 0 + 1 < L), Nat.mod_eq_of_lt (by omega : 0 + L - 1 < L)]
      simpa using hz_mem
    · have hcases := (hw_nb (k - 1)).2 z (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ k)])
      rcases hcases with hprev | hnext
      · right
        rw [show (k + L - 1) % L = k - 1 by
          have : k + L - 1 = (k - 1) + L := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
        exact hprev
      · left
        rw [show k - 1 + 2 = k + 1 by omega] at hnext
        by_cases hlast : k + 1 = L
        · rw [hlast, Nat.mod_self, hnext, hlast]
          exact ha₀_eq.symm
        · rw [Nat.mod_eq_of_lt (by omega : k + 1 < L)]
          exact hnext
  have hsurj : ∀ x : Fin t, ∃ k < L, w k = x := by
    have hstep : ∀ {a b : Fin t}, H.Adj a b → (∃ k < L, w k = a) → ∃ k < L, w k = b := by
      rintro a b hab ⟨k, hk, rfl⟩
      rcases hclosed k hk b hab with h1 | h2
      · exact ⟨(k + 1) % L, Nat.mod_lt _ (by omega), h1.symm⟩
      · exact ⟨(k + L - 1) % L, Nat.mod_lt _ (by omega), h2.symm⟩
    have hwalk : ∀ {a b : Fin t}, H.Walk a b → (∃ k < L, w k = a) → ∃ k < L, w k = b := by
      intro a b p
      induction p with
      | nil => exact id
      | @cons a b c hab _ ih => intro ha; exact ih (hstep hab ha)
    intro x
    obtain ⟨p⟩ := hconn (w 0) x
    exact hwalk p ⟨0, by omega, rfl⟩
  have hL_eq_t : L = t := by
    have hinjL : Function.Injective (fun i : Fin L => w i.val) := by
      intro i j hij
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · exact (hmin i.val j.val hlt j.isLt hij).elim
      · exact Fin.ext heq
      · exact (hmin j.val i.val hgt i.isLt hij.symm).elim
    have hle1 : L ≤ t := by
      simpa using Fintype.card_le_of_injective _ hinjL
    have hsurjL : Function.Surjective (fun i : Fin L => w i.val) := by
      intro x
      obtain ⟨k, hk, rfl⟩ := hsurj x
      exact ⟨⟨k, hk⟩, rfl⟩
    have hle2 : t ≤ L := by
      simpa using Fintype.card_le_of_surjective _ hsurjL
    omega
  have hbij : Function.Bijective (fun i : Fin t => w i.val) := by
    constructor
    · intro i j hij
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · exact (hmin i.val j.val hlt (hL_eq_t.symm ▸ j.isLt) hij).elim
      · exact Fin.ext heq
      · exact (hmin j.val i.val hgt (hL_eq_t.symm ▸ i.isLt) hij.symm).elim
    · intro x
      obtain ⟨k, hk, rfl⟩ := hsurj x
      exact ⟨⟨k, hL_eq_t ▸ hk⟩, rfl⟩
  let σ : Fin t ≃ Fin t := Equiv.ofBijective (fun i : Fin t => w i.val) hbij
  refine ⟨ht3, σ, fun i j hij => ?_⟩
  rcases hclosed i.val (hL_eq_t.symm ▸ i.isLt) (σ j) hij with h1 | h2
  · left
    have heq : σ j = σ ⟨(i.val + 1) % t, Nat.mod_lt _ (by omega)⟩ := by
      simpa [σ, hL_eq_t] using h1
    have hfin := σ.injective heq
    exact (congrArg Fin.val hfin).symm
  · right
    have heq : σ j = σ ⟨(i.val + t - 1) % t, Nat.mod_lt _ (by omega)⟩ := by
      simpa [σ, hL_eq_t] using h2
    have hfin : j.val = (i.val + t - 1) % t := congrArg Fin.val (σ.injective heq)
    rw [hfin]
    have hi : i.val < t := i.isLt
    by_cases hi0 : i.val = 0
    · rw [hi0, show (0 + t - 1) % t = t - 1 by
        rw [zero_add, Nat.mod_eq_of_lt (by omega)]]
      rw [show t - 1 + 1 = t by omega, Nat.mod_self]
    · rw [show (i.val + t - 1) % t = i.val - 1 by
        have : i.val + t - 1 = (i.val - 1) + t := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
      rw [show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]

private lemma cycle_getVert_inj {V : Type*} {G : SimpleGraph V} {u : V}
    {c : G.Walk u u} (hcyc : c.IsCycle) :
    ∀ i j : ℕ, i < c.length → j < c.length → c.getVert i = c.getVert j → i = j := by
  intro i j hi hj heq
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this j i hj hi heq.symm (Ne.symm hne) (by omega)
  have hnodup : c.support.tail.Nodup := hcyc.support_nodup
  have hlen_supp : c.support.length = c.length + 1 := c.length_support
  have hlen_tail : c.support.tail.length = c.length := by
    rw [List.length_tail, hlen_supp]; omega
  have hget_tail : ∀ k : ℕ, (hk : 1 ≤ k) → (hk' : k ≤ c.length) →
      c.support.tail[k - 1]'(by omega) = c.getVert k := by
    intro k hk hk'
    rw [List.getElem_tail]
    have h2 := (c.getVert_eq_support_getElem (n := k) hk').symm
    convert h2 using 2
    omega
  by_cases hi0 : i = 0
  · subst hi0
    have h0L : c.getVert 0 = c.getVert c.length := by
      rw [SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length]
    rw [h0L] at heq
    have h1 : c.support.tail[c.length - 1]'(by omega) = c.support.tail[j - 1]'(by omega) := by
      rw [hget_tail c.length (by omega) le_rfl, hget_tail j (by omega) hj.le, heq]
    have hidx := (List.Nodup.getElem_inj_iff hnodup).mp h1
    omega
  · have h1 : c.support.tail[i - 1]'(by omega) = c.support.tail[j - 1]'(by omega) := by
      rw [hget_tail i (by omega) hi.le, hget_tail j (by omega) hj.le, heq]
    have hidx := (List.Nodup.getElem_inj_iff hnodup).mp h1
    omega

end OMA.P_opg_forcing_2reg_R1_H2

open SimpleGraph OMA.S_opg_forcing_a_2_regular_minor

theorem OMA.solution : OMA.R_opg_forcing_a_2_regular_minor_R1.H2 := by
  intro t H _ hreg hconn V G u c hcyc hlen
  obtain ⟨ht3, σ, hσ⟩ := OMA.P_opg_forcing_2reg_R1_H2.connected_two_regular_cycle_order H hreg hconn
  let L : ℕ := c.length
  have hL_ge : t ≤ L := hlen
  let B' : Fin t → Set V := fun k =>
    if k.val < t - 1 then {c.getVert k.val}
    else {x : V | ∃ j : ℕ, t - 1 ≤ j ∧ j < L ∧ x = c.getVert j}
  let B : Fin t → Set V := fun v => B' (σ.symm v)
  have hB'_mem_lt : ∀ (k : Fin t), k.val < t - 1 → ∀ x, x ∈ B' k ↔ x = c.getVert k.val := by
    intro k hk x
    simp [B', hk]
  have hB'_mem_last : ∀ (k : Fin t), ¬ k.val < t - 1 →
      ∀ x, x ∈ B' k ↔ ∃ j : ℕ, t - 1 ≤ j ∧ j < L ∧ x = c.getVert j := by
    intro k hk x
    simp [B', hk]
  have hB'_vert : ∀ (k : Fin t) (x : V), x ∈ B' k →
      ∃ j : ℕ, j < L ∧ x = c.getVert j ∧ (if k.val < t - 1 then j = k.val else t - 1 ≤ j) := by
    intro k x hx
    by_cases hk : k.val < t - 1
    · rw [hB'_mem_lt k hk] at hx
      exact ⟨k.val, by omega, hx, by simp [hk]⟩
    · rw [hB'_mem_last k hk] at hx
      obtain ⟨j, hj1, hj2, rfl⟩ := hx
      exact ⟨j, hj2, rfl, by simp [hk, hj1]⟩
  refine ⟨B, ?_, ?_, ?_⟩
  · intro v
    let k := σ.symm v
    change (G.induce (B' k)).Connected
    by_cases hk : k.val < t - 1
    · have hne : Nonempty (B' k) := ⟨⟨c.getVert k.val, (hB'_mem_lt k hk _).mpr rfl⟩⟩
      refine SimpleGraph.Connected.mk fun a b => ?_
      have ha : a.val = c.getVert k.val := (hB'_mem_lt k hk _).mp a.property
      have hb : b.val = c.getVert k.val := (hB'_mem_lt k hk _).mp b.property
      have hab : a = b := Subtype.ext (ha.trans hb.symm)
      subst hab
      exact SimpleGraph.Reachable.refl a
    · have hroot_mem : c.getVert (t - 1) ∈ B' k :=
        (hB'_mem_last k hk _).mpr ⟨t - 1, le_rfl, by omega, rfl⟩
      let root : B' k := ⟨c.getVert (t - 1), hroot_mem⟩
      have hreach_root : ∀ (d : ℕ) (hd : t - 1 + d < L),
          (G.induce (B' k)).Reachable root
            ⟨c.getVert (t - 1 + d), (hB'_mem_last k hk _).mpr ⟨t - 1 + d, by omega, hd, rfl⟩⟩ := by
        intro d
        induction d with
        | zero =>
          intro _
          simp [root]
        | succ d ih =>
          intro hd
          have hprev := ih (by omega)
          have hadj : G.Adj (c.getVert (t - 1 + d)) (c.getVert (t - 1 + d + 1)) :=
            c.adj_getVert_succ (by omega)
          have hstep : (G.induce (B' k)).Adj
              ⟨c.getVert (t - 1 + d), (hB'_mem_last k hk _).mpr ⟨t - 1 + d, by omega, by omega, rfl⟩⟩
              ⟨c.getVert (t - 1 + (d + 1)), (hB'_mem_last k hk _).mpr ⟨t - 1 + (d + 1), by omega, hd, rfl⟩⟩ := by
            simpa [Nat.add_assoc] using hadj
          exact hprev.trans hstep.reachable
      have hne : Nonempty (B' k) := ⟨root⟩
      refine SimpleGraph.Connected.mk fun a b => ?_
      have ha : (G.induce (B' k)).Reachable root a := by
        obtain ⟨j, hj1, hj2, hj_eq⟩ := (hB'_mem_last k hk _).mp a.property
        have h1 := hreach_root (j - (t - 1)) (by omega)
        have ha_eq : (⟨c.getVert (t - 1 + (j - (t - 1))),
            (hB'_mem_last k hk _).mpr ⟨t - 1 + (j - (t - 1)), by omega, by omega, rfl⟩⟩ : B' k) = a := by
          apply Subtype.ext
          simp only [Nat.add_sub_cancel' hj1]
          exact hj_eq.symm
        exact ha_eq ▸ h1
      have hb : (G.induce (B' k)).Reachable root b := by
        obtain ⟨j, hj1, hj2, hj_eq⟩ := (hB'_mem_last k hk _).mp b.property
        have h1 := hreach_root (j - (t - 1)) (by omega)
        have hb_eq : (⟨c.getVert (t - 1 + (j - (t - 1))),
            (hB'_mem_last k hk _).mpr ⟨t - 1 + (j - (t - 1)), by omega, by omega, rfl⟩⟩ : B' k) = b := by
          apply Subtype.ext
          simp only [Nat.add_sub_cancel' hj1]
          exact hj_eq.symm
        exact hb_eq ▸ h1
      exact ha.symm.trans hb
  · intro v₁ v₂ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    obtain ⟨j₁, hj1L, hx1eq, hj1k⟩ := hB'_vert (σ.symm v₁) x hx1
    obtain ⟨j₂, hj2L, hx2eq, hj2k⟩ := hB'_vert (σ.symm v₂) x hx2
    have hj_eq : j₁ = j₂ :=
      OMA.P_opg_forcing_2reg_R1_H2.cycle_getVert_inj hcyc j₁ j₂ hj1L hj2L (hx1eq.symm.trans hx2eq)
    have hk_ne : (σ.symm v₁).val ≠ (σ.symm v₂).val := fun h =>
      hne (σ.symm.injective (Fin.ext h))
    by_cases h1 : (σ.symm v₁).val < t - 1 <;> by_cases h2 : (σ.symm v₂).val < t - 1
    · simp only [h1, ite_true] at hj1k
      simp only [h2, ite_true] at hj2k
      omega
    · simp only [h1, ite_true] at hj1k
      simp only [h2, ite_false] at hj2k
      omega
    · simp only [h1, ite_false] at hj1k
      simp only [h2, ite_true] at hj2k
      omega
    · have hi1 := (σ.symm v₁).isLt
      have hi2 := (σ.symm v₂).isLt
      omega
  · have hstep_edge : ∀ (i j : Fin t), (i.val + 1) % t = j.val →
        ∃ x ∈ B' i, ∃ y ∈ B' j, G.Adj x y := by
      intro i j hij
      by_cases hi : i.val < t - 1
      · have hj_val : j.val = i.val + 1 := by
          rw [← hij, Nat.mod_eq_of_lt (by omega)]
        have hx : c.getVert i.val ∈ B' i := (hB'_mem_lt i hi _).mpr rfl
        have hy : c.getVert (i.val + 1) ∈ B' j := by
          by_cases hj : j.val < t - 1
          · rw [hB'_mem_lt j hj, hj_val]
          · rw [hB'_mem_last j hj]
            exact ⟨i.val + 1, by omega, by omega, rfl⟩
        exact ⟨c.getVert i.val, hx, c.getVert (i.val + 1), hy, c.adj_getVert_succ (by omega)⟩
      · have hi_eq : i.val = t - 1 := by have := i.isLt; omega
        have hj_val : j.val = 0 := by
          rw [← hij, hi_eq, show t - 1 + 1 = t by omega, Nat.mod_self]
        have hx : c.getVert (L - 1) ∈ B' i :=
          (hB'_mem_last i hi _).mpr ⟨L - 1, by omega, by omega, rfl⟩
        have hy : c.getVert 0 ∈ B' j := by
          have hj : j.val < t - 1 := by omega
          rw [hB'_mem_lt j hj, hj_val]
        have hadj : G.Adj (c.getVert (L - 1)) (c.getVert 0) := by
          have h1 : G.Adj (c.getVert (L - 1)) (c.getVert L) := by
            have := c.adj_getVert_succ (i := L - 1) (by omega)
            rwa [Nat.sub_add_cancel (by omega : 1 ≤ L)] at this
          rw [c.getVert_zero]
          rwa [c.getVert_length] at h1
        exact ⟨c.getVert (L - 1), hx, c.getVert 0, hy, hadj⟩
    intro v₁ v₂ hadj
    have hσ_adj : H.Adj (σ (σ.symm v₁)) (σ (σ.symm v₂)) := by simpa using hadj
    rcases hσ (σ.symm v₁) (σ.symm v₂) hσ_adj with h1 | h2
    · exact hstep_edge (σ.symm v₁) (σ.symm v₂) h1
    · obtain ⟨y, hy, x, hx, hyx⟩ := hstep_edge (σ.symm v₂) (σ.symm v₁) h2
      exact ⟨x, hx, y, hy, hyx.symm⟩

