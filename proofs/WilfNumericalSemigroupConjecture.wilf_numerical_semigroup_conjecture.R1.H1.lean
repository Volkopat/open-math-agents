import OMAReductions.R_WilfNumericalSemigroupConjecture_wilf_numerical_semigroup_conjecture_R1
import Mathlib

namespace OMA.WilfH1

open Finset

/-- The set of sums of the pairs in `s`. -/
def sums (s : Finset (ℕ × ℕ)) : Finset ℕ := s.image (fun p => p.1 + p.2)

theorem mem_sums {s : Finset (ℕ × ℕ)} {v : ℕ} : v ∈ sums s ↔ ∃ p ∈ s, p.1 + p.2 = v := by
  unfold sums
  exact Finset.mem_image

theorem card_sums_le (s : Finset (ℕ × ℕ)) : (sums s).card ≤ s.card := Finset.card_image_le

theorem one_le_of_mem {α : Type*} {s : Finset α} {a : α} (ha : a ∈ s) : 1 ≤ s.card :=
  Finset.card_pos.mpr ⟨a, ha⟩

theorem two_le_of_mem {α : Type*} [DecidableEq α] {s : Finset α} {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) : 2 ≤ s.card := by
  have hsub : ({a, b} : Finset α) ⊆ s := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  calc 2 = ({a, b} : Finset α).card := (Finset.card_pair hab).symm
    _ ≤ s.card := Finset.card_le_card hsub

theorem three_le_of_mem {α : Type*} [DecidableEq α] {s : Finset α} {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ s.card := by
  have hsub : ({a, b, c} : Finset α) ⊆ s := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  calc 3 = ({a, b, c} : Finset α).card :=
        (Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩).symm
    _ ≤ s.card := Finset.card_le_card hsub

theorem pair_ne {a b c d : ℕ} (h : a ≠ c) : (a, b) ≠ (c, d) := fun e => h (congrArg Prod.fst e)

theorem sum_fiber (s : Finset (ℕ × ℕ)) (U : Finset ℕ) :
    ∑ v ∈ U, (s.filter (fun p => p.1 + p.2 = v)).card
      = (s.filter (fun p => p.1 + p.2 ∈ U)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1 + p.2) (t := U)]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro p _
    constructor
    · intro h
      exact ⟨by rw [h]; exact hv, h⟩
    · intro h
      exact h.2
  · intro p hp
    rw [Finset.mem_coe] at hp ⊢
    exact (Finset.mem_filter.mp hp).2

/-- The core counting lemma for the part of `[c, c+m)` above `3m`. -/
theorem L1 (M : ℕ) (Alo B B' : Finset ℕ) (h0 : 0 ∈ Alo) (hAlo : ∀ x ∈ Alo, x < M)
    (hB : ∀ x ∈ B, x < M) (hcl : ∀ x ∈ Alo, ∀ y ∈ Alo, x + y < M → x + y ∈ B) (hB'B : B' ⊆ B)
    (hB'c : ∀ z ∈ B, z ∉ B' → ∃ x ∈ Alo, ∃ y ∈ Alo, x + y = z) :
    3 * ((sums (Alo ×ˢ B)).filter (· < M)).card
      + ((Alo ×ˢ Alo).filter (fun p => M ≤ p.1 + p.2)).card
      + ((Alo ×ˢ B).filter (fun p => M ≤ p.1 + p.2)).card
      + 2 * ((Alo.erase 0).filter (fun x => M ≤ 3 * x)).card
      ≤ (Alo.card + B'.card) * (1 + Alo.card + B.card) := by
  classical
  set T := (sums (Alo ×ˢ B)).filter (· < M) with hT
  set U := T.filter (· ∉ B) with hU
  have hmemT : ∀ v, v ∈ T ↔ v ∈ sums (Alo ×ˢ B) ∧ v < M := fun v => by
    rw [hT, Finset.mem_filter]
  have hmemU : ∀ v, v ∈ U ↔ (v ∈ sums (Alo ×ˢ B) ∧ v < M) ∧ v ∉ B := fun v => by
    rw [hU, Finset.mem_filter, hmemT]
  have hAB : ∀ x ∈ Alo, x ∈ B := by
    intro x hx
    have := hcl x hx 0 h0 (by have := hAlo x hx; omega)
    simpa using this
  have hAB' : Alo ⊆ B := fun x hx => hAB x hx
  have hab : Alo.card ≤ B.card := Finset.card_le_card hAB'
  have hBT : B ⊆ T := by
    intro z hz
    rw [hmemT, mem_sums]
    exact ⟨⟨(0, z), Finset.mem_product.mpr ⟨h0, hz⟩, by simp⟩, hB z hz⟩
  have hTU : T.card = B.card + U.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := T) (fun v => v ∈ B)]
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hBT]
  -- pairs from Alo x Alo
  set PAA := (Alo ×ˢ Alo).filter (fun p : ℕ × ℕ => p.1 + p.2 < M) with hPAA
  set GAA := (Alo ×ˢ Alo).filter (fun p : ℕ × ℕ => M ≤ p.1 + p.2) with hGAA
  have hAA : PAA.card + GAA.card = Alo.card * Alo.card := by
    have := Finset.card_filter_add_card_filter_not (s := Alo ×ˢ Alo)
      (fun p : ℕ × ℕ => p.1 + p.2 < M)
    rw [Finset.card_product] at this
    have hneg : (Alo ×ˢ Alo).filter (fun p : ℕ × ℕ => ¬ (p.1 + p.2 < M)) = GAA := by
      rw [hGAA]
      apply Finset.filter_congr
      intro p _
      exact not_lt
    rw [hneg] at this
    exact this
  -- pairs from Alo x B
  set XB := (Alo ×ˢ B).filter (fun p : ℕ × ℕ => p.1 + p.2 ∈ B) with hXB
  set XU := (Alo ×ˢ B).filter (fun p : ℕ × ℕ => p.1 + p.2 ∈ U) with hXU
  set GAB := (Alo ×ˢ B).filter (fun p : ℕ × ℕ => M ≤ p.1 + p.2) with hGAB
  have hXpart : XB.card + XU.card + GAB.card = Alo.card * B.card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := Alo ×ˢ B)
      (fun p : ℕ × ℕ => p.1 + p.2 ∈ B)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := (Alo ×ˢ B).filter (fun p : ℕ × ℕ => ¬ (p.1 + p.2 ∈ B)))
      (fun p : ℕ × ℕ => p.1 + p.2 < M)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    have e1 : (Alo ×ˢ B).filter (fun p : ℕ × ℕ => ¬ (p.1 + p.2 ∈ B) ∧ p.1 + p.2 < M) = XU := by
      rw [hXU]
      apply Finset.filter_congr
      intro p hp
      rw [hmemU, mem_sums]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨⟨p, hp, rfl⟩, h2⟩, h1⟩
      · rintro ⟨⟨_, h2⟩, h1⟩
        exact ⟨h1, h2⟩
    have e2 : (Alo ×ˢ B).filter
        (fun p : ℕ × ℕ => ¬ (p.1 + p.2 ∈ B) ∧ ¬ (p.1 + p.2 < M)) = GAB := by
      rw [hGAB]
      apply Finset.filter_congr
      intro p _
      constructor
      · rintro ⟨_, h2⟩
        omega
      · intro h
        refine ⟨fun hm => ?_, by omega⟩
        have := hB _ hm
        omega
    rw [e1, e2] at h2
    rw [Finset.card_product, ← hXB] at h1
    omega
  -- (i)
  have hi : PAA.card + (B.filter (· ∉ Alo)).card ≤ XB.card := by
    have hdisj : Disjoint PAA ((B.filter (· ∉ Alo)).image (fun b => ((0 : ℕ), b))) := by
      rw [Finset.disjoint_left]
      intro p hp hp2
      rw [Finset.mem_image] at hp2
      obtain ⟨b, hb, rfl⟩ := hp2
      rw [Finset.mem_filter] at hb
      rw [hPAA, Finset.mem_filter, Finset.mem_product] at hp
      exact hb.2 hp.1.2
    have hcard : ((B.filter (· ∉ Alo)).image (fun b => ((0 : ℕ), b))).card
        = (B.filter (· ∉ Alo)).card :=
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)
    rw [← hcard, ← Finset.card_union_of_disjoint hdisj]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_union] at hp
    rw [hXB, Finset.mem_filter, Finset.mem_product]
    rcases hp with hp | hp
    · rw [hPAA, Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨⟨hp.1.1, hAB _ hp.1.2⟩, hcl _ hp.1.1 _ hp.1.2 hp.2⟩
    · rw [Finset.mem_image] at hp
      obtain ⟨b, hb, rfl⟩ := hp
      rw [Finset.mem_filter] at hb
      exact ⟨⟨h0, hb.1⟩, by simpa using hb.1⟩
  have hBA : (B.filter (· ∉ Alo)).card + Alo.card = B.card := by
    have := Finset.card_filter_add_card_filter_not (s := B) (fun z => z ∈ Alo)
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hAB'] at this
    omega
  -- pairs from B' x Alo
  set YB := (B' ×ˢ Alo).filter (fun p : ℕ × ℕ => p.1 + p.2 ∈ B) with hYB
  set YU := (B' ×ˢ Alo).filter (fun p : ℕ × ℕ => p.1 + p.2 ∈ U) with hYU
  have hY : YB.card + YU.card ≤ B'.card * Alo.card := by
    rw [← Finset.card_product, ← Finset.card_union_of_disjoint]
    · apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact (Finset.mem_filter.mp hp).1
      · exact (Finset.mem_filter.mp hp).1
    · rw [hYB, hYU]
      apply Finset.disjoint_filter.mpr
      intro p _ h1 h2
      exact ((hmemU _).mp h2).2 h1
  have hii : B'.card ≤ YB.card := by
    rw [← Finset.card_image_of_injective B' (f := fun z => (z, (0 : ℕ)))
      (fun a b h => by simpa using h)]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨z, hz, rfl⟩ := hp
    rw [hYB, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hz, h0⟩, by simpa using hB'B hz⟩
  -- the per-element bound on U
  set Rset := ((Alo.erase 0) ×ˢ (Alo.erase 0)).filter
    (fun p : ℕ × ℕ => p.1 ≠ p.2 ∧ p.1 + p.2 < M) with hRset
  set K3 := (Alo.erase 0).filter (fun x => 3 * x < M) with hK3
  set Kset := (Alo.erase 0).filter (fun x => M ≤ 3 * x) with hKset
  set Q1 := sums (Alo ×ˢ B') with hQ1
  set Q3 := K3.image (fun x => 3 * x) with hQ3
  set Q2 := Rset.image (fun p : ℕ × ℕ => 2 * p.1 + p.2) with hQ2
  have perv : ∀ v ∈ U, 3 ≤ ((Alo ×ˢ B).filter (fun p : ℕ × ℕ => p.1 + p.2 = v)).card
      + ((B' ×ˢ Alo).filter (fun p : ℕ × ℕ => p.1 + p.2 = v)).card
      + (if v ∈ Q1 then 1 else 0) + 2 * (if v ∈ Q3 then 1 else 0)
      + (if v ∈ Q2 then 1 else 0) := by
    intro v hv
    rw [hmemU, mem_sums] at hv
    obtain ⟨⟨⟨⟨x, b⟩, hxb, hsum⟩, hvM⟩, hvB⟩ := hv
    rw [Finset.mem_product] at hxb
    obtain ⟨hx, hb⟩ := hxb
    simp only at hsum hx hb
    subst hsum
    by_cases hb' : b ∈ B'
    · have h1 : 1 ≤ ((Alo ×ˢ B).filter (fun p : ℕ × ℕ => p.1 + p.2 = x + b)).card :=
        one_le_of_mem (a := (x, b))
          (by rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hx, hb⟩, rfl⟩)
      have h2 : 1 ≤ ((B' ×ˢ Alo).filter (fun p : ℕ × ℕ => p.1 + p.2 = x + b)).card :=
        one_le_of_mem (a := (b, x))
          (by rw [Finset.mem_filter, Finset.mem_product]; exact ⟨⟨hb', hx⟩, Nat.add_comm b x⟩)
      have hq : x + b ∈ Q1 := by
        rw [hQ1, mem_sums]
        exact ⟨(x, b), Finset.mem_product.mpr ⟨hx, hb'⟩, rfl⟩
      rw [if_pos hq]
      omega
    · obtain ⟨y, hy, z, hz, hyz⟩ := hB'c b hb hb'
      subst hyz
      have hx0 : x ≠ 0 := by
        rintro rfl
        apply hvB
        simpa using hb
      have hy0 : y ≠ 0 := by
        rintro rfl
        apply hvB
        simpa using hcl x hx z hz (by omega)
      have hz0 : z ≠ 0 := by
        rintro rfl
        apply hvB
        simpa using hcl x hx y hy (by omega)
      have hxz : x + z ∈ B := hcl x hx z hz (by omega)
      have hxy : x + y ∈ B := hcl x hx y hy (by omega)
      set F := (Alo ×ˢ B).filter (fun p : ℕ × ℕ => p.1 + p.2 = x + (y + z)) with hF
      have m1 : (x, y + z) ∈ F := by
        rw [hF, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hx, hb⟩, rfl⟩
      have m2 : (y, x + z) ∈ F := by
        rw [hF, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hy, hxz⟩, by simp only; omega⟩
      have m3 : (z, x + y) ∈ F := by
        rw [hF, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hz, hxy⟩, by simp only; omega⟩
      by_cases e1 : x = y
      · by_cases e2 : x = z
        · have hq : x + (y + z) ∈ Q3 := by
            rw [hQ3, Finset.mem_image]
            refine ⟨x, ?_, by omega⟩
            rw [hK3, Finset.mem_filter, Finset.mem_erase]
            exact ⟨⟨hx0, hx⟩, by omega⟩
          have := one_le_of_mem m1
          rw [if_pos hq]
          omega
        · have hq : x + (y + z) ∈ Q2 := by
            rw [hQ2, Finset.mem_image]
            refine ⟨(x, z), ?_, by simp only; omega⟩
            rw [hRset, Finset.mem_filter, Finset.mem_product, Finset.mem_erase, Finset.mem_erase]
            exact ⟨⟨⟨hx0, hx⟩, ⟨hz0, hz⟩⟩, e2, by simp only; omega⟩
          have := two_le_of_mem m1 m3 (pair_ne e2)
          rw [if_pos hq]
          omega
      · by_cases e2 : y = z
        · have hq : x + (y + z) ∈ Q2 := by
            rw [hQ2, Finset.mem_image]
            refine ⟨(y, x), ?_, by simp only; omega⟩
            rw [hRset, Finset.mem_filter, Finset.mem_product, Finset.mem_erase, Finset.mem_erase]
            exact ⟨⟨⟨hy0, hy⟩, ⟨hx0, hx⟩⟩, fun h => e1 h.symm, by simp only; omega⟩
          have := two_le_of_mem m1 m2 (pair_ne e1)
          rw [if_pos hq]
          omega
        · by_cases e3 : x = z
          · have hq : x + (y + z) ∈ Q2 := by
              rw [hQ2, Finset.mem_image]
              refine ⟨(x, y), ?_, by simp only; omega⟩
              rw [hRset, Finset.mem_filter, Finset.mem_product, Finset.mem_erase,
                Finset.mem_erase]
              exact ⟨⟨⟨hx0, hx⟩, ⟨hy0, hy⟩⟩, e1, by simp only; omega⟩
            have := two_le_of_mem m1 m2 (pair_ne e1)
            rw [if_pos hq]
            omega
          · have := three_le_of_mem m1 m2 m3 (pair_ne e1) (pair_ne e3) (pair_ne e2)
            omega
  have hsumU := Finset.sum_le_sum perv
  rw [Finset.sum_const, smul_eq_mul] at hsumU
  simp only [Finset.sum_add_distrib] at hsumU
  rw [← Finset.mul_sum, sum_fiber, sum_fiber, ← Finset.card_filter, ← Finset.card_filter,
    ← Finset.card_filter] at hsumU
  -- bounds on the indicator parts
  have h4 : (U.filter (· ∈ Q1)).card ≤ Alo.card * B'.card := by
    calc (U.filter (· ∈ Q1)).card ≤ Q1.card :=
          Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ (Alo ×ˢ B').card := by rw [hQ1]; exact card_sums_le _
      _ = Alo.card * B'.card := Finset.card_product _ _
  have h5 : (U.filter (· ∈ Q3)).card ≤ K3.card := by
    calc (U.filter (· ∈ Q3)).card ≤ Q3.card :=
          Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ K3.card := by rw [hQ3]; exact Finset.card_image_le
  have h6 : (U.filter (· ∈ Q2)).card ≤ Rset.card := by
    calc (U.filter (· ∈ Q2)).card ≤ Q2.card :=
          Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)
      _ ≤ Rset.card := by rw [hQ2]; exact Finset.card_image_le
  have hK : K3.card + Kset.card = (Alo.erase 0).card := by
    have := Finset.card_filter_add_card_filter_not (s := Alo.erase 0) (fun x => 3 * x < M)
    have hneg : (Alo.erase 0).filter (fun x => ¬ (3 * x < M)) = Kset := by
      rw [hKset]
      apply Finset.filter_congr
      intro p _
      exact not_lt
    rw [hneg] at this
    exact this
  have herase : (Alo.erase 0).card + 1 = Alo.card := Finset.card_erase_add_one h0
  have hXU' : (Alo ×ˢ B).filter (fun p : ℕ × ℕ => p.1 + p.2 ∈ U) = XU := by rw [hXU]
  have hYU' : (B' ×ˢ Alo).filter (fun p : ℕ × ℕ => p.1 + p.2 ∈ U) = YU := by rw [hYU]
  rw [hXU', hYU'] at hsumU
  -- (vii)
  have hBB' : (B.filter (· ∉ B')).card + B'.card = B.card := by
    have := Finset.card_filter_add_card_filter_not (s := B) (fun z => z ∈ B')
    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hB'B] at this
    omega
  have hvii : 2 * (B.filter (· ∉ B')).card + 2 * (Alo.erase 0).card + Rset.card
      ≤ 2 * PAA.card := by
    have hs1 := Finset.card_filter_add_card_filter_not (s := PAA) (fun p : ℕ × ℕ => p.1 ≤ p.2)
    have hp1 : (B.filter (· ∉ B')).card ≤ (PAA.filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card := by
      calc (B.filter (· ∉ B')).card ≤ (sums (PAA.filter (fun p : ℕ × ℕ => p.1 ≤ p.2))).card := by
            apply Finset.card_le_card
            intro z hz
            rw [Finset.mem_filter] at hz
            obtain ⟨x, hx, y, hy, rfl⟩ := hB'c z hz.1 hz.2
            have hlt := hB _ hz.1
            rw [mem_sums]
            by_cases hxy : x ≤ y
            · refine ⟨(x, y), ?_, rfl⟩
              rw [Finset.mem_filter, hPAA, Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨⟨hx, hy⟩, hlt⟩, hxy⟩
            · refine ⟨(y, x), ?_, by simp only; omega⟩
              rw [Finset.mem_filter, hPAA, Finset.mem_filter, Finset.mem_product]
              exact ⟨⟨⟨hy, hx⟩, by simp only; omega⟩, by simp only; omega⟩
        _ ≤ _ := card_sums_le _
    set R1 := Rset.filter (fun p : ℕ × ℕ => p.2 < p.1) with hR1
    have hp2 : (Alo.erase 0).card + R1.card
        ≤ (PAA.filter (fun p : ℕ × ℕ => ¬ (p.1 ≤ p.2))).card := by
      have hdisj : Disjoint ((Alo.erase 0).image (fun x => (x, (0 : ℕ)))) R1 := by
        rw [Finset.disjoint_left]
        intro p hp hp2
        rw [Finset.mem_image] at hp
        obtain ⟨x, _, rfl⟩ := hp
        rw [hR1, Finset.mem_filter, hRset, Finset.mem_filter, Finset.mem_product,
          Finset.mem_erase, Finset.mem_erase] at hp2
        exact hp2.1.1.2.1 rfl
      rw [← Finset.card_image_of_injective (Alo.erase 0) (f := fun x => (x, (0 : ℕ)))
        (fun a b h => by simpa using h), ← Finset.card_union_of_disjoint hdisj]
      apply Finset.card_le_card
      intro p hp
      rw [Finset.mem_union] at hp
      rw [Finset.mem_filter, hPAA, Finset.mem_filter, Finset.mem_product]
      rcases hp with hp | hp
      · rw [Finset.mem_image] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        rw [Finset.mem_erase] at hx
        have := hAlo x hx.2
        exact ⟨⟨⟨hx.2, h0⟩, by simp only; omega⟩, by simp only; omega⟩
      · rw [hR1, Finset.mem_filter, hRset, Finset.mem_filter, Finset.mem_product,
          Finset.mem_erase, Finset.mem_erase] at hp
        exact ⟨⟨⟨hp.1.1.1.2, hp.1.1.2.2⟩, hp.1.2.2⟩, by omega⟩
    have hsym : (Rset.filter (fun p : ℕ × ℕ => ¬ (p.2 < p.1))).card = R1.card := by
      rw [hR1]
      apply Finset.card_nbij' Prod.swap Prod.swap
      · intro p hp
        rw [Finset.mem_coe] at hp ⊢
        rw [Finset.mem_filter, hRset, Finset.mem_filter, Finset.mem_product, Finset.mem_erase,
          Finset.mem_erase] at hp ⊢
        obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hp
        refine ⟨⟨⟨h2, h1⟩, ?_, ?_⟩, ?_⟩
        · simp only [Prod.fst_swap, Prod.snd_swap]
          exact fun h => h3 h.symm
        · simp only [Prod.fst_swap, Prod.snd_swap]
          omega
        · simp only [Prod.fst_swap, Prod.snd_swap]
          omega
      · intro p hp
        rw [Finset.mem_coe] at hp ⊢
        rw [Finset.mem_filter, hRset, Finset.mem_filter, Finset.mem_product, Finset.mem_erase,
          Finset.mem_erase] at hp ⊢
        obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hp
        refine ⟨⟨⟨h2, h1⟩, ?_, ?_⟩, ?_⟩
        · simp only [Prod.fst_swap, Prod.snd_swap]
          exact fun h => h3 h.symm
        · simp only [Prod.fst_swap, Prod.snd_swap]
          omega
        · simp only [Prod.fst_swap, Prod.snd_swap]
          omega
      · intro p _
        exact Prod.swap_swap p
      · intro p _
        exact Prod.swap_swap p
    have hsplit := Finset.card_filter_add_card_filter_not (s := Rset) (fun p : ℕ × ℕ => p.2 < p.1)
    rw [← hR1, hsym] at hsplit
    omega
  have hmul : Alo.card * B'.card ≤ B.card * B'.card := Nat.mul_le_mul_right _ hab
  have hexp : (Alo.card + B'.card) * (1 + Alo.card + B.card)
      = Alo.card + Alo.card * Alo.card + Alo.card * B.card + B'.card + B'.card * Alo.card
        + B'.card * B.card := by ring
  rw [hexp, hTU]
  nlinarith



theorem L2arith (W P1 P2 P3 Q4 Q5 Q6 GAA GAB K h alo a b β mM : ℕ)
    (hper : 3 * W ≤ 2 * P1 + 3 * P2 + P3 + Q4 + 2 * Q5 + Q6)
    (h1 : P1 ≤ GAA) (h1' : P1 ≤ GAB) (h2 : P2 ≤ alo * h) (h3 : P3 ≤ h * h) (h4 : Q4 ≤ h)
    (h5 : Q5 ≤ K) (h6 : Q6 ≤ mM) (hlob : alo ≤ b) (ha : a = alo + h) :
    3 * W ≤ GAA + GAB + 2 * K + h * (1 + a + b) + (alo + β) * h + mM := by
  subst ha
  have := Nat.mul_le_mul_left h hlob
  nlinarith

theorem L2 (m M : ℕ) (hM : 1 ≤ M) (hMm : M ≤ m) (A B : Finset ℕ) (hA0 : 0 ∈ A)
    (hA : ∀ x ∈ A, x < m) (hB : ∀ y ∈ B, y < M)
    (hAAB : ∀ x ∈ A, ∀ y ∈ A, x + y < M → x + y ∈ B) :
    3 * ((Finset.image (fun p : ℕ × ℕ => p.1 + p.2) (A ×ˢ A)).filter
        (fun w => M ≤ w ∧ w < m + M)).card
    ≤ (((A.filter (· < M)) ×ˢ (A.filter (· < M))).filter (fun p => M ≤ p.1 + p.2)).card
      + (((A.filter (· < M)) ×ˢ B).filter (fun p => M ≤ p.1 + p.2)).card
      + 2 * ((A.filter (· < M)).filter (fun x => 0 < x ∧ M ≤ 3 * x)).card
      + (A.filter (M ≤ ·)).card * (1 + A.card + B.card)
      + ((A.filter (· < M)).card
          + (B.filter (fun y => y ∉ Finset.image (fun p : ℕ × ℕ => p.1 + p.2) (A ×ˢ A))).card)
        * (A.filter (M ≤ ·)).card
      + (m - M) := by
  classical
  set Alo := A.filter (· < M) with hAlo
  set Ahi := A.filter (M ≤ ·) with hAhi
  set W := (Finset.image (fun p : ℕ × ℕ => p.1 + p.2) (A ×ˢ A)).filter
        (fun w => M ≤ w ∧ w < m + M) with hW
  set P1 := (Alo ×ˢ Alo).filter (fun p => p.1 + p.2 ∈ W) with hP1
  set P2 := (Alo ×ˢ Ahi).filter (fun p => p.1 + p.2 ∈ W) with hP2
  set P3 := (Ahi ×ˢ Ahi).filter (fun p => p.1 + p.2 ∈ W) with hP3
  set Q4 := Ahi.filter (fun y => 2 * y ∈ W) with hQ4
  set Q5 := Alo.filter (fun x => 2 * x ∈ W) with hQ5
  set Q6 := W.filter (fun w => 2 * M ≤ w) with hQ6
  have hAloB : ∀ x ∈ Alo, x ∈ B := by
    intro x hx
    rw [hAlo, Finset.mem_filter] at hx
    have := hAAB x hx.1 0 hA0 (by omega)
    simpa using this
  have hmemW : ∀ x ∈ A, ∀ y ∈ A, M ≤ x + y → x + y < m + M → x + y ∈ W := by
    intro x hx y hy h1 h2
    rw [hW, Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩, h1, h2⟩
  -- per-element inequality
  have hper : ∀ w ∈ W, 3 ≤ 2 * (P1.filter (fun p => p.1 + p.2 = w)).card
      + 3 * (P2.filter (fun p => p.1 + p.2 = w)).card
      + (P3.filter (fun p => p.1 + p.2 = w)).card
      + (Q4.filter (fun y => 2 * y = w)).card
      + 2 * (Q5.filter (fun x => 2 * x = w)).card
      + (Q6.filter (fun v => v = w)).card := by
    intro w hw
    have hw' := hw
    rw [hW, Finset.mem_filter, Finset.mem_image] at hw'
    obtain ⟨⟨⟨x, y⟩, hxy, rfl⟩, hw1, hw2⟩ := hw'
    rw [Finset.mem_product] at hxy
    obtain ⟨hx, hy⟩ := hxy
    simp only at hw1 hw2 ⊢
    by_cases hxl : x < M <;> by_cases hyl : y < M
    · -- both low
      have hxA : x ∈ Alo := by rw [hAlo, Finset.mem_filter]; exact ⟨hx, hxl⟩
      have hyA : y ∈ Alo := by rw [hAlo, Finset.mem_filter]; exact ⟨hy, hyl⟩
      have m1 : (x, y) ∈ P1.filter (fun p => p.1 + p.2 = x + y) := by
        rw [Finset.mem_filter, hP1, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨⟨hxA, hyA⟩, hw⟩, rfl⟩
      by_cases hxy : x = y
      · subst hxy
        have m5 : x ∈ Q5.filter (fun z => 2 * z = x + x) := by
          rw [Finset.mem_filter, hQ5, Finset.mem_filter]
          exact ⟨⟨hxA, by rw [two_mul]; exact hw⟩, by ring⟩
        have c1 := Finset.card_pos.mpr ⟨_, m1⟩
        have c5 := Finset.card_pos.mpr ⟨_, m5⟩
        omega
      · have m1' : (y, x) ∈ P1.filter (fun p => p.1 + p.2 = x + y) := by
          rw [Finset.mem_filter, hP1, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨⟨hyA, hxA⟩, by rw [add_comm]; exact hw⟩, by simp [add_comm]⟩
        have c1 : 1 < (P1.filter (fun p => p.1 + p.2 = x + y)).card :=
          Finset.one_lt_card.mpr ⟨_, m1, _, m1', by simp [hxy]⟩
        omega
    · have hxA : x ∈ Alo := by rw [hAlo, Finset.mem_filter]; exact ⟨hx, hxl⟩
      have hyA : y ∈ Ahi := by rw [hAhi, Finset.mem_filter]; exact ⟨hy, by omega⟩
      have m2 : (x, y) ∈ P2.filter (fun p => p.1 + p.2 = x + y) := by
        rw [Finset.mem_filter, hP2, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨⟨hxA, hyA⟩, hw⟩, rfl⟩
      have c2 := Finset.card_pos.mpr ⟨_, m2⟩
      omega
    · have hyA : y ∈ Alo := by rw [hAlo, Finset.mem_filter]; exact ⟨hy, hyl⟩
      have hxA : x ∈ Ahi := by rw [hAhi, Finset.mem_filter]; exact ⟨hx, by omega⟩
      have m2 : (y, x) ∈ P2.filter (fun p => p.1 + p.2 = x + y) := by
        rw [Finset.mem_filter, hP2, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨⟨hyA, hxA⟩, by rw [add_comm]; exact hw⟩, by simp [add_comm]⟩
      have c2 := Finset.card_pos.mpr ⟨_, m2⟩
      omega
    · -- both high
      have hxA : x ∈ Ahi := by rw [hAhi, Finset.mem_filter]; exact ⟨hx, by omega⟩
      have hyA : y ∈ Ahi := by rw [hAhi, Finset.mem_filter]; exact ⟨hy, by omega⟩
      have m3 : (x, y) ∈ P3.filter (fun p => p.1 + p.2 = x + y) := by
        rw [Finset.mem_filter, hP3, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨⟨hxA, hyA⟩, hw⟩, rfl⟩
      have m6 : x + y ∈ Q6.filter (fun v => v = x + y) := by
        rw [Finset.mem_filter, hQ6, Finset.mem_filter]
        exact ⟨⟨hw, by omega⟩, rfl⟩
      have c6 := Finset.card_pos.mpr ⟨_, m6⟩
      by_cases hxy : x = y
      · subst hxy
        have m4 : x ∈ Q4.filter (fun z => 2 * z = x + x) := by
          rw [Finset.mem_filter, hQ4, Finset.mem_filter]
          exact ⟨⟨hxA, by rw [two_mul]; exact hw⟩, by ring⟩
        have c3 := Finset.card_pos.mpr ⟨_, m3⟩
        have c4 := Finset.card_pos.mpr ⟨_, m4⟩
        omega
      · have m3' : (y, x) ∈ P3.filter (fun p => p.1 + p.2 = x + y) := by
          rw [Finset.mem_filter, hP3, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨⟨hyA, hxA⟩, by rw [add_comm]; exact hw⟩, by simp [add_comm]⟩
        have c3 : 1 < (P3.filter (fun p => p.1 + p.2 = x + y)).card :=
          Finset.one_lt_card.mpr ⟨_, m3, _, m3', by simp [hxy]⟩
        omega
  have hsum : 3 * W.card ≤ 2 * P1.card + 3 * P2.card + P3.card + Q4.card + 2 * Q5.card
      + Q6.card := by
    have e1 := Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1 + p.2) (s := P1)
      (t := W) (fun p hp => (Finset.mem_filter.mp hp).2)
    have e2 := Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1 + p.2) (s := P2)
      (t := W) (fun p hp => (Finset.mem_filter.mp hp).2)
    have e3 := Finset.card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ => p.1 + p.2) (s := P3)
      (t := W) (fun p hp => (Finset.mem_filter.mp hp).2)
    have e4 := Finset.card_eq_sum_card_fiberwise (f := fun y : ℕ => 2 * y) (s := Q4)
      (t := W) (fun p hp => (Finset.mem_filter.mp hp).2)
    have e5 := Finset.card_eq_sum_card_fiberwise (f := fun y : ℕ => 2 * y) (s := Q5)
      (t := W) (fun p hp => (Finset.mem_filter.mp hp).2)
    have e6 := Finset.card_eq_sum_card_fiberwise (f := fun y : ℕ => y) (s := Q6)
      (t := W) (fun p hp => (Finset.mem_filter.mp hp).1)
    have hs := Finset.sum_le_sum hper
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6, Finset.sum_const, smul_eq_mul] at hs
    omega
  apply L2arith W.card P1.card P2.card P3.card Q4.card Q5.card Q6.card _ _ _ Ahi.card
    Alo.card A.card B.card _ (m - M) hsum
  · apply Finset.card_le_card
    intro p hp
    rw [hP1, Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    refine ⟨hp.1, ?_⟩
    have := hp.2
    rw [hW, Finset.mem_filter] at this
    exact this.2.1
  · apply Finset.card_le_card
    intro p hp
    rw [hP1, Finset.mem_filter, Finset.mem_product] at hp
    rw [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hp.1.1, hAloB _ hp.1.2⟩, ?_⟩
    have := hp.2
    rw [hW, Finset.mem_filter] at this
    exact this.2.1
  · rw [← Finset.card_product]; exact Finset.card_filter_le _ _
  · rw [← Finset.card_product]; exact Finset.card_filter_le _ _
  · exact Finset.card_filter_le _ _
  · apply Finset.card_le_card
    intro x hx
    rw [hQ5, Finset.mem_filter] at hx
    rw [Finset.mem_filter]
    refine ⟨hx.1, ?_⟩
    have := hx.2
    rw [hW, Finset.mem_filter] at this
    omega
  · have : Q6 ⊆ Finset.Ico (2 * M) (m + M) := by
      intro w hw
      rw [hQ6, Finset.mem_filter] at hw
      have := hw.1
      rw [hW, Finset.mem_filter] at this
      rw [Finset.mem_Ico]; omega
    have := Finset.card_le_card this
    simp only [Nat.card_Ico] at this
    omega
  · exact Finset.card_le_card (fun x hx => hAloB x hx)
  · have e : A.filter (fun x => ¬ x < M) = Ahi := by
      rw [hAhi]; exact Finset.filter_congr (fun x _ => not_lt)
    have e2 : Alo.card + Ahi.card = A.card := by
      rw [← e, hAlo]; exact Finset.card_filter_add_card_filter_not _
    omega



open AddSubmonoid WilfNumericalSemigroupConjecture

/-- The combinatorial key inequality (proved separately). -/
def KeyProp : Prop :=
  ∀ (m M : ℕ), 1 ≤ M → M ≤ m → ∀ (A B : Finset ℕ), 0 ∈ A → (∀ x ∈ A, x < m) →
    (∀ y ∈ B, y < M) → (∀ x ∈ A, ∀ y ∈ A, x + y < M → x + y ∈ B) →
    3 * ((Finset.image (fun p : ℕ × ℕ => p.1 + p.2) (A ×ˢ B)).filter (· < M)).card
    + 3 * ((Finset.image (fun p : ℕ × ℕ => p.1 + p.2) (A ×ˢ A)).filter
        (fun w => M ≤ w ∧ w < m + M)).card
    ≤ (A.card + (B.filter (fun y => y ∉ Finset.image (fun p : ℕ × ℕ => p.1 + p.2) (A ×ˢ A))).card)
        * (1 + A.card + B.card) + (m - M)

theorem arith (m M a b β τ ω e : ℕ) (hMm : M ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (K : 3 * τ + 3 * ω ≤ (a + β) * (1 + a + b) + (m - M))
    (he : a + β + (m - (τ + ω)) ≤ e) : 2 * m + M ≤ e * (1 + a + b) := by
  by_cases hle : τ + ω ≤ m
  · obtain ⟨d, hd⟩ : ∃ d, τ + ω + d = m := ⟨m - (τ + ω), by omega⟩
    have he' : a + β + d ≤ e := by omega
    have h1 : (a + β + d) * (1 + a + b) ≤ e * (1 + a + b) := Nat.mul_le_mul_right _ he'
    have h2 : 3 * d ≤ d * (1 + a + b) := by nlinarith
    have h3 : (a + β + d) * (1 + a + b) = (a + β) * (1 + a + b) + d * (1 + a + b) := by ring
    obtain ⟨k, hk⟩ : ∃ k, M + k = m := ⟨m - M, by omega⟩
    have hk' : m - M = k := by omega
    rw [hk'] at K
    linarith
  · have he' : a + β ≤ e := by omega
    have h1 : (a + β) * (1 + a + b) ≤ e * (1 + a + b) := Nat.mul_le_mul_right _ he'
    omega

theorem trans (hkey : KeyProp) :
    OMA.R_WilfNumericalSemigroupConjecture_wilf_numerical_semigroup_conjecture_R1.H1 := by
  intro S hS h2 h3
  classical
  set c := S.conductor with hc
  set m := sInf {x : ℕ | 0 < x ∧ x ∈ S} with hm
  have hmem : ∀ y, c ≤ y → y ∈ S := fun y hy => hS.mem_of_conductor_le hy
  have hcpos : 0 < c := by omega
  have hne : {x : ℕ | 0 < x ∧ x ∈ S}.Nonempty := ⟨c, hcpos, hmem c le_rfl⟩
  obtain ⟨hmpos, hmS⟩ : 0 < m ∧ m ∈ S := Nat.sInf_mem hne
  have hmin : ∀ x, 0 < x → x ∈ S → m ≤ x := fun x hx hxS => Nat.sInf_le ⟨hx, hxS⟩
  set M := c - 2 * m with hM
  have hM1 : 1 ≤ M := by omega
  have hMm : M ≤ m := by omega
  have hcM : c = 2 * m + M := by omega
  set A := (Finset.range m).filter (fun x => m + x ∈ S) with hA
  set B := (Finset.range M).filter (fun y => 2 * m + y ∈ S) with hB
  have hA0 : 0 ∈ A := by
    simp only [hA, Finset.mem_filter, Finset.mem_range]; exact ⟨hmpos, by simpa using hmS⟩
  have hAlt : ∀ x ∈ A, x < m := by
    intro x hx; simp only [hA, Finset.mem_filter, Finset.mem_range] at hx; exact hx.1
  have hBlt : ∀ y ∈ B, y < M := by
    intro y hy; simp only [hB, Finset.mem_filter, Finset.mem_range] at hy; exact hy.1
  have hAAB : ∀ x ∈ A, ∀ y ∈ A, x + y < M → x + y ∈ B := by
    intro x hx y hy hxy
    simp only [hA, Finset.mem_filter, Finset.mem_range] at hx hy
    simp only [hB, Finset.mem_filter, Finset.mem_range]
    refine ⟨hxy, ?_⟩
    have := S.add_mem hx.2 hy.2
    have e : m + x + (m + y) = 2 * m + (x + y) := by ring
    rwa [e] at this
  have K := hkey m M hM1 hMm A B hA0 hAlt hBlt hAAB
  set f : ℕ × ℕ → ℕ := fun p => p.1 + p.2 with hf
  set T := (Finset.image f (A ×ˢ B)).filter (· < M) with hT
  set W := (Finset.image f (A ×ˢ A)).filter (fun w => M ≤ w ∧ w < m + M) with hW
  set B' := B.filter (fun y => y ∉ Finset.image f (A ×ˢ A)) with hB'
  -- sporadic count
  have hn : sporadicCount S = 1 + A.card + B.card := by
    unfold sporadicCount
    have hset : (Finset.range c).filter (· ∈ S) =
        insert 0 (A.image (m + ·) ∪ B.image (2 * m + ·)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_union,
        Finset.mem_image, hA, hB]
      constructor
      · rintro ⟨hx, hxS⟩
        rcases Nat.eq_zero_or_pos x with h0 | hpos
        · exact Or.inl h0
        · have := hmin x hpos hxS
          right
          by_cases h2m : x < 2 * m
          · left; exact ⟨x - m, ⟨by omega, by rwa [Nat.add_sub_cancel' this]⟩, by omega⟩
          · right
            exact ⟨x - 2 * m, ⟨by omega, by rwa [Nat.add_sub_cancel' (by omega)]⟩, by omega⟩
      · rintro (rfl | ⟨y, ⟨hy, hyS⟩, rfl⟩ | ⟨y, ⟨hy, hyS⟩, rfl⟩)
        · exact ⟨hcpos, S.zero_mem⟩
        · exact ⟨by omega, hyS⟩
        · exact ⟨by omega, hyS⟩
    rw [← hc, hset, Finset.card_insert_of_notMem, Finset.card_union_of_disjoint,
      Finset.card_image_of_injective _ (add_right_injective m),
      Finset.card_image_of_injective _ (add_right_injective (2 * m))]
    · ring
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_image, hA, hB, Finset.mem_filter, Finset.mem_range] at hx1 hx2
      obtain ⟨y, ⟨hy, _⟩, rfl⟩ := hx1
      obtain ⟨z, ⟨hz, _⟩, hz2⟩ := hx2
      omega
    · simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
      exact ⟨fun y _ h => by omega, fun y _ h => by omega⟩
  -- generators
  set G := {x : ℕ | 0 < x ∧ x ∈ S ∧
      ¬ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S ∧ b ∈ S ∧ x = a + b} with hG
  have hGfin : G.Finite := by
    apply (Set.finite_Iio (c + m)).subset
    rintro x ⟨hx, hxS, hnot⟩
    simp only [Set.mem_Iio]
    by_contra hge
    exact hnot ⟨m, x - m, hmpos, by omega, hmS, hmem _ (by omega), by omega⟩
  set R := Finset.Ico c (c + m) \ (T.image (3 * m + ·) ∪ W.image (2 * m + ·)) with hR
  have hRcard : m - (T.card + W.card) ≤ R.card := by
    have h1 := Finset.le_card_sdiff (T.image (3 * m + ·) ∪ W.image (2 * m + ·))
      (Finset.Ico c (c + m))
    have h2 := Finset.card_union_le (T.image (3 * m + ·)) (W.image (2 * m + ·))
    have h3 := Finset.card_image_le (s := T) (f := (3 * m + ·))
    have h4 := Finset.card_image_le (s := W) (f := (2 * m + ·))
    simp only [Nat.card_Ico] at h1
    rw [hR]; omega
  -- membership facts
  have hAG : ∀ x ∈ A, m + x ∈ G := by
    intro x hx
    simp only [hA, Finset.mem_filter, Finset.mem_range] at hx
    refine ⟨by omega, hx.2, ?_⟩
    rintro ⟨a, b, ha, hb, haS, hbS, hab⟩
    have := hmin a ha haS
    have := hmin b hb hbS
    omega
  have hB'G : ∀ y ∈ B', 2 * m + y ∈ G := by
    intro y hy
    simp only [hB', hB, Finset.mem_filter, Finset.mem_range] at hy
    obtain ⟨⟨hyM, hyS⟩, hyn⟩ := hy
    refine ⟨by omega, hyS, ?_⟩
    rintro ⟨a, b, ha, hb, haS, hbS, hab⟩
    have hma := hmin a ha haS
    have hmb := hmin b hb hbS
    apply hyn
    simp only [Finset.mem_image, Finset.mem_product, hA, Finset.mem_filter, Finset.mem_range]
    refine ⟨(a - m, b - m), ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, ?_⟩
    · rwa [Nat.add_sub_cancel' hma]
    · rwa [Nat.add_sub_cancel' hmb]
    · simp only [hf]; omega
  have hdec : ∀ x, c ≤ x → x < c + m → ∀ a b, m ≤ a → a < 2 * m → m ≤ b → b ∈ S → a ∈ S →
      x = a + b → x ∈ T.image (3 * m + ·) ∪ W.image (2 * m + ·) := by
    intro x hx1 hx2 a b ha1 ha2 hb1 hbS haS hab
    simp only [Finset.mem_union, Finset.mem_image]
    by_cases hb2 : b < 2 * m
    · right
      refine ⟨x - 2 * m, ?_, by omega⟩
      simp only [hW, Finset.mem_filter, Finset.mem_image, Finset.mem_product, hA,
        Finset.mem_range]
      refine ⟨⟨(a - m, b - m), ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, ?_⟩, by omega, by omega⟩
      · rwa [Nat.add_sub_cancel' ha1]
      · rwa [Nat.add_sub_cancel' hb1]
      · simp only [hf]; omega
    · left
      refine ⟨x - 3 * m, ?_, by omega⟩
      simp only [hT, Finset.mem_filter, Finset.mem_image, Finset.mem_product, hA, hB,
        Finset.mem_range]
      refine ⟨⟨(a - m, b - 2 * m), ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, ?_⟩, by omega⟩
      · rwa [Nat.add_sub_cancel' ha1]
      · rwa [Nat.add_sub_cancel' (by omega)]
      · simp only [hf]; omega
  have hRG : ∀ x ∈ R, x ∈ G := by
    intro x hx
    rw [hR, Finset.mem_sdiff, Finset.mem_Ico] at hx
    obtain ⟨⟨hx1, hx2⟩, hxn⟩ := hx
    refine ⟨by omega, hmem x hx1, ?_⟩
    rintro ⟨a, b, ha, hb, haS, hbS, hab⟩
    have hma := hmin a ha haS
    have hmb := hmin b hb hbS
    apply hxn
    by_cases ha2 : a < 2 * m
    · exact hdec x hx1 hx2 a b hma ha2 hmb hbS haS hab
    · exact hdec x hx1 hx2 b a hmb (by omega) hma haS hbS (by omega)
  have he : A.card + B'.card + (m - (T.card + W.card)) ≤ S.embeddingDim := by
    set F := A.image (m + ·) ∪ B'.image (2 * m + ·) ∪ R with hF
    have hsub : (F : Set ℕ) ⊆ G := by
      intro x hx
      simp only [hF, Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_image] at hx
      rcases hx with (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩) | hx
      · exact hAG y hy
      · exact hB'G y hy
      · exact hRG x hx
    have hcardF : A.card + B'.card + R.card ≤ F.card := by
      have hd1 : Disjoint (A.image (m + ·)) (B'.image (2 * m + ·)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_image] at hx1 hx2
        obtain ⟨y, hy, rfl⟩ := hx1
        obtain ⟨z, hz, hz2⟩ := hx2
        have := hAlt y hy
        omega
      have hd2 : Disjoint (A.image (m + ·) ∪ B'.image (2 * m + ·)) R := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [hR, Finset.mem_sdiff, Finset.mem_Ico] at hx2
        simp only [Finset.mem_union, Finset.mem_image] at hx1
        rcases hx1 with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
        · have := hAlt y hy; omega
        · have : y ∈ B := (Finset.mem_filter.mp hy).1
          have := hBlt y this; omega
      rw [hF, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
        Finset.card_image_of_injective _ (add_right_injective m),
        Finset.card_image_of_injective _ (add_right_injective (2 * m))]
    have := Set.ncard_le_ncard hsub hGfin
    rw [Set.ncard_coe_finset] at this
    unfold embeddingDim
    rw [← hG]
    omega
  rw [hn]
  -- arithmetic
  have ha1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨0, hA0⟩
  have hb1 : 1 ≤ B.card := by
    apply Finset.card_pos.mpr
    exact ⟨0, hAAB 0 hA0 0 hA0 (by omega)⟩
  rw [hcM]
  exact arith m M A.card B.card B'.card T.card W.card S.embeddingDim hMm ha1 hb1 K he


theorem keyThm : KeyProp := by
  intro m M hM hMm A B hA0 hA hB hAAB
  classical
  have hAlo0 : 0 ∈ A.filter (· < M) := Finset.mem_filter.mpr ⟨hA0, by omega⟩
  have hAloM : ∀ x ∈ A.filter (· < M), x < M := fun x hx => (Finset.mem_filter.mp hx).2
  have hcl : ∀ x ∈ A.filter (· < M), ∀ y ∈ A.filter (· < M), x + y < M → x + y ∈ B :=
    fun x hx y hy hxy => hAAB x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
  have hB'c : ∀ z ∈ B, z ∉ B.filter (fun y => y ∉ Finset.image (fun p : ℕ × ℕ => p.1 + p.2) (A ×ˢ A)) →
      ∃ x ∈ A.filter (· < M), ∃ y ∈ A.filter (· < M), x + y = z := by
    intro z hz hz'
    rw [Finset.mem_filter, not_and, not_not] at hz'
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp (hz' hz)
    rw [Finset.mem_product] at hxy
    have := hB _ hz
    simp only at this
    exact ⟨x, Finset.mem_filter.mpr ⟨hxy.1, by omega⟩, y, Finset.mem_filter.mpr ⟨hxy.2, by omega⟩, rfl⟩
  have hL1 := L1 M (A.filter (· < M)) B
    (B.filter (fun y => y ∉ Finset.image (fun p : ℕ × ℕ => p.1 + p.2) (A ×ˢ A)))
    hAlo0 hAloM hB hcl (Finset.filter_subset _ _) hB'c
  have hL2 := L2 m M hM hMm A B hA0 hA hB hAAB
  have hT : (Finset.image (fun p : ℕ × ℕ => p.1 + p.2) (A ×ˢ B)).filter (· < M)
      = (sums ((A.filter (· < M)) ×ˢ B)).filter (· < M) := by
    ext v
    simp only [Finset.mem_filter, mem_sums, Finset.mem_image, Finset.mem_product]
    constructor
    · rintro ⟨⟨p, ⟨h1, h2⟩, h3⟩, h4⟩
      exact ⟨⟨p, ⟨⟨h1, by omega⟩, h2⟩, h3⟩, h4⟩
    · rintro ⟨⟨p, ⟨⟨h1, _⟩, h2⟩, h3⟩, h4⟩
      exact ⟨⟨p, ⟨h1, h2⟩, h3⟩, h4⟩
  have hK : (A.filter (· < M)).filter (fun x => 0 < x ∧ M ≤ 3 * x)
      = ((A.filter (· < M)).erase 0).filter (fun x => M ≤ 3 * x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨by omega, h1⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h2, by omega, h3⟩
  have ha : A.card = (A.filter (· < M)).card + (A.filter (M ≤ ·)).card := by
    have := Finset.card_filter_add_card_filter_not (s := A) (fun x => x < M)
    have hneg : A.filter (fun x => ¬ (x < M)) = A.filter (M ≤ ·) := by
      apply Finset.filter_congr
      intro x _
      exact not_lt
    rw [hneg] at this
    omega
  rw [hT]
  rw [hK] at hL2
  rw [ha] at hL2 ⊢
  nlinarith

end OMA.WilfH1

theorem OMA.solution :
    OMA.R_WilfNumericalSemigroupConjecture_wilf_numerical_semigroup_conjecture_R1.H1 :=
  OMA.WilfH1.trans OMA.WilfH1.keyThm
