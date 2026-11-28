import FormalConjectures.ErdosProblems.«652»

open Finset
open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos652.erdos_652.variants.product := by
  classical
  let : DecidableEq ℝ² := Classical.decEq _
  let : DecidableEq ℝ := Classical.decEq _
  refine ⟨1 / 4, by norm_num, fun P p hp q hq hpq => ?_⟩
  let R := (P.erase p).erase q
  let Dp := (P.erase p).image (dist · p)
  let Dq := (P.erase q).image (dist · q)
  let f (x : ℝ²) := (dist x p, dist x q)
  have hp' : p ∈ P.erase q := mem_erase.2 ⟨hpq, hp⟩
  have hq' : q ∈ P.erase p := mem_erase.2 ⟨hpq.symm, hq⟩
  have hcnt := card_le_mul_card_image_of_maps_to (s := R) (t := Dp ×ˢ Dq) (f := f)
    (fun x hx => by
      obtain ⟨hxq, hxp⟩ := mem_erase.1 hx
      exact mk_mem_product (mem_image_of_mem _ hxp)
        (mem_image_of_mem _ (mem_erase.2 ⟨hxq, (mem_erase.1 hxp).2⟩)))
    2 fun d _ => by
      let F := R.filter (f · = d)
      by_cases h1 : F.card ≤ 1
      · dsimp [F] at h1; omega
      obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (by omega : 1 < F.card)
      have ha' := (mem_filter.1 ha).2; have hb' := (mem_filter.1 hb).2
      refine (card_le_card (s := F) (t := {a, b}) fun x hx => ?_).trans card_le_two
      have hx' := (mem_filter.1 hx).2
      obtain h | h := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
        finrank_euclideanSpace_fin hpq hab (congrArg Prod.fst ha') (congrArg Prod.fst hb')
        (congrArg Prod.fst hx') (congrArg Prod.snd ha') (congrArg Prod.snd hb')
        (congrArg Prod.snd hx') <;> simp [h]
  rw [card_product, card_erase_of_mem hq', card_erase_of_mem hp] at hcnt
  have : 1 < P.card := one_lt_card.2 ⟨p, hp, q, hq, hpq⟩
  have : 0 < Dp.card := card_pos.2 ⟨_, mem_image_of_mem _ hq'⟩
  have : 0 < Dq.card := card_pos.2 ⟨_, mem_image_of_mem _ hp'⟩
  have : 0 < Dp.card * Dq.card := Nat.mul_pos ‹_› ‹_›
  have hR : (P.card : ℝ) ≤ 4 * (Dp.card * Dq.card : ℝ) := by
    exact_mod_cast (show P.card ≤ 4 * (Dp.card * Dq.card) by omega)
  change (1 / 4 : ℝ) * P.card ≤ Dp.card * Dq.card; linarith
