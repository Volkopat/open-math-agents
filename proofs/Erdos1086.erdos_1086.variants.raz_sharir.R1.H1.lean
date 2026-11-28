import OMAReductions.R_Erdos1086_erdos_1086_variants_raz_sharir_R1
import Mathlib.Tactic

-- Step Erdos1086.erdos_1086.variants.raz_sharir.R1.H1: hypothesis H1 of reduction Erdos1086.erdos_1086.variants.raz_sharir.R1
-- Credit: @RiverMint78

open Finset EuclideanGeometry Filter
open scoped EuclideanGeometry

-- Each new set overlaps the earlier union in at most one point per earlier set.
private lemma sum_card_le_card_biUnion_add_sq {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → Finset β)
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (f a ∩ f b).card ≤ 1) :
    (∑ a ∈ s, (f a).card) ≤ (s.biUnion f).card + s.card ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hi : f a ∩ s.biUnion f = s.biUnion (fun b => f a ∩ f b) := by
      ext x
      simp only [mem_inter, mem_biUnion]
      aesop
    have hcard : (f a ∩ s.biUnion f).card ≤ s.card := by
      rw [hi]
      calc
        _ ≤ ∑ b ∈ s, (f a ∩ f b).card := card_biUnion_le
        _ ≤ ∑ _ ∈ s, 1 := sum_le_sum fun b hb =>
          h a (mem_insert_self a s) b (mem_insert_of_mem hb) (fun e => ha (e ▸ hb))
        _ = s.card := by simp
    have hind := ih (fun x hx y hy hxy => h x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hxy)
    have hcnt := card_union_add_card_inter (f a) (s.biUnion f)
    rw [sum_insert ha, biUnion_insert, card_insert_of_notMem ha]
    nlinarith

-- A family of m rich sets would already require at least m² points.
private lemma rich_cover_sum {α β : Type*} [DecidableEq β] (s : Finset α)
    (f : α → Finset β) (P : Finset β) (m : ℕ) (hsmall : P.card < m ^ 2)
    (hsub : ∀ a ∈ s, f a ⊆ P) (hrich : ∀ a ∈ s, 2 * m ≤ (f a).card)
    (hpair : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (f a ∩ f b).card ≤ 1) :
    (∑ a ∈ s, (f a).card) ≤ 2 * P.card := by
  classical
  have est (t : Finset α) (ht : t ⊆ s) :
      2 * m * t.card ≤ (∑ a ∈ t, (f a).card) ∧
      (∑ a ∈ t, (f a).card) ≤ P.card + t.card ^ 2 := by
    constructor
    · simpa [mul_comm] using (sum_le_sum (s := t) fun a ha => hrich a (ht ha))
    · have hc : (t.biUnion f).card ≤ P.card :=
        card_le_card (fun _ hx => by
          obtain ⟨a, ha, hx⟩ := mem_biUnion.mp hx
          exact hsub a (ht ha) hx)
      exact (sum_card_le_card_biUnion_add_sq t f fun a ha b hb => hpair a (ht ha) b (ht hb)).trans
        (Nat.add_le_add_right hc _)
  have ht : s.card < m := by
    by_contra! h
    obtain ⟨t, hts, ht⟩ := exists_subset_card_eq h
    obtain ⟨hlo, hhi⟩ := est t hts
    rw [ht] at hlo hhi
    nlinarith
  obtain ⟨hlo, hhi⟩ := est s (Subset.refl s)
  have hsq := Nat.mul_le_mul_left s.card ht.le
  nlinarith

private lemma area_on_line_map (a b r : ℝ²) (s t : ℝ) :
    triangle_area (AffineMap.lineMap a b s) (AffineMap.lineMap a b t) r =
    (t - s) * triangle_area a b r := by
  simp [triangle_area_eq_det, Matrix.det_fin_three, AffineMap.lineMap_apply_module',
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private lemma area_inj_on_line {a b p r q q' : ℝ²}
    (hp : p ∈ affineSpan ℝ ({a, b} : Set ℝ²))
    (hq : q ∈ affineSpan ℝ ({a, b} : Set ℝ²))
    (hq' : q' ∈ affineSpan ℝ ({a, b} : Set ℝ²))
    (h : triangle_area p q r = triangle_area p q' r)
    (hn : triangle_area p q r ≠ 0) : q = q' := by
  obtain ⟨s, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hp
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hq
  obtain ⟨t', rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hq'
  rw [area_on_line_map, area_on_line_map] at h
  rw [area_on_line_map] at hn
  have nz : triangle_area a b r ≠ 0 := (mul_ne_zero_iff.mp hn).2
  exact congrArg (AffineMap.lineMap a b) (sub_left_inj.mp (mul_right_cancel₀ nz h))

private lemma area_abs_of_triple_eq {a b c p q r : ℝ²}
    (h : ({a, b, c} : Finset ℝ²) = {p, q, r})
    (hcard : ({p, q, r} : Finset ℝ²).card = 3) :
    |triangle_area a b c| = |triangle_area p q r| := by
  classical
  have hs : ({a, b, c} : Finset ℝ²).card = 3 := h ▸ hcard
  have pair_le (x y : ℝ²) : ({x, y} : Finset ℝ²).card ≤ 2 :=
    (Finset.card_insert_le x {y}).trans (by simp)
  have hab : a ≠ b := by
    intro e
    subst b
    rw [Finset.insert_idem] at hs
    have := pair_le a c
    omega
  have hac : a ≠ c := by
    intro e
    subst c
    rw [Finset.insert_comm a b ({a} : Finset ℝ²),
      show (insert a {a} : Finset ℝ²) = {a} by simp] at hs
    have := pair_le b a
    omega
  have hbc : b ≠ c := by
    intro e
    subst c
    rw [show (insert b {b} : Finset ℝ²) = {b} by simp] at hs
    have := pair_le a b
    omega
  have left_mem (x : ℝ²) (hx : x ∈ ({a, b, c} : Finset ℝ²)) :
      x = p ∨ x = q ∨ x = r := by
    rw [h] at hx
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
  have ha := left_mem a (by simp)
  have hb := left_mem b (by simp)
  have hc := left_mem c (by simp)
  rcases ha with e | e | e <;> subst a <;>
    rcases hb with e | e | e <;> subst b <;>
    rcases hc with e | e | e <;> subst c <;>
    try contradiction
  all_goals
    rw [← sq_eq_sq_iff_abs_eq_abs] <;>
      simp [triangle_area_eq_det, Matrix.det_fin_three] <;> ring

private noncomputable def spanLine (u v : ℝ²) : AffineSubspace ℝ ℝ² := affineSpan ℝ ({u, v} : Set ℝ²)

private lemma count_partners (u v p r : ℝ²) (S : Finset ℝ²)
    (hp : p ∈ spanLine u v) (hS : ∀ q ∈ S, q ∈ spanLine u v) :
    (S.filter (fun q => |triangle_area p q r| = 1)).card ≤ 2 := by
  classical
  let B := S.filter (fun q => |triangle_area p q r| = 1)
  calc
    B.card ≤ ({(1 : ℝ), -1} : Finset ℝ).card := by
      apply card_le_card_of_injOn (fun q => triangle_area p q r)
      · intro q hq
        have ha := (mem_filter.mp hq).2
        simpa using (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp ha
      · intro q hq q' hq' heq
        obtain ⟨hqS, hqA⟩ := mem_filter.mp hq
        exact area_inj_on_line hp (hS q hqS) (hS q' (mem_filter.mp hq').1) heq
          (fun hz => by simp [hz] at hqA)
    _ ≤ 2 := card_le_two

open scoped Classical in
private lemma rich_triangles_le {P : Finset ℝ²} (m : ℕ) (hsmall : P.card < m ^ 2)
    (hm : (2 * m : ℝ) ≤ (P.card : ℝ) ^ (5 / 9 : ℝ)) :
    ((P.powersetCard 3).filter fun T =>
      (∃ p q r : ℝ², T = {p, q, r} ∧ |triangle_area p q r| = 1) ∧
      (∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧
        ((P.card : ℝ) ^ (5 / 9 : ℝ)) ≤
          ((P.filter fun w => w ∈ affineSpan ℝ ({u, v} : Set ℝ²)).card : ℝ))).card ≤
    4 * P.card ^ 2 := by
  classical
  let pts (l : AffineSubspace ℝ ℝ²) := P.filter fun w => w ∈ l
  let lines := (P.offDiag.image (fun uv => spanLine uv.1 uv.2)).filter
    (fun l => (P.card : ℝ) ^ (5 / 9 : ℝ) ≤ ((pts l).card : ℝ))
  let choices (l : AffineSubspace ℝ ℝ²) (pr : ℝ² × ℝ²) : Finset (Finset ℝ²) :=
    ((pts l).filter fun q => |triangle_area pr.1 q pr.2| = 1).image
      (fun q => {pr.1, q, pr.2})
  -- An apex and a base vertex leave at most two partners on a fixed line.
  let cover (l : AffineSubspace ℝ ℝ²) := ((pts l) ×ˢ P).biUnion (choices l)
  have hline (l : AffineSubspace ℝ ℝ²) (hl : l ∈ lines) : ∃ u v, l = spanLine u v := by
    obtain ⟨⟨u,v⟩, _, h⟩ := mem_image.mp (mem_filter.mp hl).1
    exact ⟨u, v, h.symm⟩
  have hpts (l : AffineSubspace ℝ ℝ²) : pts l ⊆ P := filter_subset _ _
  have hpts_line {l : AffineSubspace ℝ ℝ²} {p : ℝ²} (hp : p ∈ pts l) : p ∈ l :=
    (mem_filter.mp hp).2
  have hcount : (∑ l ∈ lines, (pts l).card) ≤ 2 * P.card := by
    apply rich_cover_sum lines pts P m hsmall (fun l _ => hpts l)
    · intro l hl
      exact_mod_cast hm.trans (mem_filter.mp hl).2
    · intro l hl l' hl' hne
      apply card_le_one_iff.mpr
      intro p p' hp hp'
      by_contra hpp'
      obtain ⟨u, v, rfl⟩ := hline l hl
      obtain ⟨u', v', rfl⟩ := hline l' hl'
      obtain ⟨hp1, hp2⟩ := mem_inter.mp hp
      obtain ⟨hp1', hp2'⟩ := mem_inter.mp hp'
      exact hne ((affineSpan_pair_eq_of_mem_of_mem_of_ne (hpts_line hp1) (hpts_line hp1') hpp').symm.trans
        (affineSpan_pair_eq_of_mem_of_mem_of_ne (hpts_line hp2) (hpts_line hp2') hpp'))
  have hcover_size (l : AffineSubspace ℝ ℝ²) (hl : l ∈ lines) :
      (cover l).card ≤ (2 * P.card) * (pts l).card := by
    calc
      _ ≤ ∑ pr ∈ (pts l) ×ˢ P, (choices l pr).card := card_biUnion_le
      _ ≤ ∑ _ ∈ (pts l) ×ˢ P, 2 := by
        apply sum_le_sum
        intro pr hpr
        obtain ⟨u, v, rfl⟩ := hline l hl
        exact card_image_le.trans (count_partners u v pr.1 pr.2 (pts (spanLine u v))
          (hpts_line (mem_product.mp hpr).1) (fun _ => hpts_line))
      _ = _ := by simp [card_product, mul_assoc, mul_comm]
  calc
    _ ≤ (lines.biUnion cover).card := by
      apply card_le_card
      intro T hT
      obtain ⟨hT0, ⟨a,b,c,hT1,hA⟩, ⟨u,hu,v,hv,huv,hrich⟩⟩ := mem_filter.mp hT
      obtain ⟨hTP,hcard⟩ := mem_powersetCard.mp hT0
      let l := spanLine u v
      have hl : l ∈ lines := mem_filter.mpr ⟨mem_image.mpr
        ⟨(u,v), mem_offDiag.mpr ⟨hTP hu, hTP hv, huv⟩, rfl⟩, hrich⟩
      have hthird : (T \ {u,v}).Nonempty := by
        by_contra! hempty
        have hsub : T ⊆ {u,v} := sdiff_eq_empty_iff_subset.mp hempty
        have hbad := card_le_card hsub
        simp [hcard, huv] at hbad
      obtain ⟨r, hrT⟩ := hthird
      obtain ⟨hr, hruv⟩ := mem_sdiff.mp hrT
      have hru : r ≠ u := fun h => hruv (by simp [h])
      have hrv : r ≠ v := fun h => hruv (by simp [h])
      have hTr : T = {u,v,r} := by
        symm
        apply eq_of_subset_of_card_le
        · simp [insert_subset, hu, hv, hr]
        · simp [hcard, huv, hru.symm, hrv.symm]
      have hArea : |triangle_area u v r| = 1 := by
        rw [← area_abs_of_triple_eq (hT1.symm.trans hTr) (hTr ▸ hcard)]
        exact hA
      have hpu : u ∈ pts l := mem_filter.mpr ⟨hTP hu, left_mem_affineSpan_pair ℝ u v⟩
      have hpv : v ∈ pts l := mem_filter.mpr ⟨hTP hv, right_mem_affineSpan_pair ℝ u v⟩
      exact mem_biUnion.mpr ⟨l, hl, mem_biUnion.mpr ⟨(u,r), mem_product.mpr ⟨hpu,hTP hr⟩,
        mem_image.mpr ⟨v, mem_filter.mpr ⟨hpv,hArea⟩, hTr.symm⟩⟩⟩
    _ ≤ ∑ l ∈ lines, (cover l).card := card_biUnion_le
    _ ≤ ∑ l ∈ lines, (2 * P.card) * (pts l).card := sum_le_sum hcover_size
    _ = (2 * P.card) * (∑ l ∈ lines, (pts l).card) := by rw [mul_sum]
    _ ≤ (2 * P.card) * (2 * P.card) := Nat.mul_le_mul_left _ hcount
    _ = 4 * P.card ^ 2 := by ring

set_option maxHeartbeats 500000 in
theorem OMA.solution : OMA.R_Erdos1086_erdos_1086_variants_raz_sharir_R1.H1 := by
  classical
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 18 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨(N : ℝ) + 4, by positivity, ?_⟩
  intro P
  let T := (P.powersetCard 3).filter fun T =>
    (∃ p q r : ℝ², T = {p, q, r} ∧ |triangle_area p q r| = 1) ∧
    (∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧
      ((P.card : ℝ) ^ (5 / 9 : ℝ)) ≤
        ((P.filter fun w => w ∈ affineSpan ℝ ({u, v} : Set ℝ²)).card : ℝ))
  change (T.card : ℝ) ≤ ((N : ℝ) + 4) * (P.card : ℝ) ^ (20 / 9 : ℝ)
  by_cases hzero : P.card = 0
  · have hT : T.card = 0 := card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr (fun t ht => by
      have hs := (mem_powersetCard.mp (mem_filter.mp ht).1)
      have hb := card_le_card hs.1
      omega))
    simp only [hT, Nat.cast_zero]
    positivity
  have hn : 1 ≤ (P.card : ℝ) := by exact_mod_cast (show 1 ≤ P.card by omega)
  have hpow : (P.card : ℝ)^2 ≤ (P.card : ℝ) ^ (20 / 9 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  by_cases hlarge : N ≤ P.card
  · let m := P.card.sqrt + 1
    have hsmall : P.card < m ^ 2 := Nat.lt_succ_sqrt' _
    have hsqrt : (P.card.sqrt : ℝ) ≤ Real.sqrt (P.card : ℝ) := by
      apply Real.le_sqrt_of_sq_le
      exact_mod_cast Nat.sqrt_le' P.card
    have hsqrt_one : 1 ≤ Real.sqrt (P.card : ℝ) := by
      simpa using Real.sqrt_le_sqrt hn
    have hm : (2 * m : ℝ) ≤ (P.card : ℝ) ^ (5 / 9 : ℝ) := by
      calc
        _ ≤ 4 * Real.sqrt (P.card : ℝ) := by dsimp [m]; push_cast; linarith
        _ ≤ (P.card : ℝ) ^ (1 / 18 : ℝ) * Real.sqrt (P.card : ℝ) :=
          mul_le_mul_of_nonneg_right (hN _ hlarge) (Real.sqrt_nonneg _)
        _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]; norm_num
    have hbound : T.card ≤ 4 * P.card ^ 2 := rich_triangles_le m hsmall hm
    calc
      _ ≤ 4 * (P.card : ℝ) ^ 2 := by exact_mod_cast hbound
      _ ≤ ((N : ℝ) + 4) * (P.card : ℝ) ^ (20 / 9 : ℝ) := by
        exact mul_le_mul (le_add_of_nonneg_left (Nat.cast_nonneg N)) hpow (sq_nonneg _) (by positivity)
  · have hbound : T.card ≤ P.card ^ 3 := by
      calc
        _ ≤ (P.powersetCard 3).card := card_filter_le _ _
        _ = P.card.choose 3 := card_powersetCard _ _
        _ ≤ _ := Nat.choose_le_pow _ _
    have hsmall : (P.card : ℝ) ≤ N := by exact_mod_cast (show P.card ≤ N by omega)
    calc
      _ ≤ (P.card : ℝ) ^ 3 := by exact_mod_cast hbound
      _ ≤ (N : ℝ) * (P.card : ℝ) ^ 2 := by
        rw [pow_succ, mul_comm ((P.card : ℝ) ^ 2)]
        exact mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ ≤ ((N : ℝ) + 4) * (P.card : ℝ) ^ (20 / 9 : ℝ) := by
        exact mul_le_mul (le_add_of_nonneg_right (by norm_num)) hpow (sq_nonneg _) (by positivity)
