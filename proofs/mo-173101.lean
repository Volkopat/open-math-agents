import OMAStatements.S_mo_173101
import Mathlib

open Set Finset OMA.S_mo_173101

private theorem continuousCap {k : ℕ} (j : Option (Fin k)) :
    Continuous (fun x : Space k => cap x j) := by
  cases j with
  | none => exact continuous_const.sub (continuous_finset_sum _ fun i _ => continuous_apply i)
  | some i => exact continuous_apply i

private theorem capCombination {k : ℕ} (x y : Space k) (a b : ℝ) (h : a+b = 1)
    (j : Option (Fin k)) : cap (a • x + b • y) j = a * cap x j + b * cap y j := by
  cases j with
  | some i => rfl
  | none =>
    simp only [cap, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [congrArg (fun t : ℝ => t * (k : ℝ)) h]

private theorem cubeFibers (k : ℕ) : fibers (cube k) intervals := by
  intro z j
  by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
  · have he : {x | x ∈ cube k ∧ z ∈ intervals x j} =
        cube k ∩ {x : Space k | z ≤ cap x j} := by
      ext x
      simp [intervals, le_min_iff, hz.1, hz.2]
    rw [he]
    refine ⟨isCompact_Icc.inter_right (isClosed_le continuous_const (continuousCap j)), ?_⟩
    apply (convex_Icc (𝕜 := ℝ) _ _).inter
    intro x hx y hy a b ha hb hab
    change z ≤ cap (a • x + b • y) j
    rw [capCombination x y a b hab]
    calc
      z = a*z+b*z := by rw [← add_mul, hab, one_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
  · have he : {x | x ∈ cube k ∧ z ∈ intervals x j} = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr ?_
      rintro x ⟨_, hz'⟩
      exact hz ⟨hz'.1, hz'.2.trans (min_le_left _ _)⟩
    rw [he]
    exact ⟨isCompact_empty, convex_empty⟩

private theorem oneInTests (k : ℕ) : (1 : ℝ) ∈ tests (cube k) intervals k := by
  classical
  intro J hJ
  have hcard : J.card < Fintype.card (Option (Fin k)) := by
    simpa [Fintype.card_option] using Nat.lt_succ_of_le hJ
  obtain ⟨j, hj⟩ : ∃ j, j ∉ J := by
    by_contra! hall
    have hsub : (Finset.univ : Finset (Option (Fin k))) ⊆ J := fun j _ => hall j
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    exact (not_le_of_gt hcard) hle
  cases j with
  | none =>
    refine ⟨fun _ => 1, ⟨by intro i; norm_num, le_rfl⟩, ?_⟩
    intro j hmem
    cases j with
    | none => exact (hj hmem).elim
    | some i => norm_num [intervals, cap]
  | some i =>
    let x : Space k := fun j => if j = i then 0 else 1
    have hx : x ∈ cube k := by
      constructor <;> intro j <;> by_cases h : j = i <;> simp [x, h]
    have hs : (∑ j, x j) = (k : ℝ) - 1 := by
      rw [show x = fun j => 1 - (if j = i then (1 : ℝ) else 0) from by
        funext j
        by_cases h : j = i <;> simp [x, h]]
      rw [Finset.sum_sub_distrib]
      simp
    refine ⟨x, hx, ?_⟩
    intro j hmem
    cases j with
    | none =>
      have hcap : cap x none = 1 := by simp only [cap, hs]; ring
      simp [intervals, hcap]
    | some j =>
      have hji : j ≠ i := by rintro rfl; exact hj hmem
      simp [intervals, cap, x, hji]

theorem OMA.solution : type_of% @OMA.S_mo_173101.main := by
  classical
  constructor
  · intro k Y Z _ X R hF
    have hct : common X R ⊆ tests X R (k + 1) := by
      rintro z ⟨x, hx, hmem⟩ J _
      exact ⟨x, hx, fun y _ => hmem y⟩
    have htc : tests X R (k + 1) ⊆ common X R := by
      intro z hz
      let F : Y → Set (Space k) := fun y => {x | x ∈ X ∧ z ∈ R x y}
      have inter : (⋂ y, F y).Nonempty := by
        refine Convex.helly_theorem_compact' (𝕜 := ℝ) (fun y => (hF z y).2) (fun y => (hF z y).1) ?_
        intro J hJ
        have hJ' : J.card ≤ k + 1 := by simpa [Module.finrank_pi] using hJ
        obtain ⟨x, hx, hmem⟩ := hz J hJ'
        refine ⟨x, ?_⟩
        simp only [Set.mem_iInter]
        exact fun j hj => ⟨hx, hmem j hj⟩
      obtain ⟨x, hx⟩ := inter
      have hall (y : Y) : x ∈ F y := Set.mem_iInter.mp hx y
      exact ⟨x, (hall (Classical.choice ‹Nonempty Y›)).1, fun y => (hall y).2⟩
    have eq := subset_antisymm hct htc
    have hcs : common X R ⊆ separate X R := by
      rintro z ⟨x, hx, hmem⟩ y
      exact ⟨x, hx, hmem y⟩
    exact ⟨eq, ⟨fun h => h.symm ▸ hct, fun hs => subset_antisymm hcs (hs.trans htc)⟩⟩
  · intro k _
    refine ⟨cubeFibers k, fun j => continuous_const.min (continuousCap j), ?_, oneInTests k, ?_⟩
    · intro x hx j
      have hcap : 0 ≤ cap x j := by
        cases j with
        | some i => exact hx.1 i
        | none =>
          apply sub_nonneg.mpr
          calc
            (∑ i, x i) ≤ ∑ _ : Fin k, (1 : ℝ) := sum_le_sum (fun i _ => hx.2 i)
            _ = k := by simp
      exact ⟨⟨le_rfl, le_min zero_le_one hcap⟩, fun _ ht => ⟨ht.1, ht.2.trans (min_le_left _ _)⟩⟩
    · rintro ⟨x, hx, htest⟩
      have hx1 : x = fun _ => 1 := by
        funext i
        exact le_antisymm (hx.2 i) ((htest (some i)).2.trans (min_le_right _ _))
      have hnone : (1 : ℝ) ≤ cap x none := (htest none).2.trans (min_le_right _ _)
      rw [hx1] at hnone
      have hc : cap (fun (_ : Fin k) => (1 : ℝ)) none = 0 := by simp [cap]
      rw [hc] at hnone
      norm_num at hnone