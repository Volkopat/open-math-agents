import FormalConjectures.ErdosProblems.«652»

/-! Elekes's construction on an axis and concentric circles. -/

open scoped EuclideanGeometry
open Finset Filter Erdos652

theorem OMA.solution : type_of% @Erdos652.erdos_652.variants.elekes := by
  classical
  intro k
  refine ⟨5 * (k : ℝ) + 3, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max k 1)] with n hn
  have hkn : k ≤ n := (le_max_left ..).trans hn
  have h1 : 1 ≤ n := (le_max_right ..).trans hn
  let m := n.sqrt + 1
  let anc (h : ℕ) : ℝ² := WithLp.toLp 2 ![(h : ℝ), 0]
  let grd (p : Fin m × Fin m) : ℝ² :=
    WithLp.toLp 2 ![-(p.1.1 : ℝ), Real.sqrt ((m : ℝ) ^ 2 + p.2.1 - (p.1.1 : ℝ) ^ 2)]
  have hnn (p : Fin m × Fin m) : 0 ≤ (m : ℝ) ^ 2 + p.2.1 - (p.1.1 : ℝ) ^ 2 := by
    have : (p.1.1 : ℝ) ≤ m := by exact_mod_cast p.1.2.le
    nlinarith [Nat.cast_nonneg (α := ℝ) p.1.1, Nat.cast_nonneg (α := ℝ) p.2.1]
  have hai : Function.Injective anc := fun a b h => by
    exact_mod_cast (by simpa [anc] using congrArg (· 0) h : (a : ℝ) = b)
  have hgi : Function.Injective grd := fun p q h => by
    have h1 := congrArg (· 0) h; simp [grd] at h1
    have hx : p.1 = q.1 := Fin.ext (by exact_mod_cast h1)
    have h2 := congrArg (fun z : ℝ² => (z 1) ^ 2) h
    change (Real.sqrt _) ^ 2 = (Real.sqrt _) ^ 2 at h2
    rw [Real.sq_sqrt (hnn p), Real.sq_sqrt (hnn q), hx] at h2
    exact Prod.ext hx (Fin.ext (by exact_mod_cast (show (p.2.1 : ℝ) = q.2.1 by linarith)))
  let A := (range k).image anc
  let B := univ.image grd
  have ha : A.card = k := by simp [A, card_image_of_injective _ hai]
  have hb : B.card = m * m := by simp [B, card_image_of_injective _ hgi]
  obtain ⟨pts, hA, hpts, hcard⟩ := exists_subsuperset_card_eq
    (subset_union_left : A ⊆ A ∪ B) (ha ▸ hkn)
    ((Nat.sqrt_lt.mp (show n.sqrt < m by omega)).le.trans (hb ▸ card_le_card subset_union_right))
  have hs : (n.sqrt : ℝ) * n.sqrt ≤ n := by exact_mod_cast Nat.sqrt_le n
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n)
  have hh : (n.sqrt : ℝ) ≤ Real.sqrt n := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hr : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast h1)
  have hm : (m : ℝ) ≤ 2 * Real.sqrt n := by dsimp [m]; push_cast; linarith
  refine ⟨pts, hcard, ha.ge.trans (card_le_card fun x hx => ?_)⟩
  obtain ⟨h, hh', rfl⟩ := mem_image.mp hx
  have hhk := mem_range.mp hh'
  refine mem_filter.2 ⟨hA (mem_image_of_mem _ hh'), ?_⟩
  let D := (range ((2 * k + 1) * m)).image fun j : ℕ => Real.sqrt ((m : ℝ) ^ 2 + (h : ℝ) ^ 2 + j)
  have hsub : ((pts.erase (anc h)).image (dist · (anc h))) ⊆ (A.image (dist · (anc h))) ∪ D := by
    rintro _ hy; obtain ⟨y, hypts, rfl⟩ := mem_image.mp hy
    rcases mem_union.mp (hpts (mem_of_mem_erase hypts)) with ha' | hb'
    · exact mem_union_left _ (mem_image_of_mem _ ha')
    · obtain ⟨p, _, rfl⟩ := mem_image.mp hb'
      refine mem_union_right _ (mem_image.2 ⟨p.2.1 + 2 * h * p.1.1, mem_range.2 ?_, ?_⟩)
      · have := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hhk.le) p.1.2.le; nlinarith [p.2.2]
      · rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]; congr 1
        simp only [Real.dist_eq, sq_abs]
        change _ = (-(p.1.1 : ℝ) - h) ^ 2 + (Real.sqrt _ - 0) ^ 2
        rw [sub_zero, Real.sq_sqrt (hnn p)]; push_cast; ring
  have hdd : distinctDistancesFrom pts (anc h) ≤ k + (2 * k + 1) * m := by
    have deq : distinctDistancesFrom pts (anc h) = ((pts.erase (anc h)).image (dist · (anc h))).card := by
      unfold distinctDistancesFrom; congr 1; ext d; simp [mem_erase]
    rw [deq]
    exact (card_le_card hsub).trans ((card_union_le ..).trans <|
      Nat.add_le_add (card_image_le.trans ha.le) (card_image_le.trans (card_range _).le))
  have hddR : (distinctDistancesFrom pts (anc h) : ℝ) ≤ k + (2 * (k : ℝ) + 1) * m := by exact_mod_cast hdd
  nlinarith [mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * (k : ℝ) + 1),
    mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) k)]
