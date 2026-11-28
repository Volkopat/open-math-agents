import FormalConjectures.ErdosProblems.«652»

open Real Finset

open scoped EuclideanGeometry

theorem OMA.solution : type_of% @Erdos652.erdos_652.variants.first := by
  let : DecidableEq ℝ² := Classical.decEq _
  intro n hn
  have hnR : (0 : ℝ) < n := by positivity
  let t (i : Fin (n - 1)) : ℝ := i / n
  let p (i : Fin (n - 1)) : ℝ² := WithLp.toLp 2 ![t i, √(1 - t i ^ 2)]
  have hi : Function.Injective p := fun i j h => Fin.ext <| by
    exact_mod_cast (div_left_inj' hnR.ne').1 (congrArg (· 0) h)
  let s := univ.map ⟨p, hi⟩
  have hd : ∀ x ∈ s, dist x 0 = 1 := by
    simp only [s, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk, forall_exists_index]
    rintro _ i rfl
    have ht : t i ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast i.2.le.trans (by omega)) hnR.le
    rw [dist_zero_right, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, p, sq_sqrt (sub_nonneg.2 (pow_le_one₀ (by positivity) ht))]
  have hz : (0 : ℝ²) ∉ s := fun h => by simpa using hd 0 h
  refine ⟨insert 0 s, by rw [card_insert_of_notMem hz]; simp [s]; omega, 0, mem_insert_self _ _, ?_⟩
  rw [distinctDistancesFrom, erase_insert hz, image_congr hd, image_const (card_pos.1 (by simp [s]; omega))]
  simp
