import OMAStatements.S_oeis_a250364

/-!
# Direct proof of OEIS A250364 (Colin Barker conjectures)

We count arrays `y : Fin 6 → Fin (n + 1)` failing `AtMostThrice` by partitioning them according to
the unique value `v` attained at least 4 times and its fiber `S = {j | value y j = v}`. Since
`|Fin 6| = 6 < 4 + 4`, at most one value can appear 4 or more times in any array, making these
fibers pairwise disjoint. Summing over `S` for each fixed `v` depends only on the cardinality
`k = |{j : Fin 6 | j + 1 ≤ v ≤ j + 1 + n}|`, yielding `a 1 = 64`, `a 2 = 729`, `a 3 = 4048`, and
the exact degree-6 polynomial `a n = n^6 + 6*n^5 + 15*n^4 + 5*n^3 + 57*n^2 + 13*n + 1` for all
`n ≥ 4`. Both the generating-function product identity and the 7th-order recurrence for `n > 10`
follow immediately.
-/

namespace OMA.A250364Proof

open PowerSeries OMA.S_oeis_a250364

private def activeSet (n v : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun j : Fin 6 => j.val + 1 ≤ v ∧ v ≤ j.val + 1 + n

private def coordSet (n : ℕ) (S : Finset (Fin 6)) (v : ℕ) (j : Fin 6) : Finset (Fin (n + 1)) :=
  Finset.univ.filter fun x : Fin (n + 1) => j.val + 1 + x.val = v ↔ j ∈ S

private def coordCount (n : ℕ) (S : Finset (Fin 6)) (v : ℕ) (j : Fin 6) : ℕ :=
  if j ∈ S then
    if j ∈ activeSet n v then 1 else 0
  else
    if j ∈ activeSet n v then n else n + 1

private def fiber (n : ℕ) (S : Finset (Fin 6)) (v : ℕ) : Finset (Fin 6 → Fin (n + 1)) :=
  Finset.univ.filter fun y => ∀ j : Fin 6, value y j = v ↔ j ∈ S

private def heavySubsets : Finset (Finset (Fin 6)) :=
  Finset.univ.filter fun S : Finset (Fin 6) => 4 ≤ S.card

private def badArrays (n : ℕ) : Finset (Fin 6 → Fin (n + 1)) :=
  Finset.univ.filter fun y => ¬ AtMostThrice y

private def g (n k : ℕ) : ℕ :=
  match k with
  | 4 => (n + 1) ^ 2
  | 5 => (5 * n + 1) * (n + 1)
  | 6 => 15 * n ^ 2 + 6 * n + 1
  | _ => 0

private def poly (n : ℕ) : ℕ :=
  n ^ 6 + 6 * n ^ 5 + 15 * n ^ 4 + 5 * n ^ 3 + 57 * n ^ 2 + 13 * n + 1

private lemma card_a_add_badArrays (n : ℕ) :
    a n + (badArrays n).card = (n + 1) ^ 6 := by
  unfold a badArrays
  rw [← Finset.card_union_of_disjoint]
  · have hunion :
        (Finset.univ.filter fun y : Fin 6 → Fin (n + 1) => AtMostThrice y) ∪
          (Finset.univ.filter fun y : Fin 6 → Fin (n + 1) => ¬ AtMostThrice y) =
          Finset.univ := by
      ext y
      simp [em]
    rw [hunion]
    simp [Fintype.card_fin]
  · rw [Finset.disjoint_left]
    intro y h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 h1

private lemma card_coordSet (n : ℕ) (S : Finset (Fin 6)) (v : ℕ) (j : Fin 6) :
    (coordSet n S v j).card = coordCount n S v j := by
  by_cases hA : j ∈ activeSet n v
  · have hrange : j.val + 1 ≤ v ∧ v ≤ j.val + 1 + n := by
      simpa [activeSet] using hA
    let x0 : Fin (n + 1) := ⟨v - (j.val + 1), by omega⟩
    have hx0 : ∀ x : Fin (n + 1), j.val + 1 + x.val = v ↔ x = x0 := by
      intro x
      constructor
      · intro h
        exact Fin.ext (by dsimp [x0]; omega)
      · intro h
        subst h
        dsimp [x0]
        omega
    by_cases hS : j ∈ S
    · have hset : coordSet n S v j = {x0} := by
        ext x
        simp [coordSet, hS, hx0]
      simp [hset, coordCount, hS, hA]
    · have hset : coordSet n S v j = Finset.univ.erase x0 := by
        ext x
        simp [coordSet, hS, hx0]
      rw [hset, Finset.card_erase_of_mem (Finset.mem_univ x0)]
      simp [coordCount, hS, hA]
  · have hno : ∀ x : Fin (n + 1), j.val + 1 + x.val ≠ v := by
      intro x
      have hxlt : x.val < n + 1 := x.isLt
      simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      omega
    by_cases hS : j ∈ S
    · have hset : coordSet n S v j = ∅ := by
        ext x
        simp [coordSet, hS, hno x]
      simp [hset, coordCount, hS, hA]
    · have hset : coordSet n S v j = Finset.univ := by
        ext x
        simp [coordSet, hS, hno x]
      simp [hset, coordCount, hS, hA]

private lemma fiber_eq_piFinset (n : ℕ) (S : Finset (Fin 6)) (v : ℕ) :
    fiber n S v = Fintype.piFinset (coordSet n S v) := by
  ext y
  rw [fiber, Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Finset.mem_univ, true_and, coordSet, Finset.mem_filter]
  rfl

private lemma card_fiber (n : ℕ) (S : Finset (Fin 6)) (v : ℕ) :
    (fiber n S v).card = ∏ j : Fin 6, coordCount n S v j := by
  rw [fiber_eq_piFinset, Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun j _ => card_coordSet n S v j

private lemma badArrays_eq_biUnion (n : ℕ) :
    badArrays n = (Finset.range (n + 7) ×ˢ heavySubsets).biUnion fun p => fiber n p.2 p.1 := by
  ext y
  simp only [badArrays, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
    Finset.mem_product, Finset.mem_range, heavySubsets, fiber]
  constructor
  · intro hnot
    unfold AtMostThrice at hnot
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    refine ⟨(value y i, Finset.univ.filter fun j : Fin 6 => value y j = value y i), ⟨?_, ?_⟩, ?_⟩
    · unfold value
      have hi6 : i.val < 6 := i.isLt
      have hy : (y i).val < n + 1 := (y i).isLt
      omega
    · dsimp only
      omega
    · intro j
      simp
  · rintro ⟨⟨v, S⟩, ⟨_, hS⟩, hy⟩
    dsimp only at hS hy
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hiS⟩ := hne
    have hvi : value y i = v := (hy i).mpr hiS
    have hfilt : (Finset.univ.filter fun j : Fin 6 => value y j = value y i) = S := by
      ext j
      simp [hvi, hy j]
    unfold AtMostThrice
    intro hle
    have := hle i
    rw [hfilt] at this
    omega

private lemma pairwiseDisjoint_fiber (n : ℕ) :
    Set.PairwiseDisjoint (↑(Finset.range (n + 7) ×ˢ heavySubsets) : Set (ℕ × Finset (Fin 6)))
      fun p => fiber n p.2 p.1 := by
  intro p₁ hp₁ p₂ hp₂ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro y hy₁ hy₂
  simp only [Finset.mem_coe, Finset.mem_product, heavySubsets, Finset.mem_filter,
    Finset.mem_univ, true_and] at hp₁ hp₂
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
  have hinter : (p₁.2 ∩ p₂.2).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hdisj : Disjoint p₁.2 p₂.2 := Finset.disjoint_iff_inter_eq_empty.mpr hemp
    have hcard : (p₁.2 ∪ p₂.2).card ≤ 6 := by
      calc (p₁.2 ∪ p₂.2).card ≤ (Finset.univ : Finset (Fin 6)).card :=
            Finset.card_le_card (Finset.subset_univ _)
        _ = 6 := by simp
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    omega
  obtain ⟨j, hj⟩ := hinter
  rw [Finset.mem_inter] at hj
  have hv : p₁.1 = p₂.1 := ((hy₁ j).mpr hj.1).symm.trans ((hy₂ j).mpr hj.2)
  have hS : p₁.2 = p₂.2 := by
    ext i
    rw [← hy₁ i, ← hy₂ i, hv]
  exact hne (Prod.ext hv hS)

private lemma card_badArrays_eq_double_sum (n : ℕ) :
    (badArrays n).card =
      ∑ v ∈ Finset.range (n + 7), ∑ S ∈ heavySubsets, ∏ j : Fin 6, coordCount n S v j := by
  rw [badArrays_eq_biUnion, Finset.card_biUnion (pairwiseDisjoint_fiber n), Finset.sum_product]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun S _ => ?_
  exact card_fiber n S v

private lemma prod_coordCount_of_subset (n v : ℕ) {S : Finset (Fin 6)}
    (hSA : S ⊆ activeSet n v) :
    ∏ j : Fin 6, coordCount n S v j =
      n ^ ((activeSet n v).card - S.card) * (n + 1) ^ (6 - (activeSet n v).card) := by
  set A := activeSet n v
  rw [← Finset.prod_mul_prod_compl A, ← Finset.prod_sdiff hSA]
  have hS_prod : ∏ j ∈ S, coordCount n S v j = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    have hjA : j ∈ activeSet n v := hSA hj
    simp [coordCount, hj, hjA]
  have hdiff_prod : ∏ j ∈ A \ S, coordCount n S v j = n ^ (A.card - S.card) := by
    have hcongr : ∏ j ∈ A \ S, coordCount n S v j = ∏ _j ∈ A \ S, n := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finset.mem_sdiff] at hj
      have hjA : j ∈ activeSet n v := hj.1
      simp [coordCount, hj.2, hjA]
    rw [hcongr, Finset.prod_const]
    have hcard : (A \ S).card + S.card = A.card := Finset.card_sdiff_add_card_eq_card hSA
    congr 1
    omega
  have hcompl_prod : ∏ j ∈ Aᶜ, coordCount n S v j = (n + 1) ^ (6 - A.card) := by
    have hcongr : ∏ j ∈ Aᶜ, coordCount n S v j = ∏ _j ∈ Aᶜ, (n + 1) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finset.mem_compl] at hj
      have hjA : j ∉ activeSet n v := hj
      have hjS : j ∉ S := fun h => hj (hSA h)
      simp [coordCount, hjA, hjS]
    rw [hcongr, Finset.prod_const, Finset.card_compl, Fintype.card_fin]
  rw [hS_prod, hdiff_prod, hcompl_prod, mul_one]

private lemma prod_coordCount_of_not_subset (n v : ℕ) {S : Finset (Fin 6)}
    (hnot : ¬ S ⊆ activeSet n v) :
    ∏ j : Fin 6, coordCount n S v j = 0 := by
  obtain ⟨j, hjS, hjA⟩ := Finset.not_subset.mp hnot
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [coordCount, hjS, hjA])

private lemma sum_heavySubsets_eq_g (n v : ℕ) :
    ∑ S ∈ heavySubsets, ∏ j : Fin 6, coordCount n S v j = g n (activeSet n v).card := by
  set A := activeSet n v
  have hfilter :
      ∑ S ∈ heavySubsets, ∏ j : Fin 6, coordCount n S v j =
        ∑ S ∈ heavySubsets.filter (· ⊆ A), ∏ j : Fin 6, coordCount n S v j := by
    symm
    refine Finset.sum_filter_of_ne fun S _ hne => ?_
    by_contra hnot
    exact hne (prod_coordCount_of_not_subset n v hnot)
  rw [hfilter]
  have hunion :
      heavySubsets.filter (· ⊆ A) =
        (A.powersetCard 4 ∪ A.powersetCard 5) ∪ A.powersetCard 6 := by
    ext S
    simp only [heavySubsets, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨h4, hSA⟩
      have hle : S.card ≤ 6 := by
        calc S.card ≤ (Finset.univ : Finset (Fin 6)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = 6 := by simp
      have hcases : S.card = 4 ∨ S.card = 5 ∨ S.card = 6 := by omega
      rcases hcases with h | h | h
      · exact Or.inl (Or.inl ⟨hSA, h⟩)
      · exact Or.inl (Or.inr ⟨hSA, h⟩)
      · exact Or.inr ⟨hSA, h⟩
    · rintro ((⟨hSA, h⟩ | ⟨hSA, h⟩) | ⟨hSA, h⟩) <;> exact ⟨by omega, hSA⟩
  have hdisj45 : Disjoint (A.powersetCard 4) (A.powersetCard 5) := by
    rw [Finset.disjoint_left]
    intro S h4 h5
    rw [Finset.mem_powersetCard] at h4 h5
    omega
  have hdisj456 : Disjoint (A.powersetCard 4 ∪ A.powersetCard 5) (A.powersetCard 6) := by
    rw [Finset.disjoint_left]
    intro S h45 h6
    rw [Finset.mem_union, Finset.mem_powersetCard, Finset.mem_powersetCard] at h45
    rw [Finset.mem_powersetCard] at h6
    omega
  rw [hunion, Finset.sum_union hdisj456, Finset.sum_union hdisj45]
  have hsum_r : ∀ r : ℕ,
      ∑ S ∈ A.powersetCard r, ∏ j : Fin 6, coordCount n S v j =
        A.card.choose r * (n ^ (A.card - r) * (n + 1) ^ (6 - A.card)) := by
    intro r
    have hcongr :
        ∑ S ∈ A.powersetCard r, ∏ j : Fin 6, coordCount n S v j =
          ∑ _S ∈ A.powersetCard r, (n ^ (A.card - r) * (n + 1) ^ (6 - A.card)) := by
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.mem_powersetCard] at hS
      rw [prod_coordCount_of_subset n v hS.1, hS.2]
    rw [hcongr, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
  rw [hsum_r 4, hsum_r 5, hsum_r 6]
  have hk : A.card ≤ 6 := by
    calc A.card ≤ (Finset.univ : Finset (Fin 6)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = 6 := by simp
  set k := A.card
  interval_cases k <;> simp only [g]
  · change 0 * _ + 0 * _ + 0 * _ = 0; ring
  · change 0 * _ + 0 * _ + 0 * _ = 0; ring
  · change 0 * _ + 0 * _ + 0 * _ = 0; ring
  · change 0 * _ + 0 * _ + 0 * _ = 0; ring
  · change 1 * (n ^ 0 * (n + 1) ^ 2) + 0 * _ + 0 * _ = _; ring
  · change 5 * (n ^ 1 * (n + 1) ^ 1) + 1 * (n ^ 0 * (n + 1) ^ 1) + 0 * _ = _; ring
  · change 15 * (n ^ 2 * (n + 1) ^ 0) + 6 * (n ^ 1 * (n + 1) ^ 0) + 1 * (n ^ 0 * (n + 1) ^ 0) = _
    ring

private lemma card_badArrays_eq_sum_g (n : ℕ) :
    (badArrays n).card = ∑ v ∈ Finset.range (n + 7), g n (activeSet n v).card := by
  rw [card_badArrays_eq_double_sum]
  exact Finset.sum_congr rfl fun v _ => sum_heavySubsets_eq_g n v

private lemma a_one : a 1 = 64 := by
  have h1 := card_a_add_badArrays 1
  have h2 : (badArrays 1).card = 0 := by
    rw [card_badArrays_eq_sum_g]
    decide
  omega

private lemma a_two : a 2 = 729 := by
  have h1 := card_a_add_badArrays 2
  have h2 : (badArrays 2).card = 0 := by
    rw [card_badArrays_eq_sum_g]
    decide
  omega

private lemma a_three : a 3 = 4048 := by
  have h1 := card_a_add_badArrays 3
  have h2 : (badArrays 3).card = 48 := by
    rw [card_badArrays_eq_sum_g]
    decide
  omega

private lemma activeSet_card_low (m : ℕ) :
    (activeSet (m + 4) 0).card = 0 ∧
    (activeSet (m + 4) 1).card = 1 ∧
    (activeSet (m + 4) 2).card = 2 ∧
    (activeSet (m + 4) 3).card = 3 ∧
    (activeSet (m + 4) 4).card = 4 ∧
    (activeSet (m + 4) 5).card = 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : activeSet (m + 4) 0 = ∅ := by
      ext j; fin_cases j <;> simp [activeSet]
    simp [h]
  · have h : activeSet (m + 4) 1 = {0} := by
      ext j; fin_cases j <;> simp [activeSet]
    simp [h]
  · have h : activeSet (m + 4) 2 = {0, 1} := by
      ext j
      (fin_cases j <;> simp [activeSet])
      omega
    simp [h]
  · have h : activeSet (m + 4) 3 = {0, 1, 2} := by
      ext j; fin_cases j <;> simp [activeSet] <;> omega
    simp [h]
  · have h : activeSet (m + 4) 4 = {0, 1, 2, 3} := by
      ext j; fin_cases j <;> simp [activeSet] <;> omega
    simp [h]
  · have h : activeSet (m + 4) 5 = {0, 1, 2, 3, 4} := by
      ext j; fin_cases j <;> simp [activeSet] <;> omega
    simp [h]

private lemma activeSet_card_mid (m t : ℕ) (ht : t < m) :
    (activeSet (m + 4) (6 + t)).card = 6 := by
  have h : activeSet (m + 4) (6 + t) = Finset.univ := by
    ext j
    fin_cases j <;> simp [activeSet] <;> omega
  simp [h]

private lemma activeSet_card_high (m : ℕ) :
    (activeSet (m + 4) (6 + m)).card = 5 ∧
    (activeSet (m + 4) (6 + m + 1)).card = 4 ∧
    (activeSet (m + 4) (6 + m + 2)).card = 3 ∧
    (activeSet (m + 4) (6 + m + 3)).card = 2 ∧
    (activeSet (m + 4) (6 + m + 4)).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h : activeSet (m + 4) (6 + m) = {1, 2, 3, 4, 5} := by
      ext j; fin_cases j <;> simp [activeSet] <;> omega
    simp [h]
  · have h : activeSet (m + 4) (6 + m + 1) = {2, 3, 4, 5} := by
      ext j; fin_cases j <;> simp [activeSet] <;> omega
    simp [h]
  · have h : activeSet (m + 4) (6 + m + 2) = {3, 4, 5} := by
      ext j; fin_cases j <;> simp [activeSet] <;> omega
    simp [h]
  · have h : activeSet (m + 4) (6 + m + 3) = {4, 5} := by
      ext j; fin_cases j <;> simp [activeSet] <;> omega
    simp [h]
  · have h : activeSet (m + 4) (6 + m + 4) = {5} := by
      ext j; fin_cases j <;> simp [activeSet] <;> omega
    simp [h]

private lemma a_add_four (m : ℕ) : a (m + 4) = poly (m + 4) := by
  have hbad :
      (badArrays (m + 4)).card =
        2 * (m + 5) ^ 2 + 2 * (5 * (m + 4) + 1) * (m + 5) +
          m * (15 * (m + 4) ^ 2 + 6 * (m + 4) + 1) := by
    rw [card_badArrays_eq_sum_g]
    have hsplit : m + 4 + 7 = 6 + m + 5 := by omega
    rw [hsplit, Finset.sum_range_add, Finset.sum_range_add]
    have hlow := activeSet_card_low m
    have hhigh := activeSet_card_high m
    have h1 :
        ∑ v ∈ Finset.range 6, g (m + 4) (activeSet (m + 4) v).card =
          (m + 5) ^ 2 + (5 * (m + 4) + 1) * (m + 5) := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      rw [hlow.1, hlow.2.1, hlow.2.2.1, hlow.2.2.2.1, hlow.2.2.2.2.1, hlow.2.2.2.2.2]
      simp [g]
    have h2 :
        ∑ t ∈ Finset.range m, g (m + 4) (activeSet (m + 4) (6 + t)).card =
          m * (15 * (m + 4) ^ 2 + 6 * (m + 4) + 1) := by
      have hcongr :
          ∑ t ∈ Finset.range m, g (m + 4) (activeSet (m + 4) (6 + t)).card =
            ∑ _t ∈ Finset.range m, (15 * (m + 4) ^ 2 + 6 * (m + 4) + 1) := by
        refine Finset.sum_congr rfl fun t ht => ?_
        rw [Finset.mem_range] at ht
        rw [activeSet_card_mid m t ht]
        rfl
      rw [hcongr, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h3 :
        ∑ t ∈ Finset.range 5, g (m + 4) (activeSet (m + 4) (6 + m + t)).card =
          (5 * (m + 4) + 1) * (m + 5) + (m + 5) ^ 2 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, add_zero]
      rw [hhigh.1, hhigh.2.1, hhigh.2.2.1, hhigh.2.2.2.1, hhigh.2.2.2.2]
      simp [g]
    rw [h1, h2, h3]
    ring
  have htot := card_a_add_badArrays (m + 4)
  have hpoly : poly (m + 4) + (badArrays (m + 4)).card = (m + 4 + 1) ^ 6 := by
    rw [hbad]
    unfold poly
    ring
  omega

private lemma a_eq_poly {n : ℕ} (hn : 4 ≤ n) : a n = poly n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm]
  exact a_add_four m

private lemma recurrence (n : ℕ) (hn : 10 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4)
      + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
  have h0 : a (m + 11) = poly (m + 11) := a_eq_poly (by omega)
  have h1 : a (m + 11 - 1) = poly (m + 10) := by
    have : m + 11 - 1 = m + 10 := by omega
    rw [this]; exact a_eq_poly (by omega)
  have h2 : a (m + 11 - 2) = poly (m + 9) := by
    have : m + 11 - 2 = m + 9 := by omega
    rw [this]; exact a_eq_poly (by omega)
  have h3 : a (m + 11 - 3) = poly (m + 8) := by
    have : m + 11 - 3 = m + 8 := by omega
    rw [this]; exact a_eq_poly (by omega)
  have h4 : a (m + 11 - 4) = poly (m + 7) := by
    have : m + 11 - 4 = m + 7 := by omega
    rw [this]; exact a_eq_poly (by omega)
  have h5 : a (m + 11 - 5) = poly (m + 6) := by
    have : m + 11 - 5 = m + 6 := by omega
    rw [this]; exact a_eq_poly (by omega)
  have h6 : a (m + 11 - 6) = poly (m + 5) := by
    have : m + 11 - 6 = m + 5 := by omega
    rw [this]; exact a_eq_poly (by omega)
  have h7 : a (m + 11 - 7) = poly (m + 4) := by
    have : m + 11 - 7 = m + 4 := by omega
    rw [this]; exact a_eq_poly (by omega)
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  unfold poly
  push_cast
  ring

private lemma gf_identity :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (64 + 281 * X + 289 * X ^ 2 + 98 * X ^ 3 + 44 * X ^ 4 + 57 * X ^ 5 - 405 * X ^ 6
        + 482 * X ^ 7 - 232 * X ^ 8 + 42 * X ^ 9) := by
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have hlhs :
      F * (1 - X) ^ 7 =
        F - C 7 * (X ^ 1 * F) + C 21 * (X ^ 2 * F) - C 35 * (X ^ 3 * F) + C 35 * (X ^ 4 * F)
          - C 21 * (X ^ 5 * F) + C 7 * (X ^ 6 * F) - X ^ 7 * F := by
    simp only [map_ofNat]
    ring
  have hrhs :
      X * (64 + 281 * X + 289 * X ^ 2 + 98 * X ^ 3 + 44 * X ^ 4 + 57 * X ^ 5 - 405 * X ^ 6
        + 482 * X ^ 7 - 232 * X ^ 8 + 42 * X ^ 9) =
        C 64 * (X : PowerSeries ℚ) ^ 1 + C 281 * X ^ 2 + C 289 * X ^ 3 + C 98 * X ^ 4
          + C 44 * X ^ 5 + C 57 * X ^ 6 - C 405 * X ^ 7 + C 482 * X ^ 8 - C 232 * X ^ 9
          + C 42 * X ^ 10 := by
    simp only [map_ofNat]
    ring
  rw [hlhs, hrhs]
  ext k
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk]
  by_cases hk : k ≤ 10
  · have h4 : a 4 = 15365 := by rw [a_eq_poly (by omega)]; unfold poly; norm_num
    have h5 : a 5 = 45866 := by rw [a_eq_poly (by omega)]; unfold poly; norm_num
    have h6 : a 6 = 115963 := by rw [a_eq_poly (by omega)]; unfold poly; norm_num
    have h7 : a 7 = 259106 := by rw [a_eq_poly (by omega)]; unfold poly; norm_num
    have h8 : a 8 = 526505 := by rw [a_eq_poly (by omega)]; unfold poly; norm_num
    have h9 : a 9 = 992530 := by rw [a_eq_poly (by omega)]; unfold poly; norm_num
    have h10 : a 10 = 1760831 := by rw [a_eq_poly (by omega)]; unfold poly; norm_num
    interval_cases k <;> simp [a_one, a_two, a_three, h4, h5, h6, h7, h8, h9, h10] <;> norm_num
  · have hk10 : 10 < k := by omega
    have hrec :
        (a k : ℚ) =
          7 * a (k - 1) - 21 * a (k - 2) + 35 * a (k - 3) - 35 * a (k - 4)
            + 21 * a (k - 5) - 7 * a (k - 6) + a (k - 7) := by
      have hz := recurrence k hk10
      exact_mod_cast hz
    have hle : ∀ j : ℕ, j ≤ 7 → j ≤ k := fun j hj => by omega
    have hnz : ∀ j : ℕ, j ≤ 7 → k - j ≠ 0 := fun j hj => by omega
    have hne : ∀ j : ℕ, j ≤ 10 → k ≠ j := fun j hj => by omega
    simp only [hne 0 (by omega), hne 1 (by omega), hne 2 (by omega), hne 3 (by omega),
      hne 4 (by omega), hne 5 (by omega), hne 6 (by omega), hne 7 (by omega),
      hne 8 (by omega), hne 9 (by omega), hne 10 (by omega),
      hle 1 (by omega), hle 2 (by omega), hle 3 (by omega), hle 4 (by omega),
      hle 5 (by omega), hle 6 (by omega), hle 7 (by omega),
      hnz 1 (by omega), hnz 2 (by omega), hnz 3 (by omega), hnz 4 (by omega),
      hnz 5 (by omega), hnz 6 (by omega), hnz 7 (by omega),
      ite_true, ite_false, mul_zero, add_zero, sub_zero]
    linarith

end OMA.A250364Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a250364.main :=
  ⟨OMA.A250364Proof.gf_identity, OMA.A250364Proof.recurrence⟩
