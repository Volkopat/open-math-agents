import OMAStatements.S_mo_354319

open OMA.S_mo_354319

private def aV (m k : ℕ) (hk : k ≤ m) : Fin (4 * (m + 1)) := ⟨4 * k, by omega⟩
private def bV (m k : ℕ) (hk : k ≤ m) : Fin (4 * (m + 1)) := ⟨4 * k + 1, by omega⟩
private def sV (m k : ℕ) (hk : k ≤ m) : Fin (4 * (m + 1)) := ⟨4 * k + 2, by omega⟩
private def tV (m k : ℕ) (hk : k ≤ m) : Fin (4 * (m + 1)) := ⟨4 * k + 3, by omega⟩

private def adjSame (r1 r2 : ℕ) : Prop :=
  (r1 = 2 ∧ r2 = 3) ∨ (r1 = 3 ∧ r2 = 2) ∨
  (r1 = 2 ∧ r2 = 1) ∨ (r1 = 1 ∧ r2 = 2) ∨
  (r1 = 3 ∧ r2 = 0) ∨ (r1 = 0 ∧ r2 = 3)

private def adjRel {m : ℕ} (u v : Fin (4 * (m + 1))) : Prop :=
  (u.val / 4 = v.val / 4 ∧ adjSame (u.val % 4) (v.val % 4)) ∨
  (u.val / 4 < v.val / 4 ∧ v.val % 4 < 2) ∨
  (v.val / 4 < u.val / 4 ∧ u.val % 4 < 2)

private lemma adjSame_symm {r1 r2 : ℕ} (h : adjSame r1 r2) : adjSame r2 r1 := by
  unfold adjSame at h ⊢
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
  · right; left; exact ⟨b, a⟩
  · left; exact ⟨b, a⟩
  · right; right; right; left; exact ⟨b, a⟩
  · right; right; left; exact ⟨b, a⟩
  · right; right; right; right; right; exact ⟨b, a⟩
  · right; right; right; right; left; exact ⟨b, a⟩

private lemma adjSame_irrefl (r : ℕ) : ¬ adjSame r r := by
  intro h
  rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega

private lemma adjRel_symm {m : ℕ} {u v : Fin (4 * (m + 1))} (h : adjRel u v) : adjRel v u := by
  rcases h with ⟨h1, h2⟩ | h | h
  · exact Or.inl ⟨h1.symm, adjSame_symm h2⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

private def counterGraph (m : ℕ) : SimpleGraph (Fin (4 * (m + 1))) where
  Adj := adjRel
  symm := ⟨fun _ _ h => adjRel_symm h⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩
    · exact adjSame_irrefl _ h
    · omega
    · omega⟩

private lemma adj_of_03 {m : ℕ} {x y : Fin (4 * (m + 1))}
    (hd : x.val / 4 = y.val / 4) (hne : x ≠ y)
    (hx : x.val % 4 = 0 ∨ x.val % 4 = 3)
    (hy : y.val % 4 = 0 ∨ y.val % 4 = 3) :
    (counterGraph m).Adj x y := by
  have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
  have hmod : x.val % 4 ≠ y.val % 4 := by omega
  left
  refine ⟨hd, ?_⟩
  unfold adjSame
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exfalso; exact hmod (by omega)
  · right; right; right; right; right; exact ⟨hx, hy⟩
  · right; right; right; right; left; exact ⟨hx, hy⟩
  · exfalso; exact hmod (by omega)

private lemma adj_of_12 {m : ℕ} {x y : Fin (4 * (m + 1))}
    (hd : x.val / 4 = y.val / 4) (hne : x ≠ y)
    (hx : ¬(x.val % 4 = 0 ∨ x.val % 4 = 3))
    (hy : ¬(y.val % 4 = 0 ∨ y.val % 4 = 3)) :
    (counterGraph m).Adj x y := by
  have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
  have hx' : x.val % 4 = 1 ∨ x.val % 4 = 2 := by omega
  have hy' : y.val % 4 = 1 ∨ y.val % 4 = 2 := by omega
  have hmod : x.val % 4 ≠ y.val % 4 := by omega
  left
  refine ⟨hd, ?_⟩
  unfold adjSame
  rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
  · exfalso; exact hmod (by omega)
  · right; right; right; left; exact ⟨hx', hy'⟩
  · right; right; left; exact ⟨hx', hy'⟩
  · exfalso; exact hmod (by omega)

private lemma adj_of_23 {m : ℕ} {x y : Fin (4 * (m + 1))}
    (hd : x.val / 4 = y.val / 4) (hne : x ≠ y)
    (hx : 2 ≤ x.val % 4) (hy : 2 ≤ y.val % 4) :
    (counterGraph m).Adj x y := by
  have hne' : x.val ≠ y.val := fun h => hne (Fin.ext h)
  have hx' : x.val % 4 = 2 ∨ x.val % 4 = 3 := by omega
  have hy' : y.val % 4 = 2 ∨ y.val % 4 = 3 := by omega
  have hmod : x.val % 4 ≠ y.val % 4 := by omega
  left
  refine ⟨hd, ?_⟩
  unfold adjSame
  rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
  · exfalso; exact hmod (by omega)
  · left; exact ⟨hx', hy'⟩
  · right; left; exact ⟨hx', hy'⟩
  · exfalso; exact hmod (by omega)

private lemma card_level_le_two {m L : ℕ} {S : Finset (Fin (4 * (m + 1)))}
    (hS : (counterGraph m).IsIndepSet (S : Set (Fin (4 * (m + 1)))))
    (hlvl : ∀ v ∈ S, v.val / 4 = L) : S.card ≤ 2 := by
  have hsplit : S.card =
      (S.filter (fun v => v.val % 4 = 0 ∨ v.val % 4 = 3)).card +
      (S.filter (fun v => ¬(v.val % 4 = 0 ∨ v.val % 4 = 3))).card := by
    have h := (Finset.sum_filter_add_sum_filter_not S
      (fun v : Fin (4 * (m + 1)) => v.val % 4 = 0 ∨ v.val % 4 = 3) (fun _ => (1 : ℕ))).symm
    simpa [Finset.sum_const, smul_eq_mul, mul_one] using h
  have h1 : (S.filter (fun v => v.val % 4 = 0 ∨ v.val % 4 = 3)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    by_contra hne
    exact hS hx.1 hy.1 hne (adj_of_03 (by rw [hlvl x hx.1, hlvl y hy.1]) hne hx.2 hy.2)
  have h2 : (S.filter (fun v => ¬(v.val % 4 = 0 ∨ v.val % 4 = 3))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy
    by_contra hne
    exact hS hx.1 hy.1 hne (adj_of_12 (by rw [hlvl x hx.1, hlvl y hy.1]) hne hx.2 hy.2)
  omega

private def wt (m : ℕ) (u : Fin (4 * (m + 1))) : ℕ := 2 ^ (u.val / 4)

private lemma wt_pos (m : ℕ) (u : Fin (4 * (m + 1))) : 0 < wt m u :=
  Nat.two_pow_pos _

private lemma sum_wt_le_level (m : ℕ) :
    ∀ L : ℕ, L ≤ m →
      ∀ T : Finset (Fin (4 * (m + 1))),
        (counterGraph m).IsIndepSet (T : Set (Fin (4 * (m + 1)))) →
        (∀ v ∈ T, v.val / 4 ≤ L) →
        ∑ v ∈ T, wt m v ≤ 2 ^ (L + 1) := by
  intro L
  induction L with
  | zero =>
    intro _ T hT hbound
    have hlevel : ∀ v ∈ T, v.val / 4 = 0 := fun v hv => Nat.eq_zero_of_le_zero (hbound v hv)
    have hcard : T.card ≤ 2 := card_level_le_two hT hlevel
    have hsum : ∑ v ∈ T, wt m v = T.card := by
      calc ∑ v ∈ T, wt m v = ∑ _v ∈ T, 1 := by
            refine Finset.sum_congr rfl fun v hv => ?_
            simp [wt, hlevel v hv]
        _ = T.card := by simp
    omega
  | succ L ih =>
    intro hL T hT hbound
    set Ttop := T.filter (fun v => v.val / 4 = L + 1) with hTtop_def
    set Tbot := T.filter (fun v => v.val / 4 ≠ L + 1) with hTbot_def
    have hsplit : ∑ v ∈ T, wt m v = (∑ v ∈ Ttop, wt m v) + (∑ v ∈ Tbot, wt m v) := by
      simpa [hTtop_def, hTbot_def] using
        (Finset.sum_filter_add_sum_filter_not T (fun v : Fin (4 * (m + 1)) => v.val / 4 = L + 1) (wt m)).symm
    have htop_sum : ∑ v ∈ Ttop, wt m v = Ttop.card * 2 ^ (L + 1) := by
      calc ∑ v ∈ Ttop, wt m v = ∑ _v ∈ Ttop, 2 ^ (L + 1) := by
            refine Finset.sum_congr rfl fun v hv => ?_
            rw [hTtop_def, Finset.mem_filter] at hv
            simp [wt, hv.2]
        _ = Ttop.card * 2 ^ (L + 1) := by simp
    have htop_indep : (counterGraph m).IsIndepSet (Ttop : Set (Fin (4 * (m + 1)))) := by
      intro x hx y hy hne
      exact hT (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hne
    by_cases hsmall : ∃ v ∈ Ttop, v.val % 4 < 2
    · rcases hsmall with ⟨v, hv_mem, hv_mod⟩
      have hvT : v ∈ T := (Finset.mem_filter.mp hv_mem).1
      have hv_lvl : v.val / 4 = L + 1 := (Finset.mem_filter.mp hv_mem).2
      have hbot_empty : Tbot = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro u hu
        rw [hTbot_def, Finset.mem_filter] at hu
        have hu_le : u.val / 4 ≤ L + 1 := hbound u hu.1
        have hu_lt : u.val / 4 < v.val / 4 := by omega
        have hne : u ≠ v := fun h => by rw [h] at hu_lt; omega
        exact hT hu.1 hvT hne (Or.inr (Or.inl ⟨hu_lt, hv_mod⟩))
      have hcard : Ttop.card ≤ 2 :=
        card_level_le_two htop_indep (fun x hx => (Finset.mem_filter.mp hx).2)
      rw [hsplit, htop_sum, hbot_empty, Finset.sum_empty, add_zero]
      calc Ttop.card * 2 ^ (L + 1) ≤ 2 * 2 ^ (L + 1) := Nat.mul_le_mul_right _ hcard
        _ = 2 ^ (L + 1 + 1) := by ring
    · have hge2 : ∀ v ∈ Ttop, 2 ≤ v.val % 4 := by
        intro v hv
        have : ¬ (v.val % 4 < 2) := fun h => hsmall ⟨v, hv, h⟩
        omega
      have hcard : Ttop.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        by_contra hne
        exact htop_indep hx hy hne
          (adj_of_23 (by rw [(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2])
            hne (hge2 x hx) (hge2 y hy))
      have hbot_indep : (counterGraph m).IsIndepSet (Tbot : Set (Fin (4 * (m + 1)))) := by
        intro x hx y hy hne
        exact hT (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hne
      have hbot_bound : ∀ u ∈ Tbot, u.val / 4 ≤ L := by
        intro u hu
        rw [hTbot_def, Finset.mem_filter] at hu
        have := hbound u hu.1
        omega
      have hbot_sum : ∑ v ∈ Tbot, wt m v ≤ 2 ^ (L + 1) :=
        ih (by omega) Tbot hbot_indep hbot_bound
      have htop_le : Ttop.card * 2 ^ (L + 1) ≤ 2 ^ (L + 1) := by
        calc Ttop.card * 2 ^ (L + 1) ≤ 1 * 2 ^ (L + 1) := Nat.mul_le_mul_right _ hcard
          _ = 2 ^ (L + 1) := one_mul _
      rw [hsplit, htop_sum]
      calc Ttop.card * 2 ^ (L + 1) + ∑ v ∈ Tbot, wt m v
          ≤ 2 ^ (L + 1) + 2 ^ (L + 1) := Nat.add_le_add htop_le hbot_sum
        _ = 2 ^ (L + 1 + 1) := by ring

private lemma sum_wt_le (m : ℕ) (T : Finset (Fin (4 * (m + 1))))
    (hT : (counterGraph m).IsIndepSet (T : Set (Fin (4 * (m + 1))))) :
    ∑ v ∈ T, wt m v ≤ 2 ^ (m + 1) :=
  sum_wt_le_level m m le_rfl T hT fun v _ => by omega

private def upperS (m k : ℕ) : Finset (Fin (4 * (m + 1))) :=
  Finset.univ.filter (fun v => k < v.val / 4 ∧ v.val % 4 = 2)

private lemma upperS_indep (m k : ℕ) :
    (counterGraph m).IsIndepSet (upperS m k : Set (Fin (4 * (m + 1)))) := by
  intro u hu v hv _ hadj
  rw [Finset.mem_coe, upperS, Finset.mem_filter] at hu hv
  have hu2 : u.val % 4 = 2 := hu.2.2
  have hv2 : v.val % 4 = 2 := hv.2.2
  rcases hadj with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
  · rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
  · omega
  · omega

private lemma indep_insert {m : ℕ} {S : Finset (Fin (4 * (m + 1)))} {x : Fin (4 * (m + 1))}
    (hS : (counterGraph m).IsIndepSet (S : Set (Fin (4 * (m + 1)))))
    (hx : ∀ y ∈ S, ¬ (counterGraph m).Adj x y) :
    (counterGraph m).IsIndepSet ((insert x S : Finset (Fin (4 * (m + 1)))) : Set (Fin (4 * (m + 1)))) := by
  intro u hu v hv hne hadj
  rw [Finset.mem_coe, Finset.mem_insert] at hu hv
  rcases hu with rfl | hu <;> rcases hv with rfl | hv
  · exact hne rfl
  · exact hx v hv hadj
  · exact hx u hu (adjRel_symm hadj)
  · exact hS hu hv hne hadj

private lemma not_adj_of_lt_ge2 {m : ℕ} {u v : Fin (4 * (m + 1))}
    (h1 : u.val / 4 < v.val / 4) (h2 : 2 ≤ v.val % 4) :
    ¬ (counterGraph m).Adj u v := by
  rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩) <;> omega

private lemma not_adj_of_mod {m : ℕ} {u v : Fin (4 * (m + 1))}
    (hd : u.val / 4 = v.val / 4) (hnot : ¬ adjSame (u.val % 4) (v.val % 4)) :
    ¬ (counterGraph m).Adj u v := by
  rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
  · exact hnot h
  · omega
  · omega

private lemma sum_wt_upperS (m : ℕ) :
    ∀ d : ℕ, d ≤ m →
      ∑ v ∈ upperS m (m - d), wt m v + 2 ^ (m - d + 1) = 2 ^ (m + 1) := by
  intro d
  induction d with
  | zero =>
    intro _
    have hempty : upperS m m = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      rw [upperS, Finset.mem_filter] at hv
      omega
    simp [hempty]
  | succ d ih =>
    intro hd
    have hstep : upperS m (m - (d + 1)) =
        insert (sV m (m - d) (by omega)) (upperS m (m - d)) := by
      ext v
      simp only [upperS, sV, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]
      constructor
      · intro hv
        by_cases h : v.val / 4 = m - d
        · left; omega
        · right; omega
      · rintro (h | h) <;> omega
    have hnotmem : sV m (m - d) (by omega) ∉ upperS m (m - d) := by
      simp only [upperS, sV, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hstep, Finset.sum_insert hnotmem]
    have hwt : wt m (sV m (m - d) (by omega)) = 2 ^ (m - d) := by
      simp only [wt, sV]
      congr 1
      omega
    rw [hwt]
    have hih := ih (by omega)
    have hpow : 2 ^ (m - (d + 1) + 1) = 2 ^ (m - d) := by
      congr 1
      omega
    rw [hpow]
    have hpow2 : 2 ^ (m - d + 1) = 2 ^ (m - d) + 2 ^ (m - d) := by ring
    omega

private lemma sum_wt_upperS' (m k : ℕ) (hk : k ≤ m) :
    ∑ v ∈ upperS m k, wt m v + 2 ^ (k + 1) = 2 ^ (m + 1) := by
  have h := sum_wt_upperS m (m - k) (by omega)
  have hsub : m - (m - k) = k := by omega
  rwa [hsub] at h

private def setB (m k : ℕ) (hk : k + 1 ≤ m) : Finset (Fin (4 * (m + 1))) :=
  insert (aV m (k + 1) hk) (insert (sV m (k + 1) hk) (upperS m (k + 1)))

private def setD (m k : ℕ) (hk : k + 1 ≤ m) : Finset (Fin (4 * (m + 1))) :=
  insert (aV m k (by omega))
    (insert (bV m k (by omega)) (insert (sV m (k + 1) hk) (upperS m (k + 1))))

private def setC (m k : ℕ) (hk : k + 1 ≤ m) : Finset (Fin (4 * (m + 1))) :=
  insert (bV m (k + 1) hk) (insert (tV m (k + 1) hk) (upperS m (k + 1)))

private def setE (m k : ℕ) (hk : k + 1 ≤ m) : Finset (Fin (4 * (m + 1))) :=
  insert (aV m k (by omega))
    (insert (bV m k (by omega)) (insert (tV m (k + 1) hk) (upperS m (k + 1))))

private lemma sV_insert_indep (m k : ℕ) (hk : k + 1 ≤ m) :
    (counterGraph m).IsIndepSet
      ((insert (sV m (k + 1) hk) (upperS m (k + 1)) : Finset _) : Set _) := by
  refine indep_insert (upperS_indep m (k + 1)) fun y hy => ?_
  rw [upperS, Finset.mem_filter] at hy
  exact not_adj_of_lt_ge2 (by simp only [sV]; omega) (by omega)

private lemma tV_insert_indep (m k : ℕ) (hk : k + 1 ≤ m) :
    (counterGraph m).IsIndepSet
      ((insert (tV m (k + 1) hk) (upperS m (k + 1)) : Finset _) : Set _) := by
  refine indep_insert (upperS_indep m (k + 1)) fun y hy => ?_
  rw [upperS, Finset.mem_filter] at hy
  exact not_adj_of_lt_ge2 (by simp only [tV]; omega) (by omega)

private lemma not_mem_upperS_of_le {m k : ℕ} {x : Fin (4 * (m + 1))}
    (hx : x.val / 4 ≤ k + 1) : x ∉ upperS m (k + 1) := by
  rw [upperS, Finset.mem_filter]
  intro h
  omega

private lemma setB_mem_optima (m k : ℕ) (hk : k + 1 ≤ m) :
    setB m k hk ∈ optima (counterGraph m) (wt m) := by
  refine ⟨?_, ?_⟩
  · refine indep_insert (sV_insert_indep m k hk) fun y hy => ?_
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · refine not_adj_of_mod (by simp only [aV, sV]; omega) ?_
      intro h; simp only [aV, sV] at h
      rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    · rw [upperS, Finset.mem_filter] at hy
      exact not_adj_of_lt_ge2 (by simp only [aV]; omega) (by omega)
  · intro T hT
    have hle := sum_wt_le m T hT
    have h1 : aV m (k + 1) hk ∉ insert (sV m (k + 1) hk) (upperS m (k + 1)) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · rw [Fin.ext_iff] at h; simp only [aV, sV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [aV]; omega) h
    have h2 : sV m (k + 1) hk ∉ upperS m (k + 1) :=
      not_mem_upperS_of_le (by simp only [sV]; omega)
    have hsum : ∑ v ∈ setB m k hk, wt m v = 2 ^ (m + 1) := by
      rw [setB, Finset.sum_insert h1, Finset.sum_insert h2]
      have hwa : wt m (aV m (k + 1) hk) = 2 ^ (k + 1) := by simp only [wt, aV]; congr 1; omega
      have hws : wt m (sV m (k + 1) hk) = 2 ^ (k + 1) := by simp only [wt, sV]; congr 1; omega
      have hu := sum_wt_upperS' m (k + 1) hk
      have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      omega
    omega

private lemma setD_mem_optima (m k : ℕ) (hk : k + 1 ≤ m) :
    setD m k hk ∈ optima (counterGraph m) (wt m) := by
  refine ⟨?_, ?_⟩
  · have hb : (counterGraph m).IsIndepSet
        ((insert (bV m k (by omega)) (insert (sV m (k + 1) hk) (upperS m (k + 1))) : Finset _) : Set _) := by
      refine indep_insert (sV_insert_indep m k hk) fun y hy => ?_
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact not_adj_of_lt_ge2 (by simp only [bV, sV]; omega) (by simp only [sV]; omega)
      · rw [upperS, Finset.mem_filter] at hy
        exact not_adj_of_lt_ge2 (by simp only [bV]; omega) (by omega)
    refine indep_insert hb fun y hy => ?_
    rw [Finset.mem_insert, Finset.mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · refine not_adj_of_mod (by simp only [aV, bV]; omega) ?_
      intro h; simp only [aV, bV] at h
      rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    · exact not_adj_of_lt_ge2 (by simp only [aV, sV]; omega) (by simp only [sV]; omega)
    · rw [upperS, Finset.mem_filter] at hy
      exact not_adj_of_lt_ge2 (by simp only [aV]; omega) (by omega)
  · intro T hT
    have hle := sum_wt_le m T hT
    have h1 : aV m k (by omega) ∉
        insert (bV m k (by omega)) (insert (sV m (k + 1) hk) (upperS m (k + 1))) := by
      rw [Finset.mem_insert, Finset.mem_insert]; rintro (h | h | h)
      · rw [Fin.ext_iff] at h; simp only [aV, bV] at h; omega
      · rw [Fin.ext_iff] at h; simp only [aV, sV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [aV]; omega) h
    have h2 : bV m k (by omega) ∉ insert (sV m (k + 1) hk) (upperS m (k + 1)) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · rw [Fin.ext_iff] at h; simp only [bV, sV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [bV]; omega) h
    have h3 : sV m (k + 1) hk ∉ upperS m (k + 1) :=
      not_mem_upperS_of_le (by simp only [sV]; omega)
    have hsum : ∑ v ∈ setD m k hk, wt m v = 2 ^ (m + 1) := by
      rw [setD, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3]
      have hwa : wt m (aV m k (by omega)) = 2 ^ k := by simp only [wt, aV]; congr 1; omega
      have hwb : wt m (bV m k (by omega)) = 2 ^ k := by simp only [wt, bV]; congr 1; omega
      have hws : wt m (sV m (k + 1) hk) = 2 ^ (k + 1) := by simp only [wt, sV]; congr 1; omega
      have hu := sum_wt_upperS' m (k + 1) hk
      have hp1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      have hp2 : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      omega
    omega

private lemma setC_mem_optima (m k : ℕ) (hk : k + 1 ≤ m) :
    setC m k hk ∈ optima (counterGraph m) (wt m) := by
  refine ⟨?_, ?_⟩
  · refine indep_insert (tV_insert_indep m k hk) fun y hy => ?_
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · refine not_adj_of_mod (by simp only [bV, tV]; omega) ?_
      intro h; simp only [bV, tV] at h
      rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    · rw [upperS, Finset.mem_filter] at hy
      exact not_adj_of_lt_ge2 (by simp only [bV]; omega) (by omega)
  · intro T hT
    have hle := sum_wt_le m T hT
    have h1 : bV m (k + 1) hk ∉ insert (tV m (k + 1) hk) (upperS m (k + 1)) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · rw [Fin.ext_iff] at h; simp only [bV, tV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [bV]; omega) h
    have h2 : tV m (k + 1) hk ∉ upperS m (k + 1) :=
      not_mem_upperS_of_le (by simp only [tV]; omega)
    have hsum : ∑ v ∈ setC m k hk, wt m v = 2 ^ (m + 1) := by
      rw [setC, Finset.sum_insert h1, Finset.sum_insert h2]
      have hwb : wt m (bV m (k + 1) hk) = 2 ^ (k + 1) := by simp only [wt, bV]; congr 1; omega
      have hwt : wt m (tV m (k + 1) hk) = 2 ^ (k + 1) := by simp only [wt, tV]; congr 1; omega
      have hu := sum_wt_upperS' m (k + 1) hk
      have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      omega
    omega

private lemma setE_mem_optima (m k : ℕ) (hk : k + 1 ≤ m) :
    setE m k hk ∈ optima (counterGraph m) (wt m) := by
  refine ⟨?_, ?_⟩
  · have hb : (counterGraph m).IsIndepSet
        ((insert (bV m k (by omega)) (insert (tV m (k + 1) hk) (upperS m (k + 1))) : Finset _) : Set _) := by
      refine indep_insert (tV_insert_indep m k hk) fun y hy => ?_
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact not_adj_of_lt_ge2 (by simp only [bV, tV]; omega) (by simp only [tV]; omega)
      · rw [upperS, Finset.mem_filter] at hy
        exact not_adj_of_lt_ge2 (by simp only [bV]; omega) (by omega)
    refine indep_insert hb fun y hy => ?_
    rw [Finset.mem_insert, Finset.mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · refine not_adj_of_mod (by simp only [aV, bV]; omega) ?_
      intro h; simp only [aV, bV] at h
      rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> omega
    · exact not_adj_of_lt_ge2 (by simp only [aV, tV]; omega) (by simp only [tV]; omega)
    · rw [upperS, Finset.mem_filter] at hy
      exact not_adj_of_lt_ge2 (by simp only [aV]; omega) (by omega)
  · intro T hT
    have hle := sum_wt_le m T hT
    have h1 : aV m k (by omega) ∉
        insert (bV m k (by omega)) (insert (tV m (k + 1) hk) (upperS m (k + 1))) := by
      rw [Finset.mem_insert, Finset.mem_insert]; rintro (h | h | h)
      · rw [Fin.ext_iff] at h; simp only [aV, bV] at h; omega
      · rw [Fin.ext_iff] at h; simp only [aV, tV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [aV]; omega) h
    have h2 : bV m k (by omega) ∉ insert (tV m (k + 1) hk) (upperS m (k + 1)) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · rw [Fin.ext_iff] at h; simp only [bV, tV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [bV]; omega) h
    have h3 : tV m (k + 1) hk ∉ upperS m (k + 1) :=
      not_mem_upperS_of_le (by simp only [tV]; omega)
    have hsum : ∑ v ∈ setE m k hk, wt m v = 2 ^ (m + 1) := by
      rw [setE, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3]
      have hwa : wt m (aV m k (by omega)) = 2 ^ k := by simp only [wt, aV]; congr 1; omega
      have hwb : wt m (bV m k (by omega)) = 2 ^ k := by simp only [wt, bV]; congr 1; omega
      have hwt : wt m (tV m (k + 1) hk) = 2 ^ (k + 1) := by simp only [wt, tV]; congr 1; omega
      have hu := sum_wt_upperS' m (k + 1) hk
      have hp1 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      have hp2 : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      omega
    omega

private lemma optima_sum_eq {n : ℕ} {G : SimpleGraph (Fin n)} {w : Fin n → ℕ}
    {S1 S2 : Finset (Fin n)} (h1 : S1 ∈ optima G w) (h2 : S2 ∈ optima G w) :
    ∑ v ∈ S1, w v = ∑ v ∈ S2, w v :=
  le_antisymm (h2.2 S1 h1.1) (h1.2 S2 h2.1)

private lemma w'_lower_bound (m : ℕ) (w' : Fin (4 * (m + 1)) → ℕ)
    (hw'_pos : ∀ v, 0 < w' v)
    (hopt : optima (counterGraph m) w' = optima (counterGraph m) (wt m)) :
    ∀ k : ℕ, (hk : k ≤ m) → 2 ^ k ≤ w' (aV m k hk) ∧ 2 ^ k ≤ w' (bV m k hk) := by
  intro k
  induction k with
  | zero =>
    intro hk
    exact ⟨hw'_pos _, hw'_pos _⟩
  | succ k ih =>
    intro hk
    have hprev := ih (by omega)
    have hB : setB m k hk ∈ optima (counterGraph m) w' := hopt ▸ setB_mem_optima m k hk
    have hD : setD m k hk ∈ optima (counterGraph m) w' := hopt ▸ setD_mem_optima m k hk
    have hC : setC m k hk ∈ optima (counterGraph m) w' := hopt ▸ setC_mem_optima m k hk
    have hE : setE m k hk ∈ optima (counterGraph m) w' := hopt ▸ setE_mem_optima m k hk
    have hBD := optima_sum_eq hB hD
    have hCE := optima_sum_eq hC hE
    have haB : aV m (k + 1) hk ∉ insert (sV m (k + 1) hk) (upperS m (k + 1)) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · rw [Fin.ext_iff] at h; simp only [aV, sV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [aV]; omega) h
    have haD : aV m k (by omega) ∉
        insert (bV m k (by omega)) (insert (sV m (k + 1) hk) (upperS m (k + 1))) := by
      rw [Finset.mem_insert, Finset.mem_insert]; rintro (h | h | h)
      · rw [Fin.ext_iff] at h; simp only [aV, bV] at h; omega
      · rw [Fin.ext_iff] at h; simp only [aV, sV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [aV]; omega) h
    have hbD : bV m k (by omega) ∉ insert (sV m (k + 1) hk) (upperS m (k + 1)) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · rw [Fin.ext_iff] at h; simp only [bV, sV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [bV]; omega) h
    have hbC : bV m (k + 1) hk ∉ insert (tV m (k + 1) hk) (upperS m (k + 1)) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · rw [Fin.ext_iff] at h; simp only [bV, tV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [bV]; omega) h
    have haE : aV m k (by omega) ∉
        insert (bV m k (by omega)) (insert (tV m (k + 1) hk) (upperS m (k + 1))) := by
      rw [Finset.mem_insert, Finset.mem_insert]; rintro (h | h | h)
      · rw [Fin.ext_iff] at h; simp only [aV, bV] at h; omega
      · rw [Fin.ext_iff] at h; simp only [aV, tV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [aV]; omega) h
    have hbE : bV m k (by omega) ∉ insert (tV m (k + 1) hk) (upperS m (k + 1)) := by
      rw [Finset.mem_insert]; rintro (h | h)
      · rw [Fin.ext_iff] at h; simp only [bV, tV] at h; omega
      · exact not_mem_upperS_of_le (by simp only [bV]; omega) h
    rw [setB, setD, Finset.sum_insert haB, Finset.sum_insert haD, Finset.sum_insert hbD] at hBD
    rw [setC, setE, Finset.sum_insert hbC, Finset.sum_insert haE, Finset.sum_insert hbE] at hCE
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_354319.main) := by
  rintro ⟨B, _, hB_sub, hB_opt⟩
  rcases hB_sub 5 (by omega) with ⟨N, hN⟩
  set m := N + 5
  rcases hB_opt (4 * (m + 1)) (counterGraph m) (wt m) (wt_pos m) with ⟨w', hw'_bound, hopt⟩
  have hlow := (w'_lower_bound m w' (fun v => (hw'_bound v).1) hopt m le_rfl).1
  have hB_ge : 2 ^ m ≤ B (4 * (m + 1)) := le_trans hlow (hw'_bound (aV m m le_rfl)).2
  have h1 : (2 ^ m) ^ 5 ≤ B (4 * (m + 1)) ^ 5 := Nat.pow_le_pow_left hB_ge 5
  have h2 : B (4 * (m + 1)) ^ 5 ≤ 2 ^ (4 * (m + 1)) := hN (4 * (m + 1)) (by omega)
  have h3 : 2 ^ (5 * m) ≤ 2 ^ (4 * (m + 1)) := by
    calc 2 ^ (5 * m) = (2 ^ m) ^ 5 := by rw [← pow_mul, mul_comm]
      _ ≤ B (4 * (m + 1)) ^ 5 := h1
      _ ≤ 2 ^ (4 * (m + 1)) := h2
  have h4 : 5 * m ≤ 4 * (m + 1) := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega
