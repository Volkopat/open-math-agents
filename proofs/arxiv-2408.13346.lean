import OMAStatements.S_arxiv_2408_13346
namespace OMA.P_arxiv_2408_13346

open OMA.S_arxiv_2408_13346

private lemma pre2_zero : pre2 0 = 0 := by
  simp [pre2, Multiset.powersetCard_zero_right]

private lemma pre2_cons (a : ℕ) (s : Multiset ℕ) :
    pre2 (a ::ₘ s) = pre2 s + s.map (a * ·) := by
  simp only [pre2, Multiset.powersetCard_cons, Multiset.powersetCard_one,
    Multiset.map_add, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp [Function.comp]

private lemma pre2_singleton (a : ℕ) : pre2 {a} = 0 := by
  change pre2 (a ::ₘ 0) = 0
  rw [pre2_cons, pre2_zero]
  simp

private lemma pre2_mono {s t : Multiset ℕ} (h : s ≤ t) : pre2 s ≤ pre2 t :=
  Multiset.map_le_map (Multiset.powersetCard_mono 2 h)

private lemma sum_pow_sq (s : Multiset ℕ) (r : ℕ) :
    (s.map (· ^ r)).sum ^ 2 =
      (s.map (· ^ (2 * r))).sum + 2 * ((pre2 s).map (· ^ r)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [pre2_zero]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
      pre2_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map]
    have hmap : (s.map ((· ^ r) ∘ (a * ·))).sum = a ^ r * (s.map (· ^ r)).sum := by
      have heq : s.map ((· ^ r) ∘ (a * ·)) = (s.map (· ^ r)).map (a ^ r * ·) := by
        rw [Multiset.map_map]
        apply Multiset.map_congr rfl
        intro x _
        simp [Function.comp, mul_pow]
      rw [heq, Multiset.sum_map_mul_left]
      simp
    have hpow : a ^ (2 * r) = (a ^ r) ^ 2 := by
      rw [mul_comm, pow_mul]
    rw [hmap, hpow]
    linarith [ih]

private lemma pow_two_sum_eq (s t : Multiset ℕ)
    (hsum : s.sum = t.sum) (hpre : pre2 s = pre2 t) :
    ∀ m : ℕ, (s.map (· ^ (2 ^ m))).sum = (t.map (· ^ (2 ^ m))).sum := by
  intro m
  induction m with
  | zero => simpa using hsum
  | succ m ih =>
    have h1 := sum_pow_sq s (2 ^ m)
    have h2 := sum_pow_sq t (2 ^ m)
    have hexp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    rw [hexp]
    rw [ih, hpre] at h1
    omega

private lemma sum_map_eq_finset_sum (s : Multiset ℕ) (U : Finset ℕ) (hU : ∀ x ∈ s, x ∈ U)
    (f : ℕ → ℕ) :
    (s.map f).sum = ∑ x ∈ U, s.count x * f x := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a ∈ U := hU a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x ∈ U := fun x hx => hU x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.sum_cons, ih hs]
    have hsplit : ∀ x ∈ U, (a ::ₘ s).count x * f x =
        (if x = a then f a else 0) + s.count x * f x := by
      intro x _
      by_cases hxa : x = a
      · subst hxa; simp [Multiset.count_cons_self, add_mul, add_comm]
      · simp [Multiset.count_cons_of_ne hxa, hxa]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    simp [ha]

private lemma card_eq_finset_sum_count (s : Multiset ℕ) (U : Finset ℕ) (hU : ∀ x ∈ s, x ∈ U) :
    s.card = ∑ x ∈ U, s.count x := by
  have h := sum_map_eq_finset_sum s U hU (fun _ => 1)
  simpa using h

private lemma bernoulli_nat (a r : ℕ) : (a + r) * a ^ r ≤ a * (a + 1) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc (a + (r + 1)) * a ^ (r + 1)
        = (a + r + 1) * a * a ^ r := by ring
      _ ≤ (a + r) * (a + 1) * a ^ r := by
          have : (a + r + 1) * a ≤ (a + r) * (a + 1) := by nlinarith
          exact Nat.mul_le_mul_right _ this
      _ = (a + r) * a ^ r * (a + 1) := by ring
      _ ≤ a * (a + 1) ^ r * (a + 1) := Nat.mul_le_mul_right _ ih
      _ = a * (a + 1) ^ (r + 1) := by ring

private lemma not_count_lt_of_pow_two_sum_eq (s t : Multiset ℕ) (M : ℕ) (hM : 0 < M)
    (hlt : t.count M < s.count M)
    (hgt : ∀ x : ℕ, M < x → s.count x = t.count x)
    (hpow : ∀ m : ℕ, (s.map (· ^ (2 ^ m))).sum = (t.map (· ^ (2 ^ m))).sum) : False := by
  let U : Finset ℕ := insert M (s.toFinset ∪ t.toFinset)
  have hsU : ∀ x ∈ s, x ∈ U := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hx))
  have htU : ∀ x ∈ t, x ∈ U := fun x hx =>
    Finset.mem_insert_of_mem (Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hx))
  have hbound : ∀ m : ℕ, M ^ (2 ^ m) ≤ t.card * (M - 1) ^ (2 ^ m) := by
    intro m
    let r := 2 ^ m
    have heq : ∑ x ∈ U, s.count x * x ^ r = ∑ x ∈ U, t.count x * x ^ r := by
      rw [← sum_map_eq_finset_sum s U hsU (· ^ r), ← sum_map_eq_finset_sum t U htU (· ^ r)]
      exact hpow m
    have hpart : ∀ g : ℕ → ℕ,
        ∑ x ∈ U, g x =
          (∑ x ∈ U.filter (· < M), g x) + g M + (∑ x ∈ U.filter (M < ·), g x) := by
      intro g
      rw [← Finset.sum_filter_add_sum_filter_not U (· < M) g]
      have hM_mem : M ∈ U.filter (fun x => ¬ x < M) :=
        Finset.mem_filter.mpr ⟨Finset.mem_insert_self M _, by omega⟩
      rw [← Finset.add_sum_erase _ _ hM_mem]
      have herase : (U.filter (fun x => ¬ x < M)).erase M = U.filter (M < ·) := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_filter]
        constructor
        · rintro ⟨hne, hxU, hge⟩; exact ⟨hxU, by omega⟩
        · rintro ⟨hxU, hgt⟩; exact ⟨by omega, hxU, by omega⟩
      rw [herase]
      omega
    have hgt_sum : ∑ x ∈ U.filter (M < ·), s.count x * x ^ r =
        ∑ x ∈ U.filter (M < ·), t.count x * x ^ r := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hgt x (Finset.mem_filter.mp hx).2]
    rw [hpart (fun x => s.count x * x ^ r), hpart (fun x => t.count x * x ^ r), hgt_sum] at heq
    have hdiff : M ^ r ≤ ∑ x ∈ U.filter (· < M), t.count x * x ^ r := by
      have h1 : (t.count M + 1) * M ^ r ≤ s.count M * M ^ r :=
        Nat.mul_le_mul_right _ hlt
      have h2 : s.count M * M ^ r ≤
          (∑ x ∈ U.filter (· < M), t.count x * x ^ r) + t.count M * M ^ r := by omega
      linarith
    have hle_t : ∑ x ∈ U.filter (· < M), t.count x * x ^ r ≤
        (∑ x ∈ U.filter (· < M), t.count x) * (M - 1) ^ r := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro x hx
      have hxM : x ≤ M - 1 := by
        have := (Finset.mem_filter.mp hx).2
        omega
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxM r)
    have hcard_le : ∑ x ∈ U.filter (· < M), t.count x ≤ t.card := by
      rw [card_eq_finset_sum_count t U htU]
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ U)
    exact le_trans hdiff (le_trans hle_t (Nat.mul_le_mul_right _ hcard_le))
  by_cases hM1 : M = 1
  · subst hM1
    have h0 := hbound 0
    simp at h0
  · let a := M - 1
    have ha_pos : 0 < a := by omega
    have hMa : M = a + 1 := by omega
    let m := a * t.card + 1
    have hr_gt : a * t.card < 2 ^ m := lt_trans (by omega) (Nat.lt_two_pow_self (n := m))
    have hbm := hbound m
    rw [hMa] at hbm
    have hbern := bernoulli_nat a (2 ^ m)
    have h1 : (a + 2 ^ m) * a ^ (2 ^ m) ≤ a * (t.card * a ^ (2 ^ m)) :=
      le_trans hbern (Nat.mul_le_mul_left a hbm)
    have h2 : a * (t.card * a ^ (2 ^ m)) = (a * t.card) * a ^ (2 ^ m) := by ring
    rw [h2] at h1
    have ha_pow_pos : 0 < a ^ (2 ^ m) := Nat.pow_pos ha_pos
    have h3 : a + 2 ^ m ≤ a * t.card := Nat.le_of_mul_le_mul_right h1 ha_pow_pos
    omega

private lemma eq_of_pow_two_sum_eq (s t : Multiset ℕ)
    (hs : ∀ x ∈ s, 0 < x) (ht : ∀ x ∈ t, 0 < x)
    (hpow : ∀ m : ℕ, (s.map (· ^ (2 ^ m))).sum = (t.map (· ^ (2 ^ m))).sum) : s = t := by
  by_contra hne
  have hex : ∃ x : ℕ, s.count x ≠ t.count x := by
    by_contra hall
    push Not at hall
    exact hne (Multiset.ext.mpr hall)
  let D : Finset ℕ := (s.toFinset ∪ t.toFinset).filter (fun x => s.count x ≠ t.count x)
  have hD_ne : D.Nonempty := by
    rcases hex with ⟨x, hx⟩
    refine ⟨x, Finset.mem_filter.mpr ⟨?_, hx⟩⟩
    by_cases hxs : x ∈ s
    · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hxs)
    · have hxt : x ∈ t := by
        by_contra hxt
        rw [Multiset.count_eq_zero.mpr hxs, Multiset.count_eq_zero.mpr hxt] at hx
        exact hx rfl
      exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hxt)
  let M := D.max' hD_ne
  have hM_mem : M ∈ D := Finset.max'_mem D hD_ne
  have hM_ne : s.count M ≠ t.count M := (Finset.mem_filter.mp hM_mem).2
  have hM_pos : 0 < M := by
    rcases Finset.mem_union.mp (Finset.mem_filter.mp hM_mem).1 with h1 | h2
    · exact hs M (Multiset.mem_toFinset.mp h1)
    · exact ht M (Multiset.mem_toFinset.mp h2)
  have hgt : ∀ x : ℕ, M < x → s.count x = t.count x := by
    intro x hx
    by_contra hxc
    have hxD : x ∈ D := by
      refine Finset.mem_filter.mpr ⟨?_, hxc⟩
      by_cases hxs : x ∈ s
      · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr hxs)
      · have hxt : x ∈ t := by
          by_contra hxt
          rw [Multiset.count_eq_zero.mpr hxs, Multiset.count_eq_zero.mpr hxt] at hxc
          exact hxc rfl
        exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr hxt)
    have hle : x ≤ M := Finset.le_max' D x hxD
    omega
  rcases lt_or_gt_of_ne hM_ne with hlt | hlt
  · exact not_count_lt_of_pow_two_sum_eq t s M hM_pos hlt (fun x hx => (hgt x hx).symm)
      (fun m => (hpow m).symm)
  · exact not_count_lt_of_pow_two_sum_eq s t M hM_pos hlt hgt hpow

private lemma pre2_partition_injective (n : ℕ) :
    Function.Injective (fun lam : Nat.Partition n => pre2 lam.parts) := by
  intro lam μ h
  apply Nat.Partition.ext
  exact eq_of_pow_two_sum_eq lam.parts μ.parts
    (fun _ hx => lam.parts_pos hx)
    (fun _ hx => μ.parts_pos hx)
    (pow_two_sum_eq lam.parts μ.parts (lam.parts_sum.trans μ.parts_sum.symm) h)

private lemma pre2_all_odd {s : Multiset ℕ} (hs : ∀ x ∈ s, Odd x) :
    ∀ y ∈ pre2 s, Odd y := by
  induction s using Multiset.induction_on with
  | empty => simp [pre2_zero]
  | cons a s ih =>
    intro y hy
    rw [pre2_cons, Multiset.mem_add] at hy
    rcases hy with hy1 | hy2
    · exact ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx)) y hy1
    · rcases Multiset.mem_map.mp hy2 with ⟨b, hb, rfl⟩
      exact (hs a (Multiset.mem_cons_self a s)).mul (hs b (Multiset.mem_cons_of_mem hb))

private lemma nodup_pre2_cases {s : Multiset ℕ} (hnodup : (pre2 s).Nodup) :
    s.Nodup ∨ ∃ a : ℕ, s = {a, a} := by
  by_cases hnd : s.Nodup
  · exact Or.inl hnd
  · right
    rw [Multiset.nodup_iff_count_le_one] at hnd
    push Not at hnd
    rcases hnd with ⟨a, ha⟩
    have hle2 : ({a, a} : Multiset ℕ) ≤ s := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hxa : x = a
      · subst hxa
        change Multiset.count x (x ::ₘ {x}) ≤ s.count x
        simp only [Multiset.count_cons_self, Multiset.count_singleton_self]
        omega
      · have h0 : Multiset.count x ({a, a} : Multiset ℕ) = 0 := by
          change Multiset.count x (a ::ₘ {a}) = 0
          simp [hxa]
        omega
    have hcard_le : s.card ≤ 2 := by
      by_contra hgt
      push Not at hgt
      obtain ⟨r, hr⟩ := Multiset.le_iff_exists_add.mp hle2
      have hr_ne : r ≠ 0 := by
        intro hr0
        rw [hr0, add_zero] at hr
        have hc : s.card = 2 := by rw [hr]; rfl
        omega
      obtain ⟨b, hb⟩ := Multiset.exists_mem_of_ne_zero hr_ne
      have hle3 : (a ::ₘ a ::ₘ {b}) ≤ s := by
        rw [hr]
        have hbr : {b} ≤ r := Multiset.singleton_le.mpr hb
        have hstep : ({a, a} : Multiset ℕ) + {b} ≤ ({a, a} : Multiset ℕ) + r :=
          add_le_add (le_refl _) hbr
        have heq3 : (a ::ₘ a ::ₘ {b}) = ({a, a} : Multiset ℕ) + {b} := by
          ext x
          change (a ::ₘ a ::ₘ b ::ₘ 0).count x = ((a ::ₘ a ::ₘ 0) + (b ::ₘ 0)).count x
          simp only [Multiset.count_add, Multiset.count_cons, Multiset.count_zero]
          omega
        rwa [heq3]
      have hpre3 : pre2 (a ::ₘ a ::ₘ {b}) ≤ pre2 s := pre2_mono hle3
      have hcount3 : (pre2 (a ::ₘ a ::ₘ {b})).count (a * b) ≥ 2 := by
        rw [pre2_cons, pre2_cons, pre2_singleton]
        simp only [zero_add, Multiset.map_cons, Multiset.map_singleton, Multiset.count_add,
          Multiset.count_cons, Multiset.count_singleton]
        split_ifs <;> omega
      have hcount_le := Multiset.nodup_iff_count_le_one.mp hnodup (a * b)
      have hcount_mono := Multiset.count_le_of_le (a * b) hpre3
      omega
    obtain ⟨r, hr⟩ := Multiset.le_iff_exists_add.mp hle2
    have hrc : r.card = 0 := by
      have hc := congrArg Multiset.card hr
      simp only [Multiset.card_add] at hc
      have h2c : ({a, a} : Multiset ℕ).card = 2 := rfl
      omega
    have hr0 : r = 0 := Multiset.card_eq_zero.mp hrc
    rw [hr0, add_zero] at hr
    exact ⟨a, hr⟩

private lemma main_proof :
    ∀ n : ℕ,
      ((pre2Image n).filter (fun m => m.Nodup)).card ≤
        ((pre2Image n).filter (fun m => ∀ x ∈ m, Odd x)).card := by
  intro n
  by_cases hn0 : n = 0
  · subst hn0
    have hsub : (pre2Image 0).filter (fun m => m.Nodup) ⊆
        (pre2Image 0).filter (fun m => ∀ x ∈ m, Odd x) := by
      intro m hm
      rw [Finset.mem_filter] at hm ⊢
      refine ⟨hm.1, ?_⟩
      rcases Finset.mem_image.mp hm.1 with ⟨lam, _, rfl⟩
      have h0 : lam.parts = 0 := by
        by_contra hne
        obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
        have hpos := lam.parts_pos hx
        have hle := Multiset.single_le_sum (fun _ _ => Nat.zero_le _) x hx
        rw [lam.parts_sum] at hle
        omega
      rw [h0, pre2_zero]
      simp
    exact Finset.card_le_card hsub
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    let pSingle : Nat.Partition n :=
      { parts := {n}
        parts_pos := by intro i hi; rw [Multiset.mem_singleton] at hi; omega
        parts_sum := by simp }
    by_cases heven : Even n
    · obtain ⟨k, hk⟩ := heven
      have hk_pos : 0 < k := by omega
      let pDouble : Nat.Partition n :=
        { parts := {k, k}
          parts_pos := by
            intro i hi
            change i ∈ (k ::ₘ {k}) at hi
            rw [Multiset.mem_cons, Multiset.mem_singleton] at hi
            rcases hi with rfl | rfl <;> exact hk_pos
          parts_sum := by
            change (k ::ₘ {k}).sum = n
            simp only [Multiset.sum_cons, Multiset.sum_singleton]
            omega }
      -- Lower bound on odd partitions in `pre2Image n`: `odds n` plus `pSingle`.
      let oddSrc : Finset (Nat.Partition n) := insert pSingle (Nat.Partition.odds n)
      have hpSingle_not_odd : pSingle ∉ Nat.Partition.odds n := by
        intro hmem
        simp only [Nat.Partition.odds, Nat.Partition.restricted, Finset.mem_filter,
          Finset.mem_univ, true_and] at hmem
        exact hmem n (Multiset.mem_singleton_self n) ⟨k, hk⟩
      have hodd_sub : oddSrc.image (fun lam => pre2 lam.parts) ⊆
          (pre2Image n).filter (fun m => ∀ x ∈ m, Odd x) := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨lam, hlam, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_image.mpr ⟨lam, Finset.mem_univ _, rfl⟩, ?_⟩
        rcases Finset.mem_insert.mp hlam with rfl | hodd
        · simp [pSingle, pre2_singleton]
        · simp only [Nat.Partition.odds, Nat.Partition.restricted, Finset.mem_filter,
            Finset.mem_univ, true_and] at hodd
          exact pre2_all_odd (fun x hx => Nat.not_even_iff_odd.mp (hodd x hx))
      have hodd_lb : (Nat.Partition.odds n).card + 1 ≤
          ((pre2Image n).filter (fun m => ∀ x ∈ m, Odd x)).card := by
        calc (Nat.Partition.odds n).card + 1
            = oddSrc.card := (Finset.card_insert_of_notMem hpSingle_not_odd).symm
          _ = (oddSrc.image (fun lam => pre2 lam.parts)).card :=
              (Finset.card_image_of_injective oddSrc (pre2_partition_injective n)).symm
          _ ≤ ((pre2Image n).filter (fun m => ∀ x ∈ m, Odd x)).card :=
              Finset.card_le_card hodd_sub
      -- Upper bound on distinct partitions in `pre2Image n`: image of `distincts n` plus `pDouble`.
      let distSrc : Finset (Nat.Partition n) := insert pDouble (Nat.Partition.distincts n)
      have hdist_sub : (pre2Image n).filter (fun m => m.Nodup) ⊆
          distSrc.image (fun lam => pre2 lam.parts) := by
        intro m hm
        rw [Finset.mem_filter] at hm
        rcases Finset.mem_image.mp hm.1 with ⟨lam, _, rfl⟩
        refine Finset.mem_image.mpr ⟨lam, ?_, rfl⟩
        rcases nodup_pre2_cases hm.2 with hnd | ⟨a, ha⟩
        · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnd⟩)
        · apply Finset.mem_insert.mpr
          left
          apply Nat.Partition.ext
          rw [ha]
          have hsum := lam.parts_sum
          rw [ha] at hsum
          change (a ::ₘ {a}).sum = n at hsum
          simp only [Multiset.sum_cons, Multiset.sum_singleton] at hsum
          have hak : a = k := by omega
          subst hak
          rfl
      have hdist_ub : ((pre2Image n).filter (fun m => m.Nodup)).card ≤
          (Nat.Partition.distincts n).card + 1 := by
        calc ((pre2Image n).filter (fun m => m.Nodup)).card
            ≤ (distSrc.image (fun lam => pre2 lam.parts)).card := Finset.card_le_card hdist_sub
          _ ≤ distSrc.card := Finset.card_image_le
          _ ≤ (Nat.Partition.distincts n).card + 1 := Finset.card_insert_le _ _
      have heuler := Nat.Partition.card_odds_eq_card_distincts n
      omega
    · -- `n` is odd: no `{a, a}` partition exists!
      have hodd_sub : (Nat.Partition.odds n).image (fun lam => pre2 lam.parts) ⊆
          (pre2Image n).filter (fun m => ∀ x ∈ m, Odd x) := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨lam, hodd, rfl⟩
        rw [Finset.mem_filter]
        simp only [Nat.Partition.odds, Nat.Partition.restricted, Finset.mem_filter,
          Finset.mem_univ, true_and] at hodd
        exact ⟨Finset.mem_image.mpr ⟨lam, Finset.mem_univ _, rfl⟩,
          pre2_all_odd (fun x hx => Nat.not_even_iff_odd.mp (hodd x hx))⟩
      have hodd_lb : (Nat.Partition.odds n).card ≤
          ((pre2Image n).filter (fun m => ∀ x ∈ m, Odd x)).card := by
        calc (Nat.Partition.odds n).card
            = ((Nat.Partition.odds n).image (fun lam => pre2 lam.parts)).card :=
              (Finset.card_image_of_injective _ (pre2_partition_injective n)).symm
          _ ≤ ((pre2Image n).filter (fun m => ∀ x ∈ m, Odd x)).card :=
              Finset.card_le_card hodd_sub
      have hdist_sub : (pre2Image n).filter (fun m => m.Nodup) ⊆
          (Nat.Partition.distincts n).image (fun lam => pre2 lam.parts) := by
        intro m hm
        rw [Finset.mem_filter] at hm
        rcases Finset.mem_image.mp hm.1 with ⟨lam, _, rfl⟩
        refine Finset.mem_image.mpr ⟨lam, ?_, rfl⟩
        rcases nodup_pre2_cases hm.2 with hnd | ⟨a, ha⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnd⟩
        · exfalso
          have hsum := lam.parts_sum
          rw [ha] at hsum
          change (a ::ₘ {a}).sum = n at hsum
          simp only [Multiset.sum_cons, Multiset.sum_singleton] at hsum
          exact heven ⟨a, hsum.symm⟩
      have hdist_ub : ((pre2Image n).filter (fun m => m.Nodup)).card ≤
          (Nat.Partition.distincts n).card := by
        calc ((pre2Image n).filter (fun m => m.Nodup)).card
            ≤ ((Nat.Partition.distincts n).image (fun lam => pre2 lam.parts)).card :=
              Finset.card_le_card hdist_sub
          _ ≤ (Nat.Partition.distincts n).card := Finset.card_image_le
      have heuler := Nat.Partition.card_odds_eq_card_distincts n
      omega

end OMA.P_arxiv_2408_13346

theorem OMA.solution : type_of% @OMA.S_arxiv_2408_13346.main :=
  OMA.P_arxiv_2408_13346.main_proof
