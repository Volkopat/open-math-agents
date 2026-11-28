import OMAStatements.S_oeis_a321775

namespace OMA.S_oeis_a321775

open PowerSeries Finset




section generic

variable {k n : ℕ}

/-- The multiplicity of the value at position i. -/
def mult (c : Fin k → Fin (n + 1)) (i : Fin k) : ℕ := (univ.filter (fun j => c j = c i)).card

/-- Distinct values occur with distinct multiplicities. -/
def DM (c : Fin k → Fin (n + 1)) : Prop := ∀ i j, c i ≠ c j → mult c i ≠ mult c j

instance (c : Fin k → Fin (n + 1)) : Decidable (DM c) := by unfold DM mult; infer_instance

lemma mult_pos (c : Fin k → Fin (n + 1)) (i : Fin k) : 0 < mult c i :=
  Finset.card_pos.mpr ⟨i, by simp⟩

lemma mult_le (c : Fin k → Fin (n + 1)) (i : Fin k) : mult c i ≤ k := by
  unfold mult
  calc (univ.filter (fun j => c j = c i)).card ≤ (univ : Finset (Fin k)).card :=
        Finset.card_filter_le _ _
    _ = k := by simp

/-- The multiplicities of the distinct values sum to k. -/
lemma sum_mult_image (c : Fin k → Fin (n + 1)) (h : DM c) : ∑ s ∈ univ.image (mult c), s = k := by
  have h1 : ∑ v ∈ univ.image c, (univ.filter (fun i => c i = v)).card = k := by
    rw [← Finset.card_eq_sum_card_image]
    simp
  have h2 : univ.image (mult c) =
      (univ.image c).image (fun v => (univ.filter (fun i => c i = v)).card) := by
    rw [Finset.image_image]
    rfl
  rw [h2, Finset.sum_image]
  · exact h1
  · intro v hv w hw hvw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
    by_contra hne
    exact h i j hne hvw

lemma mult_comp {r : ℕ} (m : Fin r → ℕ) (β : Fin k → Fin r) (v : Fin r → Fin (n + 1))
    (hβ : ∀ j, (univ.filter (fun i => β i = j)).card = m j) (hv : Function.Injective v)
    (i : Fin k) : mult (v ∘ β) i = m (β i) := by
  unfold mult
  rw [← hβ (β i)]
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and, Function.comp]
  exact hv.eq_iff

lemma sum_comp {r : ℕ} (m : Fin r → ℕ) (β : Fin k → Fin r) (v : Fin r → Fin (n + 1))
    (hβ : ∀ j, (univ.filter (fun i => β i = j)).card = m j) :
    ∑ i, ((v ∘ β) i).val = ∑ j, m j * (v j).val := by
  rw [← Finset.sum_fiberwise univ β (fun i => ((v ∘ β) i).val)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have e : ∀ i ∈ univ.filter (fun i => β i = j), ((v ∘ β) i).val = (v j).val := by
    intro i hi
    simp only [Function.comp, (Finset.mem_filter.mp hi).2]
  rw [Finset.sum_congr rfl e, Finset.sum_const, smul_eq_mul, hβ j]

/-- Compositions with multiplicity set the image of m, counted by fibre maps and value maps. -/
lemma card_D {r : ℕ} (m : Fin r → ℕ) (hm : Function.Injective m) (hpos : ∀ j, 0 < m j) :
    ((univ : Finset (Fin k → Fin (n + 1))).filter (fun c => (∀ i, 0 < (c i).val) ∧
      ∑ i, (c i).val = n ∧ DM c ∧ univ.image (mult c) = univ.image m)).card =
    ((univ : Finset (Fin k → Fin r)).filter
      (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = m j)).card *
    ((univ : Finset (Fin r → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, m j * (v j).val = n)).card := by
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij (fun p _ => p.2 ∘ p.1) ?_ ?_ ?_
  · rintro ⟨β, v⟩ hp
    simp only [mem_product, mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨hβ, hvinj, hvpos, hvsum⟩ := hp
    have hmult := mult_comp m β v hβ hvinj
    refine ⟨fun i => hvpos _, by rw [sum_comp m β v hβ]; exact hvsum, ?_, ?_⟩
    · intro i j hne heq
      rw [hmult, hmult] at heq
      exact hne (by simp only [Function.comp, hm heq])
    · ext s
      simp only [mem_image, mem_univ, true_and, hmult]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨β i, rfl⟩
      · rintro ⟨j, rfl⟩
        have hne : (univ.filter (fun i => β i = j)).Nonempty := by
          rw [← Finset.card_pos, hβ j]
          exact hpos j
        obtain ⟨i, hi⟩ := hne
        exact ⟨i, by rw [(Finset.mem_filter.mp hi).2]⟩
  · rintro ⟨β, v⟩ hp ⟨β', v'⟩ hp' heq
    simp only [mem_product, mem_filter, mem_univ, true_and] at hp hp'
    simp only at heq
    have hb : β = β' := by
      funext i
      apply hm
      rw [← mult_comp m β v hp.1 hp.2.1 i, ← mult_comp m β' v' hp'.1 hp'.2.1 i, heq]
    subst hb
    have hv : v = v' := by
      funext j
      have hne : (univ.filter (fun i => β i = j)).Nonempty := by
        rw [← Finset.card_pos, hp.1 j]
        exact hpos j
      obtain ⟨i, hi⟩ := hne
      have e := congrFun heq i
      simp only [Function.comp, (Finset.mem_filter.mp hi).2] at e
      exact e
    rw [hv]
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    obtain ⟨hpos', hsum, hdm, himg⟩ := hc
    have h1 : ∀ i, ∃ j, m j = mult c i := by
      intro i
      have : mult c i ∈ univ.image m := by
        rw [← himg]
        exact Finset.mem_image_of_mem _ (mem_univ i)
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp this
      exact ⟨j, hj⟩
    have h2 : ∀ j, ∃ i, mult c i = m j := by
      intro j
      have : m j ∈ univ.image (mult c) := by
        rw [himg]
        exact Finset.mem_image_of_mem _ (mem_univ j)
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp this
      exact ⟨i, hi⟩
    choose β hβ using h1
    choose rep hrep using h2
    have hcv : ∀ i, c (rep (β i)) = c i := by
      intro i
      by_contra hne
      exact hdm _ _ hne (by rw [hrep, hβ])
    have hcard : ∀ j, (univ.filter (fun i => β i = j)).card = m j := by
      intro j
      have e : univ.filter (fun i => β i = j) = univ.filter (fun i => c i = c (rep j)) := by
        ext i
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro h
          rw [← hcv i, h]
        · intro h
          apply hm
          rw [hβ, ← hrep j]
          unfold mult
          rw [h]
      rw [e]
      exact hrep j
    refine ⟨(β, fun j => c (rep j)), ?_, ?_⟩
    · simp only [mem_product, mem_filter, mem_univ, true_and]
      refine ⟨hcard, fun j j' hjj => ?_, fun j => hpos' _, ?_⟩
      · have hjj' : c (rep j) = c (rep j') := hjj
        apply hm
        rw [← hrep j, ← hrep j']
        unfold mult
        rw [hjj']
      · have hs := sum_comp m β (fun j => c (rep j)) hcard
        have e : (fun j => c (rep j)) ∘ β = c := funext hcv
        rw [e] at hs
        rw [← hs]
        exact hsum
    · funext i
      exact hcv i

end generic

/-- Sums of x^(m t) over t >= 1. -/
def P (m : ℕ) : ℚ⟦X⟧ := PowerSeries.mk (fun t => if 0 < t ∧ m ∣ t then 1 else 0)

lemma hP (m : ℕ) (hm : 0 < m) : (1 - X ^ m) * P m = X ^ m := by
  ext t
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_X_pow]
  simp only [P, coeff_mk]
  by_cases h1 : m ≤ t
  · rw [if_pos h1]
    obtain ⟨u, rfl⟩ : ∃ u, t = u + m := ⟨t - m, by omega⟩
    rw [show u + m - m = u by omega]
    by_cases hu : u = 0
    · subst hu
      simp [hm]
    · rw [if_neg (by omega : ¬ (u + m = m))]
      have hd : m ∣ u + m ↔ m ∣ u := Nat.dvd_add_self_right
      by_cases h2 : m ∣ u
      · rw [if_pos ⟨by omega, hd.2 h2⟩, if_pos ⟨by omega, h2⟩, sub_self]
      · rw [if_neg (fun h => h2 (hd.1 h.2)), if_neg (fun h => h2 h.2), sub_self]
  · rw [if_neg h1, sub_zero, if_neg (by omega : ¬ (t = m))]
    rw [if_neg]
    rintro ⟨h0, hd⟩
    exact h1 (Nat.le_of_dvd h0 hd)

/-- Pairs (v0, v1) of positive integers with a v0 + b v1 = t. -/
def U2 (a b t : ℕ) : Finset (ℕ × ℕ) :=
  ((range (t + 1)) ×ˢ (range (t + 1))).filter (fun p => 0 < p.1 ∧ 0 < p.2 ∧ a * p.1 + b * p.2 = t)

lemma coeff_PP (a b t : ℕ) (ha : 0 < a) (hb : 0 < b) :
    coeff t (P a * P b) = ((U2 a b t).card : ℚ) := by
  rw [coeff_mul]
  have e : ∀ p ∈ antidiagonal t, coeff p.1 (P a) * coeff p.2 (P b) =
      if (0 < p.1 ∧ a ∣ p.1) ∧ (0 < p.2 ∧ b ∣ p.2) then 1 else 0 := by
    intro p _
    simp only [P, coeff_mk]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl e, Finset.sum_boole]
  congr 1
  refine Finset.card_bij (fun p _ => (p.1 / a, p.2 / b)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨hxy, ⟨hx, ⟨u, rfl⟩⟩, ⟨hy, ⟨w, rfl⟩⟩⟩ := hp
    simp only [U2, mem_filter, mem_product, mem_range]
    rw [Nat.mul_div_cancel_left u ha, Nat.mul_div_cancel_left w hb]
    refine ⟨⟨?_, ?_⟩, ?_, ?_, hxy⟩
    · nlinarith
    · nlinarith
    · exact Nat.pos_of_ne_zero (fun h => by simp [h] at hx)
    · exact Nat.pos_of_ne_zero (fun h => by simp [h] at hy)
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
    simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp hp'
    obtain ⟨-, ⟨-, ⟨u, rfl⟩⟩, ⟨-, ⟨w, rfl⟩⟩⟩ := hp
    obtain ⟨-, ⟨-, ⟨u', rfl⟩⟩, ⟨-, ⟨w', rfl⟩⟩⟩ := hp'
    simp only [Prod.mk.injEq, Nat.mul_div_cancel_left _ ha, Nat.mul_div_cancel_left _ hb] at h
    rw [h.1, h.2]
  · rintro ⟨u, w⟩ hq
    simp only [U2, mem_filter, mem_product, mem_range] at hq
    obtain ⟨-, hu, hw, hs⟩ := hq
    refine ⟨(a * u, b * w), ?_, ?_⟩
    · simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
      exact ⟨hs, ⟨Nat.mul_pos ha hu, dvd_mul_right a u⟩, ⟨Nat.mul_pos hb hw, dvd_mul_right b w⟩⟩
    · simp only [Nat.mul_div_cancel_left _ ha, Nat.mul_div_cancel_left _ hb]

/-- Injective value pairs with a v0 + b v1 = n: all pairs minus the diagonal. -/
lemma card_V2 (a b n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((((univ : Finset (Fin 2 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![a, b] j * (v j).val = n)).card : ℕ) : ℚ) =
    coeff n (P a * P b) - coeff n (P (a + b)) := by
  rw [coeff_PP a b n ha hb]
  simp only [P, coeff_mk]
  have hsplit : (U2 a b n).card = ((U2 a b n).filter (fun p => p.1 ≠ p.2)).card +
      ((U2 a b n).filter (fun p => p.1 = p.2)).card := by
    have := Finset.card_filter_add_card_filter_not (s := U2 a b n) (fun p => p.1 = p.2)
    simp only [ne_eq] at this ⊢
    omega
  have hdiag : ((U2 a b n).filter (fun p => p.1 = p.2)).card =
      if 0 < n ∧ a + b ∣ n then 1 else 0 := by
    split_ifs with h
    · obtain ⟨hn, u, hu⟩ := h
      have hu0 : 0 < u := by
        rcases Nat.eq_zero_or_pos u with h0 | h0
        · rw [h0, mul_zero] at hu
          omega
        · exact h0
      rw [Finset.card_eq_one]
      refine ⟨(u, u), ?_⟩
      ext ⟨x, y⟩
      simp only [U2, mem_filter, mem_product, mem_range, mem_singleton, Prod.mk.injEq]
      constructor
      · intro hxy
        obtain ⟨⟨⟨-, -⟩, -, -, hs⟩, he⟩ := hxy
        rw [← he] at hs
        have h1 : (a + b) * x = (a + b) * u := by rw [← hu]; linarith
        have h2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < a + b) h1
        exact ⟨h2, he ▸ h2⟩
      · intro hxy
        obtain ⟨hx, hy⟩ := hxy
        rw [hx, hy]
        exact ⟨⟨⟨by nlinarith, by nlinarith⟩, hu0, hu0, by rw [hu]; ring⟩, rfl⟩
    · rw [Finset.card_eq_zero]
      ext ⟨x, y⟩
      simp only [U2, mem_filter, mem_product, mem_range, Finset.notMem_empty, iff_false, not_and]
      intro hA hxy
      obtain ⟨-, hx, -, hs⟩ := hA
      rw [← hxy] at hs
      exact h ⟨by nlinarith, x, by rw [← hs]; ring⟩
  have hbij : ((univ : Finset (Fin 2 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![a, b] j * (v j).val = n)).card =
      ((U2 a b n).filter (fun p => p.1 ≠ p.2)).card := by
    refine Finset.card_bij (fun v _ => ((v 0).val, (v 1).val)) ?_ ?_ ?_
    · intro v hv
      simp only [mem_filter, mem_univ, true_and, Fin.sum_univ_two] at hv
      obtain ⟨hinj, hpos, hs⟩ := hv
      simp only [U2, mem_filter, mem_product, mem_range]
      refine ⟨⟨⟨(v 0).isLt, (v 1).isLt⟩, hpos 0, hpos 1, by simpa using hs⟩, ?_⟩
      intro e
      exact absurd (hinj (Fin.ext e)) (by decide)
    · intro v _ v' _ h
      simp only [Prod.mk.injEq] at h
      funext j
      fin_cases j
      · exact Fin.ext h.1
      · exact Fin.ext h.2
    · rintro ⟨x, y⟩ hq
      simp only [U2, mem_filter, mem_product, mem_range] at hq
      obtain ⟨⟨⟨hx, hy⟩, hx0, hy0, hs⟩, hne⟩ := hq
      refine ⟨![⟨x, hx⟩, ⟨y, hy⟩], ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and, Fin.sum_univ_two]
      refine ⟨?_, fun j => ?_, by simpa using hs⟩
      · intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact absurd (congrArg Fin.val hij) (by simpa using hne)
        · exact absurd (congrArg Fin.val hij) (by simpa using fun h => hne h.symm)
        · rfl
      · fin_cases j
        · simpa using hx0
        · simpa using hy0
  rw [hbij]
  have hdiag' : ((((U2 a b n).filter (fun p => p.1 = p.2)).card : ℕ) : ℚ) =
      if 0 < n ∧ a + b ∣ n then 1 else 0 := by
    rw [hdiag]
    split_ifs <;> simp
  rw [← hdiag', hsplit]
  push_cast
  ring

/-- The value maps for one value: v 0 = n / 5. -/
lemma card_V1 (n : ℕ) :
    ((((univ : Finset (Fin 1 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![5] j * (v j).val = n)).card : ℕ) : ℚ) = coeff n (P 5) := by
  simp only [P, coeff_mk]
  split_ifs with h
  · obtain ⟨hn, u, hu⟩ := h
    rw [Nat.cast_eq_one, Finset.card_eq_one]
    refine ⟨fun _ => ⟨u, by omega⟩, ?_⟩
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.sum_univ_one]
    constructor
    · rintro ⟨-, -, hs⟩
      funext j
      rw [Subsingleton.elim j 0]
      apply Fin.ext
      simp only [Matrix.cons_val_zero] at hs
      show (v 0).val = u
      omega
    · rintro rfl
      refine ⟨fun x y _ => Subsingleton.elim x y, fun j => ?_, ?_⟩
      · simp only
        omega
      · simp only [Matrix.cons_val_zero]
        omega
  · rw [Nat.cast_eq_zero, Finset.card_eq_zero]
    ext v
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and,
      Fin.sum_univ_one, Matrix.cons_val_zero]
    intro _ hpos hs
    exact h ⟨by have := hpos 0; omega, v 0, hs.symm⟩

lemma types : ∀ T ∈ (range 6).powerset, 0 ∉ T → ∑ s ∈ T, s = 5 →
    T = {5} ∨ T = {4, 1} ∨ T = {3, 2} := by
  decide

lemma img5 : (univ.image ![5] : Finset ℕ) = {5} := by decide
lemma img41 : (univ.image ![4, 1] : Finset ℕ) = {4, 1} := by decide
lemma img32 : (univ.image ![3, 2] : Finset ℕ) = {3, 2} := by decide

lemma B5 : ((univ : Finset (Fin 5 → Fin 1)).filter
    (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![5] j)).card = 1 := by decide
lemma B41 : ((univ : Finset (Fin 5 → Fin 2)).filter
    (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![4, 1] j)).card = 5 := by decide
lemma B32 : ((univ : Finset (Fin 5 → Fin 2)).filter
    (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![3, 2] j)).card = 10 := by decide

/-- The compositions with a given multiplicity set. -/
def D (n : ℕ) (T : Finset ℕ) : Finset (Fin 5 → Fin (n + 1)) :=
  (univ : Finset (Fin 5 → Fin (n + 1))).filter (fun c => (∀ i, 0 < (c i).val) ∧
    ∑ i, (c i).val = n ∧ DM c ∧ univ.image (mult c) = T)

lemma a_split (n : ℕ) : a n = (D n {5}).card + (D n {4, 1}).card + (D n {3, 2}).card := by
  have hsplit : (univ : Finset (Fin 5 → Fin (n + 1))).filter good =
      D n {5} ∪ D n {4, 1} ∪ D n {3, 2} := by
    ext c
    simp only [D, mem_union, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hdm : DM c := h3
      have hT := types (univ.image (mult c))
        (by
          rw [Finset.mem_powerset]
          intro s hs
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
          exact Finset.mem_range.mpr (by have := mult_le c i; omega))
        (by
          intro h0
          obtain ⟨i, -, hi⟩ := Finset.mem_image.mp h0
          exact absurd hi (mult_pos c i).ne')
        (sum_mult_image c hdm)
      rcases hT with hT | hT | hT
      · exact Or.inl (Or.inl ⟨h1, h2, hdm, hT⟩)
      · exact Or.inl (Or.inr ⟨h1, h2, hdm, hT⟩)
      · exact Or.inr ⟨h1, h2, hdm, hT⟩
    · rintro ((⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩) | ⟨h1, h2, h3, -⟩) <;> exact ⟨h1, h2, h3⟩
  have hd : ∀ T T' : Finset ℕ, T ≠ T' → Disjoint (D n T) (D n T') := by
    intro T T' hTT
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [D, mem_filter, mem_univ, true_and] at hc hc'
    exact hTT (hc.2.2.2.symm.trans hc'.2.2.2)
  unfold a
  rw [hsplit, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  all_goals first
    | exact hd _ _ (by decide)
    | (rw [Finset.disjoint_union_left]; exact ⟨hd _ _ (by decide), hd _ _ (by decide)⟩)

lemma cD5 (n : ℕ) : (D n {5}).card =
    ((univ : Finset (Fin 5 → Fin 1)).filter
      (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![5] j)).card *
    ((univ : Finset (Fin 1 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![5] j * (v j).val = n)).card := by
  unfold D
  rw [← img5]
  exact card_D ![5] (by decide) (by decide)

lemma cD41 (n : ℕ) : (D n {4, 1}).card =
    ((univ : Finset (Fin 5 → Fin 2)).filter
      (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![4, 1] j)).card *
    ((univ : Finset (Fin 2 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![4, 1] j * (v j).val = n)).card := by
  unfold D
  rw [← img41]
  exact card_D ![4, 1] (by decide) (by decide)

lemma cD32 (n : ℕ) : (D n {3, 2}).card =
    ((univ : Finset (Fin 5 → Fin 2)).filter
      (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![3, 2] j)).card *
    ((univ : Finset (Fin 2 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![3, 2] j * (v j).val = n)).card := by
  unfold D
  rw [← img32]
  exact card_D ![3, 2] (by decide) (by decide)

/-- The g.f. of the counts: -14 P 5 + 5 P 4 P 1 + 10 P 3 P 2. -/
lemma gf_P : PowerSeries.mk (fun n => (a n : ℚ)) =
    C (-14 : ℚ) * P 5 + C (5 : ℚ) * (P 4 * P 1) + C (10 : ℚ) * (P 3 * P 2) := by
  ext n
  rw [coeff_mk, a_split, cD5, cD41, cD32, B5, B41, B32]
  push_cast
  rw [card_V1, card_V2 4 1 n (by norm_num) (by norm_num), card_V2 3 2 n (by norm_num) (by norm_num)]
  simp only [map_add, coeff_C_mul]
  norm_num
  ring

lemma a_zero : a 0 = 0 := by decide

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
      X ^ 5 * (1 + 6 * X + 21 * X ^ 2 + 35 * X ^ 3 + 49 * X ^ 4 + 34 * X ^ 5 + 29 * X ^ 6) := by
  have hA : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      PowerSeries.mk (fun n => (a n : ℚ)) := by
    ext n
    simp only [coeff_mk]
    split_ifs with h
    · subst h
      rw [a_zero]
      simp
    · rfl
  rw [hA, gf_P]
  simp only [map_neg, map_ofNat]
  have h5 := hP 5 (by norm_num)
  have h4 := hP 4 (by norm_num)
  have h3 := hP 3 (by norm_num)
  have h2 := hP 2 (by norm_num)
  have h1 := hP 1 (by norm_num)
  linear_combination
    (-14 * ((1 - X) * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2))) * h5 +
    (5 * ((1 + X + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) * ((1 - X ^ 1) * P 1)) * h4 +
    (5 * ((1 + X + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) * X ^ 4) * h1 +
    (10 * ((1 + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) * ((1 - X ^ 2) * P 2)) * h3 +
    (10 * ((1 + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) * X ^ 3) * h2

/-- Barker's recurrence, for n > 15 (the coefficient identity of the g.f. above degree 11). -/
theorem recur : ∀ n : ℕ, 15 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) + a (n - 4) + 2 * a (n - 5) +
    2 * a (n - 6) + a (n - 7) - a (n - 9) - a (n - 10) - a (n - 11) := by
  intro n hn
  have h := congrArg (coeff n) gf
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) *
      (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) = A + A * X ^ 1 + A * X ^ 2 - A * X ^ 4 - A * X ^ 5 * C 2 -
      A * X ^ 6 * C 2 - A * X ^ 7 + A * X ^ 9 + A * X ^ 10 + A * X ^ 11 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2]
    ring
  have e2 : (X ^ 5 * (1 + 6 * X + 21 * X ^ 2 + 35 * X ^ 3 + 49 * X ^ 4 + 34 * X ^ 5 + 29 * X ^ 6) :
      ℚ⟦X⟧) = X ^ 5 + X ^ 6 * C 6 + X ^ 7 * C 21 + X ^ 8 * C 35 + X ^ 9 * C 49 + X ^ 10 * C 34 +
      X ^ 11 * C 29 := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6, show (C (21 : ℚ) : ℚ⟦X⟧) = 21 from map_ofNat C 21,
      show (C (35 : ℚ) : ℚ⟦X⟧) = 35 from map_ofNat C 35, show (C (49 : ℚ) : ℚ⟦X⟧) = 49 from map_ofNat C 49,
      show (C (34 : ℚ) : ℚ⟦X⟧) = 34 from map_ofNat C 34, show (C (29 : ℚ) : ℚ⟦X⟧) = 29 from map_ofNat C 29]
    ring
  rw [e1, e2] at h
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 16 := ⟨n - 16, by omega⟩
  simp only [show 1 ≤ m + 16 by omega, show 2 ≤ m + 16 by omega, show 4 ≤ m + 16 by omega,
    show 5 ≤ m + 16 by omega, show 6 ≤ m + 16 by omega, show 7 ≤ m + 16 by omega,
    show 9 ≤ m + 16 by omega, show 10 ≤ m + 16 by omega, show 11 ≤ m + 16 by omega,
    show ¬ (m + 16 = 0) by omega, show ¬ (m + 16 - 1 = 0) by omega, show ¬ (m + 16 - 2 = 0) by omega,
    show ¬ (m + 16 - 4 = 0) by omega, show ¬ (m + 16 - 5 = 0) by omega,
    show ¬ (m + 16 - 6 = 0) by omega, show ¬ (m + 16 - 7 = 0) by omega,
    show ¬ (m + 16 - 9 = 0) by omega, show ¬ (m + 16 - 10 = 0) by omega,
    show ¬ (m + 16 - 11 = 0) by omega, show ¬ (m + 16 = 5) by omega, show ¬ (m + 16 = 6) by omega,
    show ¬ (m + 16 = 7) by omega, show ¬ (m + 16 = 8) by omega, show ¬ (m + 16 = 9) by omega,
    show ¬ (m + 16 = 10) by omega, show ¬ (m + 16 = 11) by omega, if_true, if_false] at h
  have hq : (a (m + 16) : ℚ) = -a (m + 16 - 1) - a (m + 16 - 2) + a (m + 16 - 4) +
      2 * a (m + 16 - 5) + 2 * a (m + 16 - 6) + a (m + 16 - 7) - a (m + 16 - 9) -
      a (m + 16 - 10) - a (m + 16 - 11) := by
    linear_combination h
  exact_mod_cast hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
        X ^ 5 * (1 + 6 * X + 21 * X ^ 2 + 35 * X ^ 3 + 49 * X ^ 4 + 34 * X ^ 5 + 29 * X ^ 6) ∧
    ∀ n : ℕ, 15 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) + a (n - 4) + 2 * a (n - 5) +
      2 * a (n - 6) + a (n - 7) - a (n - 9) - a (n - 10) - a (n - 11) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a321775

theorem OMA.solution : type_of% @OMA.S_oeis_a321775.main :=
  OMA.S_oeis_a321775.conjecture
