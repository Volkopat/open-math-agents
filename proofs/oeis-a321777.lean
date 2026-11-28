import OMAStatements.S_oeis_a321777

namespace OMA.S_oeis_a321777

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

lemma card_V1 (m n : ℕ) (hm : 0 < m) :
    ((((univ : Finset (Fin 1 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![m] j * (v j).val = n)).card : ℕ) : ℚ) = coeff n (P m) := by
  simp only [P, coeff_mk]
  split_ifs with h
  · obtain ⟨hn, u, hu⟩ := h
    have hu0 : 0 < u := by
      rcases Nat.eq_zero_or_pos u with h0 | h0
      · rw [h0, mul_zero] at hu
        omega
      · exact h0
    rw [Nat.cast_eq_one, Finset.card_eq_one]
    refine ⟨fun _ => ⟨u, by nlinarith⟩, ?_⟩
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.sum_univ_one, Matrix.cons_val_zero]
    constructor
    · rintro ⟨-, -, hs⟩
      funext j
      rw [Subsingleton.elim j 0]
      apply Fin.ext
      show (v 0).val = u
      exact Nat.eq_of_mul_eq_mul_left hm (hs.trans hu)
    · rintro rfl
      exact ⟨fun x y _ => Subsingleton.elim x y, fun j => hu0, hu.symm⟩
  · rw [Nat.cast_eq_zero, Finset.card_eq_zero]
    ext v
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and,
      Fin.sum_univ_one, Matrix.cons_val_zero]
    intro _ hpos hs
    exact h ⟨by have := hpos 0; nlinarith, (v 0).val, hs.symm⟩

/-- Triples of positive integers with a v0 + b v1 + c v2 = t. -/
def U3 (a b c t : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (t + 1)) ×ˢ (range (t + 1)) ×ˢ (range (t + 1))).filter
    (fun p => 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧ a * p.1 + b * p.2.1 + c * p.2.2 = t)

lemma coeff_PPP (a b c t : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    coeff t (P a * P b * P c) = ((U3 a b c t).card : ℚ) := by
  rw [coeff_mul]
  have e : ∀ q ∈ antidiagonal t, coeff q.1 (P a * P b) * coeff q.2 (P c) =
      (((U3 a b c t).filter (fun p => (a * p.1 + b * p.2.1, c * p.2.2) = q)).card : ℚ) := by
    rintro ⟨q1, q2⟩ hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    simp only at hq ⊢
    rw [coeff_PP a b q1 ha hb]
    simp only [P, coeff_mk]
    split_ifs with h
    · rw [mul_one]
      obtain ⟨h0, w, hw⟩ := h
      have hw0 : 0 < w := by
        rcases Nat.eq_zero_or_pos w with h1 | h1
        · rw [h1, mul_zero] at hw
          omega
        · exact h1
      congr 1
      refine Finset.card_bij (fun p _ => (p.1, p.2, w)) ?_ ?_ ?_
      · rintro ⟨x, y⟩ hp
        simp only [U2, mem_filter, mem_product, mem_range] at hp
        simp only [U3, mem_filter, mem_product, mem_range, Prod.mk.injEq]
        obtain ⟨⟨hx, hy⟩, hx0, hy0, hs⟩ := hp
        exact ⟨⟨⟨by omega, by omega, by nlinarith⟩, hx0, hy0, hw0, by linarith⟩, hs, hw.symm⟩
      · rintro ⟨x, y⟩ _ ⟨x', y'⟩ _ h
        simp only [Prod.mk.injEq] at h
        rw [h.1, h.2.1]
      · rintro ⟨x, y, z⟩ hp
        simp only [U3, mem_filter, mem_product, mem_range, Prod.mk.injEq] at hp
        obtain ⟨⟨⟨hx, hy, hz⟩, hx0, hy0, hz0, hs⟩, hq1, hq2⟩ := hp
        refine ⟨(x, y), ?_, ?_⟩
        · simp only [U2, mem_filter, mem_product, mem_range]
          exact ⟨⟨by nlinarith, by nlinarith⟩, hx0, hy0, hq1⟩
        · have hzw : z = w := Nat.eq_of_mul_eq_mul_left hc (hq2.trans hw)
          simp only [hzw]
    · rw [mul_zero]
      symm
      rw [Nat.cast_eq_zero, Finset.card_eq_zero]
      ext ⟨x, y, z⟩
      simp only [U3, mem_filter, mem_product, mem_range, Finset.notMem_empty, iff_false, not_and,
        Prod.mk.injEq]
      intro hA _ hq2
      obtain ⟨-, -, -, hz0, -⟩ := hA
      exact h ⟨by rw [← hq2]; exact Nat.mul_pos hc hz0, z, hq2.symm⟩
  rw [Finset.sum_congr rfl e]
  norm_cast
  exact (Finset.card_eq_sum_card_fiberwise
    (f := fun p : ℕ × ℕ × ℕ => (a * p.1 + b * p.2.1, c * p.2.2))
    (fun p hp => by
      simp only [Finset.mem_coe, U3, mem_filter, mem_product, mem_range] at hp
      simp only [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal]
      linarith)).symm

/-- Injective value triples: all triples minus the three coincidences plus twice the diagonal. -/
lemma card_V3 (a b c n : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((((univ : Finset (Fin 3 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![a, b, c] j * (v j).val = n)).card : ℕ) : ℚ) =
    coeff n (P a * P b * P c) - coeff n (P (a + b) * P c) - coeff n (P (a + c) * P b) -
      coeff n (P a * P (b + c)) + 2 * coeff n (P (a + b + c)) := by
  rw [coeff_PPP a b c n ha hb hc, coeff_PP (a + b) c n (by omega) hc,
    coeff_PP (a + c) b n (by omega) hb, coeff_PP a (b + c) n ha (by omega)]
  simp only [P, coeff_mk]
  have hV : ((univ : Finset (Fin 3 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![a, b, c] j * (v j).val = n)).card =
      ((U3 a b c n).filter (fun p => ¬ (p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2))).card := by
    refine Finset.card_bij (fun v _ => ((v 0).val, (v 1).val, (v 2).val)) ?_ ?_ ?_
    · intro v hv
      simp only [mem_filter, mem_univ, true_and, Fin.sum_univ_three] at hv
      obtain ⟨hinj, hpos, hs⟩ := hv
      simp only [U3, mem_filter, mem_product, mem_range]
      refine ⟨⟨⟨(v 0).isLt, (v 1).isLt, (v 2).isLt⟩, hpos 0, hpos 1, hpos 2, by simpa using hs⟩, ?_⟩
      rintro (e | e | e)
      · exact absurd (hinj (Fin.ext e)) (by decide)
      · exact absurd (hinj (Fin.ext e)) (by decide)
      · exact absurd (hinj (Fin.ext e)) (by decide)
    · intro v _ v' _ h
      simp only [Prod.mk.injEq] at h
      funext j
      fin_cases j
      · exact Fin.ext h.1
      · exact Fin.ext h.2.1
      · exact Fin.ext h.2.2
    · rintro ⟨x, y, z⟩ hq
      simp only [U3, mem_filter, mem_product, mem_range] at hq
      obtain ⟨⟨⟨hx, hy, hz⟩, hx0, hy0, hz0, hs⟩, hne⟩ := hq
      refine ⟨![⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩], ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and, Fin.sum_univ_three]
      refine ⟨?_, fun j => ?_, by simpa using hs⟩
      · intro i j hij
        have hv := congrArg Fin.val hij
        fin_cases i <;> fin_cases j <;> simp at hv ⊢ <;> omega
      · fin_cases j
        · simpa using hx0
        · simpa using hy0
        · simpa using hz0
  set S := U3 a b c n with hS
  have hsplit : S.card = (S.filter (fun p => ¬ (p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2))).card +
      (S.filter (fun p => p.1 = p.2.1) ∪ S.filter (fun p => p.1 = p.2.2) ∪
        S.filter (fun p => p.2.1 = p.2.2)).card := by
    have e : S.filter (fun p => p.1 = p.2.1) ∪ S.filter (fun p => p.1 = p.2.2) ∪
        S.filter (fun p => p.2.1 = p.2.2) = S.filter (fun p => p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2) := by
      ext p
      simp only [mem_union, mem_filter]
      tauto
    rw [e]
    have := Finset.card_filter_add_card_filter_not (s := S)
      (fun p : ℕ × ℕ × ℕ => p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2)
    omega
  have hT1 : S.filter (fun p => p.1 = p.2.1) ∩ S.filter (fun p => p.1 = p.2.2) =
      S.filter (fun p => p.1 = p.2.1 ∧ p.1 = p.2.2) := by
    ext p
    simp only [mem_inter, mem_filter]
    tauto
  have hT2 : (S.filter (fun p => p.1 = p.2.1) ∪ S.filter (fun p => p.1 = p.2.2)) ∩
      S.filter (fun p => p.2.1 = p.2.2) = S.filter (fun p => p.1 = p.2.1 ∧ p.1 = p.2.2) := by
    ext p
    simp only [mem_inter, mem_union, mem_filter]
    constructor
    · rintro ⟨(⟨h0, h1⟩ | ⟨h0, h1⟩), -, h2⟩
      · exact ⟨h0, h1, by omega⟩
      · exact ⟨h0, by omega, h1⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨Or.inl ⟨h0, h1⟩, h0, by omega⟩
  have hu1 := Finset.card_union_add_card_inter (S.filter (fun p => p.1 = p.2.1))
    (S.filter (fun p => p.1 = p.2.2))
  have hu2 := Finset.card_union_add_card_inter
    (S.filter (fun p => p.1 = p.2.1) ∪ S.filter (fun p => p.1 = p.2.2))
    (S.filter (fun p => p.2.1 = p.2.2))
  rw [hT1] at hu1
  rw [hT2] at hu2
  have h01 : (S.filter (fun p => p.1 = p.2.1)).card = (U2 (a + b) c n).card := by
    refine Finset.card_bij (fun p _ => (p.1, p.2.2)) ?_ ?_ ?_
    · rintro ⟨x, y, z⟩ hp
      simp only [hS, U3, U2, mem_filter, mem_product, mem_range] at hp ⊢
      obtain ⟨⟨⟨hx, hy, hz⟩, hx0, hy0, hz0, hs⟩, hxy⟩ := hp
      subst hxy
      exact ⟨⟨hx, hz⟩, hx0, hz0, by rw [← hs]; ring⟩
    · rintro ⟨x, y, z⟩ hp ⟨x', y', z'⟩ hp' h
      simp only [mem_filter] at hp hp'
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [← hp.2, ← hp'.2, h.1], h.2⟩
    · rintro ⟨x, z⟩ hq
      simp only [U2, mem_filter, mem_product, mem_range] at hq
      obtain ⟨⟨hx, hz⟩, hx0, hz0, hs⟩ := hq
      refine ⟨(x, x, z), ?_, rfl⟩
      simp only [hS, U3, mem_filter, mem_product, mem_range]
      exact ⟨⟨⟨hx, hx, hz⟩, hx0, hx0, hz0, by rw [← hs]; ring⟩, trivial⟩
  have h02 : (S.filter (fun p => p.1 = p.2.2)).card = (U2 (a + c) b n).card := by
    refine Finset.card_bij (fun p _ => (p.1, p.2.1)) ?_ ?_ ?_
    · rintro ⟨x, y, z⟩ hp
      simp only [hS, U3, U2, mem_filter, mem_product, mem_range] at hp ⊢
      obtain ⟨⟨⟨hx, hy, hz⟩, hx0, hy0, hz0, hs⟩, hxz⟩ := hp
      subst hxz
      exact ⟨⟨hx, hy⟩, hx0, hy0, by rw [← hs]; ring⟩
    · rintro ⟨x, y, z⟩ hp ⟨x', y', z'⟩ hp' h
      simp only [mem_filter] at hp hp'
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, h.2, by rw [← hp.2, ← hp'.2, h.1]⟩
    · rintro ⟨x, y⟩ hq
      simp only [U2, mem_filter, mem_product, mem_range] at hq
      obtain ⟨⟨hx, hy⟩, hx0, hy0, hs⟩ := hq
      refine ⟨(x, y, x), ?_, rfl⟩
      simp only [hS, U3, mem_filter, mem_product, mem_range]
      exact ⟨⟨⟨hx, hy, hx⟩, hx0, hy0, hx0, by rw [← hs]; ring⟩, trivial⟩
  have h12 : (S.filter (fun p => p.2.1 = p.2.2)).card = (U2 a (b + c) n).card := by
    refine Finset.card_bij (fun p _ => (p.1, p.2.1)) ?_ ?_ ?_
    · rintro ⟨x, y, z⟩ hp
      simp only [hS, U3, U2, mem_filter, mem_product, mem_range] at hp ⊢
      obtain ⟨⟨⟨hx, hy, hz⟩, hx0, hy0, hz0, hs⟩, hyz⟩ := hp
      subst hyz
      exact ⟨⟨hx, hy⟩, hx0, hy0, by rw [← hs]; ring⟩
    · rintro ⟨x, y, z⟩ hp ⟨x', y', z'⟩ hp' h
      simp only [mem_filter] at hp hp'
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, h.2, by rw [← hp.2, ← hp'.2, h.2]⟩
    · rintro ⟨x, y⟩ hq
      simp only [U2, mem_filter, mem_product, mem_range] at hq
      obtain ⟨⟨hx, hy⟩, hx0, hy0, hs⟩ := hq
      refine ⟨(x, y, y), ?_, rfl⟩
      simp only [hS, U3, mem_filter, mem_product, mem_range]
      exact ⟨⟨⟨hx, hy, hy⟩, hx0, hy0, hy0, by rw [← hs]; ring⟩, trivial⟩
  have hT : (S.filter (fun p => p.1 = p.2.1 ∧ p.1 = p.2.2)).card =
      if 0 < n ∧ a + b + c ∣ n then 1 else 0 := by
    split_ifs with h
    · obtain ⟨hn, u, hu⟩ := h
      have hu0 : 0 < u := by
        rcases Nat.eq_zero_or_pos u with h0 | h0
        · rw [h0, mul_zero] at hu
          omega
        · exact h0
      rw [Finset.card_eq_one]
      refine ⟨(u, u, u), ?_⟩
      ext ⟨x, y, z⟩
      simp only [hS, U3, mem_filter, mem_product, mem_range, mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨-, -, -, -, hs⟩, hxy, hxz⟩
        rw [← hxy, ← hxz] at hs
        have h1 : (a + b + c) * x = (a + b + c) * u := by rw [← hu]; linarith
        have h2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < a + b + c) h1
        exact ⟨h2, hxy ▸ h2, hxz ▸ h2⟩
      · rintro ⟨hx, hy, hz⟩
        rw [hx, hy, hz]
        exact ⟨⟨⟨by nlinarith, by nlinarith, by nlinarith⟩, hu0, hu0, hu0, by rw [hu]; ring⟩,
          rfl, rfl⟩
    · rw [Finset.card_eq_zero]
      ext ⟨x, y, z⟩
      simp only [hS, U3, mem_filter, mem_product, mem_range, Finset.notMem_empty, iff_false, not_and]
      intro hA hxy hxz
      obtain ⟨-, hx, -, -, hs⟩ := hA
      rw [← hxy, ← hxz] at hs
      exact h ⟨by nlinarith, x, by rw [← hs]; ring⟩
  rw [hV]
  have key : ((S.filter (fun p => ¬ (p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2))).card : ℚ) =
      S.card - (U2 (a + b) c n).card - (U2 (a + c) b n).card - (U2 a (b + c) n).card +
        2 * (S.filter (fun p => p.1 = p.2.1 ∧ p.1 = p.2.2)).card := by
    have : (S.filter (fun p => ¬ (p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2))).card +
        (U2 (a + b) c n).card + (U2 (a + c) b n).card + (U2 a (b + c) n).card =
        S.card + 2 * (S.filter (fun p => p.1 = p.2.1 ∧ p.1 = p.2.2)).card := by omega
    have hq : ((S.filter (fun p => ¬ (p.1 = p.2.1 ∨ p.1 = p.2.2 ∨ p.2.1 = p.2.2))).card : ℚ) +
        (U2 (a + b) c n).card + (U2 (a + c) b n).card + (U2 a (b + c) n).card =
        S.card + 2 * (S.filter (fun p => p.1 = p.2.1 ∧ p.1 = p.2.2)).card := by exact_mod_cast this
    linear_combination hq
  rw [key, hT, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  try ring

lemma types : ∀ T ∈ (range 8).powerset, 0 ∉ T → ∑ s ∈ T, s = 7 →
    T = {7} ∨ T = {6, 1} ∨ T = {5, 2} ∨ T = {4, 3} ∨ T = {4, 2, 1} := by
  decide +kernel

lemma img0 : (univ.image ![7] : Finset ℕ) = {7} := by decide
lemma img1 : (univ.image ![6, 1] : Finset ℕ) = {6, 1} := by decide
lemma img2 : (univ.image ![5, 2] : Finset ℕ) = {5, 2} := by decide
lemma img3 : (univ.image ![4, 3] : Finset ℕ) = {4, 3} := by decide
lemma img4 : (univ.image ![4, 2, 1] : Finset ℕ) = {4, 2, 1} := by decide

lemma B0 : ((univ : Finset (Fin 7 → Fin 1)).filter
    (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![7] j)).card = 1 := by
  decide +kernel
lemma B1 : ((univ : Finset (Fin 7 → Fin 2)).filter
    (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![6, 1] j)).card = 7 := by
  decide +kernel
lemma B2 : ((univ : Finset (Fin 7 → Fin 2)).filter
    (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![5, 2] j)).card = 21 := by
  decide +kernel
lemma B3 : ((univ : Finset (Fin 7 → Fin 2)).filter
    (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![4, 3] j)).card = 35 := by
  decide +kernel
lemma B4 : ((univ : Finset (Fin 7 → Fin 3)).filter
    (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![4, 2, 1] j)).card = 105 := by
  decide +kernel

/-- The compositions with a given multiplicity set. -/
def D (n : ℕ) (T : Finset ℕ) : Finset (Fin 7 → Fin (n + 1)) :=
  (univ : Finset (Fin 7 → Fin (n + 1))).filter (fun c => (∀ i, 0 < (c i).val) ∧
    ∑ i, (c i).val = n ∧ DM c ∧ univ.image (mult c) = T)

lemma a_split (n : ℕ) : a n = (D n {7}).card + (D n {6, 1}).card + (D n {5, 2}).card + (D n {4, 3}).card + (D n {4, 2, 1}).card := by
  have hsplit : (univ : Finset (Fin 7 → Fin (n + 1))).filter good = D n {7} ∪ D n {6, 1} ∪ D n {5, 2} ∪ D n {4, 3} ∪ D n {4, 2, 1} := by
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
      rcases hT with hT | hT | hT | hT | hT
      · exact Or.inl (Or.inl (Or.inl (Or.inl (⟨h1, h2, hdm, hT⟩))))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨h1, h2, hdm, hT⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨h1, h2, hdm, hT⟩))
      · exact Or.inl (Or.inr ⟨h1, h2, hdm, hT⟩)
      · exact Or.inr ⟨h1, h2, hdm, hT⟩
    · rintro ((((⟨h1, h2, h3, -⟩ | ⟨h1, h2, h3, -⟩) | ⟨h1, h2, h3, -⟩) | ⟨h1, h2, h3, -⟩) | ⟨h1, h2, h3, -⟩) <;> exact ⟨h1, h2, h3⟩
  have hd : ∀ T T' : Finset ℕ, T ≠ T' → Disjoint (D n T) (D n T') := by
    intro T T' hTT
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [D, mem_filter, mem_univ, true_and] at hc hc'
    exact hTT (hc.2.2.2.symm.trans hc'.2.2.2)
  unfold a
  rw [hsplit]
  repeat rw [Finset.card_union_of_disjoint]
  all_goals (try simp only [Finset.disjoint_union_left])
  all_goals repeat' (first | exact hd _ _ (by decide) | constructor)

lemma cD0 (n : ℕ) : (D n {7}).card =
    ((univ : Finset (Fin 7 → Fin 1)).filter
      (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![7] j)).card *
    ((univ : Finset (Fin 1 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![7] j * (v j).val = n)).card := by
  unfold D
  rw [← img0]
  exact card_D ![7] (by decide) (by decide)

lemma cD1 (n : ℕ) : (D n {6, 1}).card =
    ((univ : Finset (Fin 7 → Fin 2)).filter
      (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![6, 1] j)).card *
    ((univ : Finset (Fin 2 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![6, 1] j * (v j).val = n)).card := by
  unfold D
  rw [← img1]
  exact card_D ![6, 1] (by decide) (by decide)

lemma cD2 (n : ℕ) : (D n {5, 2}).card =
    ((univ : Finset (Fin 7 → Fin 2)).filter
      (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![5, 2] j)).card *
    ((univ : Finset (Fin 2 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![5, 2] j * (v j).val = n)).card := by
  unfold D
  rw [← img2]
  exact card_D ![5, 2] (by decide) (by decide)

lemma cD3 (n : ℕ) : (D n {4, 3}).card =
    ((univ : Finset (Fin 7 → Fin 2)).filter
      (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![4, 3] j)).card *
    ((univ : Finset (Fin 2 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![4, 3] j * (v j).val = n)).card := by
  unfold D
  rw [← img3]
  exact card_D ![4, 3] (by decide) (by decide)

lemma cD4 (n : ℕ) : (D n {4, 2, 1}).card =
    ((univ : Finset (Fin 7 → Fin 3)).filter
      (fun β => ∀ j, (univ.filter (fun i => β i = j)).card = ![4, 2, 1] j)).card *
    ((univ : Finset (Fin 3 → Fin (n + 1))).filter (fun v => Function.Injective v ∧
      (∀ j, 0 < (v j).val) ∧ ∑ j, ![4, 2, 1] j * (v j).val = n)).card := by
  unfold D
  rw [← img4]
  exact card_D ![4, 2, 1] (by decide) (by decide)

/-- The g.f. of the counts as a combination of products of the P m. -/
lemma gf_P : PowerSeries.mk (fun n => (a n : ℚ)) =
    C (148 : ℚ) * (P 7) + C (-98 : ℚ) * (P 6 * P 1) + C (-84 : ℚ) * (P 5 * P 2) + C (-70 : ℚ) * (P 4 * P 3) + C (105 : ℚ) * (P 4 * P 2 * P 1) := by
  ext n
  rw [coeff_mk, a_split, cD0, cD1, cD2, cD3, cD4, B0, B1, B2, B3, B4]
  push_cast
  rw [card_V1 7 n (by norm_num), card_V2 6 1 n (by norm_num) (by norm_num), card_V2 5 2 n (by norm_num) (by norm_num), card_V2 4 3 n (by norm_num) (by norm_num), card_V3 4 2 1 n (by norm_num) (by norm_num) (by norm_num)]
  simp only [map_add, coeff_C_mul]
  norm_num
  ring

lemma a_zero : a 0 = 0 := by decide

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6)) =
        X ^ 7 * (1 + 8 * X + 36 * X ^ 2 + 78 * X ^ 3 + 245 * X ^ 4 + 475 * X ^ 5 + 719 * X ^ 6 + 1069 * X ^ 7 + 1419 * X ^ 8 + 1539 * X ^ 9 + 1645 * X ^ 10 + 1478 * X ^ 11 + 1100 * X ^ 12 + 708 * X ^ 13 + 505 * X ^ 14) := by
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
  have h1 := hP 1 (by norm_num)
  have h2 := hP 2 (by norm_num)
  have h3 := hP 3 (by norm_num)
  have h4 := hP 4 (by norm_num)
  have h5 := hP 5 (by norm_num)
  have h6 := hP 6 (by norm_num)
  have h7 := hP 7 (by norm_num)
  linear_combination
    (148 * (1 + X + X ^ 2 + X ^ 3 - X ^ 5 - 2 * X ^ 6 - 2 * X ^ 7 - 2 * X ^ 8 - X ^ 9 + X ^ 11 + X ^ 12 + X ^ 13 + X ^ 14)) * h7 +
    (-98 * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 + 3 * X ^ 5 + 2 * X ^ 6 - 2 * X ^ 8 - 3 * X ^ 9 - 4 * X ^ 10 - 4 * X ^ 11 - 3 * X ^ 12 - 2 * X ^ 13 - X ^ 14) * ((1 - X ^ 1) * P 1)) * h6 +
    (-98 * (1 + 2 * X + 3 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 + 3 * X ^ 5 + 2 * X ^ 6 - 2 * X ^ 8 - 3 * X ^ 9 - 4 * X ^ 10 - 4 * X ^ 11 - 3 * X ^ 12 - 2 * X ^ 13 - X ^ 14) * X ^ 6) * h1 +
    (-84 * (1 + X + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + X ^ 6 - X ^ 8 - 2 * X ^ 9 - 2 * X ^ 10 - 2 * X ^ 11 - 2 * X ^ 12 - X ^ 13 - X ^ 14) * ((1 - X ^ 2) * P 2)) * h5 +
    (-84 * (1 + X + 2 * X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + X ^ 6 - X ^ 8 - 2 * X ^ 9 - 2 * X ^ 10 - 2 * X ^ 11 - 2 * X ^ 12 - X ^ 13 - X ^ 14) * X ^ 5) * h2 +
    (-70 * (1 + X + X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 - X ^ 8 - X ^ 9 - 2 * X ^ 10 - 2 * X ^ 11 - X ^ 12 - X ^ 13 - X ^ 14) * ((1 - X ^ 3) * P 3)) * h4 +
    (-70 * (1 + X + X ^ 2 + 2 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 - X ^ 8 - X ^ 9 - 2 * X ^ 10 - 2 * X ^ 11 - X ^ 12 - X ^ 13 - X ^ 14) * X ^ 4) * h3 +
    (105 * (1 + 2 * X + 4 * X ^ 2 + 6 * X ^ 3 + 9 * X ^ 4 + 11 * X ^ 5 + 13 * X ^ 6 + 13 * X ^ 7 + 13 * X ^ 8 + 11 * X ^ 9 + 9 * X ^ 10 + 6 * X ^ 11 + 4 * X ^ 12 + 2 * X ^ 13 + X ^ 14) * ((1 - X ^ 2) * P 2) * ((1 - X ^ 1) * P 1)) * h4 +
    (105 * (1 + 2 * X + 4 * X ^ 2 + 6 * X ^ 3 + 9 * X ^ 4 + 11 * X ^ 5 + 13 * X ^ 6 + 13 * X ^ 7 + 13 * X ^ 8 + 11 * X ^ 9 + 9 * X ^ 10 + 6 * X ^ 11 + 4 * X ^ 12 + 2 * X ^ 13 + X ^ 14) * X ^ 4 * ((1 - X ^ 1) * P 1)) * h2 +
    (105 * (1 + 2 * X + 4 * X ^ 2 + 6 * X ^ 3 + 9 * X ^ 4 + 11 * X ^ 5 + 13 * X ^ 6 + 13 * X ^ 7 + 13 * X ^ 8 + 11 * X ^ 9 + 9 * X ^ 10 + 6 * X ^ 11 + 4 * X ^ 12 + 2 * X ^ 13 + X ^ 14) * X ^ 4 * X ^ 2) * h1

/-- Barker's recurrence, for n > 27 (the coefficient identity of the g.f.). -/
theorem recur : ∀ n : ℕ, 27 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) - a (n - 3) + a (n - 5) + 2 * a (n - 6) + 3 * a (n - 7) + 3 * a (n - 8) + 2 * a (n - 9) + a (n - 10) - a (n - 11) - 2 * a (n - 12) - 3 * a (n - 13) - 3 * a (n - 14) - 2 * a (n - 15) - a (n - 16) + a (n - 18) + a (n - 19) + a (n - 20) + a (n - 21) := by
  intro n hn
  have h := congrArg (coeff n) gf
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6)) = A + A * X ^ 1 + A * X ^ 2 + A * X ^ 3 - A * X ^ 5 - A * X ^ 6 * C 2 - A * X ^ 7 * C 3 - A * X ^ 8 * C 3 - A * X ^ 9 * C 2 - A * X ^ 10 + A * X ^ 11 + A * X ^ 12 * C 2 + A * X ^ 13 * C 3 + A * X ^ 14 * C 3 + A * X ^ 15 * C 2 + A * X ^ 16 - A * X ^ 18 - A * X ^ 19 - A * X ^ 20 - A * X ^ 21 := by
    rw [show (C (2 : ℚ) : ℚ⟦X⟧) = 2 from map_ofNat C 2, show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3]
    ring
  have e2 : (X ^ 7 * (1 + 8 * X + 36 * X ^ 2 + 78 * X ^ 3 + 245 * X ^ 4 + 475 * X ^ 5 + 719 * X ^ 6 + 1069 * X ^ 7 + 1419 * X ^ 8 + 1539 * X ^ 9 + 1645 * X ^ 10 + 1478 * X ^ 11 + 1100 * X ^ 12 + 708 * X ^ 13 + 505 * X ^ 14) : ℚ⟦X⟧) = X ^ 7 + X ^ 8 * C 8 + X ^ 9 * C 36 + X ^ 10 * C 78 + X ^ 11 * C 245 + X ^ 12 * C 475 + X ^ 13 * C 719 + X ^ 14 * C 1069 + X ^ 15 * C 1419 + X ^ 16 * C 1539 + X ^ 17 * C 1645 + X ^ 18 * C 1478 + X ^ 19 * C 1100 + X ^ 20 * C 708 + X ^ 21 * C 505 := by
    rw [show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8, show (C (36 : ℚ) : ℚ⟦X⟧) = 36 from map_ofNat C 36, show (C (78 : ℚ) : ℚ⟦X⟧) = 78 from map_ofNat C 78, show (C (245 : ℚ) : ℚ⟦X⟧) = 245 from map_ofNat C 245, show (C (475 : ℚ) : ℚ⟦X⟧) = 475 from map_ofNat C 475, show (C (505 : ℚ) : ℚ⟦X⟧) = 505 from map_ofNat C 505, show (C (708 : ℚ) : ℚ⟦X⟧) = 708 from map_ofNat C 708, show (C (719 : ℚ) : ℚ⟦X⟧) = 719 from map_ofNat C 719, show (C (1069 : ℚ) : ℚ⟦X⟧) = 1069 from map_ofNat C 1069, show (C (1100 : ℚ) : ℚ⟦X⟧) = 1100 from map_ofNat C 1100, show (C (1419 : ℚ) : ℚ⟦X⟧) = 1419 from map_ofNat C 1419, show (C (1478 : ℚ) : ℚ⟦X⟧) = 1478 from map_ofNat C 1478, show (C (1539 : ℚ) : ℚ⟦X⟧) = 1539 from map_ofNat C 1539, show (C (1645 : ℚ) : ℚ⟦X⟧) = 1645 from map_ofNat C 1645]
    ring
  rw [e1, e2] at h
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk] at h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 28 := ⟨n - 28, by omega⟩
  simp only [show ¬ (m + 28 = 0) by omega,
    show 1 ≤ m + 28 by omega,
    show ¬ (m + 28 - 1 = 0) by omega,
    show 2 ≤ m + 28 by omega,
    show ¬ (m + 28 - 2 = 0) by omega,
    show 3 ≤ m + 28 by omega,
    show ¬ (m + 28 - 3 = 0) by omega,
    show 5 ≤ m + 28 by omega,
    show ¬ (m + 28 - 5 = 0) by omega,
    show 6 ≤ m + 28 by omega,
    show ¬ (m + 28 - 6 = 0) by omega,
    show 7 ≤ m + 28 by omega,
    show ¬ (m + 28 - 7 = 0) by omega,
    show 8 ≤ m + 28 by omega,
    show ¬ (m + 28 - 8 = 0) by omega,
    show 9 ≤ m + 28 by omega,
    show ¬ (m + 28 - 9 = 0) by omega,
    show 10 ≤ m + 28 by omega,
    show ¬ (m + 28 - 10 = 0) by omega,
    show 11 ≤ m + 28 by omega,
    show ¬ (m + 28 - 11 = 0) by omega,
    show 12 ≤ m + 28 by omega,
    show ¬ (m + 28 - 12 = 0) by omega,
    show 13 ≤ m + 28 by omega,
    show ¬ (m + 28 - 13 = 0) by omega,
    show 14 ≤ m + 28 by omega,
    show ¬ (m + 28 - 14 = 0) by omega,
    show 15 ≤ m + 28 by omega,
    show ¬ (m + 28 - 15 = 0) by omega,
    show 16 ≤ m + 28 by omega,
    show ¬ (m + 28 - 16 = 0) by omega,
    show 18 ≤ m + 28 by omega,
    show ¬ (m + 28 - 18 = 0) by omega,
    show 19 ≤ m + 28 by omega,
    show ¬ (m + 28 - 19 = 0) by omega,
    show 20 ≤ m + 28 by omega,
    show ¬ (m + 28 - 20 = 0) by omega,
    show 21 ≤ m + 28 by omega,
    show ¬ (m + 28 - 21 = 0) by omega,
    show ¬ (m + 28 = 7) by omega,
    show ¬ (m + 28 = 8) by omega,
    show ¬ (m + 28 = 9) by omega,
    show ¬ (m + 28 = 10) by omega,
    show ¬ (m + 28 = 11) by omega,
    show ¬ (m + 28 = 12) by omega,
    show ¬ (m + 28 = 13) by omega,
    show ¬ (m + 28 = 14) by omega,
    show ¬ (m + 28 = 15) by omega,
    show ¬ (m + 28 = 16) by omega,
    show ¬ (m + 28 = 17) by omega,
    show ¬ (m + 28 = 18) by omega,
    show ¬ (m + 28 = 19) by omega,
    show ¬ (m + 28 = 20) by omega,
    show ¬ (m + 28 = 21) by omega, if_true, if_false] at h
  have hq : (a (m + 28) : ℚ) = -a (m + 28 - 1) - a (m + 28 - 2) - a (m + 28 - 3) + a (m + 28 - 5) + 2 * a (m + 28 - 6) + 3 * a (m + 28 - 7) + 3 * a (m + 28 - 8) + 2 * a (m + 28 - 9) + a (m + 28 - 10) - a (m + 28 - 11) - 2 * a (m + 28 - 12) - 3 * a (m + 28 - 13) - 3 * a (m + 28 - 14) - 2 * a (m + 28 - 15) - a (m + 28 - 16) + a (m + 28 - 18) + a (m + 28 - 19) + a (m + 28 - 20) + a (m + 28 - 21) := by
    linear_combination h
  exact_mod_cast hq

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 - X + X ^ 2) * (1 + X ^ 2) * (1 + X + X ^ 2) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) * (1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6)) =
        X ^ 7 * (1 + 8 * X + 36 * X ^ 2 + 78 * X ^ 3 + 245 * X ^ 4 + 475 * X ^ 5 + 719 * X ^ 6 + 1069 * X ^ 7 + 1419 * X ^ 8 + 1539 * X ^ 9 + 1645 * X ^ 10 + 1478 * X ^ 11 + 1100 * X ^ 12 + 708 * X ^ 13 + 505 * X ^ 14) ∧
    ∀ n : ℕ, 27 < n → (a n : ℤ) = -a (n - 1) - a (n - 2) - a (n - 3) + a (n - 5) + 2 * a (n - 6) + 3 * a (n - 7) + 3 * a (n - 8) + 2 * a (n - 9) + a (n - 10) - a (n - 11) - 2 * a (n - 12) - 3 * a (n - 13) - 3 * a (n - 14) - 2 * a (n - 15) - a (n - 16) + a (n - 18) + a (n - 19) + a (n - 20) + a (n - 21) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a321777

theorem OMA.solution : type_of% @OMA.S_oeis_a321777.main :=
  OMA.S_oeis_a321777.conjecture
