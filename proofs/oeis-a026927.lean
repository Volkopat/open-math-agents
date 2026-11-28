import OMAStatements.S_oeis_a026927

namespace OMA.P_oeis_a026927
open OMA.S_oeis_a026927

/-- Triples (c1, c2, c3) = (number of 1's, 2's, 3's) of a partition of n with a part 3 and
number of parts ≡ r mod 2. -/
def F (r n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n / 2 + 1) ×ˢ Finset.range (n / 3 + 1)).filter
    (fun t => t.1 + 2 * t.2.1 + 3 * t.2.2 = n ∧ 1 ≤ t.2.2 ∧ (t.1 + t.2.1 + t.2.2) % 2 = r)

lemma mem_F {r n : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ F r n ↔ t.1 + 2 * t.2.1 + 3 * t.2.2 = n ∧ 1 ≤ t.2.2 ∧ (t.1 + t.2.1 + t.2.2) % 2 = r := by
  simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨⟨by omega, by omega, by omega⟩, h⟩

lemma decomp (s : Multiset ℕ) (h : ∀ i ∈ s, 0 < i ∧ i ≤ 3) :
    s = Multiset.replicate (s.count 1) 1 + Multiset.replicate (s.count 2) 2 +
      Multiset.replicate (s.count 3) 3 := by
  ext i
  simp only [Multiset.count_add, Multiset.count_replicate]
  by_cases h1 : i = 1
  · subst h1; simp
  by_cases h2 : i = 2
  · subst h2; simp
  by_cases h3 : i = 3
  · subst h3; simp
  have : s.count i = 0 := Multiset.count_eq_zero.mpr (fun hi => by have := h i hi; omega)
  rw [this]
  split_ifs <;> omega

lemma part_card (r n : ℕ) (Q : ℕ → Prop) (hQ : ∀ x, Q x ↔ x % 2 = r) :
    Nat.card {p : n.Partition // Q p.parts.card ∧ 3 ∈ p.parts ∧ ∀ i ∈ p.parts, i ≤ 3} =
      (F r n).card := by
  have hF : (F r n).card = Nat.card {t // t ∈ F r n} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hF]
  apply Nat.card_congr
  have facts : ∀ p : n.Partition, (∀ i ∈ p.parts, i ≤ 3) →
      p.parts.count 1 + 2 * p.parts.count 2 + 3 * p.parts.count 3 = n ∧
      Multiset.card p.parts = p.parts.count 1 + p.parts.count 2 + p.parts.count 3 := by
    intro p hp
    have hd := decomp p.parts (fun i hi => ⟨p.parts_pos hi, hp i hi⟩)
    constructor
    · have hs := p.parts_sum
      rw [hd] at hs
      simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul] at hs
      omega
    · conv_lhs => rw [hd]
      simp only [Multiset.card_add, Multiset.card_replicate]
  exact
    { toFun := fun p => ⟨(p.1.parts.count 1, p.1.parts.count 2, p.1.parts.count 3), by
        obtain ⟨hq, h3, hle⟩ := p.2
        obtain ⟨hsum, hcard⟩ := facts p.1 hle
        have h3' : 0 < p.1.parts.count 3 := Multiset.count_pos.mpr h3
        rw [mem_F]
        refine ⟨hsum, h3', ?_⟩
        rw [← hcard]; exact (hQ _).1 hq⟩
      invFun := fun t =>
        ⟨{ parts := Multiset.replicate t.1.1 1 + Multiset.replicate t.1.2.1 2 +
              Multiset.replicate t.1.2.2 3
           parts_pos := by
             intro i hi
             simp only [Multiset.mem_add, Multiset.mem_replicate] at hi
             omega
           parts_sum := by
             have hm := mem_F.1 t.2
             simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
             omega }, by
          have hm := mem_F.1 t.2
          refine ⟨?_, ?_, ?_⟩
          · simp only [Multiset.card_add, Multiset.card_replicate]
            exact (hQ _).2 hm.2.2
          · exact Multiset.mem_add.2 (Or.inr (Multiset.mem_replicate.2 ⟨by omega, rfl⟩))
          · intro i hi
            simp only [Multiset.mem_add, Multiset.mem_replicate] at hi
            omega⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Nat.Partition.ext
        exact (decomp p.1.parts (fun i hi => ⟨p.1.parts_pos hi, p.2.2.2 i hi⟩)).symm
      right_inv := fun t => by
        apply Subtype.ext
        simp [Multiset.count_replicate] }

lemma shift2 (r m : ℕ) : ((F r (m + 4)).filter (fun t => 2 ≤ t.2.1)).card = (F r m).card := by
  apply Finset.card_nbij' (fun t => (t.1, t.2.1 - 2, t.2.2)) (fun t => (t.1, t.2.1 + 2, t.2.2))
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, mem_F] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, mem_F] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_F] at h
    show (x, y - 2 + 2, z) = (x, y, z)
    rw [Nat.sub_add_cancel (by omega : 2 ≤ y)]
  · rintro ⟨x, y, z⟩ _
    show (x, y + 2 - 2, z) = (x, y, z)
    rw [Nat.add_sub_cancel]

/-- the triples with c2 < 2 -/
def R (r n : ℕ) : Finset (ℕ × ℕ × ℕ) := (F r n).filter (fun t => ¬ 2 ≤ t.2.1)

lemma shift3 (r m : ℕ) : ((R r (m + 6)).filter (fun t => 3 ≤ t.2.2)).card = (R r m).card := by
  apply Finset.card_nbij' (fun t => (t.1, t.2.1, t.2.2 - 2)) (fun t => (t.1, t.2.1, t.2.2 + 2))
  · rintro ⟨x, y, z⟩ h
    simp only [R, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_F] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [R, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_F] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [R, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_F] at h
    show (x, y, z - 2 + 2) = (x, y, z)
    rw [Nat.sub_add_cancel (by omega : 2 ≤ z)]
  · rintro ⟨x, y, z⟩ _
    show (x, y, z + 2 - 2) = (x, y, z)
    rw [Nat.add_sub_cancel]

/-- the triples with c2 < 2 and c3 < 3 -/
def H (r n : ℕ) : Finset (ℕ × ℕ × ℕ) := (R r n).filter (fun t => ¬ 3 ≤ t.2.2)

lemma H_succ (r m : ℕ) : (H r (m + 9)).card = (H r (m + 8)).card := by
  symm
  apply Finset.card_nbij' (fun t => if t.2.1 = 0 then (t.1 - 1, 1, t.2.2) else (t.1 + 3, 0, t.2.2))
    (fun t => if t.2.1 = 1 then (t.1 + 1, 0, t.2.2) else (t.1 - 3, 1, t.2.2))
  · rintro ⟨x, y, z⟩ h
    simp only [H, R, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_F] at h ⊢
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp <;> omega
  · rintro ⟨x, y, z⟩ h
    simp only [H, R, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_F] at h ⊢
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp <;> omega
  · rintro ⟨x, y, z⟩ h
    simp only [H, R, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_F] at h
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp <;> omega
  · rintro ⟨x, y, z⟩ h
    simp only [H, R, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_F] at h
    rcases (by omega : y = 0 ∨ y = 1) with rfl | rfl <;> simp <;> omega

lemma split_card {α : Type} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (s.filter P).card + (s.filter (fun x => ¬ P x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x <;> simp [hp]

lemma e1 (r m : ℕ) : (F r (m + 4)).card = (F r m).card + (R r (m + 4)).card := by
  rw [← shift2 r m, R, split_card]

lemma e2 (r m : ℕ) : (R r (m + 6)).card = (R r m).card + (H r (m + 6)).card := by
  rw [← shift3 r m, H, split_card]

lemma rec_F (r m : ℕ) : ((F r (m + 12)).card : ℤ) = (F r (m + 11)).card + (F r (m + 8)).card -
    (F r (m + 7)).card + (F r (m + 6)).card - (F r (m + 5)).card - (F r (m + 2)).card +
    (F r (m + 1)).card := by
  have h1 : (F r (m + 12)).card = (F r (m + 8)).card + (R r (m + 12)).card := e1 r (m + 8)
  have h2 : (F r (m + 11)).card = (F r (m + 7)).card + (R r (m + 11)).card := e1 r (m + 7)
  have h3 : (F r (m + 6)).card = (F r (m + 2)).card + (R r (m + 6)).card := e1 r (m + 2)
  have h4 : (F r (m + 5)).card = (F r (m + 1)).card + (R r (m + 5)).card := e1 r (m + 1)
  have h5 : (R r (m + 12)).card = (R r (m + 6)).card + (H r (m + 12)).card := e2 r (m + 6)
  have h6 : (R r (m + 11)).card = (R r (m + 5)).card + (H r (m + 11)).card := e2 r (m + 5)
  have h7 : (H r (m + 12)).card = (H r (m + 11)).card := H_succ r (m + 3)
  omega

/-- the power series identity from the recurrence and the first twelve values -/
lemma gf_of (f : ℕ → ℕ) (hrec : ∀ m, (f (m + 12) : ℤ) = f (m + 11) + f (m + 8) - f (m + 7) +
      f (m + 6) - f (m + 5) - f (m + 2) + f (m + 1)) (N : PowerSeries ℚ)
    (hN : ∀ n, n < 12 → PowerSeries.coeff n N = (f n : ℚ) - (if 1 ≤ n then (f (n - 1) : ℚ) else 0)
      - (if 4 ≤ n then (f (n - 4) : ℚ) else 0) + (if 5 ≤ n then (f (n - 5) : ℚ) else 0)
      - (if 6 ≤ n then (f (n - 6) : ℚ) else 0) + (if 7 ≤ n then (f (n - 7) : ℚ) else 0)
      + (if 10 ≤ n then (f (n - 10) : ℚ) else 0) - (if 11 ≤ n then (f (n - 11) : ℚ) else 0))
    (hN' : ∀ n, 12 ≤ n → PowerSeries.coeff n N = 0) :
    PowerSeries.mk (fun n => (f n : ℚ)) *
      ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 *
        (1 - PowerSeries.X + PowerSeries.X ^ 2) * (1 + PowerSeries.X ^ 2) *
        (1 + PowerSeries.X + PowerSeries.X ^ 2)) = N := by
  set s := PowerSeries.mk (fun n => (f n : ℚ)) with hs
  have hL : s * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 *
        (1 - PowerSeries.X + PowerSeries.X ^ 2) * (1 + PowerSeries.X ^ 2) *
        (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
      s - s * PowerSeries.X ^ 1 - s * PowerSeries.X ^ 4 + s * PowerSeries.X ^ 5 -
        s * PowerSeries.X ^ 6 + s * PowerSeries.X ^ 7 + s * PowerSeries.X ^ 10 -
        s * PowerSeries.X ^ 11 := by
    ring
  rw [hL]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_mul_X_pow', hs, PowerSeries.coeff_mk]
  rcases lt_or_ge n 12 with h | h
  · rw [hN n h]
  · rw [hN' n h]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
    have e : ∀ d, d ≤ 11 → d ≤ m + 12 := fun d hd => by omega
    simp only [e 1 (by norm_num), e 4 (by norm_num), e 5 (by norm_num), e 6 (by norm_num),
      e 7 (by norm_num), e 10 (by norm_num), e 11 (by norm_num), ↓reduceIte,
      show m + 12 - 1 = m + 11 by omega, show m + 12 - 4 = m + 8 by omega,
      show m + 12 - 5 = m + 7 by omega, show m + 12 - 6 = m + 6 by omega,
      show m + 12 - 7 = m + 5 by omega, show m + 12 - 10 = m + 2 by omega,
      show m + 12 - 11 = m + 1 by omega]
    have := hrec m
    have hq : ((f (m + 12) : ℤ) : ℚ) = ((f (m + 11) + f (m + 8) - f (m + 7) +
      f (m + 6) - f (m + 5) - f (m + 2) + f (m + 1) : ℤ) : ℚ) := by rw [this]
    push_cast at hq
    linarith

lemma rec_of {f : ℕ → ℕ} (hrec : ∀ m, (f (m + 12) : ℤ) = f (m + 11) + f (m + 8) - f (m + 7) +
      f (m + 6) - f (m + 5) - f (m + 2) + f (m + 1)) :
    ∀ n : ℕ, 12 ≤ n → (f n : ℤ) = f (n - 1) + f (n - 4) - f (n - 5) + f (n - 6) - f (n - 7) -
      f (n - 10) + f (n - 11) := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [show m + 12 - 1 = m + 11 by omega, show m + 12 - 4 = m + 8 by omega,
    show m + 12 - 5 = m + 7 by omega, show m + 12 - 6 = m + 6 by omega,
    show m + 12 - 7 = m + 5 by omega, show m + 12 - 10 = m + 2 by omega,
    show m + 12 - 11 = m + 1 by omega]
  exact hrec m

lemma small (r : ℕ) (hr : r < 2) : ∀ n, n < 12 → (F r n).card =
    if r = 1 then [0, 0, 0, 1, 0, 1, 1, 3, 2, 4, 3, 6].getD n 0
    else [0, 0, 0, 0, 1, 1, 2, 1, 3, 3, 5, 4].getD n 0 := by
  intro n hn
  interval_cases n <;> interval_cases r <;> decide


lemma a_eq (n : ℕ) : a n = (F 0 n).card := part_card 0 n Even (fun _ => Nat.even_iff)

theorem prove_main : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 *
        (1 - PowerSeries.X + PowerSeries.X ^ 2) * (1 + PowerSeries.X ^ 2) *
        (1 + PowerSeries.X + PowerSeries.X ^ 2)) =
      PowerSeries.X ^ 4 * (1 + PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4) ∧
    ∀ n : ℕ, 12 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5) + a (n - 6) - a (n - 7) -
      a (n - 10) + a (n - 11) := by
  have hrec : ∀ m, (a (m + 12) : ℤ) = a (m + 11) + a (m + 8) - a (m + 7) +
      a (m + 6) - a (m + 5) - a (m + 2) + a (m + 1) := by
    intro m; simp only [a_eq]; exact rec_F 0 m
  have hR : (PowerSeries.X : PowerSeries ℚ) ^ 4 * (1 + PowerSeries.X ^ 2 - PowerSeries.X ^ 3 +
      PowerSeries.X ^ 4) = PowerSeries.X ^ 4 + PowerSeries.X ^ 6 - PowerSeries.X ^ 7 +
      PowerSeries.X ^ 8 := by ring
  refine ⟨gf_of a hrec _ ?_ ?_, rec_of hrec⟩
  · intro n hn
    rw [hR]
    simp only [map_sub, map_add, PowerSeries.coeff_X_pow, a_eq]
    interval_cases n <;> simp [small 0 (by norm_num)] <;> norm_num
  · intro n hn
    rw [hR]
    simp [PowerSeries.coeff_X_pow, show n ≠ 4 by omega, show n ≠ 6 by omega,
      show n ≠ 7 by omega, show n ≠ 8 by omega]

end OMA.P_oeis_a026927

theorem OMA.solution : type_of% @OMA.S_oeis_a026927.main := OMA.P_oeis_a026927.prove_main
