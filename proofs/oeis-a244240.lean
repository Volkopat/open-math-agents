import OMAStatements.S_oeis_a244240

namespace OMA.P_oeis_a244240
open OMA.S_oeis_a244240

/-- triples (p1, p2, p3) of the sorted parts; p4 = n - p1 - p2 - p3 -/
def T (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n / 4 + 1) ×ˢ Finset.range (n / 3 + 1) ×ˢ Finset.range (n / 2 + 1)).filter
    (fun t => 1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + 2 * t.2.2 ≤ n ∧ t.1 ≠ 1 ∧
      t.2.1 ≠ 2 ∧ t.2.2 ≠ 3 ∧ t.1 + t.2.1 + t.2.2 + 4 ≠ n)

lemma mem_T {n : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ T n ↔ 1 ≤ t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + 2 * t.2.2 ≤ n ∧ t.1 ≠ 1 ∧
      t.2.1 ≠ 2 ∧ t.2.2 ≠ 3 ∧ t.1 + t.2.1 + t.2.2 + 4 ≠ n := by
  simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨⟨by omega, by omega, by omega⟩, h⟩

lemma sorted4 {n : ℕ} (p : n.Partition) (h : Multiset.card p.parts = 4) :
    ∃ x0 x1 x2 x3, p.parts.sort (· ≤ ·) = [x0, x1, x2, x3] ∧ 0 < x0 ∧ x0 ≤ x1 ∧ x1 ≤ x2 ∧
      x2 ≤ x3 ∧ x0 + x1 + x2 + x3 = n := by
  have hl : (p.parts.sort (· ≤ ·)).length = 4 := by rw [Multiset.length_sort]; exact h
  have hs := Multiset.pairwise_sort p.parts (· ≤ ·)
  have he := Multiset.sort_eq p.parts (· ≤ ·)
  have hsum := p.parts_sum
  have hpos : ∀ i ∈ p.parts, 0 < i := fun i hi => p.parts_pos hi
  rw [← he] at hsum hpos
  generalize p.parts.sort (· ≤ ·) = l at hl hs hsum hpos ⊢
  obtain _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, l⟩⟩⟩⟩⟩ := l <;> simp at hl
  simp at hs hsum
  have h0 := hpos x0 (by simp)
  exact ⟨x0, x1, x2, x3, rfl, h0, by omega, by omega, by omega, by omega⟩

lemma sort4 (x0 x1 x2 x3 : ℕ) (h1 : x0 ≤ x1) (h2 : x1 ≤ x2) (h3 : x2 ≤ x3) :
    (x0 ::ₘ x1 ::ₘ x2 ::ₘ {x3} : Multiset ℕ).sort (· ≤ ·) = [x0, x1, x2, x3] := by
  rw [Multiset.sort_cons, Multiset.sort_cons, Multiset.sort_cons, Multiset.sort_singleton] <;>
    simp <;> omega

lemma a_eq (n : ℕ) : a n = (T n).card := by
  have hF : (T n).card = Nat.card {t // t ∈ T n} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hF]
  unfold a
  apply Nat.card_congr
  exact
    { toFun := fun p => ⟨((p.1.parts.sort (· ≤ ·)).getD 0 0, (p.1.parts.sort (· ≤ ·)).getD 1 0,
          (p.1.parts.sort (· ≤ ·)).getD 2 0), by
        obtain ⟨x0, x1, x2, x3, hl, h0, h1, h2, h3, hs⟩ := sorted4 p.1 p.2.1
        have hc := p.2.2
        rw [hl] at hc
        rw [hl]
        have c0 := hc 0 (by simp)
        have c1 := hc 1 (by simp)
        have c2 := hc 2 (by simp)
        have c3 := hc 3 (by simp)
        simp at c0 c1 c2 c3
        show (x0, x1, x2) ∈ T n
        simp only [mem_T]
        omega⟩
      invFun := fun t =>
        ⟨{ parts := t.1.1 ::ₘ t.1.2.1 ::ₘ t.1.2.2 ::ₘ {n - (t.1.1 + t.1.2.1 + t.1.2.2)}
           parts_pos := by
             intro i hi
             have hm := mem_T.1 t.2
             simp only [Multiset.mem_cons, Multiset.mem_singleton] at hi
             omega
           parts_sum := by
             have hm := mem_T.1 t.2
             simp only [Multiset.sum_cons, Multiset.sum_singleton]
             omega }, by
          have hm := mem_T.1 t.2
          refine ⟨by simp, ?_⟩
          dsimp only
          rw [sort4 _ _ _ _ (by omega) (by omega) (by omega)]
          intro i hi
          simp at hi
          interval_cases i <;> simp <;> omega⟩
      left_inv := fun p => by
        obtain ⟨x0, x1, x2, x3, hl, h0, h1, h2, h3, hs⟩ := sorted4 p.1 p.2.1
        apply Subtype.ext
        apply Nat.Partition.ext
        have he := Multiset.sort_eq p.1.parts (· ≤ ·)
        rw [hl] at he
        dsimp only
        rw [hl]
        rw [← he]
        show x0 ::ₘ x1 ::ₘ x2 ::ₘ {n - (x0 + x1 + x2)} = (↑[x0, x1, x2, x3] : Multiset ℕ)
        rw [show n - (x0 + x1 + x2) = x3 by omega]
        rfl
      right_inv := fun t => by
        have hm := mem_T.1 t.2
        apply Subtype.ext
        dsimp only
        rw [sort4 _ _ _ _ (by omega) (by omega) (by omega)]
        rfl }

/-- the triples with p3 = p4 -/
def U (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (T n).filter (fun t => t.1 + t.2.1 + 2 * t.2.2 = n)
/-- the triples with p2 = p3 = p4 -/
def V (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (U n).filter (fun t => t.2.1 = t.2.2)
/-- the triples with p1 = p2 = p3 = p4 -/
def W (n : ℕ) : Finset (ℕ × ℕ × ℕ) := (V n).filter (fun t => t.1 = t.2.1)

lemma split_card {α : Type} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (s.filter P).card + (s.filter (fun x => ¬ P x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : P x <;> simp [hp]

lemma s1 (k : ℕ) : (T (k + 18)).filter (fun t => ¬ (t.1 + t.2.1 + 2 * t.2.2 = k + 18)) =
    T (k + 17) := by
  ext ⟨x, y, z⟩
  simp only [Finset.mem_filter, mem_T]
  constructor <;> intro h <;> omega

lemma e1 (k : ℕ) : (T (k + 18)).card = (U (k + 18)).card + (T (k + 17)).card := by
  rw [← s1 k, U, split_card]

lemma s2 (k : ℕ) : ((U (k + 19)).filter (fun t => ¬ t.2.1 = t.2.2)).card = (U (k + 17)).card := by
  apply Finset.card_nbij' (fun t => (t.1, t.2.1, t.2.2 - 1)) (fun t => (t.1, t.2.1, t.2.2 + 1))
  · rintro ⟨x, y, z⟩ h
    simp only [U, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_T] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [U, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_T] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [U, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_T] at h
    show (x, y, z - 1 + 1) = (x, y, z)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ z)]
  · rintro ⟨x, y, z⟩ _
    show (x, y, z + 1 - 1) = (x, y, z)
    rw [Nat.add_sub_cancel]

lemma e2 (k : ℕ) : (U (k + 19)).card = (V (k + 19)).card + (U (k + 17)).card := by
  rw [← s2 k, V, split_card]

lemma s3 (k : ℕ) : ((V (k + 20)).filter (fun t => ¬ t.1 = t.2.1)).card = (V (k + 17)).card := by
  apply Finset.card_nbij' (fun t => (t.1, t.2.1 - 1, t.2.2 - 1))
    (fun t => (t.1, t.2.1 + 1, t.2.2 + 1))
  · rintro ⟨x, y, z⟩ h
    simp only [V, U, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_T] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [V, U, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_T] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [V, U, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_T] at h
    show (x, y - 1 + 1, z - 1 + 1) = (x, y, z)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ y), Nat.sub_add_cancel (by omega : 1 ≤ z)]
  · rintro ⟨x, y, z⟩ _
    show (x, y + 1 - 1, z + 1 - 1) = (x, y, z)
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel]

lemma e3 (k : ℕ) : (V (k + 20)).card = (W (k + 20)).card + (V (k + 17)).card := by
  rw [← s3 k, W, split_card]

lemma e4 (k : ℕ) : (W (k + 21)).card = (W (k + 17)).card := by
  apply Finset.card_nbij' (fun t => (t.1 - 1, t.2.1 - 1, t.2.2 - 1))
    (fun t => (t.1 + 1, t.2.1 + 1, t.2.2 + 1))
  · rintro ⟨x, y, z⟩ h
    simp only [W, V, U, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_T] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [W, V, U, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_T] at h ⊢
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [W, V, U, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter,
      mem_T] at h
    show (x - 1 + 1, y - 1 + 1, z - 1 + 1) = (x, y, z)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ x), Nat.sub_add_cancel (by omega : 1 ≤ y),
      Nat.sub_add_cancel (by omega : 1 ≤ z)]
  · rintro ⟨x, y, z⟩ _
    show (x + 1 - 1, y + 1 - 1, z + 1 - 1) = (x, y, z)
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.add_sub_cancel]

lemma rec_T (m : ℕ) : ((T (m + 27)).card : ℤ) = (T (m + 26)).card + (T (m + 25)).card -
    2 * (T (m + 22)).card + (T (m + 19)).card + (T (m + 18)).card - (T (m + 17)).card := by
  have u0 : (T (m + 18)).card = (U (m + 18)).card + (T (m + 17)).card := e1 (m + 0)
  have u1 : (T (m + 19)).card = (U (m + 19)).card + (T (m + 18)).card := e1 (m + 1)
  have u2 : (T (m + 20)).card = (U (m + 20)).card + (T (m + 19)).card := e1 (m + 2)
  have u3 : (T (m + 21)).card = (U (m + 21)).card + (T (m + 20)).card := e1 (m + 3)
  have u4 : (T (m + 22)).card = (U (m + 22)).card + (T (m + 21)).card := e1 (m + 4)
  have u5 : (T (m + 23)).card = (U (m + 23)).card + (T (m + 22)).card := e1 (m + 5)
  have u6 : (T (m + 24)).card = (U (m + 24)).card + (T (m + 23)).card := e1 (m + 6)
  have u7 : (T (m + 25)).card = (U (m + 25)).card + (T (m + 24)).card := e1 (m + 7)
  have u8 : (T (m + 26)).card = (U (m + 26)).card + (T (m + 25)).card := e1 (m + 8)
  have u9 : (T (m + 27)).card = (U (m + 27)).card + (T (m + 26)).card := e1 (m + 9)
  have v0 : (U (m + 19)).card = (V (m + 19)).card + (U (m + 17)).card := e2 (m + 0)
  have v1 : (U (m + 20)).card = (V (m + 20)).card + (U (m + 18)).card := e2 (m + 1)
  have v2 : (U (m + 21)).card = (V (m + 21)).card + (U (m + 19)).card := e2 (m + 2)
  have v3 : (U (m + 22)).card = (V (m + 22)).card + (U (m + 20)).card := e2 (m + 3)
  have v4 : (U (m + 23)).card = (V (m + 23)).card + (U (m + 21)).card := e2 (m + 4)
  have v5 : (U (m + 24)).card = (V (m + 24)).card + (U (m + 22)).card := e2 (m + 5)
  have v6 : (U (m + 25)).card = (V (m + 25)).card + (U (m + 23)).card := e2 (m + 6)
  have v7 : (U (m + 26)).card = (V (m + 26)).card + (U (m + 24)).card := e2 (m + 7)
  have v8 : (U (m + 27)).card = (V (m + 27)).card + (U (m + 25)).card := e2 (m + 8)
  have w0 : (V (m + 20)).card = (W (m + 20)).card + (V (m + 17)).card := e3 (m + 0)
  have w1 : (V (m + 21)).card = (W (m + 21)).card + (V (m + 18)).card := e3 (m + 1)
  have w2 : (V (m + 22)).card = (W (m + 22)).card + (V (m + 19)).card := e3 (m + 2)
  have w3 : (V (m + 23)).card = (W (m + 23)).card + (V (m + 20)).card := e3 (m + 3)
  have w4 : (V (m + 24)).card = (W (m + 24)).card + (V (m + 21)).card := e3 (m + 4)
  have w5 : (V (m + 25)).card = (W (m + 25)).card + (V (m + 22)).card := e3 (m + 5)
  have w6 : (V (m + 26)).card = (W (m + 26)).card + (V (m + 23)).card := e3 (m + 6)
  have w7 : (V (m + 27)).card = (W (m + 27)).card + (V (m + 24)).card := e3 (m + 7)
  have z0 : (W (m + 21)).card = (W (m + 17)).card := e4 (m + 0)
  have z1 : (W (m + 22)).card = (W (m + 18)).card := e4 (m + 1)
  have z2 : (W (m + 23)).card = (W (m + 19)).card := e4 (m + 2)
  have z3 : (W (m + 24)).card = (W (m + 20)).card := e4 (m + 3)
  have z4 : (W (m + 25)).card = (W (m + 21)).card := e4 (m + 4)
  have z5 : (W (m + 26)).card = (W (m + 22)).card := e4 (m + 5)
  have z6 : (W (m + 27)).card = (W (m + 23)).card := e4 (m + 6)
  omega

lemma small : ∀ n, n < 27 → (T n).card = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 7, 11, 15, 19, 25, 30, 37, 44, 53, 61, 72].getD n 0 := by
  intro n hn
  interval_cases n <;> decide +kernel

theorem prove_main : (∀ n : ℕ, 27 ≤ n → (a n : ℤ) = a (n - 1) + a (n - 2) - 2 * a (n - 5) +
      a (n - 8) + a (n - 9) - a (n - 10)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((PowerSeries.X - 1) ^ 4 * (PowerSeries.X + 1) ^ 2 * (PowerSeries.X ^ 2 + 1) *
        (PowerSeries.X ^ 2 + PowerSeries.X + 1)) =
      PowerSeries.X ^ 14 * (-PowerSeries.X ^ 4 + PowerSeries.X + 1) *
        (PowerSeries.X ^ 8 - PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 4 +
          2 * PowerSeries.X + 1) := by
  have hrec : ∀ m, (a (m + 27) : ℤ) = a (m + 26) + a (m + 25) - 2 * a (m + 22) + a (m + 19) +
      a (m + 18) - a (m + 17) := by
    intro m; simp only [a_eq]; exact rec_T m
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [show m + 27 - 1 = m + 26 by omega, show m + 27 - 2 = m + 25 by omega,
      show m + 27 - 5 = m + 22 by omega, show m + 27 - 8 = m + 19 by omega,
      show m + 27 - 9 = m + 18 by omega, show m + 27 - 10 = m + 17 by omega]
    exact hrec m
  · set s := PowerSeries.mk (fun n => (a n : ℚ)) with hs
    have hL : s * ((PowerSeries.X - 1) ^ 4 * (PowerSeries.X + 1) ^ 2 * (PowerSeries.X ^ 2 + 1) *
        (PowerSeries.X ^ 2 + PowerSeries.X + 1)) =
        s - s * PowerSeries.X ^ 1 - s * PowerSeries.X ^ 2 + 2 • (s * PowerSeries.X ^ 5) -
          s * PowerSeries.X ^ 8 - s * PowerSeries.X ^ 9 + s * PowerSeries.X ^ 10 := by
      ring
    have hR : (PowerSeries.X : PowerSeries ℚ) ^ 14 * (-PowerSeries.X ^ 4 + PowerSeries.X + 1) *
        (PowerSeries.X ^ 8 - PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 4 +
          2 * PowerSeries.X + 1) =
        PowerSeries.X ^ 14 + 3 • PowerSeries.X ^ 15 + 2 • PowerSeries.X ^ 16 - 3 • PowerSeries.X ^ 18 - 5 • PowerSeries.X ^ 19 - PowerSeries.X ^ 20 + 3 • PowerSeries.X ^ 22 + 2 • PowerSeries.X ^ 23 - PowerSeries.X ^ 26 := by
      ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_nsmul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      hs, PowerSeries.coeff_mk]
    simp only [nsmul_eq_mul]
    rcases lt_or_ge n 27 with h | h
    · interval_cases n <;> simp [a_eq, small] <;> norm_num
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      have e : ∀ d, d ≤ 10 → d ≤ m + 27 := fun d hd => by omega
      simp only [e 1 (by norm_num), e 2 (by norm_num), e 5 (by norm_num), e 8 (by norm_num),
        e 9 (by norm_num), e 10 (by norm_num), ↓reduceIte,
        show m + 27 ≠ 14 by omega, show m + 27 ≠ 15 by omega, show m + 27 ≠ 16 by omega, show m + 27 ≠ 18 by omega, show m + 27 ≠ 19 by omega, show m + 27 ≠ 20 by omega, show m + 27 ≠ 22 by omega, show m + 27 ≠ 23 by omega, show m + 27 ≠ 26 by omega,
        show m + 27 - 1 = m + 26 by omega, show m + 27 - 2 = m + 25 by omega,
        show m + 27 - 5 = m + 22 by omega, show m + 27 - 8 = m + 19 by omega,
        show m + 27 - 9 = m + 18 by omega, show m + 27 - 10 = m + 17 by omega]
      have hq : ((a (m + 27) : ℤ) : ℚ) = ((a (m + 26) + a (m + 25) - 2 * a (m + 22) + a (m + 19) +
          a (m + 18) - a (m + 17) : ℤ) : ℚ) := by rw [hrec m]
      push_cast at hq ⊢
      linarith

end OMA.P_oeis_a244240

theorem OMA.solution : type_of% @OMA.S_oeis_a244240.main := OMA.P_oeis_a244240.prove_main
