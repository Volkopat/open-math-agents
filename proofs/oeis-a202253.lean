import OMAStatements.S_oeis_a202253

namespace OMA.S_oeis_a202253

open Finset



/-- The pairs (u, v) in [-n, n]^2 with u = v (mod 3). -/
noncomputable def pairs (n : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n).filter fun p => (p.1 - p.2) % 3 = 0

lemma card_arrays (n : ℕ) : (arrays n).card = (pairs n).card := by
  apply card_nbij' (fun t => (t.1 - t.2.1, t.2.1 - t.2.2))
    (fun p => ((p.2 - p.1) / 3 + p.1, (p.2 - p.1) / 3, (p.2 - p.1) / 3 - p.2))
  · rintro ⟨x, y, z⟩ h
    simp only [arrays, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc, mem_coe] at h
    simp only [pairs, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc, mem_coe]
    omega
  · rintro ⟨u, v⟩ h
    simp only [pairs, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc, mem_coe] at h
    simp only [arrays, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc, mem_coe]
    omega
  · rintro ⟨x, y, z⟩ h
    simp only [arrays, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc, mem_coe] at h
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨u, v⟩ h
    simp only [pairs, coe_filter, Set.mem_ofPred_eq, mem_product, mem_Icc, mem_coe] at h
    simp only [Prod.mk.injEq]
    omega

/-- The elements of [-n, n] with residue r mod 3. -/
noncomputable def cls (n : ℕ) (r : ℤ) : Finset ℤ := (Icc (-(n : ℤ)) n).filter fun u => u % 3 = r

lemma card_pairs (n : ℕ) :
    (pairs n).card = (cls n 0).card ^ 2 + (cls n 1).card ^ 2 + (cls n 2).card ^ 2 := by
  have hsplit : pairs n = (cls n 0 ×ˢ cls n 0) ∪ (cls n 1 ×ˢ cls n 1) ∪ (cls n 2 ×ˢ cls n 2) := by
    ext ⟨u, v⟩
    simp only [pairs, cls, mem_filter, mem_product, mem_Icc, mem_union]
    omega
  have d1 : Disjoint (cls n 0 ×ˢ cls n 0) (cls n 1 ×ˢ cls n 1) := by
    rw [disjoint_left]
    rintro ⟨u, v⟩ h1 h2
    simp only [cls, mem_filter, mem_product, mem_Icc] at h1 h2
    omega
  have d2 : Disjoint ((cls n 0 ×ˢ cls n 0) ∪ (cls n 1 ×ˢ cls n 1)) (cls n 2 ×ˢ cls n 2) := by
    rw [disjoint_left]
    rintro ⟨u, v⟩ h1 h2
    simp only [cls, mem_filter, mem_product, mem_Icc, mem_union] at h1 h2
    omega
  rw [hsplit, card_union_of_disjoint d2, card_union_of_disjoint d1, card_product, card_product,
    card_product]
  ring

lemma card_cls (n : ℕ) (r : ℤ) (hr0 : 0 ≤ r) (hr : r < 3) :
    ((cls n r).card : ℤ) = (n - r) / 3 + (n + r) / 3 + 1 := by
  have h : (cls n r).card = (Icc (-((n + r) / 3)) ((n - r) / 3)).card := by
    apply card_nbij' (fun u => u / 3) (fun t => 3 * t + r)
    · intro u hu
      simp only [cls, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_coe] at hu
      simp only [mem_coe, mem_Icc]
      omega
    · intro t ht
      simp only [mem_coe, mem_Icc] at ht
      simp only [cls, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_coe]
      omega
    · intro u hu
      simp only [cls, coe_filter, Set.mem_ofPred_eq, mem_Icc, mem_coe] at hu
      show 3 * (u / 3) + r = u
      omega
    · intro t ht
      show (3 * t + r) / 3 = t
      omega
  rw [h, Int.card_Icc]
  have : 0 ≤ (n - r) / 3 + 1 - -((n + r) / 3) := by omega
  rw [Int.toNat_of_nonneg this]
  ring

lemma key (m : ℤ) (hm : 0 ≤ m) :
    (m / 3 + m / 3 + 1) ^ 2 + ((m - 1) / 3 + (m + 1) / 3 + 1) ^ 2 +
      ((m - 2) / 3 + (m + 2) / 3 + 1) ^ 2 = 1 + 2 * ((2 * m ^ 2 + 2 * m) / 3) := by
  obtain ⟨q, s, hs0, hs3, rfl⟩ : ∃ q s : ℤ, 0 ≤ s ∧ s < 3 ∧ m = 3 * q + s :=
    ⟨m / 3, m % 3, by omega, by omega, by omega⟩
  have hsq : 2 * (3 * q + s) ^ 2 + 2 * (3 * q + s) =
      (2 * s ^ 2 + 2 * s) + (6 * q ^ 2 + 4 * q * s + 2 * q) * 3 := by ring
  rw [hsq, Int.add_mul_ediv_right _ _ (by norm_num : (3 : ℤ) ≠ 0)]
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
  · rw [show (3 * q + 0) / 3 = q by omega, show (3 * q + 0 - 1) / 3 = q - 1 by omega,
      show (3 * q + 0 + 1) / 3 = q by omega, show (3 * q + 0 - 2) / 3 = q - 1 by omega,
      show (3 * q + 0 + 2) / 3 = q by omega]
    norm_num
    ring
  · rw [show (3 * q + 1) / 3 = q by omega, show (3 * q + 1 - 1) / 3 = q by omega,
      show (3 * q + 1 + 1) / 3 = q by omega, show (3 * q + 1 - 2) / 3 = q - 1 by omega,
      show (3 * q + 1 + 2) / 3 = q + 1 by omega]
    norm_num
    ring
  · rw [show (3 * q + 2) / 3 = q by omega, show (3 * q + 2 - 1) / 3 = q by omega,
      show (3 * q + 2 + 1) / 3 = q + 1 by omega, show (3 * q + 2 - 2) / 3 = q by omega,
      show (3 * q + 2 + 2) / 3 = q + 1 by omega]
    norm_num
    ring

/-- Kimberling's conjecture: a(n) = 1 + 2 floor((2n^2 + 2n)/3) for n >= 1. -/
theorem conjecture : ∀ n : ℕ, 1 ≤ n → a n = 1 + 2 * ((2 * n ^ 2 + 2 * n) / 3) := by
  intro n hn
  unfold a
  rw [card_arrays, card_pairs]
  have c0 := card_cls n 0 le_rfl (by norm_num)
  have c1 := card_cls n 1 (by norm_num) (by norm_num)
  have c2 := card_cls n 2 (by norm_num) (by norm_num)
  zify
  rw [c0, c1, c2]
  have hk := key (n : ℤ) (by positivity)
  push_cast
  simp only [sub_zero, add_zero] at hk ⊢
  linarith

/-- Controls from the entry: a(1..6) = 3, 9, 17, 27, 41, 57, by kernel computation from the
definition. -/
example : a 1 = 3 ∧ a 2 = 9 ∧ a 3 = 17 ∧ a 4 = 27 := by
  unfold a arrays
  decide +kernel

end OMA.S_oeis_a202253

theorem OMA.solution : type_of% @OMA.S_oeis_a202253.main :=
  OMA.S_oeis_a202253.conjecture
