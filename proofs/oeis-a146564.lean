import OMAStatements.S_oeis_a146564

open OMA.S_oeis_a146564

namespace OMA.P_oeis_a146564

lemma memB (n b : ℕ) (hn : 1 ≤ n) :
    (0 < b ∧ ∃ c : ℕ, b < c ∧ (1 : ℚ) / n = 1 / b - 1 / c) ↔
      (0 < b ∧ b < n ∧ (n - b) ∣ n * b) := by
  constructor
  · rintro ⟨hb, c, hbc, h⟩
    have hbq : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_sub_div _ _ hbq hcq, div_eq_div_iff hnq (mul_ne_zero hbq hcq)] at h
    have h2 : (b : ℚ) * c = ((c : ℚ) - b) * n := by linear_combination h
    have hlt : b < n := by
      by_contra hcon
      push_neg at hcon
      have h3 : (n : ℚ) ≤ b := by exact_mod_cast hcon
      have h4 : (0 : ℚ) < b := by exact_mod_cast hb
      have h5 : (b : ℚ) < c := by exact_mod_cast hbc
      nlinarith [mul_le_mul_of_nonneg_left h3 (sub_nonneg.mpr h5.le), mul_pos h4 h4]
    refine ⟨hb, hlt, c, ?_⟩
    have h6 : ((n - b : ℕ) : ℚ) * c = ((n * b : ℕ) : ℚ) := by
      rw [Nat.cast_sub hlt.le]
      push_cast
      linear_combination -h2
    exact_mod_cast h6.symm
  · rintro ⟨hb, hlt, c, hc⟩
    have hc' : ((n : ℚ) - b) * c = n * b := by
      have h7 : ((n - b : ℕ) : ℚ) * c = ((n * b : ℕ) : ℚ) := by exact_mod_cast hc.symm
      rw [Nat.cast_sub hlt.le] at h7
      push_cast at h7
      linear_combination h7
    have hbq : (0 : ℚ) < b := by exact_mod_cast hb
    have hnb : (b : ℚ) < n := by exact_mod_cast hlt
    have hbc : b < c := by
      by_contra hcon
      push_neg at hcon
      have h1 : (c : ℚ) ≤ b := by exact_mod_cast hcon
      nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hnb.le), mul_pos hbq hbq]
    refine ⟨hb, c, hbc, ?_⟩
    have hbq' : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcq : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_sub_div _ _ hbq' hcq, div_eq_div_iff hnq (mul_ne_zero hbq' hcq)]
    linear_combination -hc'

lemma dvd_iff_big (d n : ℕ) :
    (((d + n : ℕ) : ℤ) - n) ∣ ((d + n : ℕ) : ℤ) * n ↔ d ∣ n ^ 2 := by
  have e1 : (((d + n : ℕ) : ℤ) - n) = (d : ℤ) := by push_cast; ring
  have e2 : ((d + n : ℕ) : ℤ) * n = (d : ℤ) * n + ((n ^ 2 : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, dvd_add_right (dvd_mul_right _ _)]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

lemma dvd_iff_small (k n : ℕ) (hk : k < n) :
    (((k : ℤ) - n) ∣ (k : ℤ) * n) ↔ (n - k) ∣ n * k := by
  have e1 : ((k : ℤ) - n) = -(((n - k : ℕ) : ℤ)) := by rw [Nat.cast_sub hk.le]; ring
  have e2 : (k : ℤ) * n = ((n * k : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2, neg_dvd]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

lemma setEq (n : ℕ) (hn : 1 ≤ n) :
    {k : ℕ | 0 < k ∧ k ≠ n ∧ ((k : ℤ) - n) ∣ (k : ℤ) * n} =
      (fun d => d + n) '' ((n ^ 2).divisors : Set ℕ) ∪
        {b : ℕ | 0 < b ∧ ∃ c : ℕ, b < c ∧ (1 : ℚ) / n = 1 / b - 1 / c} := by
  ext k
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image, Finset.mem_coe, Nat.mem_divisors]
  constructor
  · rintro ⟨hk0, hkn, hdvd⟩
    rcases lt_or_gt_of_ne hkn with hlt | hgt
    · right
      rw [memB n k hn]
      exact ⟨hk0, hlt, (dvd_iff_small k n hlt).1 hdvd⟩
    · left
      refine ⟨k - n, ⟨?_, pow_ne_zero 2 (by omega)⟩, by omega⟩
      have hk : k = (k - n) + n := by omega
      rw [hk] at hdvd
      exact (dvd_iff_big (k - n) n).1 hdvd
  · rintro (⟨d, ⟨hd, hn2⟩, rfl⟩ | hb)
    · have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn2)
      exact ⟨by omega, by omega, (dvd_iff_big d n).2 hd⟩
    · rw [memB n k hn] at hb
      obtain ⟨hb0, hlt, hdv⟩ := hb
      exact ⟨hb0, by omega, (dvd_iff_small k n hlt).2 hdv⟩

lemma disj (n : ℕ) (hn : 1 ≤ n) :
    Disjoint ((fun d => d + n) '' ((n ^ 2).divisors : Set ℕ))
      {b : ℕ | 0 < b ∧ ∃ c : ℕ, b < c ∧ (1 : ℚ) / n = 1 / b - 1 / c} := by
  rw [Set.disjoint_left]
  rintro x ⟨d, _, rfl⟩ hx
  rw [Set.mem_setOf_eq, memB n (d + n) hn] at hx
  exact absurd hx.2.1 (by omega)

lemma fin2 (n : ℕ) (hn : 1 ≤ n) :
    {b : ℕ | 0 < b ∧ ∃ c : ℕ, b < c ∧ (1 : ℚ) / n = 1 / b - 1 / c}.Finite := by
  apply (Set.finite_Iio n).subset
  intro b hb
  rw [Set.mem_setOf_eq, memB n b hn] at hb
  exact hb.2.1

end OMA.P_oeis_a146564

open OMA.P_oeis_a146564 in
theorem OMA.solution : type_of% @OMA.S_oeis_a146564.main := by
  intro n hn
  unfold a A048691 A063647
  rw [setEq n hn, Set.ncard_union_eq (disj n hn) ((Finset.finite_toSet _).image _) (fin2 n hn),
    Set.ncard_image_of_injective _ (add_left_injective n)]
  first
  | rw [Set.ncard_coe_finset]
  | rw [Set.ncard_coe_Finset]
  | simp
