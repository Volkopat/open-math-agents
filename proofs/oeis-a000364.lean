import OMAStatements.S_oeis_a000364

section Aux
open OMA.S_oeis_a000364

lemma sec_succ (n : ℕ) : secantNumber (n + 1) = ∑ j ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (j + 2) * ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * secantNumber (n - j) := by
  rw [secantNumber]
  exact Fin.sum_univ_eq_sum_range (fun j => (-1 : ℤ) ^ (j + 2) * ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * secantNumber (n - j)) (n + 1)

@[simp] lemma s0 : secantNumber 0 = 1 := by rw [secantNumber]

@[simp] lemma s1 : secantNumber (0 + 1) = 1 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s2 : secantNumber (1 + 1) = 5 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s3 : secantNumber (2 + 1) = 61 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s4 : secantNumber (3 + 1) = 1385 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s5 : secantNumber (4 + 1) = 50521 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s6 : secantNumber (5 + 1) = 2702765 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s7 : secantNumber (6 + 1) = 199360981 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s8 : secantNumber (7 + 1) = 19391512145 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s9 : secantNumber (8 + 1) = 2404879675441 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s10 : secantNumber (9 + 1) = 370371188237525 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s11 : secantNumber (10 + 1) = 69348874393137901 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s12 : secantNumber (11 + 1) = 15514534163557086905 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s13 : secantNumber (12 + 1) = 4087072509293123892361 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s14 : secantNumber (13 + 1) = 1252259641403629865468285 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s15 : secantNumber (14 + 1) = 441543893249023104553682821 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s16 : secantNumber (15 + 1) = 177519391579539289436664789665 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s17 : secantNumber (16 + 1) = 80723299235887898062168247453281 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s18 : secantNumber (17 + 1) = 41222060339517702122347079671259045 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]
@[simp] lemma s19 : secantNumber (18 + 1) = 23489580527043108252017828576198947741 := by
  rw [sec_succ]; simp only [Finset.sum_range_succ]; norm_num [Nat.choose]

end Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a000364.main) := by
  open OMA.S_oeis_a000364 in
  intro h
  obtain ⟨p, hp, hd, hmod⟩ := h 27 (by norm_num)
  have ht : Nat.totient 27 = 18 := by decide
  rw [ht] at hd
  have hp18 : p ≤ 18 := Nat.le_of_dvd (by norm_num) hd
  have h1 := hmod 1 le_rfl
  have h2 := hmod 2 (by norm_num)
  interval_cases p <;> first
    | (exfalso; revert hd; decide)
    | (norm_num [Int.ModEq] at h1; done)
    | (norm_num [Int.ModEq] at h2; done)
