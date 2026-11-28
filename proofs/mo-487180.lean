import OMAStatements.S_mo_487180

namespace OMA.S_mo_487180.Disproof

private noncomputable def f1 : ℝ → ℤ := OMA.S_mo_487180.floorSum [1, 1, 3, 4]
private noncomputable def f2 : ℝ → ℤ := OMA.S_mo_487180.floorSum [1, 2, 2, 4]
private noncomputable def f3 : ℝ → ℤ := OMA.S_mo_487180.floorSum [1, 2, 3, 3]
private noncomputable def f4 : ℝ → ℤ := OMA.S_mo_487180.floorSum [2, 2, 2, 3]

private lemma floor_mul_add_int (n : ℕ) (m : ℤ) (y : ℝ) :
    ⌊(n : ℝ) * ((m : ℝ) + y)⌋ = (n : ℤ) * m + ⌊(n : ℝ) * y⌋ := by
  have h : (n : ℝ) * ((m : ℝ) + y) = (((n : ℤ) * m : ℤ) : ℝ) + (n : ℝ) * y := by push_cast; ring
  rw [h, Int.floor_intCast_add]

private lemma floorSum_shift (a : List ℕ) (m : ℤ) (y : ℝ) :
    OMA.S_mo_487180.floorSum a ((m : ℝ) + y) =
      ((a.sum : ℕ) : ℤ) * m + OMA.S_mo_487180.floorSum a y := by
  induction a with
  | nil => simp [OMA.S_mo_487180.floorSum]
  | cons n ns ih =>
    change ⌊(n : ℝ) * ((m : ℝ) + y)⌋ + OMA.S_mo_487180.floorSum ns ((m : ℝ) + y) =
      (((n + ns.sum : ℕ) : ℤ)) * m + (⌊(n : ℝ) * y⌋ + OMA.S_mo_487180.floorSum ns y)
    rw [floor_mul_add_int, ih, Nat.cast_add]
    ring

private lemma f1_eq (x : ℝ) : f1 x = 9 * ⌊x⌋ + f1 (Int.fract x) := by
  have hx : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
  conv_lhs => rw [hx]
  simpa [f1] using floorSum_shift [1, 1, 3, 4] ⌊x⌋ (Int.fract x)

private lemma f2_eq (x : ℝ) : f2 x = 9 * ⌊x⌋ + f2 (Int.fract x) := by
  have hx : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
  conv_lhs => rw [hx]
  simpa [f2] using floorSum_shift [1, 2, 2, 4] ⌊x⌋ (Int.fract x)

private lemma f3_eq (x : ℝ) : f3 x = 9 * ⌊x⌋ + f3 (Int.fract x) := by
  have hx : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
  conv_lhs => rw [hx]
  simpa [f3] using floorSum_shift [1, 2, 3, 3] ⌊x⌋ (Int.fract x)

private lemma f4_eq (x : ℝ) : f4 x = 9 * ⌊x⌋ + f4 (Int.fract x) := by
  have hx : x = (⌊x⌋ : ℝ) + Int.fract x := (Int.floor_add_fract x).symm
  conv_lhs => rw [hx]
  simpa [f4] using floorSum_shift [2, 2, 2, 3] ⌊x⌋ (Int.fract x)

private lemma floor_eq_of_bounds {r : ℝ} {k : ℤ} (h1 : (k : ℝ) ≤ r) (h2 : r < (k : ℝ) + 1) :
    ⌊r⌋ = k :=
  Int.floor_eq_iff.mpr ⟨h1, h2⟩

private lemma f1_at_quarter : f1 (1 / 4) = 1 := by
  have h1 : ⌊((1 : ℕ) : ℝ) * (1 / 4)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h3 : ⌊((3 : ℕ) : ℝ) * (1 / 4)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h4 : ⌊((4 : ℕ) : ℝ) * (1 / 4)⌋ = 1 := floor_eq_of_bounds (by norm_num) (by norm_num)
  change ⌊((1 : ℕ) : ℝ) * (1 / 4)⌋ + (⌊((1 : ℕ) : ℝ) * (1 / 4)⌋ +
    (⌊((3 : ℕ) : ℝ) * (1 / 4)⌋ + (⌊((4 : ℕ) : ℝ) * (1 / 4)⌋ + 0))) = 1
  rw [h1, h3, h4]; norm_num

private lemma f2_at_quarter : f2 (1 / 4) = 1 := by
  have h1 : ⌊((1 : ℕ) : ℝ) * (1 / 4)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h2 : ⌊((2 : ℕ) : ℝ) * (1 / 4)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h4 : ⌊((4 : ℕ) : ℝ) * (1 / 4)⌋ = 1 := floor_eq_of_bounds (by norm_num) (by norm_num)
  change ⌊((1 : ℕ) : ℝ) * (1 / 4)⌋ + (⌊((2 : ℕ) : ℝ) * (1 / 4)⌋ +
    (⌊((2 : ℕ) : ℝ) * (1 / 4)⌋ + (⌊((4 : ℕ) : ℝ) * (1 / 4)⌋ + 0))) = 1
  rw [h1, h2, h4]; norm_num

private lemma f3_at_quarter : f3 (1 / 4) = 0 := by
  have h1 : ⌊((1 : ℕ) : ℝ) * (1 / 4)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h2 : ⌊((2 : ℕ) : ℝ) * (1 / 4)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h3 : ⌊((3 : ℕ) : ℝ) * (1 / 4)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  change ⌊((1 : ℕ) : ℝ) * (1 / 4)⌋ + (⌊((2 : ℕ) : ℝ) * (1 / 4)⌋ +
    (⌊((3 : ℕ) : ℝ) * (1 / 4)⌋ + (⌊((3 : ℕ) : ℝ) * (1 / 4)⌋ + 0))) = 0
  rw [h1, h2, h3]; norm_num

private lemma f4_at_quarter : f4 (1 / 4) = 0 := by
  have h2 : ⌊((2 : ℕ) : ℝ) * (1 / 4)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h3 : ⌊((3 : ℕ) : ℝ) * (1 / 4)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  change ⌊((2 : ℕ) : ℝ) * (1 / 4)⌋ + (⌊((2 : ℕ) : ℝ) * (1 / 4)⌋ +
    (⌊((2 : ℕ) : ℝ) * (1 / 4)⌋ + (⌊((3 : ℕ) : ℝ) * (1 / 4)⌋ + 0))) = 0
  rw [h2, h3]; norm_num

private lemma f1_at_third : f1 (1 / 3) = 2 := by
  have h1 : ⌊((1 : ℕ) : ℝ) * (1 / 3)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h3 : ⌊((3 : ℕ) : ℝ) * (1 / 3)⌋ = 1 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h4 : ⌊((4 : ℕ) : ℝ) * (1 / 3)⌋ = 1 := floor_eq_of_bounds (by norm_num) (by norm_num)
  change ⌊((1 : ℕ) : ℝ) * (1 / 3)⌋ + (⌊((1 : ℕ) : ℝ) * (1 / 3)⌋ +
    (⌊((3 : ℕ) : ℝ) * (1 / 3)⌋ + (⌊((4 : ℕ) : ℝ) * (1 / 3)⌋ + 0))) = 2
  rw [h1, h3, h4]; norm_num

private lemma f2_at_third : f2 (1 / 3) = 1 := by
  have h1 : ⌊((1 : ℕ) : ℝ) * (1 / 3)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h2 : ⌊((2 : ℕ) : ℝ) * (1 / 3)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h4 : ⌊((4 : ℕ) : ℝ) * (1 / 3)⌋ = 1 := floor_eq_of_bounds (by norm_num) (by norm_num)
  change ⌊((1 : ℕ) : ℝ) * (1 / 3)⌋ + (⌊((2 : ℕ) : ℝ) * (1 / 3)⌋ +
    (⌊((2 : ℕ) : ℝ) * (1 / 3)⌋ + (⌊((4 : ℕ) : ℝ) * (1 / 3)⌋ + 0))) = 1
  rw [h1, h2, h4]; norm_num

private lemma f3_at_third : f3 (1 / 3) = 2 := by
  have h1 : ⌊((1 : ℕ) : ℝ) * (1 / 3)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h2 : ⌊((2 : ℕ) : ℝ) * (1 / 3)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h3 : ⌊((3 : ℕ) : ℝ) * (1 / 3)⌋ = 1 := floor_eq_of_bounds (by norm_num) (by norm_num)
  change ⌊((1 : ℕ) : ℝ) * (1 / 3)⌋ + (⌊((2 : ℕ) : ℝ) * (1 / 3)⌋ +
    (⌊((3 : ℕ) : ℝ) * (1 / 3)⌋ + (⌊((3 : ℕ) : ℝ) * (1 / 3)⌋ + 0))) = 2
  rw [h1, h2, h3]; norm_num

private lemma f4_at_third : f4 (1 / 3) = 1 := by
  have h2 : ⌊((2 : ℕ) : ℝ) * (1 / 3)⌋ = 0 := floor_eq_of_bounds (by norm_num) (by norm_num)
  have h3 : ⌊((3 : ℕ) : ℝ) * (1 / 3)⌋ = 1 := floor_eq_of_bounds (by norm_num) (by norm_num)
  change ⌊((2 : ℕ) : ℝ) * (1 / 3)⌋ + (⌊((2 : ℕ) : ℝ) * (1 / 3)⌋ +
    (⌊((2 : ℕ) : ℝ) * (1 / 3)⌋ + (⌊((3 : ℕ) : ℝ) * (1 / 3)⌋ + 0))) = 1
  rw [h2, h3]; norm_num

private lemma f1_ne_f2 : f1 ≠ f2 := by
  intro h; have := congrArg (fun g => g (1 / 3)) h; rw [f1_at_third, f2_at_third] at this; omega
private lemma f1_ne_f3 : f1 ≠ f3 := by
  intro h; have := congrArg (fun g => g (1 / 4)) h; rw [f1_at_quarter, f3_at_quarter] at this; omega
private lemma f1_ne_f4 : f1 ≠ f4 := by
  intro h; have := congrArg (fun g => g (1 / 4)) h; rw [f1_at_quarter, f4_at_quarter] at this; omega
private lemma f2_ne_f3 : f2 ≠ f3 := by
  intro h; have := congrArg (fun g => g (1 / 4)) h; rw [f2_at_quarter, f3_at_quarter] at this; omega
private lemma f2_ne_f4 : f2 ≠ f4 := by
  intro h; have := congrArg (fun g => g (1 / 4)) h; rw [f2_at_quarter, f4_at_quarter] at this; omega
private lemma f3_ne_f4 : f3 ≠ f4 := by
  intro h; have := congrArg (fun g => g (1 / 3)) h; rw [f3_at_third, f4_at_third] at this; omega

private lemma f_eval (y : ℝ) (a b c d : ℤ)
    (h1 : ⌊((1 : ℕ) : ℝ) * y⌋ = a) (h2 : ⌊((2 : ℕ) : ℝ) * y⌋ = b)
    (h3 : ⌊((3 : ℕ) : ℝ) * y⌋ = c) (h4 : ⌊((4 : ℕ) : ℝ) * y⌋ = d) :
    f1 y = a + a + c + d ∧ f2 y = a + b + b + d ∧ f3 y = a + b + c + c ∧ f4 y = b + b + b + c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change ⌊((1 : ℕ) : ℝ) * y⌋ + (⌊((1 : ℕ) : ℝ) * y⌋ + (⌊((3 : ℕ) : ℝ) * y⌋ + (⌊((4 : ℕ) : ℝ) * y⌋ + 0))) = _
    rw [h1, h3, h4]; ring
  · change ⌊((1 : ℕ) : ℝ) * y⌋ + (⌊((2 : ℕ) : ℝ) * y⌋ + (⌊((2 : ℕ) : ℝ) * y⌋ + (⌊((4 : ℕ) : ℝ) * y⌋ + 0))) = _
    rw [h1, h2, h4]; ring
  · change ⌊((1 : ℕ) : ℝ) * y⌋ + (⌊((2 : ℕ) : ℝ) * y⌋ + (⌊((3 : ℕ) : ℝ) * y⌋ + (⌊((3 : ℕ) : ℝ) * y⌋ + 0))) = _
    rw [h1, h2, h3]; ring
  · change ⌊((2 : ℕ) : ℝ) * y⌋ + (⌊((2 : ℕ) : ℝ) * y⌋ + (⌊((2 : ℕ) : ℝ) * y⌋ + (⌊((3 : ℕ) : ℝ) * y⌋ + 0))) = _
    rw [h2, h3]; ring

private lemma no_strict_min_unit (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    (¬ (f1 y < f2 y ∧ f1 y < f3 y ∧ f1 y < f4 y)) ∧
    (¬ (f2 y < f1 y ∧ f2 y < f3 y ∧ f2 y < f4 y)) ∧
    (¬ (f3 y < f1 y ∧ f3 y < f2 y ∧ f3 y < f4 y)) ∧
    (¬ (f4 y < f1 y ∧ f4 y < f2 y ∧ f4 y < f3 y)) := by
  have h1 : ⌊((1 : ℕ) : ℝ) * y⌋ = 0 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
  by_cases h14 : y < 1 / 4
  · have h2 : ⌊((2 : ℕ) : ℝ) * y⌋ = 0 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
    have h3 : ⌊((3 : ℕ) : ℝ) * y⌋ = 0 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
    have h4 : ⌊((4 : ℕ) : ℝ) * y⌋ = 0 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
    rcases f_eval y 0 0 0 0 h1 h2 h3 h4 with ⟨e1, e2, e3, e4⟩
    rw [e1, e2, e3, e4]; omega
  · by_cases h13 : y < 1 / 3
    · have h2 : ⌊((2 : ℕ) : ℝ) * y⌋ = 0 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
      have h3 : ⌊((3 : ℕ) : ℝ) * y⌋ = 0 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
      have h4 : ⌊((4 : ℕ) : ℝ) * y⌋ = 1 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
      rcases f_eval y 0 0 0 1 h1 h2 h3 h4 with ⟨e1, e2, e3, e4⟩
      rw [e1, e2, e3, e4]; omega
    · by_cases h12 : y < 1 / 2
      · have h2 : ⌊((2 : ℕ) : ℝ) * y⌋ = 0 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
        have h3 : ⌊((3 : ℕ) : ℝ) * y⌋ = 1 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
        have h4 : ⌊((4 : ℕ) : ℝ) * y⌋ = 1 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
        rcases f_eval y 0 0 1 1 h1 h2 h3 h4 with ⟨e1, e2, e3, e4⟩
        rw [e1, e2, e3, e4]; omega
      · by_cases h23 : y < 2 / 3
        · have h2 : ⌊((2 : ℕ) : ℝ) * y⌋ = 1 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
          have h3 : ⌊((3 : ℕ) : ℝ) * y⌋ = 1 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
          have h4 : ⌊((4 : ℕ) : ℝ) * y⌋ = 2 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
          rcases f_eval y 0 1 1 2 h1 h2 h3 h4 with ⟨e1, e2, e3, e4⟩
          rw [e1, e2, e3, e4]; omega
        · by_cases h34 : y < 3 / 4
          · have h2 : ⌊((2 : ℕ) : ℝ) * y⌋ = 1 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
            have h3 : ⌊((3 : ℕ) : ℝ) * y⌋ = 2 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
            have h4 : ⌊((4 : ℕ) : ℝ) * y⌋ = 2 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
            rcases f_eval y 0 1 2 2 h1 h2 h3 h4 with ⟨e1, e2, e3, e4⟩
            rw [e1, e2, e3, e4]; omega
          · have h2 : ⌊((2 : ℕ) : ℝ) * y⌋ = 1 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
            have h3 : ⌊((3 : ℕ) : ℝ) * y⌋ = 2 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
            have h4 : ⌊((4 : ℕ) : ℝ) * y⌋ = 3 := floor_eq_of_bounds (by push_cast; linarith) (by push_cast; linarith)
            rcases f_eval y 0 1 2 3 h1 h2 h3 h4 with ⟨e1, e2, e3, e4⟩
            rw [e1, e2, e3, e4]; omega

end OMA.S_mo_487180.Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_487180.main) := by
  classical
  intro hmain
  let S : Finset (ℝ → ℤ) :=
    {OMA.S_mo_487180.Disproof.f1, OMA.S_mo_487180.Disproof.f2,
     OMA.S_mo_487180.Disproof.f3, OMA.S_mo_487180.Disproof.f4}
  have hne : S.Nonempty := ⟨OMA.S_mo_487180.Disproof.f1, by simp [S]⟩
  have hmem : ∀ f ∈ S, OMA.S_mo_487180.isFloorSum f := by
    intro f hf
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact ⟨[1, 1, 3, 4], by decide, rfl⟩
    · exact ⟨[1, 2, 2, 4], by decide, rfl⟩
    · exact ⟨[1, 2, 3, 3], by decide, rfl⟩
    · exact ⟨[2, 2, 2, 3], by decide, rfl⟩
  rcases hmain S hne hmem with ⟨x, _, f, hfS, hstrict⟩
  have hunit := OMA.S_mo_487180.Disproof.no_strict_min_unit (Int.fract x)
    (Int.fract_nonneg x) (Int.fract_lt_one x)
  have hf1 := OMA.S_mo_487180.Disproof.f1_eq x
  have hf2 := OMA.S_mo_487180.Disproof.f2_eq x
  have hf3 := OMA.S_mo_487180.Disproof.f3_eq x
  have hf4 := OMA.S_mo_487180.Disproof.f4_eq x
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hfS
  rcases hfS with rfl | rfl | rfl | rfl
  · have h12 := hstrict OMA.S_mo_487180.Disproof.f2 (by simp [S]) OMA.S_mo_487180.Disproof.f1_ne_f2.symm
    have h13 := hstrict OMA.S_mo_487180.Disproof.f3 (by simp [S]) OMA.S_mo_487180.Disproof.f1_ne_f3.symm
    have h14 := hstrict OMA.S_mo_487180.Disproof.f4 (by simp [S]) OMA.S_mo_487180.Disproof.f1_ne_f4.symm
    exact hunit.1 ⟨by omega, by omega, by omega⟩
  · have h21 := hstrict OMA.S_mo_487180.Disproof.f1 (by simp [S]) OMA.S_mo_487180.Disproof.f1_ne_f2
    have h23 := hstrict OMA.S_mo_487180.Disproof.f3 (by simp [S]) OMA.S_mo_487180.Disproof.f2_ne_f3.symm
    have h24 := hstrict OMA.S_mo_487180.Disproof.f4 (by simp [S]) OMA.S_mo_487180.Disproof.f2_ne_f4.symm
    exact hunit.2.1 ⟨by omega, by omega, by omega⟩
  · have h31 := hstrict OMA.S_mo_487180.Disproof.f1 (by simp [S]) OMA.S_mo_487180.Disproof.f1_ne_f3
    have h32 := hstrict OMA.S_mo_487180.Disproof.f2 (by simp [S]) OMA.S_mo_487180.Disproof.f2_ne_f3
    have h34 := hstrict OMA.S_mo_487180.Disproof.f4 (by simp [S]) OMA.S_mo_487180.Disproof.f3_ne_f4.symm
    exact hunit.2.2.1 ⟨by omega, by omega, by omega⟩
  · have h41 := hstrict OMA.S_mo_487180.Disproof.f1 (by simp [S]) OMA.S_mo_487180.Disproof.f1_ne_f4
    have h42 := hstrict OMA.S_mo_487180.Disproof.f2 (by simp [S]) OMA.S_mo_487180.Disproof.f2_ne_f4
    have h43 := hstrict OMA.S_mo_487180.Disproof.f3 (by simp [S]) OMA.S_mo_487180.Disproof.f3_ne_f4
    exact hunit.2.2.2 ⟨by omega, by omega, by omega⟩
