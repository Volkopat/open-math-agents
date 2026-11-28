import OMAStatements.S_mse_4804070

private def W (i j : Fin 6) : ℕ :=
  match i.val, j.val with
  | 0, 1 | 1, 0 => 6
  | 0, 2 | 2, 0 => 10
  | 0, 3 | 3, 0 => 14
  | 0, 4 | 4, 0 => 7
  | 0, 5 | 5, 0 => 8
  | 1, 2 | 2, 1 => 3
  | 1, 3 | 3, 1 => 15
  | 1, 4 | 4, 1 => 2
  | 1, 5 | 5, 1 => 5
  | 2, 3 | 3, 2 => 12
  | 2, 4 | 4, 2 => 13
  | 2, 5 | 5, 2 => 11
  | 3, 4 | 4, 3 => 4
  | 3, 5 | 5, 3 => 9
  | 4, 5 | 5, 4 => 1
  | _, _ => 0

private def best1 : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 4
  | 2 => 1
  | 3 => 4
  | 4 => 5
  | 5 => 4

private def best2 : Fin 6 → Fin 6
  | 0 => 4
  | 1 => 2
  | 2 => 0
  | 3 => 5
  | 4 => 1
  | 5 => 1

private lemma fin6_cases (x : Fin 6) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
  revert x; decide

private lemma W_diag : ∀ i : Fin 6, W i i = 0 := by decide

private lemma W_symm : ∀ i j : Fin 6, W i j = W j i := by decide

private lemma W_distinct (i : Fin 6) :
    ∀ j k l : Fin 6, i ≠ j → k ≠ l → W i j = W k l →
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  rcases fin6_cases i with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma special_pair :
    ∀ x0 x1 x5 : Fin 6, x0 ≠ x1 → x0 ≠ x5 → x1 ≠ x5 →
      (∀ w : Fin 6, w ≠ x0 → w ≠ x5 → w ≠ x1 → W x0 x5 ≤ W x0 w ∧ W x0 x1 ≤ W x0 w) →
      (x1 = best1 x0 ∧ x5 = best2 x0) ∨ (x1 = best2 x0 ∧ x5 = best1 x0) := by
  decide

private lemma tour_gt_fwd (x0 : Fin 6) :
    ∀ x2 x3 x4 : Fin 6,
      x0 ≠ x2 → x0 ≠ x3 → x0 ≠ x4 →
      best1 x0 ≠ x2 → best1 x0 ≠ x3 → best1 x0 ≠ x4 →
      best2 x0 ≠ x2 → best2 x0 ≠ x3 → best2 x0 ≠ x4 →
      x2 ≠ x3 → x2 ≠ x4 → x3 ≠ x4 →
      34 < W x0 (best1 x0) + W (best1 x0) x2 + W x2 x3 +
        W x3 x4 + W x4 (best2 x0) + W (best2 x0) x0 := by
  rcases fin6_cases x0 with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private lemma univ_fin6 :
    (Finset.univ : Finset (Fin 6)) =
      insert 0 (insert 1 (insert 2 (insert 3 (insert 4 {5})))) := by
  ext x
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact fin6_cases x

private lemma sum_fin6_cast (f : Fin 6 → ℕ) :
    ∑ j : Fin 6, (f j : ℝ) = ((∑ j : Fin 6, f j : ℕ) : ℝ) := by
  rw [univ_fin6,
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_singleton,
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_singleton]
  simp only [Nat.cast_add]

private lemma sum_fin6_eq (f : Fin 6 → ℕ) :
    ∑ j : Fin 6, f j = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [univ_fin6,
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_insert (by simp),
    Finset.sum_singleton]
  omega

private lemma sum_fin6_rot (f : Fin 6 → ℕ) (i : Fin 6) :
    ∑ j : Fin 6, f j =
      f i + f (finRotate 6 i) + f (finRotate 6 (finRotate 6 i)) +
      f (finRotate 6 (finRotate 6 (finRotate 6 i))) +
      f (finRotate 6 (finRotate 6 (finRotate 6 (finRotate 6 i)))) +
      f ((finRotate 6).symm i) := by
  rw [sum_fin6_eq]
  rcases fin6_cases i with rfl | rfl | rfl | rfl | rfl | rfl
  · have h1 : finRotate 6 0 = 1 := by decide
    have h2 : finRotate 6 1 = 2 := by decide
    have h3 : finRotate 6 2 = 3 := by decide
    have h4 : finRotate 6 3 = 4 := by decide
    have h5 : (finRotate 6).symm 0 = 5 := by decide
    rw [h1, h2, h3, h4, h5]
  · have h1 : finRotate 6 1 = 2 := by decide
    have h2 : finRotate 6 2 = 3 := by decide
    have h3 : finRotate 6 3 = 4 := by decide
    have h4 : finRotate 6 4 = 5 := by decide
    have h5 : (finRotate 6).symm 1 = 0 := by decide
    rw [h1, h2, h3, h4, h5]; omega
  · have h1 : finRotate 6 2 = 3 := by decide
    have h2 : finRotate 6 3 = 4 := by decide
    have h3 : finRotate 6 4 = 5 := by decide
    have h4 : finRotate 6 5 = 0 := by decide
    have h5 : (finRotate 6).symm 2 = 1 := by decide
    rw [h1, h2, h3, h4, h5]; omega
  · have h1 : finRotate 6 3 = 4 := by decide
    have h2 : finRotate 6 4 = 5 := by decide
    have h3 : finRotate 6 5 = 0 := by decide
    have h4 : finRotate 6 0 = 1 := by decide
    have h5 : (finRotate 6).symm 3 = 2 := by decide
    rw [h1, h2, h3, h4, h5]; omega
  · have h1 : finRotate 6 4 = 5 := by decide
    have h2 : finRotate 6 5 = 0 := by decide
    have h3 : finRotate 6 0 = 1 := by decide
    have h4 : finRotate 6 1 = 2 := by decide
    have h5 : (finRotate 6).symm 4 = 3 := by decide
    rw [h1, h2, h3, h4, h5]; omega
  · have h1 : finRotate 6 5 = 0 := by decide
    have h2 : finRotate 6 0 = 1 := by decide
    have h3 : finRotate 6 1 = 2 := by decide
    have h4 : finRotate 6 2 = 3 := by decide
    have h5 : (finRotate 6).symm 5 = 4 := by decide
    rw [h1, h2, h3, h4, h5]; omega

private lemma rot_five (i : Fin 6) :
    finRotate 6 (finRotate 6 (finRotate 6 (finRotate 6 (finRotate 6 i)))) =
      (finRotate 6).symm i := by
  revert i; decide

private lemma rot_distinct (i : Fin 6) :
    let g := finRotate 6
    i ≠ g i ∧ i ≠ g (g i) ∧ i ≠ g (g (g i)) ∧ i ≠ g (g (g (g i))) ∧ i ≠ g.symm i ∧
    g i ≠ g (g i) ∧ g i ≠ g (g (g i)) ∧ g i ≠ g (g (g (g i))) ∧ g i ≠ g.symm i ∧
    g (g i) ≠ g (g (g i)) ∧ g (g i) ≠ g (g (g (g i))) ∧ g (g i) ≠ g.symm i ∧
    g (g (g i)) ≠ g (g (g (g i))) ∧ g (g (g i)) ≠ g.symm i ∧
    g (g (g (g i))) ≠ g.symm i := by
  revert i; decide

private lemma ref_tour_val :
    ∑ j : Fin 6, W ((Equiv.refl (Fin 6)) j) ((Equiv.refl (Fin 6)) (finRotate 6 j)) = 34 := by
  rw [sum_fin6_eq]
  decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4804070.main) := by
  intro hmain
  let d : Fin 6 → Fin 6 → ℝ := fun i j => (W i j : ℝ)
  have hdiag : ∀ i, d i i = 0 := by
    intro i
    simp [d, W_diag i]
  have hsymm : ∀ i j, d i j = d j i := by
    intro i j
    simp [d, W_symm i j]
  have hnn : ∀ i j, 0 ≤ d i j := by
    intro i j
    exact Nat.cast_nonneg _
  have hdist : ∀ i j k l, i ≠ j → k ≠ l → d i j = d k l →
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
    intro i j k l hij hkl heq
    exact W_distinct i j k l hij hkl (Nat.cast_injective heq)
  obtain ⟨p, hopt, i, hspec⟩ := hmain 6 (by decide) d hdiag hsymm hnn hdist
  have hle_real : OMA.S_mse_4804070.tourLength d p ≤
      OMA.S_mse_4804070.tourLength d (Equiv.refl (Fin 6)) := hopt (Equiv.refl (Fin 6))
  have hle_nat :
      ∑ j : Fin 6, W (p j) (p (finRotate 6 j)) ≤
        ∑ j : Fin 6, W ((Equiv.refl (Fin 6)) j) ((Equiv.refl (Fin 6)) (finRotate 6 j)) := by
    have h1 : OMA.S_mse_4804070.tourLength d p =
        ((∑ j : Fin 6, W (p j) (p (finRotate 6 j)) : ℕ) : ℝ) := by
      unfold OMA.S_mse_4804070.tourLength
      exact sum_fin6_cast (fun j => W (p j) (p (finRotate 6 j)))
    have h2 : OMA.S_mse_4804070.tourLength d (Equiv.refl (Fin 6)) =
        ((∑ j : Fin 6, W ((Equiv.refl (Fin 6)) j) ((Equiv.refl (Fin 6)) (finRotate 6 j)) : ℕ) : ℝ) := by
      unfold OMA.S_mse_4804070.tourLength
      exact sum_fin6_cast (fun j => W ((Equiv.refl (Fin 6)) j) ((Equiv.refl (Fin 6)) (finRotate 6 j)))
    rw [h1, h2] at hle_real
    exact Nat.cast_le.mp hle_real
  rw [ref_tour_val] at hle_nat
  let g := finRotate 6
  let x0 := p i
  let x1 := p (g i)
  let x2 := p (g (g i))
  let x3 := p (g (g (g i)))
  let x4 := p (g (g (g (g i))))
  let x5 := p (g.symm i)
  have hsum : ∑ j : Fin 6, W (p j) (p (finRotate 6 j)) =
      W x0 x1 + W x1 x2 + W x2 x3 + W x3 x4 + W x4 x5 + W x5 x0 := by
    rw [sum_fin6_rot (fun j => W (p j) (p (finRotate 6 j))) i]
    have h5 : finRotate 6 (g (g (g (g i)))) = g.symm i := rot_five i
    have h6 : finRotate 6 (g.symm i) = i := (finRotate 6).apply_symm_apply i
    simp only [x0, x1, x2, x3, x4, x5, g, h5, h6]
  rw [hsum] at hle_nat
  obtain ⟨d01, d02, d03, d04, d05, d12, d13, d14, d15, d23, d24, d25, d34, d35, d45⟩ :=
    rot_distinct i
  have h01 : x0 ≠ x1 := p.injective.ne d01
  have h02 : x0 ≠ x2 := p.injective.ne d02
  have h03 : x0 ≠ x3 := p.injective.ne d03
  have h04 : x0 ≠ x4 := p.injective.ne d04
  have h05 : x0 ≠ x5 := p.injective.ne d05
  have h12 : x1 ≠ x2 := p.injective.ne d12
  have h13 : x1 ≠ x3 := p.injective.ne d13
  have h14 : x1 ≠ x4 := p.injective.ne d14
  have h15 : x1 ≠ x5 := p.injective.ne d15
  have h23 : x2 ≠ x3 := p.injective.ne d23
  have h24 : x2 ≠ x4 := p.injective.ne d24
  have h25 : x2 ≠ x5 := p.injective.ne d25
  have h34 : x3 ≠ x4 := p.injective.ne d34
  have h35 : x3 ≠ x5 := p.injective.ne d35
  have h45 : x4 ≠ x5 := p.injective.ne d45
  have hspec_nat : ∀ w : Fin 6, w ≠ x0 → w ≠ x5 → w ≠ x1 →
      W x0 x5 ≤ W x0 w ∧ W x0 x1 ≤ W x0 w := by
    intro w hw0 hw5 hw1
    have h := hspec w hw0 hw5 hw1
    exact ⟨Nat.cast_le.mp h.1, Nat.cast_le.mp h.2⟩
  rcases special_pair x0 x1 x5 h01 h05 h15 hspec_nat with ⟨hx1, hx5⟩ | ⟨hx1, hx5⟩
  · rw [hx1] at hle_nat h12 h13 h14
    rw [hx5] at hle_nat h25 h35 h45
    have hgt := tour_gt_fwd x0 x2 x3 x4 h02 h03 h04 h12 h13 h14
      h25.symm h35.symm h45.symm h23 h24 h34
    omega
  · rw [hx1] at hle_nat h12 h13 h14
    rw [hx5] at hle_nat h25 h35 h45
    have hgt := tour_gt_fwd x0 x4 x3 x2 h04 h03 h02 h45.symm h35.symm h25.symm
      h14 h13 h12 h34.symm h24.symm h23.symm
    have hrev : W x0 (best2 x0) + W (best2 x0) x2 + W x2 x3 + W x3 x4 +
        W x4 (best1 x0) + W (best1 x0) x0 =
        W x0 (best1 x0) + W (best1 x0) x4 + W x4 x3 + W x3 x2 +
        W x2 (best2 x0) + W (best2 x0) x0 := by
      rw [W_symm x0 (best2 x0), W_symm (best2 x0) x2, W_symm x2 x3,
        W_symm x3 x4, W_symm x4 (best1 x0), W_symm (best1 x0) x0]
      omega
    omega
