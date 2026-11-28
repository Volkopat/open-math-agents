import OMAStatements.S_mo_377077
import Mathlib

open OMA.S_mo_377077

lemma sq_add_sq_zero {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 ∧ y = 0 := by
  have hx : x^2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y^2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact ⟨pow_eq_zero_iff (by norm_num) |>.mp hx, pow_eq_zero_iff (by norm_num) |>.mp hy⟩

lemma core (w1 w2 d1 d2 e1 e2 : ℝ)
    (E1 : w1^2 + w2^2 - 2 * (e1 * w1 + e2 * w2) = 0)
    (E2 : d1^2 + d2^2 + 2 * (e1 * d1 + e2 * d2) = 0)
    (P' : d1 * w2 - d2 * w1 = 0) :
    (d1 = 0 ∧ d2 = 0) ∨ (w1 = 0 ∧ w2 = 0) ∨ (d1 + w1 = 0 ∧ d2 + w2 = 0) := by
  have key : (d1 * w1 + d2 * w2) * ((d1 * w1 + d2 * w2) + (w1^2 + w2^2)) = 0 := by
    linear_combination (w1^2 + w2^2) * E2 - (d1 * w2 - d2 * w1 + 2 * (e1 * w2 - e2 * w1)) * P'
      + (d1 * w1 + d2 * w2) * E1
  rcases mul_eq_zero.mp key with k | k
  · have : (d1^2 + d2^2) * (w1^2 + w2^2) = 0 := by
      linear_combination (d1 * w1 + d2 * w2) * k + (d1 * w2 - d2 * w1) * P'
    rcases mul_eq_zero.mp this with k2 | k2
    · exact Or.inl (sq_add_sq_zero k2)
    · exact Or.inr (Or.inl (sq_add_sq_zero k2))
  · have : ((d1 + w1)^2 + (d2 + w2)^2) * (w1^2 + w2^2) = 0 := by
      linear_combination ((d1 + w1) * w1 + (d2 + w2) * w2) * k + (d1 * w2 - d2 * w1) * P'
    rcases mul_eq_zero.mp this with k2 | k2
    · exact Or.inr (Or.inr (sq_add_sq_zero k2))
    · exact Or.inr (Or.inl (sq_add_sq_zero k2))

/-- three distinct concyclic points of ℂ are not collinear -/
lemma noncollinear (a b c O : ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : ‖a - O‖ = ‖c - O‖) (h2 : ‖b - O‖ = ‖c - O‖) :
    (b - c).re * (c - a).im - (b - c).im * (c - a).re ≠ 0 := by
  intro P
  have s1 : ‖a - O‖^2 = ‖c - O‖^2 := by rw [h1]
  have s2 : ‖b - O‖^2 = ‖c - O‖^2 := by rw [h2]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at s1 s2 P
  rcases core (c.re - a.re) (c.im - a.im) (b.re - c.re) (b.im - c.im) (c.re - O.re) (c.im - O.im)
    (by linear_combination s1) (by linear_combination s2) (by linear_combination P) with
    ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
  · exact hbc (Complex.ext (by linarith) (by linarith))
  · exact hac (Complex.ext (by linarith) (by linarith))
  · exact hab (Complex.ext (by linarith) (by linarith))

lemma ortho_eq (a b c O H : ℂ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : ‖a - O‖ = ‖c - O‖) (h2 : ‖b - O‖ = ‖c - O‖)
    (ca : ((H - a) * (starRingEnd ℂ) (b - c)).re = 0)
    (cb : ((H - b) * (starRingEnd ℂ) (c - a)).re = 0) :
    H = a + b + c - 2 * O := by
  have hX := noncollinear a b c O hab hac hbc h1 h2
  have s1 : ‖a - O‖^2 = ‖c - O‖^2 := by rw [h1]
  have s2 : ‖b - O‖^2 = ‖c - O‖^2 := by rw [h2]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at s1 s2 hX
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im] at ca cb
  set x := H.re - (a.re + b.re + c.re - 2 * O.re)
  set y := H.im - (a.im + b.im + c.im - 2 * O.im)
  have Eq1 : x * (b.re - c.re) + y * (b.im - c.im) = 0 := by
    simp only [x, y]; linear_combination ca - s2
  have Eq2 : x * (c.re - a.re) + y * (c.im - a.im) = 0 := by
    simp only [x, y]; linear_combination cb + s1
  have hx : x * ((b.re - c.re) * (c.im - a.im) - (b.im - c.im) * (c.re - a.re)) = 0 := by
    linear_combination (c.im - a.im) * Eq1 - (b.im - c.im) * Eq2
  have hy : y * ((b.re - c.re) * (c.im - a.im) - (b.im - c.im) * (c.re - a.re)) = 0 := by
    linear_combination (b.re - c.re) * Eq2 - (c.re - a.re) * Eq1
  have x0 : x = 0 := (mul_eq_zero.mp hx).resolve_right hX
  have y0 : y = 0 := (mul_eq_zero.mp hy).resolve_right hX
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.mul_re]; norm_num; simp only [x] at x0; linarith
  · simp only [Complex.sub_im, Complex.add_im, Complex.mul_im]; norm_num; simp only [y] at y0; linarith

theorem OMA.solution : type_of% @OMA.S_mo_377077.main := by
  intro n hn A hA ⟨O, r, hr⟩ H hH
  set T := (Finset.univ : Finset (Fin n)).powersetCard 3 with hT
  -- formula for the orthocenter
  have hform : ∀ i : Fin n, ∀ p : Finset (Fin n), p.card = 2 → i ∉ p →
      H (insert i p) = A i + ∑ x ∈ p, A x - 2 * O := by
    intro i p hp hi
    obtain ⟨k, l, hkl, rfl⟩ := Finset.card_eq_two.mp hp
    have hik : i ≠ k := fun h => hi (by simp [h])
    have hil : i ≠ l := fun h => hi (by simp [h])
    have hmem : insert i {k, l} ∈ T := by
      rw [hT, Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem hi, hp]
    have hO := hH _ hmem
    have e := ortho_eq (A i) (A k) (A l) O (H (insert i {k, l}))
      (hA.ne hik) (hA.ne hil) (hA.ne hkl) (by rw [hr, hr]) (by rw [hr, hr])
      (hO i (by simp) k (by simp) l (by simp) hik hil hkl)
      (hO k (by simp) l (by simp) i (by simp) hkl hik.symm hil.symm)
    rw [e, Finset.sum_pair hkl]; ring
  have hdiff : ∀ i j : Fin n, ∀ p : Finset (Fin n), p.card = 2 → i ∉ p → j ∉ p →
      ‖H (insert i p) - H (insert j p)‖ = ‖A i - A j‖ := by
    intro i j p hp hi hj
    rw [hform i p hp hi, hform j p hp hj]; congr 1; ring
  set S := ((Finset.univ : Finset (Fin n)) ×ˢ (Finset.univ : Finset (Fin n))).filter
    (fun x => x.1 ≠ x.2) with hS
  set P : Fin n × Fin n → Finset (Finset (Fin n)) :=
    fun x => ((Finset.univ : Finset (Fin n)) \ {x.1, x.2}).powersetCard 2 with hP
  have hcard : ∀ x ∈ S, ((P x).card : ℝ) = ((n : ℝ) - 2) * ((n : ℝ) - 3) / 2 := by
    intro x hx
    have hne : x.1 ≠ x.2 := (Finset.mem_filter.mp hx).2
    simp only [hP, Finset.card_powersetCard]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hne, Nat.cast_choose_two, Nat.cast_sub (by omega)]
    push_cast; ring
  have step1 : ((n : ℝ) - 2) * ((n : ℝ) - 3) / 2 * ∑ i, ∑ j, ‖A i - A j‖ =
      ∑ x ∈ S, ∑ p ∈ P x, ‖A x.1 - A x.2‖ := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product' (f := fun i j => ((n : ℝ) - 2) * ((n : ℝ) - 3) / 2 * ‖A i - A j‖)]
    rw [hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · rw [Finset.sum_const, nsmul_eq_mul, hcard x (by rw [hS]; simp [h])]
    · rw [show x.1 = x.2 from not_not.mp h]; simp
  rw [step1, Finset.sum_sigma']
  have step2 : ∑ y ∈ S.sigma P, ‖A y.1.1 - A y.1.2‖ =
      ∑ y ∈ S.sigma P, ‖H (insert y.1.1 y.2) - H (insert y.1.2 y.2)‖ := by
    apply Finset.sum_congr rfl
    rintro ⟨x, p⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨_, hp⟩ := hy
    simp only [hP, Finset.mem_powersetCard, Finset.subset_sdiff] at hp
    obtain ⟨⟨_, hdisj⟩, hpc⟩ := hp
    rw [hdiff x.1 x.2 p hpc]
    · exact fun h => Finset.disjoint_left.mp hdisj h (by simp)
    · exact fun h => Finset.disjoint_left.mp hdisj h (by simp)
  rw [step2]
  set φ : (Σ _ : Fin n × Fin n, Finset (Fin n)) → Finset (Fin n) × Finset (Fin n) :=
    fun y => (insert y.1.1 y.2, insert y.1.2 y.2) with hφ
  have hmemSP : ∀ y ∈ S.sigma P, y.1.1 ≠ y.1.2 ∧ y.1.1 ∉ y.2 ∧ y.1.2 ∉ y.2 ∧ y.2.card = 2 := by
    rintro ⟨x, p⟩ hy
    rw [Finset.mem_sigma] at hy
    obtain ⟨hx, hp⟩ := hy
    simp only [hP, Finset.mem_powersetCard, Finset.subset_sdiff] at hp
    obtain ⟨⟨_, hdisj⟩, hpc⟩ := hp
    refine ⟨(Finset.mem_filter.mp hx).2, ?_, ?_, hpc⟩
    · exact fun h => Finset.disjoint_left.mp hdisj h (by simp)
    · exact fun h => Finset.disjoint_left.mp hdisj h (by simp)
  have hinter : ∀ i j : Fin n, ∀ p : Finset (Fin n), i ≠ j → i ∉ p → j ∉ p →
      insert i p ∩ insert j p = p := by
    intro i j p hij hi hj
    ext x
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact absurd (h1.symm.trans h2) hij
      · exact h2
      · exact h1
      · exact h1
    · intro h; exact ⟨Or.inr h, Or.inr h⟩
  have hinj : Set.InjOn φ (S.sigma P) := by
    rintro ⟨⟨i, j⟩, p⟩ hy ⟨⟨i', j'⟩, p'⟩ hy' heq
    obtain ⟨h1, h2, h3, _⟩ := hmemSP _ hy
    obtain ⟨h1', h2', h3', _⟩ := hmemSP _ hy'
    simp only [hφ, Prod.mk.injEq] at heq h1 h2 h3 h1' h2' h3'
    obtain ⟨e1, e2⟩ := heq
    have hpp : p = p' := by
      rw [← hinter i j p h1 h2 h3, ← hinter i' j' p' h1' h2' h3', e1, e2]
    subst hpp
    have hi : i = i' := by
      have : i ∈ insert i' p := e1 ▸ Finset.mem_insert_self i p
      rcases Finset.mem_insert.mp this with h | h
      · exact h
      · exact absurd h h2
    have hj : j = j' := by
      have : j ∈ insert j' p := e2 ▸ Finset.mem_insert_self j p
      rcases Finset.mem_insert.mp this with h | h
      · exact h
      · exact absurd h h3
    subst hi; subst hj; rfl
  have himg : (S.sigma P).image φ ⊆ T ×ˢ T := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨_, h2, h3, h4⟩ := hmemSP y hy
    simp only [hφ, hT, Finset.mem_product, Finset.mem_powersetCard]
    refine ⟨⟨Finset.subset_univ _, ?_⟩, ⟨Finset.subset_univ _, ?_⟩⟩
    · rw [Finset.card_insert_of_notMem h2, h4]
    · rw [Finset.card_insert_of_notMem h3, h4]
  rw [← Finset.sum_product']
  calc ∑ y ∈ S.sigma P, ‖H (insert y.1.1 y.2) - H (insert y.1.2 y.2)‖
      = ∑ z ∈ (S.sigma P).image φ, ‖H z.1 - H z.2‖ := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ z ∈ T ×ˢ T, ‖H z.1 - H z.2‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => norm_nonneg _)
