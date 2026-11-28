import OMAStatements.S_oeis_a270236
import Mathlib

open OMA.S_oeis_a270236

private abbrev mx (l : List ℕ) : ℕ := l.foldr max 0

private lemma foldr_max_v (l : List ℕ) (v : ℕ) : l.foldr max v = max (mx l) v := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons, mx] at ih ⊢; rw [ih]; omega

private lemma mx_append (l : List ℕ) (v : ℕ) : mx (l ++ [v]) = max (mx l) v := by
  simp only [mx, List.foldr_append, List.foldr_cons, List.foldr_nil]
  rw [show max v 0 = v by omega]
  exact foldr_max_v l v

private lemma mx_le (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) : mx l ≤ B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [mx, List.foldr_cons] at *
    have := h a (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    omega

private lemma rgf_append (l : List ℕ) (v : ℕ) :
    IsRGF (l ++ [v]) ↔ IsRGF l ∧ 1 ≤ v ∧ v ≤ mx l + 1 := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have hi := h ⟨i, by simp⟩
      simp only [Fin.getElem_fin, List.getElem_append_left i.2] at hi ⊢
      rwa [List.take_append_of_le_length (by omega)] at hi
    · have hi := h ⟨l.length, by simp⟩
      simp only [Fin.getElem_fin, List.getElem_concat_length] at hi
      rw [List.take_left' rfl] at hi
      exact hi
  · rintro ⟨h, h1, h2⟩ ⟨i, hi⟩
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i l.length with hl | hl
    · have := h ⟨i, hl⟩
      simp only [Fin.getElem_fin] at this ⊢
      simp only [List.getElem_append_left hl]
      rw [List.take_append_of_le_length (by omega)]
      exact this
    · obtain rfl : i = l.length := by omega
      simp only [Fin.getElem_fin, List.getElem_concat_length]
      rw [List.take_left' rfl]
      exact ⟨h1, h2⟩

private lemma rgf_le (l : List ℕ) (h : IsRGF l) : ∀ x ∈ l, x ≤ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l v ih =>
    rw [rgf_append] at h
    have hl := ih h.1
    have hm := mx_le l _ hl
    intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    simp only [List.length_append, List.length_singleton]
    rcases hx with hx | rfl
    · have := hl x hx; omega
    · omega

private lemma mem_rgfs (n : ℕ) (l : List ℕ) : l ∈ rgfs n ↔ l.length = n ∧ IsRGF l := by
  unfold rgfs
  simp only [Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨⟨f, -, rfl⟩, h⟩
    exact ⟨List.length_ofFn, h⟩
  · rintro ⟨rfl, h⟩
    refine ⟨⟨fun i => l[i], fun i => ?_, List.ofFn_getElem⟩, h⟩
    have := rgf_le l h l[i] (List.getElem_mem _)
    dsimp only
    omega

private lemma rgfs_zero : rgfs 0 = {[]} := by
  ext l
  rw [mem_rgfs, Finset.mem_singleton, List.length_eq_zero_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, fun i => i.elim0⟩

private lemma rgfs_succ (L : ℕ) : rgfs (L + 1) =
    (rgfs L).biUnion (fun l => (Finset.Icc 1 (mx l + 1)).image (fun v => l ++ [v])) := by
  ext l'
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Icc, mem_rgfs]
  constructor
  · rintro ⟨hlen, h⟩
    rcases List.eq_nil_or_concat l' with rfl | ⟨l, v, rfl⟩
    · simp at hlen
    · rw [List.concat_eq_append] at h hlen ⊢
      rw [rgf_append] at h
      simp only [List.length_append, List.length_singleton] at hlen
      exact ⟨l, ⟨by omega, h.1⟩, v, h.2, rfl⟩
  · rintro ⟨l, ⟨hlen, h⟩, v, hv, rfl⟩
    refine ⟨by simp [hlen], (rgf_append l v).2 ⟨h, hv⟩⟩

private lemma sum_succ (L : ℕ) (g : List ℕ → ℕ) :
    ∑ l' ∈ rgfs (L + 1), g l' = ∑ l ∈ rgfs L, ∑ v ∈ Finset.Icc 1 (mx l + 1), g (l ++ [v]) := by
  rw [rgfs_succ, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_image]
    intro v1 _ v2 _ h
    simpa using h
  · intro l1 _ l2 _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image] at hx1 hx2
    obtain ⟨v1, -, rfl⟩ := hx1
    obtain ⟨v2, -, h⟩ := hx2
    exact hne (by simpa using (congrArg List.dropLast h).symm)

private lemma innerS (x M c p : ℕ) :
    ∑ v ∈ Finset.Icc 1 (x + 1), (if max x v = M + 1 then c + (if v = p then 1 else 0) else 0) =
      (if x = M + 1 then (M + 1) * c + (if 1 ≤ p ∧ p ≤ M + 1 then 1 else 0) else 0) +
      (if x = M then c + (if p = M + 1 then 1 else 0) else 0) := by
  by_cases h1 : x = M + 1
  · subst h1
    rw [if_pos rfl, if_neg (show ¬ (M + 1 = M) by omega), add_zero, Finset.sum_Icc_succ_top (by omega),
      if_neg (show ¬ (max (M + 1) (M + 1 + 1) = M + 1) by omega), add_zero]
    rw [Finset.sum_congr rfl (g := fun v => c + (if v = p then 1 else 0)) (fun v hv => by
      simp only [Finset.mem_Icc] at hv; rw [if_pos (by omega)])]
    rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul, Finset.sum_ite_eq']
    simp only [Finset.mem_Icc]
    rw [show M + 1 + 1 - 1 = M + 1 by omega]
  · by_cases h0 : x = M
    · subst h0
      rw [if_neg h1, if_pos rfl, zero_add]
      rw [Finset.sum_congr rfl (g := fun v => if v = x + 1 then c + (if v = p then 1 else 0) else 0)
        (fun v hv => by
          simp only [Finset.mem_Icc] at hv
          by_cases hv' : v = x + 1
          · rw [if_pos (by omega), if_pos hv']
          · rw [if_neg (by omega), if_neg hv'])]
      rw [Finset.sum_ite_eq', if_pos (by simp)]
      by_cases hp : x + 1 = p
      · rw [if_pos hp, if_pos hp.symm]
      · rw [if_neg hp, if_neg (Ne.symm hp)]
    · rw [if_neg h1, if_neg h0, add_zero]
      apply Finset.sum_eq_zero
      intro v hv
      simp only [Finset.mem_Icc] at hv
      rw [if_neg (by omega)]

private def A (L M : ℕ) : ℕ := ∑ l ∈ rgfs L, (if mx l = M then 1 else 0)

private def Cc (L M p : ℕ) : ℕ := ∑ l ∈ rgfs L, (if mx l = M then l.count p else 0)

private lemma Cc_rec (L M p : ℕ) : Cc (L + 1) (M + 1) p = (M + 1) * Cc L (M + 1) p +
    (if 1 ≤ p ∧ p ≤ M + 1 then A L (M + 1) else 0) + Cc L M p + (if p = M + 1 then A L M else 0) := by
  unfold Cc A
  rw [sum_succ]
  have : ∀ l ∈ rgfs L, ∑ v ∈ Finset.Icc 1 (mx l + 1),
      (if mx (l ++ [v]) = M + 1 then (l ++ [v]).count p else 0) =
      (if mx l = M + 1 then (M + 1) * l.count p + (if 1 ≤ p ∧ p ≤ M + 1 then 1 else 0) else 0) +
      (if mx l = M then l.count p + (if p = M + 1 then 1 else 0) else 0) := by
    intro l _
    rw [← innerS]
    apply Finset.sum_congr rfl
    intro v _
    rw [mx_append, List.count_append, List.count_singleton]
    simp only [beq_iff_eq]
  rw [Finset.sum_congr rfl this]
  have e : ∀ l ∈ rgfs L,
      (if mx l = M + 1 then (M + 1) * l.count p + (if 1 ≤ p ∧ p ≤ M + 1 then 1 else 0) else 0) +
      (if mx l = M then l.count p + (if p = M + 1 then 1 else 0) else 0) =
      (M + 1) * (if mx l = M + 1 then l.count p else 0) +
      (if 1 ≤ p ∧ p ≤ M + 1 then 1 else 0) * (if mx l = M + 1 then 1 else 0) +
      (if mx l = M then l.count p else 0) + (if p = M + 1 then 1 else 0) * (if mx l = M then 1 else 0) := by
    intro l _; split_ifs <;> ring
  rw [Finset.sum_congr rfl e]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  split_ifs <;> ring

private lemma A_rec (L M : ℕ) : A (L + 1) (M + 1) = (M + 1) * A L (M + 1) + A L M := by
  unfold A
  rw [sum_succ, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  have h := innerS (mx l) M 1 0
  rw [Finset.sum_congr rfl (g := fun v => if max (mx l) v = M + 1 then 1 + (if v = 0 then 1 else 0) else 0)
    (fun v hv => by
      simp only [Finset.mem_Icc] at hv
      rw [mx_append, if_neg (show v ≠ 0 by omega), add_zero]), h]
  by_cases ha : mx l = M + 1 <;> by_cases hb : mx l = M <;> simp [ha, hb] <;> omega

private lemma A_zero (L : ℕ) : A (L + 1) 0 = 0 := by
  unfold A
  rw [sum_succ]
  apply Finset.sum_eq_zero
  intro l _
  apply Finset.sum_eq_zero
  intro v hv
  simp only [Finset.mem_Icc] at hv
  rw [mx_append, if_neg (by omega)]

private lemma Cc_zero (L p : ℕ) : Cc (L + 1) 0 p = 0 := by
  unfold Cc
  rw [sum_succ]
  apply Finset.sum_eq_zero
  intro l _
  apply Finset.sum_eq_zero
  intro v hv
  simp only [Finset.mem_Icc] at hv
  rw [mx_append, if_neg (by omega)]

private lemma A_base (M : ℕ) : A 0 M = if M = 0 then 1 else 0 := by
  unfold A; rw [rgfs_zero, Finset.sum_singleton]; simp [mx, eq_comm]

private lemma Cc_base (M p : ℕ) : Cc 0 M p = 0 := by
  unfold Cc; rw [rgfs_zero, Finset.sum_singleton]; simp; exact ite_self _

private lemma A_big (L : ℕ) : ∀ M, L < M → A L M = 0 := by
  induction L with
  | zero => intro M hM; rw [A_base, if_neg (by omega)]
  | succ L ih =>
    intro M hM
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    rw [A_rec, ih _ (by omega), ih _ (by omega)]; simp

private lemma A_diag (L : ℕ) : A L L = 1 := by
  induction L with
  | zero => rw [A_base, if_pos rfl]
  | succ L ih => rw [A_rec, A_big L (L + 1) (by omega), ih]; simp

private lemma A_sub1 (L : ℕ) : 2 * A (L + 1) L = (L + 1) * L := by
  induction L with
  | zero => rw [A_zero]
  | succ L ih => rw [A_rec, A_diag]; ring_nf; ring_nf at ih; omega

private lemma A_sub2 (L : ℕ) : 24 * A (L + 2) L = (L + 2) * (L + 1) * L * (3 * L + 1) := by
  induction L with
  | zero => rw [A_zero]
  | succ L ih =>
    rw [show L + 1 + 2 = (L + 2) + 1 by ring, A_rec]
    have h1 := A_sub1 (L + 1)
    rw [show L + 1 + 1 = L + 2 by ring] at h1
    nlinarith [h1, ih]

private lemma Cc_big (L : ℕ) : ∀ M p, L < M → Cc L M p = 0 := by
  induction L with
  | zero => intro M p _; exact Cc_base M p
  | succ L ih =>
    intro M p hM
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    rw [Cc_rec, ih _ _ (by omega), ih _ _ (by omega), A_big L _ (by omega), A_big L _ (by omega)]
    simp

private lemma Cc_small (L : ℕ) : ∀ M p, M < p → Cc L M p = 0 := by
  induction L with
  | zero => intro M p _; exact Cc_base M p
  | succ L ih =>
    intro M p hM
    rcases M with _ | M'
    · exact Cc_zero L p
    · rw [Cc_rec, ih _ _ (by omega), ih _ _ (by omega), if_neg (by omega), if_neg (by omega)]; simp

private lemma Cc_diag (L : ℕ) : ∀ p, 1 ≤ p → p ≤ L → Cc L L p = 1 := by
  induction L with
  | zero => intro p h1 h2; omega
  | succ L ih =>
    intro p h1 h2
    rw [Cc_rec, Cc_big L _ _ (by omega), A_big L _ (by omega)]
    rcases Nat.lt_or_ge p (L + 1) with h | h
    · rw [ih p h1 (by omega)]; simp [show p ≠ L + 1 by omega]
    · obtain rfl : p = L + 1 := by omega
      rw [Cc_small L _ _ (by omega), if_pos rfl, A_diag]; simp

private lemma T_eq (L p : ℕ) : T L p = ∑ M ∈ Finset.range (L + 1), Cc L M p := by
  unfold T Cc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_ite_eq, if_pos]
  rw [mem_rgfs] at hl
  have := mx_le l L (fun x hx => hl.1 ▸ rgf_le l hl.2 x hx)
  simp only [Finset.mem_range]; omega

private lemma X_eq (m : ℕ) : 2 * Cc (m + 2) (m + 1) (m + 1) = 2 * (m + 2) + (m + 1) * m := by
  rw [Cc_rec, Cc_diag (m + 1) (m + 1) (by omega) le_rfl, if_pos ⟨by omega, le_rfl⟩, A_diag,
    Cc_small (m + 1) m (m + 1) (by omega), if_pos rfl]
  have := A_sub1 m
  omega

private lemma T1 (m : ℕ) : T (m + 2) (m + 1) = Cc (m + 2) (m + 1) (m + 1) + 1 := by
  rw [T_eq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero
    (fun M hM => Cc_small _ M _ (by simp at hM; omega)), Cc_diag (m + 2) (m + 1) (by omega) (by omega)]
  ring

private lemma T2 (m : ℕ) : T (m + 3) (m + 1) = Cc (m + 3) (m + 1) (m + 1) +
    Cc (m + 3) (m + 2) (m + 1) + 1 := by
  rw [T_eq, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_eq_zero
    (fun M hM => Cc_small _ M _ (by simp at hM; omega)), Cc_diag (m + 3) (m + 1) (by omega) (by omega)]
  ring

theorem OMA.solution : type_of% @OMA.S_oeis_a270236.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 1 = m + 1 by omega, T1]
    have hx := X_eq m
    have : (m + 2) * (m + 1) = (m + 1) * m + 2 * (m + 1) := by ring
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 1 = m + 1 by omega, show m + 2 + 1 = m + 3 by ring, T2]
    have hx := X_eq m
    have hY : Cc (m + 3) (m + 2) (m + 1) = (m + 2) + 1 + Cc (m + 2) (m + 1) (m + 1) := by
      rw [show m + 3 = (m + 2) + 1 by ring, show m + 2 = (m + 1) + 1 by ring, Cc_rec]
      rw [Cc_diag (m + 1 + 1) (m + 1) (by omega) (by omega), if_pos ⟨by omega, by omega⟩, A_diag,
        if_neg (by omega)]
      ring
    have hZ : Cc (m + 3) (m + 1) (m + 1) = (m + 1) * Cc (m + 2) (m + 1) (m + 1) + A (m + 2) (m + 1) +
        A (m + 2) m := by
      rw [show m + 3 = (m + 2) + 1 by ring, Cc_rec, if_pos ⟨by omega, le_rfl⟩,
        Cc_small (m + 2) m (m + 1) (by omega), if_pos rfl]
      ring
    have h1 := A_sub1 (m + 1)
    have h2 := A_sub2 m
    rw [hY, hZ]
    push_cast
    have hx' : (2 : ℚ) * Cc (m + 2) (m + 1) (m + 1) = 2 * (m + 2) + (m + 1) * m := by exact_mod_cast hx
    have h1' : (2 : ℚ) * A (m + 1 + 1) (m + 1) = (m + 1 + 1) * (m + 1) := by exact_mod_cast h1
    have h2' : (24 : ℚ) * A (m + 2) m = (m + 2) * (m + 1) * m * (3 * m + 1) := by exact_mod_cast h2
    rw [show m + 1 + 1 = m + 2 by ring] at h1'
    push_cast at h1'
    linear_combination (((m : ℚ) + 1) / 2 + 1 / 2) * hx' + h1' / 2 + h2' / 24
