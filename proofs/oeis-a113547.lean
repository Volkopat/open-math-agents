import OMAStatements.S_oeis_a113547
import Mathlib

open OMA.S_oeis_a113547

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

private lemma A_base (M : ℕ) : A 0 M = if M = 0 then 1 else 0 := by
  unfold A; rw [rgfs_zero, Finset.sum_singleton]; simp [mx, eq_comm]

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

private lemma le_mx (L : List ℕ) (x : ℕ) (h : x ∈ L) : x ≤ mx L := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    simp only [mx, List.foldr_cons] at *
    rcases List.mem_cons.1 h with rfl | h'
    · omega
    · have := ih h'; omega

private lemma in_l (l : List ℕ) (h : IsRGF l) : ∀ v, 1 ≤ v → v ≤ mx l → v ∈ l := by
  induction l using List.reverseRecOn with
  | nil => intro v h1 h2; simp [mx] at h2; omega
  | append_singleton l w ih =>
    rw [rgf_append] at h
    intro v h1 h2
    rw [mx_append] at h2
    simp only [List.mem_append, List.mem_singleton]
    by_cases hv : v ≤ mx l
    · exact Or.inl (ih h.1 v h1 hv)
    · right; omega

private lemma mm_le (l : List ℕ) : maximin l ≤ l.length := by
  unfold maximin
  apply mx_le
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have h1 : l.idxOf (l.getD i 0) < l.length := by
    rw [List.idxOf_lt_length_iff]
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  omega

private lemma mm_append (l : List ℕ) (v : ℕ) (h : IsRGF l) (hv1 : 1 ≤ v) (hv : v ≤ mx l + 1) :
    maximin (l ++ [v]) = if v ≤ mx l then maximin l else l.length + 1 := by
  unfold maximin
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append, List.foldr_append]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  have hprev : (List.range l.length).map (fun i => (l ++ [v]).idxOf ((l ++ [v]).getD i 0) + 1) =
      (List.range l.length).map (fun i => l.idxOf (l.getD i 0) + 1) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    have hg : (l ++ [v]).getD i 0 = l.getD i 0 := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi,
        List.getElem_append_left hi]
    rw [hg, List.idxOf_append_of_mem]
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _
  rw [hprev]
  have hlast : (l ++ [v]).getD l.length 0 = v := by
    rw [List.getD_eq_getElem _ _ (by simp)]; simp
  rw [hlast, foldr_max_v]
  show max (maximin l) _ = if v ≤ mx l then maximin l else l.length + 1
  by_cases hle : v ≤ mx l
  · rw [if_pos hle]
    have hmem := in_l l h v hv1 hle
    rw [List.idxOf_append_of_mem hmem]
    -- the value v already occurs, so its term is among the previous ones
    have : l.idxOf v + 1 ≤ maximin l := by
      unfold maximin
      have hi : l.idxOf v < l.length := List.idxOf_lt_length_iff.2 hmem
      have key : l.idxOf (l.getD (l.idxOf v) 0) + 1 ∈
          (List.range l.length).map (fun i => l.idxOf (l.getD i 0) + 1) :=
        List.mem_map.2 ⟨l.idxOf v, List.mem_range.2 hi, rfl⟩
      rw [List.getD_eq_getElem _ _ hi, List.getElem_idxOf hi] at key
      exact le_mx _ _ key
    omega
  · rw [if_neg hle]
    have hnm : v ∉ l := by
      intro hm
      have := le_mx l v hm
      omega
    rw [List.idxOf_append_of_notMem hnm]
    simp only [List.idxOf_cons_self, add_zero]
    have := mm_le l
    omega

private def E (L m M : ℕ) : ℕ := ∑ l ∈ rgfs L, (if maximin l = m ∧ mx l = M then 1 else 0)

private lemma top_mm (l : List ℕ) (h : IsRGF l) : maximin (l ++ [mx l + 1]) = l.length + 1 := by
  rw [mm_append l _ h (by omega) le_rfl, if_neg (by omega)]

private lemma top_mx (l : List ℕ) : mx (l ++ [mx l + 1]) = mx l + 1 := by
  rw [mx_append]; omega

private lemma E_rec (L m M : ℕ) (hm : m ≤ L) : E (L + 1) m M = M * E L m M := by
  unfold E
  rw [sum_succ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [mem_rgfs] at hl
  rw [Finset.sum_Icc_succ_top (by omega), top_mm l hl.2, if_neg (by omega), add_zero]
  rw [Finset.sum_congr rfl (g := fun _ => if maximin l = m ∧ mx l = M then 1 else 0) (fun v hv => by
    simp only [Finset.mem_Icc] at hv
    rw [mm_append l v hl.2 hv.1 (by omega), if_pos hv.2, mx_append, show max (mx l) v = mx l by omega])]
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, show mx l + 1 - 1 = mx l by omega]
  by_cases h : maximin l = m ∧ mx l = M
  · simp [h]
  · rw [if_neg h]; simp

private lemma E_top (L M : ℕ) : E (L + 1) (L + 1) (M + 1) = A L M := by
  unfold E A
  rw [sum_succ]
  apply Finset.sum_congr rfl
  intro l hl
  rw [mem_rgfs] at hl
  rw [Finset.sum_Icc_succ_top (by omega), top_mm l hl.2, top_mx, hl.1]
  rw [Finset.sum_eq_zero (fun v hv => by
    simp only [Finset.mem_Icc] at hv
    rw [mm_append l v hl.2 hv.1 (by omega), if_pos hv.2]
    have := mm_le l
    rw [if_neg (by omega)])]
  by_cases h : mx l = M
  · rw [if_pos ⟨rfl, by omega⟩, if_pos h]
  · rw [if_neg (by omega), if_neg h]

private lemma E_top0 (L : ℕ) : E (L + 1) (L + 1) 0 = 0 := by
  unfold E
  rw [sum_succ]
  apply Finset.sum_eq_zero
  intro l _
  apply Finset.sum_eq_zero
  intro v hv
  simp only [Finset.mem_Icc] at hv
  rw [mx_append, if_neg (by omega)]

private lemma T_E (n m : ℕ) : T n m = ∑ M ∈ Finset.range (n + 1), E n m M := by
  unfold T E
  rw [Finset.card_filter, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [mem_rgfs] at hl
  have hb : mx l < n + 1 := by
    have := mx_le l n (fun x hx => hl.1 ▸ rgf_le l hl.2 x hx); omega
  by_cases hmm : maximin l = m
  · simp only [hmm, true_and, if_true]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hb)]
  · simp [hmm]

private lemma A21 : A 2 1 = 1 := by have := A_sub1 1; norm_num at this; omega
private lemma A32 : A 3 2 = 3 := by have := A_sub1 2; norm_num at this; omega
private lemma A31 : A 3 1 = 1 := by rw [show (3 : ℕ) = 2 + 1 from rfl, A_rec, A21, A_zero]

private lemma E3 (k M : ℕ) : E (k + 3) 3 M = (if M = 2 then 2 ^ k else 0) + (if M = 3 then 3 ^ k else 0) := by
  induction k with
  | zero =>
    rcases M with _ | M'
    · exact E_top0 2
    · rw [show (0 + 3 : ℕ) = 2 + 1 from rfl, E_top]
      rcases Nat.lt_or_ge M' 3 with h | h
      · interval_cases M'
        · rw [A_zero]; simp
        · rw [A21]; simp
        · rw [A_diag]; simp
      · rw [A_big 2 M' (by omega), if_neg (by omega), if_neg (by omega)]
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by ring, E_rec _ _ _ (by omega), ih]
    by_cases h2 : M = 2
    · subst h2; simp [pow_succ]; ring
    · by_cases h3 : M = 3
      · subst h3; simp [pow_succ]; ring
      · simp [h2, h3]

private lemma E4 (k M : ℕ) : E (k + 4) 4 M = (if M = 2 then 2 ^ k else 0) +
    (if M = 3 then 3 * 3 ^ k else 0) + (if M = 4 then 4 ^ k else 0) := by
  induction k with
  | zero =>
    rcases M with _ | M'
    · exact E_top0 3
    · rw [show (0 + 4 : ℕ) = 3 + 1 from rfl, E_top]
      rcases Nat.lt_or_ge M' 4 with h | h
      · interval_cases M'
        · rw [A_zero]; simp
        · rw [A31]; simp
        · rw [A32]; simp
        · rw [A_diag]; simp
      · rw [A_big 3 M' (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  | succ k ih =>
    rw [show k + 1 + 4 = (k + 4) + 1 by ring, E_rec _ _ _ (by omega), ih]
    by_cases h2 : M = 2
    · subst h2; simp [pow_succ]; ring
    · by_cases h3 : M = 3
      · subst h3; simp [pow_succ]; ring
      · by_cases h4 : M = 4
        · subst h4; simp [pow_succ]; ring
        · simp [h2, h3, h4]

theorem OMA.solution : type_of% @OMA.S_oeis_a113547.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [T_E, Finset.sum_congr rfl (fun M _ => E3 k M), Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq', if_pos (by simp), if_pos (by simp), show k + 3 - 3 = k by omega]
    rfl
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [T_E, Finset.sum_congr rfl (fun M _ => E4 k M), Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (by simp), if_pos (by simp),
      if_pos (by simp), show k + 4 - 4 = k by omega, show k + 4 - 3 = k + 1 by omega, pow_succ]
    ring
