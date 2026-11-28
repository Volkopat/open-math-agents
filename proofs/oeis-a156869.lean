import OMAStatements.S_oeis_a156869

open OMA.S_oeis_a156869

private def egyptSolutions (n : ℕ) (q : ℚ) : Set (Multiset ℕ) :=
  {s | s.card = n ∧ (∀ x ∈ s, 0 < x) ∧ (s.map (fun x : ℕ => (1 : ℚ) / x)).sum = q}

/-- A solution of length `n+1` has a least denominator at most `(n+1)/q`.
Removing it leaves one of finitely many shorter solution sets. -/
private lemma egypt_rat_finite (n : ℕ) (q : ℚ) : (egyptSolutions n q).Finite := by
  classical
  induction n generalizing q with
  | zero =>
    refine (Set.finite_singleton (0 : Multiset ℕ)).subset ?_
    intro s hs
    exact Multiset.card_eq_zero.mp hs.1
  | succ n ih =>
    let sizes := Finset.range (⌊((n + 1 : ℕ) : ℚ) / q⌋₊ + 1)
    let extend (d : ℕ) := Multiset.cons d '' egyptSolutions n (q - 1 / d)
    have hf : (⋃ d ∈ (sizes : Set ℕ), extend d).Finite :=
      sizes.finite_toSet.biUnion fun d _ => (ih (q - 1 / d)).image (Multiset.cons d)
    refine hf.subset ?_
    rintro s ⟨hcard, hpos, hsum⟩
    obtain ⟨d, hd, hmin⟩ := Multiset.exists_min_image id
      (Multiset.card_pos.mp (show 0 < s.card by omega))
    have hdpos : (0 : ℚ) < d := by exact_mod_cast hpos d hd
    have hbound := (s.map (fun x : ℕ => (1 : ℚ) / x)).sum_le_card_nsmul (1 / d) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      exact one_div_le_one_div_of_le hdpos (by exact_mod_cast hmin x hx))
    simp only [hsum, Multiset.card_map, hcard, nsmul_eq_mul, mul_one_div] at hbound
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hd
    simp only [Multiset.map_cons, Multiset.sum_cons] at hsum
    have hnonneg : 0 ≤ (t.map (fun x : ℕ => (1 : ℚ) / x)).sum := by
      apply Multiset.sum_nonneg
      intro y hy
      obtain ⟨x, _, rfl⟩ := Multiset.mem_map.mp hy
      positivity
    have hq : 0 < q := by linarith [one_div_pos.mpr hdpos]
    have hsize : d ∈ sizes := by
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply Nat.le_floor
      apply (le_div_iff₀ hq).mpr
      simpa [mul_comm] using (le_div_iff₀ hdpos).mp hbound
    refine Set.mem_iUnion₂.mpr ⟨d, hsize, t, ?_, rfl⟩
    refine ⟨by simpa using hcard, fun x hx => hpos x (Multiset.mem_cons_of_mem hx), ?_⟩
    linarith

private lemma egypt_finite (n k : ℕ) : (seqs n k).Finite :=
  egypt_rat_finite n k

private lemma egypt_ones {n m : ℕ} {s : Multiset ℕ}
    (hs : s ∈ seqs (2*n+m) (n+m)) : m ≤ s.count 1 := by
  obtain ⟨hcard, hpos, hsum⟩ := hs
  have bound (t : Multiset ℕ) (ht : ∀ x ∈ t, 0 < x) :
      2 * (t.map (fun x : ℕ => (1 : ℚ) / x)).sum ≤ t.card + (t.count 1 : ℚ) := by
    induction t using Multiset.induction_on with
    | empty => simp
    | cons x t ih =>
      have hx := ht x (Multiset.mem_cons_self _ _)
      have hi := ih (fun y hy => ht y (Multiset.mem_cons_of_mem hy))
      by_cases he : x = 1
      · subst x
        simp only [Multiset.map_cons, Nat.cast_one, div_one, Multiset.sum_cons,
          Multiset.card_cons, Multiset.count_cons_self, Nat.cast_add]
        linarith
      · have hxq : (2 : ℚ) ≤ x := by exact_mod_cast (show 2 ≤ x by omega)
        have hrec : (1 : ℚ) / x ≤ 1 / 2 := by apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hxq
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          Multiset.count_cons_of_ne (Ne.symm he), Nat.cast_add, Nat.cast_one]
        linarith
  have h := bound s hpos
  rw [hcard, hsum] at h
  push_cast at h
  exact_mod_cast (show (m : ℚ) ≤ s.count 1 by linarith)

private lemma egypt_add_iff (a b r : ℕ) (s : Multiset ℕ) :
    s + Multiset.replicate r 1 ∈ seqs (a+r) (b+r) ↔ s ∈ seqs a b := by
  simp only [seqs, Set.mem_ofPred_eq, Multiset.card_add, Multiset.card_replicate,
    Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
    Nat.cast_one, div_one, Multiset.sum_replicate, nsmul_eq_mul, mul_one,
    Nat.cast_add, add_left_inj]
  constructor
  · rintro ⟨hc, hp, ht⟩
    exact ⟨hc, fun x hx => hp x (Multiset.mem_add.mpr (Or.inl hx)), ht⟩
  · rintro ⟨hc, hp, ht⟩
    refine ⟨hc, ?_, ht⟩
    intro x hx
    rcases Multiset.mem_add.mp hx with h|h
    · exact hp x h
    · have he := Multiset.eq_of_mem_replicate h
      omega

private lemma egypt_add_ones {a b : ℕ} {s : Multiset ℕ} (hs : s ∈ seqs a b) (r : ℕ) :
    s + Multiset.replicate r 1 ∈ seqs (a+r) (b+r) :=
  (egypt_add_iff a b r s).mpr hs

private lemma egypt_positive
    (ones : ∀ {n m : ℕ} {s : Multiset ℕ}, s ∈ seqs (2*n+m) (n+m) → m ≤ s.count 1)
    (n m : ℕ) : T (2*n+m) (n+m) = T (2*n) n := by
  let f (s : Multiset ℕ) := s + Multiset.replicate m 1
  have image_eq : f '' seqs (2*n) n = seqs (2*n+m) (n+m) := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact egypt_add_ones ht m
    · intro hs
      have le : Multiset.replicate m 1 ≤ s := Multiset.le_count_iff_replicate_le.mp (ones hs)
      let t := s - Multiset.replicate m 1
      have he : f t = s := tsub_add_cancel_of_le le
      refine ⟨t, (egypt_add_iff (2*n) n m t).mp ?_, he⟩
      change f t ∈ _
      rwa [he]
  unfold T
  rw [← image_eq]
  exact Set.ncard_image_of_injective _ (fun _ _ h => add_right_cancel h)

private lemma egypt_negative (fin : ∀ a b, (seqs a b).Finite) (n r : ℕ)
    (hr : 1 ≤ r) (hrn : r < n) : T (2*n-r) (n-r) ≠ T (2*n) n := by
  let append (s : Multiset ℕ) := s + Multiset.replicate r 1
  let twos := Multiset.replicate (2*n) 2
  have member : twos ∈ seqs (2*n) n := by
    refine ⟨Multiset.card_replicate .., ?_, ?_⟩
    · intro x hx
      have : x = 2 := Multiset.eq_of_mem_replicate hx
      omega
    · simp [twos, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
      ring
  have strict : append '' seqs (2*n-r) (n-r) ⊂ seqs (2*n) n := by
    constructor
    · rintro _ ⟨s, hs, rfl⟩
      simpa [append, Nat.sub_add_cancel (show r ≤ 2*n by omega), Nat.sub_add_cancel hrn.le] using
        egypt_add_ones hs r
    · intro cover
      obtain ⟨s, _, heq⟩ := cover member
      have hone : 1 ∈ append s := Multiset.mem_add.mpr (Or.inr (Multiset.mem_replicate.mpr ⟨by omega,rfl⟩))
      rw [heq] at hone
      have : (1 : ℕ) = 2 := Multiset.eq_of_mem_replicate hone
      omega
  have smaller := Set.ncard_lt_ncard strict (fin _ _)
  have injective : Function.Injective append := fun _ _ h => add_right_cancel h
  rw [Set.ncard_image_of_injective _ injective] at smaller
  exact smaller.ne

theorem OMA.solution : type_of% @OMA.S_oeis_a156869.main := by
  intro n _
  exact ⟨egypt_positive (fun hs => egypt_ones hs) n, egypt_negative egypt_finite n⟩
