import OMAStatements.S_oeis_a156870

/-!
The conjecture is due to Jens Voß (2009), OEIS A156870,
https://oeis.org/A156870. The companion entry A156869 records the
removal-of-a-one observation of Franklin T. Adams-Watters.

Credit: @grp06
-/

namespace OMA.S_oeis_a156870

open Multiset

private def reciprocal (d : ℕ) : ℚ := 1 / (d : ℚ)

private def total (s : Multiset ℕ) : ℚ := (s.map reciprocal).sum

private def solutions (L : ℕ) (q : ℚ) : Set (Multiset ℕ) :=
  {s | s.card = L ∧ (∀ d ∈ s, 0 < d) ∧ total s = q}

private theorem total_add (s t : Multiset ℕ) : total (s + t) = total s + total t := by
  simp only [total, Multiset.map_add, Multiset.sum_add]

private theorem total_cons (d : ℕ) (s : Multiset ℕ) :
    total (d ::ₘ s) = reciprocal d + total s := by
  simp only [total, Multiset.map_cons, Multiset.sum_cons]

private theorem total_replicate (L d : ℕ) :
    total (replicate L d) = (L : ℚ) * reciprocal d := by
  simp only [total, Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]

private theorem reciprocal_pos {d : ℕ} (hd : 0 < d) : 0 < reciprocal d := by
  unfold reciprocal
  exact one_div_pos.mpr (by exact_mod_cast hd)

private theorem reciprocal_le {b d : ℕ} (hb : 0 < b) (hbd : b ≤ d) :
    reciprocal d ≤ reciprocal b := by
  unfold reciprocal
  exact one_div_le_one_div_of_le (by exact_mod_cast hb) (by exact_mod_cast hbd)

private theorem total_le (s : Multiset ℕ) (c : ℚ)
    (h : ∀ d ∈ s, reciprocal d ≤ c) : total s ≤ (s.card : ℚ) * c := by
  have hs := Multiset.sum_le_card_nsmul (s.map reciprocal) c (by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hx
    exact h d hd)
  simpa only [total, Multiset.card_map, nsmul_eq_mul] using hs

private theorem total_nonneg (s : Multiset ℕ) (hp : ∀ d ∈ s, 0 < d) :
    0 ≤ total s := by
  unfold total
  apply Multiset.sum_nonneg
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hx
  exact (reciprocal_pos (hp d hd)).le

-- Every denominator other than one contributes at most one half.
private theorem enough_ones {n m : ℕ} {s : Multiset ℕ}
    (hs : s ∈ solutions (2 * n + m) ((n : ℚ) + m)) : m ≤ s.count 1 := by
  obtain ⟨hc, hp, hq⟩ := hs
  let u := s.filter (fun d => ¬ 1 = d)
  have hone : s.filter (fun d => 1 = d) = replicate (s.count 1) 1 := by
    apply Multiset.eq_replicate.mpr
    refine ⟨(Multiset.count_eq_card_filter_eq s 1).symm, ?_⟩
    intro d hd
    exact (Multiset.mem_filter.mp hd).2.symm
  have hsplit : replicate (s.count 1) 1 + u = s := by
    rw [← hone]
    exact Multiset.filter_add_not (fun d : ℕ => 1 = d) s
  have hlen : s.count 1 + u.card = 2 * n + m := by
    simpa only [Multiset.card_add, Multiset.card_replicate, hc] using
      congrArg Multiset.card hsplit
  have hlenQ : (s.count 1 : ℚ) + (u.card : ℚ) = 2 * (n : ℚ) + m := by
    exact_mod_cast hlen
  have hbound : total u ≤ (u.card : ℚ) * (1 / 2) := by
    apply total_le
    intro d hd
    have hmem : d ∈ s ∧ ¬ 1 = d := Multiset.mem_filter.mp hd
    have hdpos := hp d hmem.1
    have hd2 : 2 ≤ d := by
      have hne := hmem.2
      omega
    exact reciprocal_le (by decide : 0 < (2 : ℕ)) hd2
  have hsum : (s.count 1 : ℚ) + total u = (n : ℚ) + m := by
    have h := congrArg total hsplit
    rw [total_add, total_replicate, hq] at h
    simpa [reciprocal] using h
  have h : (m : ℚ) ≤ (s.count 1 : ℚ) := by linarith
  exact_mod_cast h

private theorem solutions_finite (L : ℕ) (q : ℚ) : (solutions L q).Finite := by
  classical
  induction L using Nat.strong_induction_on generalizing q with
  | h L ih =>
    by_cases hL : L = 0
    · refine (Set.finite_singleton (0 : Multiset ℕ)).subset ?_
      intro s hs
      have hc : s.card = L := hs.1
      exact Set.mem_singleton_iff.mpr (Multiset.card_eq_zero.mp (hc.trans hL))
    by_cases hpop : (solutions L q).Nonempty
    · obtain ⟨s, hs⟩ := hpop
      obtain ⟨hc, hp, hsum⟩ := hs
      have hs0 : s ≠ 0 := by
        intro he
        apply hL
        simpa [he] using hc.symm
      obtain ⟨d, hd⟩ := Multiset.exists_mem_of_ne_zero hs0
      have hq : 0 < q := by
        have he := congrArg total (Multiset.cons_erase hd)
        rw [total_cons, hsum] at he
        have hpos := reciprocal_pos (hp d hd)
        have htail := total_nonneg (s.erase d) (fun x hx => hp x (mem_of_mem_erase hx))
        linarith
      obtain ⟨B, hB⟩ := exists_nat_gt ((L : ℚ) / q)
      have hBmul : (L : ℚ) < (B : ℚ) * q := (div_lt_iff₀ hq).mp hB
      have hnonneg : 0 ≤ (L : ℚ) / q :=
        div_nonneg (by positivity) hq.le
      have hBposQ : 0 < (B : ℚ) := hnonneg.trans_lt hB
      have hBpos : 0 < B := by exact_mod_cast hBposQ
      have hcut : (L : ℚ) / (B : ℚ) < q := (div_lt_iff₀ hBposQ).mpr
        (by simpa only [mul_comm q (B : ℚ)] using hBmul)
      -- Each solution can be recovered by inserting one bounded denominator.
      let U : Fin (B + 1) → Set (Multiset ℕ) := fun i =>
        (fun t => (i : ℕ) ::ₘ t) '' solutions (L - 1) (q - reciprocal (i : ℕ))
      have hU : (⋃ i, U i).Finite := by
        apply Set.finite_iUnion
        intro i
        exact (ih (L - 1) (by omega) (q - reciprocal (i : ℕ))).image _
      refine hU.subset ?_
      intro t ht
      obtain ⟨htc, htp, htq⟩ := ht
      have hsmall : ∃ b ∈ t, b ≤ B := by
        by_contra! h
        have hle := total_le t (reciprocal B) (fun b hb =>
          reciprocal_le hBpos (by have := h b hb; omega))
        rw [htq, htc, reciprocal, mul_one_div] at hle
        exact (not_lt_of_ge hle) hcut
      obtain ⟨b, hb, hbB⟩ := hsmall
      let i : Fin (B + 1) := ⟨b, by omega⟩
      have he := Multiset.cons_erase hb
      have hm : t.erase b ∈ solutions (L - 1) (q - reciprocal b) := by
        refine ⟨?_, fun x hx => htp x (mem_of_mem_erase hx), ?_⟩
        · have hcard := Multiset.card_erase_add_one hb
          omega
        · have hsum' := congrArg total he
          rw [total_cons, htq] at hsum'
          linarith
      exact Set.mem_iUnion.mpr ⟨i, ⟨t.erase b, hm, he⟩⟩
    · have he : solutions L q = ∅ := Set.not_nonempty_iff_eq_empty.mp hpop
      rw [he]
      exact Set.finite_empty

private def addOnes (m : ℕ) (s : Multiset ℕ) : Multiset ℕ := replicate m 1 + s

private theorem addOnes_injective (m : ℕ) : Function.Injective (addOnes m) := by
  intro s t h
  exact add_left_cancel h

private theorem addOnes_mem_iff {m L : ℕ} {q : ℚ} {s : Multiset ℕ} :
    addOnes m s ∈ solutions (L + m) (q + m) ↔ s ∈ solutions L q := by
  change (addOnes m s).card = L + m ∧
      (∀ d ∈ addOnes m s, 0 < d) ∧ total (addOnes m s) = q + m ↔
    s.card = L ∧ (∀ d ∈ s, 0 < d) ∧ total s = q
  have hsum : total (addOnes m s) = (m : ℚ) + total s := by
    simp [addOnes, total_add, total_replicate, reciprocal]
  rw [hsum]
  simp only [addOnes, Multiset.card_add, Multiset.card_replicate]
  constructor
  · rintro ⟨hc, hp, hq⟩
    exact ⟨by omega, fun d hd => hp d (Multiset.mem_add.mpr (Or.inr hd)), by linarith⟩
  · rintro ⟨hc, hp, hq⟩
    refine ⟨by omega, ?_, by linarith⟩
    intro d hd
    rcases Multiset.mem_add.mp hd with hd | hd
    · rw [Multiset.eq_of_mem_replicate hd]
      decide
    · exact hp d hd

private theorem nonnegative_image (n m : ℕ) :
    addOnes m '' solutions (2 * n) n = solutions (2 * n + m) ((n : ℚ) + m) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact addOnes_mem_iff.mpr hs
  · intro s hs
    have hle : replicate m (1 : ℕ) ≤ s := by
      apply Multiset.le_iff_count.mpr
      intro d
      by_cases hd : d = 1
      · subst d
        rw [Multiset.count_replicate_self]
        exact enough_ones hs
      · rw [Multiset.count_replicate, if_neg (Ne.symm hd)]
        exact Nat.zero_le _
    have he : addOnes m (s - replicate m 1) = s := add_tsub_cancel_of_le hle
    refine ⟨s - replicate m 1, (addOnes_mem_iff (m := m)).mp ?_, he⟩
    rwa [he]

private theorem negative_image (n r : ℕ) (hr : 1 ≤ r) (hrn : r < n) :
    addOnes r '' solutions (2 * n - r) (↑(n - r) : ℚ) ⊂ solutions (2 * n) n := by
  have hlen : 2 * n - r + r = 2 * n := by omega
  have hq : (↑(n - r) : ℚ) + (r : ℚ) = (n : ℚ) := by
    exact_mod_cast (show n - r + r = n by omega)
  have hsub : addOnes r '' solutions (2 * n - r) (↑(n - r) : ℚ) ⊆
      solutions (2 * n) n := by
    rintro _ ⟨s, hs, rfl⟩
    have ht := (addOnes_mem_iff (m := r)).mpr hs
    rwa [hlen, hq] at ht
  apply (Set.ssubset_iff_of_subset hsub).mpr
  refine ⟨replicate (2 * n) 2, ?_, ?_⟩
  · refine ⟨Multiset.card_replicate _ _, ?_, ?_⟩
    · intro d hd
      rw [Multiset.eq_of_mem_replicate hd]
      decide
    · change total (replicate (2 * n) 2) = (n : ℚ)
      rw [total_replicate]
      unfold reciprocal
      push_cast <;> ring
  · rintro ⟨s, _, he⟩
    have hm : (1 : ℕ) ∈ addOnes r s :=
      Multiset.mem_add.mpr (Or.inl (Multiset.mem_replicate.mpr ⟨by omega, rfl⟩))
    rw [he] at hm
    have h12 : (1 : ℕ) = 2 := Multiset.eq_of_mem_replicate hm
    omega

end OMA.S_oeis_a156870

open OMA.S_oeis_a156870 in
theorem OMA.solution : type_of% @OMA.S_oeis_a156870.main := by
  intro n _
  constructor
  · intro m
    change (solutions (2 * n + m) (↑(n + m) : ℚ)).ncard = (solutions (2 * n) n).ncard
    rw [Nat.cast_add, ← nonnegative_image]
    exact Set.ncard_image_of_injective _ (addOnes_injective m)
  · intro r hr hrn
    change (solutions (2 * n - r) (↑(n - r) : ℚ)).ncard ≠ (solutions (2 * n) n).ncard
    have hlt := Set.ncard_lt_ncard (negative_image n r hr hrn) (solutions_finite (2 * n) n)
    rw [Set.ncard_image_of_injective _ (addOnes_injective r)] at hlt
    exact ne_of_lt hlt
