import OMAStatements.S_oeis_a338169

-- Problem: A338169: A list of all finite sequences of distinct positive integers sorted by their maximum value, then lexicographically.
-- Upstream: formal-conjectures statements/oeis-a338169.lean:0 (declaration OMA.S_oeis_a338169.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the sequences with maximum n are the orderings of insert n t for the subsets t of
-- 1..n-1; each t gives (|t|+1)! lists, all with sum n + sum(t). The reflection x -> n - x maps
-- the subsets of 1..n-1 onto themselves and keeps their size, so the sum over t of
-- w(|t|) * sum(t) equals the sum of w(|t|) * n|t|/2. Grouping the subsets by size, the total is
-- Sum_j binomial(n-1,j) (j+1)! (n + n j/2), which agrees termwise with the formula of A281912.

namespace S07A338169

open OMA.S_oeis_a338169 Finset

/-- The reflection x -> n - x of a set. -/
def Rf (n : ℕ) (t : Finset ℕ) : Finset ℕ := t.image (fun x => n - x)

theorem notMem_U (n : ℕ) (hn : 1 ≤ n) (t : Finset ℕ) (ht : t ⊆ Icc 1 (n - 1)) : n ∉ t := by
  intro h
  have := Finset.mem_Icc.mp (ht h)
  omega

theorem mem_Lp (n : ℕ) (t : Finset ℕ) (l : List ℕ) :
    l ∈ (insert n t).toList.permutations.toFinset ↔ l.Perm (insert n t).toList := by
  rw [List.mem_toFinset, List.mem_permutations]

theorem mem_Fs (n : ℕ) (hn : 1 ≤ n) (l : List ℕ) :
    l ∈ (Icc 1 (n - 1)).powerset.biUnion (fun t => (insert n t).toList.permutations.toFinset) ↔ IsSeq n l := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨t, ht, hl⟩
    rw [Finset.mem_powerset] at ht
    rw [mem_Lp] at hl
    refine ⟨hl.nodup_iff.mpr (Finset.nodup_toList _), ?_, ?_⟩
    · intro x hx
      have hx2 : x ∈ insert n t := Finset.mem_toList.mp (hl.subset hx)
      rcases Finset.mem_insert.mp hx2 with h | h
      · omega
      · have := Finset.mem_Icc.mp (ht h)
        omega
    · exact hl.symm.subset (Finset.mem_toList.mpr (Finset.mem_insert_self n t))
  · rintro ⟨hnd, hr, hmem⟩
    refine ⟨l.toFinset.erase n, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_erase, List.mem_toFinset] at hx
      have := hr x hx.2
      rw [Finset.mem_Icc]
      omega
    · rw [mem_Lp]
      apply List.perm_of_nodup_nodup_toFinset_eq hnd (Finset.nodup_toList _)
      rw [Finset.toList_toFinset, Finset.insert_erase (List.mem_toFinset.mpr hmem)]

theorem disj (n : ℕ) (hn : 1 ≤ n) :
    ((Icc 1 (n - 1)).powerset : Set (Finset ℕ)).PairwiseDisjoint
      (fun t => (insert n t).toList.permutations.toFinset) := by
  intro t1 ht1 t2 ht2 hne
  show Disjoint ((insert n t1).toList.permutations.toFinset)
    ((insert n t2).toList.permutations.toFinset)
  rw [Finset.disjoint_left]
  intro l h1 h2
  apply hne
  rw [Finset.mem_coe, Finset.mem_powerset] at ht1 ht2
  rw [mem_Lp] at h1 h2
  have e : insert n t1 = insert n t2 := by
    rw [← Finset.toList_toFinset (insert n t1), ← Finset.toList_toFinset (insert n t2),
      ← List.toFinset_eq_of_perm _ _ h1, ← List.toFinset_eq_of_perm _ _ h2]
  rw [← Finset.erase_insert (notMem_U n hn t1 ht1), e,
    Finset.erase_insert (notMem_U n hn t2 ht2)]

theorem sum_Lp (n : ℕ) (hn : 1 ≤ n) (t : Finset ℕ) (ht : t ⊆ Icc 1 (n - 1)) :
    ∑ l ∈ (insert n t).toList.permutations.toFinset, (l.sum : ℚ) = ((t.card + 1).factorial : ℚ) * ((n : ℚ) + ∑ x ∈ t, (x : ℚ)) := by
  have hnt := notMem_U n hn t ht
  have hs : ∀ l ∈ (insert n t).toList.permutations.toFinset, (l.sum : ℚ) = (n : ℚ) + ∑ x ∈ t, (x : ℚ) := by
    intro l hl
    rw [mem_Lp] at hl
    rw [hl.sum_eq, Finset.sum_toList, Finset.sum_insert hnt, Nat.cast_add, Nat.cast_sum]
  have hc : ((insert n t).toList.permutations.toFinset).card = (t.card + 1).factorial := by
    rw [List.toFinset_card_of_nodup (List.nodup_permutations _ (Finset.nodup_toList _)),
      List.length_permutations, Finset.length_toList, Finset.card_insert_of_notMem hnt]
  rw [Finset.sum_congr rfl hs, Finset.sum_const, hc, nsmul_eq_mul]

theorem sum_Fs (n : ℕ) (hn : 1 ≤ n) :
    ∑ l ∈ (Icc 1 (n - 1)).powerset.biUnion (fun t => (insert n t).toList.permutations.toFinset), (l.sum : ℚ) =
      ∑ t ∈ (Icc 1 (n - 1)).powerset,
        ((t.card + 1).factorial : ℚ) * ((n : ℚ) + ∑ x ∈ t, (x : ℚ)) := by
  rw [Finset.sum_biUnion (disj n hn)]
  apply Finset.sum_congr rfl
  intro t ht
  exact sum_Lp n hn t (Finset.mem_powerset.mp ht)

theorem Rf_inj (n : ℕ) (t : Finset ℕ) (ht : t ⊆ Icc 1 (n - 1)) :
    Set.InjOn (fun x => n - x) (t : Set ℕ) := by
  intro x hx y hy hxy
  have h1 := Finset.mem_Icc.mp (ht (Finset.mem_coe.mp hx))
  have h2 := Finset.mem_Icc.mp (ht (Finset.mem_coe.mp hy))
  have h3 : n - x = n - y := hxy
  omega

theorem Rf_sub (n : ℕ) (t : Finset ℕ) (ht : t ⊆ Icc 1 (n - 1)) : Rf n t ⊆ Icc 1 (n - 1) := by
  intro y hy
  unfold Rf at hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have := Finset.mem_Icc.mp (ht hx)
  rw [Finset.mem_Icc]
  omega

theorem Rf_Rf (n : ℕ) (t : Finset ℕ) (ht : t ⊆ Icc 1 (n - 1)) : Rf n (Rf n t) = t := by
  ext y
  unfold Rf
  rw [Finset.mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have := Finset.mem_Icc.mp (ht hx)
    rw [show n - (n - x) = x by omega]
    exact hx
  · intro hy
    have := Finset.mem_Icc.mp (ht hy)
    refine ⟨n - y, ?_, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨y, hy, rfl⟩
    · omega

theorem Rf_card (n : ℕ) (t : Finset ℕ) (ht : t ⊆ Icc 1 (n - 1)) : (Rf n t).card = t.card :=
  Finset.card_image_of_injOn (Rf_inj n t ht)

theorem pair_sum (n : ℕ) (t : Finset ℕ) (ht : t ⊆ Icc 1 (n - 1)) :
    ∑ x ∈ t, (x : ℚ) + ∑ y ∈ Rf n t, (y : ℚ) = (n : ℚ) * (t.card : ℚ) := by
  have h5 : ∑ y ∈ Rf n t, (y : ℚ) = ∑ x ∈ t, ((n - x : ℕ) : ℚ) :=
    Finset.sum_image (Rf_inj n t ht)
  have h6 : ∀ x ∈ t, (x : ℚ) + ((n - x : ℕ) : ℚ) = (n : ℚ) := by
    intro x hx
    have := Finset.mem_Icc.mp (ht hx)
    rw [Nat.cast_sub (by omega : x ≤ n)]
    ring
  rw [h5, ← Finset.sum_add_distrib, Finset.sum_congr rfl h6, Finset.sum_const, nsmul_eq_mul]
  ring

theorem sym_sum (n : ℕ) (w : ℕ → ℚ) :
    ∑ t ∈ (Icc 1 (n - 1)).powerset, w t.card * ∑ y ∈ Rf n t, (y : ℚ) =
      ∑ t ∈ (Icc 1 (n - 1)).powerset, w t.card * ∑ x ∈ t, (x : ℚ) := by
  apply Finset.sum_nbij' (Rf n) (Rf n)
  · intro t ht
    rw [Finset.mem_powerset] at ht ⊢
    exact Rf_sub n t ht
  · intro t ht
    rw [Finset.mem_powerset] at ht ⊢
    exact Rf_sub n t ht
  · intro t ht
    exact Rf_Rf n t (Finset.mem_powerset.mp ht)
  · intro t ht
    exact Rf_Rf n t (Finset.mem_powerset.mp ht)
  · intro t ht
    rw [Rf_card n t (Finset.mem_powerset.mp ht)]

theorem total_eq (n : ℕ) :
    ∑ t ∈ (Icc 1 (n - 1)).powerset, ((t.card + 1).factorial : ℚ) * ((n : ℚ) + ∑ x ∈ t, (x : ℚ)) =
      ∑ t ∈ (Icc 1 (n - 1)).powerset,
        ((t.card + 1).factorial : ℚ) * ((n : ℚ) + (n : ℚ) * (t.card : ℚ) / 2) := by
  have hsym : ∑ t ∈ (Icc 1 (n - 1)).powerset,
        ((t.card + 1).factorial : ℚ) * ∑ y ∈ Rf n t, (y : ℚ) =
      ∑ t ∈ (Icc 1 (n - 1)).powerset, ((t.card + 1).factorial : ℚ) * ∑ x ∈ t, (x : ℚ) :=
    sym_sum n (fun j => ((j + 1).factorial : ℚ))
  have hpair : ∑ t ∈ (Icc 1 (n - 1)).powerset,
        ((t.card + 1).factorial : ℚ) * ∑ x ∈ t, (x : ℚ) +
      ∑ t ∈ (Icc 1 (n - 1)).powerset, ((t.card + 1).factorial : ℚ) * ∑ y ∈ Rf n t, (y : ℚ) =
      ∑ t ∈ (Icc 1 (n - 1)).powerset,
        ((t.card + 1).factorial : ℚ) * ((n : ℚ) * (t.card : ℚ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← mul_add, pair_sum n t (Finset.mem_powerset.mp ht)]
  have e1 : ∑ t ∈ (Icc 1 (n - 1)).powerset,
        ((t.card + 1).factorial : ℚ) * ((n : ℚ) + ∑ x ∈ t, (x : ℚ)) =
      ∑ t ∈ (Icc 1 (n - 1)).powerset, ((t.card + 1).factorial : ℚ) * (n : ℚ) +
      ∑ t ∈ (Icc 1 (n - 1)).powerset, ((t.card + 1).factorial : ℚ) * ∑ x ∈ t, (x : ℚ) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun t _ => mul_add _ _ _)
  have e2 : ∑ t ∈ (Icc 1 (n - 1)).powerset,
        ((t.card + 1).factorial : ℚ) * ((n : ℚ) + (n : ℚ) * (t.card : ℚ) / 2) =
      ∑ t ∈ (Icc 1 (n - 1)).powerset, ((t.card + 1).factorial : ℚ) * (n : ℚ) +
      (∑ t ∈ (Icc 1 (n - 1)).powerset,
        ((t.card + 1).factorial : ℚ) * ((n : ℚ) * (t.card : ℚ))) / 2 := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  rw [e1, e2]
  linarith

theorem Icc_bridge (f : ℕ → ℚ) (m : ℕ) :
    ∑ k ∈ Icc 2 (m + 1 + 1), f k = ∑ j ∈ range (m + 1), f (j + 2) := by
  apply Finset.sum_nbij' (fun k => k - 2) (fun j => j + 2)
  · intro k hk
    rw [Finset.mem_Icc] at hk
    show k - 2 ∈ range (m + 1)
    rw [Finset.mem_range]
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    show j + 2 ∈ Icc 2 (m + 1 + 1)
    rw [Finset.mem_Icc]
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    show k - 2 + 2 = k
    omega
  · intro j _
    show j + 2 - 2 = j
    omega
  · intro k hk
    rw [Finset.mem_Icc] at hk
    show f k = f (k - 2 + 2)
    rw [Nat.sub_add_cancel hk.1]

theorem term_eq (m j : ℕ) (hj : j < m + 1) :
    (m.choose j : ℚ) * (((j + 1).factorial : ℚ) *
        (((m + 1 : ℕ) : ℚ) + ((m + 1 : ℕ) : ℚ) * (j : ℚ) / 2)) =
      ((m + 1).factorial : ℚ) * (((j + 2).choose 2 : ℚ) / ((m + 1 + 1 - (j + 2)).factorial : ℚ)) := by
  have hjm : j ≤ m := by omega
  have hc : (m.choose j : ℚ) * (j.factorial : ℚ) * ((m - j).factorial : ℚ) = (m.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjm
  have hf1 : ((j + 1).factorial : ℚ) = ((j : ℚ) + 1) * (j.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ j
  have hf2 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_succ m
  have h2 : (j + 2).choose 2 * 2 = (j + 2) * (j + 1) := by
    have h := Nat.add_one_mul_choose_eq (j + 1) 1
    rw [Nat.choose_one_right] at h
    exact h.symm
  have hch : ((j + 2).choose 2 : ℚ) * 2 = ((j : ℚ) + 2) * ((j : ℚ) + 1) := by
    exact_mod_cast h2
  have hd : ((m - j).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [show m + 1 + 1 - (j + 2) = m - j by omega, hf1, hf2, Nat.cast_succ, mul_div_assoc',
    eq_div_iff hd]
  linear_combination (((j : ℚ) + 1) * ((m : ℚ) + 1) * (1 + (j : ℚ) / 2)) * hc -
    (((m : ℚ) + 1) * (m.factorial : ℚ) / 2) * hch

theorem value_eq (n : ℕ) (hn : 1 ≤ n) :
    ∑ l ∈ (Icc 1 (n - 1)).powerset.biUnion (fun t => (insert n t).toList.permutations.toFinset), (l.sum : ℚ) = A281912 n := by
  rw [sum_Fs n hn, total_eq n]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hU : (Icc 1 (m + 1 - 1)).card = m := by
    rw [Nat.card_Icc]
    omega
  have hpc : ∑ t ∈ (Icc 1 (m + 1 - 1)).powerset, ((t.card + 1).factorial : ℚ) *
        (((m + 1 : ℕ) : ℚ) + ((m + 1 : ℕ) : ℚ) * (t.card : ℚ) / 2) =
      ∑ j ∈ range ((Icc 1 (m + 1 - 1)).card + 1), ((Icc 1 (m + 1 - 1)).card).choose j •
        (((j + 1).factorial : ℚ) * (((m + 1 : ℕ) : ℚ) + ((m + 1 : ℕ) : ℚ) * (j : ℚ) / 2)) :=
    Finset.sum_powerset_apply_card
      (fun j => ((j + 1).factorial : ℚ) * (((m + 1 : ℕ) : ℚ) + ((m + 1 : ℕ) : ℚ) * (j : ℚ) / 2))
  rw [hpc, hU]
  unfold A281912
  rw [Icc_bridge, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [nsmul_eq_mul]
  exact term_eq m j (Finset.mem_range.mp hj)

theorem main_proof : ∀ n : ℕ, 1 ≤ n →
    (∃ F : Finset (List ℕ), ∀ l : List ℕ, l ∈ F ↔ IsSeq n l) ∧
    ∀ F : Finset (List ℕ), (∀ l : List ℕ, l ∈ F ↔ IsSeq n l) →
      ∑ l ∈ F, (l.sum : ℚ) = A281912 n := by
  intro n hn
  refine ⟨⟨(Icc 1 (n - 1)).powerset.biUnion (fun t => (insert n t).toList.permutations.toFinset), mem_Fs n hn⟩, ?_⟩
  intro G hG
  have hGF : G = (Icc 1 (n - 1)).powerset.biUnion (fun t => (insert n t).toList.permutations.toFinset) := by
    ext l
    rw [hG l, mem_Fs n hn]
  rw [hGF]
  exact value_eq n hn

end S07A338169

theorem OMA.solution : type_of% @OMA.S_oeis_a338169.main := S07A338169.main_proof