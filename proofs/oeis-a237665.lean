import OMAStatements.S_oeis_a237665

-- Problem: A237665: Number of partitions of n such that the distinct terms arranged in increasing order form a string of two or more consecutive integ
-- Upstream: formal-conjectures statements/oeis-a237665.lean:0 (declaration OMA.S_oeis_a237665.main)
-- Credit: @thatoneguy006 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
Proof outline. Encode a partition whose distinct parts are `m, m+1, ..., m+l-1` by its
multiplicity vector (a string of length `l` at `m`). A distinct partition with `l` parts
corresponds, through tail sums, to a string at `m = 1` whose last entry is its smallest part.
For a fixed length `l`, the strings at `m` with `k` extra copies of `l` split into strings of
length `l` at `m`, strings of length `l+1` at `m`, and the same objects at `m+1`; telescoping
over `m` gives the identity for run lengths `{2t, 2t+1}` against `2t` distinct parts, and
summing over `t` gives the theorem.
-/

namespace A237665P

open Finset

/-- Multiplicity vectors of length `ℓ`, all entries `≥ 1`, on the values `m, m+1, …, m+ℓ-1`,
of total weight `n`. -/
def strSet (ℓ m n : ℕ) : Finset (Fin ℓ → ℕ) :=
  (Fintype.piFinset fun _ => Icc 1 n).filter (fun c => ∑ i : Fin ℓ, (m + (i : ℕ)) * c i = n)

/-- A string of length `L+1` at `m` together with `k` extra copies of the weight `L+1`. -/
def gSet (L m n : ℕ) : Finset ((Fin (L + 1) → ℕ) × ℕ) :=
  ((Fintype.piFinset fun _ => Icc 1 n) ×ˢ range (n + 1)).filter
    (fun ck => ∑ i : Fin (L + 1), (m + (i : ℕ)) * ck.1 i + (L + 1) * ck.2 = n)

lemma wsum_snoc {K : ℕ} (m : ℕ) (f : Fin K → ℕ) (x : ℕ) :
    ∑ i : Fin (K + 1), (m + (i : ℕ)) * (Fin.snoc f x : Fin (K + 1) → ℕ) i
      = ∑ i : Fin K, (m + (i : ℕ)) * f i + (m + K) * x := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma wsum_cons {K : ℕ} (m : ℕ) (x : ℕ) (f : Fin K → ℕ) :
    ∑ i : Fin (K + 1), (m + (i : ℕ)) * (Fin.cons x f : Fin (K + 1) → ℕ) i
      = m * x + ∑ i : Fin K, (m + 1 + (i : ℕ)) * f i := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring_nf

lemma wsum_head {K : ℕ} (m : ℕ) (c : Fin (K + 1) → ℕ) :
    ∑ i : Fin (K + 1), (m + (i : ℕ)) * c i
      = m * c 0 + ∑ i : Fin K, (m + 1 + (i : ℕ)) * Fin.tail c i := by
  conv_lhs => rw [← Fin.cons_self_tail c]
  exact wsum_cons m (c 0) (Fin.tail c)

lemma wsum_last {K : ℕ} (m : ℕ) (c : Fin (K + 1) → ℕ) :
    ∑ i : Fin (K + 1), (m + (i : ℕ)) * c i
      = ∑ i : Fin K, (m + (i : ℕ)) * Fin.init c i + (m + K) * c (Fin.last K) := by
  conv_lhs => rw [← Fin.snoc_init_self c]
  exact wsum_snoc m (Fin.init c) (c (Fin.last K))

lemma entry_le {K : ℕ} {m n : ℕ} (hm : 1 ≤ m) (c : Fin K → ℕ) (X : ℕ)
    (h : ∑ i : Fin K, (m + (i : ℕ)) * c i + X = n) (j : Fin K) : c j ≤ n := by
  have h1 : (m + (j : ℕ)) * c j ≤ ∑ i : Fin K, (m + (i : ℕ)) * c i :=
    Finset.single_le_sum (f := fun i : Fin K => (m + (i : ℕ)) * c i)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 : c j ≤ (m + (j : ℕ)) * c j := Nat.le_mul_of_pos_left _ (by omega)
  omega

lemma mem_strSet {ℓ m n : ℕ} {c : Fin ℓ → ℕ} :
    c ∈ strSet ℓ m n ↔ (∀ i, 1 ≤ c i ∧ c i ≤ n) ∧ ∑ i : Fin ℓ, (m + (i : ℕ)) * c i = n := by
  simp [strSet, Fintype.mem_piFinset]

lemma mem_gSet {L m n : ℕ} {ck : (Fin (L + 1) → ℕ) × ℕ} :
    ck ∈ gSet L m n ↔ (∀ i, 1 ≤ ck.1 i ∧ ck.1 i ≤ n) ∧ ck.2 < n + 1 ∧
      ∑ i : Fin (L + 1), (m + (i : ℕ)) * ck.1 i + (L + 1) * ck.2 = n := by
  simp [gSet, Fintype.mem_piFinset, and_assoc]

lemma cardA (L m n : ℕ) :
    ((gSet L m n).filter (fun ck => ¬ ck.1 0 ≤ ck.2 ∧ ck.2 = 0)).card
      = (strSet (L + 1) m n).card := by
  refine Finset.card_nbij' (fun ck => ck.1) (fun c => (c, 0)) ?_ ?_ ?_ ?_
  · intro ck h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_gSet] at h
    simp only [mem_coe, mem_strSet]
    obtain ⟨⟨h1, _, h3⟩, _, h5⟩ := h
    rw [h5] at h3
    exact ⟨h1, by simpa using h3⟩
  · intro c h
    simp only [mem_coe, mem_strSet] at h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_gSet]
    obtain ⟨h1, h2⟩ := h
    refine ⟨⟨h1, by omega, by simpa using h2⟩, ?_⟩
    have := (h1 0).1
    simp only [and_true]
    omega
  · intro ck h
    simp only [coe_filter, Set.mem_ofPred_eq] at h
    exact Prod.ext rfl h.2.2.symm
  · intro c _
    rfl

lemma cardB (L m n : ℕ) (hm : 1 ≤ m) :
    ((gSet L m n).filter (fun ck => ¬ ck.1 0 ≤ ck.2 ∧ ¬ ck.2 = 0)).card
      = (strSet (L + 2) m n).card := by
  refine Finset.card_nbij'
    (fun ck => (Fin.snoc (Fin.cons (ck.1 0 - ck.2) (Fin.tail ck.1) : Fin (L + 1) → ℕ) ck.2 :
      Fin (L + 2) → ℕ))
    (fun e => ((Fin.cons (Fin.init e 0 + e (Fin.last (L + 1))) (Fin.tail (Fin.init e)) :
      Fin (L + 1) → ℕ), e (Fin.last (L + 1)))) ?_ ?_ ?_ ?_
  · rintro ⟨c, k⟩ h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_gSet] at h
    simp only [mem_coe, mem_strSet]
    obtain ⟨⟨h1, h2, h3⟩, h4, h5⟩ := h
    refine ⟨fun i => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; omega
      · simp only [Fin.snoc_castSucc]
        refine Fin.cases ?_ (fun i => ?_) i
        · simp only [Fin.cons_zero]; have := h1 0; omega
        · simp only [Fin.cons_succ, Fin.tail]; exact h1 _
    · rw [wsum_snoc, wsum_cons]
      rw [wsum_head] at h3
      obtain ⟨d, hd⟩ : ∃ d, c 0 = d + k := ⟨c 0 - k, by omega⟩
      rw [hd] at h3
      rw [hd, Nat.add_sub_cancel]
      ring_nf at h3 ⊢
      linarith
  · intro e h
    simp only [mem_coe, mem_strSet] at h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_gSet]
    obtain ⟨h1, h2⟩ := h
    rw [wsum_last] at h2
    have h2' := h2
    rw [wsum_head] at h2'
    have hl := h1 (Fin.last (L + 1))
    have h0 := h1 0
    have hi0 : Fin.init e 0 = e 0 := rfl
    have hb1 : Fin.init e 0 ≤ m * Fin.init e 0 := Nat.le_mul_of_pos_left _ hm
    have hb2 : e (Fin.last (L + 1)) ≤ (m + (L + 1 : ℕ)) * e (Fin.last (L + 1)) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hS := Nat.zero_le (∑ i : Fin L, (m + 1 + (i : ℕ)) * Fin.tail (Fin.init e) i)
    refine ⟨⟨fun i => ?_, by omega, ?_⟩, ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; omega
      · simp only [Fin.cons_succ, Fin.tail, Fin.init]; exact h1 _
    · rw [wsum_cons]
      ring_nf at h2' ⊢
      linarith
    · simp only [Fin.cons_zero]; omega
    · omega
  · rintro ⟨c, k⟩ h
    simp only [coe_filter, Set.mem_ofPred_eq] at h
    have hk : k ≤ c 0 := by omega
    simp only [Fin.init_snoc, Fin.snoc_last, Fin.cons_zero, Fin.tail_cons, Nat.sub_add_cancel hk,
      Fin.cons_self_tail]
  · intro e _
    simp only [Fin.cons_zero, Nat.add_sub_cancel, Fin.tail_cons, Fin.cons_self_tail,
      Fin.snoc_init_self]

lemma cardC (L m n : ℕ) :
    ((gSet L m n).filter (fun ck => ck.1 0 ≤ ck.2)).card = (gSet L (m + 1) n).card := by
  refine Finset.card_nbij'
    (fun ck => ((Fin.snoc (Fin.tail ck.1) (ck.1 0) : Fin (L + 1) → ℕ), ck.2 - ck.1 0))
    (fun dk => ((Fin.cons (dk.1 (Fin.last L)) (Fin.init dk.1) : Fin (L + 1) → ℕ),
      dk.2 + dk.1 (Fin.last L))) ?_ ?_ ?_ ?_
  · rintro ⟨c, k⟩ h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_gSet] at h
    simp only [mem_coe, mem_gSet]
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
    refine ⟨fun i => ?_, by omega, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; exact h1 0
      · simp only [Fin.snoc_castSucc, Fin.tail]; exact h1 _
    · rw [wsum_snoc]
      rw [wsum_head] at h3
      obtain ⟨d, hd⟩ : ∃ d, k = c 0 + d := ⟨k - c 0, by omega⟩
      rw [hd] at h3
      rw [hd, Nat.add_sub_cancel_left]
      ring_nf at h3 ⊢
      linarith
  · rintro ⟨d, k⟩ h
    simp only [mem_coe, mem_gSet] at h
    simp only [coe_filter, Set.mem_ofPred_eq, mem_gSet]
    obtain ⟨h1, h2, h3⟩ := h
    rw [wsum_last] at h3
    have hl := h1 (Fin.last L)
    have hb2 : d (Fin.last L) ≤ (m + 1 + (L : ℕ)) * d (Fin.last L) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hb3 : k ≤ (L + 1) * k := Nat.le_mul_of_pos_left _ (by omega)
    have hS := Nat.zero_le (∑ i : Fin L, (m + 1 + (i : ℕ)) * Fin.init d i)
    refine ⟨⟨fun i => ?_, by omega, ?_⟩, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp only [Fin.cons_zero]; exact hl
      · simp only [Fin.cons_succ, Fin.init]; exact h1 _
    · rw [wsum_cons]
      ring_nf at h3 ⊢
      linarith
    · simp only [Fin.cons_zero]; omega
  · rintro ⟨c, k⟩ h
    simp only [coe_filter, Set.mem_ofPred_eq] at h
    simp only [Fin.snoc_last, Fin.init_snoc, Fin.cons_self_tail, Nat.sub_add_cancel h.2]
  · rintro ⟨d, k⟩ _
    simp only [Fin.tail_cons, Fin.cons_zero, Fin.snoc_init_self, Nat.add_sub_cancel]

lemma step (L m n : ℕ) (hm : 1 ≤ m) :
    (gSet L m n).card
      = (strSet (L + 1) m n).card + (strSet (L + 2) m n).card + (gSet L (m + 1) n).card := by
  rw [← cardA L m n, ← cardB L m n hm, ← cardC L m n]
  rw [← card_filter_add_card_filter_not (s := gSet L m n) (fun ck => ck.1 0 ≤ ck.2)]
  rw [← card_filter_add_card_filter_not
    (s := (gSet L m n).filter (fun ck => ¬ ck.1 0 ≤ ck.2)) (fun ck => ck.2 = 0)]
  rw [filter_filter, filter_filter]
  ring

lemma gSet_empty (L m n : ℕ) (h : n < m) : gSet L m n = ∅ := by
  ext ck
  simp only [mem_gSet, Finset.notMem_empty, iff_false, not_and]
  intro h1 _ h3
  rw [wsum_head] at h3
  have := (h1 0).1
  have : m ≤ m * ck.1 0 := Nat.le_mul_of_pos_right _ this
  omega

lemma telescope (L n : ℕ) : ∀ N : ℕ, (gSet L 1 n).card
    = ∑ m ∈ range N, ((strSet (L + 1) (m + 1) n).card + (strSet (L + 2) (m + 1) n).card)
      + (gSet L (N + 1) n).card := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, step L (N + 1) n (by omega), sum_range_succ]
    ring

lemma core (L n : ℕ) : (gSet L 1 n).card
    = ∑ m ∈ range n, ((strSet (L + 1) (m + 1) n).card + (strSet (L + 2) (m + 1) n).card) := by
  rw [telescope L n n, gSet_empty L (n + 1) n (by omega), card_empty, add_zero]

lemma base (L n : ℕ) : (gSet L 1 n).card = ∑ c ∈ strSet (L + 1) 1 n, c (Fin.last L) := by
  have hs : ∑ c ∈ strSet (L + 1) 1 n, c (Fin.last L)
      = ((strSet (L + 1) 1 n).sigma (fun c => Icc 1 (c (Fin.last L)))).card := by
    rw [card_sigma]; simp
  rw [hs]
  refine Finset.card_nbij'
    (fun ck => (⟨(Fin.snoc (Fin.init ck.1) (ck.1 (Fin.last L) + ck.2) : Fin (L + 1) → ℕ),
      ck.1 (Fin.last L)⟩ : Σ _ : Fin (L + 1) → ℕ, ℕ))
    (fun cj => ((Fin.snoc (Fin.init cj.1) cj.2 : Fin (L + 1) → ℕ), cj.1 (Fin.last L) - cj.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨c, k⟩ h
    simp only [mem_coe, mem_gSet] at h
    simp only [mem_coe, mem_sigma, mem_strSet, mem_Icc, Fin.snoc_last]
    obtain ⟨h1, h2, h3⟩ := h
    rw [wsum_last] at h3
    have hl := h1 (Fin.last L)
    have hb1 : c (Fin.last L) ≤ (1 + L) * c (Fin.last L) := Nat.le_mul_of_pos_left _ (by omega)
    have hb2 : k ≤ (L + 1) * k := Nat.le_mul_of_pos_left _ (by omega)
    have hS := Nat.zero_le (∑ i : Fin L, (1 + (i : ℕ)) * Fin.init c i)
    refine ⟨⟨fun i => ?_, ?_⟩, hl.1, Nat.le_add_right _ _⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; omega
      · simp only [Fin.snoc_castSucc, Fin.init]; exact h1 _
    · rw [wsum_snoc]; ring_nf at h3 ⊢; linarith
  · rintro ⟨c, j⟩ h
    simp only [mem_coe, mem_sigma, mem_strSet, mem_Icc] at h
    simp only [mem_coe, mem_gSet]
    obtain ⟨⟨h1, h2⟩, hj1, hj2⟩ := h
    rw [wsum_last] at h2
    refine ⟨fun i => ?_, ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]; have := h1 (Fin.last L); omega
      · simp only [Fin.snoc_castSucc, Fin.init]; exact h1 _
    · have := (h1 (Fin.last L)).2; omega
    · rw [wsum_snoc]
      obtain ⟨d, hd⟩ : ∃ d, c (Fin.last L) = j + d := ⟨c (Fin.last L) - j, by omega⟩
      rw [hd] at h2; rw [hd, Nat.add_sub_cancel_left]
      ring_nf at h2 ⊢; linarith
  · rintro ⟨c, k⟩ _
    simp only [Fin.init_snoc, Fin.snoc_last, Nat.add_sub_cancel_left, Fin.snoc_init_self]
  · rintro ⟨c, j⟩ h
    simp only [mem_coe, mem_sigma, mem_Icc] at h
    simp only [Fin.init_snoc, Fin.snoc_last, Nat.add_sub_of_le h.2.2, Fin.snoc_init_self]

/-- The multiset with `c i` copies of `m + i`. -/
def toMS {K : ℕ} (m : ℕ) (c : Fin K → ℕ) : Multiset ℕ :=
  ∑ i : Fin K, Multiset.replicate (c i) (m + (i : ℕ))

lemma count_toMS {K : ℕ} (m : ℕ) (c : Fin K → ℕ) (j : Fin K) :
    (toMS m c).count (m + (j : ℕ)) = c j := by
  simp only [toMS, Multiset.count_sum', Multiset.count_replicate]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext (by omega))
  · intro h; exact absurd (Finset.mem_univ j) h

lemma mem_toMS {K : ℕ} (m : ℕ) (c : Fin K → ℕ) (x : ℕ) :
    x ∈ toMS m c ↔ ∃ i, c i ≠ 0 ∧ x = m + (i : ℕ) := by
  simp [toMS, Multiset.mem_sum, Multiset.mem_replicate]

lemma sum_toMS {K : ℕ} (m : ℕ) (c : Fin K → ℕ) :
    (toMS m c).sum = ∑ i : Fin K, (m + (i : ℕ)) * c i := by
  simp [toMS, Multiset.sum_sum, Multiset.sum_replicate, mul_comm]

lemma fiber_card (K m n : ℕ) (hm : 1 ≤ m) :
    ((univ : Finset (Nat.Partition n)).filter
      (fun p => p.parts.toFinset = Icc m (m + K))).card = (strSet (K + 1) m n).card := by
  symm
  refine Finset.card_bij
    (fun c hc => (⟨toMS m c, fun {i} hi => by
        obtain ⟨j, _, rfl⟩ := (mem_toMS m c i).1 hi; omega,
      by rw [sum_toMS]; exact (mem_strSet.1 hc).2⟩ : Nat.Partition n)) ?_ ?_ ?_
  · intro c hc
    simp only [mem_filter, mem_univ, true_and]
    ext x
    simp only [Multiset.mem_toFinset, mem_toMS, mem_Icc]
    constructor
    · rintro ⟨i, _, rfl⟩; have := i.isLt; omega
    · intro hx
      refine ⟨⟨x - m, by omega⟩, ?_, by simp; omega⟩
      have := ((mem_strSet.1 hc).1 ⟨x - m, by omega⟩).1
      omega
  · intro c1 _ c2 _ h
    have h' : toMS m c1 = toMS m c2 := congrArg Nat.Partition.parts h
    funext j
    rw [← count_toMS m c1 j, ← count_toMS m c2 j, h']
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    set c : Fin (K + 1) → ℕ := fun i => p.parts.count (m + (i : ℕ)) with hc
    have hparts : p.parts = toMS m c := by
      ext x
      by_cases hx : m ≤ x ∧ x ≤ m + K
      · have hx' : x = m + ((⟨x - m, by omega⟩ : Fin (K + 1)) : ℕ) := by simp; omega
        rw [hx', count_toMS]
      · rw [Multiset.count_eq_zero.2, Multiset.count_eq_zero.2]
        · rw [mem_toMS]; rintro ⟨i, _, rfl⟩; have := i.isLt; omega
        · intro hmem
          have : x ∈ p.parts.toFinset := Multiset.mem_toFinset.2 hmem
          rw [hp, mem_Icc] at this; exact hx this
    have hw : ∑ i : Fin (K + 1), (m + (i : ℕ)) * c i = n := by
      rw [← sum_toMS, ← hparts, p.parts_sum]
    refine ⟨c, ?_, Nat.Partition.ext hparts.symm⟩
    rw [mem_strSet]
    refine ⟨fun i => ⟨?_, entry_le hm c 0 (by simpa using hw) i⟩, hw⟩
    have : m + (i : ℕ) ∈ p.parts.toFinset := by rw [hp, mem_Icc]; have := i.isLt; omega
    exact Multiset.count_pos.2 (Multiset.mem_toFinset.1 this)

lemma lhs_eq (n : ℕ) : OMA.S_oeis_a237665.a n
    = ∑ r ∈ range n, ∑ m ∈ range n, (strSet (r + 2) (m + 1) n).card := by
  classical
  have hset : (univ : Finset (Nat.Partition n)).filter
        (fun p => OMA.S_oeis_a237665.ConsecutiveDistinctParts p)
      = (range n ×ˢ range n).biUnion (fun rm => (univ : Finset (Nat.Partition n)).filter
        (fun p => p.parts.toFinset = Icc (rm.2 + 1) (rm.2 + 1 + (rm.1 + 1)))) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_biUnion]
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_range, Prod.exists]
    unfold OMA.S_oeis_a237665.ConsecutiveDistinctParts
    constructor
    · rintro ⟨m0, r0, hr, hs⟩
      have hm0 : m0 ∈ p.parts := by
        rw [← Multiset.mem_toFinset, hs, mem_Icc]; omega
      have hmr : m0 + r0 ∈ p.parts := by
        rw [← Multiset.mem_toFinset, hs, mem_Icc]; omega
      have h1 := p.parts_pos hm0
      have h2 := Nat.Partition.le_of_mem_parts hmr
      refine ⟨r0 - 1, m0 - 1, ⟨by omega, by omega⟩, ?_⟩
      rw [hs]; congr 1 <;> omega
    · rintro ⟨r, m, _, hs⟩
      exact ⟨m + 1, r + 1, by omega, hs⟩
  have hdisj : ((range n ×ˢ range n : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun rm => (univ : Finset (Nat.Partition n)).filter
        (fun p => p.parts.toFinset = Icc (rm.2 + 1) (rm.2 + 1 + (rm.1 + 1)))) := by
    rintro ⟨r1, m1⟩ _ ⟨r2, m2⟩ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro p _ h1 h2
    apply hne
    have e := h1.symm.trans h2
    have ha := (Finset.ext_iff.1 e (m1 + 1)).1 (by simp)
    have hb := (Finset.ext_iff.1 e (m1 + 1 + (r1 + 1))).1 (by simp)
    have hc := (Finset.ext_iff.1 e (m2 + 1)).2 (by simp)
    have hd := (Finset.ext_iff.1 e (m2 + 1 + (r2 + 1))).2 (by simp)
    simp only [mem_Icc] at ha hb hc hd
    ext <;> simp <;> omega
  unfold OMA.S_oeis_a237665.a
  rw [show (univ.filter fun p : Nat.Partition n =>
        OMA.S_oeis_a237665.ConsecutiveDistinctParts p) = _ from hset]
  rw [card_biUnion hdisj, sum_product]
  refine sum_congr rfl fun r _ => sum_congr rfl fun m _ => ?_
  rw [fiber_card (r + 1) (m + 1) n (by omega)]

/-- Tail sums: `mu c i = c i + c (i+1) + ⋯ + c K`. -/
def mu {K : ℕ} (c : Fin (K + 1) → ℕ) (i : Fin (K + 1)) : ℕ := ∑ j ∈ Ici i, c j

lemma mu_last {K : ℕ} (c : Fin (K + 1) → ℕ) : mu c (Fin.last K) = c (Fin.last K) := by
  have : Ici (Fin.last K) = {Fin.last K} := by
    ext x; simp only [mem_Ici, mem_singleton, Fin.le_iff_val_le_val, Fin.ext_iff, Fin.val_last]
    have := x.isLt; omega
  simp [mu, this]

lemma mu_castSucc {K : ℕ} (c : Fin (K + 1) → ℕ) (i : Fin K) :
    mu c i.castSucc = c i.castSucc + mu c i.succ := by
  have : Ici i.castSucc = insert i.castSucc (Ici i.succ) := by
    ext x; simp only [mem_Ici, mem_insert, Fin.le_iff_val_le_val, Fin.ext_iff, Fin.val_succ,
      Fin.val_castSucc]
    omega
  rw [mu, this, sum_insert]
  · rfl
  · simp [Fin.le_iff_val_le_val]

lemma le_mu {K : ℕ} (c : Fin (K + 1) → ℕ) (i : Fin (K + 1)) : c i ≤ mu c i :=
  Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (by simp)

lemma mu_strictAnti {K : ℕ} (c : Fin (K + 1) → ℕ) (hc : ∀ i, 1 ≤ c i) : StrictAnti (mu c) := by
  intro i j hij
  refine Finset.sum_lt_sum_of_subset (i := i) ?_ (by simp) ?_ (by have := hc i; omega)
    (fun _ _ _ => Nat.zero_le _)
  · intro x hx; simp only [mem_Ici] at hx ⊢; exact le_trans hij.le hx
  · simp only [mem_Ici, not_le]; exact hij

lemma weight_mu {K : ℕ} (c : Fin (K + 1) → ℕ) :
    ∑ i, mu c i = ∑ i : Fin (K + 1), (1 + (i : ℕ)) * c i := by
  simp only [mu]
  rw [Finset.sum_comm' (t' := univ) (s' := fun j => Iic j)]
  · refine sum_congr rfl fun j _ => ?_
    rw [sum_const, Fin.card_Iic, smul_eq_mul, add_comm]
  · intro x y; simp

lemma mu_det {K : ℕ} (c d : Fin (K + 1) → ℕ) (h : mu c = mu d) : c = d := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [← mu_last c, ← mu_last d, h]
  · have h1 := mu_castSucc c j
    have h2 := mu_castSucc d j
    rw [h] at h1
    omega

lemma map_inj_of_strictAnti {K : ℕ} (f g : Fin (K + 1) → ℕ) (hf : StrictAnti f)
    (hg : StrictAnti g) (h : (univ : Finset (Fin (K + 1))).val.map f = univ.val.map g) :
    f = g := by
  classical
  set s := ((univ : Finset (Fin (K + 1))).val.map f).toFinset with hs
  have hcard : s.card = K + 1 := by
    rw [hs, Multiset.toFinset_card_of_nodup (Multiset.Nodup.map hf.injective univ.nodup)]
    simp
  have hfm : StrictMono (f ∘ Fin.rev) := fun a b hab => hf (Fin.rev_lt_rev.2 hab)
  have hgm : StrictMono (g ∘ Fin.rev) := fun a b hab => hg (Fin.rev_lt_rev.2 hab)
  have e1 := Finset.orderEmbOfFin_unique hcard (f := f ∘ Fin.rev)
    (fun x => by
      rw [hs]; exact Multiset.mem_toFinset.2 (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))) hfm
  have e2 := Finset.orderEmbOfFin_unique hcard (f := g ∘ Fin.rev)
    (fun x => by
      rw [hs, h]; exact Multiset.mem_toFinset.2 (Multiset.mem_map_of_mem _ (Finset.mem_univ_val _))) hgm
  funext i
  have := congrFun (e1.trans e2.symm) (Fin.rev i)
  simpa using this

/-- The distinct partition attached to a string at `m = 1`. -/
def phi {K n : ℕ} (c : Fin (K + 1) → ℕ) (hc : c ∈ strSet (K + 1) 1 n) : Nat.Partition n where
  parts := (univ : Finset (Fin (K + 1))).val.map (mu c)
  parts_pos := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.1 hx
    have := ((mem_strSet.1 hc).1 i).1
    have := le_mu c i
    omega
  parts_sum := by
    rw [Finset.sum_map_val, weight_mu]
    exact (mem_strSet.1 hc).2

lemma smallest_phi {K n : ℕ} (c : Fin (K + 1) → ℕ) (hc : c ∈ strSet (K + 1) 1 n) :
    OMA.S_oeis_a237665.smallestPart (phi c hc) = c (Fin.last K) := by
  have hanti := mu_strictAnti c (fun i => ((mem_strSet.1 hc).1 i).1)
  have hmem : mu c (Fin.last K) ∈ (phi c hc).parts.toFinset :=
    Multiset.mem_toFinset.2 (Multiset.mem_map_of_mem (mu c) (Finset.mem_univ_val (Fin.last K)))
  unfold OMA.S_oeis_a237665.smallestPart
  rw [dif_pos ⟨_, hmem⟩, ← mu_last c]
  refine le_antisymm (Finset.min'_le _ _ hmem) ?_
  refine Finset.le_min' _ _ _ fun y hy => ?_
  simp only [phi, Multiset.mem_toFinset, Multiset.mem_map, Finset.mem_val, mem_univ,
    true_and] at hy
  obtain ⟨i, rfl⟩ := hy
  exact hanti.antitone (Fin.le_last i)

lemma rhs_fiber (K n : ℕ) :
    ∑ c ∈ strSet (K + 1) 1 n, c (Fin.last K)
      = ∑ p ∈ (univ : Finset (Nat.Partition n)).filter
          (fun p => p.parts.Nodup ∧ Multiset.card p.parts = K + 1),
        OMA.S_oeis_a237665.smallestPart p := by
  classical
  refine Finset.sum_bij (fun c hc => phi c hc) ?_ ?_ ?_ ?_
  · intro c hc
    have hanti := mu_strictAnti c (fun i => ((mem_strSet.1 hc).1 i).1)
    simp only [mem_filter, mem_univ, true_and, phi]
    exact ⟨Multiset.Nodup.map hanti.injective univ.nodup, by simp⟩
  · intro c1 hc1 c2 hc2 h
    have h' := congrArg Nat.Partition.parts h
    simp only [phi] at h'
    exact mu_det c1 c2 (map_inj_of_strictAnti _ _
      (mu_strictAnti c1 (fun i => ((mem_strSet.1 hc1).1 i).1))
      (mu_strictAnti c2 (fun i => ((mem_strSet.1 hc2).1 i).1)) h')
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    obtain ⟨hnd, hcard⟩ := hp
    set s := p.parts.toFinset with hs
    have hsc : s.card = K + 1 := by rw [hs, Multiset.toFinset_card_of_nodup hnd, hcard]
    set e := s.orderEmbOfFin hsc with he
    set ν : Fin (K + 1) → ℕ := fun i => e (Fin.rev i) with hν
    have hνanti : StrictAnti ν := fun a b hab => e.strictMono (Fin.rev_lt_rev.2 hab)
    have hνmem : ∀ i, ν i ∈ p.parts := by
      intro i
      have : ν i ∈ s := Finset.orderEmbOfFin_mem s hsc _
      exact Multiset.mem_toFinset.1 this
    have hνparts : (univ : Finset (Fin (K + 1))).val.map ν = p.parts := by
      refine (Multiset.Nodup.ext (Multiset.Nodup.map hνanti.injective univ.nodup) hnd).2 ?_
      intro a
      simp only [Multiset.mem_map, Finset.mem_val, mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩; exact hνmem i
      · intro ha
        have : a ∈ Set.range e := by
          rw [Finset.range_orderEmbOfFin]; exact Multiset.mem_toFinset.2 ha
        obtain ⟨j, rfl⟩ := this
        exact ⟨Fin.rev j, by simp [hν]⟩
    set c : Fin (K + 1) → ℕ := fun i =>
      ν i - (if h : (i : ℕ) < K then ν ⟨(i : ℕ) + 1, by omega⟩ else 0) with hc
    have hmu : mu c = ν := by
      funext i
      induction i using Fin.reverseInduction with
      | last =>
        rw [mu_last]; simp [hc]
      | cast j ih =>
        rw [mu_castSucc, ih]
        have hlt : ν j.succ < ν j.castSucc := hνanti Fin.castSucc_lt_succ
        have : c j.castSucc = ν j.castSucc - ν j.succ := by
          simp only [hc, Fin.val_castSucc, j.isLt, dif_pos]
          rfl
        rw [this]; omega
    have hc1 : ∀ i, 1 ≤ c i := by
      intro i
      by_cases h : (i : ℕ) < K
      · have hlt : ν ⟨(i : ℕ) + 1, by omega⟩ < ν i := hνanti (Fin.lt_def.2 (by simp))
        simp only [hc, dif_pos h]; omega
      · have := p.parts_pos (hνmem i)
        simp only [hc, dif_neg h]; omega
    have hw : ∑ i : Fin (K + 1), (1 + (i : ℕ)) * c i = n := by
      rw [← weight_mu, hmu, ← Finset.sum_map_val, hνparts, p.parts_sum]
    have hcs : c ∈ strSet (K + 1) 1 n := by
      rw [mem_strSet]
      exact ⟨fun i => ⟨hc1 i, entry_le le_rfl c 0 (by simpa using hw) i⟩, hw⟩
    refine ⟨c, hcs, Nat.Partition.ext ?_⟩
    simp only [phi, hmu, hνparts]
  · intro c hc
    exact (smallest_phi c hc).symm

lemma strSet_empty (ℓ m n : ℕ) (hm : 1 ≤ m) (h : n < ℓ) : strSet ℓ m n = ∅ := by
  ext c
  simp only [mem_strSet, Finset.notMem_empty, iff_false, not_and]
  intro h1 h2
  have : ∑ _i : Fin ℓ, 1 ≤ ∑ i : Fin ℓ, (m + (i : ℕ)) * c i :=
    Finset.sum_le_sum fun i _ => by
      have := (h1 i).1
      exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  simp at this
  omega

lemma rhs_eq (n : ℕ) : OMA.S_oeis_a237665.sumSmallestEvenDistinct n
    = ∑ t ∈ range n, ∑ c ∈ strSet (2 * t + 1 + 1) 1 n, c (Fin.last (2 * t + 1)) := by
  classical
  have hset : (univ : Finset (Nat.Partition n)).filter
        (fun p => p.parts.Nodup ∧ p.parts ≠ 0 ∧ Even (Multiset.card p.parts))
      = (range n).biUnion (fun t => (univ : Finset (Nat.Partition n)).filter
        (fun p => p.parts.Nodup ∧ Multiset.card p.parts = 2 * t + 1 + 1)) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_biUnion]
    simp only [mem_univ, true_and, mem_range, mem_filter]
    have hle : Multiset.card p.parts ≤ n := by
      have := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) (fun x hx => p.parts_pos hx)
      rw [p.parts_sum, smul_eq_mul, mul_one] at this
      exact this
    constructor
    · rintro ⟨hnd, hne, r, hr⟩
      have : Multiset.card p.parts ≠ 0 := fun h0 => hne (Multiset.card_eq_zero.1 h0)
      exact ⟨r - 1, by omega, hnd, by omega⟩
    · rintro ⟨t, _, hnd, hc⟩
      refine ⟨hnd, fun h0 => ?_, ⟨t + 1, by omega⟩⟩
      rw [h0] at hc; simp at hc
  have hdisj : ((range n : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun t => (univ : Finset (Nat.Partition n)).filter
        (fun p => p.parts.Nodup ∧ Multiset.card p.parts = 2 * t + 1 + 1)) := by
    intro t1 _ t2 _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    rintro p _ ⟨_, h1⟩ ⟨_, h2⟩
    exact hne (by omega)
  unfold OMA.S_oeis_a237665.sumSmallestEvenDistinct
  rw [hset, sum_biUnion hdisj]
  exact sum_congr rfl fun t _ => (rhs_fiber (2 * t + 1) n).symm

lemma pair (F : ℕ → ℕ) : ∀ N : ℕ,
    ∑ t ∈ range N, (F (2 * t + 1 + 1) + F (2 * t + 1 + 2)) = ∑ r ∈ range (2 * N), F (r + 2) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ,
      sum_range_succ]
    have e : 2 * N + 1 + 1 = 2 * N + 2 := by omega
    rw [e]
    ring

theorem final (n : ℕ) :
    OMA.S_oeis_a237665.a n = OMA.S_oeis_a237665.sumSmallestEvenDistinct n := by
  rw [lhs_eq, rhs_eq]
  set F : ℕ → ℕ := fun ℓ => ∑ m ∈ range n, (strSet ℓ (m + 1) n).card with hF
  have hR : ∑ t ∈ range n, ∑ c ∈ strSet (2 * t + 1 + 1) 1 n, c (Fin.last (2 * t + 1))
      = ∑ t ∈ range n, (F (2 * t + 1 + 1) + F (2 * t + 1 + 2)) := by
    refine sum_congr rfl fun t _ => ?_
    rw [← base, core, sum_add_distrib]
  rw [hR, pair F n]
  refine Finset.sum_subset (fun r hr => by simp only [mem_range] at hr ⊢; omega) ?_
  intro r _ hr
  simp only [mem_range, not_lt] at hr
  show ∑ m ∈ range n, (strSet (r + 2) (m + 1) n).card = 0
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [strSet_empty (r + 2) (m + 1) n (by omega) (by omega), card_empty]

end A237665P

theorem OMA.solution : type_of% @OMA.S_oeis_a237665.main := by
  intro n
  exact A237665P.final n
