import OMAReductions.R_Erdos1_erdos_1_variants_least_N_9_R2
import Mathlib

/-! In the finite distinct-subset-sums search, a second-largest element below
96 is incompatible with the second-moment bound. The span constraints used
here are the six- and seven-element cases of the equal-cardinality
subset-sum condition in Borwein and Mossinghoff, *Newman polynomials with
prescribed vanishing and integer sets with distinct subset sums*,
Math. Comp. 72 (2003), 787–800, Algorithm 4. -/

namespace OMA.R_Erdos1_erdos_1_variants_least_N_9_R2_H2_R1

open Finset

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
/-- The two small span certificates use a bitmask search after translation
to minimum 1. A common shift encodes the cardinality of each subset in its
sum. The kernel computes only the searches for these short intervals. -/
private theorem span_certificate (k B : ℕ)
    (hkB : (k = 6 ∧ B = 12) ∨ (k = 7 ∧ B = 21))
    (A : Finset ℕ) (lo : ℕ) (hlo : lo ∈ A) (hA : A ⊆ Icc lo (lo + B))
    (hc : A.card = k) :
    ¬ (∀ S ⊆ A, ∀ T ⊆ A, S.card = T.card → S.sum id = T.sum id → S = T) := by
  let mask (l : List ℕ) : ℕ := l.foldr (fun a bits => bits ||| (bits <<< a)) 1
  let hasSubsetSum (A : Finset ℕ) (n : ℕ) : Prop := ∃ S ⊆ A, S.sum id = n
  let distinctSums (A : Finset ℕ) : Prop :=
    ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T
  let pseudoDistinct (A : Finset ℕ) : Prop :=
    ∀ S ⊆ A, ∀ T ⊆ A, S.card = T.card → S.sum id = T.sum id → S = T
  let addWeight (offset : ℕ) : ℕ ↪ ℕ :=
    ⟨fun x => x + offset, fun _ _ h => Nat.add_right_cancel h⟩

  -- Branch on choosing the largest remaining index. An overlapping shifted
  -- mask discards the branch that chooses it.
  let search (weight : ℕ → ℕ) (k b bits : ℕ) : Bool :=
    Nat.rec (motive := fun _ => ℕ → ℕ → Bool)
      (fun k _ => k == 0)
      (fun b recur k bits =>
        match k with
        | 0 => true
        | k + 1 =>
          let shifted := bits <<< weight (b + 1)
          ((bits &&& shifted == 0) && recur k (bits ||| shifted)) || recur (k + 1) bits)
      b k bits
  have mask_nil : mask [] = 1 := rfl
  have mask_cons (a : ℕ) (l : List ℕ) :
      mask (a :: l) = mask l ||| (mask l <<< a) := rfl
  have search_zero_k (weight : ℕ → ℕ) (b bits : ℕ) :
      search weight 0 b bits = true := by cases b <;> rfl
  have search_succ (weight : ℕ → ℕ) (k b bits : ℕ) :
      search weight (k + 1) (b + 1) bits =
        let shifted := bits <<< weight (b + 1)
        ((bits &&& shifted == 0) && search weight k b (bits ||| shifted)) ||
          search weight (k + 1) b bits := rfl

  have distinct_mono {A B : Finset ℕ} (hAB : A ⊆ B) (hB : distinctSums B) :
      distinctSums A := by
    intro S hS T hT h
    exact hB S (hS.trans hAB) T (hT.trans hAB) h

  have has_subset_sum_insert {a n : ℕ} {A : Finset ℕ} (ha : a ∉ A) :
      hasSubsetSum (insert a A) n ↔ hasSubsetSum A n ∨
        a ≤ n ∧ hasSubsetSum A (n - a) := by
    constructor
    · rintro ⟨S, hS, hsum⟩
      by_cases hm : a ∈ S
      · right
        have Tsub : S.erase a ⊆ A := by
          intro b hb
          rcases Finset.mem_erase.mp hb with ⟨hba, hbin⟩
          exact (Finset.mem_insert.mp (hS hbin)).resolve_left hba
        have hdecomp : (S.erase a).sum id + a = n := by
          simpa only [Finset.sum_erase_add _ _ hm, id_eq] using hsum
        exact ⟨by omega, S.erase a, Tsub, by omega⟩
      · left
        refine ⟨S, ?_, hsum⟩
        intro b hb
        exact (Finset.mem_insert.mp (hS hb)).resolve_left (by rintro rfl; exact hm hb)
    · rintro (⟨S, hS, hsum⟩ | ⟨hn, S, hS, hsum⟩)
      · exact ⟨S, hS.trans (subset_insert _ _), hsum⟩
      · have hna : a ∉ S := fun h ↦ ha (hS h)
        refine ⟨insert a S, Finset.insert_subset_insert _ hS, ?_⟩
        rw [Finset.sum_insert hna, id_eq, hsum]
        omega

  have mask_testBit_iff (l : List ℕ) (hl : l.Nodup) (n : ℕ) :
      (mask l).testBit n = true ↔ hasSubsetSum l.toFinset n := by
    induction l generalizing n with
    | nil =>
        simp only [mask_nil, List.toFinset_nil, hasSubsetSum, Finset.subset_empty,
          exists_eq_left, Finset.sum_empty]
        cases n <;> simp [Nat.testBit_succ]
    | cons a l ih =>
        obtain ⟨ha, hnd⟩ := List.nodup_cons.mp hl
        have hnot : a ∉ l.toFinset := by simpa using ha
        simp only [mask_cons, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, ih hnd, List.toFinset_cons]
        exact (has_subset_sum_insert hnot).symm

  have shift_and_zero_of_distinct {a : ℕ} {l : List ℕ} (hl : l.Nodup) (ha : a ∉ l.toFinset)
      (h : distinctSums (insert a l.toFinset)) :
      mask l &&& (mask l <<< a) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro n
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]
    by_cases hb : ((mask l).testBit n && (decide (a ≤ n) && (mask l).testBit (n - a))) = true
    · have hb' : (mask l).testBit n = true ∧ a ≤ n ∧ (mask l).testBit (n - a) = true := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using hb
      obtain ⟨h0, han, h2⟩ := hb'
      obtain ⟨S, hS, hsumS⟩ := (mask_testBit_iff l hl n).mp h0
      obtain ⟨T, hT, hsumT⟩ := (mask_testBit_iff l hl (n - a)).mp h2
      have hna : a ∉ T := fun h' ↦ ha (hT h')
      have hsum : (insert a T).sum id = n := by
        rw [Finset.sum_insert hna, id_eq, hsumT]
        omega
      have he := h S (hS.trans (subset_insert _ _)) (insert a T)
        (Finset.insert_subset_insert _ hT) (hsumS.trans hsum.symm)
      exact False.elim (ha (hS (he ▸ Finset.mem_insert_self a T)))
    · exact Bool.eq_false_iff.mpr hb

  have search_complete (weight : ℕ ↪ ℕ) {R : Finset ℕ} {l : List ℕ} {b : ℕ}
      (hR : ∀ x ∈ R, 0 < x ∧ x ≤ b) (hl : l.Nodup)
      (hD : Disjoint (R.map weight) l.toFinset)
      (h : distinctSums (R.map weight ∪ l.toFinset)) :
      search weight R.card b (mask l) = true := by
    induction b generalizing R l with
    | zero =>
      have hE : R = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun a ha => by
        obtain ⟨h₀, h₁⟩ := hR a ha
        omega
      simp [hE, search_zero_k]
    | succ b ih =>
      cases hcard : R.card with
      | zero => simp [search_zero_k]
      | succ k =>
        by_cases hb : b + 1 ∈ R
        · have hbL : weight (b + 1) ∉ l.toFinset := fun hx =>
            (Finset.disjoint_left.mp hD) (Finset.mem_map_of_mem _ hb) hx
          have hnd : (weight (b + 1) :: l).Nodup :=
            List.nodup_cons.mpr ⟨by simpa using hbL, hl⟩
          have htail : ∀ x ∈ R.erase (b + 1), 0 < x ∧ x ≤ b := by
            intro x hx
            obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
            obtain ⟨h₀, h₁⟩ := hR x hmem
            exact ⟨h₀, by omega⟩
          have hdis : Disjoint ((R.erase (b + 1)).map weight)
              (weight (b + 1) :: l).toFinset := by
            rw [List.toFinset_cons, Finset.map_erase, Finset.disjoint_right]
            intro x hx
            obtain rfl | hm := Finset.mem_insert.mp hx
            · exact Finset.notMem_erase _ _
            · exact fun hr => (Finset.disjoint_left.mp hD) (Finset.mem_of_mem_erase hr) hm
          have hunion : (R.erase (b + 1)).map weight ∪ (weight (b + 1) :: l).toFinset =
              R.map weight ∪ l.toFinset := by
            rw [List.toFinset_cons, Finset.map_erase, Finset.union_insert,
              ← Finset.insert_union, Finset.insert_erase (Finset.mem_map_of_mem _ hb)]
          have hrec := ih htail hnd hdis (hunion.symm ▸ h)
          have herase : (R.erase (b + 1)).card = k := by
            rw [Finset.card_erase_of_mem hb, hcard]
            omega
          rw [herase, mask_cons] at hrec
          have hprefix : insert (weight (b + 1)) l.toFinset ⊆ R.map weight ∪ l.toFinset := by
            refine Finset.insert_subset_iff.mpr ⟨Finset.mem_union_left _
              (Finset.mem_map_of_mem _ hb), Finset.subset_union_right⟩
          have htest := shift_and_zero_of_distinct hl hbL (distinct_mono hprefix h)
          simp [search_succ, htest, hrec]
        · have htail : ∀ x ∈ R, 0 < x ∧ x ≤ b := by
            intro x hx
            obtain ⟨h₀, h₁⟩ := hR x hx
            have hne : x ≠ b + 1 := fun he => hb (he ▸ hx)
            exact ⟨h₀, by omega⟩
          have hrec := ih htail hl hD h
          rw [hcard] at hrec
          simp [search_succ, hrec]

  have sum_map_add (A : Finset ℕ) (offset : ℕ) :
      (A.map (addWeight offset)).sum id = A.sum id + A.card * offset := by
    rw [Finset.sum_map]
    change (∑ x ∈ A, (x + offset)) = A.sum id + A.card * offset
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, id_eq, Nat.cast_id]

  have sum_lt_of_card_lt {r s m n c : ℕ} (hr : r < c) (hmn : m < n) :
      r + m * c < s + n * c := by
    calc
      r + m * c < c + m * c := Nat.add_lt_add_right hr _
      _ = (m + 1) * c := by ring
      _ ≤ n * c := Nat.mul_le_mul_right _ hmn
      _ ≤ s + n * c := Nat.le_add_left _ _

  -- Adding a large common offset encodes cardinality together with each sum.
  have shifted_distinct {A : Finset ℕ} {offset : ℕ}
      (hsmall : ∀ S ⊆ A, S.sum id < offset) (hA : pseudoDistinct A) :
      distinctSums (A.map (addWeight offset)) := by
    intro S hS T hT he
    obtain ⟨S', hS', rfl⟩ := Finset.subset_map_iff.mp hS
    obtain ⟨T', hT', rfl⟩ := Finset.subset_map_iff.mp hT
    rw [sum_map_add, sum_map_add] at he
    have hc : S'.card = T'.card := by
      by_contra hn
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact (ne_of_lt (sum_lt_of_card_lt (hsmall S' hS') hlt)) he
      · exact (ne_of_lt (sum_lt_of_card_lt (hsmall T' hT') hgt)) he.symm
    rw [hc] at he
    have hsum : S'.sum id = T'.sum id := Nat.add_right_cancel he
    rw [hA S' hS' T' hT' hc hsum]

  have sum_lt_encoding_bound {A : Finset ℕ} {k B : ℕ}
      (hA : A ⊆ Icc 1 B) (hc : A.card = k) {S : Finset ℕ} (hS : S ⊆ A) :
      S.sum id < k * B + 1 := by
    refine Nat.lt_succ_of_le ?_
    calc
      S.sum id ≤ S.card * B :=
        Finset.sum_le_card_nsmul _ _ _ fun x hx => (Finset.mem_Icc.mp (hA (hS hx))).2
      _ ≤ k * B := Nat.mul_le_mul_right _ (hc ▸ Finset.card_le_card hS)

  -- For span bounds the smallest point is translated to 1 and forced into the prefix.
  have no_normalized_of_search_false (k B : ℕ)
      (hf : search (addWeight ((k + 1) * B + 1)) k B
        (mask [addWeight ((k + 1) * B + 1) 1]) = false)
      (A : Finset ℕ) (hA : A ⊆ Icc 1 B) (hc : A.card = k + 1) (h1 : 1 ∈ A) :
      ¬ pseudoDistinct A := by
    intro h
    let w := addWeight ((k + 1) * B + 1)
    let R := A.erase 1
    have hr : R.card = k := by
      rw [Finset.card_erase_of_mem h1, hc]
      omega
    have hb : ∀ x ∈ R, 0 < x ∧ x ≤ B := by
      intro x hx
      exact Finset.mem_Icc.mp (hA (Finset.mem_of_mem_erase hx))
    have hd : Disjoint (R.map w) [w 1].toFinset := by
      simp [R, Finset.map_erase]
    have he : R.map w ∪ [w 1].toFinset = A.map w := by
      rw [List.toFinset_cons, List.toFinset_nil, Finset.union_insert, Finset.union_empty]
      change insert (w 1) ((A.erase 1).map w) = A.map w
      rw [Finset.map_erase, Finset.insert_erase (Finset.mem_map_of_mem _ h1)]
    have h' := search_complete w hb (by simp : [w 1].Nodup) hd
      (he.symm ▸ shifted_distinct (fun S hS => sum_lt_encoding_bound hA hc hS) h)
    rw [hr] at h'
    exact Bool.false_ne_true (hf.symm.trans h')

  have pseudo_map_add_iff (A : Finset ℕ) (b : ℕ) :
      pseudoDistinct (A.map (addWeight b)) ↔ pseudoDistinct A := by
    constructor
    · intro h S hS T hT hc he
      apply Finset.map_injective (addWeight b)
      apply h _ (Finset.map_subset_map.mpr hS) _ (Finset.map_subset_map.mpr hT)
      · simpa using hc
      · rw [sum_map_add, sum_map_add, he, hc]
    · intro h S hS T hT hc he
      obtain ⟨S', hS', rfl⟩ := Finset.subset_map_iff.mp hS
      obtain ⟨T', hT', rfl⟩ := Finset.subset_map_iff.mp hT
      have hc' : S'.card = T'.card := by simpa using hc
      rw [sum_map_add, sum_map_add, hc'] at he
      have hsum : S'.sum id = T'.sum id := Nat.add_right_cancel he
      rw [h S' hS' T' hT' hc' hsum]

  -- Translate an arbitrary interval so that its first point becomes 1.
  have obstruction_on_interval {k B : ℕ}
      (h : ∀ A : Finset ℕ, A ⊆ Icc 1 (B + 1) → A.card = k → 1 ∈ A → ¬ pseudoDistinct A)
      (A : Finset ℕ) (lo : ℕ) (hlo : lo ∈ A) (hA : A ⊆ Icc lo (lo + B))
      (hc : A.card = k) : ¬ pseudoDistinct A := by
    let f : ℕ → ℕ := fun x => x - lo + 1
    let C := A.image f
    have hi : Set.InjOn f (↑A : Set ℕ) := by
      intro x hx y hy he
      have hxl := (Finset.mem_Icc.mp (hA hx)).1
      have hyl := (Finset.mem_Icc.mp (hA hy)).1
      dsimp [f] at he
      omega
    have hC : C ⊆ Icc 1 (B + 1) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hxl, hxu⟩ := Finset.mem_Icc.mp (hA hx)
      apply Finset.mem_Icc.mpr
      dsimp [f]
      omega
    have hC1 : 1 ∈ C := Finset.mem_image.mpr ⟨lo, hlo, by simp [f]⟩
    have heq : C.map (addWeight lo) = A.map (addWeight 1) := by
      rw [Finset.map_eq_image, Finset.map_eq_image, Finset.image_image]
      refine Finset.image_congr fun x hx => ?_
      obtain ⟨hxl, _⟩ := Finset.mem_Icc.mp (hA hx)
      change x - lo + 1 + lo = x + 1
      omega
    have hCcard : C.card = k := (Finset.card_image_of_injOn hi).trans hc
    intro hP
    apply h C hC hCcard hC1
    rw [← pseudo_map_add_iff C lo, heq, pseudo_map_add_iff]
    exact hP

  rcases hkB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact obstruction_on_interval (no_normalized_of_search_false 5 13 (by decide +kernel))
      A lo hlo hA hc
  · exact obstruction_on_interval (no_normalized_of_search_false 6 22 (by decide +kernel))
      A lo hlo hA hc

/-- A span obstruction for short equal-cardinality-sum sets bounds each tail
of the increasing enumeration of a sum-distinct set. -/
private theorem tail_gap {k : ℕ} {A : Finset ℕ} {N : ℕ}
    (hA : ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T) (f : Fin k → ℕ) (hf : StrictMono f)
    (hfA : ∀ j, f j ∈ A) (hfu : ∀ j, f j ≤ N) (i : Fin k) (width : ℕ)
    (hspan : (k - i.val = 6 ∧ width = 12) ∨ (k - i.val = 7 ∧ width = 21)) :
    f i + width + 1 ≤ N := by
  by_contra! h
  let B := (Ici i).image f
  have hfi : f i ∈ B := Finset.mem_image.mpr ⟨i, Finset.mem_Ici.mpr le_rfl, rfl⟩
  have hB : B ⊆ Icc (f i) (f i + width) := by
    intro j hj
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hj
    have hbound := hfu t
    exact Finset.mem_Icc.mpr ⟨hf.monotone (Finset.mem_Ici.mp ht), by omega⟩
  have hc : B.card = k - i.val := by
    change ((Ici i).image f).card = _
    rw [Finset.card_image_of_injOn hf.injective.injOn, Fin.card_Ici]
  apply span_certificate _ _ hspan B (f i) hfi hB hc
  intro S hS T hT hc he
  have hBA : B ⊆ A := by
    intro j hj
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hj
    exact hfA t
  exact hA S (hS.trans hBA) T (hT.trans hBA) he

/-- Within the exact 160-bound search, the second-largest number is at least
96. This eliminates an entire initial choice interval before any masks. -/
private theorem second_largest_ge_96 {A : Finset ℕ}
    (hA : ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T) (hbound : ∀ x ∈ A, x ≤ 160) (hc : A.card = 9)
    (hmoment : 87381 ≤ ∑ x ∈ A, x ^ 2) :
    96 ≤ (A.orderIsoOfFin hc (7 : Fin 9)).val := by
  let e := A.orderIsoOfFin hc
  let f : Fin 9 → ℕ := fun i => (e i).val
  have hf : StrictMono f := fun _ _ h => e.strictMono h
  have hmem : ∀ i, f i ∈ A := fun i => (e i).property
  change 96 ≤ f 7
  by_contra! h
  let g : Fin 8 → ℕ := fun i => f i.castSucc
  have hg : StrictMono g := fun i j hij =>
    hf (show i.castSucc < j.castSucc from hij)
  have hgA : ∀ i, g i ∈ A := fun i => hmem i.castSucc
  have hgU : ∀ i, g i ≤ 95 := by
    intro i
    have hib : i.castSucc ≤ (7 : Fin 9) := Nat.le_of_lt_succ i.isLt
    exact (hf.monotone hib).trans (by omega)
  have h22 : g 1 + 21 + 1 ≤ 95 :=
    tail_gap hA g hg hgA hgU 1 21 (Or.inr ⟨by decide, rfl⟩)
  have h13 : g 2 + 12 + 1 ≤ 95 :=
    tail_gap hA g hg hgA hgU 2 12 (Or.inl ⟨by decide, rfl⟩)
  change f 1 + 21 + 1 ≤ 95 at h22
  change f 2 + 12 + 1 ≤ 95 at h13
  have h01 := hf (by decide : (0 : Fin 9) < 1)
  have h34 := hf (by decide : (3 : Fin 9) < 4)
  have h45 := hf (by decide : (4 : Fin 9) < 5)
  have h56 := hf (by decide : (5 : Fin 9) < 6)
  have h67 := hf (by decide : (6 : Fin 9) < 7)
  have h8 : f 8 ≤ 160 := hbound _ (hmem 8)
  let cap : Fin 9 → ℕ := ![72, 73, 82, 91, 92, 93, 94, 95, 160]
  have hcap (i : Fin 9) : f i ≤ cap i := by
    fin_cases i <;> simp [cap] <;> omega
  have hsmall : (∑ i : Fin 9, cap i ^ 2) < 87381 := by decide +kernel
  have htotal : (∑ x ∈ A, x ^ 2) < 87381 := calc
    (∑ x ∈ A, x ^ 2) = ∑ x : A, x.val ^ 2 :=
      (sum_coe_sort A (fun x : ℕ => x ^ 2)).symm
    _ = ∑ i : Fin 9, f i ^ 2 := (Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)).symm
    _ ≤ ∑ i : Fin 9, cap i ^ 2 :=
      Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left (hcap i) 2
    _ < _ := hsmall
  exact (not_lt_of_ge hmoment) htotal

/-- Candidates of maximum 152 through 156 with at least two elements at least 96. -/
def H1 : Prop :=
  ∀ A : Finset ℕ, A ⊆ Icc 1 156 → (∃ x ∈ A, 152 ≤ x) → A.card = 9 →
    87381 ≤ (∑ x ∈ A, x ^ 2) → 511 ≤ A.sum id → 2 ≤ (A.filter (96 ≤ ·)).card →
    ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id

/-- Candidates of maximum 157 through 160 with at least two elements at least 96. -/
def H2 : Prop :=
  ∀ A : Finset ℕ, A ⊆ Icc 1 160 → (∃ x ∈ A, 157 ≤ x) → A.card = 9 →
    87381 ≤ (∑ x ∈ A, x ^ 2) → 511 ≤ A.sum id → 2 ≤ (A.filter (96 ≤ ·)).card →
    ∃ S ⊆ A, ∃ T ⊆ A, S ≠ T ∧ S.sum id = T.sum id

theorem main : H1 → H2 → OMA.R_Erdos1_erdos_1_variants_least_N_9_R2.H2 := by
  classical
  intro lower upper A hA hmax hcard hmoment hsum
  by_contra hcollision
  have hdistinct : ∀ S ⊆ A, ∀ T ⊆ A, S.sum id = T.sum id → S = T := by
    intro S hS T hT he
    by_contra hne
    exact hcollision ⟨S, hS, T, hT, hne, he⟩
  let e := A.orderIsoOfFin hcard
  have h7 : 96 ≤ (e (7 : Fin 9)).val :=
    second_largest_ge_96 hdistinct (fun _ hx => (mem_Icc.mp (hA hx)).2) hcard hmoment
  have h78 : (e (7 : Fin 9)).val < (e (8 : Fin 9)).val :=
    e.strictMono (by decide : (7 : Fin 9) < 8)
  have h8 : 96 ≤ (e (8 : Fin 9)).val := h7.trans h78.le
  have htwo : 2 ≤ (A.filter (96 ≤ ·)).card :=
    one_lt_card.mpr ⟨_, mem_filter.mpr ⟨(e (7 : Fin 9)).property, h7⟩,
      _, mem_filter.mpr ⟨(e (8 : Fin 9)).property, h8⟩, h78.ne⟩
  by_cases hupper : ∃ x ∈ A, 157 ≤ x
  · exact hcollision (upper A hA hupper hcard hmoment hsum htwo)
  · have hlower : A ⊆ Icc 1 156 := by
      intro x hx
      have hx₁ := (mem_Icc.mp (hA hx)).1
      have hx₂ : x ≤ 156 := by
        by_contra! hgt
        exact hupper ⟨x, hx, by omega⟩
      exact mem_Icc.mpr ⟨hx₁, hx₂⟩
    exact hcollision (lower A hlower hmax hcard hmoment hsum htwo)

end OMA.R_Erdos1_erdos_1_variants_least_N_9_R2_H2_R1
