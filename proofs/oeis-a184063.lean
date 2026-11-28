import OMAStatements.S_oeis_a184063

-- Problem: A184063: Number of (n+1) X 2 binary arrays with rows and columns in nondecreasing order and adjacent 2x2 subblock sums differing by at most 1.
-- Credit: @ceejcake
-- Proof via bijection with row-multiplicity tuples (c0, c1, c2, c3) summing to n+1.

namespace ProofA184063

open OMA.S_oeis_a184063
open scoped Classical

-- Encode a row (b0, b1) as a natural number in {0, 1, 2, 3}: 00↦0, 01↦1, 10↦2, 11↦3.
private def rowCode (b0 b1 : Bool) : ℕ := 2 * b0.toNat + b1.toNat

private lemma rowsNondecreasing_iff {n : ℕ} (A : Fin (n + 1) → Fin 2 → Bool) :
    rowsNondecreasing A ↔ ∀ r1 r2 : Fin (n + 1), r1 ≤ r2 →
      rowCode (A r1 0) (A r1 1) ≤ rowCode (A r2 0) (A r2 1) := by
  constructor
  · intro h
    have hstep : ∀ i : Fin n,
        rowCode (A i.castSucc 0) (A i.castSucc 1) ≤ rowCode (A i.succ 0) (A i.succ 1) := by
      intro i
      have hi := h i
      unfold rowCode
      cases h1 : A i.castSucc 0 <;> cases h2 : A i.castSucc 1 <;>
      cases h3 : A i.succ 0 <;> cases h4 : A i.succ 1 <;> simp_all
    intro r1 r2 hle
    have hup : ∀ d : ℕ, (hd : r1.val + d ≤ n) →
        rowCode (A r1 0) (A r1 1) ≤ rowCode (A ⟨r1.val + d, by omega⟩ 0) (A ⟨r1.val + d, by omega⟩ 1) := by
      intro d
      induction d with
      | zero => intro _; exact le_rfl
      | succ d ih =>
        intro hd
        have h1 := ih (by omega)
        have h2 := hstep ⟨r1.val + d, by omega⟩
        have hfin : (⟨r1.val + d, by omega⟩ : Fin n).succ = ⟨r1.val + (d + 1), by omega⟩ := by
          ext; simp; omega
        rw [hfin] at h2
        exact le_trans h1 h2
    have hres := hup (r2.val - r1.val) (by omega)
    have hfin : (⟨r1.val + (r2.val - r1.val), by omega⟩ : Fin (n + 1)) = r2 := by ext; simp; omega
    rw [hfin] at hres
    exact hres
  · intro h i
    have hi := h i.castSucc i.succ (by exact Nat.le_succ i.val)
    unfold rowCode at hi
    cases h1 : A i.castSucc 0 <;> cases h2 : A i.castSucc 1 <;>
    cases h3 : A i.succ 0 <;> cases h4 : A i.succ 1 <;> simp_all

-- Valid count tuples (c0, c1, c2, c3) with c0+c1+c2+c3 = n+1
private def validTuple (n : ℕ) (t : Fin (n + 2) × Fin (n + 2) × Fin (n + 2) × Fin (n + 2)) : Prop :=
  let (c0, c1, c2, c3) := t
  c0.val + c1.val + c2.val + c3.val = n + 1 ∧
  (1 ≤ c1.val ∨ c2.val = 0) ∧
  ¬ (1 ≤ c0.val ∧ 1 ≤ c3.val ∧ c1.val + c2.val ≤ 1)

-- Build an array from a tuple (c0, c1, c2, c3)
private def mkArray {n : ℕ} (c0 c1 c2 : ℕ) : Fin (n + 1) → Fin 2 → Bool :=
  fun r col =>
    if r.val < c0 then false
    else if r.val < c0 + c1 then (col == 1)
    else if r.val < c0 + c1 + c2 then (col == 0)
    else true

-- Bijection between valid arrays (for n ≥ 2) and valid tuples!
private lemma card_valid_eq_tuples (n : ℕ) (hn : 1 < n) :
    Fintype.card {A : Fin (n + 1) → Fin 2 → Bool // isValid n A} =
    (Finset.univ.filter (validTuple n)).card := by
  rw [Fintype.card_subtype]
  let cnt (A : Fin (n + 1) → Fin 2 → Bool) (k : ℕ) : ℕ :=
    (Finset.univ.filter (fun r : Fin (n + 1) => rowCode (A r 0) (A r 1) = k)).card
  have hcnt_le : ∀ A k, cnt A k ≤ n + 1 := fun A k =>
    le_trans (Finset.card_filter_le _ _) (by simp)
  have hcnt_sum : ∀ A, cnt A 0 + cnt A 1 + cnt A 2 + cnt A 3 = n + 1 := by
    intro A
    have hdisj : (Finset.range 4 : Set ℕ).PairwiseDisjoint
        (fun k => Finset.univ.filter (fun r : Fin (n + 1) => rowCode (A r 0) (A r 1) = k)) := by
      intro k1 _ k2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro r h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (h1.symm.trans h2)
    have hunion : Finset.univ = (Finset.range 4).biUnion
        (fun k => Finset.univ.filter (fun r : Fin (n + 1) => rowCode (A r 0) (A r 1) = k)) := by
      ext r
      simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
        true_and, true_iff]
      refine ⟨rowCode (A r 0) (A r 1), ?_, rfl⟩
      unfold rowCode
      cases A r 0 <;> cases A r 1 <;> decide
    have hcard := congr_arg Finset.card hunion
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_biUnion hdisj] at hcard
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hcard
    exact hcard.symm
  -- For a row-sorted array A, A = mkArray (cnt A 0) (cnt A 1) (cnt A 2)!
  have hA_eq : ∀ A, rowsNondecreasing A → A = mkArray (cnt A 0) (cnt A 1) (cnt A 2) := by
    intro A hrows
    have hmono := (rowsNondecreasing_iff A).mp hrows
    -- For any k ∈ {0,1,2,3}, the prefix of rows with rowCode < k has size ∑_{j<k} cnt A j
    have hlt_iff : ∀ (r : Fin (n + 1)) (k : ℕ),
        (rowCode (A r 0) (A r 1) < k) ↔
        r.val < (Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) < k)).card := by
      intro r k
      let S := Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) < k)
      -- S is downward closed, hence S = Finset.univ.filter (fun r' => r'.val < S.card)
      have hdown : ∀ r1 r2 : Fin (n + 1), r1 ≤ r2 → r2 ∈ S → r1 ∈ S := by
        intro r1 r2 hle h2
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h2 ⊢
        exact lt_of_le_of_lt (hmono r1 r2 hle) h2
      have hS_eq : S = Finset.univ.filter (fun r' : Fin (n + 1) => r'.val < S.card) := by
        -- Prove by strong contradiction: if S ≠ prefix of size S.card, there is r1 ∉ S with r1 < r2 ∈ S
        by_contra hne
        have hnot_sub : ¬ (S ⊆ Finset.univ.filter (fun r' : Fin (n + 1) => r'.val < S.card)) := by
          intro hsub
          have hcard_eq : S.card = (Finset.univ.filter (fun r' : Fin (n + 1) => r'.val < S.card)).card := by
            have hle : S.card ≤ n + 1 := le_trans (Finset.card_filter_le _ _) (by simp)
            have : (Finset.univ.filter (fun r' : Fin (n + 1) => r'.val < S.card)).card = S.card := by
              have hcr : (Finset.range S.card).card = S.card := Finset.card_range S.card
              rw [← hcr]
              refine Finset.card_bij (fun r' _ => r'.val) ?_ ?_ ?_
              · intro r' hr'; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
                rw [Finset.mem_range]; omega
              · intro r1 _ r2 _ h; exact Fin.ext h
              · intro x hx; rw [Finset.mem_range] at hx
                exact ⟨⟨x, by omega⟩, by simp [hx], rfl⟩
            exact this.symm
          exact hne (Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq.symm))
        rw [Finset.not_subset] at hnot_sub
        rcases hnot_sub with ⟨r2, hr2S, hr2not⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hr2not
        -- Then every r' ≤ r2 is in S, giving at least r2.val + 1 > S.card elements in S!
        have hsub : Finset.univ.filter (fun r' : Fin (n + 1) => r'.val ≤ r2.val) ⊆ S := by
          intro r1 hr1
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr1
          exact hdown r1 r2 hr1 hr2S
        have hcard_ge : r2.val + 1 ≤ S.card := by
          have hle := Finset.card_le_card hsub
          have hc : (Finset.univ.filter (fun r' : Fin (n + 1) => r'.val ≤ r2.val)).card = r2.val + 1 := by
            rw [← Finset.card_range (r2.val + 1)]
            refine Finset.card_bij (fun r' _ => r'.val) ?_ ?_ ?_
            · intro r' hr'; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
              exact Finset.mem_range.mpr (by omega)
            · intro a _ b _ h; exact Fin.ext h
            · intro x hx; rw [Finset.mem_range] at hx
              exact ⟨⟨x, by have := r2.isLt; omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact Nat.le_of_lt_succ hx, rfl⟩
          omega
        omega
      have hmem : r ∈ S ↔ r.val < S.card := by
        conv_lhs => rw [hS_eq]
        simp
      simpa [S] using hmem
    have hlt1 : (Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) < 1)).card = cnt A 0 := by
      congr 1; ext r'; simp
    have hlt2 : (Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) < 2)).card = cnt A 0 + cnt A 1 := by
      have hunion : Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) < 2) =
          Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) = 0) ∪
          Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) = 1) := by
        ext r'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
      rw [hunion, Finset.card_union_of_disjoint]
      rw [Finset.disjoint_left]; intro r' h0 h1; simp only [Finset.mem_filter] at h0 h1; omega
    have hlt3 : (Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) < 3)).card = cnt A 0 + cnt A 1 + cnt A 2 := by
      have hunion : Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) < 3) =
          Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) < 2) ∪
          Finset.univ.filter (fun r' : Fin (n + 1) => rowCode (A r' 0) (A r' 1) = 2) := by
        ext r'; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]; omega
      rw [hunion, Finset.card_union_of_disjoint, hlt2]
      rw [Finset.disjoint_left]; intro r' h0 h1; simp only [Finset.mem_filter] at h0 h1; omega
    ext r col
    have h1 := hlt_iff r 1; rw [hlt1] at h1
    have h2 := hlt_iff r 2; rw [hlt2] at h2
    have h3 := hlt_iff r 3; rw [hlt3] at h3
    unfold mkArray
    unfold rowCode at h1 h2 h3
    cases hb0 : A r 0 <;> cases hb1 : A r 1 <;>
    · simp only [hb0, hb1, Bool.toNat_false, Bool.toNat_true, mul_zero, mul_one, add_zero, zero_add,
        show (2 : ℕ) + 1 = 3 by rfl,
        Nat.zero_lt_one, true_iff, false_iff, not_lt, Nat.lt_irrefl,
        show (1 : ℕ) < 2 by decide, show (1 : ℕ) < 3 by decide,
        show (2 : ℕ) < 3 by decide, show ¬ ((2 : ℕ) < 1) by decide,
        show ¬ ((2 : ℕ) < 2) by decide, show ¬ ((3 : ℕ) < 1) by decide,
        show ¬ ((3 : ℕ) < 2) by decide, show ¬ ((3 : ℕ) < 3) by decide] at h1 h2 h3
      fin_cases col
      · change A r 0 = _; rw [hb0]; split_ifs <;> first | decide | omega
      · change A r 1 = _; rw [hb1]; split_ifs <;> first | decide | omega
  -- Now establish the bijection!
  refine Finset.card_bij
    (fun A _ => (⟨cnt A 0, by have := hcnt_le A 0; omega⟩,
                 ⟨cnt A 1, by have := hcnt_le A 1; omega⟩,
                 ⟨cnt A 2, by have := hcnt_le A 2; omega⟩,
                 ⟨cnt A 3, by have := hcnt_le A 3; omega⟩)) ?_ ?_ ?_
  · intro A hA
    rw [Finset.mem_filter] at hA ⊢
    rcases hA.2 with ⟨hrows, hcols, hsmooth⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [validTuple]
    have hEq := hA_eq A hrows
    have hEq_r : ∀ r col, A r col = mkArray (cnt A 0) (cnt A 1) (cnt A 2) r col :=
      fun r col => congr_fun (congr_fun hEq r) col
    refine ⟨hcnt_sum A, ?_, ?_⟩
    · -- colsNondecreasing → c1 ≥ 1 ∨ c2 = 0
      by_contra h
      push Not at h
      rcases h with ⟨hc1, hc2⟩
      have hc10 : cnt A 1 = 0 := by omega
      have hrc2 : cnt A 0 < n + 1 := by have := hcnt_sum A; omega
      let r0 : Fin (n + 1) := ⟨cnt A 0, hrc2⟩
      have hA_r0_0 : A r0 0 = true := by rw [hEq_r]; unfold mkArray; simp only [r0, hc10]; split_ifs <;> first | rfl | omega
      have hA_r0_1 : A r0 1 = false := by rw [hEq_r]; unfold mkArray; simp only [r0, hc10]; split_ifs <;> first | rfl | omega
      rcases hcols with hall | ⟨r, hr_lt, hr0, hr1⟩
      · have := hall r0; rw [hA_r0_0, hA_r0_1] at this; cases this
      · by_cases hlt : r.val < cnt A 0
        · have h1 : A r 1 = false := by rw [hEq_r]; simp [mkArray, hlt]
          rw [h1] at hr1; cases hr1
        · by_cases heq : r.val = cnt A 0
          · have : r = r0 := Fin.ext heq
            rw [this, hA_r0_0] at hr0; cases hr0
          · have hlt' : r0 < r := by show r0.val < r.val; simp [r0]; omega
            have := hr_lt r0 hlt'; rw [hA_r0_0, hA_r0_1] at this; cases this
    · -- smoothSubblocks → ¬(c0 ≥ 1 ∧ c3 ≥ 1 ∧ c1 + c2 ≤ 1)
      rintro ⟨hc0, hc3, hmid⟩
      have hsum := hcnt_sum A
      by_cases hlt : cnt A 0 < n
      · have hi_lt : cnt A 0 - 1 < n := by omega
        have hsm := hsmooth ⟨cnt A 0 - 1, hi_lt⟩ ⟨cnt A 0, hlt⟩ (by simp; omega)
        have h1 : (A ⟨cnt A 0 - 1, by omega⟩ 0).toNat + (A ⟨cnt A 0 - 1, by omega⟩ 1).toNat = 0 := by
          rw [hEq_r, hEq_r]; unfold mkArray; dsimp only; split_ifs <;> first | rfl | omega
        have h2 : (A ⟨cnt A 0 + 1, by omega⟩ 0).toNat + (A ⟨cnt A 0 + 1, by omega⟩ 1).toNat = 2 := by
          rw [hEq_r, hEq_r]; unfold mkArray; dsimp only; split_ifs <;> first | rfl | omega
        unfold subblockSum at hsm
        have hidx1 : (⟨cnt A 0 - 1, hi_lt⟩ : Fin n).castSucc = ⟨cnt A 0 - 1, by omega⟩ := by ext; rfl
        have hidx2 : (⟨cnt A 0 - 1, hi_lt⟩ : Fin n).succ = (⟨cnt A 0, hlt⟩ : Fin n).castSucc := by ext; simp; omega
        have hidx3 : (⟨cnt A 0, hlt⟩ : Fin n).succ = ⟨cnt A 0 + 1, by omega⟩ := by ext; simp
        rw [hidx1, hidx2, hidx3] at hsm
        omega
      · have hc0n : cnt A 0 = n := by omega
        have hsm := hsmooth ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ (by simp; omega)
        have h1 : (A ⟨n - 2, by omega⟩ 0).toNat + (A ⟨n - 2, by omega⟩ 1).toNat = 0 := by
          rw [hEq_r, hEq_r]; unfold mkArray; dsimp only; split_ifs <;> first | rfl | omega
        have h2 : (A ⟨n, by omega⟩ 0).toNat + (A ⟨n, by omega⟩ 1).toNat = 2 := by
          rw [hEq_r, hEq_r]; unfold mkArray; dsimp only; split_ifs <;> first | rfl | omega
        unfold subblockSum at hsm
        have hidx1 : (⟨n - 2, by omega⟩ : Fin n).castSucc = ⟨n - 2, by omega⟩ := by ext; rfl
        have hidx2 : (⟨n - 2, by omega⟩ : Fin n).succ = (⟨n - 1, by omega⟩ : Fin n).castSucc := by ext; simp; omega
        have hidx3 : (⟨n - 1, by omega⟩ : Fin n).succ = ⟨n, by omega⟩ := by ext; simp; omega
        rw [hidx1, hidx2, hidx3] at hsm
        omega
  · intro A hA B hB h
    rw [Finset.mem_filter] at hA hB
    have h0 : cnt A 0 = cnt B 0 := congr_arg (fun t => t.1.val) h
    have h1 : cnt A 1 = cnt B 1 := congr_arg (fun t => t.2.1.val) h
    have h2 : cnt A 2 = cnt B 2 := congr_arg (fun t => t.2.2.1.val) h
    rw [hA_eq A hA.2.1, hA_eq B hB.2.1, h0, h1, h2]
  · intro ⟨c0, c1, c2, c3⟩ ht
    rw [Finset.mem_filter] at ht
    rcases ht.2 with ⟨hsum, hcol, hsm⟩
    let A := mkArray (n := n) c0.val c1.val c2.val
    have hcnts : cnt A 0 = c0.val ∧ cnt A 1 = c1.val ∧ cnt A 2 = c2.val ∧ cnt A 3 = c3.val := by
      have haux : ∀ k lo hi : ℕ, hi ≤ n + 1 → lo ≤ hi →
          (∀ r : Fin (n + 1), rowCode (A r 0) (A r 1) = k ↔ lo ≤ r.val ∧ r.val < hi) →
          cnt A k = hi - lo := by
        intro k lo hi hhi hlo hiff
        unfold cnt
        rw [← Nat.card_Ico lo hi]
        refine Finset.card_bij (fun r _ => r.val) ?_ ?_ ?_
        · intro r hr; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
          exact Finset.mem_Ico.mpr ((hiff r).mp hr)
        · intro r1 _ r2 _ h; exact Fin.ext h
        · intro x hx; rw [Finset.mem_Ico] at hx
          exact ⟨⟨x, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact (hiff _).mpr hx, rfl⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := haux 0 0 c0.val (by omega) (by omega) (fun r => by
          unfold A mkArray rowCode; split_ifs <;> simp_all <;> omega)
        omega
      · have := haux 1 c0.val (c0.val + c1.val) (by omega) (by omega) (fun r => by
          unfold A mkArray rowCode; split_ifs <;> simp_all <;> omega)
        omega
      · have := haux 2 (c0.val + c1.val) (c0.val + c1.val + c2.val) (by omega) (by omega) (fun r => by
          unfold A mkArray rowCode; split_ifs <;> simp_all <;> omega)
        omega
      · have := haux 3 (c0.val + c1.val + c2.val) (n + 1) (by omega) (by omega) (fun r => by
          unfold A mkArray rowCode; split_ifs <;> simp_all <;> omega)
        omega
    refine ⟨A, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
      · rw [rowsNondecreasing_iff]
        intro r1 r2 hle
        unfold A mkArray rowCode
        split_ifs <;> simp_all <;> omega
      · rcases hcol with hc1 | hc2
        · right
          refine ⟨⟨c0.val, by omega⟩, ?_, ?_, ?_⟩
          · intro r' hr'; unfold A mkArray; have : r'.val < c0.val := hr'; simp [this]
          · unfold A mkArray; dsimp only; split_ifs <;> first | rfl | omega
          · unfold A mkArray; dsimp only; split_ifs <;> first | rfl | omega
        · by_cases hc1 : 1 ≤ c1.val
          · right
            refine ⟨⟨c0.val, by omega⟩, ?_, ?_, ?_⟩
            · intro r' hr'; unfold A mkArray; have : r'.val < c0.val := hr'; simp [this]
            · unfold A mkArray; dsimp only; split_ifs <;> first | rfl | omega
            · unfold A mkArray; dsimp only; split_ifs <;> first | rfl | omega
          · left; intro r; unfold A mkArray; split_ifs <;> first | rfl | omega
      · intro i j hij
        have hrowSum : ∀ r : Fin (n + 1),
            (A r 0).toNat + (A r 1).toNat =
              if r.val < c0.val then 0
              else if r.val < c0.val + c1.val + c2.val then 1 else 2 := by
          intro r; unfold A mkArray; split_ifs <;> first | rfl | omega
        unfold subblockSum
        have hjeq : i.succ = j.castSucc := by ext; simp [hij]
        rw [hjeq]
        have hs1 := hrowSum i.castSucc
        have hs2 := hrowSum j.succ
        simp only [Fin.val_castSucc, Fin.val_succ] at hs1 hs2
        split_ifs at hs1 hs2 <;> omega
    · ext <;> simp [hcnts]

-- Sum identity: 6 * (4 + ∑_{m=2}^{n+1} m * (n + 2 - m)) = n^3 + 6*n^2 + 5*n + 24
private lemma sum_formula (n : ℕ) (hn : 1 < n) :
    6 * (4 + ∑ m ∈ Finset.Icc 2 (n + 1), m * (n + 2 - m)) =
      n ^ 3 + 6 * n ^ 2 + 5 * n + 24 := by
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 1
    · subst hk; decide
    · have hk1 : 1 < k := by omega
      have hih := ih hk1
      have hsplit : ∑ m ∈ Finset.Icc 2 (k + 2), m * (k + 3 - m) =
          (∑ m ∈ Finset.Icc 2 (k + 1), m * (k + 2 - m)) +
          (∑ m ∈ Finset.Icc 2 (k + 1), m) + (k + 2) := by
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hlast : (k + 2) * (k + 3 - (k + 2)) = k + 2 := by
          have : k + 3 - (k + 2) = 1 := by omega
          rw [this, mul_one]
        rw [hlast, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun m hm => ?_)
        rw [Finset.mem_Icc] at hm
        have : k + 3 - m = (k + 2 - m) + 1 := by omega
        rw [this, mul_add, mul_one]
      have htri : 2 * ∑ m ∈ Finset.Icc 2 (k + 1), m = (k + 1) * (k + 2) - 2 := by
        have h1 : ∑ m ∈ Finset.Icc 2 (k + 1), m + 1 = ∑ m ∈ Finset.range (k + 2), m := by
          have hI : Finset.range (k + 2) = {0, 1} ∪ Finset.Icc 2 (k + 1) := by
            ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton, Finset.mem_Icc]; omega
          rw [hI, Finset.sum_union]
          · simp; ring
          · rw [Finset.disjoint_left]; intro x hx1 hx2
            simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hx1 hx2; omega
        have h2 := Finset.sum_range_id_mul_two (k + 2)
        have hsub : k + 2 - 1 = k + 1 := by omega
        rw [hsub] at h2
        have h3 : 2 * ∑ m ∈ Finset.range (k + 2), m = (k + 2) * (k + 1) := by linarith
        have h4 : (k + 2) * (k + 1) = (k + 1) * (k + 2) := Nat.mul_comm _ _
        omega
      rw [hsplit]
      have hge : 2 ≤ (k + 1) * (k + 2) := by nlinarith
      have htri' : 2 * ∑ m ∈ Finset.Icc 2 (k + 1), m + 2 = (k + 1) * (k + 2) := by omega
      linarith

-- Count valid tuples by grouping on m = c1 + c2
private lemma card_validTuple (n : ℕ) (hn : 1 < n) :
    (Finset.univ.filter (validTuple n)).card =
      4 + ∑ m ∈ Finset.Icc 2 (n + 1), m * (n + 2 - m) := by
  let S := Finset.univ.filter (validTuple n)
  let fiber (m : ℕ) := S.filter (fun t => t.2.1.val + t.2.2.1.val = m)
  have hpart : S.card = ∑ m ∈ Finset.range (n + 2), (fiber m).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext ⟨c0, c1, c2, c3⟩
      simp only [Finset.mem_biUnion, Finset.mem_range, fiber, Finset.mem_filter, S,
        Finset.mem_univ, true_and]
      constructor
      · intro ht; exact ⟨c1.val + c2.val, by have := ht.1; omega, ht, rfl⟩
      · rintro ⟨_, _, ht, _⟩; exact ht
    · intro m1 _ m2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro t h1 h2
      simp only [fiber, Finset.mem_filter] at h1 h2
      exact hne (h1.2.symm.trans h2.2)
  have hrange : Finset.range (n + 2) = {0, 1} ∪ Finset.Icc 2 (n + 1) := by
    ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_Icc]; omega
  rw [hpart, hrange, Finset.sum_union]
  · simp only [Finset.sum_pair (show (0 : ℕ) ≠ 1 by decide)]
    have hf0 : (fiber 0).card = 2 := by
      have hset : fiber 0 =
          {(⟨n + 1, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩),
           (⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨n + 1, by omega⟩)} := by
        ext ⟨c0, c1, c2, c3⟩
        simp only [fiber, S, Finset.mem_filter, Finset.mem_univ, true_and, validTuple,
          Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff]
        constructor
        · rintro ⟨⟨hsum, _, hsm⟩, hm0⟩
          have hc1 : c1.val = 0 := by omega
          have hc2 : c2.val = 0 := by omega
          by_cases h0 : c0.val = 0
          · right; refine ⟨h0, hc1, hc2, by omega⟩
          · left; refine ⟨by omega, hc1, hc2, by omega⟩
        · rintro (⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩) <;>
          refine ⟨⟨by omega, Or.inr (by omega), by omega⟩, by omega⟩
      rw [hset, Finset.card_pair]
      intro h; have := congr_arg (fun t => t.1.val) h; simp at this
    have hf1 : (fiber 1).card = 2 := by
      have hset : fiber 1 =
          {(⟨n, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩),
           (⟨0, by omega⟩, ⟨1, by omega⟩, ⟨0, by omega⟩, ⟨n, by omega⟩)} := by
        ext ⟨c0, c1, c2, c3⟩
        simp only [fiber, S, Finset.mem_filter, Finset.mem_univ, true_and, validTuple,
          Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Fin.ext_iff]
        constructor
        · rintro ⟨⟨hsum, hcol, hsm⟩, hm1⟩
          have hc1 : c1.val = 1 := by omega
          have hc2 : c2.val = 0 := by omega
          by_cases h0 : c0.val = 0
          · right; refine ⟨h0, hc1, hc2, by omega⟩
          · left; refine ⟨by omega, hc1, hc2, by omega⟩
        · rintro (⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩) <;>
          refine ⟨⟨by omega, Or.inl (by omega), by omega⟩, by omega⟩
      rw [hset, Finset.card_pair]
      intro h; have := congr_arg (fun t => t.1.val) h; simp at this; omega
    have hfm : ∀ m ∈ Finset.Icc 2 (n + 1), (fiber m).card = m * (n + 2 - m) := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      have hcard : (fiber m).card = (Finset.Icc 1 m ×ˢ Finset.range (n + 2 - m)).card := by
        refine Finset.card_bij (fun t _ => (t.2.1.val, t.1.val)) ?_ ?_ ?_
        · intro ⟨c0, c1, c2, c3⟩ ht
          simp only [fiber, S, Finset.mem_filter, Finset.mem_univ, true_and, validTuple] at ht
          simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
          omega
        · intro ⟨a0, a1, a2, a3⟩ ha ⟨b0, b1, b2, b3⟩ hb h
          simp only [fiber, S, Finset.mem_filter, Finset.mem_univ, true_and, validTuple] at ha hb
          simp only [Prod.mk.injEq] at h
          ext <;> dsimp only <;> omega
        · intro ⟨x, y⟩ hxy
          simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hxy
          refine ⟨(⟨y, by omega⟩, ⟨x, by omega⟩, ⟨m - x, by omega⟩, ⟨n + 1 - m - y, by omega⟩), ?_, rfl⟩
          simp only [fiber, S, Finset.mem_filter, Finset.mem_univ, true_and, validTuple]
          refine ⟨⟨by omega, Or.inl (by omega), by omega⟩, by omega⟩
      rw [hcard, Finset.card_product, Nat.card_Icc, Finset.card_range]
      have : m + 1 - 1 = m := by omega
      rw [this]
    rw [hf0, hf1, Finset.sum_congr rfl hfm]
  · rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc] at hx1 hx2; omega

theorem main :
    (∀ n : ℕ, 1 < n → 6 * a n = n ^ 3 + 6 * n ^ 2 + 5 * n + 24) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  have hclosed : ∀ n : ℕ, 1 < n → 6 * a n = n ^ 3 + 6 * n ^ 2 + 5 * n + 24 := by
    intro n hn
    unfold a
    rw [Nat.card_eq_fintype_card, card_valid_eq_tuples n hn, card_validTuple n hn]
    exact sum_formula n hn
  refine ⟨hclosed, ?_⟩
  intro n hn
  have h0 : 6 * (a n : ℤ) = (n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 2 + 5 * (n : ℤ) + 24 := by
    exact_mod_cast hclosed n (by omega)
  have h1 : 6 * (a (n - 1) : ℤ) = ((n - 1 : ℕ) : ℤ) ^ 3 + 6 * ((n - 1 : ℕ) : ℤ) ^ 2 + 5 * ((n - 1 : ℕ) : ℤ) + 24 := by
    exact_mod_cast hclosed (n - 1) (by omega)
  have h2 : 6 * (a (n - 2) : ℤ) = ((n - 2 : ℕ) : ℤ) ^ 3 + 6 * ((n - 2 : ℕ) : ℤ) ^ 2 + 5 * ((n - 2 : ℕ) : ℤ) + 24 := by
    exact_mod_cast hclosed (n - 2) (by omega)
  have h3 : 6 * (a (n - 3) : ℤ) = ((n - 3 : ℕ) : ℤ) ^ 3 + 6 * ((n - 3 : ℕ) : ℤ) ^ 2 + 5 * ((n - 3 : ℕ) : ℤ) + 24 := by
    exact_mod_cast hclosed (n - 3) (by omega)
  have h4 : 6 * (a (n - 4) : ℤ) = ((n - 4 : ℕ) : ℤ) ^ 3 + 6 * ((n - 4 : ℕ) : ℤ) ^ 2 + 5 * ((n - 4 : ℕ) : ℤ) + 24 := by
    exact_mod_cast hclosed (n - 4) (by omega)
  have c1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
  have c3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by rw [Nat.cast_sub (by omega)]; simp
  have c4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by rw [Nat.cast_sub (by omega)]; simp
  rw [c1] at h1; rw [c2] at h2; rw [c3] at h3; rw [c4] at h4
  linarith

end ProofA184063

theorem OMA.solution : type_of% @OMA.S_oeis_a184063.main :=
  ProofA184063.main
