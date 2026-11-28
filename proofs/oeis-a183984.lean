import OMAStatements.S_oeis_a183984

-- Problem: OEIS-A183984: 1/4 the number of (n+1) X 8 binary arrays with all 2 X 2 subblock sums the same.
-- Credit: @ceejcake
-- Proof via exact partition by constant 2x2 subblock sum s in {0, 1, 2, 3, 4}.

namespace GridEqual2x2

open scoped Classical

def subblockSum {n m : ℕ} (A : Fin (n + 1) → Fin (m + 1) → Bool) (i : Fin n) (j : Fin m) : ℕ :=
  (A i.castSucc j.castSucc).toNat + (A i.castSucc j.succ).toNat +
  (A i.succ j.castSucc).toNat + (A i.succ j.succ).toNat

def hasConstSum {n m : ℕ} (s : ℕ) (A : Fin (n + 1) → Fin (m + 1) → Bool) : Prop :=
  ∀ (i : Fin n) (j : Fin m), subblockSum A i j = s

def isValid (n m : ℕ) (A : Fin (n + 1) → Fin (m + 1) → Bool) : Prop :=
  ∃ s : ℕ, hasConstSum s A

-- Helper: Bool.toNat arithmetic
private lemma toNat_le_one (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
private lemma toNat_not (b : Bool) : (!b).toNat = 1 - b.toNat := by cases b <;> decide

-- Helper: Finset of arrays with constant sum s
private noncomputable def S (n m s : ℕ) : Finset (Fin (n + 1) → Fin (m + 1) → Bool) :=
  Finset.univ.filter (hasConstSum s)

-- Helper: every valid array has s ∈ {0,1,2,3,4}
private lemma subblockSum_le_four {n m : ℕ} (A : Fin (n + 1) → Fin (m + 1) → Bool)
    (i : Fin n) (j : Fin m) : subblockSum A i j ≤ 4 := by
  unfold subblockSum
  have h1 := toNat_le_one (A i.castSucc j.castSucc)
  have h2 := toNat_le_one (A i.castSucc j.succ)
  have h3 := toNat_le_one (A i.succ j.castSucc)
  have h4 := toNat_le_one (A i.succ j.succ)
  omega

-- 1. |S 0| = 1 and |S 4| = 1
private lemma card_S_zero {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (S n m 0).card = 1 := by
  have hset : S n m 0 = {fun _ _ => false} := by
    ext A
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hA
      ext r c
      have hsub : ∀ (i : Fin n) (j : Fin m),
          A i.castSucc j.castSucc = false ∧ A i.castSucc j.succ = false ∧
          A i.succ j.castSucc = false ∧ A i.succ j.succ = false := by
        intro i j
        have hs := hA i j
        unfold subblockSum at hs
        cases h1 : A i.castSucc j.castSucc <;> cases h2 : A i.castSucc j.succ <;>
        cases h3 : A i.succ j.castSucc <;> cases h4 : A i.succ j.succ <;>
        simp_all
      by_cases hr : r.val < n
      · by_cases hc : c.val < m
        · exact (hsub ⟨r.val, hr⟩ ⟨c.val, hc⟩).1
        · have hc' : c.val = m := by omega
          have h := (hsub ⟨r.val, hr⟩ ⟨m - 1, by omega⟩).2.1
          have hce : (⟨m - 1, by omega⟩ : Fin m).succ = c := by ext; simp; omega
          rw [hce] at h; exact h
      · have hr' : r.val = n := by omega
        have hre : (⟨n - 1, by omega⟩ : Fin n).succ = r := by ext; simp; omega
        by_cases hc : c.val < m
        · have h := (hsub ⟨n - 1, by omega⟩ ⟨c.val, hc⟩).2.2.1
          rw [hre] at h; exact h
        · have hc' : c.val = m := by omega
          have hce : (⟨m - 1, by omega⟩ : Fin m).succ = c := by ext; simp; omega
          have h := (hsub ⟨n - 1, by omega⟩ ⟨m - 1, by omega⟩).2.2.2
          rw [hre, hce] at h; exact h
    · rintro rfl i j; simp [subblockSum]
  rw [hset, Finset.card_singleton]

private lemma card_S_four {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (S n m 4).card = 1 := by
  have hset : S n m 4 = {fun _ _ => true} := by
    ext A
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hA
      ext r c
      have hsub : ∀ (i : Fin n) (j : Fin m),
          A i.castSucc j.castSucc = true ∧ A i.castSucc j.succ = true ∧
          A i.succ j.castSucc = true ∧ A i.succ j.succ = true := by
        intro i j
        have hs := hA i j
        unfold subblockSum at hs
        cases h1 : A i.castSucc j.castSucc <;> cases h2 : A i.castSucc j.succ <;>
        cases h3 : A i.succ j.castSucc <;> cases h4 : A i.succ j.succ <;>
        simp_all
      by_cases hr : r.val < n
      · by_cases hc : c.val < m
        · exact (hsub ⟨r.val, hr⟩ ⟨c.val, hc⟩).1
        · have hc' : c.val = m := by omega
          have h := (hsub ⟨r.val, hr⟩ ⟨m - 1, by omega⟩).2.1
          have hce : (⟨m - 1, by omega⟩ : Fin m).succ = c := by ext; simp; omega
          rw [hce] at h; exact h
      · have hr' : r.val = n := by omega
        have hre : (⟨n - 1, by omega⟩ : Fin n).succ = r := by ext; simp; omega
        by_cases hc : c.val < m
        · have h := (hsub ⟨n - 1, by omega⟩ ⟨c.val, hc⟩).2.2.1
          rw [hre] at h; exact h
        · have hc' : c.val = m := by omega
          have hce : (⟨m - 1, by omega⟩ : Fin m).succ = c := by ext; simp; omega
          have h := (hsub ⟨n - 1, by omega⟩ ⟨m - 1, by omega⟩).2.2.2
          rw [hre, hce] at h; exact h
    · rintro rfl i j; simp [subblockSum]
  rw [hset, Finset.card_singleton]

-- 2. |S 3| = |S 1| via complementation
private lemma card_S_three {n m : ℕ} : (S n m 3).card = (S n m 1).card := by
  refine Finset.card_bij (fun A _ => fun r c => !(A r c)) ?_ ?_ ?_
  · intro A hA
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    intro i j
    have hs := hA i j
    unfold subblockSum at hs ⊢
    cases h1 : A i.castSucc j.castSucc <;> cases h2 : A i.castSucc j.succ <;>
    cases h3 : A i.succ j.castSucc <;> cases h4 : A i.succ j.succ <;>
    simp_all
  · intro A _ B _ h
    ext r c
    have hrc := congr_fun (congr_fun h r) c
    cases hA : A r c <;> cases hB : B r c <;> simp_all
  · intro B hB
    refine ⟨fun r c => !(B r c), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
      intro i j
      have hs := hB i j
      unfold subblockSum at hs ⊢
      cases h1 : B i.castSucc j.castSucc <;> cases h2 : B i.castSucc j.succ <;>
      cases h3 : B i.succ j.castSucc <;> cases h4 : B i.succ j.succ <;>
      simp_all
    · ext r c; simp

-- 3. |S 2| = 2^(n+1) + 2^(m+1) - 2
private def rowAlt {n m : ℕ} (A : Fin (n + 1) → Fin (m + 1) → Bool) : Prop :=
  ∀ (r : Fin (n + 1)) (j : Fin m), A r j.succ = !(A r j.castSucc)

private def colAlt {n m : ℕ} (A : Fin (n + 1) → Fin (m + 1) → Bool) : Prop :=
  ∀ (i : Fin n) (c : Fin (m + 1)), A i.succ c = !(A i.castSucc c)

private lemma S2_iff {n m : ℕ} (A : Fin (n + 1) → Fin (m + 1) → Bool) :
    hasConstSum 2 A ↔ rowAlt A ∨ colAlt A := by
  constructor
  · intro hA
    by_cases hr : rowAlt A
    · exact Or.inl hr
    · right
      -- If not rowAlt, there exist r0, j0 with A r0 j0.succ = A r0 j0.castSucc
      simp only [rowAlt, not_forall] at hr
      rcases hr with ⟨r0, j0, hneq⟩
      have heq0 : A r0 j0.succ = A r0 j0.castSucc := by
        cases h1 : A r0 j0.succ <;> cases h2 : A r0 j0.castSucc <;> simp_all
      -- Key 2x2 step: in any 2x2 block, (top eq -> bottom eq & both cols alt),
      -- and (bottom eq -> top eq & both cols alt), and (one col alt -> other col alt)
      have hstep : ∀ (i : Fin n) (j : Fin m),
          (A i.castSucc j.succ = A i.castSucc j.castSucc →
            A i.succ j.castSucc = !(A i.castSucc j.castSucc) ∧
            A i.succ j.succ = !(A i.castSucc j.succ)) ∧
          (A i.succ j.succ = A i.succ j.castSucc →
            A i.succ j.castSucc = !(A i.castSucc j.castSucc) ∧
            A i.succ j.succ = !(A i.castSucc j.succ)) ∧
          (A i.succ j.castSucc = !(A i.castSucc j.castSucc) ↔
            A i.succ j.succ = !(A i.castSucc j.succ)) := by
        intro i j
        have hs := hA i j
        unfold subblockSum at hs
        cases h1 : A i.castSucc j.castSucc <;> cases h2 : A i.castSucc j.succ <;>
        cases h3 : A i.succ j.castSucc <;> cases h4 : A i.succ j.succ <;>
        simp_all
      -- First prove A r j0.succ = A r j0.castSucc for ALL r (moving up and down from r0)
      have hcol_j0 : ∀ (i : Fin n), A i.succ j0.castSucc = !(A i.castSucc j0.castSucc) := by
        -- Prove ∀ r, A r j0.succ = A r j0.castSucc by induction on distance from r0
        have heq_all : ∀ k : ℕ, (hk : k ≤ n) →
            A ⟨k, by omega⟩ j0.succ = A ⟨k, by omega⟩ j0.castSucc := by
          -- Step up from r0
          have hup : ∀ d : ℕ, (hd : r0.val + d ≤ n) →
              A ⟨r0.val + d, by omega⟩ j0.succ = A ⟨r0.val + d, by omega⟩ j0.castSucc := by
            intro d
            induction d with
            | zero => intro _; simpa using heq0
            | succ d ih =>
              intro hd
              have hprev := ih (by omega)
              have hi := (hstep ⟨r0.val + d, by omega⟩ j0).1 hprev
              have hfin : (⟨r0.val + d, by omega⟩ : Fin n).succ = ⟨r0.val + (d + 1), by omega⟩ := by
                ext; simp; omega
              rw [← hfin, hi.1, hi.2]
              exact congr_arg not hprev
          -- Step down from r0
          have hdown : ∀ d : ℕ, (hd : d ≤ r0.val) →
              A ⟨r0.val - d, by omega⟩ j0.succ = A ⟨r0.val - d, by omega⟩ j0.castSucc := by
            intro d
            induction d with
            | zero => intro _; simpa using heq0
            | succ d ih =>
              intro hd
              have hprev := ih (by omega)
              have hidx : (⟨r0.val - (d + 1), by omega⟩ : Fin n).succ = ⟨r0.val - d, by omega⟩ := by
                ext; simp; omega
              have hprev' : A (⟨r0.val - (d + 1), by omega⟩ : Fin n).succ j0.succ =
                  A (⟨r0.val - (d + 1), by omega⟩ : Fin n).succ j0.castSucc := by
                rw [hidx]; exact hprev
              have hi := (hstep ⟨r0.val - (d + 1), by omega⟩ j0).2.1 hprev'
              cases h1 : A ⟨r0.val - (d + 1), by omega⟩ j0.castSucc <;>
              cases h2 : A ⟨r0.val - (d + 1), by omega⟩ j0.succ <;>
              simp_all
          intro k hk
          by_cases hle : r0.val ≤ k
          · have := hup (k - r0.val) (by omega)
            have heq : r0.val + (k - r0.val) = k := by omega
            convert this using 2 <;> ext <;> simp [heq]
          · have := hdown (r0.val - k) (by omega)
            have heq : r0.val - (r0.val - k) = k := by omega
            convert this using 2 <;> ext <;> simp [heq]
        intro i
        exact ((hstep i j0).1 (heq_all i.val (by omega))).1
      -- Now propagate colAlt from j0.castSucc to ALL columns c
      intro i c
      have hup : ∀ d : ℕ, (hd : j0.val + d ≤ m) →
          A i.succ ⟨j0.val + d, by omega⟩ = !(A i.castSucc ⟨j0.val + d, by omega⟩) := by
        intro d
        induction d with
        | zero => intro _; exact hcol_j0 i
        | succ d ih =>
          intro hd
          exact (hstep i ⟨j0.val + d, by omega⟩).2.2.mp (ih (by omega))
      have hdown : ∀ d : ℕ, (hd : d ≤ j0.val) →
          A i.succ ⟨j0.val - d, by omega⟩ = !(A i.castSucc ⟨j0.val - d, by omega⟩) := by
        intro d
        induction d with
        | zero => intro _; exact hcol_j0 i
        | succ d ih =>
          intro hd
          have hidx : (⟨j0.val - (d + 1), by omega⟩ : Fin m).succ = ⟨j0.val - d, by omega⟩ := by
            ext; simp; omega
          have hprev : A i.succ (⟨j0.val - (d + 1), by omega⟩ : Fin m).succ =
              !(A i.castSucc (⟨j0.val - (d + 1), by omega⟩ : Fin m).succ) := by
            rw [hidx]; exact ih (by omega)
          exact (hstep i ⟨j0.val - (d + 1), by omega⟩).2.2.mpr hprev
      by_cases hle : j0.val ≤ c.val
      · have := hup (c.val - j0.val) (by omega)
        have hfin : (⟨j0.val + (c.val - j0.val), by omega⟩ : Fin (m + 1)) = c := by ext; simp; omega
        rw [hfin] at this; exact this
      · have := hdown (j0.val - c.val) (by omega)
        have hfin : (⟨j0.val - (j0.val - c.val), by omega⟩ : Fin (m + 1)) = c := by ext; simp; omega
        rw [hfin] at this; exact this
  · rintro (hr | hc) i j
    · unfold subblockSum
      rw [hr i.castSucc j, hr i.succ j]
      cases A i.castSucc j.castSucc <;> cases A i.succ j.castSucc <;> decide
    · unfold subblockSum
      rw [hc i j.castSucc, hc i j.succ]
      cases A i.castSucc j.castSucc <;> cases A i.castSucc j.succ <;> decide

private lemma card_rowAlt {n m : ℕ} :
    (Finset.univ.filter (rowAlt (n := n) (m := m))).card = 2 ^ (n + 1) := by
  have hbij : (Finset.univ.filter (rowAlt (n := n) (m := m))).card =
      Fintype.card (Fin (n + 1) → Bool) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun A _ r => A r 0) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro A hA B hB h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA hB
      ext r c
      induction c using Fin.induction with
      | zero => exact congr_fun h r
      | succ j ih => rw [hA r j, hB r j, ih]
    · intro f _
      refine ⟨fun r c => xor (f r) (decide (c.val % 2 = 1)), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro r j
        simp only [Fin.val_succ, Fin.val_castSucc]
        have : (j.val + 1) % 2 = 1 ↔ ¬ (j.val % 2 = 1) := by omega
        cases f r <;> by_cases hj : j.val % 2 = 1 <;> simp_all
      · ext r; simp
  rw [hbij, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

private lemma card_colAlt {n m : ℕ} :
    (Finset.univ.filter (colAlt (n := n) (m := m))).card = 2 ^ (m + 1) := by
  have hbij : (Finset.univ.filter (colAlt (n := n) (m := m))).card =
      Fintype.card (Fin (m + 1) → Bool) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun A _ c => A 0 c) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro A hA B hB h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA hB
      ext r c
      induction r using Fin.induction with
      | zero => exact congr_fun h c
      | succ i ih => rw [hA i c, hB i c, ih]
    · intro g _
      refine ⟨fun r c => xor (g c) (decide (r.val % 2 = 1)), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i c
        simp only [Fin.val_succ, Fin.val_castSucc]
        have : (i.val + 1) % 2 = 1 ↔ ¬ (i.val % 2 = 1) := by omega
        cases g c <;> by_cases hi : i.val % 2 = 1 <;> simp_all
      · ext c; simp
  rw [hbij, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

private lemma card_rowAlt_inter_colAlt {n m : ℕ} :
    (Finset.univ.filter (rowAlt (n := n) (m := m)) ∩
      Finset.univ.filter (colAlt (n := n) (m := m))).card = 2 := by
  have hbij : (Finset.univ.filter (rowAlt (n := n) (m := m)) ∩
      Finset.univ.filter (colAlt (n := n) (m := m))).card = Fintype.card Bool := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun A _ => A 0 0) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro A hA B hB h
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hA hB
      ext r c
      induction r using Fin.induction with
      | zero =>
        induction c using Fin.induction with
        | zero => exact h
        | succ j ih => rw [hA.1 0 j, hB.1 0 j, ih]
      | succ i ih => rw [hA.2 i c, hB.2 i c, ih]
    · intro b _
      refine ⟨fun r c => xor b (decide ((r.val + c.val) % 2 = 1)), ?_, ?_⟩
      · simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro r j
          simp only [Fin.val_succ, Fin.val_castSucc]
          have : (r.val + (j.val + 1)) % 2 = 1 ↔ ¬ ((r.val + j.val) % 2 = 1) := by omega
          cases b <;> by_cases h : (r.val + j.val) % 2 = 1 <;> simp_all
        · intro i c
          simp only [Fin.val_succ, Fin.val_castSucc]
          have : (i.val + 1 + c.val) % 2 = 1 ↔ ¬ ((i.val + c.val) % 2 = 1) := by omega
          cases b <;> by_cases h : (i.val + c.val) % 2 = 1 <;> simp_all
      · simp
  rw [hbij, Fintype.card_bool]

private lemma card_S_two {n m : ℕ} :
    (S n m 2).card = 2 ^ (n + 1) + 2 ^ (m + 1) - 2 := by
  have hunion : S n m 2 = Finset.univ.filter (rowAlt (n := n) (m := m)) ∪
      Finset.univ.filter (colAlt (n := n) (m := m)) := by
    ext A
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact S2_iff A
  rw [hunion]
  have hcu := Finset.card_union_add_card_inter
    (Finset.univ.filter (rowAlt (n := n) (m := m)))
    (Finset.univ.filter (colAlt (n := n) (m := m)))
  rw [card_rowAlt, card_colAlt, card_rowAlt_inter_colAlt] at hcu
  omega

-- 4. |S 1| = 2^((n+2)/2) + 2^((n+1)/2) + 2^((m+2)/2) + 2^((m+1)/2) - 4
-- Family of row-striped arrays of parity p ∈ {0, 1}:
-- rows with r.val % 2 ≠ p are all false; rows with r.val % 2 = p alternate!
private def rowStripe {n m : ℕ} (p : ℕ) (A : Fin (n + 1) → Fin (m + 1) → Bool) : Prop :=
  (∀ (r : Fin (n + 1)) (c : Fin (m + 1)), r.val % 2 ≠ p → A r c = false) ∧
  (∀ (r : Fin (n + 1)) (j : Fin m), r.val % 2 = p → A r j.succ = !(A r j.castSucc))

private def colStripe {n m : ℕ} (p : ℕ) (A : Fin (n + 1) → Fin (m + 1) → Bool) : Prop :=
  (∀ (r : Fin (n + 1)) (c : Fin (m + 1)), c.val % 2 ≠ p → A r c = false) ∧
  (∀ (i : Fin n) (c : Fin (m + 1)), c.val % 2 = p → A i.succ c = !(A i.castSucc c))

-- Key lemma: if A ∈ S 1 and some row r0 is all false, then A is a rowStripe!
private lemma S1_of_zero_row {n m : ℕ} (hm : 1 ≤ m) (A : Fin (n + 1) → Fin (m + 1) → Bool)
    (hA : hasConstSum 1 A) (r0 : Fin (n + 1)) (hz : ∀ c, A r0 c = false) :
    rowStripe (1 - r0.val % 2) A := by
  -- Step: if row i is all false then adjacent row alternates, and if row alternates then adjacent row is all false
  have hstep : ∀ (i : Fin n),
      ((∀ c, A i.castSucc c = false) → (∀ j : Fin m, A i.succ j.succ = !(A i.succ j.castSucc))) ∧
      ((∀ j : Fin m, A i.castSucc j.succ = !(A i.castSucc j.castSucc)) → (∀ c, A i.succ c = false)) ∧
      ((∀ c, A i.succ c = false) → (∀ j : Fin m, A i.castSucc j.succ = !(A i.castSucc j.castSucc))) ∧
      ((∀ j : Fin m, A i.succ j.succ = !(A i.succ j.castSucc)) → (∀ c, A i.castSucc c = false)) := by
    intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 j
      have hs := hA i j
      unfold subblockSum at hs
      rw [h0 j.castSucc, h0 j.succ] at hs
      cases h1 : A i.succ j.castSucc <;> cases h2 : A i.succ j.succ <;> simp_all
    · intro halt c
      by_cases hc : c.val < m
      · have hs := hA i ⟨c.val, hc⟩
        unfold subblockSum at hs
        have ha := halt ⟨c.val, hc⟩
        cases h1 : A i.castSucc (⟨c.val, hc⟩ : Fin m).castSucc <;>
        cases h2 : A i.succ (⟨c.val, hc⟩ : Fin m).castSucc <;>
        cases h3 : A i.succ (⟨c.val, hc⟩ : Fin m).succ <;> simp_all
      · have hs := hA i ⟨m - 1, by omega⟩
        unfold subblockSum at hs
        have ha := halt ⟨m - 1, by omega⟩
        have hce : (⟨m - 1, by omega⟩ : Fin m).succ = c := by ext; simp; omega
        cases h1 : A i.castSucc (⟨m - 1, by omega⟩ : Fin m).castSucc <;>
        cases h2 : A i.succ (⟨m - 1, by omega⟩ : Fin m).castSucc <;>
        cases h3 : A i.succ (⟨m - 1, by omega⟩ : Fin m).succ <;> simp_all
    · intro h0 j
      have hs := hA i j
      unfold subblockSum at hs
      rw [h0 j.castSucc, h0 j.succ] at hs
      cases h1 : A i.castSucc j.castSucc <;> cases h2 : A i.castSucc j.succ <;> simp_all
    · intro halt c
      by_cases hc : c.val < m
      · have hs := hA i ⟨c.val, hc⟩
        unfold subblockSum at hs
        have ha := halt ⟨c.val, hc⟩
        cases h1 : A i.succ (⟨c.val, hc⟩ : Fin m).castSucc <;>
        cases h2 : A i.castSucc (⟨c.val, hc⟩ : Fin m).castSucc <;>
        cases h3 : A i.castSucc (⟨c.val, hc⟩ : Fin m).succ <;> simp_all
      · have hs := hA i ⟨m - 1, by omega⟩
        unfold subblockSum at hs
        have ha := halt ⟨m - 1, by omega⟩
        have hce : (⟨m - 1, by omega⟩ : Fin m).succ = c := by ext; simp; omega
        cases h1 : A i.succ (⟨m - 1, by omega⟩ : Fin m).castSucc <;>
        cases h2 : A i.castSucc (⟨m - 1, by omega⟩ : Fin m).castSucc <;>
        cases h3 : A i.castSucc (⟨m - 1, by omega⟩ : Fin m).succ <;> simp_all
  -- Propagate up and down from r0
  have hprop : ∀ (r : Fin (n + 1)),
      (r.val % 2 = r0.val % 2 → ∀ c, A r c = false) ∧
      (r.val % 2 ≠ r0.val % 2 → ∀ j : Fin m, A r j.succ = !(A r j.castSucc)) := by
    have hup : ∀ d : ℕ, (hd : r0.val + d ≤ n) →
        ((r0.val + d) % 2 = r0.val % 2 → ∀ c, A ⟨r0.val + d, by omega⟩ c = false) ∧
        ((r0.val + d) % 2 ≠ r0.val % 2 → ∀ j : Fin m, A ⟨r0.val + d, by omega⟩ j.succ = !(A ⟨r0.val + d, by omega⟩ j.castSucc)) := by
      intro d
      induction d with
      | zero =>
        intro _
        exact ⟨fun _ => by simpa using hz, fun h => absurd rfl h⟩
      | succ d ih =>
        intro hd
        have ⟨ih0, ih1⟩ := ih (by omega)
        constructor
        · intro heq
          exact (hstep ⟨r0.val + d, by omega⟩).2.1 (ih1 (by omega))
        · intro hne
          exact (hstep ⟨r0.val + d, by omega⟩).1 (ih0 (by omega))
    have hdown : ∀ d : ℕ, (hd : d ≤ r0.val) →
        ((r0.val - d) % 2 = r0.val % 2 → ∀ c, A ⟨r0.val - d, by omega⟩ c = false) ∧
        ((r0.val - d) % 2 ≠ r0.val % 2 → ∀ j : Fin m, A ⟨r0.val - d, by omega⟩ j.succ = !(A ⟨r0.val - d, by omega⟩ j.castSucc)) := by
      intro d
      induction d with
      | zero =>
        intro _
        exact ⟨fun _ => by simpa using hz, fun h => absurd rfl h⟩
      | succ d ih =>
        intro hd
        have ⟨ih0, ih1⟩ := ih (by omega)
        have hidx : (⟨r0.val - (d + 1), by omega⟩ : Fin n).succ = ⟨r0.val - d, by omega⟩ := by
          ext; simp; omega
        constructor
        · intro heq
          have halt : ∀ j : Fin m, A (⟨r0.val - (d + 1), by omega⟩ : Fin n).succ j.succ =
              !(A (⟨r0.val - (d + 1), by omega⟩ : Fin n).succ j.castSucc) := by
            rw [hidx]; exact ih1 (by omega)
          exact (hstep ⟨r0.val - (d + 1), by omega⟩).2.2.2 halt
        · intro hne
          have hzero : ∀ c, A (⟨r0.val - (d + 1), by omega⟩ : Fin n).succ c = false := by
            rw [hidx]; exact ih0 (by omega)
          exact (hstep ⟨r0.val - (d + 1), by omega⟩).2.2.1 hzero
    intro r
    by_cases hle : r0.val ≤ r.val
    · have ⟨h1, h2⟩ := hup (r.val - r0.val) (by omega)
      have heq : r0.val + (r.val - r0.val) = r.val := by omega
      have hfin : (⟨r0.val + (r.val - r0.val), by omega⟩ : Fin (n + 1)) = r := by ext; exact heq
      rw [hfin] at h1 h2
      exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩
    · have ⟨h1, h2⟩ := hdown (r0.val - r.val) (by omega)
      have heq : r0.val - (r0.val - r.val) = r.val := by omega
      have hfin : (⟨r0.val - (r0.val - r.val), by omega⟩ : Fin (n + 1)) = r := by ext; exact heq
      rw [hfin] at h1 h2
      exact ⟨fun h => h1 (by omega), fun h => h2 (by omega)⟩
  refine ⟨fun r c hne => (hprop r).1 (by omega) c, fun r j heq => (hprop r).2 (by omega) j⟩

-- Transpose helper: swapping rows and columns preserves hasConstSum 1!
private def transpose {n m : ℕ} (A : Fin (n + 1) → Fin (m + 1) → Bool) :
    Fin (m + 1) → Fin (n + 1) → Bool := fun c r => A r c

private lemma hasConstSum_transpose {n m s : ℕ} (A : Fin (n + 1) → Fin (m + 1) → Bool)
    (hA : hasConstSum s A) : hasConstSum s (transpose A) := by
  intro j i
  have hs := hA i j
  unfold subblockSum at hs ⊢
  dsimp only [transpose]
  omega

private lemma S1_of_zero_col {n m : ℕ} (hn : 1 ≤ n) (A : Fin (n + 1) → Fin (m + 1) → Bool)
    (hA : hasConstSum 1 A) (c0 : Fin (m + 1)) (hz : ∀ r, A r c0 = false) :
    colStripe (1 - c0.val % 2) A := by
  have h := S1_of_zero_row hn (transpose A) (hasConstSum_transpose A hA) c0 hz
  exact ⟨fun r c hne => h.1 c r hne, fun i c heq => h.2 c i heq⟩

private lemma S1_nbr {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (A : Fin (n + 1) → Fin (m + 1) → Bool) (hA : hasConstSum 1 A)
    (r1 r2 : Fin (n + 1)) (c1 c2 : Fin (m + 1))
    (ht : A r1 c1 = true)
    (hr : r1.val ≤ r2.val + 1 ∧ r2.val ≤ r1.val + 1)
    (hc : c1.val ≤ c2.val + 1 ∧ c2.val ≤ c1.val + 1)
    (hne : r1 ≠ r2 ∨ c1 ≠ c2) : A r2 c2 = false := by
  let i0 := min r1.val r2.val
  let j0 := min c1.val c2.val
  have hi : (if i0 < n then i0 else n - 1) < n := by split_ifs <;> omega
  have hj : (if j0 < m then j0 else m - 1) < m := by split_ifs <;> omega
  let i : Fin n := ⟨if i0 < n then i0 else n - 1, hi⟩
  let j : Fin m := ⟨if j0 < m then j0 else m - 1, hj⟩
  have hi_val : i.val = if i0 < n then i0 else n - 1 := rfl
  have hj_val : j.val = if j0 < m then j0 else m - 1 := rfl
  have hs := hA i j
  unfold subblockSum at hs
  have hr1 : r1 = i.castSucc ∨ r1 = i.succ := by
    by_cases h : r1.val = i.val
    · left; ext; exact h
    · right; ext; simp only [Fin.val_succ, hi_val, i0] at h ⊢; split_ifs at h ⊢ <;> omega
  have hr2 : r2 = i.castSucc ∨ r2 = i.succ := by
    by_cases h : r2.val = i.val
    · left; ext; exact h
    · right; ext; simp only [Fin.val_succ, hi_val, i0] at h ⊢; split_ifs at h ⊢ <;> omega
  have hc1 : c1 = j.castSucc ∨ c1 = j.succ := by
    by_cases h : c1.val = j.val
    · left; ext; exact h
    · right; ext; simp only [Fin.val_succ, hj_val, j0] at h ⊢; split_ifs at h ⊢ <;> omega
  have hc2 : c2 = j.castSucc ∨ c2 = j.succ := by
    by_cases h : c2.val = j.val
    · left; ext; exact h
    · right; ext; simp only [Fin.val_succ, hj_val, j0] at h ⊢; split_ifs at h ⊢ <;> omega
  rcases hr1 with hr1 | hr1 <;> rcases hr2 with hr2 | hr2 <;>
  rcases hc1 with hc1 | hc1 <;> rcases hc2 with hc2 | hc2 <;>
  · simp only [hr1, hr2, hc1, hc2] at ht hne ⊢
    first
    | exact absurd rfl (by tauto)
    | (rw [ht] at hs; cases h2 : A _ _
       · rfl
       · rw [h2] at hs; simp only [Bool.toNat_true] at hs; omega)

-- Key structural theorem for S 1 (for n ≥ 1, m ≥ 1):
-- Every A ∈ S 1 has either an all-false row or an all-false column!
private lemma S1_exists_zero_row_or_col {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (A : Fin (n + 1) → Fin (m + 1) → Bool) (hA : hasConstSum 1 A) :
    (∃ r0, ∀ c, A r0 c = false) ∨ (∃ c0, ∀ r, A r c0 = false) := by
  -- Look at block (0, 0): at least one entry is true; call its row r0
  have hex : ∃ (r0 : Fin (n + 1)) (c0 : Fin (m + 1)), A r0 c0 = true := by
    have hs := hA ⟨0, by omega⟩ ⟨0, by omega⟩
    unfold subblockSum at hs
    by_contra h
    push Not at h
    have hf : ∀ r c, A r c = false := fun r c => Bool.eq_false_iff.mpr (h r c)
    simp [hf] at hs
  rcases hex with ⟨r0, c0, ht0⟩
  -- Either row r0 alternates (in which case an adjacent row is all false!),
  -- or there is some column j with A r0 j.castSucc = false ∧ A r0 j.succ = false!
  by_cases halt : ∀ j : Fin m, A r0 j.succ = !(A r0 j.castSucc)
  · -- Pick a row r1 adjacent to r0 (either r0 + 1 or r0 - 1)
    left
    by_cases hlt : r0.val < n
    · refine ⟨(⟨r0.val, hlt⟩ : Fin n).succ, fun c => ?_⟩
      -- Every entry in row r0+1 is adjacent to a true in row r0
      by_cases hc : c.val < m
      · have hs := hA ⟨r0.val, hlt⟩ ⟨c.val, hc⟩
        unfold subblockSum at hs
        have ha := halt ⟨c.val, hc⟩
        have hre : (⟨r0.val, hlt⟩ : Fin n).castSucc = r0 := by ext; rfl
        rw [hre] at hs
        cases h1 : A r0 (⟨c.val, hc⟩ : Fin m).castSucc <;>
        cases h2 : A (⟨r0.val, hlt⟩ : Fin n).succ (⟨c.val, hc⟩ : Fin m).castSucc <;>
        cases h3 : A (⟨r0.val, hlt⟩ : Fin n).succ (⟨c.val, hc⟩ : Fin m).succ <;> simp_all
      · have hs := hA ⟨r0.val, hlt⟩ ⟨m - 1, by omega⟩
        unfold subblockSum at hs
        have ha := halt ⟨m - 1, by omega⟩
        have hre : (⟨r0.val, hlt⟩ : Fin n).castSucc = r0 := by ext; rfl
        have hce : (⟨m - 1, by omega⟩ : Fin m).succ = c := by ext; simp; omega
        rw [hre] at hs
        cases h1 : A r0 (⟨m - 1, by omega⟩ : Fin m).castSucc <;>
        cases h2 : A (⟨r0.val, hlt⟩ : Fin n).succ (⟨m - 1, by omega⟩ : Fin m).castSucc <;>
        cases h3 : A (⟨r0.val, hlt⟩ : Fin n).succ (⟨m - 1, by omega⟩ : Fin m).succ <;> simp_all
    · refine ⟨(⟨r0.val - 1, by omega⟩ : Fin n).castSucc, fun c => ?_⟩
      by_cases hc : c.val < m
      · have hs := hA ⟨r0.val - 1, by omega⟩ ⟨c.val, hc⟩
        unfold subblockSum at hs
        have ha := halt ⟨c.val, hc⟩
        have hre : (⟨r0.val - 1, by omega⟩ : Fin n).succ = r0 := by ext; simp; omega
        rw [hre] at hs
        cases h1 : A r0 (⟨c.val, hc⟩ : Fin m).castSucc <;>
        cases h2 : A (⟨r0.val - 1, by omega⟩ : Fin n).castSucc (⟨c.val, hc⟩ : Fin m).castSucc <;>
        cases h3 : A (⟨r0.val - 1, by omega⟩ : Fin n).castSucc (⟨c.val, hc⟩ : Fin m).succ <;> simp_all
      · have hs := hA ⟨r0.val - 1, by omega⟩ ⟨m - 1, by omega⟩
        unfold subblockSum at hs
        have ha := halt ⟨m - 1, by omega⟩
        have hre : (⟨r0.val - 1, by omega⟩ : Fin n).succ = r0 := by ext; simp; omega
        have hce : (⟨m - 1, by omega⟩ : Fin m).succ = c := by ext; simp; omega
        rw [hre] at hs
        cases h1 : A r0 (⟨m - 1, by omega⟩ : Fin m).castSucc <;>
        cases h2 : A (⟨r0.val - 1, by omega⟩ : Fin n).castSucc (⟨m - 1, by omega⟩ : Fin m).castSucc <;>
        cases h3 : A (⟨r0.val - 1, by omega⟩ : Fin n).castSucc (⟨m - 1, by omega⟩ : Fin m).succ <;> simp_all
  · -- Row r0 does NOT alternate: since no two adjacent entries in row r0 are both true,
    -- there is a pair (j, j+1) of consecutive falses in row r0, AND there is a true in row r0 (at c0).
    -- Moving from c0 toward that pair, we find a true adjacent to TWO consecutive falses in row r0!
    -- Actually simpler: there exists a column c_zero in row r0 with A r0 c_zero = false
    -- AND the column c_zero is ALL false!
    -- Wait: let's prove directly that there is a pair (c_t, c_z) with |c_t - c_z| = 1,
    -- A r0 c_t = true, A r0 c_z = false, AND the other side of c_z (c_o with |c_o - c_z| = 1, c_o ≠ c_t)
    -- ALSO has A r0 c_o = false!
    have hex_triple : ∃ (c_z : Fin (m + 1)) (c_t c_o : Fin (m + 1)),
        A r0 c_t = true ∧ A r0 c_z = false ∧ A r0 c_o = false ∧
        ((c_t.val + 1 = c_z.val ∧ c_z.val + 1 = c_o.val) ∨
         (c_o.val + 1 = c_z.val ∧ c_z.val + 1 = c_t.val)) := by
      -- Since ¬ halt, there exists j with A r0 j.castSucc = A r0 j.succ.
      -- Both must be false (by S1_nbr hn hm A hA, they can't both be true).
      simp only [not_forall] at halt
      rcases halt with ⟨j1, hj1⟩
      have hff : A r0 j1.castSucc = false ∧ A r0 j1.succ = false := by
        cases h1 : A r0 j1.castSucc <;> cases h2 : A r0 j1.succ
        · exact ⟨rfl, rfl⟩
        · exfalso; exact hj1 (by simp [h1, h2])
        · exfalso; exact hj1 (by simp [h1, h2])
        · exfalso
          have := S1_nbr hn hm A hA r0 r0 j1.castSucc j1.succ h1 (by omega) (by simp; omega)
            (Or.inr (by intro h; have := congr_arg Fin.val h; simp at this))
          simp_all
      -- Now we have A r0 c0 = true and two adjacent falses at j1.val, j1.val + 1!
      -- Either c0.val < j1.val (scan right from c0 to first pair of falses) or j1.val + 1 < c0.val (scan left)!
      have hne1 : c0.val ≠ j1.val := by
        intro h; have : c0 = j1.castSucc := by ext; exact h
        rw [this] at ht0; rw [ht0] at hff; cases hff.1
      have hne2 : c0.val ≠ j1.val + 1 := by
        intro h; have : c0 = j1.succ := by ext; exact h
        rw [this] at ht0; rw [ht0] at hff; cases hff.2
      by_cases hlt : c0.val < j1.val
      · -- Find the largest t < j1.val with A r0 ⟨t, _⟩ = true (exists since c0 works)
        let S_t := Finset.univ.filter (fun c : Fin (m + 1) => c.val < j1.val ∧ A r0 c = true)
        have hneS : S_t.Nonempty := ⟨c0, by simp [S_t, hlt, ht0]⟩
        let c_t := S_t.max' hneS
        have hct_mem : c_t ∈ S_t := Finset.max'_mem S_t hneS
        simp only [S_t, Finset.mem_filter, Finset.mem_univ, true_and] at hct_mem
        have hct_max : ∀ c : Fin (m + 1), c.val < j1.val → A r0 c = true → c ≤ c_t :=
          fun c h1 h2 => Finset.le_max' S_t c (by simp [S_t, h1, h2])
        refine ⟨⟨c_t.val + 1, by omega⟩, c_t, ⟨c_t.val + 2, by omega⟩, hct_mem.2, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
        · exact S1_nbr hn hm A hA r0 r0 c_t ⟨c_t.val + 1, by omega⟩ hct_mem.2 (by omega) (by simp; omega)
            (Or.inr (by intro h; have := congr_arg Fin.val h; simp at this))
        · by_cases heq : c_t.val + 2 = j1.val
          · have : (⟨c_t.val + 2, by omega⟩ : Fin (m + 1)) = j1.castSucc := by ext; exact heq
            rw [this]; exact hff.1
          · by_cases heq2 : c_t.val + 2 = j1.val + 1
            · have : (⟨c_t.val + 2, by omega⟩ : Fin (m + 1)) = j1.succ := by ext; exact heq2
              rw [this]; exact hff.2
            · cases hval : A r0 ⟨c_t.val + 2, by omega⟩
              · rfl
              · exfalso
                have hle := hct_max ⟨c_t.val + 2, by omega⟩ (by simp; omega) hval
                have : c_t.val + 2 ≤ c_t.val := hle
                omega
      · -- c0.val > j1.val + 1: find the smallest t > j1.val + 1 with A r0 ⟨t, _⟩ = true
        let S_t := Finset.univ.filter (fun c : Fin (m + 1) => j1.val + 1 < c.val ∧ A r0 c = true)
        have hneS : S_t.Nonempty := ⟨c0, by simp [S_t, ht0]; omega⟩
        let c_t := S_t.min' hneS
        have hct_mem : c_t ∈ S_t := Finset.min'_mem S_t hneS
        simp only [S_t, Finset.mem_filter, Finset.mem_univ, true_and] at hct_mem
        have hct_min : ∀ c : Fin (m + 1), j1.val + 1 < c.val → A r0 c = true → c_t ≤ c :=
          fun c h1 h2 => Finset.min'_le S_t c (by simp [S_t, h1, h2])
        refine ⟨⟨c_t.val - 1, by omega⟩, c_t, ⟨c_t.val - 2, by omega⟩, hct_mem.2, ?_, ?_, Or.inr ⟨by simp; omega, by simp; omega⟩⟩
        · exact S1_nbr hn hm A hA r0 r0 c_t ⟨c_t.val - 1, by omega⟩ hct_mem.2 (by omega) (by simp; omega)
            (Or.inr (by intro h; have := congr_arg Fin.val h; simp at this; omega))
        · by_cases heq : c_t.val - 2 = j1.val + 1
          · have : (⟨c_t.val - 2, by omega⟩ : Fin (m + 1)) = j1.succ := by ext; exact heq
            rw [this]; exact hff.2
          · by_cases heq2 : c_t.val - 2 = j1.val
            · have : (⟨c_t.val - 2, by omega⟩ : Fin (m + 1)) = j1.castSucc := by ext; exact heq2
              rw [this]; exact hff.1
            · cases hval : A r0 ⟨c_t.val - 2, by omega⟩
              · rfl
              · exfalso
                have hle := hct_min ⟨c_t.val - 2, by omega⟩ (by simp; omega) hval
                have : c_t.val ≤ c_t.val - 2 := hle
                omega
    -- NOW: column c_z is ALL false!!
    -- Why? In every row r, either A r c_t = true or A r c_o = true (Wait: induction up and down from r0:
    -- at r0, A r0 c_t = true and A r0 c_z = false and A r0 c_o = false;
    -- in adjacent row r0 ± 1, both c_z and c_t are false by S1_nbr hn hm A hA, so in the 2x2 block {r0, r0±1} × {c_z, c_o},
    -- A (r0±1) c_o MUST be true!! Then swap roles of c_t and c_o!!)
    rcases hex_triple with ⟨c_z, c_t, c_o, ht, hz, ho, hadj⟩
    right
    refine ⟨c_z, ?_⟩
    -- Prove by induction up and down from r0 that at distance d:
    -- (A r c_z = false) ∧ (if d % 2 = 0 then A r c_t = true ∧ A r c_o = false else A r c_t = false ∧ A r c_o = true)
    have hstep_row : ∀ (r1 r2 : Fin (n + 1)),
        (r1.val + 1 = r2.val ∨ r2.val + 1 = r1.val) →
        ∀ (ca cb : Fin (m + 1)),
        ((ca.val + 1 = c_z.val ∧ c_z.val + 1 = cb.val) ∨
         (cb.val + 1 = c_z.val ∧ c_z.val + 1 = ca.val)) →
        A r1 ca = true → A r1 c_z = false → A r1 cb = false →
        A r2 ca = false ∧ A r2 c_z = false ∧ A r2 cb = true := by
      intro r1 r2 hr ca cb hcab h1a h1z h1b
      have h2a : A r2 ca = false := S1_nbr hn hm A hA r1 r2 ca ca h1a (by omega) (by omega)
        (Or.inl (by intro h; have := congr_arg Fin.val h; omega))
      have h2z : A r2 c_z = false := S1_nbr hn hm A hA r1 r2 ca c_z h1a (by omega) (by omega)
        (Or.inl (by intro h; have := congr_arg Fin.val h; omega))
      refine ⟨h2a, h2z, ?_⟩
      -- Look at the 2x2 block with rows {r1, r2} and cols {c_z, cb}
      let i : Fin n := ⟨min r1.val r2.val, by omega⟩
      let j : Fin m := ⟨min c_z.val cb.val, by omega⟩
      have hs := hA i j
      unfold subblockSum at hs
      have hrm : (r1 = i.castSucc ∧ r2 = i.succ) ∨ (r2 = i.castSucc ∧ r1 = i.succ) := by
        rcases hr with h | h
        · left; constructor <;> ext <;> simp [i] <;> omega
        · right; constructor <;> ext <;> simp [i] <;> omega
      have hcm : (c_z = j.castSucc ∧ cb = j.succ) ∨ (cb = j.castSucc ∧ c_z = j.succ) := by
        rcases hcab with ⟨_, h⟩ | ⟨h, _⟩
        · left; constructor <;> ext <;> simp [j] <;> omega
        · right; constructor <;> ext <;> simp [j] <;> omega
      rcases hrm with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ <;> rcases hcm with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩ <;>
      · simp only [hr1, hr2, hc1, hc2] at h1z h1b h2z ⊢
        rw [h1z, h1b, h2z] at hs
        cases h : A _ _ <;> simp_all
    have hup : ∀ d : ℕ, (hd : r0.val + d ≤ n) →
        A ⟨r0.val + d, by omega⟩ c_z = false ∧
        (d % 2 = 0 → A ⟨r0.val + d, by omega⟩ c_t = true ∧ A ⟨r0.val + d, by omega⟩ c_o = false) ∧
        (d % 2 = 1 → A ⟨r0.val + d, by omega⟩ c_o = true ∧ A ⟨r0.val + d, by omega⟩ c_t = false) := by
      intro d
      induction d with
      | zero =>
        intro _
        exact ⟨by simpa using hz, fun _ => ⟨by simpa using ht, by simpa using ho⟩, fun h => by omega⟩
      | succ d ih =>
        intro hd
        have ⟨ihz, ihe, iho⟩ := ih (by omega)
        have hstep_adj : (⟨r0.val + d, by omega⟩ : Fin (n + 1)).val + 1 =
            (⟨r0.val + (d + 1), by omega⟩ : Fin (n + 1)).val := by simp; omega
        by_cases hpar : d % 2 = 0
        · have ⟨h1, h2⟩ := ihe hpar
          have hst := hstep_row ⟨r0.val + d, by omega⟩ ⟨r0.val + (d + 1), by omega⟩ (Or.inl hstep_adj)
            c_t c_o hadj h1 ihz h2
          exact ⟨hst.2.1, fun h => by omega, fun _ => ⟨hst.2.2, hst.1⟩⟩
        · have ⟨h1, h2⟩ := iho (by omega)
          have hst := hstep_row ⟨r0.val + d, by omega⟩ ⟨r0.val + (d + 1), by omega⟩ (Or.inl hstep_adj)
            c_o c_t hadj.symm h1 ihz h2
          exact ⟨hst.2.1, fun _ => ⟨hst.2.2, hst.1⟩, fun h => by omega⟩
    have hdown : ∀ d : ℕ, (hd : d ≤ r0.val) →
        A ⟨r0.val - d, by omega⟩ c_z = false ∧
        (d % 2 = 0 → A ⟨r0.val - d, by omega⟩ c_t = true ∧ A ⟨r0.val - d, by omega⟩ c_o = false) ∧
        (d % 2 = 1 → A ⟨r0.val - d, by omega⟩ c_o = true ∧ A ⟨r0.val - d, by omega⟩ c_t = false) := by
      intro d
      induction d with
      | zero =>
        intro _
        exact ⟨by simpa using hz, fun _ => ⟨by simpa using ht, by simpa using ho⟩, fun h => by omega⟩
      | succ d ih =>
        intro hd
        have ⟨ihz, ihe, iho⟩ := ih (by omega)
        have hstep_adj : (⟨r0.val - (d + 1), by omega⟩ : Fin (n + 1)).val + 1 =
            (⟨r0.val - d, by omega⟩ : Fin (n + 1)).val := by simp; omega
        by_cases hpar : d % 2 = 0
        · have ⟨h1, h2⟩ := ihe hpar
          have hst := hstep_row ⟨r0.val - d, by omega⟩ ⟨r0.val - (d + 1), by omega⟩ (Or.inr hstep_adj)
            c_t c_o hadj h1 ihz h2
          exact ⟨hst.2.1, fun h => by omega, fun _ => ⟨hst.2.2, hst.1⟩⟩
        · have ⟨h1, h2⟩ := iho (by omega)
          have hst := hstep_row ⟨r0.val - d, by omega⟩ ⟨r0.val - (d + 1), by omega⟩ (Or.inr hstep_adj)
            c_o c_t hadj.symm h1 ihz h2
          exact ⟨hst.2.1, fun _ => ⟨hst.2.2, hst.1⟩, fun h => by omega⟩
    intro r
    by_cases hle : r0.val ≤ r.val
    · have := (hup (r.val - r0.val) (by omega)).1
      have heq : (⟨r0.val + (r.val - r0.val), by omega⟩ : Fin (n + 1)) = r := by ext; simp; omega
      rw [heq] at this; exact this
    · have := (hdown (r0.val - r.val) (by omega)).1
      have heq : (⟨r0.val - (r0.val - r.val), by omega⟩ : Fin (n + 1)) = r := by ext; simp; omega
      rw [heq] at this; exact this

-- Therefore S 1 = (rowStripe 0 ∪ rowStripe 1) ∪ (colStripe 0 ∪ colStripe 1)!
private lemma S1_iff {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (A : Fin (n + 1) → Fin (m + 1) → Bool) :
    hasConstSum 1 A ↔ (rowStripe 0 A ∨ rowStripe 1 A) ∨ (colStripe 0 A ∨ colStripe 1 A) := by
  constructor
  · intro hA
    rcases S1_exists_zero_row_or_col hn hm A hA with ⟨r0, hz⟩ | ⟨c0, hz⟩
    · left
      have h := S1_of_zero_row hm A hA r0 hz
      by_cases hp : r0.val % 2 = 0
      · right; rw [hp] at h; exact h
      · left; have hp1 : r0.val % 2 = 1 := by omega
        rw [hp1] at h; exact h
    · right
      have h := S1_of_zero_col hn A hA c0 hz
      by_cases hp : c0.val % 2 = 0
      · right; rw [hp] at h; exact h
      · left; have hp1 : c0.val % 2 = 1 := by omega
        rw [hp1] at h; exact h
  · rintro ((⟨h0, h1⟩ | ⟨h0, h1⟩) | (⟨h0, h1⟩ | ⟨h0, h1⟩)) i j
    · unfold subblockSum
      by_cases hp : i.val % 2 = 0
      · have hodd : i.succ.val % 2 ≠ 0 := by simp; omega
        rw [h0 i.succ j.castSucc hodd, h0 i.succ j.succ hodd, h1 i.castSucc j hp]
        cases A i.castSucc j.castSucc <;> decide
      · have heven : i.succ.val % 2 = 0 := by simp; omega
        rw [h0 i.castSucc j.castSucc hp, h0 i.castSucc j.succ hp, h1 i.succ j heven]
        cases A i.succ j.castSucc <;> decide
    · unfold subblockSum
      by_cases hp : i.val % 2 = 1
      · have heven : i.succ.val % 2 ≠ 1 := by simp; omega
        rw [h0 i.succ j.castSucc heven, h0 i.succ j.succ heven, h1 i.castSucc j hp]
        cases A i.castSucc j.castSucc <;> decide
      · have hodd : i.succ.val % 2 = 1 := by simp; omega
        rw [h0 i.castSucc j.castSucc hp, h0 i.castSucc j.succ hp, h1 i.succ j hodd]
        cases A i.succ j.castSucc <;> decide
    · unfold subblockSum
      by_cases hp : j.val % 2 = 0
      · have hodd : j.succ.val % 2 ≠ 0 := by simp; omega
        rw [h0 i.castSucc j.succ hodd, h0 i.succ j.succ hodd, h1 i j.castSucc hp]
        cases A i.castSucc j.castSucc <;> decide
      · have heven : j.succ.val % 2 = 0 := by simp; omega
        rw [h0 i.castSucc j.castSucc hp, h0 i.succ j.castSucc hp, h1 i j.succ heven]
        cases A i.castSucc j.succ <;> decide
    · unfold subblockSum
      by_cases hp : j.val % 2 = 1
      · have heven : j.succ.val % 2 ≠ 1 := by simp; omega
        rw [h0 i.castSucc j.succ heven, h0 i.succ j.succ heven, h1 i j.castSucc hp]
        cases A i.castSucc j.castSucc <;> decide
      · have hodd : j.succ.val % 2 = 1 := by simp; omega
        rw [h0 i.castSucc j.castSucc hp, h0 i.succ j.castSucc hp, h1 i j.succ hodd]
        cases A i.castSucc j.succ <;> decide

-- Count rowStripe p: bijection with ({r : Fin (n+1) // r.val % 2 = p} → Bool)
private lemma card_rowStripe {n m : ℕ} (p : ℕ) (_hp : p < 2) :
    (Finset.univ.filter (rowStripe (n := n) (m := m) p)).card =
      2 ^ (Finset.univ.filter (fun r : Fin (n + 1) => r.val % 2 = p)).card := by
  let R := Finset.univ.filter (fun r : Fin (n + 1) => r.val % 2 = p)
  have hbij : (Finset.univ.filter (rowStripe (n := n) (m := m) p)).card =
      Fintype.card ({r : Fin (n + 1) // r ∈ R} → Bool) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun A _ r => A r.1 0) (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro A hA B hB h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA hB
      ext r c
      by_cases hr : r.val % 2 = p
      · induction c using Fin.induction with
        | zero => exact congr_fun h ⟨r, by simp [R, hr]⟩
        | succ j ih => rw [hA.2 r j hr, hB.2 r j hr, ih]
      · rw [hA.1 r c hr, hB.1 r c hr]
    · intro f _
      refine ⟨fun r c => if hr : r.val % 2 = p then xor (f ⟨r, by simp [R, hr]⟩) (decide (c.val % 2 = 1)) else false, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun r c hr => by simp [hr], fun r j hr => ?_⟩
        simp only [hr, ↓reduceDIte, Fin.val_succ, Fin.val_castSucc]
        have : (j.val + 1) % 2 = 1 ↔ ¬ (j.val % 2 = 1) := by omega
        cases f ⟨r, by simp [R, hr]⟩ <;> by_cases hj : j.val % 2 = 1 <;> simp_all
      · ext ⟨r, hr⟩
        have hr' : r.val % 2 = p := by simp [R] at hr; exact hr
        simp [hr']
  rw [hbij, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

private lemma card_colStripe {n m : ℕ} (p : ℕ) (hp : p < 2) :
    (Finset.univ.filter (colStripe (n := n) (m := m) p)).card =
      2 ^ (Finset.univ.filter (fun c : Fin (m + 1) => c.val % 2 = p)).card := by
  have heq : (Finset.univ.filter (colStripe (n := n) (m := m) p)).card =
      (Finset.univ.filter (rowStripe (n := m) (m := n) p)).card := by
    refine Finset.card_bij (fun A _ => transpose A) ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
      exact ⟨fun c r h => hA.1 r c h, fun c i h => hA.2 i c h⟩
    · intro A _ B _ h; ext r c; exact congr_fun (congr_fun h c) r
    · intro B hB
      refine ⟨transpose B, ?_, by ext r c; rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
      exact ⟨fun r c h => hB.1 c r h, fun i c h => hB.2 c i h⟩
  rw [heq, card_rowStripe p hp]

private lemma card_mod2_eq {k : ℕ} :
    (Finset.univ.filter (fun r : Fin (k + 1) => r.val % 2 = 0)).card = (k + 2) / 2 ∧
    (Finset.univ.filter (fun r : Fin (k + 1) => r.val % 2 = 1)).card = (k + 1) / 2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hsplit : ∀ p : ℕ, (Finset.univ.filter (fun r : Fin (k + 2) => r.val % 2 = p)).card =
        (Finset.univ.filter (fun r : Fin (k + 1) => r.val % 2 = p)).card +
        (if (k + 1) % 2 = p then 1 else 0) := by
      intro p
      have hcard : (Finset.univ.filter (fun r : Fin (k + 2) => r.val % 2 = p)).card =
          ((Finset.univ.filter (fun r : Fin (k + 1) => r.val % 2 = p)).map
            ⟨Fin.castSucc, Fin.castSucc_injective _⟩ ∪
          (if (k + 1) % 2 = p then {Fin.last (k + 1)} else ∅)).card := by
        congr 1
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
          Finset.mem_map, Function.Embedding.coeFn_mk]
        split_ifs with hp
        · simp only [Finset.mem_singleton]
          constructor
          · intro hr
            by_cases hlast : r = Fin.last (k + 1)
            · exact Or.inr hlast
            · left
              refine ⟨⟨r.val, by have := r.isLt; have : r.val ≠ k + 1 := fun h => hlast (Fin.ext h); omega⟩, hr, by ext; rfl⟩
          · rintro (⟨r', hr', rfl⟩ | rfl)
            · exact hr'
            · exact hp
        · simp only [Finset.notMem_empty, or_false]
          constructor
          · intro hr
            have hne : r.val ≠ k + 1 := by intro h; rw [h] at hr; exact hp hr
            exact ⟨⟨r.val, by have := r.isLt; omega⟩, hr, by ext; rfl⟩
          · rintro ⟨r', hr', rfl⟩; exact hr'
      rw [hcard, Finset.card_union_of_disjoint, Finset.card_map]
      · split_ifs <;> simp
      · split_ifs
        · simp only [Finset.disjoint_singleton_right, Finset.mem_map, Finset.mem_filter,
            Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, not_exists, not_and]
          intro x _ hx
          have := congr_arg Fin.val hx
          simp at this
          omega
        · exact Finset.disjoint_empty_right _
    rw [hsplit 0, hsplit 1, ih.1, ih.2]
    constructor <;> split_ifs <;> omega

private lemma card_rowStripe_inter_colStripe {n m : ℕ} (hm : 1 ≤ m) (pr pc : ℕ) (hpr : pr < 2) (hpc : pc < 2) :
    (Finset.univ.filter (rowStripe (n := n) (m := m) pr) ∩
      Finset.univ.filter (colStripe (n := n) (m := m) pc)).card = 1 := by
  let B : Fin (n + 1) → Fin (m + 1) → Bool :=
    fun r c => decide (r.val % 2 = pr ∧ c.val % 2 = pc)
  have hset : Finset.univ.filter (rowStripe (n := n) (m := m) pr) ∩
      Finset.univ.filter (colStripe (n := n) (m := m) pc) = {B} := by
    ext A
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hr0, hr1⟩, ⟨hc0, hc1⟩⟩
      ext r c
      by_cases h1 : r.val % 2 = pr
      · by_cases h2 : c.val % 2 = pc
        · simp only [B, h1, h2, and_self, decide_true]
          -- If A r c = false, then since row r alternates, adjacent col (with ≠ pc) would be true, contradicting hc0!
          cases hval : A r c
          · exfalso
            by_cases hlt : c.val < m
            · have ha := hr1 r ⟨c.val, hlt⟩ h1
              have hne : (⟨c.val, hlt⟩ : Fin m).succ.val % 2 ≠ pc := by simp; omega
              have hf := hc0 r (⟨c.val, hlt⟩ : Fin m).succ hne
              have hce : (⟨c.val, hlt⟩ : Fin m).castSucc = c := by ext; rfl
              rw [hce, hval] at ha
              simp_all
            · have ha := hr1 r ⟨m - 1, by omega⟩ h1
              have hne : (⟨m - 1, by omega⟩ : Fin m).castSucc.val % 2 ≠ pc := by simp; omega
              have hf := hc0 r (⟨m - 1, by omega⟩ : Fin m).castSucc hne
              have hce : (⟨m - 1, by omega⟩ : Fin m).succ = c := by ext; simp; omega
              rw [hce, hval] at ha
              rw [hf] at ha
              cases ha
          · rfl
        · simp only [B, h2, and_false, decide_false]
          exact hc0 r c h2
      · simp only [B, h1, false_and, decide_false]
        exact hr0 r c h1
    · rintro rfl
      refine ⟨⟨fun r c hr => by simp [B, hr], fun r j hr => ?_⟩,
              ⟨fun r c hc => by simp [B, hc], fun i c hc => ?_⟩⟩
      · simp only [B, hr, true_and, Fin.val_succ, Fin.val_castSucc]
        have : (j.val + 1) % 2 = pc ↔ ¬ (j.val % 2 = pc) := by omega
        by_cases h : j.val % 2 = pc <;> simp_all
      · simp only [B, hc, and_true, Fin.val_succ, Fin.val_castSucc]
        have : (i.val + 1) % 2 = pr ↔ ¬ (i.val % 2 = pr) := by omega
        by_cases h : i.val % 2 = pr <;> simp_all
  rw [hset, Finset.card_singleton]

private lemma card_S_one {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (S n m 1).card = 2 ^ ((n + 2) / 2) + 2 ^ ((n + 1) / 2) +
      2 ^ ((m + 2) / 2) + 2 ^ ((m + 1) / 2) - 4 := by
  let R0 := Finset.univ.filter (rowStripe (n := n) (m := m) 0)
  let R1 := Finset.univ.filter (rowStripe (n := n) (m := m) 1)
  let C0 := Finset.univ.filter (colStripe (n := n) (m := m) 0)
  let C1 := Finset.univ.filter (colStripe (n := n) (m := m) 1)
  have hunion : S n m 1 = (R0 ∪ R1) ∪ (C0 ∪ C1) := by
    ext A
    simp only [S, R0, R1, C0, C1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact S1_iff hn hm A
  have hdisjR : Disjoint R0 R1 := by
    rw [Finset.disjoint_left]
    intro A h0 h1
    simp only [R0, R1, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
    have ha := h0.2 0 ⟨0, by omega⟩ (by simp)
    have hf0 := h1.1 0 (⟨0, by omega⟩ : Fin m).castSucc (by simp)
    have hf1 := h1.1 0 (⟨0, by omega⟩ : Fin m).succ (by simp)
    rw [hf0, hf1] at ha
    simp at ha
  have hdisjC : Disjoint C0 C1 := by
    rw [Finset.disjoint_left]
    intro A h0 h1
    simp only [C0, C1, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h1
    have ha := h0.2 ⟨0, by omega⟩ 0 (by simp)
    have hf0 := h1.1 (⟨0, by omega⟩ : Fin n).castSucc 0 (by simp)
    have hf1 := h1.1 (⟨0, by omega⟩ : Fin n).succ 0 (by simp)
    rw [hf0, hf1] at ha
    simp at ha
  have hR : (R0 ∪ R1).card = 2 ^ ((n + 2) / 2) + 2 ^ ((n + 1) / 2) := by
    rw [Finset.card_union_of_disjoint hdisjR, card_rowStripe 0 (by omega), card_rowStripe 1 (by omega),
      (card_mod2_eq (k := n)).1, (card_mod2_eq (k := n)).2]
  have hC : (C0 ∪ C1).card = 2 ^ ((m + 2) / 2) + 2 ^ ((m + 1) / 2) := by
    rw [Finset.card_union_of_disjoint hdisjC, card_colStripe 0 (by omega), card_colStripe 1 (by omega),
      (card_mod2_eq (k := m)).1, (card_mod2_eq (k := m)).2]
  have hInter : ((R0 ∪ R1) ∩ (C0 ∪ C1)).card = 4 := by
    have hdist : (R0 ∪ R1) ∩ (C0 ∪ C1) = ((R0 ∩ C0) ∪ (R0 ∩ C1)) ∪ ((R1 ∩ C0) ∪ (R1 ∩ C1)) := by
      ext A; simp only [Finset.mem_inter, Finset.mem_union]; tauto
    rw [hdist]
    have hd1 : Disjoint (R0 ∩ C0) (R0 ∩ C1) :=
      Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisjC
    have hd2 : Disjoint (R1 ∩ C0) (R1 ∩ C1) :=
      Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hdisjC
    have hd3 : Disjoint ((R0 ∩ C0) ∪ (R0 ∩ C1)) ((R1 ∩ C0) ∪ (R1 ∩ C1)) := by
      refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
      · refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
        · exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisjR
        · exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisjR
      · refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
        · exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisjR
        · exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisjR
    rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd1,
      Finset.card_union_of_disjoint hd2,
      card_rowStripe_inter_colStripe hm 0 0 (by omega) (by omega),
      card_rowStripe_inter_colStripe hm 0 1 (by omega) (by omega),
      card_rowStripe_inter_colStripe hm 1 0 (by omega) (by omega),
      card_rowStripe_inter_colStripe hm 1 1 (by omega) (by omega)]
  have hcu := Finset.card_union_add_card_inter (R0 ∪ R1) (C0 ∪ C1)
  rw [← hunion, hR, hC, hInter] at hcu
  omega

-- Main parametric theorem: total number of valid (n+1) × (m+1) binary arrays
theorem card_valid {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Fintype.card {A : Fin (n + 1) → Fin (m + 1) → Bool // isValid n m A} =
      2 ^ (n + 1) + 2 ^ (m + 1) +
      2 * (2 ^ ((n + 2) / 2) + 2 ^ ((n + 1) / 2) + 2 ^ ((m + 2) / 2) + 2 ^ ((m + 1) / 2)) - 8 := by
  rw [Fintype.card_subtype]
  have hunion : Finset.univ.filter (isValid n m) =
      (Finset.range 5).biUnion (S n m) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, S, isValid]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_, hs⟩
      have hle := subblockSum_le_four A ⟨0, by omega⟩ ⟨0, by omega⟩
      rw [hs ⟨0, by omega⟩ ⟨0, by omega⟩] at hle
      omega
    · rintro ⟨s, _, hs⟩; exact ⟨s, hs⟩
  rw [hunion, Finset.card_biUnion]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [card_S_zero hn hm, card_S_four hn hm, card_S_three, card_S_two, card_S_one hn hm]
    have h2n : 2 ≤ 2 ^ (n + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h2m : 2 ≤ 2 ^ (m + 1) := by
      have : 2 ^ 1 ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h1n : 1 ≤ 2 ^ ((n + 2) / 2) := Nat.one_le_pow _ _ (by omega)
    have h1n' : 1 ≤ 2 ^ ((n + 1) / 2) := Nat.one_le_pow _ _ (by omega)
    have h1m : 1 ≤ 2 ^ ((m + 2) / 2) := Nat.one_le_pow _ _ (by omega)
    have h1m' : 1 ≤ 2 ^ ((m + 1) / 2) := Nat.one_le_pow _ _ (by omega)
    omega
  · intro s1 _ s2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro A h1 h2
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    have e1 := h1 ⟨0, by omega⟩ ⟨0, by omega⟩
    have e2 := h2 ⟨0, by omega⟩ ⟨0, by omega⟩
    exact hne (e1.symm.trans e2)

end GridEqual2x2

open scoped Classical in
theorem div4_formula {n m C : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hC : 2 ^ (m + 1) + 2 * (2 ^ ((m + 2) / 2) + 2 ^ ((m + 1) / 2)) - 8 = 4 * C) :
    (Even n → Nat.card {A : Fin (n + 1) → Fin (m + 1) → Bool // GridEqual2x2.isValid n m A} / 4 =
      3 * 2 ^ (n / 2 - 1) + 2 ^ (n - 1) + C) ∧
    (Odd n → Nat.card {A : Fin (n + 1) → Fin (m + 1) → Bool // GridEqual2x2.isValid n m A} / 4 =
      2 ^ (n - 1) + 2 ^ ((n + 1) / 2) + C) := by
  have hcard : Nat.card {A : Fin (n + 1) → Fin (m + 1) → Bool // GridEqual2x2.isValid n m A} =
      2 ^ (n + 1) + 2 * (2 ^ ((n + 2) / 2) + 2 ^ ((n + 1) / 2)) + 4 * C := by
    rw [Nat.card_eq_fintype_card, GridEqual2x2.card_valid hn hm]
    have h1m : 8 ≤ 2 ^ (m + 1) + 2 * (2 ^ ((m + 2) / 2) + 2 ^ ((m + 1) / 2)) := by
      have h2m : 4 ≤ 2 ^ (m + 1) := by
        have := Nat.pow_le_pow_right (show 1 ≤ 2 by omega) (show 2 ≤ m + 1 by omega)
        simpa using this
      have h2m1 : 1 ≤ 2 ^ ((m + 2) / 2) := Nat.one_le_pow _ _ (by omega)
      have h2m2 : 1 ≤ 2 ^ ((m + 1) / 2) := Nat.one_le_pow _ _ (by omega)
      omega
    have hC' : 2 ^ (m + 1) + 2 * (2 ^ ((m + 2) / 2) + 2 ^ ((m + 1) / 2)) = 4 * C + 8 := by omega
    have hsum : 2 ^ (n + 1) + 2 ^ (m + 1) +
        2 * (2 ^ ((n + 2) / 2) + 2 ^ ((n + 1) / 2) + 2 ^ ((m + 2) / 2) + 2 ^ ((m + 1) / 2)) =
        (2 ^ (n + 1) + 2 * (2 ^ ((n + 2) / 2) + 2 ^ ((n + 1) / 2)) + 4 * C) + 8 := by linarith
    rw [hsum, Nat.add_sub_cancel]
  constructor
  · rintro ⟨t, rfl⟩
    have ht : 1 ≤ t := by omega
    have hpow1 : 2 ^ (t + t + 1) = 4 * 2 ^ (t + t - 1) := by
      have : t + t + 1 = (t + t - 1) + 2 := by omega
      rw [this, pow_add]; ring
    have hpow2 : 2 ^ ((t + t + 2) / 2) = 4 * 2 ^ (t - 1) := by
      have : (t + t + 2) / 2 = (t - 1) + 2 := by omega
      rw [this, pow_add]; ring
    have hpow3 : 2 ^ ((t + t + 1) / 2) = 2 * 2 ^ (t - 1) := by
      have : (t + t + 1) / 2 = (t - 1) + 1 := by omega
      rw [this, pow_add]; ring
    have hdiv : (t + t) / 2 - 1 = t - 1 := by omega
    rw [hcard, hpow1, hpow2, hpow3, hdiv]
    omega
  · rintro ⟨t, rfl⟩
    have hpow1 : 2 ^ (2 * t + 1 + 1) = 4 * 2 ^ (2 * t) := by
      have : 2 * t + 1 + 1 = 2 * t + 2 := by omega
      rw [this, pow_add]; ring
    have hpow2 : (2 * t + 1 + 2) / 2 = (2 * t + 1 + 1) / 2 := by omega
    have hsub : 2 * t + 1 - 1 = 2 * t := by omega
    rw [hcard, hpow1, hpow2, hsub]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a183984.main := by
  have heq : ∀ n : ℕ, OMA.S_oeis_a183984.a n =
      Nat.card {A : Fin (n + 1) → Fin (7 + 1) → Bool // GridEqual2x2.isValid n 7 A} / 4 := by
    intro n; rfl
  refine ⟨fun n hn he => ?_, fun n hn ho => ?_⟩
  · rw [heq]
    exact (div4_formula (n := n) (m := 7) (C := 78) hn (by omega) (by decide)).1 he
  · rw [heq]
    exact (div4_formula (n := n) (m := 7) (C := 78) hn (by omega) (by decide)).2 ho
