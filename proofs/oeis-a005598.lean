import OMAStatements.S_oeis_a005598

/-!
# Proof of OEIS A005598: Regions of a Farey fan

We prove that the complement of the fan lines `y + i * x = k` (`1 ≤ i ≤ n`, `1 ≤ k ≤ i`)
in the open unit square `(0, 1)²` has
`1 + ∑ j ∈ Finset.range n, (n - j) * Nat.totient (j + 1)`
connected components.

The proof proceeds in four elementary steps:
1. Sign-vector cells: each point `p ∈ fanComplement n` has a boolean sign vector
   recording which side of each fan line it lies on. Every nonempty fiber is open
   and convex (hence connected), so the connected components are in bijection with
   the nonempty sign vectors `activeSigs n`.
2. Induction step via parallel slices: passing from `n` to `n + 1` adds the `n + 1`
   parallel lines `y + (n + 1) * x = k` (`1 ≤ k ≤ n + 1`). Each cell of `fanComplement n`
   is split into `1 + (# new lines meeting it)` subcells, so the increase in regions is
   the sum over `k` of the number of cells met by the `k`-th new line.
3. Segment subdivision: each new line meets `(0, 1)²` in an open segment parameterized by
   `x ∈ ((k - 1)/(n + 1), k/(n + 1))`. Removing the finite set `interX n k` of rational
   intersection `x`-coordinates with earlier fan lines splits the segment into
   `1 + (interX n k).card` intervals corresponding bijectively to the cells it meets.
4. Farey counting and Gauss's totient sum: the union of `interX n k` over `1 ≤ k ≤ n + 1`
   is disjoint and equals the set of reduced rationals `p / q ∈ (0, 1)` with `q ≤ n` and
   `¬ (q ∣ n + 1)`. Combining its cardinality with `Nat.sum_totient (n + 1)` yields an
   increment of `∑ j ∈ Finset.range (n + 1), Nat.totient (j + 1)`.
-/

open scoped BigOperators

namespace OMA.A005598Proof

open Classical
open OMA.S_oeis_a005598

/-- Sign vector assigning each fan line `(i + 1, k + 1)` (`i < n`, `k ≤ i`) a side. -/
abbrev Sig (n : ℕ) := (i : Fin n) → (k : Fin (i.1 + 1)) → Bool

/-- Linear form `y + i * x` defining the fan lines. -/
def lineVal (i : ℕ) (p : ℝ × ℝ) : ℝ :=
  p.2 + (i : ℝ) * p.1

/-- Sign vector of a point `p` with respect to the fan lines up to `n`. -/
noncomputable def sig (n : ℕ) (p : ℝ × ℝ) : Sig n :=
  fun i k => decide (lineVal (i.1 + 1) p < ((k.1 + 1 : ℕ) : ℝ))

/-- The cell of points in `fanComplement n` having sign vector `σ`. -/
def cell (n : ℕ) (σ : Sig n) : Set (ℝ × ℝ) :=
  {p ∈ fanComplement n | sig n p = σ}

/-- The finite set of sign vectors whose cells are nonempty. -/
noncomputable def activeSigs (n : ℕ) : Finset (Sig n) :=
  Finset.univ.filter (fun σ => (cell n σ).Nonempty)

lemma mem_fanComplement_iff (n : ℕ) (p : ℝ × ℝ) :
    p ∈ fanComplement n ↔
      0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1 ∧
      ∀ (i : Fin n) (k : Fin (i.1 + 1)), lineVal (i.1 + 1) p ≠ ((k.1 + 1 : ℕ) : ℝ) := by
  constructor
  · rintro ⟨h1, h2, h3, h4, hline⟩
    refine ⟨h1, h2, h3, h4, fun i k => ?_⟩
    exact hline (i.1 + 1) (k.1 + 1) (by omega) i.2 (by omega) k.2
  · rintro ⟨h1, h2, h3, h4, hline⟩
    refine ⟨h1, h2, h3, h4, fun i k hi1 hin hk1 hki => ?_⟩
    let i' : Fin n := ⟨i - 1, by omega⟩
    have hi : i'.1 + 1 = i := by dsimp [i']; omega
    let k' : Fin (i'.1 + 1) := ⟨k - 1, by omega⟩
    have hk : k'.1 + 1 = k := by dsimp [k']; omega
    have h := hline i' k'
    simpa [lineVal, hi, hk] using h

lemma mem_cell_iff (n : ℕ) (σ : Sig n) (p : ℝ × ℝ) :
    p ∈ cell n σ ↔
      0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1 ∧
      ∀ (i : Fin n) (k : Fin (i.1 + 1)),
        if σ i k then lineVal (i.1 + 1) p < ((k.1 + 1 : ℕ) : ℝ)
        else ((k.1 + 1 : ℕ) : ℝ) < lineVal (i.1 + 1) p := by
  constructor
  · rintro ⟨hp, hsig⟩
    rw [mem_fanComplement_iff] at hp
    rcases hp with ⟨h1, h2, h3, h4, hne⟩
    refine ⟨h1, h2, h3, h4, fun i k => ?_⟩
    have heq : sig n p i k = σ i k := congrFun (congrFun hsig i) k
    unfold sig at heq
    cases hσ : σ i k
    · rw [hσ, decide_eq_false_iff_not] at heq
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact lt_of_le_of_ne (le_of_not_gt heq) (hne i k).symm
    · rw [hσ, decide_eq_true_eq] at heq
      simpa using heq
  · rintro ⟨h1, h2, h3, h4, hcond⟩
    refine ⟨?_, ?_⟩
    · rw [mem_fanComplement_iff]
      refine ⟨h1, h2, h3, h4, fun i k => ?_⟩
      have hc := hcond i k
      cases hσ : σ i k
      · rw [hσ] at hc; simp only [Bool.false_eq_true, ↓reduceIte] at hc; exact ne_of_gt hc
      · rw [hσ] at hc; simp only [↓reduceIte] at hc; exact ne_of_lt hc
    · funext i k
      unfold sig
      have hc := hcond i k
      cases hσ : σ i k
      · rw [hσ] at hc
        simp only [Bool.false_eq_true, ↓reduceIte] at hc
        rw [decide_eq_false_iff_not]
        exact not_lt_of_gt hc
      · rw [hσ] at hc
        simp only [↓reduceIte] at hc
        rw [decide_eq_true_eq]
        exact hc

lemma convex_cell (n : ℕ) (σ : Sig n) : Convex ℝ (cell n σ) := by
  intro p hp q hq a b ha hb hab
  rw [mem_cell_iff] at hp hq ⊢
  rcases hp with ⟨hp1, hp2, hp3, hp4, hp5⟩
  rcases hq with ⟨hq1, hq2, hq3, hq4, hq5⟩
  have hcomb : ∀ x y c : ℝ, x < c → y < c → a * x + b * y < c := by
    intro x y c hx hy
    have hlt : a * x + b * y < a * c + b * c := by
      rcases eq_or_lt_of_le ha with rfl | ha'
      · have hb1 : b = 1 := by linarith
        subst hb1; linarith
      · rcases eq_or_lt_of_le hb with rfl | hb'
        · have ha1 : a = 1 := by linarith
          subst ha1; linarith
        · nlinarith
    have hsum : a * c + b * c = c := by
      calc
        a * c + b * c = (a + b) * c := by ring
        _ = 1 * c := by rw [hab]
        _ = c := one_mul c
    linarith
  have hcomb' : ∀ x y c : ℝ, c < x → c < y → c < a * x + b * y := by
    intro x y c hx hy
    have := hcomb (-x) (-y) (-c) (by linarith) (by linarith)
    linarith
  refine ⟨?_, ?_, ?_, ?_, fun i k => ?_⟩
  · simpa [Prod.smul_fst, Prod.fst_add] using hcomb' p.1 q.1 0 hp1 hq1
  · simpa [Prod.smul_fst, Prod.fst_add] using hcomb p.1 q.1 1 hp2 hq2
  · simpa [Prod.smul_snd, Prod.snd_add] using hcomb' p.2 q.2 0 hp3 hq3
  · simpa [Prod.smul_snd, Prod.snd_add] using hcomb p.2 q.2 1 hp4 hq4
  · have hlin : lineVal (i.1 + 1) (a • p + b • q) =
        a * lineVal (i.1 + 1) p + b * lineVal (i.1 + 1) q := by
      simp only [lineVal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    rw [hlin]
    have hpi := hp5 i k
    have hqi := hq5 i k
    cases hσ : σ i k
    · rw [hσ] at hpi hqi; simp only [Bool.false_eq_true, ↓reduceIte] at hpi hqi ⊢
      exact hcomb' _ _ _ hpi hqi
    · rw [hσ] at hpi hqi; simp only [↓reduceIte] at hpi hqi ⊢
      exact hcomb _ _ _ hpi hqi

lemma isOpen_cell (n : ℕ) (σ : Sig n) : IsOpen (cell n σ) := by
  have heq : cell n σ =
      {p : ℝ × ℝ | 0 < p.1} ∩ {p : ℝ × ℝ | p.1 < 1} ∩
      {p : ℝ × ℝ | 0 < p.2} ∩ {p : ℝ × ℝ | p.2 < 1} ∩
      ⋂ (i : Fin n) (k : Fin (i.1 + 1)),
        {p : ℝ × ℝ | if σ i k then lineVal (i.1 + 1) p < ((k.1 + 1 : ℕ) : ℝ)
                     else ((k.1 + 1 : ℕ) : ℝ) < lineVal (i.1 + 1) p} := by
    ext p
    simp only [mem_cell_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    tauto
  rw [heq]
  have hcont : ∀ m : ℕ, Continuous (lineVal m) := fun m =>
    continuous_snd.add (continuous_const.mul continuous_fst)
  refine ((((isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_const)).inter
    (isOpen_lt continuous_const continuous_snd)).inter
    (isOpen_lt continuous_snd continuous_const)).inter ?_
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
  cases σ i k
  · exact isOpen_lt continuous_const (hcont (i.1 + 1))
  · exact isOpen_lt (hcont (i.1 + 1)) continuous_const

lemma connectedComponentIn_eq_cell (n : ℕ) {p : ℝ × ℝ} (hp : p ∈ fanComplement n) :
    connectedComponentIn (fanComplement n) p = cell n (sig n p) := by
  apply Set.Subset.antisymm
  · let U := cell n (sig n p)
    let V := ⋃ τ : {τ : Sig n // τ ≠ sig n p}, cell n τ.1
    have hU : IsOpen U := isOpen_cell n (sig n p)
    have hV : IsOpen V := isOpen_iUnion fun τ => isOpen_cell n τ.1
    have hsub : connectedComponentIn (fanComplement n) p ⊆ U ∪ V := by
      intro q hq
      have hqf : q ∈ fanComplement n := connectedComponentIn_subset (fanComplement n) p hq
      by_cases h : sig n q = sig n p
      · exact Or.inl ⟨hqf, h⟩
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨sig n q, h⟩, ⟨hqf, rfl⟩⟩)
    have hdisj : Disjoint U V := by
      rw [Set.disjoint_left]
      intro q hqU hqV
      rcases Set.mem_iUnion.mp hqV with ⟨⟨τ, hne⟩, hqτ⟩
      exact hne (hqτ.2.symm.trans hqU.2)
    have hne : (connectedComponentIn (fanComplement n) p ∩ U).Nonempty :=
      ⟨p, mem_connectedComponentIn hp, ⟨hp, rfl⟩⟩
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hU hV hdisj hsub hne
  · exact (convex_cell n (sig n p)).isPreconnected.subset_connectedComponentIn
      ⟨hp, rfl⟩ (fun _ hq => hq.1)

lemma ncard_fanRegions_eq_card_activeSigs (n : ℕ) :
    (fanRegions n).ncard = (activeSigs n).card := by
  have himg : fanRegions n = (fun σ => cell n σ) '' (activeSigs n : Set (Sig n)) := by
    ext R
    simp only [fanRegions, Set.mem_image, Finset.mem_coe, activeSigs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨sig n p, ⟨p, hp, rfl⟩, (connectedComponentIn_eq_cell n hp).symm⟩
    · rintro ⟨σ, ⟨p, hp⟩, rfl⟩
      exact ⟨p, hp.1, by rw [connectedComponentIn_eq_cell n hp.1, hp.2]⟩
  have hinj : Set.InjOn (fun σ => cell n σ) (activeSigs n : Set (Sig n)) := by
    intro σ hσ τ _ hEq
    simp only [Finset.mem_coe, activeSigs, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rcases hσ with ⟨p, hp⟩
    dsimp only at hEq
    have hp' : p ∈ cell n τ := by rwa [← hEq]
    exact hp.2.symm.trans hp'.2
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset]

lemma card_activeSigs_zero : (activeSigs 0).card = 1 := by
  have huniv : activeSigs 0 = Finset.univ := by
    ext σ
    simp only [activeSigs, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    refine ⟨((1 : ℝ) / 2, (1 : ℝ) / 2), ?_⟩
    rw [mem_cell_iff]
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, fun i => Fin.elim0 i⟩
  rw [huniv, Finset.card_univ]
  have huniq : Unique (Sig 0) :=
    ⟨⟨fun i => Fin.elim0 i⟩, fun f => funext fun i => Fin.elim0 i⟩
  exact @Fintype.card_unique (Sig 0) huniq _

/-! ### Step 2: Parallel slice decomposition from `n` to `n + 1` -/

/-- Restrict a sign vector from `n + 1` lines to the first `n` lines. -/
def restrictSig {n : ℕ} (τ : Sig (n + 1)) : Sig n :=
  fun i k => τ i.castSucc k

/-- Extend a sign vector `σ : Sig n` with a threshold `m : Fin (n + 2)` on the `(n + 1)`-st lines. -/
def extendSig {n : ℕ} (σ : Sig n) (m : Fin (n + 2)) : Sig (n + 1) :=
  Fin.snoc (α := fun i : Fin (n + 1) => Fin (i.1 + 1) → Bool) σ
    (fun k => decide (m.1 < k.1 + 1))

lemma restrictSig_extendSig {n : ℕ} (σ : Sig n) (m : Fin (n + 2)) :
    restrictSig (extendSig σ m) = σ := by
  funext i k
  simp [restrictSig, extendSig, Fin.snoc_castSucc]

lemma extendSig_last {n : ℕ} (σ : Sig n) (m : Fin (n + 2)) (k : Fin (n + 1)) :
    extendSig σ m (Fin.last n) k = decide (m.1 < k.1 + 1) := by
  simp [extendSig, Fin.snoc_last]

lemma extendSig_injective {n : ℕ} (σ : Sig n) : Function.Injective (extendSig σ) := by
  have aux : ∀ a b : Fin (n + 2), a.1 < b.1 → extendSig σ a ≠ extendSig σ b := by
    intro a b hlt h
    let k : Fin (n + 1) := ⟨a.1, by omega⟩
    have h1 := congrFun (congrFun h (Fin.last n)) k
    rw [extendSig_last, extendSig_last] at h1
    have ht : decide (a.1 < k.1 + 1) = true := by simp [k]
    have hf : decide (b.1 < k.1 + 1) = false := by
      simp only [decide_eq_false_iff_not, k]
      omega
    rw [ht, hf] at h1
    exact Bool.noConfusion h1
  intro m₁ m₂ h
  rcases lt_trichotomy m₁.1 m₂.1 with hlt | heq | hgt
  · exact absurd h (aux m₁ m₂ hlt)
  · exact Fin.ext heq
  · exact absurd h.symm (aux m₂ m₁ hgt)

/-- Band `m ∈ {0, ..., n + 1}` is hit by cell `σ` if `m < y + (n + 1) x < m + 1` on `cell n σ`. -/
def cellHits (n : ℕ) (σ : Sig n) (m : Fin (n + 2)) : Prop :=
  ∃ p ∈ cell n σ, (m.1 : ℝ) < lineVal (n + 1) p ∧ lineVal (n + 1) p < ((m.1 + 1 : ℕ) : ℝ)

/-- Line `k + 1` (`k : Fin (n + 1)`) crosses cell `σ` if `y + (n + 1) x = k + 1` on `cell n σ`. -/
def cellCrosses (n : ℕ) (σ : Sig n) (k : Fin (n + 1)) : Prop :=
  ∃ p ∈ cell n σ, lineVal (n + 1) p = ((k.1 + 1 : ℕ) : ℝ)

noncomputable def hitBands (n : ℕ) (σ : Sig n) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (cellHits n σ)

noncomputable def crossLines (n : ℕ) (σ : Sig n) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (cellCrosses n σ)

lemma extendSig_mem_activeSigs_iff {n : ℕ} (σ : Sig n) (m : Fin (n + 2)) :
    extendSig σ m ∈ activeSigs (n + 1) ↔ m ∈ hitBands n σ := by
  simp only [activeSigs, hitBands, Finset.mem_filter, Finset.mem_univ, true_and, cellHits]
  constructor
  · rintro ⟨p, hp⟩
    rw [mem_cell_iff] at hp
    rcases hp with ⟨h1, h2, h3, h4, hcond⟩
    have hpσ : p ∈ cell n σ := by
      rw [mem_cell_iff]
      refine ⟨h1, h2, h3, h4, fun i k => ?_⟩
      have hc := hcond i.castSucc k
      have hEq : extendSig σ m i.castSucc k = σ i k := by
        simpa [restrictSig] using congrFun (congrFun (restrictSig_extendSig σ m) i) k
      simpa [hEq] using hc
    refine ⟨p, hpσ, ?_, ?_⟩
    · by_cases hm0 : m.1 = 0
      · rw [hm0]; simp only [Nat.cast_zero, lineVal]; positivity
      · let k : Fin (n + 1) := ⟨m.1 - 1, by omega⟩
        have hc := hcond (Fin.last n) k
        rw [extendSig_last] at hc
        have hf : decide (m.1 < k.1 + 1) = false := by
          simp only [decide_eq_false_iff_not, k]; omega
        rw [hf] at hc
        simp only [Bool.false_eq_true, ↓reduceIte, Fin.val_last] at hc
        have hk : k.1 + 1 = m.1 := by dsimp [k]; omega
        simpa [hk] using hc
    · by_cases hmn : m.1 = n + 1
      · rw [hmn]
        simp only [lineVal]
        push_cast
        nlinarith
      · let k : Fin (n + 1) := ⟨m.1, by omega⟩
        have hc := hcond (Fin.last n) k
        rw [extendSig_last] at hc
        have ht : decide (m.1 < k.1 + 1) = true := by simp [k]
        rw [ht] at hc
        simp only [↓reduceIte, Fin.val_last] at hc
        simpa [k] using hc
  · rintro ⟨p, hpσ, hlo, hhi⟩
    rw [mem_cell_iff] at hpσ
    rcases hpσ with ⟨h1, h2, h3, h4, hcond⟩
    refine ⟨p, ?_⟩
    rw [mem_cell_iff]
    refine ⟨h1, h2, h3, h4, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro k
      rw [extendSig_last]
      simp only [Fin.val_last]
      by_cases hmk : m.1 < k.1 + 1
      · simp only [hmk, decide_true, ↓reduceIte]
        have : ((m.1 + 1 : ℕ) : ℝ) ≤ ((k.1 + 1 : ℕ) : ℝ) := by exact_mod_cast hmk
        linarith
      · simp only [hmk, decide_false, Bool.false_eq_true, ↓reduceIte]
        have : ((k.1 + 1 : ℕ) : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast (show k.1 + 1 ≤ m.1 by omega)
        linarith
    · intro k
      have hEq : extendSig σ m j.castSucc k = σ j k := by
        simpa [restrictSig] using congrFun (congrFun (restrictSig_extendSig σ m) j) k
      simpa [hEq] using hcond j k

lemma exists_extendSig_of_mem_activeSigs {n : ℕ} {τ : Sig (n + 1)} (hτ : τ ∈ activeSigs (n + 1)) :
    ∃ m : Fin (n + 2), τ = extendSig (restrictSig τ) m ∧ m ∈ hitBands n (restrictSig τ) := by
  simp only [activeSigs, Finset.mem_filter, Finset.mem_univ, true_and] at hτ
  rcases hτ with ⟨p, hp⟩
  have hp' := hp
  rw [mem_cell_iff] at hp'
  rcases hp' with ⟨h1, h2, h3, h4, hcond⟩
  have hval_pos : 0 < lineVal (n + 1) p := by
    simp only [lineVal]; positivity
  have hval_lt : lineVal (n + 1) p < ((n + 2 : ℕ) : ℝ) := by
    simp only [lineVal]
    push_cast
    nlinarith
  let mNat := Nat.floor (lineVal (n + 1) p)
  have hm_lt : mNat < n + 2 := (Nat.floor_lt (le_of_lt hval_pos)).mpr hval_lt
  let m : Fin (n + 2) := ⟨mNat, hm_lt⟩
  have hm_le : (m.1 : ℝ) ≤ lineVal (n + 1) p := Nat.floor_le (le_of_lt hval_pos)
  have hτ_eq : τ = extendSig (restrictSig τ) m := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · funext k
      rw [extendSig_last]
      have hc := hcond (Fin.last n) k
      simp only [Fin.val_last] at hc
      cases hτk : τ (Fin.last n) k
      · rw [hτk] at hc
        simp only [Bool.false_eq_true, ↓reduceIte] at hc
        have hle : k.1 + 1 ≤ m.1 := Nat.le_floor (le_of_lt hc)
        have : ¬ (m.1 < k.1 + 1) := by omega
        simp [this]
      · rw [hτk] at hc
        simp only [↓reduceIte] at hc
        have hlt : m.1 < k.1 + 1 := by
          have : (m.1 : ℝ) < ((k.1 + 1 : ℕ) : ℝ) := lt_of_le_of_lt hm_le hc
          exact_mod_cast this
        simp [hlt]
    · funext k
      simp [restrictSig, extendSig, Fin.snoc_castSucc]
  refine ⟨m, hτ_eq, ?_⟩
  rw [← extendSig_mem_activeSigs_iff, ← hτ_eq]
  simp only [activeSigs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨p, hp⟩

lemma card_activeSigs_succ (n : ℕ) :
    (activeSigs (n + 1)).card = ∑ σ ∈ activeSigs n, (hitBands n σ).card := by
  let f : (Σ σ : Sig n, Fin (n + 2)) → Sig (n + 1) := fun x => extendSig x.1 x.2
  have himg : activeSigs (n + 1) =
      ((activeSigs n).sigma (hitBands n)).image f := by
    ext τ
    simp only [Finset.mem_image, Finset.mem_sigma, Sigma.exists, f]
    constructor
    · intro hτ
      rcases exists_extendSig_of_mem_activeSigs hτ with ⟨m, hEq, hm⟩
      refine ⟨restrictSig τ, m, ⟨?_, hm⟩, hEq.symm⟩
      simp only [activeSigs, Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      rcases hτ with ⟨p, hp⟩
      refine ⟨p, ?_⟩
      rw [mem_cell_iff] at hp ⊢
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, fun i k => hp.2.2.2.2 i.castSucc k⟩
    · rintro ⟨σ, m, ⟨_, hm⟩, rfl⟩
      exact (extendSig_mem_activeSigs_iff σ m).mpr hm
  rw [himg, Finset.card_image_of_injOn, Finset.card_sigma]
  intro x _ y _ hxy
  have h1 : x.1 = y.1 := by
    have := congrArg restrictSig hxy
    simpa [f, restrictSig_extendSig] using this
  cases x; cases y
  dsimp at h1
  subst h1
  have h2 : _ = _ := extendSig_injective _ hxy
  subst h2
  rfl

lemma hitBands_nonempty {n : ℕ} {σ : Sig n} (hσ : σ ∈ activeSigs n) :
    (hitBands n σ).Nonempty := by
  simp only [activeSigs, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  rcases hσ with ⟨p, hp⟩
  have hopen := isOpen_cell n σ
  rw [Metric.isOpen_iff] at hopen
  rcases hopen p hp with ⟨δ, hδpos, hball⟩
  have hp' := (mem_cell_iff n σ p).mp hp
  rcases hp' with ⟨h1, h2, h3, h4, _⟩
  have hval_pos : 0 < lineVal (n + 1) p := by
    simp only [lineVal]; positivity
  have hval_lt : lineVal (n + 1) p < ((n + 2 : ℕ) : ℝ) := by
    simp only [lineVal]
    push_cast
    nlinarith
  let mNat := Nat.floor (lineVal (n + 1) p)
  have hm_lt : mNat < n + 2 := (Nat.floor_lt (le_of_lt hval_pos)).mpr hval_lt
  have hm_le : (mNat : ℝ) ≤ lineVal (n + 1) p := Nat.floor_le (le_of_lt hval_pos)
  have hm_lt_succ : lineVal (n + 1) p < ((mNat + 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (lineVal (n + 1) p)
  by_cases heq : lineVal (n + 1) p = (mNat : ℝ)
  · let ε := min (δ / 2) ((1 : ℝ) / 2)
    have hεpos : 0 < ε := lt_min (by linarith) (by norm_num)
    have hεltδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hεlt1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    let q : ℝ × ℝ := (p.1, p.2 + ε)
    have hq : q ∈ cell n σ := by
      apply hball
      rw [Metric.mem_ball, Prod.dist_eq]
      simp only [q, dist_self, Real.dist_eq, add_sub_cancel_left, abs_of_pos hεpos]
      exact max_lt hδpos hεltδ
    refine ⟨⟨mNat, hm_lt⟩, ?_⟩
    simp only [hitBands, Finset.mem_filter, Finset.mem_univ, true_and, cellHits]
    refine ⟨q, hq, ?_, ?_⟩
    · have : lineVal (n + 1) q = lineVal (n + 1) p + ε := by simp [lineVal, q]; ring
      linarith
    · have : lineVal (n + 1) q = lineVal (n + 1) p + ε := by simp [lineVal, q]; ring
      push_cast
      linarith
  · refine ⟨⟨mNat, hm_lt⟩, ?_⟩
    simp only [hitBands, Finset.mem_filter, Finset.mem_univ, true_and, cellHits]
    exact ⟨p, hp, lt_of_le_of_ne hm_le (Ne.symm heq), hm_lt_succ⟩

lemma cellCrosses_imp_hits {n : ℕ} {σ : Sig n} {k : Fin (n + 1)}
    (hk : cellCrosses n σ k) :
    (⟨k.1, by omega⟩ : Fin (n + 2)) ∈ hitBands n σ ∧
    (⟨k.1 + 1, by omega⟩ : Fin (n + 2)) ∈ hitBands n σ := by
  rcases hk with ⟨p, hp, hval⟩
  have hopen := isOpen_cell n σ
  rw [Metric.isOpen_iff] at hopen
  rcases hopen p hp with ⟨δ, hδpos, hball⟩
  let ε := min (δ / 2) ((1 : ℝ) / 2)
  have hεpos : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεltδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεlt1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  constructor
  · let q : ℝ × ℝ := (p.1, p.2 - ε)
    have hq : q ∈ cell n σ := by
      apply hball
      rw [Metric.mem_ball, Prod.dist_eq]
      simp only [q, dist_self, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hεpos]
      exact max_lt hδpos hεltδ
    simp only [hitBands, Finset.mem_filter, Finset.mem_univ, true_and, cellHits]
    refine ⟨q, hq, ?_, ?_⟩
    · have : lineVal (n + 1) q = lineVal (n + 1) p - ε := by simp [lineVal, q]; ring
      rw [this, hval]; push_cast; linarith
    · have : lineVal (n + 1) q = lineVal (n + 1) p - ε := by simp [lineVal, q]; ring
      rw [this, hval]; linarith
  · let q : ℝ × ℝ := (p.1, p.2 + ε)
    have hq : q ∈ cell n σ := by
      apply hball
      rw [Metric.mem_ball, Prod.dist_eq]
      simp only [q, dist_self, Real.dist_eq, add_sub_cancel_left, abs_of_pos hεpos]
      exact max_lt hδpos hεltδ
    simp only [hitBands, Finset.mem_filter, Finset.mem_univ, true_and, cellHits]
    refine ⟨q, hq, ?_, ?_⟩
    · have : lineVal (n + 1) q = lineVal (n + 1) p + ε := by simp [lineVal, q]; ring
      rw [this, hval]; linarith
    · have : lineVal (n + 1) q = lineVal (n + 1) p + ε := by simp [lineVal, q]; ring
      rw [this, hval]; push_cast; linarith

lemma hits_imp_cellCrosses {n : ℕ} {σ : Sig n} {a b : Fin (n + 2)} {k : Fin (n + 1)}
    (ha : a ∈ hitBands n σ) (hb : b ∈ hitBands n σ)
    (hak : a.1 ≤ k.1) (hkb : k.1 < b.1) :
    cellCrosses n σ k := by
  simp only [hitBands, Finset.mem_filter, Finset.mem_univ, true_and, cellHits] at ha hb
  rcases ha with ⟨p, hp, _, hphi⟩
  rcases hb with ⟨q, hq, hqlo, _⟩
  have hvp_lt : lineVal (n + 1) p < ((k.1 + 1 : ℕ) : ℝ) := by
    have : ((a.1 + 1 : ℕ) : ℝ) ≤ ((k.1 + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ hak)
    linarith
  have hlt_vq : ((k.1 + 1 : ℕ) : ℝ) < lineVal (n + 1) q := by
    have : ((k.1 + 1 : ℕ) : ℝ) ≤ (b.1 : ℝ) := by exact_mod_cast hkb
    linarith
  let t : ℝ := (((k.1 + 1 : ℕ) : ℝ) - lineVal (n + 1) p) /
    (lineVal (n + 1) q - lineVal (n + 1) p)
  have hden : 0 < lineVal (n + 1) q - lineVal (n + 1) p := by linarith
  have ht0 : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hden)
  have ht1 : t ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hmem : (1 - t) • p + t • q ∈ cell n σ :=
    convex_cell n σ hp hq (by linarith) ht0 (by ring)
  refine ⟨(1 - t) • p + t • q, hmem, ?_⟩
  have hlin : lineVal (n + 1) ((1 - t) • p + t • q) =
      (1 - t) * lineVal (n + 1) p + t * lineVal (n + 1) q := by
    simp only [lineVal, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hlin]
  have hne : lineVal (n + 1) q - lineVal (n + 1) p ≠ 0 := ne_of_gt hden
  dsimp only [t]
  field_simp [hne]
  ring

lemma card_hitBands_eq_succ_card_crossLines {n : ℕ} {σ : Sig n} (hσ : σ ∈ activeSigs n) :
    (hitBands n σ).card = 1 + (crossLines n σ).card := by
  have hne := hitBands_nonempty hσ
  let a := (hitBands n σ).min' hne
  let b := (hitBands n σ).max' hne
  have ha : a ∈ hitBands n σ := Finset.min'_mem _ hne
  have hb : b ∈ hitBands n σ := Finset.max'_mem _ hne
  have hab : a.1 ≤ b.1 := Finset.min'_le _ b hb
  have hH : hitBands n σ = Finset.univ.filter (fun m : Fin (n + 2) => a.1 ≤ m.1 ∧ m.1 ≤ b.1) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hm
      exact ⟨Finset.min'_le _ m hm, Finset.le_max' _ m hm⟩
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with heq | hlt
      · exact Fin.ext heq ▸ ha
      · let k : Fin (n + 1) := ⟨m.1 - 1, by omega⟩
        have hcross : cellCrosses n σ k :=
          hits_imp_cellCrosses ha hb (by dsimp [k]; omega) (by dsimp [k]; omega)
        have hhit := (cellCrosses_imp_hits hcross).2
        have hmk : (⟨k.1 + 1, by omega⟩ : Fin (n + 2)) = m := by
          ext; dsimp [k]; omega
        simpa [hmk] using hhit
  have hK : crossLines n σ = Finset.univ.filter (fun k : Fin (n + 1) => a.1 ≤ k.1 ∧ k.1 < b.1) := by
    ext k
    simp only [crossLines, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hk
      have ⟨h1, h2⟩ := cellCrosses_imp_hits hk
      have ha1 : a.1 ≤ k.1 := Finset.min'_le _ _ h1
      have hb1 : k.1 + 1 ≤ b.1 := Finset.le_max' _ _ h2
      exact ⟨ha1, by omega⟩
    · rintro ⟨h1, h2⟩
      exact hits_imp_cellCrosses ha hb h1 h2
  have hcardH : (hitBands n σ).card = b.1 - a.1 + 1 := by
    rw [hH]
    have hbij : (Finset.univ.filter (fun m : Fin (n + 2) => a.1 ≤ m.1 ∧ m.1 ≤ b.1)).card =
        (Finset.Icc a.1 b.1).card := by
      refine Finset.card_bij (fun m _ => m.1) ?_ ?_ ?_
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
        exact Finset.mem_Icc.mpr hm
      · intro m₁ _ m₂ _ h; exact Fin.ext h
      · intro x hx
        rw [Finset.mem_Icc] at hx
        exact ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    rw [hbij, Nat.card_Icc]
    omega
  have hcardK : (crossLines n σ).card = b.1 - a.1 := by
    rw [hK]
    have hbij : (Finset.univ.filter (fun k : Fin (n + 1) => a.1 ≤ k.1 ∧ k.1 < b.1)).card =
        (Finset.Ico a.1 b.1).card := by
      refine Finset.card_bij (fun k _ => k.1) ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact Finset.mem_Ico.mpr hk
      · intro k₁ _ k₂ _ h; exact Fin.ext h
      · intro x hx
        rw [Finset.mem_Ico] at hx
        exact ⟨⟨x, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    rw [hbij, Nat.card_Ico]
  omega

/-- Cells of `fanComplement n` intersected by the new line `y + (n + 1) x = k + 1`. -/
noncomputable def crossCells (n : ℕ) (k : Fin (n + 1)) : Finset (Sig n) :=
  (activeSigs n).filter (fun σ => cellCrosses n σ k)

lemma card_activeSigs_succ_eq_add_sum_crossCells (n : ℕ) :
    (activeSigs (n + 1)).card =
      (activeSigs n).card + ∑ k : Fin (n + 1), (crossCells n k).card := by
  rw [card_activeSigs_succ]
  have h1 : ∑ σ ∈ activeSigs n, (hitBands n σ).card =
      ∑ σ ∈ activeSigs n, (1 + (crossLines n σ).card) :=
    Finset.sum_congr rfl fun σ hσ => card_hitBands_eq_succ_card_crossLines hσ
  rw [h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  congr 1
  have h2 : ∀ σ ∈ activeSigs n,
      (crossLines n σ).card = ∑ k : Fin (n + 1), if cellCrosses n σ k then 1 else 0 := by
    intro σ _
    rw [crossLines, Finset.card_filter]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [crossCells, Finset.card_filter]

/-! ### Step 3: Segment subdivision along each new line -/

/-- Point on the new line `y + (n + 1) x = k + 1` with first coordinate `x`. -/
def segPt (n : ℕ) (k : Fin (n + 1)) (x : ℝ) : ℝ × ℝ :=
  (x, ((k.1 + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) * x)

/-- Left endpoint `k / (n + 1)` of the segment `L_{n+1, k+1} ∩ (0, 1)²`. -/
noncomputable def segLo (n : ℕ) (k : Fin (n + 1)) : ℝ := (k.1 : ℝ) / ((n + 1 : ℕ) : ℝ)

/-- Right endpoint `(k + 1) / (n + 1)` of the segment `L_{n+1, k+1} ∩ (0, 1)²`. -/
noncomputable def segHi (n : ℕ) (k : Fin (n + 1)) : ℝ := ((k.1 + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)

lemma segLo_eq_ratCast (n : ℕ) (k : Fin (n + 1)) :
    segLo n k = Rat.cast ((k.1 : ℚ) / ((n + 1 : ℕ) : ℚ)) := by
  simp [segLo]

lemma segHi_eq_ratCast (n : ℕ) (k : Fin (n + 1)) :
    segHi n k = Rat.cast (((k.1 + 1 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ)) := by
  simp [segHi]

lemma segLo_lt_segHi (n : ℕ) (k : Fin (n + 1)) : segLo n k < segHi n k := by
  unfold segLo segHi
  apply div_lt_div_of_pos_right _ (by positivity)
  push_cast; linarith

lemma segPt_in_square_iff (n : ℕ) (k : Fin (n + 1)) (x : ℝ) :
    (0 < (segPt n k x).1 ∧ (segPt n k x).1 < 1 ∧
     0 < (segPt n k x).2 ∧ (segPt n k x).2 < 1) ↔
      segLo n k < x ∧ x < segHi n k := by
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  simp only [segPt, segLo, segHi]
  constructor
  · rintro ⟨_, _, hy0, hy1⟩
    constructor
    · rw [div_lt_iff₀ hn]
      have hk : ((k.1 + 1 : ℕ) : ℝ) = (k.1 : ℝ) + 1 := by push_cast; rfl
      linarith
    · rw [lt_div_iff₀ hn]
      linarith
  · rintro ⟨hlo, hhi⟩
    rw [div_lt_iff₀ hn] at hlo
    rw [lt_div_iff₀ hn] at hhi
    have hk0 : (0 : ℝ) ≤ (k.1 : ℝ) := Nat.cast_nonneg _
    have hk1 : ((k.1 + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast k.2
    have hk : ((k.1 + 1 : ℕ) : ℝ) = (k.1 : ℝ) + 1 := by push_cast; rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · linarith
    · linarith

/-- Rational `x`-coordinate where `L_{n+1, k+1}` meets `L_{i+1, r+1}`. -/
def interRat (n : ℕ) (k : Fin (n + 1)) (i : Fin n) (r : Fin (i.1 + 1)) : ℚ :=
  (((k.1 + 1 : ℕ) : ℚ) - ((r.1 + 1 : ℕ) : ℚ)) / ((n - i.1 : ℕ) : ℚ)

/-- Finite set of rational `x`-coordinates of interior intersections on `L_{n+1, k+1}`. -/
def interX (n : ℕ) (k : Fin (n + 1)) : Finset ℚ :=
  ((Finset.univ : Finset (Σ i : Fin n, Fin (i.1 + 1))).image
    (fun ir => interRat n k ir.1 ir.2)).filter
    (fun q => (k.1 : ℚ) / ((n + 1 : ℕ) : ℚ) < q ∧ q < ((k.1 + 1 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ))

lemma lineVal_segPt (n : ℕ) (k : Fin (n + 1)) (i : Fin n) (r : Fin (i.1 + 1)) (x : ℝ) :
    lineVal (i.1 + 1) (segPt n k x) - ((r.1 + 1 : ℕ) : ℝ) =
      ((n - i.1 : ℕ) : ℝ) * ((interRat n k i r : ℝ) - x) := by
  have hd : ((n - i.1 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < n - i.1 := by omega
    exact_mod_cast (ne_of_gt this)
  have hcast : ((n - i.1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) - ((i.1 + 1 : ℕ) : ℝ) := by
    have : (n - i.1) + (i.1 + 1) = n + 1 := by omega
    have h := congrArg (fun m : ℕ => (m : ℝ)) this
    push_cast at h ⊢
    linarith
  simp only [lineVal, segPt, interRat, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast]
  field_simp [hd]
  rw [hcast]
  ring

lemma segPt_mem_fanComplement_iff (n : ℕ) (k : Fin (n + 1)) (x : ℝ) :
    segPt n k x ∈ fanComplement n ↔
      segLo n k < x ∧ x < segHi n k ∧
      x ∉ (interX n k).image ((↑) : ℚ → ℝ) := by
  rw [mem_fanComplement_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4, hne⟩
    have ⟨hlo, hhi⟩ := (segPt_in_square_iff n k x).mp ⟨h1, h2, h3, h4⟩
    refine ⟨hlo, hhi, ?_⟩
    intro hmem
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨q, hq, rfl⟩
    simp only [interX, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Sigma.exists] at hq
    rcases hq with ⟨⟨i, r, rfl⟩, _⟩
    have hzero := lineVal_segPt n k i r (interRat n k i r : ℝ)
    simp only [sub_self, mul_zero] at hzero
    exact hne i r (sub_eq_zero.mp hzero)
  · rintro ⟨hlo, hhi, hnotmem⟩
    have ⟨h1, h2, h3, h4⟩ := (segPt_in_square_iff n k x).mpr ⟨hlo, hhi⟩
    refine ⟨h1, h2, h3, h4, fun i r heq => ?_⟩
    have hzero := lineVal_segPt n k i r x
    rw [heq, sub_self] at hzero
    have hd : ((n - i.1 : ℕ) : ℝ) ≠ 0 := by
      have : 0 < n - i.1 := by omega
      exact_mod_cast (ne_of_gt this)
    have hxeq : x = (interRat n k i r : ℝ) := by
      have hmul : (interRat n k i r : ℝ) - x = 0 := by
        rcases mul_eq_zero.mp hzero.symm with h | h
        · exact absurd h hd
        · exact h
      linarith
    apply hnotmem
    rw [Finset.mem_image]
    refine ⟨interRat n k i r, ?_, hxeq.symm⟩
    simp only [interX, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Sigma.exists]
    refine ⟨⟨i, r, rfl⟩, ?_, ?_⟩
    · have : segLo n k < (interRat n k i r : ℝ) := hxeq ▸ hlo
      rw [segLo_eq_ratCast, Rat.cast_lt] at this
      exact this
    · have : (interRat n k i r : ℝ) < segHi n k := hxeq ▸ hhi
      rw [segHi_eq_ratCast, Rat.cast_lt] at this
      exact this

lemma card_crossCells_eq_succ_card_interX (n : ℕ) (k : Fin (n + 1)) :
    (crossCells n k).card = 1 + (interX n k).card := by
  let P : Finset ℝ := (interX n k).image ((↑) : ℚ → ℝ)
  have hPcard : P.card = (interX n k).card :=
    Finset.card_image_of_injective _ Rat.cast_injective
  have hPmem : ∀ x ∈ P, segLo n k < x ∧ x < segHi n k := by
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨q, hq, rfl⟩
    simp only [interX, Finset.mem_filter] at hq
    rw [segLo_eq_ratCast, segHi_eq_ratCast, Rat.cast_lt, Rat.cast_lt]
    exact hq.2
  let m := P.card
  let e : Fin m ↪o ℝ := P.orderEmbOfFin rfl
  have he_mem : ∀ j : Fin m, e j ∈ P := fun j => P.orderEmbOfFin_mem rfl j
  let t : Fin (m + 2) → ℝ := fun j =>
    if h0 : j.1 = 0 then segLo n k
    else if hm : j.1 = m + 1 then segHi n k
    else e ⟨j.1 - 1, by omega⟩
  have ht_strict : StrictMono t := by
    intro a b hab
    have ha' : a.1 < b.1 := hab
    dsimp only [t]
    split_ifs with h1 h2 h3 h4 h5 h6
    · omega
    · exact segLo_lt_segHi n k
    · exact (hPmem _ (he_mem _)).1
    · omega
    · omega
    · omega
    · omega
    · exact (hPmem _ (he_mem _)).2
    · exact e.strictMono (show (⟨a.1 - 1, _⟩ : Fin m) < ⟨b.1 - 1, _⟩ by simp [Fin.lt_def]; omega)
  let mid : Fin (m + 1) → ℝ := fun j => (t j.castSucc + t j.succ) / 2
  have hmid_lo : ∀ j : Fin (m + 1), t j.castSucc < mid j := fun j => by
    have hlt := ht_strict (Fin.castSucc_lt_succ : j.castSucc < j.succ)
    dsimp [mid]; linarith
  have hmid_hi : ∀ j : Fin (m + 1), mid j < t j.succ := fun j => by
    have hlt := ht_strict (Fin.castSucc_lt_succ : j.castSucc < j.succ)
    dsimp [mid]; linarith
  have hmid_mem : ∀ j : Fin (m + 1), segPt n k (mid j) ∈ fanComplement n := by
    intro j
    rw [segPt_mem_fanComplement_iff]
    refine ⟨?_, ?_, ?_⟩
    · have h0 : segLo n k = t 0 := by simp [t]
      have hle : t 0 ≤ t j.castSucc := ht_strict.monotone (Fin.zero_le _)
      linarith [hmid_lo j]
    · have h1 : segHi n k = t (Fin.last (m + 1)) := by simp [t]
      have hle : t j.succ ≤ t (Fin.last (m + 1)) := ht_strict.monotone (Fin.le_last _)
      linarith [hmid_hi j]
    · intro hP
      have hrange : Set.range e = (P : Set ℝ) := Finset.range_orderEmbOfFin P rfl
      have hmemR : mid j ∈ Set.range e := by rwa [hrange]
      rcases hmemR with ⟨l, hl⟩
      let idx : Fin (m + 2) := ⟨l.1 + 1, by omega⟩
      have htidx : t idx = mid j := by
        have h1 : idx.1 ≠ 0 := by dsimp [idx]; omega
        have h2 : idx.1 ≠ m + 1 := by dsimp [idx]; omega
        simp only [t, h1, h2, ↓reduceDIte]
        have hsub : (⟨idx.1 - 1, by omega⟩ : Fin m) = l := by ext; dsimp [idx]
        rw [hsub, hl]
      have hgt : j.castSucc < idx := ht_strict.lt_iff_lt.mp (htidx ▸ hmid_lo j)
      have hlt : idx < j.succ := ht_strict.lt_iff_lt.mp (htidx.symm ▸ hmid_hi j)
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hgt hlt
      omega
  have hseg_val : ∀ x : ℝ, lineVal (n + 1) (segPt n k x) = ((k.1 + 1 : ℕ) : ℝ) := fun x => by
    simp [lineVal, segPt]
  let φ : Fin (m + 1) → Sig n := fun j => sig n (segPt n k (mid j))
  have hφ_mem : ∀ j : Fin (m + 1), φ j ∈ crossCells n k := by
    intro j
    rw [crossCells, Finset.mem_filter, activeSigs, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, ⟨segPt n k (mid j), hmid_mem j, rfl⟩⟩,
      ⟨segPt n k (mid j), ⟨hmid_mem j, rfl⟩, hseg_val (mid j)⟩⟩
  have hφ_inj : Function.Injective φ := by
    have aux : ∀ j₁ j₂ : Fin (m + 1), j₁ < j₂ → φ j₁ ≠ φ j₂ := by
      intro j₁ j₂ hlt hEq
      have hle : j₁.succ ≤ j₂.castSucc := by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        exact hlt
      have hm1_lt : mid j₁ < t j₁.succ := hmid_hi j₁
      have ht_lt_m2 : t j₁.succ < mid j₂ :=
        lt_of_le_of_lt (ht_strict.monotone hle) (hmid_lo j₂)
      have htP : t j₁.succ ∈ P := by
        have h1 : j₁.succ.1 ≠ 0 := by simp
        have h2 : j₁.succ.1 ≠ m + 1 := by
          simp only [Fin.val_succ]
          have : j₁.1 < j₂.1 := hlt
          omega
        simp only [t, h1, h2, ↓reduceDIte]
        exact he_mem _
      rw [Finset.mem_image] at htP
      rcases htP with ⟨q, hq, hqEq⟩
      simp only [interX, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
        Sigma.exists] at hq
      rcases hq with ⟨⟨i, r, rfl⟩, _⟩
      have hd : (0 : ℝ) < ((n - i.1 : ℕ) : ℝ) := by
        have : 0 < n - i.1 := by omega
        exact_mod_cast this
      have hv1 : ((r.1 + 1 : ℕ) : ℝ) < lineVal (i.1 + 1) (segPt n k (mid j₁)) := by
        have h := lineVal_segPt n k i r (mid j₁)
        have hpos : 0 < (interRat n k i r : ℝ) - mid j₁ := by linarith
        have : 0 < lineVal (i.1 + 1) (segPt n k (mid j₁)) - ((r.1 + 1 : ℕ) : ℝ) := by
          rw [h]; exact mul_pos hd hpos
        linarith
      have hv2 : lineVal (i.1 + 1) (segPt n k (mid j₂)) < ((r.1 + 1 : ℕ) : ℝ) := by
        have h := lineVal_segPt n k i r (mid j₂)
        have hneg : (interRat n k i r : ℝ) - mid j₂ < 0 := by linarith
        have : lineVal (i.1 + 1) (segPt n k (mid j₂)) - ((r.1 + 1 : ℕ) : ℝ) < 0 := by
          rw [h]; exact mul_neg_of_pos_of_neg hd hneg
        linarith
      have hsigEq := congrFun (congrFun hEq i) r
      unfold φ sig at hsigEq
      rw [decide_eq_decide] at hsigEq
      exact not_lt_of_gt hv1 (hsigEq.mpr hv2)
    intro j₁ j₂ hEq
    rcases lt_trichotomy j₁ j₂ with hlt | heq | hgt
    · exact absurd hEq (aux j₁ j₂ hlt)
    · exact heq
    · exact absurd hEq.symm (aux j₂ j₁ hgt)
  have hφ_surj : ∀ σ ∈ crossCells n k, ∃ j : Fin (m + 1), φ j = σ := by
    intro σ hσ
    rw [crossCells, Finset.mem_filter] at hσ
    rcases hσ.2 with ⟨p, hp, hval⟩
    have hp_eq : p = segPt n k p.1 := by
      ext
      · rfl
      · simp only [segPt]; simp only [lineVal] at hval; linarith
    have hpf : segPt n k p.1 ∈ fanComplement n := hp_eq ▸ hp.1
    have ⟨hlo, hhi, hnotP⟩ := (segPt_mem_fanComplement_iff n k p.1).mp hpf
    let S := Finset.univ.filter (fun idx : Fin (m + 2) => t idx < p.1)
    have hS_ne : S.Nonempty := ⟨0, by simp [S, t, hlo]⟩
    let idx := S.max' hS_ne
    have hidx_mem : t idx < p.1 := (Finset.mem_filter.mp (Finset.max'_mem S hS_ne)).2
    have hidx_lt : idx.1 < m + 1 := by
      by_contra hge
      have heq : idx = Fin.last (m + 1) := by ext; simp; omega
      rw [heq] at hidx_mem
      have hlast : t (Fin.last (m + 1)) = segHi n k := by simp [t]
      linarith
    let j : Fin (m + 1) := ⟨idx.1, hidx_lt⟩
    have hj_lo : t j.castSucc < p.1 := by
      have : j.castSucc = idx := by ext; rfl
      rwa [this]
    have hj_hi : p.1 < t j.succ := by
      have hnotS : j.succ ∉ S := by
        intro hmem
        have hle := Finset.le_max' S j.succ hmem
        have : j.succ.1 ≤ idx.1 := hle
        simp [j] at this
      have hle : p.1 ≤ t j.succ := le_of_not_gt (by simpa [S] using hnotS)
      refine lt_of_le_of_ne hle fun heq => ?_
      by_cases hlast : j.succ.1 = m + 1
      · have : t j.succ = segHi n k := by
          simp only [t, hlast, Nat.succ_ne_zero, ↓reduceDIte]
        linarith
      · have h0 : j.succ.1 ≠ 0 := by simp
        have : t j.succ ∈ P := by
          simp only [t, h0, hlast, ↓reduceDIte]
          exact he_mem _
        exact hnotP (heq ▸ this)
    refine ⟨j, ?_⟩
    rw [← hp.2, hp_eq]
    funext i r
    unfold φ sig
    rw [decide_eq_decide]
    have hd : (0 : ℝ) < ((n - i.1 : ℕ) : ℝ) := by
      have : 0 < n - i.1 := by omega
      exact_mod_cast this
    have hiff : ∀ x : ℝ, (lineVal (i.1 + 1) (segPt n k x) < ((r.1 + 1 : ℕ) : ℝ)) ↔
        (interRat n k i r : ℝ) < x := fun x => by
      have h := lineVal_segPt n k i r x
      constructor
      · intro hlt
        have hneg : ((n - i.1 : ℕ) : ℝ) * ((interRat n k i r : ℝ) - x) < 0 := by linarith
        nlinarith
      · intro hlt
        have hneg : ((n - i.1 : ℕ) : ℝ) * ((interRat n k i r : ℝ) - x) < 0 :=
          mul_neg_of_pos_of_neg hd (by linarith)
        linarith
    rw [hiff, hiff]
    have hnotBetween : ¬ (t j.castSucc < (interRat n k i r : ℝ) ∧
        (interRat n k i r : ℝ) < t j.succ) := by
      rintro ⟨h1, h2⟩
      have hlo' : segLo n k < (interRat n k i r : ℝ) :=
        lt_of_le_of_lt (by simpa [t] using ht_strict.monotone (Fin.zero_le j.castSucc)) h1
      have hhi' : (interRat n k i r : ℝ) < segHi n k :=
        lt_of_lt_of_le h2 (by simpa [t] using ht_strict.monotone (Fin.le_last j.succ))
      have hmemP : (interRat n k i r : ℝ) ∈ P := by
        rw [Finset.mem_image]
        refine ⟨interRat n k i r, ?_, rfl⟩
        simp only [interX, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
          Sigma.exists]
        rw [segLo_eq_ratCast, Rat.cast_lt] at hlo'
        rw [segHi_eq_ratCast, Rat.cast_lt] at hhi'
        exact ⟨⟨i, r, rfl⟩, hlo', hhi'⟩
      have hrange : Set.range e = (P : Set ℝ) := Finset.range_orderEmbOfFin P rfl
      have hmemR : (interRat n k i r : ℝ) ∈ Set.range e := by rwa [hrange]
      rcases hmemR with ⟨l, hl⟩
      let idx' : Fin (m + 2) := ⟨l.1 + 1, by omega⟩
      have htidx' : t idx' = (interRat n k i r : ℝ) := by
        have ha0 : idx'.1 ≠ 0 := by dsimp [idx']; omega
        have ham : idx'.1 ≠ m + 1 := by dsimp [idx']; omega
        simp only [t, ha0, ham, ↓reduceDIte]
        have hsub : (⟨idx'.1 - 1, by omega⟩ : Fin m) = l := by ext; dsimp [idx']
        rw [hsub, hl]
      have hgt : j.castSucc < idx' := ht_strict.lt_iff_lt.mp (htidx' ▸ h1)
      have hlt : idx' < j.succ := ht_strict.lt_iff_lt.mp (htidx'.symm ▸ h2)
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hgt hlt
      omega
    constructor <;> intro hlt
    · by_contra hge
      exact hnotBetween ⟨lt_of_lt_of_le hj_lo (le_of_not_gt hge), lt_trans hlt (hmid_hi j)⟩
    · by_contra hge
      exact hnotBetween ⟨lt_of_lt_of_le (hmid_lo j) (le_of_not_gt hge), lt_trans hlt hj_hi⟩
  have himg : crossCells n k = Finset.univ.image φ := by
    ext σ
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun h => hφ_surj σ h, fun ⟨j, hj⟩ => hj ▸ hφ_mem j⟩
  rw [himg, Finset.card_image_of_injective _ hφ_inj, Finset.card_fin]
  dsimp only [m]
  rw [hPcard]
  omega

/-! ### Step 4: Farey characterization and Gauss's totient sum -/

lemma interX_pairwiseDisjoint (n : ℕ) :
    ((Finset.univ : Finset (Fin (n + 1))) : Set (Fin (n + 1))).PairwiseDisjoint (interX n) := by
  intro k₁ _ k₂ _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro q hq1 hq2
  simp only [interX, Finset.mem_filter] at hq1 hq2
  have hn : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
  have h1lo : (k₁.1 : ℚ) < q * ((n + 1 : ℕ) : ℚ) := (div_lt_iff₀ hn).mp hq1.2.1
  have h1hi : q * ((n + 1 : ℕ) : ℚ) < ((k₁.1 + 1 : ℕ) : ℚ) := (lt_div_iff₀ hn).mp hq1.2.2
  have h2lo : (k₂.1 : ℚ) < q * ((n + 1 : ℕ) : ℚ) := (div_lt_iff₀ hn).mp hq2.2.1
  have h2hi : q * ((n + 1 : ℕ) : ℚ) < ((k₂.1 + 1 : ℕ) : ℚ) := (lt_div_iff₀ hn).mp hq2.2.2
  have h12 : (k₁.1 : ℚ) < ((k₂.1 + 1 : ℕ) : ℚ) := lt_trans h1lo h2hi
  have h21 : (k₂.1 : ℚ) < ((k₁.1 + 1 : ℕ) : ℚ) := lt_trans h2lo h1hi
  have h12' : k₁.1 < k₂.1 + 1 := by exact_mod_cast h12
  have h21' : k₂.1 < k₁.1 + 1 := by exact_mod_cast h21
  exact hne (Fin.ext (by omega))

lemma mem_biUnion_interX_iff (n : ℕ) (x : ℚ) :
    x ∈ (Finset.univ : Finset (Fin (n + 1))).biUnion (interX n) ↔
      0 < x ∧ x < 1 ∧ x.den ≤ n ∧ ¬ (x.den ∣ n + 1) := by
  constructor
  · intro hx
    rw [Finset.mem_biUnion] at hx
    rcases hx with ⟨k, _, hxk⟩
    simp only [interX, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Sigma.exists] at hxk
    rcases hxk with ⟨⟨i, r, rfl⟩, hlo, hhi⟩
    have hn : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
    have hxpos : 0 < interRat n k i r := by
      have : (0 : ℚ) ≤ (k.1 : ℚ) / ((n + 1 : ℕ) : ℚ) := by positivity
      exact lt_of_le_of_lt this hlo
    have hxlt1 : interRat n k i r < 1 := by
      have : ((k.1 + 1 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ) ≤ 1 := by
        rw [div_le_one hn]
        exact_mod_cast k.2
      exact lt_of_lt_of_le hhi this
    set x := interRat n k i r
    have hden_le : x.den ≤ n := by
      let d : ℕ := n - i.1
      have hdpos : 0 < d := by omega
      have hdn : d ≤ n := by omega
      have hmul : x * (d : ℚ) = ((k.1 + 1 : ℤ) - (r.1 + 1 : ℤ) : ℤ) := by
        dsimp only [x, interRat, d]
        have hdne : ((n - i.1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
        field_simp [hdne]
        push_cast
        ring
      have heqZ : x.num * (d : ℤ) = ((k.1 + 1 : ℤ) - (r.1 + 1 : ℤ)) * (x.den : ℤ) := by
        have hq : (x.num : ℚ) / (x.den : ℚ) * (d : ℚ) =
            (((k.1 + 1 : ℤ) - (r.1 + 1 : ℤ) : ℤ) : ℚ) := by
          rwa [Rat.num_div_den]
        have hdenne : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
        have hq' : (x.num : ℚ) * (d : ℚ) =
            (((k.1 + 1 : ℤ) - (r.1 + 1 : ℤ) : ℤ) : ℚ) * (x.den : ℚ) := by
          field_simp [hdenne] at hq
          linarith
        exact_mod_cast hq'
      have hdvdZ : (x.den : ℤ) ∣ x.num * (d : ℤ) := ⟨(k.1 + 1 : ℤ) - (r.1 + 1 : ℤ), by linarith⟩
      have hcop : IsCoprime (x.den : ℤ) x.num := by
        rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]
        exact x.reduced.symm
      have hdvd_d : x.den ∣ d := by
        have := hcop.dvd_of_dvd_mul_left hdvdZ
        exact_mod_cast this
      exact le_trans (Nat.le_of_dvd hdpos hdvd_d) hdn
    have hndvd : ¬ (x.den ∣ n + 1) := by
      rintro ⟨c, hc⟩
      have hmul : ((n + 1 : ℕ) : ℚ) * x = (((c : ℤ) * x.num : ℤ) : ℚ) := by
        conv_lhs => rw [← Rat.num_div_den x, hc]
        have hdenne : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
        push_cast
        field_simp [hdenne]
      have hlo' : (k.1 : ℚ) < ((n + 1 : ℕ) : ℚ) * x := by
        have := (div_lt_iff₀ hn).mp hlo; linarith
      have hhi' : ((n + 1 : ℕ) : ℚ) * x < ((k.1 + 1 : ℕ) : ℚ) := by
        have := (lt_div_iff₀ hn).mp hhi; linarith
      rw [hmul] at hlo' hhi'
      have h1 : (k.1 : ℤ) < (c : ℤ) * x.num := by exact_mod_cast hlo'
      have h2 : (c : ℤ) * x.num < (k.1 : ℤ) + 1 := by exact_mod_cast hhi'
      omega
    exact ⟨hxpos, hxlt1, hden_le, hndvd⟩
  · rintro ⟨hxpos, hxlt1, hden_le, hndvd⟩
    let q : ℕ := x.den
    let p : ℕ := x.num.natAbs
    have hqpos : 0 < q := x.den_pos
    have hnum_pos : 0 < x.num := Rat.num_pos.mpr hxpos
    have hnum_eq : x.num = (p : ℤ) := (Int.natAbs_of_nonneg (le_of_lt hnum_pos)).symm
    have hxpq : x = (p : ℚ) / (q : ℚ) := by
      rw [← Rat.num_div_den x, hnum_eq]; rfl
    have hp_lt_q : p < q := by
      have : (p : ℚ) / (q : ℚ) < 1 := hxpq ▸ hxlt1
      have : (p : ℚ) < (q : ℚ) := (div_lt_one (by exact_mod_cast hqpos)).mp this
      exact_mod_cast this
    have hp_pos : 0 < p := by omega
    have hcop : Nat.Coprime p q := x.reduced
    have hq_ge_2 : 2 ≤ q := by omega
    let m : ℕ := ((n + 1) * p) / q
    have hm_lt : m < n + 1 := by
      rw [Nat.div_lt_iff_lt_mul hqpos]
      exact Nat.mul_lt_mul_of_pos_left hp_lt_q (by omega)
    let k : Fin (n + 1) := ⟨m, hm_lt⟩
    have hm_lo_nat : m * q < (n + 1) * p := by
      have hle : m * q ≤ (n + 1) * p := Nat.div_mul_le_self _ _
      refine lt_of_le_of_ne hle fun heq => ?_
      have hdvd : q ∣ (n + 1) * p := ⟨m, by linarith⟩
      exact hndvd (hcop.symm.dvd_of_dvd_mul_right hdvd)
    have hm_hi_nat : (n + 1) * p < (m + 1) * q := by
      have hlt : (n + 1) * p < q * (m + 1) := Nat.lt_mul_div_succ ((n + 1) * p) hqpos
      rwa [mul_comm q (m + 1)] at hlt
    have hlo : (k.1 : ℚ) / ((n + 1 : ℕ) : ℚ) < x := by
      rw [hxpq, div_lt_div_iff₀ (by positivity) (by exact_mod_cast hqpos)]
      have hnat : k.1 * q < p * (n + 1) := by dsimp [k]; linarith [mul_comm (n + 1) p]
      exact_mod_cast hnat
    have hhi : x < ((k.1 + 1 : ℕ) : ℚ) / ((n + 1 : ℕ) : ℚ) := by
      rw [hxpq, div_lt_div_iff₀ (by exact_mod_cast hqpos) (by positivity)]
      have hnat : p * (n + 1) < (k.1 + 1) * q := by dsimp [k]; linarith [mul_comm (n + 1) p]
      exact_mod_cast hnat
    let i : Fin n := ⟨n - q, by omega⟩
    have hni : n - i.1 = q := by dsimp [i]; omega
    have hr_pos : p < k.1 + 1 := by
      have h1 : (p : ℚ) < ((k.1 + 1 : ℕ) : ℚ) := by
        have hlt : ((n + 1 : ℕ) : ℚ) * x < ((k.1 + 1 : ℕ) : ℚ) := by
          have := (lt_div_iff₀ (by positivity : (0 : ℚ) < ((n + 1 : ℕ) : ℚ))).mp hhi
          linarith
        have hqx : (q : ℚ) * x = (p : ℚ) := by
          rw [hxpq]; field_simp [show (q : ℚ) ≠ 0 by exact_mod_cast (ne_of_gt hqpos)]
        have hqn : (q : ℚ) ≤ ((n + 1 : ℕ) : ℚ) := by exact_mod_cast (show q ≤ n + 1 by omega)
        nlinarith
      exact_mod_cast h1
    have hr_le : k.1 + 1 - p ≤ i.1 + 1 := by
      have h1 : ((k.1 + 1 : ℕ) : ℚ) - (p : ℚ) < ((i.1 + 1 : ℕ) : ℚ) + 1 := by
        have hlo' : (k.1 : ℚ) < ((n + 1 : ℕ) : ℚ) * x := by
          have := (div_lt_iff₀ (by positivity : (0 : ℚ) < ((n + 1 : ℕ) : ℚ))).mp hlo
          linarith
        have hqx : (q : ℚ) * x = (p : ℚ) := by
          rw [hxpq]; field_simp [show (q : ℚ) ≠ 0 by exact_mod_cast (ne_of_gt hqpos)]
        have hiq : ((i.1 + 1 : ℕ) : ℚ) + (q : ℚ) = ((n + 1 : ℕ) : ℚ) := by
          exact_mod_cast (show i.1 + 1 + q = n + 1 by dsimp [i]; omega)
        have h1' : ((k.1 + 1 : ℕ) : ℚ) - (p : ℚ) < 1 + ((i.1 + 1 : ℕ) : ℚ) * x := by
          push_cast at hlo' hiq ⊢
          nlinarith
        have h2' : ((i.1 + 1 : ℕ) : ℚ) * x < ((i.1 + 1 : ℕ) : ℚ) := by
          have : (0 : ℚ) < ((i.1 + 1 : ℕ) : ℚ) := by positivity
          nlinarith
        linarith
      have h2 : ((k.1 + 1 - p : ℕ) : ℚ) < ((i.1 + 2 : ℕ) : ℚ) := by
        rw [Nat.cast_sub (le_of_lt hr_pos)]
        push_cast at h1 ⊢
        linarith
      have h3 : k.1 + 1 - p < i.1 + 2 := by exact_mod_cast h2
      omega
    let r : Fin (i.1 + 1) := ⟨k.1 + 1 - p - 1, by omega⟩
    have hr_val : r.1 + 1 = k.1 + 1 - p := by dsimp [r]; omega
    have hinter : interRat n k i r = x := by
      rw [interRat, hni, hr_val, hxpq]
      rw [Nat.cast_sub (le_of_lt hr_pos)]
      ring
    rw [Finset.mem_biUnion]
    refine ⟨k, Finset.mem_univ _, ?_⟩
    simp only [interX, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      Sigma.exists]
    exact ⟨⟨i, r, hinter⟩, hlo, hhi⟩

lemma card_biUnion_interX (n : ℕ) :
    ((Finset.univ : Finset (Fin (n + 1))).biUnion (interX n)).card =
      ∑ q ∈ (Finset.Icc 1 n).filter (fun q => ¬ (q ∣ n + 1)), Nat.totient q := by
  let D := (Finset.Icc 1 n).filter (fun q => ¬ (q ∣ n + 1))
  let F := D.sigma (fun q => (Finset.range q).filter (fun p => Nat.Coprime p q))
  have hbij : ((Finset.univ : Finset (Fin (n + 1))).biUnion (interX n)).card = F.card := by
    refine Finset.card_bij (fun x _ => (⟨x.den, x.num.natAbs⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_
    · intro x hx
      rw [mem_biUnion_interX_iff] at hx
      rcases hx with ⟨hxpos, hxlt1, hden_le, hndvd⟩
      have hnum_pos : 0 < x.num := Rat.num_pos.mpr hxpos
      have hp_lt_q : x.num.natAbs < x.den := by
        have hq : ((x.num.natAbs : ℕ) : ℚ) / (x.den : ℚ) < 1 := by
          have hnum : (x.num.natAbs : ℤ) = x.num := Int.natAbs_of_nonneg (le_of_lt hnum_pos)
          have hq' : ((x.num.natAbs : ℕ) : ℚ) = (x.num : ℚ) := by
            rw [← Int.cast_natCast, hnum]
          rw [hq', Rat.num_div_den]
          exact hxlt1
        have : ((x.num.natAbs : ℕ) : ℚ) < (x.den : ℚ) :=
          (div_lt_one (by exact_mod_cast x.den_pos)).mp hq
        exact_mod_cast this
      simp only [F, D, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      exact ⟨⟨⟨x.den_pos, hden_le⟩, hndvd⟩, ⟨hp_lt_q, x.reduced⟩⟩
    · intro x₁ hx₁ x₂ hx₂ hEq
      rw [mem_biUnion_interX_iff] at hx₁ hx₂
      have hden : x₁.den = x₂.den := congrArg Sigma.fst hEq
      have hnumAbs : x₁.num.natAbs = x₂.num.natAbs := by
        have := congrArg Sigma.snd hEq
        simpa using this
      have hnum : x₁.num = x₂.num := by
        have h1 : 0 ≤ x₁.num := le_of_lt (Rat.num_pos.mpr hx₁.1)
        have h2 : 0 ≤ x₂.num := le_of_lt (Rat.num_pos.mpr hx₂.1)
        omega
      exact Rat.ext hnum hden
    · intro qp hqp
      simp only [F, D, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hqp
      rcases hqp with ⟨⟨⟨hq1, hqn⟩, hndvd⟩, ⟨hpq, hcop⟩⟩
      have hqne1 : qp.1 ≠ 1 := by
        intro h1; exact hndvd (h1 ▸ one_dvd (n + 1))
      have hppos : 0 < qp.2 := by
        by_contra h0
        have hp0 : qp.2 = 0 := by omega
        rw [hp0, Nat.coprime_zero_left] at hcop
        exact hqne1 hcop
      let x : ℚ :=
        { num := (qp.2 : ℤ)
          den := qp.1
          den_nz := by omega
          reduced := by simpa using hcop }
      have hx_eq : x = (qp.2 : ℚ) / (qp.1 : ℚ) := by
        rw [← Rat.num_div_den x]
        simp [x]
      have hxpos : 0 < x := by
        rw [hx_eq]; positivity
      have hxlt1 : x < 1 := by
        rw [hx_eq, div_lt_one (by exact_mod_cast hq1)]
        exact_mod_cast hpq
      refine ⟨x, ?_, ?_⟩
      · rw [mem_biUnion_interX_iff]
        exact ⟨hxpos, hxlt1, hqn, hndvd⟩
      · ext
        · rfl
        · simp [x]
  rw [hbij, Finset.card_sigma]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext p
  simp [Nat.coprime_comm]

lemma sum_crossCells_eq_sum_totient (n : ℕ) :
    ∑ k : Fin (n + 1), (crossCells n k).card =
      ∑ j ∈ Finset.range (n + 1), Nat.totient (j + 1) := by
  have h1 : ∑ k : Fin (n + 1), (crossCells n k).card =
      ∑ k : Fin (n + 1), (1 + (interX n k).card) :=
    Finset.sum_congr rfl fun k _ => card_crossCells_eq_succ_card_interX n k
  rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul, mul_one]
  rw [← Finset.card_biUnion (interX_pairwiseDisjoint n), card_biUnion_interX]
  have hdiv : (n + 1).divisors = (Finset.Icc 1 (n + 1)).filter (fun q => q ∣ n + 1) := by
    ext q
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc, ne_eq,
      Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, and_true]
    constructor
    · intro hdvd
      exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), Nat.le_of_dvd (by omega) hdvd⟩, hdvd⟩
    · exact fun h => h.2
  have hndvd_eq : (Finset.Icc 1 n).filter (fun q => ¬ (q ∣ n + 1)) =
      (Finset.Icc 1 (n + 1)).filter (fun q => ¬ (q ∣ n + 1)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hnd⟩
      exact ⟨⟨h1, by omega⟩, hnd⟩
    · rintro ⟨⟨h1, h2⟩, hnd⟩
      have hne : q ≠ n + 1 := fun heq => hnd (heq ▸ dvd_refl _)
      exact ⟨⟨h1, by omega⟩, hnd⟩
  have hsplit : ∑ q ∈ Finset.Icc 1 (n + 1), Nat.totient q =
      (∑ q ∈ (Finset.Icc 1 (n + 1)).filter (fun q => q ∣ n + 1), Nat.totient q) +
      (∑ q ∈ (Finset.Icc 1 (n + 1)).filter (fun q => ¬ (q ∣ n + 1)), Nat.totient q) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  rw [← hdiv, Nat.sum_totient (n + 1), ← hndvd_eq] at hsplit
  rw [← hsplit]
  refine Finset.sum_bij (fun q _ => q - 1) ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_Icc] at hq
    rw [Finset.mem_range]
    omega
  · intro q₁ hq₁ q₂ hq₂ hEq
    rw [Finset.mem_Icc] at hq₁ hq₂
    omega
  · intro j hj
    rw [Finset.mem_range] at hj
    exact ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro q hq
    rw [Finset.mem_Icc] at hq
    have : q - 1 + 1 = q := by omega
    rw [this]

lemma card_activeSigs_formula (n : ℕ) :
    (activeSigs n).card =
      1 + ∑ j ∈ Finset.range n, (n - j) * Nat.totient (j + 1) := by
  induction n with
  | zero =>
    simp [card_activeSigs_zero]
  | succ n ih =>
    rw [card_activeSigs_succ_eq_add_sum_crossCells, ih, sum_crossCells_eq_sum_totient]
    rw [Finset.sum_range_succ (fun j => (n + 1 - j) * Nat.totient (j + 1)) n]
    rw [Finset.sum_range_succ (fun j => Nat.totient (j + 1)) n]
    have hsum :
        (∑ j ∈ Finset.range n, (n - j) * Nat.totient (j + 1)) +
        (∑ j ∈ Finset.range n, Nat.totient (j + 1)) =
        ∑ j ∈ Finset.range n, (n + 1 - j) * Nat.totient (j + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hsub : n + 1 - j = (n - j) + 1 := by omega
      rw [hsub, add_mul, one_mul]
    have hlast : (n + 1 - n) * Nat.totient (n + 1) = Nat.totient (n + 1) := by simp
    omega

end OMA.A005598Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a005598.main := by
  intro n
  rw [OMA.A005598Proof.ncard_fanRegions_eq_card_activeSigs,
      OMA.A005598Proof.card_activeSigs_formula]
