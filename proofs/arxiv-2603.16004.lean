import OMAStatements.S_arxiv_2603_16004

namespace Arxiv260316004

open Finset OMA.S_arxiv_2603_16004

-- ============================================================================
-- Section 1: Basic Properties of reverse, Contains, and Order Uniqueness
-- ============================================================================

private lemma reverse_reverse {m : ℕ} (π : Equiv.Perm (Fin m)) :
    reverse (reverse π) = π := by
  ext i
  simp [reverse, Fin.rev_rev]

private lemma reverse_ne_self {k : ℕ} (hk : 2 ≤ k) (p : Equiv.Perm (Fin k)) :
    reverse p ≠ p := by
  intro heq
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨k - 1, by omega⟩
  have hrev : Fin.rev i0 = i1 := by
    apply Fin.ext
    simp [Fin.val_rev, i0, i1]
  have h1 : (reverse p) i0 = p i0 := congrArg (fun q : Equiv.Perm (Fin k) => q i0) heq
  simp only [reverse, Equiv.trans_apply, Fin.revPerm_apply, hrev] at h1
  have h2 : i1 = i0 := p.injective h1
  have hval : k - 1 = 0 := congrArg Fin.val h2
  omega

private lemma rev_lt_rev_iff {m : ℕ} (i j : Fin m) :
    Fin.rev i < Fin.rev j ↔ j < i := by
  simp only [Fin.lt_def, Fin.val_rev]
  omega

private lemma contains_reverse_of {n k : ℕ} {π : Equiv.Perm (Fin n)} {p : Equiv.Perm (Fin k)}
    (h : Contains π p) : Contains (reverse π) (reverse p) := by
  rcases h with ⟨pos, hmono, hord⟩
  refine ⟨fun i => Fin.rev (pos (Fin.rev i)), ?_, ?_⟩
  · intro i j hij
    exact (rev_lt_rev_iff _ _).mpr (hmono ((rev_lt_rev_iff _ _).mpr hij))
  · intro i j
    simp only [reverse, Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_rev]
    exact hord (Fin.rev i) (Fin.rev j)

private lemma contains_reverse_iff {n k : ℕ} (π : Equiv.Perm (Fin n)) (p : Equiv.Perm (Fin k)) :
    Contains (reverse π) (reverse p) ↔ Contains π p :=
  ⟨fun h => by simpa only [reverse_reverse] using contains_reverse_of h, contains_reverse_of⟩

private lemma lt_iff_of_lt_imp {k : ℕ} {α : Type*} [LinearOrder α]
    {f : Fin k → α} (hf : Function.Injective f) (q : Equiv.Perm (Fin k))
    (h : ∀ i j : Fin k, i < j → (f i < f j ↔ q i < q j)) :
    ∀ i j : Fin k, f i < f j ↔ q i < q j := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact h i j hij
  · simp
  · have hji' := h j i hji
    have hne_f : f i ≠ f j := fun heq => (ne_of_gt hji) (hf heq)
    have hne_q : q i ≠ q j := fun heq => (ne_of_gt hji) (q.injective heq)
    constructor
    · intro hlt
      have hnot : ¬ f j < f i := not_lt_of_gt hlt
      have hnotq : ¬ q j < q i := fun hq => hnot (hji'.mpr hq)
      exact lt_of_le_of_ne (le_of_not_gt hnotq) hne_q
    · intro hlt
      have hnot : ¬ q j < q i := not_lt_of_gt hlt
      have hnotf : ¬ f j < f i := fun hf' => hnot (hji'.mp hf')
      exact lt_of_le_of_ne (le_of_not_gt hnotf) hne_f

private lemma card_filter_lt_perm {k : ℕ} (p : Equiv.Perm (Fin k)) (i : Fin k) :
    (Finset.univ.filter fun j : Fin k => p j < p i).card = (p i).val := by
  have hbij : (Finset.univ.filter fun j : Fin k => p j < p i).card =
      (Finset.range (p i).val).card := by
    refine Finset.card_bij (fun j _ => (p j).val) ?_ ?_ ?_
    · intro j hj
      rw [mem_filter] at hj
      exact mem_range.mpr hj.2
    · intro j₁ _ j₂ _ heq
      exact p.injective (Fin.ext heq)
    · intro m hm
      rw [mem_range] at hm
      let y : Fin k := ⟨m, lt_trans hm (p i).isLt⟩
      refine ⟨p.symm y, ?_, ?_⟩
      · rw [mem_filter]
        exact ⟨mem_univ _, by simpa [Fin.lt_def, y] using hm⟩
      · simp [y]
  rw [hbij, Finset.card_range]

private lemma perm_eq_of_lt_iff {k : ℕ} {p₁ p₂ : Equiv.Perm (Fin k)}
    (h : ∀ i j : Fin k, p₁ i < p₁ j ↔ p₂ i < p₂ j) : p₁ = p₂ := by
  ext i
  rw [← card_filter_lt_perm p₁ i, ← card_filter_lt_perm p₂ i]
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and]
  exact h j i

private def permCast {m₁ m₂ : ℕ} (hm : m₁ = m₂) (σ : Equiv.Perm (Fin m₁)) :
    Equiv.Perm (Fin m₂) :=
  (finCongr hm).symm.trans (σ.trans (finCongr hm))

private lemma contains_permCast_iff {m₁ m₂ k : ℕ} (hm : m₁ = m₂)
    (σ : Equiv.Perm (Fin m₁)) (q : Equiv.Perm (Fin k)) :
    Contains (permCast hm σ) q ↔ Contains σ q := by
  subst hm
  simp [permCast]

-- ============================================================================
-- Section 2: Self-Contained Erdős–Szekeres Monotone Subsequence Lemma
-- ============================================================================

private def lisLen {N n : ℕ} (f : Fin N → Fin n) : ℕ → ℕ
  | 0 => 1
  | x + 1 =>
    1 + (Finset.univ.filter fun y : Fin (x + 1) =>
          if h : y.val < N ∧ x + 1 < N then f ⟨y.val, h.1⟩ < f ⟨x + 1, h.2⟩ else False).sup
        (fun y : Fin (x + 1) => lisLen f y.val)
termination_by x => x
decreasing_by
  exact y.isLt

private lemma lisLen_pos {N n : ℕ} (f : Fin N → Fin n) (x : ℕ) :
    1 ≤ lisLen f x := by
  cases x with
  | zero => rw [lisLen]
  | succ x' => rw [lisLen]; omega

private lemma lisLen_lt_step {N n : ℕ} (f : Fin N → Fin n)
    {y x : ℕ} (hyx : y < x) (hx : x < N) (hf : f ⟨y, lt_trans hyx hx⟩ < f ⟨x, hx⟩) :
    lisLen f y + 1 ≤ lisLen f x := by
  obtain ⟨x', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
  rw [lisLen]
  let y' : Fin (x' + 1) := ⟨y, hyx⟩
  have hmem : y' ∈ Finset.univ.filter fun z : Fin (x' + 1) =>
      if h : z.val < N ∧ x' + 1 < N then f ⟨z.val, h.1⟩ < f ⟨x' + 1, h.2⟩ else False := by
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hlt : y'.val < N ∧ x' + 1 < N := ⟨lt_trans hyx hx, hx⟩
    simp only [hlt]
    exact hf
  have hle : lisLen f y'.val ≤ (Finset.univ.filter fun z : Fin (x' + 1) =>
      if h : z.val < N ∧ x' + 1 < N then f ⟨z.val, h.1⟩ < f ⟨x' + 1, h.2⟩ else False).sup
      (fun z : Fin (x' + 1) => lisLen f z.val) :=
    Finset.le_sup (f := fun z : Fin (x' + 1) => lisLen f z.val) hmem
  dsimp only [y'] at hle
  omega

private lemma lisLen_chain {N n : ℕ} (f : Fin N → Fin n) :
    ∀ x : ℕ, ∀ hx : x < N,
      ∃ c : Fin (lisLen f x) → Fin N,
        StrictMono c ∧ StrictMono (f ∘ c) ∧
        c ⟨lisLen f x - 1, by have := lisLen_pos f x; omega⟩ = ⟨x, hx⟩ := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro hx
    cases x with
    | zero =>
      have hlen0 : lisLen f 0 = 1 := by rw [lisLen]
      refine ⟨fun _ => ⟨0, hx⟩, ?_, ?_, rfl⟩
      · intro i j hij; have := j.isLt; omega
      · intro i j hij; have := j.isLt; omega
    | succ x' =>
      set S : Finset (Fin (x' + 1)) := Finset.univ.filter fun y : Fin (x' + 1) =>
        if h : y.val < N ∧ x' + 1 < N then f ⟨y.val, h.1⟩ < f ⟨x' + 1, h.2⟩ else False
      by_cases hS : S.Nonempty
      · obtain ⟨y, hyS, hsup⟩ :=
          Finset.exists_mem_eq_sup S hS (fun z : Fin (x' + 1) => lisLen f z.val)
        have hy_lt : y.val < x' + 1 := y.isLt
        have hyN : y.val < N := lt_trans hy_lt hx
        have hfy : f ⟨y.val, hyN⟩ < f ⟨x' + 1, hx⟩ := by
          have hp := (mem_filter.mp hyS).2
          simp only [hyN, hx, and_self, ↓reduceDIte] at hp
          exact hp
        have hlen : lisLen f (x' + 1) = lisLen f y.val + 1 := by
          rw [lisLen]
          change 1 + S.sup (fun z : Fin (x' + 1) => lisLen f z.val) = lisLen f y.val + 1
          rw [← hsup]
          omega
        obtain ⟨c₀, hc₀_mono, hc₀_fmono, hc₀_last⟩ := ih y.val hy_lt hyN
        have hpos_y : 1 ≤ lisLen f y.val := lisLen_pos f y.val
        let c : Fin (lisLen f (x' + 1)) → Fin N := fun i =>
          if hi : i.val < lisLen f y.val then c₀ ⟨i.val, hi⟩ else ⟨x' + 1, hx⟩
        refine ⟨c, ?_, ?_, ?_⟩
        · intro i j hij
          by_cases hj : j.val < lisLen f y.val
          · have hi : i.val < lisLen f y.val := lt_trans hij hj
            simp only [c, hi, hj, ↓reduceDIte]
            exact hc₀_mono (show (⟨i.val, hi⟩ : Fin (lisLen f y.val)) < ⟨j.val, hj⟩ from hij)
          · have hi : i.val < lisLen f y.val := by have := j.isLt; omega
            simp only [c, hi, hj, ↓reduceDIte]
            have hle : c₀ ⟨i.val, hi⟩ ≤ c₀ ⟨lisLen f y.val - 1, by omega⟩ :=
              hc₀_mono.monotone (show (⟨i.val, hi⟩ : Fin (lisLen f y.val)) ≤ ⟨lisLen f y.val - 1, by omega⟩ from by
                simp only [Fin.le_def]; omega)
            rw [hc₀_last] at hle
            exact lt_of_le_of_lt hle (show (⟨y.val, hyN⟩ : Fin N) < ⟨x' + 1, hx⟩ from hy_lt)
        · intro i j hij
          by_cases hj : j.val < lisLen f y.val
          · have hi : i.val < lisLen f y.val := lt_trans hij hj
            simp only [Function.comp_apply, c, hi, hj, ↓reduceDIte]
            exact hc₀_fmono (show (⟨i.val, hi⟩ : Fin (lisLen f y.val)) < ⟨j.val, hj⟩ from hij)
          · have hi : i.val < lisLen f y.val := by have := j.isLt; omega
            simp only [Function.comp_apply, c, hi, hj, ↓reduceDIte]
            have hle : f (c₀ ⟨i.val, hi⟩) ≤ f (c₀ ⟨lisLen f y.val - 1, by omega⟩) :=
              hc₀_fmono.monotone (show (⟨i.val, hi⟩ : Fin (lisLen f y.val)) ≤ ⟨lisLen f y.val - 1, by omega⟩ from by
                simp only [Fin.le_def]; omega)
            rw [hc₀_last] at hle
            exact lt_of_le_of_lt hle hfy
        · simp only [c]
          have hnot : ¬ (lisLen f (x' + 1) - 1 < lisLen f y.val) := by omega
          simp only [hnot, ↓reduceDIte]
      · have hS_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        have hlen : lisLen f (x' + 1) = 1 := by
          rw [lisLen]
          change 1 + S.sup (fun z : Fin (x' + 1) => lisLen f z.val) = 1
          rw [hS_empty, Finset.sup_empty]
          rfl
        refine ⟨fun _ => ⟨x' + 1, hx⟩, ?_, ?_, rfl⟩
        · intro i j hij; have := j.isLt; omega
        · intro i j hij; have := j.isLt; omega

private lemma erdos_szekeres {k N n : ℕ} (hk : 1 ≤ k) (hN : (k - 1) ^ 2 + 1 ≤ N)
    (f : Fin N → Fin n) (hf : Function.Injective f) :
    ∃ (g : Fin k → Fin N) (ε : Bool),
      StrictMono g ∧ ∀ a b : Fin k, a < b → (f (g a) < f (g b) ↔ ε = true) := by
  let f' : Fin N → Fin n := fun i => Fin.rev (f i)
  by_cases hinc : ∃ x : Fin N, k ≤ lisLen f x.val
  · rcases hinc with ⟨x, hkx⟩
    obtain ⟨c, hc_mono, hc_fmono, _⟩ := lisLen_chain f x.val x.isLt
    let g : Fin k → Fin N := fun a => c ⟨a.val, lt_of_lt_of_le a.isLt hkx⟩
    refine ⟨g, true, ?_, ?_⟩
    · intro a b hab
      exact hc_mono (show (⟨a.val, lt_of_lt_of_le a.isLt hkx⟩ : Fin (lisLen f x.val)) <
        ⟨b.val, lt_of_lt_of_le b.isLt hkx⟩ from hab)
    · intro a b hab
      simp only [iff_true]
      exact hc_fmono (show (⟨a.val, lt_of_lt_of_le a.isLt hkx⟩ : Fin (lisLen f x.val)) <
        ⟨b.val, lt_of_lt_of_le b.isLt hkx⟩ from hab)
  · by_cases hdec : ∃ x : Fin N, k ≤ lisLen f' x.val
    · rcases hdec with ⟨x, hkx⟩
      obtain ⟨c, hc_mono, hc_fmono, _⟩ := lisLen_chain f' x.val x.isLt
      let g : Fin k → Fin N := fun a => c ⟨a.val, lt_of_lt_of_le a.isLt hkx⟩
      refine ⟨g, false, ?_, ?_⟩
      · intro a b hab
        exact hc_mono (show (⟨a.val, lt_of_lt_of_le a.isLt hkx⟩ : Fin (lisLen f' x.val)) <
          ⟨b.val, lt_of_lt_of_le b.isLt hkx⟩ from hab)
      · intro a b hab
        have hrev_lt : Fin.rev (f (g a)) < Fin.rev (f (g b)) :=
          hc_fmono (show (⟨a.val, lt_of_lt_of_le a.isLt hkx⟩ : Fin (lisLen f' x.val)) <
            ⟨b.val, lt_of_lt_of_le b.isLt hkx⟩ from hab)
        have hgt : f (g b) < f (g a) := (rev_lt_rev_iff _ _).mp hrev_lt
        simp only [Bool.false_eq_true, iff_false]
        exact not_lt_of_gt hgt
    · exfalso
      have hinc_lt : ∀ x : Fin N, lisLen f x.val - 1 < k - 1 := by
        intro x
        have h1 : ¬ k ≤ lisLen f x.val := fun h => hinc ⟨x, h⟩
        have h2 := lisLen_pos f x.val
        omega
      have hdec_lt : ∀ x : Fin N, lisLen f' x.val - 1 < k - 1 := by
        intro x
        have h1 : ¬ k ≤ lisLen f' x.val := fun h => hdec ⟨x, h⟩
        have h2 := lisLen_pos f' x.val
        omega
      let Φ : Fin N → Fin (k - 1) × Fin (k - 1) :=
        fun x => (⟨lisLen f x.val - 1, hinc_lt x⟩, ⟨lisLen f' x.val - 1, hdec_lt x⟩)
      have hcard : Fintype.card (Fin (k - 1) × Fin (k - 1)) < Fintype.card (Fin N) := by
        simp only [Fintype.card_prod, Fintype.card_fin]
        have : (k - 1) ^ 2 = (k - 1) * (k - 1) := sq (k - 1)
        omega
      obtain ⟨x, y, hne, hΦ⟩ := Fintype.exists_ne_map_eq_of_card_lt Φ hcard
      have hpair : lisLen f x.val = lisLen f y.val ∧ lisLen f' x.val = lisLen f' y.val := by
        have h1 := congrArg (fun p : Fin (k - 1) × Fin (k - 1) => p.1.val) hΦ
        have h2 := congrArg (fun p : Fin (k - 1) × Fin (k - 1) => p.2.val) hΦ
        have hx1 := lisLen_pos f x.val
        have hy1 := lisLen_pos f y.val
        have hx2 := lisLen_pos f' x.val
        have hy2 := lisLen_pos f' y.val
        simp only [Φ] at h1 h2
        omega
      have hord_contra : ∀ u v : Fin N, u < v →
          lisLen f u.val = lisLen f v.val → lisLen f' u.val = lisLen f' v.val → False := by
        intro u v huv heq1 heq2
        have hne_f : f u ≠ f v := fun h => (ne_of_lt huv) (hf h)
        rcases lt_or_gt_of_ne hne_f with hfu | hfv
        · have hstep := lisLen_lt_step f (y := u.val) (x := v.val) huv v.isLt hfu
          omega
        · have hrev : f' u < f' v := (rev_lt_rev_iff _ _).mpr hfv
          have hstep := lisLen_lt_step f' (y := u.val) (x := v.val) huv v.isLt hrev
          omega
      rcases lt_or_gt_of_ne hne with hxy | hyx
      · exact hord_contra x y hxy hpair.1 hpair.2
      · exact hord_contra y x hyx hpair.1.symm hpair.2.symm

-- ============================================================================
-- Section 3: Grid-Cell Pigeonhole and Single-Cell Monotone Block Extraction
-- ============================================================================

private lemma same_filter_card_lt_iff {n : ℕ} (I : Finset (Fin n)) (φ : Fin n → Fin n)
    (hφ : Function.Injective φ) {x y : Fin n} (hx : x ∉ I) (hy : y ∉ I)
    (hcard : (I.filter fun z => φ z < φ x).card = (I.filter fun z => φ z < φ y).card)
    {z : Fin n} (hz : z ∈ I) : φ z < φ x ↔ φ z < φ y := by
  have hdir : ∀ a b : Fin n, a ∉ I → b ∉ I →
      (I.filter fun w => φ w < φ a).card = (I.filter fun w => φ w < φ b).card →
      φ z < φ a → φ z < φ b := by
    intro a b _ hb hc hza
    by_contra hnot
    have hne : φ z ≠ φ b := fun h => hb (hφ h ▸ hz)
    have hba : φ b < φ z := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)
    have hss : (I.filter fun w => φ w < φ b) ⊂ (I.filter fun w => φ w < φ a) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro w hw
        rw [mem_filter] at hw ⊢
        exact ⟨hw.1, lt_trans (lt_trans hw.2 hba) hza⟩
      · intro heq
        have hzA : z ∈ I.filter fun w => φ w < φ a := mem_filter.mpr ⟨hz, hza⟩
        rw [← heq, mem_filter] at hzA
        exact hnot hzA.2
    have hlt := Finset.card_lt_card hss
    omega
  exact ⟨hdir x y hx hy hcard, hdir y x hy hx hcard.symm⟩

private lemma single_cell_monotone_block {k n : ℕ} (hk : 2 ≤ k)
    (hn : k + (k + 1) ^ 2 * (k - 1) ^ 2 + 1 ≤ n)
    (π : Equiv.Perm (Fin n)) (I : Finset (Fin n)) (hI : I.card = k) :
    ∃ (ιB : Fin k → Fin n) (ε : Bool),
      StrictMono ιB ∧
      (∀ a : Fin k, ιB a ∉ I) ∧
      (∀ a : Fin k, ∀ z ∈ I,
        (z < ιB a ↔ z < ιB ⟨0, by omega⟩) ∧
        (π z < π (ιB a) ↔ π z < π (ιB ⟨0, by omega⟩))) ∧
      (∀ a b : Fin k, a < b → (π (ιB a) < π (ιB b) ↔ ε = true)) := by
  let cell : Fin n → Fin (k + 1) × Fin (k + 1) := fun x =>
    (⟨(I.filter fun z => z < x).card, by
        have := Finset.card_filter_le I (fun z => z < x); omega⟩,
     ⟨(I.filter fun z => π z < π x).card, by
        have := Finset.card_filter_le I (fun z => π z < π x); omega⟩)
  let R : Finset (Fin n) := Finset.univ \ I
  have hRcard : R.card = n - k := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hI]
  have hsum : ∑ c : Fin (k + 1) × Fin (k + 1), (R.filter fun x => cell x = c).card = R.card := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := cell) (t := Finset.univ) (fun _ _ => mem_univ _)]
  have hex_cell : ∃ c0 : Fin (k + 1) × Fin (k + 1),
      (k - 1) ^ 2 + 1 ≤ (R.filter fun x => cell x = c0).card := by
    by_contra hnone
    have hall : ∀ c : Fin (k + 1) × Fin (k + 1),
        (R.filter fun x => cell x = c).card ≤ (k - 1) ^ 2 := by
      intro c
      by_contra hgt
      exact hnone ⟨c, by omega⟩
    have hle : R.card ≤ (k + 1) ^ 2 * (k - 1) ^ 2 := by
      calc R.card = ∑ c : Fin (k + 1) × Fin (k + 1), (R.filter fun x => cell x = c).card := hsum.symm
        _ ≤ ∑ _c : Fin (k + 1) × Fin (k + 1), (k - 1) ^ 2 := Finset.sum_le_sum fun c _ => hall c
        _ = (k + 1) ^ 2 * (k - 1) ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              smul_eq_mul, sq]
    omega
  rcases hex_cell with ⟨c0, hc0⟩
  let C : Finset (Fin n) := R.filter fun x => cell x = c0
  let eC : Fin C.card ≃o C := C.orderIsoOfFin rfl
  let f : Fin C.card → Fin n := fun i => π (eC i).val
  have hf_inj : Function.Injective f := fun i j hij =>
    eC.injective (Subtype.ext (π.injective hij))
  obtain ⟨g, ε, hg_mono, hg_ord⟩ := erdos_szekeres (by omega : 1 ≤ k) hc0 f hf_inj
  let ιB : Fin k → Fin n := fun a => (eC (g a)).val
  refine ⟨ιB, ε, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact eC.strictMono (hg_mono hab)
  · intro a
    have hmemC : ιB a ∈ C := (eC (g a)).prop
    have hmemR : ιB a ∈ R := (mem_filter.mp hmemC).1
    exact (mem_sdiff.mp hmemR).2
  · intro a z hz
    have hmemA : ιB a ∈ C := (eC (g a)).prop
    have hmem0 : ιB ⟨0, by omega⟩ ∈ C := (eC (g ⟨0, by omega⟩)).prop
    have hnotA : ιB a ∉ I := (mem_sdiff.mp (mem_filter.mp hmemA).1).2
    have hnot0 : ιB ⟨0, by omega⟩ ∉ I := (mem_sdiff.mp (mem_filter.mp hmem0).1).2
    have hcell_eq : cell (ιB a) = cell (ιB ⟨0, by omega⟩) := by
      rw [(mem_filter.mp hmemA).2, (mem_filter.mp hmem0).2]
    have hc1 : (I.filter fun w => w < ιB a).card = (I.filter fun w => w < ιB ⟨0, by omega⟩).card :=
      congrArg (fun p : Fin (k + 1) × Fin (k + 1) => p.1.val) hcell_eq
    have hc2 : (I.filter fun w => π w < π (ιB a)).card =
        (I.filter fun w => π w < π (ιB ⟨0, by omega⟩)).card :=
      congrArg (fun p : Fin (k + 1) × Fin (k + 1) => p.2.val) hcell_eq
    exact ⟨same_filter_card_lt_iff I id Function.injective_id hnotA hnot0 hc1 hz,
           same_filter_card_lt_iff I π π.injective hnotA hnot0 hc2 hz⟩
  · intro a b hab
    exact hg_ord a b hab

-- ============================================================================
-- Section 4: Block Inflation σ(S, m) and Its Four Structural Lemmas
-- ============================================================================

section BlockInflation

variable {n k : ℕ} (π : Equiv.Perm (Fin n)) (b0 : Fin n) (ε : Bool)

private def posKey (S : Finset (Fin n)) (m : ℕ) :
    {x : Fin n // x ∈ S} ⊕ Fin m → ℤ ×ₗ ℤ
  | Sum.inl x => toLex ((x.val.val : ℤ), (0 : ℤ))
  | Sum.inr j => toLex ((b0.val : ℤ), (j.val : ℤ) + 1)

private def valKey (S : Finset (Fin n)) (m : ℕ) :
    {x : Fin n // x ∈ S} ⊕ Fin m → ℤ ×ₗ ℤ
  | Sum.inl x => toLex (((π x.val).val : ℤ), (0 : ℤ))
  | Sum.inr j => toLex (((π b0).val : ℤ), if ε then (j.val : ℤ) + 1 else -((j.val : ℤ) + 1))

private lemma posKey_injective (S : Finset (Fin n)) (m : ℕ) :
    Function.Injective (posKey b0 S m) := by
  intro a b hab
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      simp only [posKey, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hab
      exact congrArg Sum.inl (Subtype.ext (Fin.ext (by omega)))
    | inr j =>
      simp only [posKey, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hab
      omega
  | inr i =>
    cases b with
    | inl y =>
      simp only [posKey, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hab
      omega
    | inr j =>
      simp only [posKey, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hab
      exact congrArg Sum.inr (Fin.ext (by omega))

private lemma valKey_injective (S : Finset (Fin n)) (m : ℕ) :
    Function.Injective (valKey π b0 ε S m) := by
  intro a b hab
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      simp only [valKey, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hab
      exact congrArg Sum.inl (Subtype.ext (π.injective (Fin.ext (by omega))))
    | inr j =>
      simp only [valKey, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hab
      split_ifs at hab <;> omega
  | inr i =>
    cases b with
    | inl y =>
      simp only [valKey, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hab
      split_ifs at hab <;> omega
    | inr j =>
      simp only [valKey, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hab
      split_ifs at hab <;> exact congrArg Sum.inr (Fin.ext (by omega))

private lemma posKey_inl_inl {S : Finset (Fin n)} {m : ℕ}
    (x y : {x : Fin n // x ∈ S}) :
    posKey b0 S m (Sum.inl x) < posKey b0 S m (Sum.inl y) ↔ x.val < y.val := by
  simp only [posKey, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, and_false, or_false,
    Nat.cast_lt, Fin.lt_def]

private lemma posKey_inl_inr {I S : Finset (Fin n)} {m : ℕ} (hb0 : b0 ∉ I) (hSI : S ⊆ I)
    (x : {x : Fin n // x ∈ S}) (j : Fin m) :
    posKey b0 S m (Sum.inl x) < posKey b0 S m (Sum.inr j) ↔ x.val < b0 := by
  have hne : x.val.val ≠ b0.val := fun h => hb0 (hSI (Fin.ext h ▸ x.prop))
  simp only [posKey, Prod.Lex.toLex_lt_toLex, Nat.cast_lt, Nat.cast_inj, Fin.lt_def, hne,
    false_and, or_false]

private lemma posKey_inr_inl {I S : Finset (Fin n)} {m : ℕ} (hb0 : b0 ∉ I) (hSI : S ⊆ I)
    (j : Fin m) (x : {x : Fin n // x ∈ S}) :
    posKey b0 S m (Sum.inr j) < posKey b0 S m (Sum.inl x) ↔ b0 < x.val := by
  have hne : b0.val ≠ x.val.val := fun h => hb0 (hSI (Fin.ext h.symm ▸ x.prop))
  simp only [posKey, Prod.Lex.toLex_lt_toLex, Nat.cast_lt, Nat.cast_inj, Fin.lt_def, hne,
    false_and, or_false]

private lemma posKey_inr_inr {S : Finset (Fin n)} {m : ℕ} (i j : Fin m) :
    posKey b0 S m (Sum.inr i) < posKey b0 S m (Sum.inr j) ↔ i < j := by
  simp only [posKey, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or, Fin.lt_def]
  omega

private lemma valKey_inl_inl {S : Finset (Fin n)} {m : ℕ}
    (x y : {x : Fin n // x ∈ S}) :
    valKey π b0 ε S m (Sum.inl x) < valKey π b0 ε S m (Sum.inl y) ↔ π x.val < π y.val := by
  simp only [valKey, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, and_false, or_false,
    Nat.cast_lt, Fin.lt_def]

private lemma valKey_inl_inr {I S : Finset (Fin n)} {m : ℕ} (hb0 : b0 ∉ I) (hSI : S ⊆ I)
    (x : {x : Fin n // x ∈ S}) (j : Fin m) :
    valKey π b0 ε S m (Sum.inl x) < valKey π b0 ε S m (Sum.inr j) ↔ π x.val < π b0 := by
  have hne : (π x.val).val ≠ (π b0).val := fun h => hb0 (hSI (π.injective (Fin.ext h) ▸ x.prop))
  simp only [valKey, Prod.Lex.toLex_lt_toLex, Nat.cast_lt, Nat.cast_inj, Fin.lt_def, hne,
    false_and, or_false]

private lemma valKey_inr_inl {I S : Finset (Fin n)} {m : ℕ} (hb0 : b0 ∉ I) (hSI : S ⊆ I)
    (j : Fin m) (x : {x : Fin n // x ∈ S}) :
    valKey π b0 ε S m (Sum.inr j) < valKey π b0 ε S m (Sum.inl x) ↔ π b0 < π x.val := by
  have hne : (π b0).val ≠ (π x.val).val := fun h => hb0 (hSI (π.injective (Fin.ext h.symm) ▸ x.prop))
  simp only [valKey, Prod.Lex.toLex_lt_toLex, Nat.cast_lt, Nat.cast_inj, Fin.lt_def, hne,
    false_and, or_false]

private lemma valKey_inr_inr_of_lt {S : Finset (Fin n)} {m : ℕ} {i j : Fin m} (hij : i < j) :
    valKey π b0 ε S m (Sum.inr i) < valKey π b0 ε S m (Sum.inr j) ↔ ε = true := by
  have hlt : (i.val : ℤ) < (j.val : ℤ) := by exact_mod_cast (show i.val < j.val from hij)
  simp only [valKey, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or]
  cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [iff_false]; omega
  · simp only [iff_true]; omega

private noncomputable def keyOrderEquiv {α : Type*} [Fintype α] {M : ℕ}
    (key : α → ℤ ×ₗ ℤ) (hinj : Function.Injective key) (hcard : Fintype.card α = M) :
    Fin M ≃ α := by
  let Sset : Finset (ℤ ×ₗ ℤ) := Finset.univ.image key
  have hScard : Sset.card = M := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
  let e1 : Fin M ≃ Sset := (Sset.orderIsoOfFin hScard).toEquiv
  let e2 : α ≃ Sset := Equiv.ofBijective (fun a => ⟨key a, mem_image_of_mem key (mem_univ a)⟩)
    ⟨fun a b h => hinj (congrArg Subtype.val h),
     fun ⟨y, hy⟩ => by
       obtain ⟨a, _, rfl⟩ := mem_image.mp hy
       exact ⟨a, rfl⟩⟩
  exact e1.trans e2.symm

private lemma keyOrderEquiv_lt_iff {α : Type*} [Fintype α] {M : ℕ}
    (key : α → ℤ ×ₗ ℤ) (hinj : Function.Injective key) (hcard : Fintype.card α = M)
    (i j : Fin M) :
    i < j ↔ key (keyOrderEquiv key hinj hcard i) < key (keyOrderEquiv key hinj hcard j) := by
  unfold keyOrderEquiv
  dsimp only [Equiv.trans_apply]
  let Sset : Finset (ℤ ×ₗ ℤ) := Finset.univ.image key
  have hScard : Sset.card = M := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
  let e2 : α ≃ Sset := Equiv.ofBijective (fun a => ⟨key a, mem_image_of_mem key (mem_univ a)⟩)
    ⟨fun a b h => hinj (congrArg Subtype.val h),
     fun ⟨y, hy⟩ => by
       obtain ⟨a, _, rfl⟩ := mem_image.mp hy
       exact ⟨a, rfl⟩⟩
  have hkey : ∀ y : Sset, key (e2.symm y) = y.val := fun y =>
    congrArg Subtype.val (e2.apply_symm_apply y)
  change i < j ↔ key (e2.symm (Sset.orderIsoOfFin hScard i)) < key (e2.symm (Sset.orderIsoOfFin hScard j))
  rw [hkey, hkey]
  exact ((Sset.orderIsoOfFin hScard).lt_iff_lt).symm

private lemma card_sum_type (S : Finset (Fin n)) (m : ℕ) :
    Fintype.card ({x : Fin n // x ∈ S} ⊕ Fin m) = S.card + m := by
  simp [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]

private noncomputable def eP (S : Finset (Fin n)) (m : ℕ) :
    Fin (S.card + m) ≃ {x : Fin n // x ∈ S} ⊕ Fin m :=
  keyOrderEquiv (posKey b0 S m) (posKey_injective b0 S m) (card_sum_type S m)

private noncomputable def eV (S : Finset (Fin n)) (m : ℕ) :
    Fin (S.card + m) ≃ {x : Fin n // x ∈ S} ⊕ Fin m :=
  keyOrderEquiv (valKey π b0 ε S m) (valKey_injective π b0 ε S m) (card_sum_type S m)

private noncomputable def blockPerm (S : Finset (Fin n)) (m : ℕ) :
    Equiv.Perm (Fin (S.card + m)) :=
  (eP b0 S m).trans (eV π b0 ε S m).symm

private lemma eP_lt_iff (S : Finset (Fin n)) (m : ℕ) (i j : Fin (S.card + m)) :
    i < j ↔ posKey b0 S m (eP b0 S m i) < posKey b0 S m (eP b0 S m j) :=
  keyOrderEquiv_lt_iff (posKey b0 S m) (posKey_injective b0 S m) (card_sum_type S m) i j

private lemma eV_lt_iff (S : Finset (Fin n)) (m : ℕ) (i j : Fin (S.card + m)) :
    i < j ↔ valKey π b0 ε S m (eV π b0 ε S m i) < valKey π b0 ε S m (eV π b0 ε S m j) :=
  keyOrderEquiv_lt_iff (valKey π b0 ε S m) (valKey_injective π b0 ε S m) (card_sum_type S m) i j

private lemma blockPerm_lt_iff (S : Finset (Fin n)) (m : ℕ) (i j : Fin (S.card + m)) :
    blockPerm π b0 ε S m i < blockPerm π b0 ε S m j ↔
      valKey π b0 ε S m (eP b0 S m i) < valKey π b0 ε S m (eP b0 S m j) := by
  unfold blockPerm
  simp only [Equiv.trans_apply]
  rw [eV_lt_iff π b0 ε S m, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private lemma contains_blockPerm_iff (S : Finset (Fin n)) (m : ℕ) (q : Equiv.Perm (Fin k)) :
    Contains (blockPerm π b0 ε S m) q ↔
      ∃ f : Fin k → {x : Fin n // x ∈ S} ⊕ Fin m,
        (∀ i j : Fin k, i < j → posKey b0 S m (f i) < posKey b0 S m (f j)) ∧
        (∀ i j : Fin k, valKey π b0 ε S m (f i) < valKey π b0 ε S m (f j) ↔ q i < q j) := by
  constructor
  · rintro ⟨pos, hmono, hord⟩
    refine ⟨fun i => eP b0 S m (pos i), ?_, ?_⟩
    · intro i j hij
      exact (eP_lt_iff b0 S m (pos i) (pos j)).mp (hmono hij)
    · intro i j
      rw [← blockPerm_lt_iff π b0 ε S m (pos i) (pos j)]
      exact hord i j
  · rintro ⟨f, hpos, hval⟩
    refine ⟨fun i => (eP b0 S m).symm (f i), ?_, ?_⟩
    · intro i j hij
      rw [eP_lt_iff b0 S m, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hpos i j hij
    · intro i j
      rw [blockPerm_lt_iff π b0 ε S m, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hval i j

private lemma contains_of_contains_blockPerm
    {I : Finset (Fin n)} (hb0 : b0 ∉ I)
    {ιB : Fin k → Fin n}
    (hι_mono : StrictMono ιB)
    (hι_not : ∀ a : Fin k, ιB a ∉ I)
    (hι_cell : ∀ a : Fin k, ∀ z ∈ I,
      (z < ιB a ↔ z < b0) ∧ (π z < π (ιB a) ↔ π z < π b0))
    (hι_ord : ∀ a b : Fin k, a < b → (π (ιB a) < π (ιB b) ↔ ε = true))
    {S : Finset (Fin n)} (hSI : S ⊆ I) (m : ℕ) (q : Equiv.Perm (Fin k))
    (h : Contains (blockPerm π b0 ε S m) q) : Contains π q := by
  obtain ⟨f, hpos, hval⟩ := (contains_blockPerm_iff π b0 ε S m q).mp h
  let g : Fin k → Fin n := fun i =>
    match f i with
    | Sum.inl x => x.val
    | Sum.inr _ => ιB i
  have hg_mono : StrictMono g := by
    intro i j hij
    have hp := hpos i j hij
    dsimp only [g]
    cases hi : f i with
    | inl x =>
      cases hj : f j with
      | inl y =>
        rw [hi, hj, posKey_inl_inl] at hp
        exact hp
      | inr b =>
        rw [hi, hj, posKey_inl_inr b0 hb0 hSI] at hp
        exact (hι_cell j x.val (hSI x.prop)).1.mpr hp
    | inr a =>
      cases hj : f j with
      | inl y =>
        rw [hi, hj, posKey_inr_inl b0 hb0 hSI] at hp
        have hyI : y.val ∈ I := hSI y.prop
        have hnot_lt : ¬ y.val < b0 := not_lt_of_gt hp
        have hnot_lt' : ¬ y.val < ιB i := fun hlt => hnot_lt ((hι_cell i y.val hyI).1.mp hlt)
        have hne : ιB i ≠ y.val := fun heq => hι_not i (heq ▸ hyI)
        exact lt_of_le_of_ne (le_of_not_gt hnot_lt') hne
      | inr b =>
        exact hι_mono hij
  refine ⟨g, hg_mono, ?_⟩
  apply lt_iff_of_lt_imp (fun i j heq => hg_mono.injective (π.injective heq)) q
  intro i j hij
  rw [← hval i j]
  have hp := hpos i j hij
  dsimp only [g]
  cases hi : f i with
  | inl x =>
    cases hj : f j with
    | inl y =>
      dsimp only
      rw [valKey_inl_inl]
    | inr b =>
      dsimp only
      rw [valKey_inl_inr π b0 ε hb0 hSI]
      exact (hι_cell j x.val (hSI x.prop)).2
  | inr a =>
    cases hj : f j with
    | inl y =>
      dsimp only
      rw [valKey_inr_inl π b0 ε hb0 hSI]
      have hyI : y.val ∈ I := hSI y.prop
      have hne1 : π (ιB i) ≠ π y.val := fun heq => hι_not i (π.injective heq ▸ hyI)
      have hne2 : π b0 ≠ π y.val := fun heq => hb0 (π.injective heq ▸ hyI)
      have hlt_iff := (hι_cell i y.val hyI).2
      constructor
      · intro hlt
        have hnot1 : ¬ π y.val < π (ιB i) := not_lt_of_gt hlt
        have hnot2 : ¬ π y.val < π b0 := fun h' => hnot1 (hlt_iff.mpr h')
        exact lt_of_le_of_ne (le_of_not_gt hnot2) hne2
      · intro hlt
        have hnot2 : ¬ π y.val < π b0 := not_lt_of_gt hlt
        have hnot1 : ¬ π y.val < π (ιB i) := fun h' => hnot2 (hlt_iff.mp h')
        exact lt_of_le_of_ne (le_of_not_gt hnot1) hne1
    | inr b =>
      dsimp only
      rw [hi, hj, posKey_inr_inr] at hp
      rw [valKey_inr_inr_of_lt π b0 ε hp]
      exact hι_ord i j hij

private lemma contains_blockPerm_restrict
    {I S S'' : Finset (Fin n)} (hb0 : b0 ∉ I) (hSI : S ⊆ I) (hS''I : S'' ⊆ I)
    {m m' : ℕ} (hm' : k ≤ m') {q : Equiv.Perm (Fin k)}
    (f : Fin k → {x : Fin n // x ∈ S} ⊕ Fin m)
    (hpos : ∀ i j : Fin k, i < j → posKey b0 S m (f i) < posKey b0 S m (f j))
    (hval : ∀ i j : Fin k, valKey π b0 ε S m (f i) < valKey π b0 ε S m (f j) ↔ q i < q j)
    (hsub : ∀ i : Fin k, ∀ x : {x : Fin n // x ∈ S}, f i = Sum.inl x → x.val ∈ S'') :
    Contains (blockPerm π b0 ε S'' m') q := by
  rw [contains_blockPerm_iff]
  let f' : Fin k → {x : Fin n // x ∈ S''} ⊕ Fin m' := fun i =>
    match h : f i with
    | Sum.inl x => Sum.inl ⟨x.val, hsub i x h⟩
    | Sum.inr _ => Sum.inr ⟨i.val, lt_of_lt_of_le i.isLt hm'⟩
  have hf'_inl : ∀ (i : Fin k) (x : {x : Fin n // x ∈ S}) (h : f i = Sum.inl x),
      f' i = Sum.inl ⟨x.val, hsub i x h⟩ := by
    intro i x h
    dsimp only [f']
    split
    · rename_i x' hx'
      have hxx : x' = x := Sum.inl.inj (hx'.symm.trans h)
      subst hxx
      rfl
    · rename_i b hb
      exact absurd (hb.symm.trans h) (by simp)
  have hf'_inr : ∀ (i : Fin k) (b : Fin m), f i = Sum.inr b →
      f' i = Sum.inr ⟨i.val, lt_of_lt_of_le i.isLt hm'⟩ := by
    intro i b h
    dsimp only [f']
    split
    · rename_i x hx
      exact absurd (hx.symm.trans h) (by simp)
    · rfl
  have hf'_pos : ∀ i j : Fin k, i < j →
      posKey b0 S'' m' (f' i) < posKey b0 S'' m' (f' j) := by
    intro i j hij
    have hp := hpos i j hij
    cases hi : f i with
    | inl x =>
      cases hj : f j with
      | inl y =>
        rw [hi, hj, posKey_inl_inl] at hp
        rw [hf'_inl i x hi, hf'_inl j y hj, posKey_inl_inl]
        exact hp
      | inr b =>
        rw [hi, hj, posKey_inl_inr b0 hb0 hSI] at hp
        rw [hf'_inl i x hi, hf'_inr j b hj, posKey_inl_inr b0 hb0 hS''I]
        exact hp
    | inr a =>
      cases hj : f j with
      | inl y =>
        rw [hi, hj, posKey_inr_inl b0 hb0 hSI] at hp
        rw [hf'_inr i a hi, hf'_inl j y hj, posKey_inr_inl b0 hb0 hS''I]
        exact hp
      | inr b =>
        rw [hf'_inr i a hi, hf'_inr j b hj, posKey_inr_inr]
        exact hij
  refine ⟨f', hf'_pos, ?_⟩
  have hf'_inj : Function.Injective (fun i => valKey π b0 ε S'' m' (f' i)) := by
    intro i j heq
    have hfeq : f' i = f' j := valKey_injective π b0 ε S'' m' heq
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact absurd (congrArg (posKey b0 S'' m') hfeq) (ne_of_lt (hf'_pos i j hij))
    · rfl
    · exact absurd (congrArg (posKey b0 S'' m') hfeq.symm) (ne_of_lt (hf'_pos j i hji))
  apply lt_iff_of_lt_imp hf'_inj q
  intro i j hij
  rw [← hval i j]
  have hp := hpos i j hij
  cases hi : f i with
  | inl x =>
    cases hj : f j with
    | inl y =>
      rw [hf'_inl i x hi, hf'_inl j y hj, valKey_inl_inl, valKey_inl_inl]
    | inr b =>
      rw [hf'_inl i x hi, hf'_inr j b hj, valKey_inl_inr π b0 ε hb0 hS''I,
        valKey_inl_inr π b0 ε hb0 hSI]
  | inr a =>
    cases hj : f j with
    | inl y =>
      rw [hf'_inr i a hi, hf'_inl j y hj, valKey_inr_inl π b0 ε hb0 hS''I,
        valKey_inr_inl π b0 ε hb0 hSI]
    | inr b =>
      rw [hi, hj, posKey_inr_inr] at hp
      have hij' : (⟨i.val, lt_of_lt_of_le i.isLt hm'⟩ : Fin m') <
          ⟨j.val, lt_of_lt_of_le j.isLt hm'⟩ := hij
      rw [hf'_inr i a hi, hf'_inr j b hj, valKey_inr_inr_of_lt π b0 ε hij',
        valKey_inr_inr_of_lt π b0 ε hp]

private lemma eq_of_full_support
    {I S : Finset (Fin n)} (hb0 : b0 ∉ I) (hSI : S ⊆ I)
    {p₁ p₂ : Equiv.Perm (Fin k)}
    (f₁ f₂ : Fin k → {x : Fin n // x ∈ S} ⊕ Fin k)
    (hpos₁ : ∀ i j : Fin k, i < j → posKey b0 S k (f₁ i) < posKey b0 S k (f₁ j))
    (hval₁ : ∀ i j : Fin k, valKey π b0 ε S k (f₁ i) < valKey π b0 ε S k (f₁ j) ↔ p₁ i < p₁ j)
    (hpos₂ : ∀ i j : Fin k, i < j → posKey b0 S k (f₂ i) < posKey b0 S k (f₂ j))
    (hval₂ : ∀ i j : Fin k, valKey π b0 ε S k (f₂ i) < valKey π b0 ε S k (f₂ j) ↔ p₂ i < p₂ j)
    (hhit₁ : ∀ x : {x : Fin n // x ∈ S}, ∃ i : Fin k, f₁ i = Sum.inl x)
    (hhit₂ : ∀ x : {x : Fin n // x ∈ S}, ∃ i : Fin k, f₂ i = Sum.inl x) :
    p₁ = p₂ := by
  classical
  let S_lt : Finset (Fin n) := S.filter fun x => x < b0
  let S_gt : Finset (Fin n) := S.filter fun x => b0 < x
  have hS_union : S_lt ∪ S_gt = S := by
    ext x
    simp only [S_lt, S_gt, mem_union, mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      have hne : x ≠ b0 := fun h => hb0 (hSI (h ▸ hx))
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl ⟨hx, hlt⟩
      · exact Or.inr ⟨hx, hgt⟩
  have hS_disj : Disjoint S_lt S_gt := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact not_lt_of_gt (mem_filter.mp h1).2 (mem_filter.mp h2).2
  have hS_card : S_lt.card + S_gt.card = S.card := by
    rw [← Finset.card_union_of_disjoint hS_disj, hS_union]
  -- Helper analyzing any full-support witness f
  have hstruct : ∀ (f : Fin k → {x : Fin n // x ∈ S} ⊕ Fin k),
      (∀ i j : Fin k, i < j → posKey b0 S k (f i) < posKey b0 S k (f j)) →
      (∀ x : {x : Fin n // x ∈ S}, ∃ i : Fin k, f i = Sum.inl x) →
      (∀ i : Fin k,
        ((∃ x : {x : Fin n // x ∈ S}, f i = Sum.inl x ∧ x.val < b0) ↔ i.val < S_lt.card) ∧
        ((∃ x : {x : Fin n // x ∈ S}, f i = Sum.inl x ∧ b0 < x.val) ↔ k - S_gt.card ≤ i.val) ∧
        ((∃ j : Fin k, f i = Sum.inr j) ↔ S_lt.card ≤ i.val ∧ i.val < k - S_gt.card)) ∧
      (∀ i : Fin k, ∀ x : {x : Fin n // x ∈ S}, f i = Sum.inl x → x.val < b0 →
        (S_lt.filter fun y => y < x.val).card = i.val) ∧
      (∀ i : Fin k, ∀ x : {x : Fin n // x ∈ S}, f i = Sum.inl x → b0 < x.val →
        (S_gt.filter fun y => y < x.val).card = i.val - (k - S_gt.card)) := by
    intro f hf_pos hf_hit
    have hf_inj : Function.Injective f := by
      intro i j heq
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact absurd (congrArg (posKey b0 S k) heq) (ne_of_lt (hf_pos i j hij))
      · rfl
      · exact absurd (congrArg (posKey b0 S k) heq.symm) (ne_of_lt (hf_pos j i hji))
    have hlt_of_posKey : ∀ i j : Fin k, posKey b0 S k (f i) < posKey b0 S k (f j) → i < j := by
      intro i j hpk
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact hij
      · exact absurd hpk (lt_irrefl _)
      · exact absurd (hf_pos j i hji) (not_lt_of_gt hpk)
    let Af : Finset (Fin k) := Finset.univ.filter fun i =>
      match f i with | Sum.inl x => x.val < b0 | Sum.inr _ => False
    let Cf : Finset (Fin k) := Finset.univ.filter fun i =>
      match f i with | Sum.inl x => b0 < x.val | Sum.inr _ => False
    let Bf : Finset (Fin k) := Finset.univ.filter fun i =>
      match f i with | Sum.inl _ => False | Sum.inr _ => True
    have hAf_card : Af.card = S_lt.card := by
      symm
      refine Finset.card_bij (fun x hx => Classical.choose (hf_hit ⟨x, (mem_filter.mp hx).1⟩)) ?_ ?_ ?_
      · intro x hx
        have hspec := Classical.choose_spec (hf_hit ⟨x, (mem_filter.mp hx).1⟩)
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        rw [hspec]
        exact (mem_filter.mp hx).2
      · intro x₁ hx₁ x₂ hx₂ heq
        have hs1 := Classical.choose_spec (hf_hit ⟨x₁, (mem_filter.mp hx₁).1⟩)
        have hs2 := Classical.choose_spec (hf_hit ⟨x₂, (mem_filter.mp hx₂).1⟩)
        rw [heq] at hs1
        have : (⟨x₁, (mem_filter.mp hx₁).1⟩ : {x : Fin n // x ∈ S}) = ⟨x₂, (mem_filter.mp hx₂).1⟩ :=
          Sum.inl.inj (hs1.symm.trans hs2)
        exact congrArg Subtype.val this
      · intro i hi
        rw [mem_filter] at hi
        cases hfi : f i with
        | inl x =>
          rw [hfi] at hi
          refine ⟨x.val, mem_filter.mpr ⟨x.prop, hi.2⟩, ?_⟩
          have hs := Classical.choose_spec (hf_hit x)
          exact hf_inj (hs.trans hfi.symm)
        | inr _ =>
          rw [hfi] at hi; exact False.elim hi.2
    have hCf_card : Cf.card = S_gt.card := by
      symm
      refine Finset.card_bij (fun x hx => Classical.choose (hf_hit ⟨x, (mem_filter.mp hx).1⟩)) ?_ ?_ ?_
      · intro x hx
        have hspec := Classical.choose_spec (hf_hit ⟨x, (mem_filter.mp hx).1⟩)
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        rw [hspec]
        exact (mem_filter.mp hx).2
      · intro x₁ hx₁ x₂ hx₂ heq
        have hs1 := Classical.choose_spec (hf_hit ⟨x₁, (mem_filter.mp hx₁).1⟩)
        have hs2 := Classical.choose_spec (hf_hit ⟨x₂, (mem_filter.mp hx₂).1⟩)
        rw [heq] at hs1
        have : (⟨x₁, (mem_filter.mp hx₁).1⟩ : {x : Fin n // x ∈ S}) = ⟨x₂, (mem_filter.mp hx₂).1⟩ :=
          Sum.inl.inj (hs1.symm.trans hs2)
        exact congrArg Subtype.val this
      · intro i hi
        rw [mem_filter] at hi
        cases hfi : f i with
        | inl x =>
          rw [hfi] at hi
          refine ⟨x.val, mem_filter.mpr ⟨x.prop, hi.2⟩, ?_⟩
          have hs := Classical.choose_spec (hf_hit x)
          exact hf_inj (hs.trans hfi.symm)
        | inr _ =>
          rw [hfi] at hi; exact False.elim hi.2
    have hpart : ∀ i : Fin k, i ∈ Af ∨ i ∈ Bf ∨ i ∈ Cf := by
      intro i
      cases hfi : f i with
      | inl x =>
        have hne : x.val ≠ b0 := fun h => hb0 (hSI (h ▸ x.prop))
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · left; rw [mem_filter]; exact ⟨mem_univ _, by rw [hfi]; exact hlt⟩
        · right; right; rw [mem_filter]; exact ⟨mem_univ _, by rw [hfi]; exact hgt⟩
      | inr _ =>
        right; left; rw [mem_filter]; exact ⟨mem_univ _, by rw [hfi]; trivial⟩
    have hord_AB : ∀ a ∈ Af, ∀ b ∈ Bf, a < b := by
      intro a ha b hb
      rw [mem_filter] at ha hb
      cases hfa : f a with
      | inl x =>
        cases hfb : f b with
        | inl _ => rw [hfb] at hb; exact False.elim hb.2
        | inr j =>
          rw [hfa] at ha
          exact hlt_of_posKey a b (by rw [hfa, hfb, posKey_inl_inr b0 hb0 hSI]; exact ha.2)
      | inr _ => rw [hfa] at ha; exact False.elim ha.2
    have hord_BC : ∀ b ∈ Bf, ∀ c ∈ Cf, b < c := by
      intro b hb c hc
      rw [mem_filter] at hb hc
      cases hfb : f b with
      | inl _ => rw [hfb] at hb; exact False.elim hb.2
      | inr j =>
        cases hfc : f c with
        | inl y =>
          rw [hfc] at hc
          exact hlt_of_posKey b c (by rw [hfb, hfc, posKey_inr_inl b0 hb0 hSI]; exact hc.2)
        | inr _ => rw [hfc] at hc; exact False.elim hc.2
    have hord_AC : ∀ a ∈ Af, ∀ c ∈ Cf, a < c := by
      intro a ha c hc
      rw [mem_filter] at ha hc
      cases hfa : f a with
      | inl x =>
        cases hfc : f c with
        | inl y =>
          rw [hfa] at ha; rw [hfc] at hc
          exact hlt_of_posKey a c (by rw [hfa, hfc, posKey_inl_inl]; exact lt_trans ha.2 hc.2)
        | inr _ => rw [hfc] at hc; exact False.elim hc.2
      | inr _ => rw [hfa] at ha; exact False.elim ha.2
    have hdisj_AB : Disjoint Af Bf := Finset.disjoint_left.mpr fun a ha hb =>
      lt_irrefl a (hord_AB a ha a hb)
    have hdisj_AC : Disjoint Af Cf := Finset.disjoint_left.mpr fun a ha hc =>
      lt_irrefl a (hord_AC a ha a hc)
    have hdisj_BC : Disjoint Bf Cf := Finset.disjoint_left.mpr fun b hb hc =>
      lt_irrefl b (hord_BC b hb b hc)
    have hunion_all : Af ∪ Bf ∪ Cf = Finset.univ := by
      ext i
      simp only [mem_union, mem_univ, iff_true]
      rcases hpart i with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    have hcard_tot : S_lt.card + Bf.card + S_gt.card = k := by
      have h1 : (Af ∪ Bf ∪ Cf).card = Af.card + Bf.card + Cf.card := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisj_AC, hdisj_BC⟩),
          Finset.card_union_of_disjoint hdisj_AB]
      rw [hunion_all, Finset.card_univ, Fintype.card_fin, hAf_card, hCf_card] at h1
      exact h1.symm
    have hcard_lt : ∀ i : Fin k, (Finset.univ.filter fun j : Fin k => j < i).card = i.val := by
      intro i
      have h := card_filter_lt_perm (Equiv.refl (Fin k)) i
      simp only [Equiv.refl_apply] at h
      rw [← h]
      congr 1
    have hAf_iff : ∀ i : Fin k, i ∈ Af ↔ i.val < S_lt.card := by
      intro i
      constructor
      · intro hi
        have hsub : (Finset.univ.filter fun j : Fin k => j < i) ⊂ Af := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro j hj
            have hji : j < i := (mem_filter.mp hj).2
            rcases hpart j with hjA | hjB | hjC
            · exact hjA
            · exact absurd (hord_AB i hi j hjB) (not_lt_of_gt hji)
            · exact absurd (hord_AC i hi j hjC) (not_lt_of_gt hji)
          · intro heq
            have hi' := hi
            rw [← heq, mem_filter] at hi'
            exact lt_irrefl i hi'.2
        have := Finset.card_lt_card hsub
        rw [hcard_lt, hAf_card] at this
        exact this
      · intro hilt
        by_contra hnot
        have hsub : Af ⊆ Finset.univ.filter fun j : Fin k => j < i := by
          intro a ha
          rw [mem_filter]
          refine ⟨mem_univ _, ?_⟩
          rcases hpart i with hiA | hiB | hiC
          · exact absurd hiA hnot
          · exact hord_AB a ha i hiB
          · exact hord_AC a ha i hiC
        have := Finset.card_le_card hsub
        rw [hAf_card, hcard_lt] at this
        omega
    have hCf_iff : ∀ i : Fin k, i ∈ Cf ↔ k - S_gt.card ≤ i.val := by
      intro i
      constructor
      · intro hi
        have hsub : Af ∪ Bf ⊆ Finset.univ.filter fun j : Fin k => j < i := by
          intro j hj
          rw [mem_filter]
          refine ⟨mem_univ _, ?_⟩
          rcases mem_union.mp hj with hjA | hjB
          · exact hord_AC j hjA i hi
          · exact hord_BC j hjB i hi
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj_AB, hAf_card, hcard_lt] at this
        omega
      · intro hige
        by_contra hnot
        have hsub : Finset.univ.filter (fun j : Fin k => j < i) ⊂ Af ∪ Bf := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨?_, ?_⟩
          · intro j hj
            have hji : j < i := (mem_filter.mp hj).2
            rcases hpart j with hjA | hjB | hjC
            · exact mem_union_left _ hjA
            · exact mem_union_right _ hjB
            · rcases hpart i with hiA | hiB | hiC
              · exact absurd (hord_AC i hiA j hjC) (not_lt_of_gt hji)
              · exact absurd (hord_BC i hiB j hjC) (not_lt_of_gt hji)
              · exact absurd hiC hnot
          · intro heq
            have hiAB : i ∈ Af ∪ Bf := by
              rcases hpart i with hiA | hiB | hiC
              · exact mem_union_left _ hiA
              · exact mem_union_right _ hiB
              · exact absurd hiC hnot
            rw [← heq, mem_filter] at hiAB
            exact lt_irrefl i hiAB.2
        have := Finset.card_lt_card hsub
        rw [Finset.card_union_of_disjoint hdisj_AB, hAf_card, hcard_lt] at this
        omega
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hA_eq : (∃ x : {x : Fin n // x ∈ S}, f i = Sum.inl x ∧ x.val < b0) ↔ i ∈ Af := by
        rw [mem_filter]
        cases f i <;> simp
      have hC_eq : (∃ x : {x : Fin n // x ∈ S}, f i = Sum.inl x ∧ b0 < x.val) ↔ i ∈ Cf := by
        rw [mem_filter]
        cases f i <;> simp
      have hB_eq : (∃ j : Fin k, f i = Sum.inr j) ↔ i ∈ Bf := by
        rw [mem_filter]
        cases f i <;> simp
      refine ⟨hA_eq.trans (hAf_iff i), hC_eq.trans (hCf_iff i), ?_⟩
      rw [hB_eq]
      constructor
      · intro hiB
        have hnotA : i ∉ Af := Finset.disjoint_right.mp hdisj_AB hiB
        have hnotC : i ∉ Cf := Finset.disjoint_left.mp hdisj_BC hiB
        rw [hAf_iff] at hnotA
        rw [hCf_iff] at hnotC
        omega
      · rintro ⟨h1, h2⟩
        rcases hpart i with hiA | hiB | hiC
        · rw [hAf_iff] at hiA; omega
        · exact hiB
        · rw [hCf_iff] at hiC; omega
    · intro i x hfi hxb
      have hiA : i ∈ Af := by rw [mem_filter]; exact ⟨mem_univ _, by rw [hfi]; exact hxb⟩
      have hbij : (S_lt.filter fun y => y < x.val).card =
          (Finset.univ.filter fun j : Fin k => j < i).card := by
        refine Finset.card_bij (fun y hy => Classical.choose (hf_hit ⟨y, (mem_filter.mp (mem_filter.mp hy).1).1⟩)) ?_ ?_ ?_
        · intro y hy
          have hy_lt : y < x.val := (mem_filter.mp hy).2
          have hyS : y ∈ S := (mem_filter.mp (mem_filter.mp hy).1).1
          have hspec := Classical.choose_spec (hf_hit ⟨y, hyS⟩)
          rw [mem_filter]
          refine ⟨mem_univ _, hlt_of_posKey _ i ?_⟩
          rw [hspec, hfi, posKey_inl_inl]
          exact hy_lt
        · intro y₁ hy₁ y₂ hy₂ heq
          have hs1 := Classical.choose_spec (hf_hit ⟨y₁, (mem_filter.mp (mem_filter.mp hy₁).1).1⟩)
          have hs2 := Classical.choose_spec (hf_hit ⟨y₂, (mem_filter.mp (mem_filter.mp hy₂).1).1⟩)
          rw [heq] at hs1
          exact congrArg Subtype.val (Sum.inl.inj (hs1.symm.trans hs2))
        · intro j hj
          have hji : j < i := (mem_filter.mp hj).2
          have hjA : j ∈ Af := (hAf_iff j).mpr (lt_trans hji ((hAf_iff i).mp hiA))
          rw [mem_filter] at hjA
          cases hfj : f j with
          | inl y =>
            rw [hfj] at hjA
            have hpk := hf_pos j i hji
            rw [hfj, hfi, posKey_inl_inl] at hpk
            refine ⟨y.val, mem_filter.mpr ⟨mem_filter.mpr ⟨y.prop, hjA.2⟩, hpk⟩, ?_⟩
            have hs := Classical.choose_spec (hf_hit y)
            exact hf_inj (hs.trans hfj.symm)
          | inr _ => rw [hfj] at hjA; exact False.elim hjA.2
      rw [hbij, hcard_lt]
    · intro i x hfi hbx
      have hiC : i ∈ Cf := by rw [mem_filter]; exact ⟨mem_univ _, by rw [hfi]; exact hbx⟩
      have hcard_Ico : (Finset.univ.filter fun j : Fin k => k - S_gt.card ≤ j.val ∧ j < i).card =
          i.val - (k - S_gt.card) := by
        have hbij : (Finset.univ.filter fun j : Fin k => k - S_gt.card ≤ j.val ∧ j < i).card =
            (Finset.Ico (k - S_gt.card) i.val).card := by
          refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
          · intro j hj
            rw [mem_filter] at hj
            rw [Finset.mem_Ico]
            exact ⟨hj.2.1, hj.2.2⟩
          · intro j₁ _ j₂ _ heq; exact Fin.ext heq
          · intro m hm
            rw [Finset.mem_Ico] at hm
            refine ⟨⟨m, lt_trans hm.2 i.isLt⟩, ?_, rfl⟩
            rw [mem_filter]
            exact ⟨mem_univ _, hm.1, hm.2⟩
        rw [hbij, Nat.card_Ico]
      have hbij : (S_gt.filter fun y => y < x.val).card =
          (Finset.univ.filter fun j : Fin k => k - S_gt.card ≤ j.val ∧ j < i).card := by
        refine Finset.card_bij (fun y hy => Classical.choose (hf_hit ⟨y, (mem_filter.mp (mem_filter.mp hy).1).1⟩)) ?_ ?_ ?_
        · intro y hy
          have hy_lt : y < x.val := (mem_filter.mp hy).2
          have hyS_gt : y ∈ S_gt := (mem_filter.mp hy).1
          have hyS : y ∈ S := (mem_filter.mp hyS_gt).1
          have hby : b0 < y := (mem_filter.mp hyS_gt).2
          have hspec := Classical.choose_spec (hf_hit ⟨y, hyS⟩)
          set j := Classical.choose (hf_hit ⟨y, hyS⟩)
          have hjC : j ∈ Cf := by rw [mem_filter]; exact ⟨mem_univ _, by rw [hspec]; exact hby⟩
          rw [mem_filter]
          refine ⟨mem_univ _, (hCf_iff j).mp hjC, hlt_of_posKey j i ?_⟩
          rw [hspec, hfi, posKey_inl_inl]
          exact hy_lt
        · intro y₁ hy₁ y₂ hy₂ heq
          have hs1 := Classical.choose_spec (hf_hit ⟨y₁, (mem_filter.mp (mem_filter.mp hy₁).1).1⟩)
          have hs2 := Classical.choose_spec (hf_hit ⟨y₂, (mem_filter.mp (mem_filter.mp hy₂).1).1⟩)
          rw [heq] at hs1
          exact congrArg Subtype.val (Sum.inl.inj (hs1.symm.trans hs2))
        · intro j hj
          rw [mem_filter] at hj
          have hjC : j ∈ Cf := (hCf_iff j).mpr hj.2.1
          rw [mem_filter] at hjC
          cases hfj : f j with
          | inl y =>
            rw [hfj] at hjC
            have hpk := hf_pos j i hj.2.2
            rw [hfj, hfi, posKey_inl_inl] at hpk
            refine ⟨y.val, mem_filter.mpr ⟨mem_filter.mpr ⟨y.prop, hjC.2⟩, hpk⟩, ?_⟩
            have hs := Classical.choose_spec (hf_hit y)
            exact hf_inj (hs.trans hfj.symm)
          | inr _ => rw [hfj] at hjC; exact False.elim hjC.2
      rw [hbij, hcard_Ico]
  obtain ⟨hs1, hcnt1_lt, hcnt1_gt⟩ := hstruct f₁ hpos₁ hhit₁
  obtain ⟨hs2, hcnt2_lt, hcnt2_gt⟩ := hstruct f₂ hpos₂ hhit₂
  have huniq_in : ∀ (T : Finset (Fin n)) (x y : Fin n), x ∈ T → y ∈ T →
      (T.filter fun w => w < x).card = (T.filter fun w => w < y).card → x = y := by
    intro T x y hx hy hc
    by_contra hne
    have hlt_contra : ∀ a b : Fin n, a ∈ T → b ∈ T → a < b →
        (T.filter fun w => w < a).card = (T.filter fun w => w < b).card → False := by
      intro a b ha _ hab hceq
      have hss : (T.filter fun w => w < a) ⊂ (T.filter fun w => w < b) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun w hw => mem_filter.mpr ⟨(mem_filter.mp hw).1, lt_trans (mem_filter.mp hw).2 hab⟩, ?_⟩
        intro heq
        have haB : a ∈ T.filter fun w => w < b := mem_filter.mpr ⟨ha, hab⟩
        rw [← heq, mem_filter] at haB
        exact lt_irrefl a haB.2
      have := Finset.card_lt_card hss
      omega
    rcases lt_or_gt_of_ne hne with hxy | hyx
    · exact hlt_contra x y hx hy hxy hc
    · exact hlt_contra y x hy hx hyx hc.symm
  have hf_eq_lt : ∀ i : Fin k, i.val < S_lt.card → f₁ i = f₂ i := by
    intro i hi
    obtain ⟨x₁, hf1, hx1⟩ := (hs1 i).1.mpr hi
    obtain ⟨x₂, hf2, hx2⟩ := (hs2 i).1.mpr hi
    have hc1 := hcnt1_lt i x₁ hf1 hx1
    have hc2 := hcnt2_lt i x₂ hf2 hx2
    have hval_eq := huniq_in S_lt x₁.val x₂.val
      (mem_filter.mpr ⟨x₁.prop, hx1⟩) (mem_filter.mpr ⟨x₂.prop, hx2⟩) (hc1.trans hc2.symm)
    rw [hf1, hf2]
    exact congrArg Sum.inl (Subtype.ext hval_eq)
  have hf_eq_gt : ∀ i : Fin k, k - S_gt.card ≤ i.val → f₁ i = f₂ i := by
    intro i hi
    obtain ⟨x₁, hf1, hx1⟩ := (hs1 i).2.1.mpr hi
    obtain ⟨x₂, hf2, hx2⟩ := (hs2 i).2.1.mpr hi
    have hc1 := hcnt1_gt i x₁ hf1 hx1
    have hc2 := hcnt2_gt i x₂ hf2 hx2
    have hval_eq := huniq_in S_gt x₁.val x₂.val
      (mem_filter.mpr ⟨x₁.prop, hx1⟩) (mem_filter.mpr ⟨x₂.prop, hx2⟩) (hc1.trans hc2.symm)
    rw [hf1, hf2]
    exact congrArg Sum.inl (Subtype.ext hval_eq)
  apply perm_eq_of_lt_iff
  apply lt_iff_of_lt_imp p₁.injective p₂
  intro i j hij
  rw [← hval₁ i j, ← hval₂ i j]
  have hp1 := hpos₁ i j hij
  have hp2 := hpos₂ i j hij
  by_cases hiL : i.val < S_lt.card
  · rw [hf_eq_lt i hiL]
    by_cases hjL : j.val < S_lt.card
    · rw [hf_eq_lt j hjL]
    · by_cases hjG : k - S_gt.card ≤ j.val
      · rw [hf_eq_gt j hjG]
      · obtain ⟨x, hf2i, _⟩ := (hs2 i).1.mpr hiL
        obtain ⟨b₁, hf1j⟩ := (hs1 j).2.2.mpr ⟨by omega, by omega⟩
        obtain ⟨b₂, hf2j⟩ := (hs2 j).2.2.mpr ⟨by omega, by omega⟩
        rw [hf2i, hf1j, hf2j, valKey_inl_inr π b0 ε hb0 hSI, valKey_inl_inr π b0 ε hb0 hSI]
  · by_cases hiG : k - S_gt.card ≤ i.val
    · have hjG : k - S_gt.card ≤ j.val := le_trans hiG (le_of_lt hij)
      rw [hf_eq_gt i hiG, hf_eq_gt j hjG]
    · obtain ⟨a₁, hf1i⟩ := (hs1 i).2.2.mpr ⟨by omega, by omega⟩
      obtain ⟨a₂, hf2i⟩ := (hs2 i).2.2.mpr ⟨by omega, by omega⟩
      by_cases hjG : k - S_gt.card ≤ j.val
      · obtain ⟨y, hf2j, _⟩ := (hs2 j).2.1.mpr hjG
        rw [hf_eq_gt j hjG, hf1i, hf2i, hf2j,
          valKey_inr_inl π b0 ε hb0 hSI, valKey_inr_inl π b0 ε hb0 hSI]
      · have hjgeL : S_lt.card ≤ j.val := by have : i.val < j.val := hij; omega
        obtain ⟨b₁, hf1j⟩ := (hs1 j).2.2.mpr ⟨hjgeL, by omega⟩
        obtain ⟨b₂, hf2j⟩ := (hs2 j).2.2.mpr ⟨hjgeL, by omega⟩
        rw [hf1i, hf1j, posKey_inr_inr] at hp1
        rw [hf2i, hf2j, posKey_inr_inr] at hp2
        rw [hf1i, hf1j, hf2i, hf2j,
          valKey_inr_inr_of_lt π b0 ε hp1, valKey_inr_inr_of_lt π b0 ε hp2]

end BlockInflation

-- ============================================================================
-- Section 5: Master Reply Lemma and Strong Induction Closing Main Theorem
-- ============================================================================

private def RevClosed {k : ℕ} (F : Finset (Equiv.Perm (Fin k))) : Prop :=
  ∀ q : Equiv.Perm (Fin k), q ∈ F ↔ reverse q ∈ F

private lemma master_reply {k n : ℕ} (hk : 2 ≤ k)
    (hn : k + (k + 1) ^ 2 * (k - 1) ^ 2 + 1 ≤ n)
    {F : Finset (Equiv.Perm (Fin k))} (hF : RevClosed F)
    {p : Equiv.Perm (Fin k)} (hleg : Legal n F p) :
    Legal n (insert p F) (reverse p) := by
  classical
  rcases hleg with ⟨π, hπF, hπp⟩
  rcases hπp with ⟨pos, hpos_mono, hpos_ord⟩
  let I : Finset (Fin n) := Finset.univ.image pos
  have hIcard : I.card = k := by
    rw [Finset.card_image_of_injective _ hpos_mono.injective, Finset.card_univ, Fintype.card_fin]
  obtain ⟨ιB, ε, hι_mono, hι_not, hι_cell, hι_ord⟩ :=
    single_cell_monotone_block hk hn π I hIcard
  let b0 : Fin n := ιB ⟨0, by omega⟩
  have hb0 : b0 ∉ I := hι_not ⟨0, by omega⟩
  have hI_contains : Contains (blockPerm π b0 ε I k) p := by
    rw [contains_blockPerm_iff]
    refine ⟨fun i => Sum.inl ⟨pos i, mem_image_of_mem pos (mem_univ i)⟩, ?_, ?_⟩
    · intro i j hij
      rw [posKey_inl_inl]
      exact hpos_mono hij
    · intro i j
      rw [valKey_inl_inl]
      exact hpos_ord i j
  let P : ℕ → Prop := fun r =>
    ∃ S : Finset (Fin n), S ⊆ I ∧ S.card = r ∧
      (Contains (blockPerm π b0 ε S k) p ∨ Contains (blockPerm π b0 ε S k) (reverse p))
  have hexP : ∃ r : ℕ, P r := ⟨k, I, Subset.refl I, hIcard, Or.inl hI_contains⟩
  let r0 := Nat.find hexP
  obtain ⟨S, hSI, hScard, hSor⟩ := Nat.find_spec hexP
  have hmin : ∀ S' : Finset (Fin n), S' ⊆ I →
      (Contains (blockPerm π b0 ε S' k) p ∨ Contains (blockPerm π b0 ε S' k) (reverse p)) →
      S.card ≤ S'.card := by
    intro S' hS'I hS'or
    rw [hScard]
    exact Nat.find_min' hexP ⟨S', hS'I, rfl, hS'or⟩
  have hnot_both : ¬ (Contains (blockPerm π b0 ε S k) p ∧ Contains (blockPerm π b0 ε S k) (reverse p)) := by
    rintro ⟨hp1, hp2⟩
    obtain ⟨f₁, hf1_pos, hf1_val⟩ := (contains_blockPerm_iff π b0 ε S k p).mp hp1
    obtain ⟨f₂, hf2_pos, hf2_val⟩ := (contains_blockPerm_iff π b0 ε S k (reverse p)).mp hp2
    let S₁ : Finset (Fin n) := S.filter fun x => ∃ i : Fin k, ∃ hx : x ∈ S, f₁ i = Sum.inl ⟨x, hx⟩
    let S₂ : Finset (Fin n) := S.filter fun x => ∃ i : Fin k, ∃ hx : x ∈ S, f₂ i = Sum.inl ⟨x, hx⟩
    have hS1_sub : S₁ ⊆ S := Finset.filter_subset _ S
    have hS2_sub : S₂ ⊆ S := Finset.filter_subset _ S
    have hS1_cont : Contains (blockPerm π b0 ε S₁ k) p :=
      contains_blockPerm_restrict π b0 ε hb0 hSI (Subset.trans hS1_sub hSI) le_rfl f₁ hf1_pos hf1_val
        (fun i x hfi => mem_filter.mpr ⟨x.prop, i, x.prop, hfi⟩)
    have hS2_cont : Contains (blockPerm π b0 ε S₂ k) (reverse p) :=
      contains_blockPerm_restrict π b0 ε hb0 hSI (Subset.trans hS2_sub hSI) le_rfl f₂ hf2_pos hf2_val
        (fun i x hfi => mem_filter.mpr ⟨x.prop, i, x.prop, hfi⟩)
    have hS1_eq : S₁ = S := Finset.eq_of_subset_of_card_le hS1_sub
      (hmin S₁ (Subset.trans hS1_sub hSI) (Or.inl hS1_cont))
    have hS2_eq : S₂ = S := Finset.eq_of_subset_of_card_le hS2_sub
      (hmin S₂ (Subset.trans hS2_sub hSI) (Or.inr hS2_cont))
    have hhit₁ : ∀ x : {x : Fin n // x ∈ S}, ∃ i : Fin k, f₁ i = Sum.inl x := by
      intro x
      have hx1 : x.val ∈ S₁ := hS1_eq.symm ▸ x.prop
      obtain ⟨i, _, hfi⟩ := (mem_filter.mp hx1).2
      exact ⟨i, hfi⟩
    have hhit₂ : ∀ x : {x : Fin n // x ∈ S}, ∃ i : Fin k, f₂ i = Sum.inl x := by
      intro x
      have hx2 : x.val ∈ S₂ := hS2_eq.symm ▸ x.prop
      obtain ⟨i, _, hfi⟩ := (mem_filter.mp hx2).2
      exact ⟨i, hfi⟩
    have heq := eq_of_full_support π b0 ε hb0 hSI f₁ f₂ hf1_pos hf1_val hf2_pos hf2_val hhit₁ hhit₂
    exact reverse_ne_self hk p heq.symm
  have hSle : S.card ≤ k := by
    calc S.card ≤ I.card := Finset.card_le_card hSI
      _ = k := hIcard
  let m : ℕ := n - S.card
  have hm_sum : S.card + m = n := by omega
  have hm_ge : k ≤ m := by
    have hk1 : 1 ≤ k - 1 := by omega
    have hsq1 : 1 ≤ (k - 1) ^ 2 := by nlinarith
    have hsq2 : k ≤ (k + 1) ^ 2 * (k - 1) ^ 2 + 1 := by nlinarith
    omega
  let τ : Equiv.Perm (Fin n) := permCast hm_sum (blockPerm π b0 ε S m)
  have hτ_pres : ∀ q : Equiv.Perm (Fin k), Contains τ q → Contains π q := by
    intro q hq
    rw [contains_permCast_iff] at hq
    exact contains_of_contains_blockPerm π b0 ε hb0 hι_mono hι_not hι_cell hι_ord hSI m q hq
  have hτ_iff : ∀ q : Equiv.Perm (Fin k), Contains τ q ↔ Contains (blockPerm π b0 ε S k) q := by
    intro q
    rw [contains_permCast_iff]
    constructor
    · intro hq
      obtain ⟨f, hf_pos, hf_val⟩ := (contains_blockPerm_iff π b0 ε S m q).mp hq
      exact contains_blockPerm_restrict π b0 ε hb0 hSI hSI le_rfl f hf_pos hf_val (fun _ x _ => x.prop)
    · intro hq
      obtain ⟨f, hf_pos, hf_val⟩ := (contains_blockPerm_iff π b0 ε S k q).mp hq
      exact contains_blockPerm_restrict π b0 ε hb0 hSI hSI hm_ge f hf_pos hf_val (fun _ x _ => x.prop)
  have hτF : ∀ q ∈ F, ¬ Contains τ q := fun q hq hc => hπF q hq (hτ_pres q hc)
  rcases hSor with hp_cont | hpr_cont
  · have hτp : Contains τ p := (hτ_iff p).mpr hp_cont
    have hnot_τpr : ¬ Contains τ (reverse p) := fun h => hnot_both ⟨hp_cont, (hτ_iff _).mp h⟩
    refine ⟨reverse τ, ?_, (contains_reverse_iff τ p).mpr hτp⟩
    intro q hq
    rw [mem_insert] at hq
    rcases hq with hqp | hqF
    · rw [hqp]
      intro h
      have hrev := (contains_reverse_iff τ (reverse p)).mp
      rw [reverse_reverse] at hrev
      exact hnot_τpr (hrev h)
    · intro h
      have hqr : reverse q ∈ F := (hF q).mp hqF
      have hrev := (contains_reverse_iff τ (reverse q)).mp
      rw [reverse_reverse] at hrev
      exact hτF (reverse q) hqr (hrev h)
  · have hτpr : Contains τ (reverse p) := (hτ_iff (reverse p)).mpr hpr_cont
    have hnot_τp : ¬ Contains τ p := fun h => hnot_both ⟨(hτ_iff p).mp h, hpr_cont⟩
    refine ⟨τ, ?_, hτpr⟩
    intro q hq
    rw [mem_insert] at hq
    rcases hq with rfl | hqF
    · exact hnot_τp
    · exact hτF q hqF

private lemma reverseWins_of_revClosed {k n : ℕ} (hk : 2 ≤ k)
    (hn : k + (k + 1) ^ 2 * (k - 1) ^ 2 + 1 ≤ n) :
    ∀ d : ℕ, ∀ F : Finset (Equiv.Perm (Fin k)),
      (Finset.univ \ F).card = d → RevClosed F → ReverseWins n F := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro F hFcard hFrev
    refine ReverseWins.intro F ?_ ?_
    · intro p hleg
      exact master_reply hk hn hFrev hleg
    · intro p hleg
      let F' : Finset (Equiv.Perm (Fin k)) := insert (reverse p) (insert p F)
      have hF'rev : RevClosed F' := by
        intro q
        simp only [F', mem_insert]
        constructor
        · rintro (rfl | rfl | hqF)
          · exact Or.inr (Or.inl (reverse_reverse p))
          · exact Or.inl rfl
          · exact Or.inr (Or.inr ((hFrev q).mp hqF))
        · rintro (heq | heq | hqF)
          · right; left
            have := congrArg reverse heq
            simpa only [reverse_reverse] using this
          · left
            have := congrArg reverse heq
            simpa only [reverse_reverse] using this
          · exact Or.inr (Or.inr ((hFrev q).mpr hqF))
      have hp_not_F : p ∉ F := by
        intro hpF
        rcases hleg with ⟨π, hπF, hπp⟩
        exact hπF p hpF hπp
      have hss : Finset.univ \ F' ⊂ Finset.univ \ F := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro q hq
          rw [mem_sdiff] at hq ⊢
          exact ⟨hq.1, fun hqF => hq.2 (mem_insert_of_mem (mem_insert_of_mem hqF))⟩
        · intro heq
          have hp_in : p ∈ Finset.univ \ F := mem_sdiff.mpr ⟨mem_univ p, hp_not_F⟩
          rw [← heq, mem_sdiff] at hp_in
          exact hp_in.2 (mem_insert_of_mem (mem_insert_self p F))
      have hlt : (Finset.univ \ F').card < d := by
        rw [← hFcard]
        exact Finset.card_lt_card hss
      exact ih (Finset.univ \ F').card hlt F' rfl hF'rev

theorem main_proof : ∀ k : ℕ, 3 ≤ k → ∃ n₀ : ℕ, ∀ n ≥ n₀,
    ReverseWins n (∅ : Finset (Equiv.Perm (Fin k))) := by
  intro k hk
  refine ⟨k + (k + 1) ^ 2 * (k - 1) ^ 2 + 1, fun n hn => ?_⟩
  have hrev_empty : RevClosed (∅ : Finset (Equiv.Perm (Fin k))) := by
    intro q; simp
  exact reverseWins_of_revClosed (by omega : 2 ≤ k) hn _ ∅ rfl hrev_empty

end Arxiv260316004

theorem OMA.solution : type_of% @OMA.S_arxiv_2603_16004.main :=
  Arxiv260316004.main_proof
