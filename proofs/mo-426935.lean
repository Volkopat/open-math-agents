import OMAStatements.S_mo_426935

namespace MO426935Proof

open OMA.S_mo_426935
open Classical

/-! ### Part 1: Elementary graph edge add/delete operations on `Fin n` -/

private def addEdge {n : ℕ} (H : SimpleGraph (Fin n)) (u v : Fin n) (huv : u ≠ v) :
    SimpleGraph (Fin n) where
  Adj a b := H.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)
  symm := ⟨by
    intro a b h
    rcases h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (H.symm.symm _ _ h)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨by
    intro a h
    rcases h with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact H.loopless.irrefl a h
    · exact huv h
    · exact huv h.symm⟩

private def delEdge {n : ℕ} (H : SimpleGraph (Fin n)) (u v : Fin n) :
    SimpleGraph (Fin n) where
  Adj a b := H.Adj a b ∧ ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))
  symm := ⟨by
    intro a b ⟨h, hne⟩
    refine ⟨H.symm.symm _ _ h, ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hne (Or.inr ⟨rfl, rfl⟩)
    · exact hne (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨by
    intro a ⟨h, _⟩
    exact H.loopless.irrefl a h⟩

private lemma neighborFinset_addEdge {n : ℕ} (H : SimpleGraph (Fin n)) {u v : Fin n}
    (huv : u ≠ v) (hn : ¬ H.Adj u v) (x : Fin n) :
    (addEdge H u v huv).neighborFinset x =
      if x = u then insert v (H.neighborFinset u)
      else if x = v then insert u (H.neighborFinset v)
      else H.neighborFinset x := by
  ext y
  split_ifs with hxu hxv
  · subst hxu
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
    change (H.Adj x y ∨ (x = x ∧ y = v) ∨ (x = v ∧ y = x)) ↔ y = v ∨ H.Adj x y
    constructor
    · rintro (h | ⟨_, rfl⟩ | ⟨h1, _⟩)
      · exact Or.inr h
      · exact Or.inl rfl
      · exact absurd h1 huv
    · rintro (rfl | h)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl h
  · subst hxv
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
    change (H.Adj x y ∨ (x = u ∧ y = x) ∨ (x = x ∧ y = u)) ↔ y = u ∨ H.Adj x y
    constructor
    · rintro (h | ⟨h1, _⟩ | ⟨_, rfl⟩)
      · exact Or.inr h
      · exact absurd h1.symm huv
      · exact Or.inl rfl
    · rintro (rfl | h)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl h
  · simp only [SimpleGraph.mem_neighborFinset]
    change (H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) ↔ H.Adj x y
    constructor
    · rintro (h | ⟨h1, _⟩ | ⟨h1, _⟩)
      · exact h
      · exact absurd h1 hxu
      · exact absurd h1 hxv
    · exact Or.inl

private lemma degree_addEdge {n : ℕ} (H : SimpleGraph (Fin n)) {u v : Fin n}
    (huv : u ≠ v) (hn : ¬ H.Adj u v) (x : Fin n) :
    (addEdge H u v huv).degree x =
      H.degree x + (if x = u ∨ x = v then 1 else 0) := by
  simp only [SimpleGraph.degree, neighborFinset_addEdge H huv hn]
  by_cases hxu : x = u
  · subst hxu
    have hv : v ∉ H.neighborFinset x := by simpa using hn
    simp [Finset.card_insert_of_notMem hv]
  · by_cases hxv : x = v
    · subst hxv
      have hu : u ∉ H.neighborFinset x := by simpa [SimpleGraph.adj_comm] using hn
      simp [hxu, Finset.card_insert_of_notMem hu]
    · simp [hxu, hxv]

private lemma neighborFinset_delEdge {n : ℕ} (H : SimpleGraph (Fin n)) {u v : Fin n}
    (hadj : H.Adj u v) (x : Fin n) :
    (delEdge H u v).neighborFinset x =
      if x = u then (H.neighborFinset u).erase v
      else if x = v then (H.neighborFinset v).erase u
      else H.neighborFinset x := by
  have huv : u ≠ v := H.ne_of_adj hadj
  ext y
  split_ifs with hxu hxv
  · subst hxu
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
    change (H.Adj x y ∧ ¬ ((x = x ∧ y = v) ∨ (x = v ∧ y = x))) ↔ y ≠ v ∧ H.Adj x y
    constructor
    · rintro ⟨h, hne⟩
      exact ⟨fun hy => hne (Or.inl ⟨rfl, hy⟩), h⟩
    · rintro ⟨hy, h⟩
      refine ⟨h, ?_⟩
      rintro (⟨_, rfl⟩ | ⟨h1, _⟩)
      · exact hy rfl
      · exact huv h1
  · subst hxv
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase]
    change (H.Adj x y ∧ ¬ ((x = u ∧ y = x) ∨ (x = x ∧ y = u))) ↔ y ≠ u ∧ H.Adj x y
    constructor
    · rintro ⟨h, hne⟩
      exact ⟨fun hy => hne (Or.inr ⟨rfl, hy⟩), h⟩
    · rintro ⟨hy, h⟩
      refine ⟨h, ?_⟩
      rintro (⟨h1, _⟩ | ⟨_, rfl⟩)
      · exact huv h1.symm
      · exact hy rfl
  · simp only [SimpleGraph.mem_neighborFinset]
    change (H.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) ↔ H.Adj x y
    constructor
    · exact And.left
    · intro h
      refine ⟨h, ?_⟩
      rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact hxu h1
      · exact hxv h1

private lemma degree_delEdge {n : ℕ} (H : SimpleGraph (Fin n)) {u v : Fin n}
    (hadj : H.Adj u v) (x : Fin n) :
    (delEdge H u v).degree x =
      H.degree x - (if x = u ∨ x = v then 1 else 0) := by
  simp only [SimpleGraph.degree, neighborFinset_delEdge H hadj]
  by_cases hxu : x = u
  · subst hxu
    have hv : v ∈ H.neighborFinset x := by simpa using hadj
    simp [Finset.card_erase_of_mem hv]
  · by_cases hxv : x = v
    · subst hxv
      have hu : u ∈ H.neighborFinset x := by simpa [SimpleGraph.adj_comm] using hadj
      simp [hxu, Finset.card_erase_of_mem hu]
    · simp [hxu, hxv]

/-! ### Part 2: Constructive Erdős–Gallai theorem (Tripathi–Venugopalan–West) -/

private def EGCond {n : ℕ} (d : Fin n → ℕ) : Prop :=
  Antitone d ∧ Even (∑ i : Fin n, d i) ∧
  ∀ k : ℕ, k ≤ n →
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), d i) ≤
      k * (k - 1) + ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), min k (d i)

private lemma eg_deg_lt_n {n : ℕ} {d : Fin n → ℕ} (hEG : EGCond d) (i : Fin n) : d i < n := by
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero (Fin.pos i |>.ne' |> fun _ => Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le _) i.isLt))
  have h1 := hEG.2.2 1 hn1
  have hflt1 : Finset.univ.filter (fun j : Fin n => j.val < 1) = {⟨0, hn1⟩} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
    omega
  rw [hflt1, Finset.sum_singleton] at h1
  have hsum_le : (∑ j ∈ Finset.univ.filter (fun j : Fin n => 1 ≤ j.val), min 1 (d j)) ≤
      (Finset.univ.filter (fun j : Fin n => 1 ≤ j.val)).card := by
    have : (Finset.univ.filter (fun j : Fin n => 1 ≤ j.val)).card =
        ∑ _j ∈ Finset.univ.filter (fun j : Fin n => 1 ≤ j.val), 1 := by simp
    rw [this]
    exact Finset.sum_le_sum fun _ _ => Nat.min_le_left _ _
  have hcard : (Finset.univ.filter (fun j : Fin n => 1 ≤ j.val)).card = n - 1 := by
    have h := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
      (fun j : Fin n => j.val < 1) (fun _ => (1 : ℕ))
    have hflt2 : Finset.univ.filter (fun j : Fin n => ¬ j.val < 1) =
        Finset.univ.filter (fun j : Fin n => 1 ≤ j.val) := by
      ext j; simp; omega
    rw [hflt1, hflt2] at h
    simp at h
    omega
  have h0 : d i ≤ d ⟨0, hn1⟩ := hEG.1 (Fin.mk_le_mk.mpr (Nat.zero_le _))
  omega

private def IsSubreal {n : ℕ} (d : Fin n → ℕ) (H : SimpleGraph (Fin n)) : Prop :=
  (∀ i, H.degree i ≤ d i) ∧
  ∀ r : Fin n, (∀ i : Fin n, i < r → H.degree i = d i) → H.degree r < d r →
    ∀ u v : Fin n, r < u → r < v → ¬ H.Adj u v

private noncomputable def progress {n : ℕ} (d : Fin n → ℕ) (H : SimpleGraph (Fin n)) : ℕ :=
  if h : ∃ i : Fin n, H.degree i < d i then
    let r := (Finset.univ.filter (fun i : Fin n => H.degree i < d i)).min'
      (by rcases h with ⟨i, hi⟩; exact ⟨i, by simpa using hi⟩)
    r.val * (n + 1) + H.degree r
  else
    n * (n + 1)

private lemma progress_le {n : ℕ} {d : Fin n → ℕ} (hEG : EGCond d)
    {H : SimpleGraph (Fin n)} (hsub : ∀ i, H.degree i ≤ d i) :
    progress d H ≤ n * (n + 1) := by
  unfold progress
  split_ifs with h
  · set r := (Finset.univ.filter (fun i : Fin n => H.degree i < d i)).min' _
    have hrlt : H.degree r < n := lt_of_le_of_lt (hsub r) (eg_deg_lt_n hEG r)
    have hrval : r.val + 1 ≤ n := r.isLt
    nlinarith
  · exact le_rfl

private lemma progress_lt_of_step {n : ℕ} {d : Fin n → ℕ} (hEG : EGCond d)
    {H H' : SimpleGraph (Fin n)} {r : Fin n}
    (hsub : ∀ i, H.degree i ≤ d i) (_hsub' : ∀ i, H'.degree i ≤ d i)
    (hpref : ∀ i : Fin n, i < r → H.degree i = d i) (hr : H.degree r < d r)
    (hpref' : ∀ i : Fin n, i < r → H'.degree i = d i)
    (hr' : H.degree r < H'.degree r) :
    progress d H < progress d H' := by
  have hne : ∃ i : Fin n, H.degree i < d i := ⟨r, hr⟩
  have hmin : ∀ hne', (Finset.univ.filter (fun i : Fin n => H.degree i < d i)).min' hne' = r := by
    intro hne'
    apply le_antisymm
    · exact Finset.min'_le _ r (by simpa using hr)
    · refine Finset.le_min' _ _ _ fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hlt
      push Not at hlt
      exact absurd (hpref i hlt) hi.ne
  have hpH : progress d H = r.val * (n + 1) + H.degree r := by
    unfold progress
    rw [dif_pos hne]
    dsimp only
    rw [hmin]
  rw [hpH]
  unfold progress
  split_ifs with h'
  · dsimp only
    set r' := (Finset.univ.filter (fun i : Fin n => H'.degree i < d i)).min'
      (by rcases h' with ⟨i, hi⟩; exact ⟨i, by simpa using hi⟩)
    have hr'_mem : H'.degree r' < d r' := by
      have := Finset.min'_mem (Finset.univ.filter (fun i : Fin n => H'.degree i < d i))
        (by rcases h' with ⟨i, hi⟩; exact ⟨i, by simpa using hi⟩)
      simpa using this
    have hle : r ≤ r' := by
      by_contra hlt
      push Not at hlt
      exact absurd (hpref' r' hlt) hr'_mem.ne
    by_cases heq : r' = r
    · rw [heq]; omega
    · have hlt : r.val + 1 ≤ r'.val := by
        have : r < r' := lt_of_le_of_ne hle (Ne.symm heq)
        exact this
      have hdeg : H.degree r < n := lt_of_le_of_lt (hsub r) (eg_deg_lt_n hEG r)
      nlinarith
  · have hdeg : H.degree r < n := lt_of_le_of_lt (hsub r) (eg_deg_lt_n hEG r)
    have hrval : r.val + 1 ≤ n := r.isLt
    nlinarith

private lemma isSubreal_of_step {n : ℕ} {d : Fin n → ℕ}
    {H' : SimpleGraph (Fin n)} {r : Fin n}
    (hsub' : ∀ i, H'.degree i ≤ d i)
    (hpref' : ∀ i : Fin n, i < r → H'.degree i = d i)
    (hind' : ∀ u v : Fin n, r < u → r < v → ¬ H'.Adj u v) :
    IsSubreal d H' := by
  refine ⟨hsub', fun r' hpref_r' hr' u v hu hv => ?_⟩
  have hle : r ≤ r' := by
    by_contra hlt
    push Not at hlt
    exact absurd (hpref' r' hlt) hr'.ne
  exact hind' u v (lt_of_le_of_lt hle hu) (lt_of_le_of_lt hle hv)

private lemma exists_extra_neighbor {n : ℕ} (H : SimpleGraph (Fin n)) {i r : Fin n}
    (_hir : i ≠ r) (hdeg : H.degree r < H.degree i) :
    ∃ u : Fin n, u ≠ i ∧ u ≠ r ∧ H.Adj i u ∧ ¬ H.Adj r u := by
  set Si := (H.neighborFinset i).erase r
  set Sr := (H.neighborFinset r).erase i
  have hlt : Sr.card < Si.card := by
    by_cases hadj : H.Adj i r
    · have h1 : r ∈ H.neighborFinset i := by simpa using hadj
      have h2 : i ∈ H.neighborFinset r := by simpa [SimpleGraph.adj_comm] using hadj
      simp only [Si, Sr, Finset.card_erase_of_mem h1, Finset.card_erase_of_mem h2]
      have hd1 : 0 < H.degree i := Finset.card_pos.mpr ⟨r, h1⟩
      have hd2 : 0 < H.degree r := Finset.card_pos.mpr ⟨i, h2⟩
      simp only [SimpleGraph.degree] at hdeg hd1 hd2
      omega
    · have h1 : r ∉ H.neighborFinset i := by simpa using hadj
      have h2 : i ∉ H.neighborFinset r := by simpa [SimpleGraph.adj_comm] using hadj
      simp only [Si, Sr, Finset.erase_eq_of_notMem h1, Finset.erase_eq_of_notMem h2]
      exact hdeg
  have hnot_sub : ¬ Si ⊆ Sr := fun hsub => not_lt_of_ge (Finset.card_le_card hsub) hlt
  rw [Finset.not_subset] at hnot_sub
  rcases hnot_sub with ⟨u, huSi, huSr⟩
  simp only [Si, Sr, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at huSi huSr
  have hui : u ≠ i := (H.ne_of_adj huSi.2).symm
  refine ⟨u, hui, huSi.1, huSi.2, fun hru => huSr ⟨hui, hru⟩⟩

private lemma erdos_gallai_step {n : ℕ} {d : Fin n → ℕ} (hEG : EGCond d)
    {H : SimpleGraph (Fin n)} (hH : IsSubreal d H)
    {r : Fin n} (hpref : ∀ i : Fin n, i < r → H.degree i = d i) (hr : H.degree r < d r) :
    ∃ H' : SimpleGraph (Fin n), IsSubreal d H' ∧ progress d H < progress d H' := by
  have hind : ∀ u v : Fin n, r < u → r < v → ¬ H.Adj u v := hH.2 r hpref hr
  -- Case 0: some j > r with deg j < d j and ¬ Adj r j
  by_cases hcase0 : ∃ j : Fin n, r < j ∧ H.degree j < d j ∧ ¬ H.Adj r j
  · rcases hcase0 with ⟨j, hrj, hdj, hnadj⟩
    have hrj_ne : r ≠ j := ne_of_lt hrj
    set H' := addEdge H r j hrj_ne
    have hdeg' : ∀ x, H'.degree x = H.degree x + (if x = r ∨ x = j then 1 else 0) :=
      degree_addEdge H hrj_ne hnadj
    have hsub' : ∀ x, H'.degree x ≤ d x := fun x => by
      rw [hdeg' x]
      split_ifs with h
      · rcases h with rfl | rfl <;> omega
      · exact hH.1 x
    have hpref' : ∀ i : Fin n, i < r → H'.degree i = d i := fun i hi => by
      rw [hdeg' i, if_neg (by intro h; rcases h with rfl | rfl <;> exact lt_irrefl _ (by omega : i < i))]
      simp [hpref i hi]
    have hind' : ∀ u v : Fin n, r < u → r < v → ¬ H'.Adj u v := by
      intro u v hu hv h
      rcases h with h | ⟨rfl, _⟩ | ⟨_, rfl⟩
      · exact hind u v hu hv h
      · exact lt_irrefl _ hu
      · exact lt_irrefl _ hv
    exact ⟨H', isSubreal_of_step hsub' hpref' hind',
      progress_lt_of_step hEG hH.1 hsub' hpref hr hpref' (by rw [hdeg' r]; simp)⟩
  push Not at hcase0
  -- Case 1: some i < r with ¬ Adj r i
  by_cases hcase1 : ∃ i : Fin n, i < r ∧ ¬ H.Adj r i
  · rcases hcase1 with ⟨i, hir, hnadj⟩
    have hdi : H.degree r < H.degree i := by
      have := hEG.1 hir.le
      rw [hpref i hir]
      omega
    rcases exists_extra_neighbor H (ne_of_lt hir) hdi with ⟨u, hui, hur, hiu, hnru⟩
    by_cases hgap : H.degree r + 2 ≤ d r
    · set H1 := delEdge H i u
      set H2 := addEdge H1 i r (ne_of_lt hir)
      set H' := addEdge H2 u r hur
      have hn1 : ¬ H1.Adj i r := fun h => hnadj (H.symm.symm _ _ h.1)
      have hn2 : ¬ H2.Adj u r := by
        rintro (h | ⟨h1, _⟩ | ⟨h1, _⟩)
        · exact hnru (H.symm.symm _ _ h.1)
        · exact hui h1
        · exact hur h1
      have hdeg1 : ∀ x, H1.degree x = H.degree x - (if x = i ∨ x = u then 1 else 0) :=
        degree_delEdge H hiu
      have hdeg2 : ∀ x, H2.degree x = H1.degree x + (if x = i ∨ x = r then 1 else 0) :=
        degree_addEdge H1 (ne_of_lt hir) hn1
      have hdeg3 : ∀ x, H'.degree x = H2.degree x + (if x = u ∨ x = r then 1 else 0) :=
        degree_addEdge H2 hur hn2
      have hpos_i : 1 ≤ H.degree i := Finset.card_pos.mpr ⟨u, by simpa using hiu⟩
      have hpos_u : 1 ≤ H.degree u := Finset.card_pos.mpr ⟨i, by simpa [SimpleGraph.adj_comm] using hiu⟩
      have hdeg' : ∀ x, H'.degree x = if x = r then H.degree r + 2 else H.degree x := fun x => by
        rw [hdeg3 x, hdeg2 x, hdeg1 x]
        by_cases hxr : x = r
        · subst hxr
          simp [ne_of_gt hir, hur.symm]
        · by_cases hxi : x = i
          · subst hxi
            simp [hxr, hui.symm]
            omega
          · by_cases hxu : x = u
            · subst hxu
              simp [hxr, hxi]
              omega
            · simp [hxr, hxi, hxu]
      have hsub' : ∀ x, H'.degree x ≤ d x := fun x => by
        rw [hdeg' x]
        split_ifs with hxr
        · subst hxr; omega
        · exact hH.1 x
      have hpref' : ∀ x : Fin n, x < r → H'.degree x = d x := fun x hx => by
        rw [hdeg' x, if_neg (ne_of_lt hx)]
        exact hpref x hx
      have hind' : ∀ a b : Fin n, r < a → r < b → ¬ H'.Adj a b := by
        intro a b ha hb h
        rcases h with (h | ⟨_, rfl⟩ | ⟨rfl, _⟩) | ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact hind a b ha hb h.1
        · exact lt_irrefl _ hb
        · exact lt_irrefl _ ha
        · exact lt_irrefl _ hb
        · exact lt_irrefl _ ha
      exact ⟨H', isSubreal_of_step hsub' hpref' hind',
        progress_lt_of_step hEG hH.1 hsub' hpref hr hpref' (by rw [hdeg' r]; simp)⟩
    · -- d r - H.degree r = 1: find k > r with H.degree k < d k by parity
      have hgap1 : d r = H.degree r + 1 := by omega
      have hsum_even : Even (∑ x : Fin n, (d x - H.degree x)) := by
        have hH_even : Even (∑ x : Fin n, H.degree x) := by
          rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
          exact even_two_mul _
        have hadd : (∑ x : Fin n, (d x - H.degree x)) + (∑ x : Fin n, H.degree x) = ∑ x : Fin n, d x := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => Nat.sub_add_cancel (hH.1 x)
        rcases hEG.2.1 with ⟨a, ha⟩
        rcases hH_even with ⟨b, hb⟩
        exact ⟨a - b, by omega⟩
      have hex_k : ∃ k : Fin n, r < k ∧ H.degree k < d k := by
        by_contra hno
        push Not at hno
        have hsum1 : (∑ x : Fin n, (d x - H.degree x)) = 1 := by
          rw [Finset.sum_eq_single r]
          · omega
          · intro x _ hxr
            by_cases hlt : x < r
            · rw [hpref x hlt]; omega
            · have hgt : r < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hxr)
              have := hno x hgt
              have := hH.1 x
              omega
          · intro h; exact absurd (Finset.mem_univ r) h
        rw [hsum1] at hsum_even
        rcases hsum_even with ⟨m, hm⟩
        omega
      rcases hex_k with ⟨k, hrk, hdk⟩
      have hrk_adj : H.Adj r k := hcase0 k hrk hdk
      have hku : k ≠ u := fun h => hnru (h ▸ hrk_adj)
      have hki : k ≠ i := ne_of_gt (lt_trans hir hrk)
      have hkr : k ≠ r := ne_of_gt hrk
      set H1 := delEdge H i u
      set H2 := delEdge H1 r k
      set H3 := addEdge H2 i r (ne_of_lt hir)
      set H' := addEdge H3 u r hur
      have hadj1 : H1.Adj r k := by
        refine ⟨hrk_adj, ?_⟩
        rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · exact (ne_of_lt hir).symm h1
        · exact hki h2
      have hn2 : ¬ H2.Adj i r := fun h => hnadj (H.symm.symm _ _ h.1.1)
      have hn3 : ¬ H3.Adj u r := by
        rintro (h | ⟨h1, _⟩ | ⟨h1, _⟩)
        · exact hnru (H.symm.symm _ _ h.1.1)
        · exact hui h1
        · exact hur h1
      have hdeg1 := degree_delEdge H hiu
      have hdeg2 := degree_delEdge H1 hadj1
      have hdeg3 := degree_addEdge H2 (ne_of_lt hir) hn2
      have hdeg4 := degree_addEdge H3 hur hn3
      have hpos_i : 1 ≤ H.degree i := Finset.card_pos.mpr ⟨u, by simpa using hiu⟩
      have hpos_u : 1 ≤ H.degree u := Finset.card_pos.mpr ⟨i, by simpa [SimpleGraph.adj_comm] using hiu⟩
      have hpos_r : 1 ≤ H.degree r := Finset.card_pos.mpr ⟨k, by simpa using hrk_adj⟩
      have hpos_k : 1 ≤ H.degree k := Finset.card_pos.mpr ⟨r, by simpa [SimpleGraph.adj_comm] using hrk_adj⟩
      have hdeg' : ∀ x, H'.degree x =
          if x = r then H.degree r + 1
          else if x = k then H.degree k - 1
          else H.degree x := fun x => by
        rw [hdeg4 x, hdeg3 x, hdeg2 x, hdeg1 x]
        by_cases hxr : x = r
        · subst hxr; simp [ne_of_gt hir, hur.symm]; omega
        · by_cases hxk : x = k
          · subst hxk; simp [hxr, hki, hku]
          · by_cases hxi : x = i
            · subst hxi; simp [hxr, hxk, hui.symm]; omega
            · by_cases hxu : x = u
              · subst hxu; simp [hxr, hxk, hxi]; omega
              · simp [hxr, hxk, hxi, hxu]
      have hsub' : ∀ x, H'.degree x ≤ d x := fun x => by
        rw [hdeg' x]
        split_ifs with hxr hxk
        · subst hxr; omega
        · subst hxk; exact le_trans (Nat.sub_le _ _) (hH.1 x)
        · exact hH.1 x
      have hpref' : ∀ x : Fin n, x < r → H'.degree x = d x := fun x hx => by
        have hxk : x ≠ k := ne_of_lt (lt_trans hx hrk)
        rw [hdeg' x, if_neg (ne_of_lt hx), if_neg hxk]
        exact hpref x hx
      have hind' : ∀ a b : Fin n, r < a → r < b → ¬ H'.Adj a b := by
        intro a b ha hb h
        rcases h with (h | ⟨_, rfl⟩ | ⟨rfl, _⟩) | ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact hind a b ha hb h.1.1
        · exact lt_irrefl _ hb
        · exact lt_irrefl _ ha
        · exact lt_irrefl _ hb
        · exact lt_irrefl _ ha
      exact ⟨H', isSubreal_of_step hsub' hpref' hind',
        progress_lt_of_step hEG hH.1 hsub' hpref hr hpref' (by rw [hdeg' r]; simp)⟩
  push Not at hcase1
  -- Now r is adjacent to ALL i < r!
  -- Case 2: some k > r with H.degree k < min (r.val + 1) (d k)
  by_cases hcase2 : ∃ k : Fin n, r < k ∧ H.degree k < min (r.val + 1) (d k)
  · rcases hcase2 with ⟨k, hrk, hdk_min⟩
    have hdk : H.degree k < d k := lt_of_lt_of_le hdk_min (Nat.min_le_right _ _)
    have hdk_r : H.degree k < r.val + 1 := lt_of_lt_of_le hdk_min (Nat.min_le_left _ _)
    have hrk_adj : H.Adj r k := hcase0 k hrk hdk
    -- All neighbors of k are ≤ r (by hind); since deg k < r+1, some i < r is not adj to k
    have hex_i : ∃ i : Fin n, i < r ∧ ¬ H.Adj i k := by
      by_contra hno
      push Not at hno
      have hsub_nb : Finset.univ.filter (fun x : Fin n => x ≤ r) ⊆ H.neighborFinset k := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [SimpleGraph.mem_neighborFinset]
        by_cases hxr : x = r
        · exact hxr ▸ H.symm.symm _ _ hrk_adj
        · exact H.symm.symm _ _ (hno x (lt_of_le_of_ne hx hxr))
      have hcard_le := Finset.card_le_card hsub_nb
      have hcard_flt : (Finset.univ.filter (fun x : Fin n => x ≤ r)).card = r.val + 1 := by
        have heq : Finset.univ.filter (fun x : Fin n => x ≤ r) =
            (Finset.range (r.val + 1)).attach.image
              (fun j => ⟨j.1, lt_of_lt_of_le (Finset.mem_range.mp j.2) r.isLt⟩) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
            Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range]
          constructor
          · intro hx
            exact ⟨x.val, by change x.val ≤ r.val at hx; omega, Fin.ext rfl⟩
          · rintro ⟨a, ha, rfl⟩
            change a ≤ r.val; omega
        rw [heq, Finset.card_image_of_injective]
        · simp
        · intro a b hab
          exact Subtype.ext (congrArg Fin.val hab)
      change _ ≤ H.degree k at hcard_le
      omega
    rcases hex_i with ⟨i, hir, hnik⟩
    have hdi : H.degree r < H.degree i := by
      have := hEG.1 hir.le
      rw [hpref i hir]
      omega
    rcases exists_extra_neighbor H (ne_of_lt hir) hdi with ⟨u, hui, hur, hiu, hnru⟩
    have hku : k ≠ u := fun h => hnik (h ▸ hiu)
    have hik_ne : i ≠ k := ne_of_lt (lt_trans hir hrk)
    set H1 := delEdge H i u
    set H2 := addEdge H1 i k hik_ne
    set H' := addEdge H2 u r hur
    have hn1 : ¬ H1.Adj i k := fun h => hnik h.1
    have hn2 : ¬ H2.Adj u r := by
      rintro (h | ⟨h1, _⟩ | ⟨_, h2⟩)
      · exact hnru (H.symm.symm _ _ h.1)
      · exact hui h1
      · exact (ne_of_lt hir).symm h2
    have hdeg1 := degree_delEdge H hiu
    have hdeg2 := degree_addEdge H1 hik_ne hn1
    have hdeg3 := degree_addEdge H2 hur hn2
    have hpos_i : 1 ≤ H.degree i := Finset.card_pos.mpr ⟨u, by simpa using hiu⟩
    have hpos_u : 1 ≤ H.degree u := Finset.card_pos.mpr ⟨i, by simpa [SimpleGraph.adj_comm] using hiu⟩
    have hdeg' : ∀ x, H'.degree x =
        if x = r then H.degree r + 1
        else if x = k then H.degree k + 1
        else H.degree x := fun x => by
      rw [hdeg3 x, hdeg2 x, hdeg1 x]
      by_cases hxr : x = r
      · subst hxr; simp [ne_of_gt hir, hur.symm, ne_of_lt hrk]
      · by_cases hxk : x = k
        · subst hxk; simp [hxr, hik_ne.symm, hku]
        · by_cases hxi : x = i
          · subst hxi; simp [hxr, hxk, hui.symm]; omega
          · by_cases hxu : x = u
            · subst hxu; simp [hxr, hxk, hxi]; omega
            · simp [hxr, hxk, hxi, hxu]
    have hsub' : ∀ x, H'.degree x ≤ d x := fun x => by
      rw [hdeg' x]
      split_ifs with hxr hxk
      · subst hxr; omega
      · subst hxk; omega
      · exact hH.1 x
    have hpref' : ∀ x : Fin n, x < r → H'.degree x = d x := fun x hx => by
      have hxk : x ≠ k := ne_of_lt (lt_trans hx hrk)
      rw [hdeg' x, if_neg (ne_of_lt hx), if_neg hxk]
      exact hpref x hx
    have hind' : ∀ a b : Fin n, r < a → r < b → ¬ H'.Adj a b := by
      intro a b ha hb h
      rcases h with (h | ⟨rfl, _⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ | ⟨rfl, _⟩
      · exact hind a b ha hb h.1
      · exact lt_asymm ha hir
      · exact lt_asymm hb hir
      · exact lt_irrefl _ hb
      · exact lt_irrefl _ ha
    exact ⟨H', isSubreal_of_step hsub' hpref' hind',
      progress_lt_of_step hEG hH.1 hsub' hpref hr hpref' (by rw [hdeg' r]; simp)⟩
  push Not at hcase2
  -- Case 3a: some i < r, j < r with i ≠ j and ¬ Adj i j
  by_cases hcase3a : ∃ i : Fin n, ∃ j : Fin n, i < r ∧ j < r ∧ i ≠ j ∧ ¬ H.Adj i j
  · rcases hcase3a with ⟨i, j, hir, hjr, hij, hnij⟩
    have hdi : H.degree r < H.degree i := by
      have := hEG.1 hir.le; rw [hpref i hir]; omega
    have hdj : H.degree r < H.degree j := by
      have := hEG.1 hjr.le; rw [hpref j hjr]; omega
    rcases exists_extra_neighbor H (ne_of_lt hir) hdi with ⟨u, hui, hur, hiu, hnru⟩
    rcases exists_extra_neighbor H (ne_of_lt hjr) hdj with ⟨w, hwj, hwr, hjw, hnrw⟩
    have hru_gt : r < u := by
      by_contra hle
      push Not at hle
      exact hnru (hcase1 u (lt_of_le_of_ne hle hur))
    have hrw_gt : r < w := by
      by_contra hle
      push Not at hle
      exact hnrw (hcase1 w (lt_of_le_of_ne hle hwr))
    have hju : j ≠ u := ne_of_lt (lt_trans hjr hru_gt)
    have hiw : i ≠ w := ne_of_lt (lt_trans hir hrw_gt)
    set H1 := delEdge H i u
    set H2 := delEdge H1 j w
    set H3 := addEdge H2 i j hij
    set H' := addEdge H3 u r hur
    have hadj1 : H1.Adj j w := by
      refine ⟨hjw, ?_⟩
      rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact hij h1.symm
      · exact hju h1
    have hn2 : ¬ H2.Adj i j := fun h => hnij h.1.1
    have hn3 : ¬ H3.Adj u r := by
      rintro (h | ⟨h1, _⟩ | ⟨h1, _⟩)
      · exact hnru (H.symm.symm _ _ h.1.1)
      · exact hui h1
      · exact hju.symm h1
    have hdeg1 := degree_delEdge H hiu
    have hdeg2 := degree_delEdge H1 hadj1
    have hdeg3 := degree_addEdge H2 hij hn2
    have hdeg4 := degree_addEdge H3 hur hn3
    have hpos_i : 1 ≤ H.degree i := Finset.card_pos.mpr ⟨u, by simpa using hiu⟩
    have hpos_j : 1 ≤ H.degree j := Finset.card_pos.mpr ⟨w, by simpa using hjw⟩
    have hpos_u : 1 ≤ H.degree u := Finset.card_pos.mpr ⟨i, by simpa [SimpleGraph.adj_comm] using hiu⟩
    have hpos_w : 1 ≤ H.degree w := Finset.card_pos.mpr ⟨j, by simpa [SimpleGraph.adj_comm] using hjw⟩
    have hdeg_le : ∀ x, x ≠ r → H'.degree x ≤ H.degree x := fun x hxr => by
      rw [hdeg4 x, hdeg3 x, hdeg2 x, hdeg1 x]
      by_cases hxi : x = i
      · subst hxi; simp [hxr, hij, hiw, hui.symm]; omega
      · by_cases hxj : x = j
        · subst hxj; simp [hxr, hij.symm, hju, hwj.symm]; omega
        · by_cases hxu : x = u
          · subst hxu; simp [hxr, hxi, hxj]; split_ifs <;> omega
          · by_cases hxw : x = w
            · subst hxw; simp [hxr, hxi, hxj, hxu]
            · simp [hxr, hxi, hxj, hxu, hxw]
    have hdeg_pref : ∀ x : Fin n, x < r → H'.degree x = H.degree x := fun x hx => by
      have hxr : x ≠ r := ne_of_lt hx
      have hxu : x ≠ u := ne_of_lt (lt_trans hx hru_gt)
      have hxw : x ≠ w := ne_of_lt (lt_trans hx hrw_gt)
      rw [hdeg4 x, hdeg3 x, hdeg2 x, hdeg1 x]
      by_cases hxi : x = i
      · subst hxi; simp [hxr, hxu, hxw, hij]; omega
      · by_cases hxj : x = j
        · subst hxj; simp [hxr, hxu, hxw, hij.symm]; omega
        · simp [hxr, hxu, hxw, hxi, hxj]
    have hdeg_r : H'.degree r = H.degree r + 1 := by
      rw [hdeg4 r, hdeg3 r, hdeg2 r, hdeg1 r]
      simp [ne_of_gt hir, ne_of_gt hjr, hur.symm, hwr.symm]
    have hsub' : ∀ x, H'.degree x ≤ d x := fun x => by
      by_cases hxr : x = r
      · subst hxr; rw [hdeg_r]; omega
      · exact le_trans (hdeg_le x hxr) (hH.1 x)
    have hpref' : ∀ x : Fin n, x < r → H'.degree x = d x := fun x hx => by
      rw [hdeg_pref x hx, hpref x hx]
    have hind' : ∀ a b : Fin n, r < a → r < b → ¬ H'.Adj a b := by
      intro a b ha hb h
      rcases h with (h | ⟨rfl, _⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩ | ⟨rfl, _⟩
      · exact hind a b ha hb h.1.1
      · exact lt_asymm ha hir
      · exact lt_asymm hb hir
      · exact lt_irrefl _ hb
      · exact lt_irrefl _ ha
    exact ⟨H', isSubreal_of_step hsub' hpref' hind',
      progress_lt_of_step hEG hH.1 hsub' hpref hr hpref' (by rw [hdeg_r]; omega)⟩
  -- Case 3b: Contradiction with Erdős-Gallai at k = r.val + 1!
  push Not at hcase3a
  exfalso
  set K := Finset.univ.filter (fun i : Fin n => i.val < r.val + 1)
  set L := Finset.univ.filter (fun j : Fin n => r.val + 1 ≤ j.val)
  have hK_eq : ∀ i : Fin n, i ∈ K ↔ i ≤ r := fun i => by
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def]; omega
  have hL_eq : ∀ j : Fin n, j ∈ L ↔ r < j := fun j => by
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]; omega
  have hK_card : K.card = r.val + 1 := by
    have heq : K = (Finset.range (r.val + 1)).attach.image
        (fun j => ⟨j.1, lt_of_lt_of_le (Finset.mem_range.mp j.2) r.isLt⟩) := by
      ext x
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range]
      exact ⟨fun hx => ⟨x.val, hx, Fin.ext rfl⟩, fun ⟨_, ha, h⟩ => h ▸ ha⟩
    rw [heq, Finset.card_image_of_injective]
    · simp
    · intro a b hab; exact Subtype.ext (congrArg Fin.val hab)
  have hclique : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → H.Adj u v := by
    intro u hu v hv huv
    rw [hK_eq] at hu hv
    by_cases hur : u = r
    · subst hur
      exact hcase1 v (lt_of_le_of_ne hv huv.symm)
    · by_cases hvr : v = r
      · subst hvr
        exact H.symm.symm _ _ (hcase1 u (lt_of_le_of_ne hu huv))
      · exact hcase3a u v (lt_of_le_of_ne hu hur) (lt_of_le_of_ne hv hvr) huv
  have hdeg_split : ∀ u ∈ K,
      H.degree u = r.val + (L.filter (fun v => H.Adj u v)).card := by
    intro u hu
    have hnb_split : H.neighborFinset u = (K.erase u) ∪ (L.filter (fun v => H.Adj u v)) := by
      ext v
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_erase,
        Finset.mem_filter, hK_eq, hL_eq]
      constructor
      · intro huv
        by_cases hvr : v ≤ r
        · exact Or.inl ⟨(H.ne_of_adj huv).symm, hvr⟩
        · exact Or.inr ⟨lt_of_not_ge hvr, huv⟩
      · rintro (⟨hvu, hvr⟩ | ⟨_, huv⟩)
        · exact hclique u hu v ((hK_eq v).mpr hvr) hvu.symm
        · exact huv
    have hdisj : Disjoint (K.erase u) (L.filter (fun v => H.Adj u v)) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_erase, Finset.mem_filter, hK_eq, hL_eq] at h1 h2
      exact not_lt_of_ge h1.2 h2.1
    rw [SimpleGraph.degree, hnb_split, Finset.card_union_of_disjoint hdisj,
      Finset.card_erase_of_mem hu, hK_card]
    omega
  have hcross : (∑ u ∈ K, (L.filter (fun v => H.Adj u v)).card) = ∑ v ∈ L, H.degree v := by
    have h1 : (∑ u ∈ K, (L.filter (fun v => H.Adj u v)).card) =
        ∑ u ∈ K, ∑ v ∈ L, if H.Adj u v then 1 else 0 := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.card_filter]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v hv => ?_
    have hvL : r < v := (hL_eq v).mp hv
    have hnb_v : H.neighborFinset v = K.filter (fun u => H.Adj u v) := by
      ext u
      simp only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, hK_eq]
      constructor
      · intro hvu
        refine ⟨?_, H.symm.symm _ _ hvu⟩
        by_contra hnot
        exact hind v u hvL (lt_of_not_ge hnot) hvu
      · rintro ⟨_, huv⟩
        exact H.symm.symm _ _ huv
    rw [SimpleGraph.degree, hnb_v, Finset.card_filter]
  have hsum_H : (∑ u ∈ K, H.degree u) =
      (r.val + 1) * r.val + ∑ v ∈ L, H.degree v := by
    rw [Finset.sum_congr rfl hdeg_split, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul, hK_card, hcross]
  have hdeg_L : ∀ v ∈ L, min (r.val + 1) (d v) ≤ H.degree v := fun v hv =>
    hcase2 v ((hL_eq v).mp hv)
  have hL_ge : (∑ v ∈ L, min (r.val + 1) (d v)) ≤ ∑ v ∈ L, H.degree v :=
    Finset.sum_le_sum hdeg_L
  have hK_lt : (∑ u ∈ K, H.degree u) < ∑ u ∈ K, d u := by
    refine Finset.sum_lt_sum (fun u _ => hH.1 u) ⟨r, (hK_eq r).mpr le_rfl, hr⟩
  have hEG_r := hEG.2.2 (r.val + 1) r.isLt
  have hsub1 : (r.val + 1) - 1 = r.val := by omega
  rw [hsub1] at hEG_r
  change (∑ u ∈ K, d u) ≤ (r.val + 1) * r.val + ∑ v ∈ L, min (r.val + 1) (d v) at hEG_r
  omega

private lemma erdos_gallai {n : ℕ} (d : Fin n → ℕ) (hEG : EGCond d) :
    ∃ H : SimpleGraph (Fin n), ∀ i, H.degree i = d i := by
  have hgo : ∀ gap : ℕ, ∀ H : SimpleGraph (Fin n), IsSubreal d H →
      n * (n + 1) - progress d H ≤ gap →
      ∃ H' : SimpleGraph (Fin n), ∀ i, H'.degree i = d i := by
    intro gap
    induction gap with
    | zero =>
        intro H hH hgap
        by_cases hex : ∃ i : Fin n, H.degree i < d i
        · set r := (Finset.univ.filter (fun i : Fin n => H.degree i < d i)).min'
            (by rcases hex with ⟨i, hi⟩; exact ⟨i, by simpa using hi⟩)
          have hpref : ∀ i : Fin n, i < r → H.degree i = d i := by
            intro i hi
            by_contra hne
            have hlt : H.degree i < d i := lt_of_le_of_ne (hH.1 i) hne
            have := Finset.min'_le (Finset.univ.filter (fun j : Fin n => H.degree j < d j)) i
              (by simpa using hlt)
            exact not_le_of_gt hi this
          have hr : H.degree r < d r := by
            have := Finset.min'_mem (Finset.univ.filter (fun j : Fin n => H.degree j < d j))
              (by rcases hex with ⟨i, hi⟩; exact ⟨i, by simpa using hi⟩)
            simpa using this
          rcases erdos_gallai_step hEG hH hpref hr with ⟨H', hH', hlt⟩
          have hle := progress_le hEG hH'.1
          omega
        · push Not at hex
          exact ⟨H, fun i => le_antisymm (hH.1 i) (hex i)⟩
    | succ gap ih =>
        intro H hH hgap
        by_cases hex : ∃ i : Fin n, H.degree i < d i
        · set r := (Finset.univ.filter (fun i : Fin n => H.degree i < d i)).min'
            (by rcases hex with ⟨i, hi⟩; exact ⟨i, by simpa using hi⟩)
          have hpref : ∀ i : Fin n, i < r → H.degree i = d i := by
            intro i hi
            by_contra hne
            have hlt : H.degree i < d i := lt_of_le_of_ne (hH.1 i) hne
            have := Finset.min'_le (Finset.univ.filter (fun j : Fin n => H.degree j < d j)) i
              (by simpa using hlt)
            exact not_le_of_gt hi this
          have hr : H.degree r < d r := by
            have := Finset.min'_mem (Finset.univ.filter (fun j : Fin n => H.degree j < d j))
              (by rcases hex with ⟨i, hi⟩; exact ⟨i, by simpa using hi⟩)
            simpa using this
          rcases erdos_gallai_step hEG hH hpref hr with ⟨H', hH', hlt⟩
          have hle := progress_le hEG hH'.1
          exact ih H' hH' (by omega)
        · push Not at hex
          exact ⟨H, fun i => le_antisymm (hH.1 i) (hex i)⟩
  have hbot : IsSubreal d (⊥ : SimpleGraph (Fin n)) := by
    refine ⟨fun i => by simp, fun _ _ _ _ _ _ _ h => h⟩
  exact hgo (n * (n + 1)) ⊥ hbot (by omega)

/-! ### Part 3: Schreib–Yavari Capacity Bound & Parity for Imbalance Multiset -/

private lemma capacity_bound {V : Type} [Fintype V] (G : SimpleGraph V)
    (himb : ∀ e ∈ G.edgeSet, 1 ≤ imb G e) (hne : G.edgeFinset.Nonempty)
    (A : Finset (Sym2 V)) (_hA : A ⊆ G.edgeFinset) :
    let Δ := Finset.univ.sup (fun v : V => G.degree v)
    A.card * (Δ - A.card) ≤ ∑ e ∈ G.edgeFinset \ A, min A.card (imb G e) := by
  intro Δ
  set k := A.card
  by_cases hk : k = 0 ∨ Δ ≤ k
  · rcases hk with hk0 | hΔk
    · simp [hk0]
    · have : Δ - k = 0 := by omega
      rw [this, mul_zero]
      exact Nat.zero_le _
  push Not at hk
  rcases hk with ⟨hk0, hkΔ⟩
  set r := Δ - k
  have hr_pos : 1 ≤ r := by omega
  have hVne : (Finset.univ : Finset V).Nonempty := by
    rcases hne with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v => exact ⟨u, Finset.mem_univ u⟩
  rcases Finset.exists_mem_eq_sup Finset.univ hVne (fun v : V => G.degree v) with ⟨x, _, hΔx⟩
  have hdx : G.degree x = Δ := hΔx.symm
  -- Edges incident to x
  set Ex := G.incidenceFinset x
  have hEx_sub : Ex ⊆ G.edgeFinset := fun e he => by
    rw [SimpleGraph.mem_edgeFinset]
    exact (G.mem_incidenceFinset x e).mp he |>.1
  have hEx_card : Ex.card = Δ := by rw [G.card_incidenceFinset_eq_degree, hdx]
  set a := (Ex ∩ A).card
  have ha_le_k : a ≤ k := Finset.card_le_card Finset.inter_subset_right
  set W := (G.neighborFinset x).filter (fun z => s(x, z) ∉ A)
  have hW_card : W.card = Δ - a := by
    have hbij : W.card = (Ex \ A).card := by
      refine Finset.card_bij (fun z _ => s(x, z)) ?_ ?_ ?_
      · intro z hz
        simp only [W, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hz
        rw [Finset.mem_sdiff]
        exact ⟨(G.mem_incidenceFinset x _).mpr ⟨hz.1, Sym2.mem_mk_left x z⟩, hz.2⟩
      · intro z₁ _ z₂ _ heq
        rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · rw [← h1, h2]
      · intro e he
        rw [Finset.mem_sdiff, G.mem_incidenceFinset] at he
        rcases he.1 with ⟨heE, hxe⟩
        rcases Sym2.mem_iff_exists.mp hxe with ⟨z, rfl⟩
        have hadj : G.Adj x z := heE
        refine ⟨z, ?_, rfl⟩
        simp only [W, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        exact ⟨hadj, he.2⟩
    rw [hbij, Finset.card_sdiff, hEx_card]
    have hcomm : A ∩ Ex = Ex ∩ A := Finset.inter_comm A Ex
    rw [hcomm]
  have hr_le_W : r ≤ W.card := by omega
  rcases Finset.exists_subset_card_eq hr_le_W with ⟨R, hRW, hRcard⟩
  set X := W \ R
  have hXcard : X.card = k - a := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hRW, hW_card, hRcard]
    omega
  have hx_not_R : x ∉ R := fun hxR => by
    have hxW := hRW hxR
    simp only [W, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hxW
    exact G.loopless.irrefl x hxW.1
  -- Set of edges from x to R, from x to X, and escape edges F \ A
  set ER := R.image (fun z => s(x, z))
  set EX := X.image (fun z => s(x, z))
  set F := G.edgeFinset.filter (fun e => ∃ z ∈ R, ∃ y, y ∉ insert x R ∧ e = s(z, y))
  have hER_sub : ER ⊆ G.edgeFinset \ A := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨z, hzR, rfl⟩
    have hzW := hRW hzR
    simp only [W, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hzW
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨hzW.1, hzW.2⟩
  have hEX_sub : EX ⊆ G.edgeFinset \ A := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨z, hzX, rfl⟩
    have hzW := (Finset.mem_sdiff.mp hzX).1
    simp only [W, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hzW
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨hzW.1, hzW.2⟩
  have hFA_sub : F \ A ⊆ G.edgeFinset \ A :=
    Finset.sdiff_subset_sdiff (Finset.filter_subset _ _) Finset.Subset.rfl
  have hdisj_ER_EX : Disjoint ER EX := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rcases Finset.mem_image.mp h1 with ⟨z₁, hz₁, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨z₂, hz₂, heq⟩
    have hz12 : z₁ = z₂ := by
      rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
      · exact h.symm
      · rw [← h1, ← h2]
    exact (Finset.mem_sdiff.mp hz₂).2 (hz12 ▸ hz₁)
  have hF_not_x : ∀ e ∈ F, x ∉ e := by
    intro e he hxe
    rcases (Finset.mem_filter.mp he).2 with ⟨z, hzR, y, hy, rfl⟩
    rcases Sym2.mem_iff.mp hxe with rfl | rfl
    · exact hx_not_R hzR
    · exact hy (Finset.mem_insert_self x R)
  have hdisj_ER_FA : Disjoint ER (F \ A) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rcases Finset.mem_image.mp h1 with ⟨z, _, rfl⟩
    exact hF_not_x _ (Finset.mem_sdiff.mp h2).1 (Sym2.mem_mk_left x z)
  have hdisj_EX_FA : Disjoint EX (F \ A) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    rcases Finset.mem_image.mp h1 with ⟨z, _, rfl⟩
    exact hF_not_x _ (Finset.mem_sdiff.mp h2).1 (Sym2.mem_mk_left x z)
  -- Sum over ER ∪ EX ∪ (F \ A) ≤ sum over G.edgeFinset \ A
  have hunion_sub : ER ∪ EX ∪ (F \ A) ⊆ G.edgeFinset \ A :=
    Finset.union_subset (Finset.union_subset hER_sub hEX_sub) hFA_sub
  have hsum_le : (∑ e ∈ ER, min k (imb G e)) + (∑ e ∈ EX, min k (imb G e)) +
      (∑ e ∈ F \ A, min k (imb G e)) ≤ ∑ e ∈ G.edgeFinset \ A, min k (imb G e) := by
    have hdisj12 : Disjoint (ER ∪ EX) (F \ A) :=
      Finset.disjoint_union_left.mpr ⟨hdisj_ER_FA, hdisj_EX_FA⟩
    rw [← Finset.sum_union hdisj_ER_EX, ← Finset.sum_union hdisj12]
    exact Finset.sum_le_sum_of_subset hunion_sub
  -- 1. Contribution of ER
  set ρ := ∑ z ∈ R, (G.degree z - r)
  have hER_sum : (∑ e ∈ ER, min k (imb G e)) + ρ = r * k := by
    have hinj : Set.InjOn (fun z => s(x, z)) (R : Set V) := by
      intro z₁ _ z₂ _ heq
      rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
      · exact h
      · rw [← h1, h2]
    rw [Finset.sum_image hinj, ← Finset.sum_add_distrib]
    have hpt : ∀ z ∈ R, min k (imb G s(x, z)) + (G.degree z - r) = k := by
      intro z hzR
      have hzW := hRW hzR
      simp only [W, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hzW
      have hdz_le : G.degree z ≤ Δ := Finset.le_sup (f := fun v : V => G.degree v) (Finset.mem_univ z)
      have himb_xz : imb G s(x, z) = Δ - G.degree z := by
        simp only [imb, Sym2.lift_mk, hdx]
        rw [Nat.dist_eq_sub_of_le_right hdz_le]
      rw [himb_xz]
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, smul_eq_mul, hRcard]
  -- 2. Contribution of EX
  have hEX_sum : k - a ≤ ∑ e ∈ EX, min k (imb G e) := by
    have hEX_card : EX.card = k - a := by
      rw [Finset.card_image_of_injOn]
      · exact hXcard
      · intro z₁ _ z₂ _ heq
        rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
        · exact h
        · rw [← h1, h2]
    have h1 : EX.card = ∑ _e ∈ EX, 1 := by simp
    rw [← hEX_card, h1]
    refine Finset.sum_le_sum fun e he => ?_
    have heE : e ∈ G.edgeSet := (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hEX_sub he)).1)
    have hge1 := himb e heE
    omega
  -- 3. Card of F ≥ ρ
  have hF_card : ρ ≤ F.card := by
    set P := R.biUnion (fun z => ((G.neighborFinset z) \ insert x R).image (fun y => (z, y)))
    have hP_card : P.card = ∑ z ∈ R, ((G.neighborFinset z) \ insert x R).card := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun z _ => ?_
        exact Finset.card_image_of_injective _ fun y₁ y₂ h => (Prod.mk.inj h).2
      · intro z₁ _ z₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp hp2 with ⟨_, _, h⟩
        exact hne (Prod.mk.inj h).1.symm
    have hP_ge : ρ ≤ P.card := by
      rw [hP_card]
      refine Finset.sum_le_sum fun z hzR => ?_
      have hsub_deg : ((G.neighborFinset z) ∩ insert x R).card ≤ r := by
        have hsub : (G.neighborFinset z) ∩ insert x R ⊆ (insert x R).erase z := by
          intro y hy
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hy
          exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy.1).symm, hy.2⟩
        have hle := Finset.card_le_card hsub
        have hz_in : z ∈ insert x R := Finset.mem_insert_of_mem hzR
        rw [Finset.card_erase_of_mem hz_in, Finset.card_insert_of_notMem hx_not_R, hRcard] at hle
        omega
      have hcard_sdiff : ((G.neighborFinset z) \ insert x R).card =
          G.degree z - ((G.neighborFinset z) ∩ insert x R).card := by
        rw [Finset.card_sdiff, Finset.inter_comm, SimpleGraph.degree]
      omega
    have hP_le_F : P.card ≤ F.card := by
      refine Finset.card_le_card_of_injOn (fun p => s(p.1, p.2)) ?_ ?_
      · intro p hp
        rw [Finset.mem_coe, Finset.mem_biUnion] at hp
        rcases hp with ⟨z, hzR, hp'⟩
        rcases Finset.mem_image.mp hp' with ⟨y, hy, rfl⟩
        rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset] at hy
        rw [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
        exact ⟨hy.1, z, hzR, y, hy.2, rfl⟩
      · intro p₁ hp₁ p₂ hp₂ heq
        rw [Finset.mem_coe, Finset.mem_biUnion] at hp₁ hp₂
        rcases hp₁ with ⟨z₁, hz₁, hp₁'⟩
        rcases Finset.mem_image.mp hp₁' with ⟨y₁, hy₁, rfl⟩
        rcases hp₂ with ⟨z₂, hz₂, hp₂'⟩
        rcases Finset.mem_image.mp hp₂' with ⟨y₂, hy₂, rfl⟩
        rw [Finset.mem_sdiff] at hy₁ hy₂
        rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact absurd (Finset.mem_insert_of_mem hz₂) hy₁.2
    omega
  -- 4. Card of F ∩ A ≤ k - a (since F is disjoint from Ex)
  have hFA_card : ρ - (k - a) ≤ (F \ A).card := by
    have hdisj_FA_Ex : Disjoint (F ∩ A) (Ex ∩ A) := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      have hxe : x ∈ e := ((G.mem_incidenceFinset x e).mp (Finset.mem_inter.mp h2).1).2
      exact hF_not_x e (Finset.mem_inter.mp h1).1 hxe
    have hunion_A : (F ∩ A) ∪ (Ex ∩ A) ⊆ A :=
      Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
    have hFA_le : (F ∩ A).card + a ≤ k := by
      have := Finset.card_le_card hunion_A
      rwa [Finset.card_union_of_disjoint hdisj_FA_Ex] at this
    have hsdiff : (F \ A).card = F.card - (F ∩ A).card := by
      rw [Finset.card_sdiff, Finset.inter_comm]
    omega
  -- 5. Contribution of F \ A
  have hFA_sum : ρ - (k - a) ≤ ∑ e ∈ F \ A, min k (imb G e) := by
    have h1 : (F \ A).card = ∑ _e ∈ F \ A, 1 := by simp
    have hge : (F \ A).card ≤ ∑ e ∈ F \ A, min k (imb G e) := by
      rw [h1]
      refine Finset.sum_le_sum fun e he => ?_
      have heE : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hFA_sub he)).1
      have hge1 := himb e heE
      omega
    omega
  -- Combine all three disjoint pieces!
  have hcombine : r * k ≤ (∑ e ∈ ER, min k (imb G e)) + (∑ e ∈ EX, min k (imb G e)) +
      (∑ e ∈ F \ A, min k (imb G e)) := by
    omega
  have hrk_comm : k * r = r * k := Nat.mul_comm k r
  omega

private lemma parity_imb {V : Type} [Fintype V] (G : SimpleGraph V) :
    Even (∑ e ∈ G.edgeFinset, imb G e) := by
  have hmod : (∑ e ∈ G.edgeFinset, imb G e) % 2 =
      (∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => G.degree u + G.degree v, fun _ _ => Nat.add_comm _ _⟩ e) % 2 := by
    rw [Finset.sum_nat_mod]
    symm
    rw [Finset.sum_nat_mod]
    symm
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    induction e using Sym2.ind with
    | _ u v =>
        simp only [imb, Sym2.lift_mk]
        rcases le_total (G.degree u) (G.degree v) with h | h
        · rw [Nat.dist_eq_sub_of_le h]
          obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
          rw [ht]; omega
        · rw [Nat.dist_eq_sub_of_le_right h]
          obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h
          rw [ht]; omega
  have hsum_deg_sq : (∑ e ∈ G.edgeFinset,
      Sym2.lift ⟨fun u v => G.degree u + G.degree v, fun _ _ => Nat.add_comm _ _⟩ e) =
      ∑ v : V, G.degree v * G.degree v := by
    have h1 : ∀ e ∈ G.edgeFinset,
        Sym2.lift ⟨fun u v => G.degree u + G.degree v, fun _ _ => Nat.add_comm _ _⟩ e =
        ∑ v : V, if v ∈ e then G.degree v else 0 := by
      intro e he
      have heE : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
      induction e using Sym2.ind with
      | _ u v =>
          have huv : u ≠ v := G.ne_of_adj heE
          simp only [Sym2.lift_mk]
          have hflt : Finset.univ.filter (fun w : V => w ∈ s(u, v)) = {u, v} := by
            ext w
            simp [Sym2.mem_iff]
          rw [← Finset.sum_filter, hflt, Finset.sum_pair huv]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    congr 1
    have heq : G.edgeFinset.filter (fun e => v ∈ e) = G.incidenceFinset v := by
      ext e
      simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_incidenceFinset]
      rfl
    rw [heq, G.card_incidenceFinset_eq_degree]
  have hsq_mod : (∑ v : V, G.degree v * G.degree v) % 2 = (∑ v : V, G.degree v) % 2 := by
    rw [Finset.sum_nat_mod]
    symm
    rw [Finset.sum_nat_mod]
    symm
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    have : G.degree v % 2 = 0 ∨ G.degree v % 2 = 1 := Nat.mod_two_eq_zero_or_one _
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have h2m : (∑ v : V, G.degree v) % 2 = 0 := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
    omega
  rw [Nat.even_iff, hmod, hsum_deg_sq, hsq_mod, h2m]

private def insertDesc {α : Type} (f : α → ℕ) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if f y ≤ f x then x :: y :: ys else y :: insertDesc f x ys

private def sortDesc {α : Type} (f : α → ℕ) : List α → List α
  | [] => []
  | x :: xs => insertDesc f x (sortDesc f xs)

private lemma insertDesc_perm {α : Type} (f : α → ℕ) (x : α) :
    ∀ xs : List α, (insertDesc f x xs).Perm (x :: xs)
  | [] => List.Perm.refl _
  | y :: ys => by
      unfold insertDesc
      split_ifs
      · exact List.Perm.refl _
      · exact ((insertDesc_perm f x ys).cons y).trans (List.Perm.swap x y ys)

private lemma sortDesc_perm {α : Type} (f : α → ℕ) :
    ∀ xs : List α, (sortDesc f xs).Perm xs
  | [] => List.Perm.refl _
  | x :: xs => (insertDesc_perm f x _).trans ((sortDesc_perm f xs).cons x)

private lemma insertDesc_pairwise {α : Type} (f : α → ℕ) (x : α) :
    ∀ {xs : List α}, xs.Pairwise (fun a b => f b ≤ f a) →
      (insertDesc f x xs).Pairwise (fun a b => f b ≤ f a)
  | [], _ => List.pairwise_singleton _ _
  | y :: ys, h => by
      unfold insertDesc
      split_ifs with hxy
      · refine List.pairwise_cons.mpr ⟨fun z hz => ?_, h⟩
        rcases List.mem_cons.mp hz with rfl | hzy
        · exact hxy
        · exact le_trans ((List.pairwise_cons.mp h).1 z hzy) hxy
      · have hrel : f x ≤ f y := by omega
        refine List.pairwise_cons.mpr ⟨fun z hz => ?_, insertDesc_pairwise f x (List.pairwise_cons.mp h).2⟩
        have hmem : z ∈ x :: ys := (insertDesc_perm f x ys).subset hz
        rcases List.mem_cons.mp hmem with rfl | hzy
        · exact hrel
        · exact (List.pairwise_cons.mp h).1 z hzy

private lemma sortDesc_pairwise {α : Type} (f : α → ℕ) :
    ∀ xs : List α, (sortDesc f xs).Pairwise (fun a b => f b ≤ f a)
  | [] => List.Pairwise.nil
  | x :: xs => insertDesc_pairwise f x (sortDesc_pairwise f xs)

end MO426935Proof

theorem OMA.solution : type_of% @OMA.S_mo_426935.main := by
  classical
  intro V _ G himb
  by_cases hemp : G.edgeFinset = ∅
  · refine ⟨0, ⊥, ?_⟩
    simp [OMA.S_mo_426935.M, hemp]
  have hne : G.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
  set m := G.edgeFinset.card
  -- Sort the edges of G in non-increasing order of imb G
  set L := MO426935Proof.sortDesc (OMA.S_mo_426935.imb G) G.edgeFinset.toList
  have hL_perm : L.Perm G.edgeFinset.toList := MO426935Proof.sortDesc_perm _ _
  have hL_len : L.length = m := by
    rw [hL_perm.length_eq, Finset.length_toList]
  have hL_nd : L.Nodup := hL_perm.nodup_iff.mpr (Finset.nodup_toList _)
  have hL_mem : ∀ e, e ∈ L ↔ e ∈ G.edgeFinset := fun e => by
    rw [hL_perm.mem_iff, Finset.mem_toList]
  have hL_sorted : L.Pairwise (fun e₁ e₂ => OMA.S_mo_426935.imb G e₂ ≤ OMA.S_mo_426935.imb G e₁) :=
    MO426935Proof.sortDesc_pairwise _ _
  let edgeAt : Fin m → Sym2 V := fun i => L.get (i.cast hL_len.symm)
  have hedgeAt_inj : Function.Injective edgeAt := by
    intro i j hij
    have hcast : i.cast hL_len.symm = j.cast hL_len.symm :=
      (List.nodup_iff_injective_get.mp hL_nd) hij
    have hval : (i.cast hL_len.symm).val = (j.cast hL_len.symm).val := congrArg Fin.val hcast
    exact Fin.ext hval
  have hedgeAt_mem : ∀ i : Fin m, edgeAt i ∈ G.edgeFinset := fun i =>
    (hL_mem _).mp (List.get_mem _ _)
  have hedgeAt_surj : ∀ e ∈ G.edgeFinset, ∃ i : Fin m, edgeAt i = e := by
    intro e he
    rcases List.mem_iff_get.mp ((hL_mem e).mpr he) with ⟨j, rfl⟩
    exact ⟨j.cast hL_len, by simp [edgeAt]⟩
  let d : Fin m → ℕ := fun i => OMA.S_mo_426935.imb G (edgeAt i)
  have hd_anti : Antitone d := by
    intro i j hij
    by_cases heq : i = j
    · rw [heq]
    · have hlt : (i.cast hL_len.symm) < (j.cast hL_len.symm) := by
        change i.val < j.val
        exact lt_of_le_of_ne hij (fun h => heq (Fin.ext h))
      exact List.pairwise_iff_get.mp hL_sorted _ _ hlt
  have hM_eq : (Finset.univ : Finset (Fin m)).val.map d = OMA.S_mo_426935.M G := by
    unfold OMA.S_mo_426935.M
    have heq_edges : (Finset.univ : Finset (Fin m)).val.map edgeAt = G.edgeFinset.val := by
      have hnd1 : ((Finset.univ : Finset (Fin m)).val.map edgeAt).Nodup :=
        Multiset.Nodup.map hedgeAt_inj (Finset.univ : Finset (Fin m)).nodup
      exact (Multiset.Nodup.ext hnd1 G.edgeFinset.nodup).mpr fun e => by
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and]
        exact ⟨fun ⟨i, hi⟩ => hi ▸ hedgeAt_mem i, hedgeAt_surj e⟩
    rw [← heq_edges, Multiset.map_map]
    rfl
  have hsum_eq : (∑ i : Fin m, d i) = ∑ e ∈ G.edgeFinset, OMA.S_mo_426935.imb G e := by
    change ((Finset.univ : Finset (Fin m)).val.map d).sum = (OMA.S_mo_426935.M G).sum
    exact congrArg Multiset.sum hM_eq
  have hd_even : Even (∑ i : Fin m, d i) := by
    rw [hsum_eq]
    exact MO426935Proof.parity_imb G
  have hEG : MO426935Proof.EGCond d := by
    refine ⟨hd_anti, hd_even, fun k hk => ?_⟩
    set K := Finset.univ.filter (fun i : Fin m => i.val < k)
    set Lidx := Finset.univ.filter (fun i : Fin m => k ≤ i.val)
    set A := K.image edgeAt
    have hK_card : K.card = k := by
      have heq : K = (Finset.range k).attach.image
          (fun j => ⟨j.1, lt_of_lt_of_le (Finset.mem_range.mp j.2) hk⟩) := by
        ext x
        simp only [K, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range]
        exact ⟨fun hx => ⟨x.val, hx, Fin.ext rfl⟩, fun ⟨_, ha, h⟩ => h ▸ ha⟩
      rw [heq, Finset.card_image_of_injective]
      · simp
      · intro a b hab; exact Subtype.ext (congrArg Fin.val hab)
    have hA_card : A.card = k := by
      rw [Finset.card_image_of_injective _ hedgeAt_inj, hK_card]
    have hA_sub : A ⊆ G.edgeFinset := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
      exact hedgeAt_mem i
    have hcomp_eq : G.edgeFinset \ A = Lidx.image edgeAt := by
      ext e
      simp only [Finset.mem_sdiff, A, Lidx, K, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨heG, hnot⟩
        rcases hedgeAt_surj e heG with ⟨i, rfl⟩
        refine ⟨i, ?_, rfl⟩
        by_contra hlt
        exact hnot ⟨i, lt_of_not_ge hlt, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        refine ⟨hedgeAt_mem i, ?_⟩
        rintro ⟨j, hj, heq⟩
        have := hedgeAt_inj heq
        subst this
        omega
    set Δ := Finset.univ.sup (fun v : V => G.degree v)
    have hcap := MO426935Proof.capacity_bound G himb hne A hA_sub
    rw [hA_card, hcomp_eq, Finset.sum_image (fun a _ b _ h => hedgeAt_inj h)] at hcap
    have himb_le : ∀ i ∈ K, d i ≤ Δ - 1 := by
      intro i _
      have heE : edgeAt i ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp (hedgeAt_mem i)
      have hpos := himb (edgeAt i) heE
      change OMA.S_mo_426935.imb G (edgeAt i) ≤ Δ - 1
      generalize hge : edgeAt i = e at heE hpos ⊢
      induction e using Sym2.ind with
      | _ u v =>
          have hu_le : G.degree u ≤ Δ := Finset.le_sup (f := fun w : V => G.degree w) (Finset.mem_univ u)
          have hv_le : G.degree v ≤ Δ := Finset.le_sup (f := fun w : V => G.degree w) (Finset.mem_univ v)
          have hu_pos : 1 ≤ G.degree u := Finset.card_pos.mpr ⟨v, by simpa using heE⟩
          have hv_pos : 1 ≤ G.degree v := Finset.card_pos.mpr ⟨u, by simpa [SimpleGraph.adj_comm] using heE⟩
          simp only [OMA.S_mo_426935.imb, Sym2.lift_mk] at hpos ⊢
          rcases le_total (G.degree u) (G.degree v) with h | h
          · rw [Nat.dist_eq_sub_of_le h]; omega
          · rw [Nat.dist_eq_sub_of_le_right h]; omega
    have hsum_K_le : (∑ i ∈ K, d i) ≤ k * (Δ - 1) := by
      calc
        ∑ i ∈ K, d i ≤ ∑ _i ∈ K, (Δ - 1) := Finset.sum_le_sum himb_le
        _ = K.card * (Δ - 1) := by rw [Finset.sum_const, smul_eq_mul]
        _ = k * (Δ - 1) := by rw [hK_card]
    have hmid : k * (Δ - 1) ≤ k * (k - 1) + k * (Δ - k) := by
      by_cases hle : k ≤ Δ
      · by_cases hk0 : k = 0
        · simp [hk0]
        · have : Δ - 1 = (k - 1) + (Δ - k) := by omega
          rw [this, Nat.mul_add]
      · have h1 : Δ - 1 ≤ k - 1 := by omega
        exact le_trans (Nat.mul_le_mul_left k h1) (Nat.le_add_right _ _)
    exact le_trans hsum_K_le (le_trans hmid (Nat.add_le_add_left hcap _))
  rcases MO426935Proof.erdos_gallai d hEG with ⟨H, hH⟩
  refine ⟨m, H, ?_⟩
  rw [← hM_eq]
  exact Multiset.map_congr rfl fun i _ => hH i
