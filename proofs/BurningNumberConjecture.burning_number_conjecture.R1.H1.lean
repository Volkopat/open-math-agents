import OMAReductions.R_BurningNumberConjecture_burning_number_conjecture_R1

-- Step BurningNumberConjecture.burning_number_conjecture.R1.H1: hypothesis H1 of reduction BurningNumberConjecture.burning_number_conjecture.R1
-- Credit: @lettucrisp

/-!
# Burning number conjecture for spiders

We prove that every spider (tree with at most one vertex of degree ≥ 3) on `n ≤ k^2` vertices
burns in at most `k` rounds (`burningNumber T ≤ k`), following the Bonato–Lidbetter /
Das–Dev–Sadhukhan–Sahoo–Sen approach:

1. **Tree-to-spider decomposition**: Using `SimpleGraph.IsTree.existsUnique_path` from the center
   `c`, any two paths from `c` sharing their first step agree on their common prefix (because every
   vertex `x ≠ c` has degree ≤ 2). Thus `V \ {c}` partitions into disjoint path-arms indexed by
   neighbors of `c`, with explicit upper bounds on graph distance.
2. **Universal path-forest burning lemma**: By induction on `m ≥ 1`, any list `P` of `t` positive
   arm-segments with total length `N ≤ min(m^2, m * (m + 2 - t))`, excluding only the `m`-tuple
   `[2, ..., 2]` and the 2-tuple `{m^2 - 2, 2}`, can be covered by `m` balls of radii
   `m - 1, m - 2, ..., 0`.
3. **Spider induction on `k`**: If some arm has length `≥ 2k - 1`, peel `2k - 1` vertices from its
   tip with radius `k - 1` and recurse on `k - 1`. Otherwise every arm has length `≤ 2k - 2`.
   Placing radius `k - 1` at `c` leaves a path-forest satisfying the universal lemma unless
   `k ≥ 3` and the spider consists of `k - 1` arms of length `k + 1`; in that unique case, placing
   radius `k - 1` at depth `2` on one arm leaves `k - 2` segments of length `4`, burned by radii
   `k - 2, ..., 2` (one per segment for `k - 3` segments) plus `1` and `0` on the last segment.
-/

namespace SpiderBurning

open BurningNumberConjecture SimpleGraph Finset
open scoped Classical

section AbstractSpider

/-- A segment on an arm `u`, representing depths `d` with `lo ≤ d < lo + len`. -/
private structure Seg (A : Type*) where
  arm : A
  lo : ℕ
  len : ℕ

/-- An abstract spider metric interface on a vertex type `V` with center `c` and finite arm index `A`. -/
private structure SpiderData (V A : Type*) (T : SimpleGraph V) where
  c : V
  armLen : A → ℕ
  vert : (u : A) → (d : ℕ) → 1 ≤ d → d ≤ armLen u → V
  dist_c : ∀ (u : A) (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ armLen u),
    T.dist c (vert u d h1 h2) ≤ d
  dist_same : ∀ (u : A) (d₁ d₂ : ℕ) (h1 : 1 ≤ d₁) (h2 : d₁ ≤ armLen u)
    (h3 : 1 ≤ d₂) (h4 : d₂ ≤ armLen u),
    T.dist (vert u d₁ h1 h2) (vert u d₂ h3 h4) ≤ Nat.dist d₁ d₂
  dist_diff : ∀ (u₁ u₂ : A) (d₁ d₂ : ℕ) (h1 : 1 ≤ d₁) (h2 : d₁ ≤ armLen u₁)
    (h3 : 1 ≤ d₂) (h4 : d₂ ≤ armLen u₂),
    T.dist (vert u₁ d₁ h1 h2) (vert u₂ d₂ h3 h4) ≤ d₁ + d₂
  cover_all : ∀ v : V, v = c ∨ ∃ (u : A) (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ armLen u),
    v = vert u d h1 h2

private def Seg.Valid {V A : Type*} {T : SimpleGraph V} (S : SpiderData V A T) (s : Seg A) : Prop :=
  1 ≤ s.lo ∧ 1 ≤ s.len ∧ s.lo + s.len ≤ S.armLen s.arm + 1

/-- `xs : Fin m → V` burns every vertex in every segment of `P` with radii `m - 1 - i`. -/
private def BurnsSegs {V A : Type*} {T : SimpleGraph V} (S : SpiderData V A T)
    (P : List (Seg A)) {m : ℕ} (xs : Fin m → V) : Prop :=
  ∀ s ∈ P, ∀ (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ S.armLen s.arm),
    s.lo ≤ d → d < s.lo + s.len →
    ∃ i : Fin m, T.dist (xs i) (S.vert s.arm d h1 h2) + i.val < m

/-- Placing a ball of radius `r` on a valid segment `s` covers its first `min (2*r+1) s.len` vertices. -/
private lemma seg_ball_cover {V A : Type*} {T : SimpleGraph V} (S : SpiderData V A T)
    {s : Seg A} (hs : s.Valid S) (r : ℕ) :
    ∃ z : V, ∀ (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ S.armLen s.arm),
      s.lo ≤ d → d < s.lo + s.len → d < s.lo + (2 * r + 1) →
      T.dist z (S.vert s.arm d h1 h2) ≤ r := by
  have hlo := hs.1
  have hlen := hs.2.1
  have hbound := hs.2.2
  let ctr := min (s.lo + r) (s.lo + s.len - 1)
  have hctr1 : 1 ≤ ctr := by dsimp [ctr]; omega
  have hctr2 : ctr ≤ S.armLen s.arm := by dsimp [ctr]; omega
  refine ⟨S.vert s.arm ctr hctr1 hctr2, fun d h1 h2 hd1 hd2 hd3 => ?_⟩
  have hdist := S.dist_same s.arm ctr d hctr1 hctr2 h1 h2
  have hnat : Nat.dist ctr d ≤ r := by
    rw [Nat.dist_eq_max_sub_min]
    dsimp [ctr]
    omega
  exact le_trans hdist hnat

/-- List helper: removing one element splits a list into `l₁ ++ [a] ++ l₂`. -/
private lemma list_exists_max_len {A : Type*} {P : List (Seg A)} (hne : P ≠ []) :
    ∃ (l₁ l₂ : List (Seg A)) (s : Seg A), P = l₁ ++ s :: l₂ ∧ ∀ x ∈ P, x.len ≤ s.len := by
  induction P with
  | nil => exact (hne rfl).elim
  | cons a t ih =>
    cases t with
    | nil => exact ⟨[], [], a, rfl, fun x hx => by simp at hx; subst hx; exact le_rfl⟩
    | cons b t' =>
      obtain ⟨l₁, l₂, s, heq, hmax⟩ := ih (List.cons_ne_nil b t')
      by_cases hab : s.len ≤ a.len
      · refine ⟨[], b :: t', a, rfl, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact le_rfl
        · exact le_trans (hmax x hx') hab
      · refine ⟨a :: l₁, l₂, s, by simp [heq], fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · omega
        · exact hmax x hx'

private lemma list_exists_mem_split {α : Type*} {P : List α} {a : α} (h : a ∈ P) :
    ∃ l₁ l₂ : List α, P = l₁ ++ a :: l₂ := by
  induction P with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | hxs
    · exact ⟨[], xs, rfl⟩
    · obtain ⟨l₁, l₂, rfl⟩ := ih hxs
      exact ⟨x :: l₁, l₂, rfl⟩

private lemma list_sum_le_length_mul_max {A : Type*} (P : List (Seg A)) (M : ℕ)
    (hM : ∀ s ∈ P, s.len ≤ M) : (P.map Seg.len).sum ≤ P.length * M := by
  induction P with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have ha : a.len ≤ M := hM a (List.mem_cons_self ..)
    have ht : (t.map Seg.len).sum ≤ t.length * M := ih fun s hs => hM s (List.mem_cons_of_mem _ hs)
    omega

private lemma list_length_le_sum {A : Type*} (P : List (Seg A)) (hpos : ∀ s ∈ P, 1 ≤ s.len) :
    P.length ≤ (P.map Seg.len).sum := by
  induction P with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have ha := hpos a (List.mem_cons_self ..)
    have ht := ih fun s hs => hpos s (List.mem_cons_of_mem _ hs)
    omega

private lemma list_sum_eq_two_mul_of_all_two {A : Type*} (P : List (Seg A))
    (h : ∀ s ∈ P, s.len = 2) : (P.map Seg.len).sum = 2 * P.length := by
  induction P with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := h a (List.mem_cons_self ..)
    have ht := ih fun s hs => h s (List.mem_cons_of_mem _ hs)
    omega

/-- Arithmetic helper for Case 3 of `burn_path_forest`: removing the maximal segment `s`
preserves all four path-forest burning invariants. -/
private lemma burn_path_forest_case3_invariants {A : Type*} {m' : ℕ} (hm'_pos : 1 ≤ m')
    {P l₁ l₂ : List (Seg A)} {s : Seg A}
    (hPeq : P = l₁ ++ s :: l₂)
    (hmax : ∀ x ∈ P, x.len ≤ s.len)
    (hN1 : (P.map Seg.len).sum ≤ (m' + 1) ^ 2)
    (hN2 : (P.map Seg.len).sum + (m' + 1) * P.length ≤ (m' + 1) * (m' + 3))
    (ht_le_m : P.length ≤ m' + 1)
    (hnot2 : ¬ (P.length = m' + 1 ∧ ∀ x ∈ P, x.len = 2))
    (hP'_ne : l₁ ++ l₂ ≠ []) :
    let P' := l₁ ++ l₂
    (P'.map Seg.len).sum ≤ m' ^ 2 ∧
    (P'.map Seg.len).sum + m' * P'.length ≤ m' * (m' + 2) ∧
    ¬ (P'.length = m' ∧ ∀ x ∈ P', x.len = 2) ∧
    ¬ (2 ≤ m' ∧ P'.length = 2 ∧ (P'.map Seg.len).sum = m' ^ 2 ∧ ∃ x ∈ P', x.len = 2) := by
  intro P'
  have hlen' : P'.length + 1 = P.length := by rw [hPeq]; simp [P']; omega
  have hsum' : (P'.map Seg.len).sum + s.len = (P.map Seg.len).sum := by rw [hPeq]; simp [P']; omega
  have ht'_pos : 1 ≤ P'.length := List.length_pos_iff.mpr hP'_ne
  have ht_ge2 : 2 ≤ P.length := by omega
  have hmax_avg : (P.map Seg.len).sum ≤ P.length * s.len :=
    list_sum_le_length_mul_max P s.len hmax
  have havg : P.length * (P'.map Seg.len).sum ≤ P'.length * (P.map Seg.len).sum := by
    have e1 : P.length * (P'.map Seg.len).sum + P.length * s.len = P.length * (P.map Seg.len).sum := by
      rw [← Nat.mul_add, hsum']
    have e2 : P'.length * (P.map Seg.len).sum + (P.map Seg.len).sum = P.length * (P.map Seg.len).sum := by
      rw [← hlen', Nat.add_mul, one_mul]
    omega
  have hN2' : (P'.map Seg.len).sum + m' * P'.length ≤ m' * (m' + 2) := by
    let d := m' + 3 - P.length
    have hd_add : P.length + d = m' + 3 := by dsimp [d]; omega
    have hd_add' : P'.length + d = m' + 2 := by omega
    have hN_le_d : (P.map Seg.len).sum ≤ (m' + 1) * d := by
      have heq : (m' + 1) * P.length + (m' + 1) * d = (m' + 1) * (m' + 3) := by
        rw [← Nat.mul_add, hd_add]
      omega
    have h3 : P'.length * (m' + 1) ≤ P.length * m' := by nlinarith only [hlen', ht_le_m]
    have hmul : P.length * (P'.map Seg.len).sum ≤ P.length * (m' * d) := by
      calc P.length * (P'.map Seg.len).sum
          ≤ P'.length * (P.map Seg.len).sum := havg
        _ ≤ P'.length * ((m' + 1) * d) := Nat.mul_le_mul_left _ hN_le_d
        _ = (P'.length * (m' + 1)) * d := (Nat.mul_assoc ..).symm
        _ ≤ (P.length * m') * d := Nat.mul_le_mul_right d h3
        _ = P.length * (m' * d) := Nat.mul_assoc ..
    have hN'_le : (P'.map Seg.len).sum ≤ m' * d :=
      Nat.le_of_mul_le_mul_left hmul (by omega)
    have heq' : m' * P'.length + m' * d = m' * (m' + 2) := by
      rw [← Nat.mul_add, hd_add']
    omega
  have hN1' : (P'.map Seg.len).sum ≤ m' ^ 2 := by
    by_cases ht'2 : 2 ≤ P'.length
    · nlinarith only [hN2', ht'2]
    · have ht'1 : P'.length = 1 := by omega
      have ht2 : P.length = 2 := by omega
      have h2N' : 2 * (P'.map Seg.len).sum ≤ (m' + 1) ^ 2 := by
        rw [ht'1, ht2] at havg; omega
      by_cases hm'1 : m' = 1
      · subst hm'1
        by_contra hgt
        have hN'2 : (P'.map Seg.len).sum = 2 := by omega
        have hs2 : s.len = 2 := by rw [ht2] at hmax_avg; omega
        apply hnot2
        refine ⟨by omega, fun x hx => ?_⟩
        rw [hPeq] at hx
        simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with hx1 | rfl | hx2
        · have hmem : x ∈ P' := List.mem_append_left _ hx1
          have hsingleton : P' = [x] := by
            cases hP' : P' with
            | nil => exact (hP'_ne hP').elim
            | cons u v =>
              rw [hP'] at ht'1 hmem
              have hv : v = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at ht'1; omega)
              subst hv; simp at hmem; subst hmem; rfl
          rw [hsingleton] at hN'2; simpa using hN'2
        · exact hs2
        · have hmem : x ∈ P' := List.mem_append_right _ hx2
          have hsingleton : P' = [x] := by
            cases hP' : P' with
            | nil => exact (hP'_ne hP').elim
            | cons u v =>
              rw [hP'] at ht'1 hmem
              have hv : v = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at ht'1; omega)
              subst hv; simp at hmem; subst hmem; rfl
          rw [hsingleton] at hN'2; simpa using hN'2
      · have hm'2 : 2 ≤ m' := by omega
        nlinarith only [h2N', hm'2]
  have hnot2' : ¬ (P'.length = m' ∧ ∀ x ∈ P', x.len = 2) := by
    rintro ⟨h1, h2⟩
    have hsum2 := list_sum_eq_two_mul_of_all_two P' h2
    have ht_m : P.length = m' + 1 := by omega
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil P' hP'_ne
    have hyP : y ∈ P := by
      rw [hPeq]; simp only [P', List.mem_append, List.mem_cons] at hy ⊢; tauto
    have hs_ge2 : 2 ≤ s.len := by
      have hmy := hmax y hyP; rw [h2 y hy] at hmy; exact hmy
    have hs_eq2 : s.len = 2 := by
      rw [h1] at hsum2
      rw [ht_m] at hN2
      have hring : (m' + 1) * (m' + 1) + 2 * (m' + 1) = (m' + 1) * (m' + 3) := by ring
      omega
    apply hnot2
    refine ⟨ht_m, fun x hx => ?_⟩
    rw [hPeq] at hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx1 | rfl | hx2
    · exact h2 x (List.mem_append_left _ hx1)
    · exact hs_eq2
    · exact h2 x (List.mem_append_right _ hx2)
  have hnotBig' : ¬ (2 ≤ m' ∧ P'.length = 2 ∧ (P'.map Seg.len).sum = m' ^ 2 ∧
      ∃ x ∈ P', x.len = 2) := by
    rintro ⟨hm'2, hlen2, hsum_m'2, x, hxP', hx2⟩
    have ht3 : P.length = 3 := by omega
    obtain ⟨l₁', l₂', hP'eq⟩ := list_exists_mem_split hxP'
    have hrest_len : (l₁' ++ l₂').length = 1 := by
      rw [hP'eq] at hlen2; simp at hlen2 ⊢; omega
    have hrest_ne : l₁' ++ l₂' ≠ [] := by
      intro he; rw [he] at hrest_len; simp at hrest_len
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil (l₁' ++ l₂') hrest_ne
    have hl : l₁' ++ l₂' = [b] := by
      cases h : l₁' ++ l₂' with
      | nil => exact (hrest_ne h).elim
      | cons u v =>
        rw [h] at hrest_len hb
        have hv : v = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hrest_len; omega)
        subst hv; simp at hb; subst hb; rfl
    have hbP' : b ∈ P' := by
      rw [hP'eq]; simp only [List.mem_append, List.mem_cons] at hb ⊢; tauto
    have hbP : b ∈ P := by
      rw [hPeq]; simp only [P', List.mem_append, List.mem_cons] at hbP' ⊢; tauto
    have hb_len : b.len = m' ^ 2 - 2 := by
      have hs_eq : (P'.map Seg.len).sum = x.len + ((l₁' ++ l₂').map Seg.len).sum := by
        rw [hP'eq]; simp; omega
      rw [hl, hx2] at hs_eq; simp at hs_eq; omega
    have hs_ge_b : m' ^ 2 - 2 ≤ s.len := by
      have hmb := hmax b hbP; rw [hb_len] at hmb; exact hmb
    have hm'_eq2 : m' = 2 := by
      rw [ht3] at hN2
      have hring : (m' + 1) * 3 + (m' + 1) * m' = (m' + 1) * (m' + 3) := by ring
      have hN_le : (P.map Seg.len).sum ≤ (m' + 1) * m' := by omega
      have hsq : 4 ≤ m' ^ 2 := by nlinarith only [hm'2]
      have hineq : 2 * m' ^ 2 ≤ (m' + 1) * m' + 2 := by omega
      nlinarith only [hineq, hm'2]
    apply hnot2'
    refine ⟨by omega, fun y hy => ?_⟩
    rw [hP'eq] at hy
    simp only [List.mem_append, List.mem_cons] at hy
    rcases hy with hy1 | rfl | hy2
    · have hyb : y = b := by
        have : y ∈ l₁' ++ l₂' := List.mem_append_left _ hy1
        rw [hl] at this; simpa using this
      rw [hyb, hb_len, hm'_eq2]; norm_num
    · exact hx2
    · have hyb : y = b := by
        have : y ∈ l₁' ++ l₂' := List.mem_append_right _ hy2
        rw [hl] at this; simpa using this
      rw [hyb, hb_len, hm'_eq2]; norm_num
  exact ⟨hN1', hN2', hnot2', hnotBig'⟩

/-- **Universal Path-Forest Burning Lemma**: any list `P` of `t` valid segments with total length
`N ≤ min(m^2, m*(m+2-t))`, excluding only `[2,...,2]` (length `m`) and `{m^2-2, 2}`, burns in
`m` rounds (radii `m-1, ..., 0`). -/
private lemma burn_path_forest {V A : Type*} {T : SimpleGraph V} (S : SpiderData V A T) :
    ∀ (m : ℕ), 1 ≤ m → ∀ (P : List (Seg A)),
      (∀ s ∈ P, s.Valid S) →
      (P.map Seg.len).sum ≤ m ^ 2 →
      (P.map Seg.len).sum + m * P.length ≤ m * (m + 2) →
      ¬ (P.length = m ∧ ∀ s ∈ P, s.len = 2) →
      ¬ (2 ≤ m ∧ P.length = 2 ∧ (P.map Seg.len).sum = m ^ 2 ∧ ∃ s ∈ P, s.len = 2) →
      ∃ xs : Fin m → V, BurnsSegs S P xs := by
  intro m hm
  induction m with
  | zero => omega
  | succ m' ih =>
    intro P hval hN1 hN2 hnot2 hnotBig
    set m := m' + 1
    by_cases hP_empty : P = []
    · subst hP_empty
      exact ⟨fun _ => S.c, fun _ hs => by simp at hs⟩
    by_cases hm1 : m' = 0
    · -- Base case m = 1
      subst hm1
      dsimp [m] at hN1
      have hlen_le : P.length ≤ (P.map Seg.len).sum :=
        list_length_le_sum P fun s hs => (hval s hs).2.1
      have hP1 : P.length = 1 := by
        cases P with
        | nil => exact (hP_empty rfl).elim
        | cons a t =>
          have ha1 : 1 ≤ a.len := (hval a (by simp)).2.1
          simp only [List.length_cons, List.map_cons, List.sum_cons] at hlen_le hN1 ⊢
          omega
      rcases P with _ | ⟨a, _ | ⟨b, t⟩⟩
      · exact (hP_empty rfl).elim
      · have ha1 : a.len = 1 := by
          have := (hval a (by simp)).2.1
          simp at hN1
          omega
        obtain ⟨z, hz⟩ := seg_ball_cover S (hval a (by simp)) 0
        refine ⟨fun _ => z, fun s hs d h1 h2 hd1 hd2 => ?_⟩
        simp only [List.mem_singleton] at hs
        subst hs
        refine ⟨⟨0, by dsimp [m]; omega⟩, ?_⟩
        have hdist := hz d h1 h2 hd1 hd2 (by omega)
        dsimp [m]
        omega
      · simp at hP1
    · -- Inductive step: m = m' + 1 ≥ 2, so 1 ≤ m'
      have hm'_pos : 1 ≤ m' := by omega
      have hpos : ∀ s ∈ P, 1 ≤ s.len := fun s hs => (hval s hs).2.1
      have ht_le_N : P.length ≤ (P.map Seg.len).sum := list_length_le_sum P hpos
      have ht_le_m : P.length ≤ m := by
        nlinarith only [ht_le_N, hN2]
      let C := 2 * m' + 1
      -- Case 1: there is a segment of length exactly C = 2*m - 1
      by_cases hexC : ∃ s ∈ P, s.len = C
      · obtain ⟨s, hs_mem, hs_len⟩ := hexC
        obtain ⟨l₁, l₂, hPeq⟩ := list_exists_mem_split hs_mem
        let P' := l₁ ++ l₂
        have hval' : ∀ x ∈ P', x.Valid S := fun x hx =>
          hval x (by rw [hPeq]; simp only [P', List.mem_append, List.mem_cons] at hx ⊢; tauto)
        have hlen' : P'.length + 1 = P.length := by
          rw [hPeq]; simp [P']; omega
        have hsum' : (P'.map Seg.len).sum + C = (P.map Seg.len).sum := by
          rw [hPeq]; simp [P', hs_len]; omega
        obtain ⟨z, hz⟩ := seg_ball_cover S (hval s hs_mem) m'
        by_cases hP'_empty : P' = []
        · refine ⟨Fin.cons z (fun _ => S.c), fun x hx d h1 h2 hd1 hd2 => ?_⟩
          have hx_eq : x = s := by
            rw [hPeq] at hx
            have hl1 : l₁ = [] := (List.append_eq_nil_iff.mp hP'_empty).1
            have hl2 : l₂ = [] := (List.append_eq_nil_iff.mp hP'_empty).2
            rw [hl1, hl2] at hx
            simpa using hx
          subst hx_eq
          refine ⟨0, ?_⟩
          have hdist := hz d h1 h2 hd1 hd2 (by dsimp [C] at *; omega)
          simp only [Fin.cons_zero, Fin.val_zero, add_zero, m]
          omega
        · have ht_ge2 : 2 ≤ P.length := by
            have h1 : 1 ≤ P'.length := List.length_pos_iff.mpr hP'_empty
            omega
          have hN1' : (P'.map Seg.len).sum ≤ m' ^ 2 := by
            dsimp [C, m] at hsum' hN1
            nlinarith only [hsum', hN1]
          -- Strict inequality: sum(P') + m' * len(P') < m' * (m' + 2)
          have hN2'_strict : (P'.map Seg.len).sum + m' * P'.length < m' * (m' + 2) := by
            dsimp [C, m] at hsum' hN2 ⊢
            nlinarith only [hsum', hN2, hlen', ht_ge2, hm'_pos]
          have hnot2' : ¬ (P'.length = m' ∧ ∀ x ∈ P', x.len = 2) := by
            rintro ⟨h1, h2⟩
            have hsum2 := list_sum_eq_two_mul_of_all_two P' h2
            nlinarith only [h1, hsum2, hN2'_strict]
          have hnotBig' : ¬ (2 ≤ m' ∧ P'.length = 2 ∧ (P'.map Seg.len).sum = m' ^ 2 ∧
              ∃ x ∈ P', x.len = 2) := by
            rintro ⟨_, h1, h2, _⟩
            nlinarith only [h1, h2, hN2'_strict]
          obtain ⟨xs', hxs'⟩ := ih hm'_pos P' hval' hN1' (le_of_lt hN2'_strict) hnot2' hnotBig'
          refine ⟨Fin.cons z xs', fun x hx d h1 h2 hd1 hd2 => ?_⟩
          rw [hPeq] at hx
          simp only [List.mem_append, List.mem_cons] at hx
          rcases hx with hx1 | rfl | hx2
          · obtain ⟨j, hj⟩ := hxs' x (List.mem_append_left _ hx1) d h1 h2 hd1 hd2
            exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ, m]; omega⟩
          · refine ⟨0, ?_⟩
            have hdist := hz d h1 h2 hd1 hd2 (by dsimp [C] at *; omega)
            simp only [Fin.cons_zero, Fin.val_zero, add_zero, m]
            omega
          · obtain ⟨j, hj⟩ := hxs' x (List.mem_append_right _ hx2) d h1 h2 hd1 hd2
            exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ, m]; omega⟩
      · -- Case 2 & 3: no element of P has length C = 2*m - 1
        push Not at hexC
        obtain ⟨l₁, l₂, s, hPeq, hmax⟩ := list_exists_max_len hP_empty
        have hs_mem : s ∈ P := by rw [hPeq]; simp
        obtain ⟨z, hz⟩ := seg_ball_cover S (hval s hs_mem) m'
        by_cases hs_big : C < s.len
        · -- Case 2: max element s has s.len > C = 2*m - 1; peel C from s
          let s' : Seg A := ⟨s.arm, s.lo + C, s.len - C⟩
          let P' := l₁ ++ s' :: l₂
          have hs'_val : s'.Valid S := by
            rcases hval s hs_mem with ⟨hv1, hv2, hv3⟩
            exact ⟨by dsimp [s']; omega, by dsimp [s']; omega, by dsimp [s', C] at hs_big ⊢; omega⟩
          have hval' : ∀ x ∈ P', x.Valid S := by
            intro x hx
            simp only [P', List.mem_append, List.mem_cons] at hx
            rcases hx with hx1 | rfl | hx2
            · exact hval x (by rw [hPeq]; simp [hx1])
            · exact hs'_val
            · exact hval x (by rw [hPeq]; simp [hx2])
          have hlen' : P'.length = P.length := by rw [hPeq]; simp [P']
          have hsum' : (P'.map Seg.len).sum + C = (P.map Seg.len).sum := by
            rw [hPeq]; simp [P', s']; omega
          have hN1' : (P'.map Seg.len).sum ≤ m' ^ 2 := by
            dsimp [C, m] at hsum' hN1 ⊢; nlinarith only [hsum', hN1]
          have hN2' : (P'.map Seg.len).sum + m' * P'.length ≤ m' * (m' + 2) := by
            by_cases ht1 : P.length = 1
            · rw [hlen', ht1]; nlinarith only [hN1', hm'_pos]
            · have ht2 : 2 ≤ P.length := by
                have : 1 ≤ P.length := List.length_pos_iff.mpr hP_empty
                omega
              rw [hlen']
              dsimp [C, m] at hsum' hN2 ⊢
              nlinarith only [hsum', hN2, ht2]
          have hnot2' : ¬ (P'.length = m' ∧ ∀ x ∈ P', x.len = 2) := by
            rintro ⟨h1, h2⟩
            have hsum2 := list_sum_eq_two_mul_of_all_two P' h2
            have ht_eq : P.length = m' := hlen' ▸ h1
            have hm'_le2 : m' ≤ 2 := by
              dsimp [C, m] at hsum' hN2
              rw [h1] at hsum2
              rw [ht_eq] at hN2
              nlinarith only [hsum', hsum2, hN2]
            have hm'_eq2 : m' = 2 := by
              by_contra hne2
              have hm'_eq1 : m' = 1 := by omega
              rw [h1, hm'_eq1] at hsum2
              rw [hm'_eq1] at hN1'
              omega
            -- m' = 2, so m = 3, P.length = 2, sum(P) = 9, and l₁ ++ l₂ has a segment of length 2
            apply hnotBig
            refine ⟨by dsimp [m]; omega, by omega, ?_, ?_⟩
            · dsimp [C, m] at hsum' ⊢
              rw [h1, hm'_eq2] at hsum2
              rw [hm'_eq2] at hsum' ⊢
              omega
            · -- Since P'.length = 2, one of l₁ or l₂ is nonempty, giving an element of P of length 2
              have hrest_len : (l₁ ++ l₂).length = 1 := by
                simp only [P', List.length_append, List.length_cons] at h1
                simp only [List.length_append]
                omega
              have hrest_ne : l₁ ++ l₂ ≠ [] := by
                intro he; rw [he] at hrest_len; simp at hrest_len
              obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil (l₁ ++ l₂) hrest_ne
              have hyP : y ∈ P := by
                rw [hPeq]
                simp only [List.mem_append, List.mem_cons] at hy ⊢
                tauto
              have hyP' : y ∈ P' := by
                simp only [P', List.mem_append, List.mem_cons] at hy ⊢
                tauto
              exact ⟨y, hyP, h2 y hyP'⟩
          have hnotBig' : ¬ (2 ≤ m' ∧ P'.length = 2 ∧ (P'.map Seg.len).sum = m' ^ 2 ∧
              ∃ x ∈ P', x.len = 2) := by
            rintro ⟨hm'2, hlen2, hsum_m'2, x, hxP', hx2⟩
            have hP_len2 : P.length = 2 := hlen' ▸ hlen2
            have hP_sum : (P.map Seg.len).sum = m ^ 2 := by
              dsimp [C, m] at hsum' ⊢; nlinarith only [hsum', hsum_m'2]
            -- Identify the other element b ∈ l₁ ++ l₂
            have hrest_len : (l₁ ++ l₂).length = 1 := by
              simp only [P', List.length_append, List.length_cons] at hlen2
              simp only [List.length_append]
              omega
            have hrest_ne : l₁ ++ l₂ ≠ [] := by
              intro he; rw [he] at hrest_len; simp at hrest_len
            obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil (l₁ ++ l₂) hrest_ne
            have hbP : b ∈ P := by
              rw [hPeq]; simp only [List.mem_append, List.mem_cons] at hb ⊢; tauto
            have hb_sum : b.len + s'.len = m' ^ 2 := by
              have hl : l₁ ++ l₂ = [b] := by
                cases h : l₁ ++ l₂ with
                | nil => exact (hrest_ne h).elim
                | cons u v =>
                  rw [h] at hrest_len hb
                  have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hrest_len; omega)
                  subst hv0
                  simp at hb; subst hb; rfl
              have hs_eq : (P'.map Seg.len).sum = s'.len + ((l₁ ++ l₂).map Seg.len).sum := by
                simp [P']; omega
              rw [hl] at hs_eq
              simp at hs_eq
              omega
            -- Either b.len = 2 or s'.len = 2
            have hcases : b.len = 2 ∨ s'.len = 2 := by
              simp only [P', List.mem_append, List.mem_cons] at hxP'
              rcases hxP' with hx1 | rfl | hx2'
              · left
                have hxb : x = b := by
                  have hl : l₁ ++ l₂ = [b] := by
                    cases h : l₁ ++ l₂ with
                    | nil => exact (hrest_ne h).elim
                    | cons u v =>
                      rw [h] at hrest_len hb
                      have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hrest_len; omega)
                      subst hv0
                      simp at hb; subst hb; rfl
                  have hx_in : x ∈ l₁ ++ l₂ := List.mem_append_left _ hx1
                  rw [hl] at hx_in; simpa using hx_in
                exact hxb ▸ hx2
              · exact Or.inr hx2
              · left
                have hxb : x = b := by
                  have hl : l₁ ++ l₂ = [b] := by
                    cases h : l₁ ++ l₂ with
                    | nil => exact (hrest_ne h).elim
                    | cons u v =>
                      rw [h] at hrest_len hb
                      have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hrest_len; omega)
                      subst hv0
                      simp at hb; subst hb; rfl
                  have hx_in : x ∈ l₁ ++ l₂ := List.mem_append_right _ hx2'
                  rw [hl] at hx_in; simpa using hx_in
                exact hxb ▸ hx2
            rcases hcases with hb2 | hs'2
            · exact hnotBig ⟨by dsimp [m]; omega, hP_len2, hP_sum, b, hbP, hb2⟩
            · -- s'.len = 2 so s.len = C + 2 = 2*m + 1, and b.len = m'^2 - 2 ≤ s.len
              have hs_eq : s.len = C + 2 := by dsimp [s'] at hs'2; omega
              have hb_le_s : b.len ≤ s.len := hmax b hbP
              have hm'_le3 : m' ≤ 3 := by
                dsimp [C, m] at hs_eq
                nlinarith only [hs_eq, hb_le_s, hb_sum, hs'2]
              rcases (show m' = 2 ∨ m' = 3 by omega) with hm'2' | hm'3'
              · -- m' = 2 => b.len = 2
                have hb2 : b.len = 2 := by rw [hm'2', hs'2] at hb_sum; omega
                exact hnotBig ⟨by dsimp [m]; omega, hP_len2, hP_sum, b, hbP, hb2⟩
              · -- m' = 3 => m = 4, C = 7, b.len = 9 - 2 = 7 = C, contradicting hexC!
                have hbC : b.len = C := by
                  dsimp [C, m]
                  rw [hm'3', hs'2] at hb_sum
                  omega
                exact hexC b hbP hbC
          obtain ⟨xs', hxs'⟩ := ih hm'_pos P' hval' hN1' hN2' hnot2' hnotBig'
          refine ⟨Fin.cons z xs', fun x hx d h1 h2 hd1 hd2 => ?_⟩
          rw [hPeq] at hx
          simp only [List.mem_append, List.mem_cons] at hx
          rcases hx with hx1 | rfl | hx2
          · obtain ⟨j, hj⟩ := hxs' x (by simp [P', hx1]) d h1 h2 hd1 hd2
            exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ, m]; omega⟩
          · by_cases hdC : d < x.lo + C
            · refine ⟨0, ?_⟩
              have hdist := hz d h1 h2 hd1 hd2 (by dsimp [C, m] at hdC; omega)
              simp only [Fin.cons_zero, Fin.val_zero, add_zero, m]
              omega
            · obtain ⟨j, hj⟩ := hxs' s' (by simp [P']) d h1 h2
                (by dsimp [s']; omega) (by dsimp [s']; omega)
              dsimp only [s'] at hj
              exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ, m]; omega⟩
          · obtain ⟨j, hj⟩ := hxs' x (by simp [P', hx2]) d h1 h2 hd1 hd2
            exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ, m]; omega⟩
        · -- Case 3: max element s has s.len < C = 2*m - 1; burn s completely!
          have hs_le : s.len ≤ C := by omega
          let P' := l₁ ++ l₂
          have hval' : ∀ x ∈ P', x.Valid S := fun x hx =>
            hval x (by rw [hPeq]; simp only [P', List.mem_append, List.mem_cons] at hx ⊢; tauto)
          by_cases hP'_empty : P' = []
          · refine ⟨Fin.cons z (fun _ => S.c), fun x hx d h1 h2 hd1 hd2 => ?_⟩
            have hx_eq : x = s := by
              rw [hPeq] at hx
              have hl1 : l₁ = [] := (List.append_eq_nil_iff.mp hP'_empty).1
              have hl2 : l₂ = [] := (List.append_eq_nil_iff.mp hP'_empty).2
              rw [hl1, hl2] at hx
              simpa using hx
            subst hx_eq
            refine ⟨0, ?_⟩
            have hdist := hz d h1 h2 hd1 hd2 (by dsimp [C, m] at hs_le; omega)
            simp only [Fin.cons_zero, Fin.val_zero, add_zero, m]
            omega
          · have hN2_c : (P.map Seg.len).sum + (m' + 1) * P.length ≤ (m' + 1) * (m' + 3) := by
              dsimp [m] at hN2; rw [show m' + 1 + 2 = m' + 3 by omega] at hN2; exact hN2
            obtain ⟨hN1', hN2', hnot2', hnotBig'⟩ :=
              burn_path_forest_case3_invariants hm'_pos hPeq hmax hN1 hN2_c ht_le_m hnot2 hP'_empty
            obtain ⟨xs', hxs'⟩ := ih hm'_pos P' hval' hN1' hN2' hnot2' hnotBig'
            refine ⟨Fin.cons z xs', fun x hx d h1 h2 hd1 hd2 => ?_⟩
            rw [hPeq] at hx
            simp only [List.mem_append, List.mem_cons] at hx
            rcases hx with hx1 | rfl | hx2
            · obtain ⟨j, hj⟩ := hxs' x (List.mem_append_left _ hx1) d h1 h2 hd1 hd2
              exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ, m]; omega⟩
            · refine ⟨0, ?_⟩
              have hdist := hz d h1 h2 hd1 hd2 (by dsimp [C, m] at hs_le; omega)
              simp only [Fin.cons_zero, Fin.val_zero, add_zero]
              omega
            · obtain ⟨j, hj⟩ := hxs' x (List.mem_append_right _ hx2) d h1 h2 hd1 hd2
              exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ, m]; omega⟩

/-- Burning `t ≥ 1` valid segments of length `4` with `t + 1` rounds (radii `t, t - 1, ..., 0`). -/
private lemma burn_fours {V A : Type*} {T : SimpleGraph V} (S : SpiderData V A T) :
    ∀ (t : ℕ), 1 ≤ t → ∀ (Q : List (Seg A)),
      Q.length = t → (∀ s ∈ Q, s.Valid S ∧ s.len = 4) →
      ∃ xs : Fin (t + 1) → V, BurnsSegs S Q xs := by
  intro t ht
  induction t with
  | zero => omega
  | succ t' ih =>
    intro Q hlen hQ
    cases Q with
    | nil => simp at hlen
    | cons q rest =>
      have hq := hQ q (List.mem_cons_self ..)
      by_cases ht'0 : t' = 0
      · subst ht'0
        have hrest : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
        subst hrest
        -- Single segment of length 4 with radii 1, 0:
        -- radius 1 at q.lo + 1 covers q.lo, q.lo+1, q.lo+2; radius 0 at q.lo + 3 covers q.lo+3
        have h1 : 1 ≤ q.lo + 1 := by have := hq.1.1; omega
        have h2 : q.lo + 1 ≤ S.armLen q.arm := by have := hq.1.2.2; have := hq.2; omega
        have h3 : 1 ≤ q.lo + 3 := by have := hq.1.1; omega
        have h4 : q.lo + 3 ≤ S.armLen q.arm := by have := hq.1.2.2; have := hq.2; omega
        refine ⟨Fin.cons (S.vert q.arm (q.lo + 1) h1 h2)
          (Fin.cons (S.vert q.arm (q.lo + 3) h3 h4) finZeroElim),
          fun s hs d hd1 hd2 hlo hhi => ?_⟩
        simp only [List.mem_singleton] at hs; subst hs
        have hq4 := hq.2
        by_cases hd3 : d ≤ s.lo + 2
        · refine ⟨0, ?_⟩
          have hd := S.dist_same s.arm (s.lo + 1) d h1 h2 hd1 hd2
          have hnat : Nat.dist (s.lo + 1) d ≤ 1 := by rw [Nat.dist_eq_max_sub_min]; omega
          simp only [Fin.cons_zero, Fin.val_zero, add_zero]
          omega
        · refine ⟨1, ?_⟩
          have hd_eq : d = s.lo + 3 := by omega
          have hd := S.dist_same s.arm (s.lo + 3) d h3 h4 hd1 hd2
          have hnat : Nat.dist (s.lo + 3) d = 0 := by rw [hd_eq, Nat.dist_self]
          simp only [Fin.val_one]
          change T.dist (S.vert s.arm (s.lo + 3) h3 h4) (S.vert s.arm d hd1 hd2) + 1 < 2
          omega
      · have ht'1 : 1 ≤ t' := by omega
        obtain ⟨z, hz⟩ := seg_ball_cover S hq.1 (t' + 1)
        obtain ⟨xs', hxs'⟩ := ih ht'1 rest (by simpa using hlen)
          (fun s hs => hQ s (List.mem_cons_of_mem _ hs))
        refine ⟨Fin.cons z xs', fun s hs d hd1 hd2 hlo hhi => ?_⟩
        rcases List.mem_cons.mp hs with rfl | hmem
        · refine ⟨0, ?_⟩
          have hdist := hz d hd1 hd2 hlo hhi (by have := hq.2; omega)
          simp only [Fin.cons_zero, Fin.val_zero, add_zero]
          omega
        · obtain ⟨j, hj⟩ := hxs' s hmem d hd1 hd2 hlo hhi
          exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ]; omega⟩

/-- Burning an abstract spider (restricted to `cap u ≤ S.armLen u` on each arm) in `k` rounds
whenever `1 + ∑ u, cap u ≤ k^2`. -/
private lemma burn_abstract_spider {V A : Type*} [Fintype A] [DecidableEq A] {T : SimpleGraph V}
    (S : SpiderData V A T) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (cap : A → ℕ),
      (∀ u, cap u ≤ S.armLen u) →
      1 + ∑ u : A, cap u ≤ k ^ 2 →
      ∃ xs : Fin k → V,
        (∃ i : Fin k, T.dist (xs i) S.c + i.val < k) ∧
        ∀ (u : A) (d : ℕ) (h1 : 1 ≤ d) (h2 : d ≤ S.armLen u), d ≤ cap u →
          ∃ i : Fin k, T.dist (xs i) (S.vert u d h1 h2) + i.val < k := by
  intro k hk
  induction k with
  | zero => omega
  | succ k' ih =>
    intro cap hcap_le htot
    set k := k' + 1
    by_cases hk'0 : k' = 0
    · -- Base case k = 1: all cap u = 0, center burns itself
      subst hk'0
      refine ⟨fun _ => S.c, ⟨⟨0, by dsimp [k]; omega⟩, by simp [k]⟩, fun u d h1 _ hd => ?_⟩
      have hcap0 : cap u = 0 := by
        have hle : cap u ≤ ∑ v : A, cap v :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
        dsimp [k] at htot
        omega
      omega
    · have hk'1 : 1 ≤ k' := by omega
      -- Case A: some arm has cap u ≥ 2*k - 1
      by_cases hlong : ∃ u : A, 2 * k - 1 ≤ cap u
      · obtain ⟨u₀, hu₀⟩ := hlong
        -- Peel 2*k - 1 from the tip of arm u₀ using radius k' = k - 1
        let d_ctr := cap u₀ - k'
        have hd1 : 1 ≤ d_ctr := by dsimp [d_ctr, k] at hu₀ ⊢; omega
        have hd2 : d_ctr ≤ S.armLen u₀ := le_trans (by dsimp [d_ctr]; omega) (hcap_le u₀)
        let z := S.vert u₀ d_ctr hd1 hd2
        let cap' : A → ℕ := fun u => if u = u₀ then cap u₀ - (2 * k - 1) else cap u
        have hcap'_le : ∀ u, cap' u ≤ S.armLen u := fun u => by
          dsimp [cap']; split_ifs with h
          · subst h; exact le_trans (Nat.sub_le _ _) (hcap_le u)
          · exact hcap_le u
        have htot' : 1 + ∑ u : A, cap' u ≤ k' ^ 2 := by
          have hsum_eq : ∑ u : A, cap' u + (2 * k - 1) = ∑ u : A, cap u := by
            have h1 := Finset.add_sum_erase Finset.univ cap' (Finset.mem_univ u₀)
            have h2 := Finset.add_sum_erase Finset.univ cap (Finset.mem_univ u₀)
            have herase : ∑ u ∈ Finset.univ.erase u₀, cap' u =
                ∑ u ∈ Finset.univ.erase u₀, cap u :=
              Finset.sum_congr rfl fun u hu => by
                simp [cap', Finset.ne_of_mem_erase hu]
            rw [← h1, ← h2, herase]
            simp only [cap', ite_true]
            omega
          dsimp [k] at hsum_eq htot ⊢
          have h2k : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
          rw [h2k] at hsum_eq
          nlinarith
        obtain ⟨xs', hc', harm'⟩ := ih hk'1 cap' hcap'_le htot'
        refine ⟨Fin.cons z xs', ?_, ?_⟩
        · obtain ⟨j, hj⟩ := hc'
          exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ]; omega⟩
        · intro u d h1 h2 hd
          by_cases hu : u = u₀
          · subst hu
            by_cases hd_low : d ≤ cap' u
            · obtain ⟨j, hj⟩ := harm' u d h1 h2 hd_low
              exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ]; omega⟩
            · refine ⟨0, ?_⟩
              have hdist := S.dist_same u d_ctr d hd1 hd2 h1 h2
              have hnat : Nat.dist d_ctr d ≤ k' := by
                rw [Nat.dist_eq_max_sub_min]
                simp only [cap', ite_true, d_ctr, k] at hd_low hu₀ ⊢
                omega
              simp only [Fin.cons_zero, Fin.val_zero, add_zero, z, k]
              omega
          · have hd' : d ≤ cap' u := by simp [cap', hu, hd]
            obtain ⟨j, hj⟩ := harm' u d h1 h2 hd'
            exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ]; omega⟩
      · -- Case B: all arms have cap u ≤ 2*k - 2 = 2*k'
        push Not at hlong
        have hcap_bound : ∀ u, cap u ≤ 2 * k' := fun u => by
          have := hlong u; dsimp [k] at this; omega
        -- Build list of leftover segments after placing radius k' at S.c
        let longArms : Finset A := Finset.univ.filter (fun u => k' < cap u)
        let P : List (Seg A) := longArms.toList.map fun u => ⟨u, k' + 1, cap u - k'⟩
        have hP_val : ∀ s ∈ P, s.Valid S := by
          intro s hs
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
          have hgt : k' < cap u := (Finset.mem_filter.mp (Finset.mem_toList.mp hu)).2
          have hle := hcap_le u
          exact ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩
        have hP_len_le : ∀ s ∈ P, s.len ≤ k' := by
          intro s hs
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
          have := hcap_bound u
          dsimp
          omega
        have hP_card : P.length = longArms.card := by simp [P]
        have hP_sum : (P.map Seg.len).sum = ∑ u ∈ longArms, (cap u - k') := by
          have haux : ∀ (l : List A), l.Nodup →
              (l.map fun u => cap u - k').sum = ∑ u ∈ l.toFinset, (cap u - k') := by
            intro l
            induction l with
            | nil => simp
            | cons a t ih =>
              intro hnd
              rw [List.nodup_cons] at hnd
              simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
              rw [Finset.sum_insert (by simpa using hnd.1), ih hnd.2]
          have h1 := haux longArms.toList (Finset.nodup_toList longArms)
          rw [Finset.toList_toFinset] at h1
          simpa [P, List.map_map, Function.comp_def] using h1
        -- Key sum bound: N + k' * t ≤ k' * (k' + 2)
        have hN2 : (P.map Seg.len).sum + k' * P.length ≤ k' * (k' + 2) := by
          rw [hP_sum, hP_card]
          have hsub : ∑ u ∈ longArms, cap u ≤ ∑ u : A, cap u :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
          have hsplit : ∑ u ∈ longArms, (cap u - k') + k' * longArms.card =
              ∑ u ∈ longArms, cap u := by
            have h1 : k' * longArms.card = ∑ _u ∈ longArms, k' := by
              rw [Finset.sum_const, smul_eq_mul, mul_comm]
            rw [h1, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun u hu => ?_
            have hgt : k' < cap u := (Finset.mem_filter.mp hu).2
            omega
          dsimp [k] at htot
          nlinarith
        -- Bound N ≤ k'^2
        have hN1 : (P.map Seg.len).sum ≤ k' ^ 2 := by
          by_cases ht2 : 2 ≤ P.length
          · nlinarith
          · have hmax_sum := list_sum_le_length_mul_max P k' hP_len_le
            nlinarith
        -- Exclusion of {k'^2 - 2, 2} for k' ≥ 2 (actually k' ≥ 3 since all s.len ≤ k' < k'^2 - 2!)
        by_cases hbad2 : P.length = k' ∧ ∀ s ∈ P, s.len = 2
        · -- Subcase B2: P consists of k' segments of length 2!
          -- So k' ≥ 2, and longArms has k' arms of cap = k' + 2, and all other arms have cap = 0!
          have hk'2 : 2 ≤ k' := by
            have hP_ne : P ≠ [] := by
              intro h; rw [h] at hbad2; simp at hbad2; omega
            obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil P hP_ne
            have h1 := hbad2.2 s hs
            have h2 := hP_len_le s hs
            omega
          have hcap_long : ∀ u ∈ longArms, cap u = k' + 2 := by
            intro u hu
            have hmem : (⟨u, k' + 1, cap u - k'⟩ : Seg A) ∈ P :=
              List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu, rfl⟩
            have h2 := hbad2.2 _ hmem
            have hgt : k' < cap u := (Finset.mem_filter.mp hu).2
            dsimp at h2
            omega
          have hcap_other : ∀ u : A, u ∉ longArms → cap u = 0 := by
            intro u hu
            have hlong_sum : ∑ v ∈ longArms, cap v = k' * (k' + 2) := by
              rw [Finset.sum_congr rfl hcap_long, Finset.sum_const, smul_eq_mul,
                ← hP_card, hbad2.1]
            have hsum_all : ∑ v : A, cap v = ∑ v ∈ longArms, cap v +
                ∑ v ∈ Finset.univ \ longArms, cap v := by
              rw [← Finset.sum_union disjoint_sdiff_self_right,
                Finset.union_sdiff_of_subset (Finset.subset_univ _)]
            have hu_mem : u ∈ Finset.univ \ longArms := by simp [hu]
            have hle : cap u ≤ ∑ v ∈ Finset.univ \ longArms, cap v :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) hu_mem
            dsimp [k] at htot
            nlinarith
          -- Pick the first arm u₀ in longArms.toList
          have htoList_ne : longArms.toList ≠ [] := by
            intro h; have : P.length = 0 := by simp [P, h]
            omega
          cases hlist : longArms.toList with
          | nil => exact (htoList_ne hlist).elim
          | cons u₀ rest =>
            have hnd : (u₀ :: rest).Nodup := hlist ▸ Finset.nodup_toList longArms
            have hu₀_mem : u₀ ∈ longArms := Finset.mem_toList.mp (by rw [hlist]; simp)
            have hu₀_cap : cap u₀ = k' + 2 := hcap_long u₀ hu₀_mem
            -- Place radius k' at depth 2 on arm u₀
            have h2_le : 2 ≤ S.armLen u₀ := le_trans (by omega : 2 ≤ cap u₀) (hcap_le u₀)
            let z := S.vert u₀ 2 (by omega) h2_le
            -- Remaining k' - 1 arms each have leftover segment [k' - 1, k' + 2] of length 4
            let Q : List (Seg A) := rest.map fun u => ⟨u, k' - 1, 4⟩
            have hQ_len : Q.length = k' - 1 := by
              have hlen_list : (u₀ :: rest).length = k' := by
                rw [← hlist, Finset.length_toList, ← hP_card, hbad2.1]
              simp only [Q, List.length_map]
              simp only [List.length_cons] at hlen_list
              omega
            have hQ_val : ∀ s ∈ Q, s.Valid S ∧ s.len = 4 := by
              intro s hs
              obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
              have hu_mem : u ∈ longArms := Finset.mem_toList.mp (by rw [hlist]; simp [hu])
              have hucap : cap u = k' + 2 := hcap_long u hu_mem
              have hule := hcap_le u
              exact ⟨⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩, rfl⟩
            obtain ⟨xs', hxs'⟩ := burn_fours S (k' - 1) (by omega) Q hQ_len hQ_val
            have hk'_eq : (k' - 1) + 1 = k' := by omega
            let xs'' : Fin k' → V := fun j => xs' ⟨j.val, by omega⟩
            refine ⟨Fin.cons z xs'', ?_, ?_⟩
            · -- Center S.c is at distance ≤ 2 ≤ k' from z
              refine ⟨0, ?_⟩
              have hd := S.dist_c u₀ 2 (by omega) h2_le
              rw [SimpleGraph.dist_comm] at hd
              simp only [Fin.cons_zero, Fin.val_zero, add_zero, z, k]
              omega
            · intro u d h1 h2 hd
              by_cases hu_long : u ∈ longArms
              · have hu_in : u ∈ u₀ :: rest := hlist ▸ Finset.mem_toList.mpr hu_long
                rcases List.mem_cons.mp hu_in with rfl | hu_rest
                · -- On arm u: 1 ≤ d ≤ k' + 2, so |d - 2| ≤ k'
                  refine ⟨0, ?_⟩
                  have hdist := S.dist_same u 2 d (by omega) h2_le h1 h2
                  have hnat : Nat.dist 2 d ≤ k' := by rw [Nat.dist_eq_max_sub_min]; omega
                  simp only [Fin.cons_zero, Fin.val_zero, add_zero, z, k]
                  omega
                · -- On arm u ∈ rest: if d ≤ k' - 2, z reaches it via c (dist ≤ 2 + d ≤ k')
                  by_cases hd_low : d ≤ k' - 2
                  · refine ⟨0, ?_⟩
                    have hdist := S.dist_diff u₀ u 2 d (by omega) h2_le h1 h2
                    simp only [Fin.cons_zero, Fin.val_zero, add_zero, z, k]
                    omega
                  · -- Otherwise k' - 1 ≤ d ≤ k' + 2, covered by xs' on Q!
                    have hucap := hcap_long u hu_long
                    have hq_mem : (⟨u, k' - 1, 4⟩ : Seg A) ∈ Q := List.mem_map.mpr ⟨u, hu_rest, rfl⟩
                    obtain ⟨j, hj⟩ := hxs' ⟨u, k' - 1, 4⟩ hq_mem d h1 h2 (by dsimp; omega) (by dsimp; omega)
                    dsimp only at hj
                    refine ⟨(⟨j.val, by omega⟩ : Fin k').succ, ?_⟩
                    have hj_eq : (⟨j.val, by omega⟩ : Fin (k' - 1 + 1)) = j := Fin.ext rfl
                    simp only [Fin.cons_succ, Fin.val_succ, xs'', hj_eq, k]
                    omega
              · have h0 := hcap_other u hu_long
                omega
        · -- Subcase B1: P satisfies ALL 4 conditions of burn_path_forest!
          have hnotBig : ¬ (2 ≤ k' ∧ P.length = 2 ∧ (P.map Seg.len).sum = k' ^ 2 ∧
              ∃ s ∈ P, s.len = 2) := by
            rintro ⟨hk'2, hlen2, hsum2, s, hsP, hs2⟩
            -- If k' = 2, then P = [2, 2], contradicting hbad2!
            by_cases hk'eq2 : k' = 2
            · subst hk'eq2
              obtain ⟨l₁, l₂, hPeq⟩ := list_exists_mem_split hsP
              have hrest_len : (l₁ ++ l₂).length = 1 := by
                rw [hPeq] at hlen2; simp at hlen2 ⊢; omega
              have hrest_ne : l₁ ++ l₂ ≠ [] := by
                intro he; rw [he] at hrest_len; simp at hrest_len
              obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil (l₁ ++ l₂) hrest_ne
              have hl : l₁ ++ l₂ = [b] := by
                cases h : l₁ ++ l₂ with
                | nil => exact (hrest_ne h).elim
                | cons u v =>
                  rw [h] at hrest_len hb
                  have hv : v = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hrest_len; omega)
                  subst hv; simp at hb; subst hb; rfl
              have hb2 : b.len = 2 := by
                have hsum_eq : (P.map Seg.len).sum = s.len + ((l₁ ++ l₂).map Seg.len).sum := by
                  rw [hPeq]; simp; omega
                rw [hl, hs2] at hsum_eq; simp at hsum_eq; omega
              apply hbad2
              refine ⟨hlen2, fun x hx => ?_⟩
              rw [hPeq] at hx
              simp only [List.mem_append, List.mem_cons] at hx
              rcases hx with hx1 | rfl | hx2
              · have : x ∈ l₁ ++ l₂ := List.mem_append_left _ hx1
                rw [hl] at this; simp at this; rw [this, hb2]
              · exact hs2
              · have : x ∈ l₁ ++ l₂ := List.mem_append_right _ hx2
                rw [hl] at this; simp at this; rw [this, hb2]
            · -- k' ≥ 3: every segment in P has len ≤ k', so sum ≤ 2 * k' < k'^2!
              have hmax_sum := list_sum_le_length_mul_max P k' hP_len_le
              rw [hlen2] at hmax_sum
              have hk'3 : 3 ≤ k' := by omega
              nlinarith
          obtain ⟨xs', hxs'⟩ := burn_path_forest S k' hk'1 P hP_val hN1 hN2 hbad2 hnotBig
          refine ⟨Fin.cons S.c xs', ⟨0, by simp [k]⟩, fun u d h1 h2 hd => ?_⟩
          by_cases hd_low : d ≤ k'
          · refine ⟨0, ?_⟩
            have hdist := S.dist_c u d h1 h2
            simp only [Fin.cons_zero, Fin.val_zero, add_zero]
            omega
          · have hu_long : u ∈ longArms := Finset.mem_filter.mpr ⟨Finset.mem_univ u, by omega⟩
            have hs_mem : (⟨u, k' + 1, cap u - k'⟩ : Seg A) ∈ P :=
              List.mem_map.mpr ⟨u, Finset.mem_toList.mpr hu_long, rfl⟩
            obtain ⟨j, hj⟩ := hxs' ⟨u, k' + 1, cap u - k'⟩ hs_mem d h1 h2
              (by dsimp; omega) (by dsimp; omega)
            dsimp only at hj
            exact ⟨j.succ, by simp only [Fin.cons_succ, Fin.val_succ, k]; omega⟩

end AbstractSpider

section TreeToSpider

variable {V : Type} [Fintype V]

/-- For a path `p : T.Walk c v`, its vertices `p.getVert i` for `i ≤ p.length` are pairwise distinct. -/
private lemma path_getVert_inj {T : SimpleGraph V} {c v : V} {p : T.Walk c v} (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) (heq : p.getVert i = p.getVert j) :
    i = j := by
  have hi' : i < p.support.length := by rw [Walk.length_support]; omega
  have hj' : j < p.support.length := by rw [Walk.length_support]; omega
  rw [Walk.getVert_eq_support_getElem p hi, Walk.getVert_eq_support_getElem p hj] at heq
  exact (List.Nodup.getElem_inj_iff hp.support_nodup).mp heq

/-- In a spider tree `T` with center `c`, two paths from `c` with the same first step `snd`
agree on every index up to the minimum of their lengths. -/
private lemma spider_paths_prefix {T : SimpleGraph V} (c : V)
    (hdeg : ∀ v, v ≠ c → (T.neighborSet v).ncard ≤ 2)
    {v w : V} {pv : T.Walk c v} {pw : T.Walk c w}
    (hpv : pv.IsPath) (hpw : pw.IsPath)
    (hsnd : pv.snd = pw.snd) :
    ∀ i : ℕ, i ≤ pv.length → i ≤ pw.length → pv.getVert i = pw.getVert i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hiv hiw
    rcases i with _ | _ | j
    · simp
    · exact hsnd
    · have hprev : pv.getVert j = pw.getVert j := ih j (by omega) (by omega) (by omega)
      have hcurr : pv.getVert (j + 1) = pw.getVert (j + 1) :=
        ih (j + 1) (by omega) (by omega) (by omega)
      set x := pv.getVert (j + 1)
      have hx_ne_c : x ≠ c := by
        intro hxc
        have h0 : pv.getVert (j + 1) = pv.getVert 0 := by simp [x, hxc]
        have := path_getVert_inj hpv (by omega) (by omega) h0
        omega
      have hadj_prev : T.Adj x (pv.getVert j) := (pv.adj_getVert_succ (by omega)).symm
      have hadj_v : T.Adj x (pv.getVert (j + 2)) := pv.adj_getVert_succ (by omega)
      have hadj_w : T.Adj x (pw.getVert (j + 2)) := by
        rw [hcurr]
        exact pw.adj_getVert_succ (by omega)
      have hne_v : pv.getVert (j + 2) ≠ pv.getVert j := fun h => by
        have := path_getVert_inj hpv (by omega) (by omega) h; omega
      have hne_w : pw.getVert (j + 2) ≠ pv.getVert j := fun h => by
        rw [hprev] at h
        have := path_getVert_inj hpw (by omega) (by omega) h; omega
      by_contra hvw
      let S3 : Finset V := {pv.getVert j, pv.getVert (j + 2), pw.getVert (j + 2)}
      have hS3_card : S3.card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair hvw]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne_v.symm, hne_w.symm⟩
      have hsub : (S3 : Set V) ⊆ T.neighborSet x := by
        intro y hy
        simp only [S3, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hadj_prev
        · exact hadj_v
        · exact hadj_w
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_coe_finset, hS3_card] at hle
      have h2 := hdeg x hx_ne_c
      omega

/-- Build `SpiderData` from any finite spider tree `T` with center `c`, together with the
vertex count identity `Fintype.card V = 1 + ∑ u, armLen u`. -/
private lemma build_spider_data (T : SimpleGraph V) (hT : T.IsTree) (c : V)
    (hdeg : ∀ v, v ≠ c → (T.neighborSet v).ncard ≤ 2) :
    ∃ (A : Type) (_ : Fintype A) (_ : DecidableEq A) (S : SpiderData V A T),
      S.c = c ∧ Fintype.card V = 1 + ∑ u : A, S.armLen u := by
  let A := {u : V // T.Adj c u}
  -- Choose the unique path from c to each vertex v
  have hex : ∀ v : V, ∃ p : T.Walk c v, p.IsPath := fun v => (hT.existsUnique_path c v).exists
  let p : (v : V) → T.Walk c v := fun v => Classical.choose (hex v)
  have hp : ∀ v : V, (p v).IsPath := fun v => Classical.choose_spec (hex v)
  have hp_uniq : ∀ {v : V} (q : T.Walk c v), q.IsPath → q = p v := fun q hq =>
    (hT.existsUnique_path c _).unique hq (hp _)
  have hp_nil : p c = Walk.nil := (hp_uniq Walk.nil Walk.IsPath.nil).symm
  have hlen_pos : ∀ {v : V}, v ≠ c → 1 ≤ (p v).length := by
    intro v hv
    by_contra h0
    have hlen0 : (p v).length = 0 := by omega
    have hnil := Walk.eq_of_length_eq_zero hlen0
    exact hv hnil.symm
  have hadj_snd : ∀ {v : V} (hv : v ≠ c), T.Adj c (p v).snd := fun {v} hv =>
    (p v).adj_snd (Walk.not_nil_of_ne hv.symm)
  let arm : (v : V) → v ≠ c → A := fun v hv => ⟨(p v).snd, hadj_snd hv⟩
  -- For any v ≠ c and 1 ≤ d ≤ (p v).length, the d-th vertex w = (p v).getVert d has
  -- length d and the same arm as v.
  have htake : ∀ (v : V) (hv : v ≠ c) (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ (p v).length),
      let w := (p v).getVert d
      ∃ hw : w ≠ c, (p w).length = d ∧ arm w hw = arm v hv := by
    intro v hv d hd1 hd2
    set w := (p v).getVert d
    have hw_mem : w ∈ (p v).support := Walk.getVert_mem_support (p v) d
    have hw_ne_c : w ≠ c := by
      intro hwc
      have h0 : (p v).getVert d = (p v).getVert 0 := by simp [w, hwc]
      have := path_getVert_inj (hp v) hd2 (by omega) h0
      omega
    let q : T.Walk c w := (p v).takeUntil w hw_mem
    have hq_path : q.IsPath := (hp v).takeUntil hw_mem
    have hq_eq : q = p w := hp_uniq q hq_path
    have hq_len : q.length = d := by
      have h1 : (p v).getVert q.length = w := (p v).getVert_length_takeUntil hw_mem
      have h2 : q.length ≤ (p v).length := Walk.length_takeUntil_le_length (p v) hw_mem
      exact path_getVert_inj (hp v) h2 hd2 h1
    have hq_snd : q.snd = (p v).snd := by
      have h1 : 1 ≤ q.length := by omega
      have := (p v).getVert_takeUntil hw_mem h1
      simpa [q] using this
    refine ⟨hw_ne_c, hq_eq ▸ hq_len, Subtype.ext ?_⟩
    simpa [arm, hq_eq] using hq_snd
  -- Arm sets and lengths
  let armSet : A → Finset V := fun u => Finset.univ.filter fun v => ∃ hv : v ≠ c, arm v hv = u
  let armLen : A → ℕ := fun u => (armSet u).card
  -- Injectivity of length on each armSet u
  have hlen_inj : ∀ (u : A) {v w : V}, v ∈ armSet u → w ∈ armSet u →
      (p v).length = (p w).length → v = w := by
    intro u v w hv hw hlen
    obtain ⟨hv_ne, hv_arm⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨hw_ne, hw_arm⟩ := (Finset.mem_filter.mp hw).2
    have hsnd : (p v).snd = (p w).snd := congrArg Subtype.val (hv_arm.trans hw_arm.symm)
    have hpre := spider_paths_prefix c hdeg (hp v) (hp w) hsnd (p v).length le_rfl (by omega)
    have hv_end : (p v).getVert (p v).length = v := Walk.getVert_length (p v)
    have hw_end : (p w).getVert (p v).length = w := by rw [hlen]; exact Walk.getVert_length (p w)
    exact hv_end.symm.trans (hpre.trans hw_end)
  -- For every v ∈ armSet u, 1 ≤ (p v).length ≤ armLen u
  have hlen_le_armLen : ∀ (u : A) {v : V}, v ∈ armSet u → (p v).length ≤ armLen u := by
    intro u v hv
    obtain ⟨hv_ne, hv_arm⟩ := (Finset.mem_filter.mp hv).2
    have hsub : (Finset.Icc 1 (p v).length).image (fun d => (p v).getVert d) ⊆ armSet u := by
      intro w hw
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hw
      rw [Finset.mem_Icc] at hd
      obtain ⟨hw_ne, _, hw_arm⟩ := htake v hv_ne d hd.1 hd.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_ne, hw_arm.trans hv_arm⟩
    have hinj : Set.InjOn (fun d => (p v).getVert d) (Finset.Icc 1 (p v).length : Set ℕ) := by
      intro i hi j hj heq
      simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
      exact path_getVert_inj (hp v) hi.2 hj.2 heq
    calc (p v).length
        = (Finset.Icc 1 (p v).length).card := by simp
      _ = ((Finset.Icc 1 (p v).length).image (fun d => (p v).getVert d)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (armSet u).card := Finset.card_le_card hsub
  -- Conversely, for every u and 1 ≤ d ≤ armLen u, there exists v ∈ armSet u with (p v).length = d
  have hex_vert : ∀ (u : A) (d : ℕ), 1 ≤ d → d ≤ armLen u →
      ∃ v ∈ armSet u, (p v).length = d := by
    intro u d hd1 hd2
    have hne : (armSet u).Nonempty := Finset.card_pos.mp (by dsimp [armLen] at hd2; omega)
    obtain ⟨vmax, hvmax_mem, hvmax_max⟩ :=
      Finset.exists_max_image (armSet u) (fun v => (p v).length) hne
    have hmax_ge : armLen u ≤ (p vmax).length := by
      have hsub : (armSet u).image (fun v => (p v).length) ⊆ Finset.Icc 1 (p vmax).length := by
        intro k hk
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
        obtain ⟨hw_ne, _⟩ := (Finset.mem_filter.mp hw).2
        exact Finset.mem_Icc.mpr ⟨hlen_pos hw_ne, hvmax_max w hw⟩
      have hinj : Set.InjOn (fun v => (p v).length) (armSet u : Set V) :=
        fun x hx y hy h => hlen_inj u hx hy h
      calc armLen u
          = ((armSet u).image (fun v => (p v).length)).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.Icc 1 (p vmax).length).card := Finset.card_le_card hsub
        _ = (p vmax).length := by simp
    obtain ⟨hvmax_ne, hvmax_arm⟩ := (Finset.mem_filter.mp hvmax_mem).2
    obtain ⟨hw_ne, hw_len, hw_arm⟩ := htake vmax hvmax_ne d hd1 (le_trans hd2 hmax_ge)
    exact ⟨(p vmax).getVert d,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_ne, hw_arm.trans hvmax_arm⟩, hw_len⟩
  -- Define vert u d h1 h2
  let vert : (u : A) → (d : ℕ) → 1 ≤ d → d ≤ armLen u → V :=
    fun u d h1 h2 => Classical.choose (hex_vert u d h1 h2)
  have hvert_mem : ∀ u d h1 h2, vert u d h1 h2 ∈ armSet u :=
    fun u d h1 h2 => (Classical.choose_spec (hex_vert u d h1 h2)).1
  have hvert_len : ∀ u d h1 h2, (p (vert u d h1 h2)).length = d :=
    fun u d h1 h2 => (Classical.choose_spec (hex_vert u d h1 h2)).2
  -- Distance on the same arm
  have hdist_same : ∀ (u : A) (d₁ d₂ : ℕ) (h1 : 1 ≤ d₁) (h2 : d₁ ≤ armLen u)
      (h3 : 1 ≤ d₂) (h4 : d₂ ≤ armLen u),
      T.dist (vert u d₁ h1 h2) (vert u d₂ h3 h4) ≤ Nat.dist d₁ d₂ := by
    intro u d₁ d₂ h1 h2 h3 h4
    set v₁ := vert u d₁ h1 h2
    set v₂ := vert u d₂ h3 h4
    have hv₁_len : (p v₁).length = d₁ := hvert_len u d₁ h1 h2
    have hv₂_len : (p v₂).length = d₂ := hvert_len u d₂ h3 h4
    obtain ⟨_, hv₁_arm⟩ := (Finset.mem_filter.mp (hvert_mem u d₁ h1 h2)).2
    obtain ⟨_, hv₂_arm⟩ := (Finset.mem_filter.mp (hvert_mem u d₂ h3 h4)).2
    have hsnd : (p v₁).snd = (p v₂).snd := congrArg Subtype.val (hv₁_arm.trans hv₂_arm.symm)
    by_cases hle : d₁ ≤ d₂
    · have hpre : (p v₂).getVert d₁ = v₁ := by
        have := spider_paths_prefix c hdeg (hp v₁) (hp v₂) hsnd d₁ (by omega) (by omega)
        rw [← this, ← hv₁_len, Walk.getVert_length]
      let q : T.Walk v₁ v₂ := ((p v₂).drop d₁).copy hpre rfl
      have hq_len : q.length = d₂ - d₁ := by
        simp [q, hv₂_len]
      have hle_dist := SimpleGraph.dist_le q
      rw [hq_len] at hle_dist
      have : Nat.dist d₁ d₂ = d₂ - d₁ := by rw [Nat.dist_eq_max_sub_min]; omega
      omega
    · have hpre : (p v₁).getVert d₂ = v₂ := by
        have := spider_paths_prefix c hdeg (hp v₁) (hp v₂) hsnd d₂ (by omega) (by omega)
        rw [this, ← hv₂_len, Walk.getVert_length]
      let q : T.Walk v₂ v₁ := ((p v₁).drop d₂).copy hpre rfl
      have hq_len : q.length = d₁ - d₂ := by
        simp [q, hv₁_len]
      have hle_dist := SimpleGraph.dist_le q
      rw [SimpleGraph.dist_comm, hq_len] at hle_dist
      have : Nat.dist d₁ d₂ = d₁ - d₂ := by rw [Nat.dist_eq_max_sub_min]; omega
      omega
  -- Partition of Finset.univ into {c} and biUnion armSet
  have hcard_V : Fintype.card V = 1 + ∑ u : A, armLen u := by
    have hdisj_arms : Set.PairwiseDisjoint (Finset.univ : Finset A) armSet := by
      intro u₁ _ u₂ _ hne
      change Disjoint (armSet u₁) (armSet u₂)
      rw [Finset.disjoint_left]
      intro v hv₁ hv₂
      obtain ⟨h1, ha1⟩ := (Finset.mem_filter.mp hv₁).2
      obtain ⟨h2, ha2⟩ := (Finset.mem_filter.mp hv₂).2
      exact hne (ha1.symm.trans ha2)
    have hdisj_c : Disjoint ({c} : Finset V) (Finset.univ.biUnion armSet) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [Finset.mem_singleton] at hv1
      subst hv1
      obtain ⟨u, _, hu⟩ := Finset.mem_biUnion.mp hv2
      obtain ⟨hne, _⟩ := (Finset.mem_filter.mp hu).2
      exact hne rfl
    have hunion : ({c} : Finset V) ∪ Finset.univ.biUnion armSet = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_biUnion, Finset.mem_univ,
        true_and, iff_true]
      by_cases hvc : v = c
      · exact Or.inl hvc
      · exact Or.inr ⟨arm v hvc, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvc, rfl⟩⟩
    calc Fintype.card V
        = (Finset.univ : Finset V).card := rfl
      _ = (({c} : Finset V) ∪ Finset.univ.biUnion armSet).card := by rw [hunion]
      _ = 1 + (Finset.univ.biUnion armSet).card := by
          rw [Finset.card_union_of_disjoint hdisj_c, Finset.card_singleton]
      _ = 1 + ∑ u : A, armLen u := by
          rw [Finset.card_biUnion hdisj_arms]
  -- Assemble SpiderData
  refine ⟨A, inferInstance, inferInstance,
    { c := c
      armLen := armLen
      vert := vert
      dist_c := fun u d h1 h2 => by
        have := SimpleGraph.dist_le (p (vert u d h1 h2))
        rwa [hvert_len u d h1 h2] at this
      dist_same := hdist_same
      dist_diff := fun u₁ u₂ d₁ d₂ h1 h2 h3 h4 => by
        let q : T.Walk (vert u₁ d₁ h1 h2) (vert u₂ d₂ h3 h4) :=
          (p (vert u₁ d₁ h1 h2)).reverse.append (p (vert u₂ d₂ h3 h4))
        have := SimpleGraph.dist_le q
        simpa [q, Walk.length_append, Walk.length_reverse, hvert_len] using this
      cover_all := fun v => by
        by_cases hvc : v = c
        · exact Or.inl hvc
        · right
          let u := arm v hvc
          have hv_mem : v ∈ armSet u := Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvc, rfl⟩
          have hd1 : 1 ≤ (p v).length := hlen_pos hvc
          have hd2 : (p v).length ≤ armLen u := hlen_le_armLen u hv_mem
          refine ⟨u, (p v).length, hd1, hd2, ?_⟩
          exact hlen_inj u hv_mem (hvert_mem u _ hd1 hd2) (hvert_len u _ hd1 hd2).symm },
    rfl, hcard_V⟩

end TreeToSpider

end SpiderBurning

theorem OMA.solution : OMA.R_BurningNumberConjecture_burning_number_conjecture_R1.H1 := by
  intro k V _ T hT hcard hk ⟨c, _, hdeg⟩
  obtain ⟨A, _, _, S, _, hV⟩ := SpiderBurning.build_spider_data T hT c hdeg
  have htot : 1 + ∑ u : A, S.armLen u ≤ k ^ 2 := by omega
  obtain ⟨xs, hc, harms⟩ :=
    SpiderBurning.burn_abstract_spider S k (by omega) S.armLen (fun _ => le_rfl) htot
  apply Nat.sInf_le
  refine ⟨xs, fun v => ?_⟩
  rcases S.cover_all v with rfl | ⟨u, d, h1, h2, rfl⟩
  · obtain ⟨i, hi⟩ := hc
    exact ⟨i, hT.connected.preconnected (xs i) S.c, hi⟩
  · obtain ⟨i, hi⟩ := harms u d h1 h2 h2
    exact ⟨i, hT.connected.preconnected (xs i) (S.vert u d h1 h2), hi⟩
