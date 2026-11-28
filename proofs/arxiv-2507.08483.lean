import OMAStatements.S_arxiv_2507_08483

open OMA.S_arxiv_2507_08483

namespace OMA.P_arxiv_2507_08483

/-! ### 1. Word-representability implies semi-transitive orientation via `firstPos` -/

private def occ {V : Type*} [DecidableEq V] : List V → V → List ℕ
  | [], _ => []
  | a :: t, x => (if a = x then [0] else []) ++ (occ t x).map (· + 1)

private def Interleaves : List ℕ → List ℕ → Prop
  | [], [] => True
  | [_], [] => True
  | x :: xs, y :: ys => x < y ∧ Interleaves (y :: ys) xs
  | _, _ => False
termination_by xs ys => xs.length + ys.length

private lemma occ_eq_nil_iff {V : Type*} [DecidableEq V] (w : List V) (x : V) :
    occ w x = [] ↔ x ∉ w := by
  induction w with
  | nil => simp [occ]
  | cons a t ih =>
    simp only [occ, List.mem_cons, not_or]
    by_cases h : a = x
    · subst h; simp
    · simp [h, Ne.symm h, ih]

private lemma occ_nonempty {V : Type*} [DecidableEq V] {w : List V} {x : V} (hx : x ∈ w) :
    occ w x ≠ [] := by
  intro h; exact (occ_eq_nil_iff w x).mp h hx

private lemma occ_disjoint {V : Type*} [DecidableEq V] (w : List V) {x y : V} (hne : x ≠ y) :
    ∀ i ∈ occ w x, i ∉ occ w y := by
  induction w with
  | nil => simp [occ]
  | cons a t ih =>
    intro i hi hy
    simp only [occ, List.mem_append, List.mem_map] at hi hy
    by_cases hax : a = x
    · subst hax
      simp only [↓reduceIte, hne, List.mem_singleton, List.not_mem_nil, false_or] at hi hy
      rcases hy with ⟨j, hj, rfl⟩
      rcases hi with h0 | ⟨k, hk, hkj⟩
      · omega
      · exact ih k hk (by rwa [show k = j by omega])
    · simp only [hax, ↓reduceIte, List.not_mem_nil, false_or] at hi
      rcases hi with ⟨k, hk, rfl⟩
      by_cases hay : a = y
      · simp only [hay, ↓reduceIte, List.mem_singleton] at hy
        rcases hy with h0 | ⟨j, hj, hjk⟩
        · omega
        · exact ih k hk (by rwa [show k = j by omega])
      · simp only [hay, ↓reduceIte, List.not_mem_nil, false_or] at hy
        rcases hy with ⟨j, hj, hjk⟩
        exact ih k hk (by rwa [show k = j by omega])

private lemma interleaves_map_succ (xs ys : List ℕ) :
    Interleaves (xs.map (· + 1)) (ys.map (· + 1)) ↔ Interleaves xs ys := by
  suffices ∀ n (xs ys : List ℕ), xs.length + ys.length = n →
      (Interleaves (xs.map (· + 1)) (ys.map (· + 1)) ↔ Interleaves xs ys) from
    this (xs.length + ys.length) xs ys rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs ys hlen
    cases xs with
    | nil => cases ys <;> simp [Interleaves]
    | cons x xs' =>
      cases ys with
      | nil => cases xs' <;> simp [Interleaves]
      | cons y ys' =>
        simp only [List.map_cons, Interleaves]
        have hsub := ih (ys'.length + 1 + xs'.length) (by simp at hlen; omega) (y :: ys') xs' (by simp)
        simp only [List.map_cons] at hsub
        constructor
        · rintro ⟨hlt, hrest⟩; exact ⟨by omega, hsub.mp hrest⟩
        · rintro ⟨hlt, hrest⟩; exact ⟨by omega, hsub.mpr hrest⟩

private lemma alternates_head_iff {V : Type*} [DecidableEq V] (w : List V) {x y : V} (hne : x ≠ y) :
    let l := w.filter (fun z => decide (z = x ∨ z = y))
    (l = [] ↔ occ w x = [] ∧ occ w y = []) ∧
    (NoAdjEq l ∧ l.head? = some x ↔ occ w x ≠ [] ∧ Interleaves (occ w x) (occ w y)) ∧
    (NoAdjEq l ∧ l.head? = some y ↔ occ w y ≠ [] ∧ Interleaves (occ w y) (occ w x)) := by
  induction w with
  | nil => simp [occ, Interleaves]
  | cons a t ih =>
    dsimp only at ih ⊢
    obtain ⟨h_nil, h_x, h_y⟩ := ih
    set lt := t.filter (fun z => decide (z = x ∨ z = y)) with hlt_def
    by_cases hax : a = x
    · subst hax
      have hfilt : (a :: t).filter (fun z => decide (z = a ∨ z = y)) = a :: lt := by simp [lt]
      rw [hfilt]
      have hay : a ≠ y := hne
      have hox : occ (a :: t) a = 0 :: (occ t a).map (· + 1) := by simp [occ]
      have hoy : occ (a :: t) y = (occ t y).map (· + 1) := by simp [occ, hay]
      refine ⟨?_, ?_, ?_⟩
      · simp [hox]
      · simp only [List.head?_cons, and_true, hox, hoy, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
        cases hlt : lt with
        | nil =>
          have ⟨hx0, hy0⟩ := h_nil.mp hlt
          simp [NoAdjEq, hx0, hy0, Interleaves]
        | cons b bs =>
          have hb_mem : b ∈ t.filter (fun z => decide (z = a ∨ z = y)) := by rw [← hlt_def, hlt]; simp
          have hb_or : b = a ∨ b = y := by simpa using (List.mem_filter.mp hb_mem).2
          rcases hb_or with hba | hby
          · subst hba
            simp only [NoAdjEq, ne_eq, not_true_eq_false, false_and, false_iff]
            intro hint
            cases hoy_eq : occ t y with
            | nil =>
              rw [hoy_eq, List.map_nil] at hint
              have hne_a : occ t b ≠ [] := by
                intro ha0
                have := h_nil.mpr ⟨ha0, hoy_eq⟩
                rw [hlt] at this; exact List.cons_ne_nil _ _ this
              cases hta : occ t b with
              | nil => exact hne_a hta
              | cons u us => rw [hta] at hint; simp [Interleaves] at hint
            | cons u us =>
              rw [hoy_eq, List.map_cons, Interleaves] at hint
              have hiy := (interleaves_map_succ (u :: us) (occ t b)).mp hint.2
              have hy_hd : NoAdjEq lt ∧ lt.head? = some y := h_y.mpr ⟨by rw [hoy_eq]; simp, by rwa [hoy_eq]⟩
              rw [hlt] at hy_hd; simp [hay] at hy_hd
          · subst hby
            simp only [NoAdjEq, hay, ne_eq, not_false_eq_true, true_and]
            have hlt_y : NoAdjEq lt ∧ lt.head? = some b ↔ NoAdjEq (b :: bs) := by rw [hlt]; simp
            rw [← hlt_y, h_y]
            cases hoy_eq : occ t b with
            | nil =>
              have hne_y : occ t b ≠ [] := by
                intro hy0
                have hny : b ∉ t := (occ_eq_nil_iff t b).mp hy0
                exact hny (List.mem_filter.mp hb_mem).1
              exact absurd hoy_eq hne_y
            | cons u us =>
              simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and, List.map_cons, Interleaves]
              have h0lt : 0 < u + 1 := Nat.succ_pos _
              simp only [h0lt, true_and]
              have hms := interleaves_map_succ (u :: us) (occ t a)
              simpa [hoy_eq] using hms.symm
      · simp only [List.head?_cons, Option.some.injEq, hay, and_false, false_iff, not_and]
        intro hne_y hint
        rw [hox, hoy] at hint
        rw [hoy] at hne_y
        cases hoy_eq : occ t y with
        | nil => rw [hoy_eq, List.map_nil] at hne_y; exact hne_y rfl
        | cons u us =>
          rw [hoy_eq, List.map_cons, Interleaves] at hint
          omega
    · by_cases hay : a = y
      · subst hay
        have hfilt : (a :: t).filter (fun z => decide (z = x ∨ z = a)) = a :: lt := by simp [lt]
        rw [hfilt]
        have hox : occ (a :: t) x = (occ t x).map (· + 1) := by simp [occ, hax]
        have hoy : occ (a :: t) a = 0 :: (occ t a).map (· + 1) := by simp [occ]
        refine ⟨?_, ?_, ?_⟩
        · simp [hoy]
        · simp only [List.head?_cons, Option.some.injEq, hax, and_false, false_iff, not_and]
          intro hne_x hint
          rw [hox, hoy] at hint
          rw [hox] at hne_x
          cases hox_eq : occ t x with
          | nil => rw [hox_eq, List.map_nil] at hne_x; exact hne_x rfl
          | cons u us =>
            rw [hox_eq, List.map_cons, Interleaves] at hint
            omega
        · simp only [List.head?_cons, and_true, hox, hoy, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
          cases hlt : lt with
          | nil =>
            have ⟨hx0, hy0⟩ := h_nil.mp hlt
            simp [NoAdjEq, hx0, hy0, Interleaves]
          | cons b bs =>
            have hb_mem : b ∈ t.filter (fun z => decide (z = x ∨ z = a)) := by rw [← hlt_def, hlt]; simp
            have hb_or : b = x ∨ b = a := by simpa using (List.mem_filter.mp hb_mem).2
            rcases hb_or with hbx | hba
            · subst hbx
              simp only [NoAdjEq, hax, ne_eq, not_false_eq_true, true_and]
              have hlt_x : NoAdjEq lt ∧ lt.head? = some b ↔ NoAdjEq (b :: bs) := by rw [hlt]; simp
              rw [← hlt_x, h_x]
              cases hox_eq : occ t b with
              | nil =>
                have hne_x : occ t b ≠ [] := by
                  intro hx0
                  have hnx : b ∉ t := (occ_eq_nil_iff t b).mp hx0
                  exact hnx (List.mem_filter.mp hb_mem).1
                exact absurd hox_eq hne_x
              | cons u us =>
                simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and, List.map_cons, Interleaves]
                have h0lt : 0 < u + 1 := Nat.succ_pos _
                simp only [h0lt, true_and]
                have hms := interleaves_map_succ (u :: us) (occ t a)
                simpa [hox_eq] using hms.symm
            · subst hba
              simp only [NoAdjEq, ne_eq, not_true_eq_false, false_and, false_iff]
              intro hint
              cases hox_eq : occ t x with
              | nil =>
                rw [hox_eq, List.map_nil] at hint
                have hne_a : occ t b ≠ [] := by
                  intro ha0
                  have := h_nil.mpr ⟨hox_eq, ha0⟩
                  rw [hlt] at this; exact List.cons_ne_nil _ _ this
                cases hta : occ t b with
                | nil => exact hne_a hta
                | cons u us => rw [hta] at hint; simp [Interleaves] at hint
              | cons u us =>
                rw [hox_eq, List.map_cons, Interleaves] at hint
                have hix := (interleaves_map_succ (u :: us) (occ t b)).mp hint.2
                have hx_hd : NoAdjEq lt ∧ lt.head? = some x := h_x.mpr ⟨by rw [hox_eq]; simp, by rwa [hox_eq]⟩
                rw [hlt] at hx_hd; simp [hax] at hx_hd
      · have hfilt : (a :: t).filter (fun z => decide (z = x ∨ z = y)) = lt := by simp [lt, hax, hay]
        rw [hfilt]
        have hox : occ (a :: t) x = (occ t x).map (· + 1) := by simp [occ, hax]
        have hoy : occ (a :: t) y = (occ t y).map (· + 1) := by simp [occ, hay]
        rw [hox, hoy]
        refine ⟨?_, ?_, ?_⟩
        · simpa using h_nil
        · rw [h_x, interleaves_map_succ]; simp
        · rw [h_y, interleaves_map_succ]; simp

private lemma interleaves_iff_getD (xs ys : List ℕ) :
    Interleaves xs ys ↔
      ys.length ≤ xs.length ∧ xs.length ≤ ys.length + 1 ∧
      (∀ r < ys.length, xs.getD r 0 < ys.getD r 0) ∧
      (∀ r, r + 1 < xs.length → ys.getD r 0 < xs.getD (r + 1) 0) := by
  suffices ∀ n (xs ys : List ℕ), xs.length + ys.length = n →
      (Interleaves xs ys ↔
        ys.length ≤ xs.length ∧ xs.length ≤ ys.length + 1 ∧
        (∀ r < ys.length, xs.getD r 0 < ys.getD r 0) ∧
        (∀ r, r + 1 < xs.length → ys.getD r 0 < xs.getD (r + 1) 0)) from
    this (xs.length + ys.length) xs ys rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs ys hlen
    cases xs with
    | nil => cases ys <;> simp [Interleaves]
    | cons x xs' =>
      cases ys with
      | nil => cases xs' <;> simp [Interleaves]
      | cons y ys' =>
        simp only [Interleaves]
        have hsub := ih (ys'.length + 1 + xs'.length) (by simp only [List.length_cons] at hlen; omega) (y :: ys') xs' (by simp only [List.length_cons])
        rw [hsub]
        constructor
        · rintro ⟨hxy, hle1, hle2, hlt1, hlt2⟩
          simp only [List.length_cons] at hle1 hle2 ⊢
          refine ⟨by omega, by omega, ?_, ?_⟩
          · intro r hr
            cases r with
            | zero => simpa using hxy
            | succ r' =>
              have h := hlt2 r' (by simp only [List.length_cons] at hr ⊢; omega)
              simpa using h
          · intro r hr
            have h := hlt1 r (by omega)
            simpa using h
        · rintro ⟨hle1, hle2, hlt1, hlt2⟩
          simp only [List.length_cons] at hle1 hle2 hlt1 hlt2 ⊢
          refine ⟨by simpa using hlt1 0 (Nat.zero_lt_succ _), by omega, by omega, ?_, ?_⟩
          · intro r hr
            have h := hlt2 r (by omega)
            simpa using h
          · intro r hr
            have h := hlt1 (r + 1) (by omega)
            simpa using h

private lemma alternates_iff_interleaves {V : Type*} [DecidableEq V] {w : List V}
    {x y : V} (hne : x ≠ y) (hx : x ∈ w) (hy : y ∈ w) :
    Alternates w x y ↔ Interleaves (occ w x) (occ w y) ∨ Interleaves (occ w y) (occ w x) := by
  have ⟨h_nil, h_x, h_y⟩ := alternates_head_iff w hne
  have hox := occ_nonempty hx
  have hoy := occ_nonempty hy
  set l := w.filter (fun z => decide (z = x ∨ z = y))
  have hl_ne : l ≠ [] := fun h => hox (h_nil.mp h).1
  cases hl : l with
  | nil => exact absurd hl hl_ne
  | cons a t =>
    have ha_mem : a ∈ l := by rw [hl]; simp
    have ha_or : a = x ∨ a = y := by simpa [l] using (List.mem_filter.mp ha_mem).2
    change NoAdjEq l ↔ _
    constructor
    · intro hno
      rcases ha_or with rfl | rfl
      · exact Or.inl (h_x.mp ⟨hno, by rw [hl]; rfl⟩).2
      · exact Or.inr (h_y.mp ⟨hno, by rw [hl]; rfl⟩).2
    · rintro (h1 | h2)
      · exact (h_x.mpr ⟨hox, h1⟩).1
      · exact (h_y.mpr ⟨hoy, h2⟩).1

private lemma interleaves_first_lt {xs ys : List ℕ} (h : Interleaves xs ys) (hys : ys ≠ []) :
    xs.getD 0 0 < ys.getD 0 0 := by
  have ⟨_, _, hlt1, _⟩ := (interleaves_iff_getD xs ys).mp h
  exact hlt1 0 (List.length_pos_of_ne_nil hys)

private def IsSemiTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ D : V → V → Prop,
    (∀ u v, D u v → G.Adj u v) ∧
    (∀ u v, G.Adj u v → D u v ∨ D v u) ∧
    (∀ u v, D u v → ¬ D v u) ∧
    (∀ (l : List V) (hlen : 2 ≤ l.length),
      (∀ i (h : i + 1 < l.length), D (l[i]'(by omega)) (l[i + 1])) →
      l[0]'(by omega) ≠ l[l.length - 1]'(by omega)) ∧
    (∀ (l : List V) (hlen : 3 ≤ l.length),
      (∀ i (h : i + 1 < l.length), D (l[i]'(by omega)) (l[i + 1])) →
      D (l[0]'(by omega)) (l[l.length - 1]'(by omega)) →
      ∀ i j (hi : i < j) (hj : j < l.length), D (l[i]'(by omega)) (l[j]))

private lemma wordRep_imp_semiTransitive {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hG : IsWordRepresentable G) : IsSemiTransitive G := by
  obtain ⟨w, hw_mem, hw_alt⟩ := hG
  let first : V → ℕ := fun v => (occ w v).getD 0 0
  have hfirst_mem : ∀ v : V, first v ∈ occ w v := by
    intro v
    have hne := occ_nonempty (hw_mem v)
    cases ho : occ w v with
    | nil => exact absurd ho hne
    | cons hd tl => simp [first, ho]
  have hfirst_inj : ∀ u v : V, u ≠ v → first u ≠ first v := by
    intro u v hne heq
    have hu0 : first u ∈ occ w u := hfirst_mem u
    have hv0 : first v ∈ occ w v := hfirst_mem v
    rw [heq] at hu0
    exact occ_disjoint w hne _ hu0 hv0
  let D : V → V → Prop := fun u v => G.Adj u v ∧ first u < first v
  have hD_inter : ∀ u v : V, D u v → Interleaves (occ w u) (occ w v) := by
    intro u v ⟨hadj, hlt⟩
    have hne : u ≠ v := G.ne_of_adj hadj
    rcases (alternates_iff_interleaves hne (hw_mem u) (hw_mem v)).mp ((hw_alt u v hne).mp hadj) with h1 | h2
    · exact h1
    · have hgt := interleaves_first_lt h2 (occ_nonempty (hw_mem u))
      exact absurd hlt (by dsimp only [first] at *; omega)
  refine ⟨D, fun _ _ h => h.1, ?_, fun _ _ h1 h2 => by omega, ?_, ?_⟩
  · intro u v hadj
    have hne := hfirst_inj u v (G.ne_of_adj hadj)
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨hadj, h⟩
    · exact Or.inr ⟨hadj.symm, h⟩
  · intro l hlen hpath
    have hmono : ∀ a b (hab : a < b) (hb : b < l.length),
        first (l[a]'(by omega)) < first (l[b]) := by
      intro a b hab hb
      induction b with
      | zero => omega
      | succ b ih =>
        by_cases h : a = b
        · subst h; exact (hpath a hb).2
        · exact lt_trans (ih (by omega) (by omega)) (hpath b hb).2
    intro heq
    have hlt := hmono 0 (l.length - 1) (by omega) (by omega)
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · intro l hlen hpath hshort i j hij hj
    have hstep_len : ∀ a b (hab : a ≤ b) (hb : b < l.length),
        (occ w (l[b])).length ≤ (occ w (l[a]'(by omega))).length := by
      intro a b hab hb
      induction b with
      | zero =>
        have : a = 0 := by omega
        subst this; exact le_rfl
      | succ b ih =>
        by_cases h : a = b + 1
        · subst h; exact le_rfl
        · have h1 := ih (by omega) (by omega)
          have h2 := ((interleaves_iff_getD _ _).mp (hD_inter _ _ (hpath b hb))).1
          exact le_trans h2 h1
    have hstep_lt : ∀ a b (hab : a < b) (hb : b < l.length) (r : ℕ)
        (hr : r < (occ w (l[b])).length),
        (occ w (l[a]'(by omega))).getD r 0 < (occ w (l[b])).getD r 0 := by
      intro a b hab hb r hr
      induction b with
      | zero => omega
      | succ b ih =>
        have hlast := ((interleaves_iff_getD _ _).mp (hD_inter _ _ (hpath b hb))).2.2.1 r hr
        by_cases h : a = b
        · subst h; exact hlast
        · have hrb : r < (occ w (l[b]'(by omega))).length := by
            have := hstep_len b (b + 1) (by omega) hb; omega
          exact lt_trans (ih (by omega) (by omega) hrb) hlast
    have hstep_le : ∀ a b (hab : a ≤ b) (hb : b < l.length) (r : ℕ)
        (hr : r < (occ w (l[b])).length),
        (occ w (l[a]'(by omega))).getD r 0 ≤ (occ w (l[b])).getD r 0 := by
      intro a b hab hb r hr
      rcases eq_or_lt_of_le hab with rfl | hlt
      · exact le_rfl
      · exact le_of_lt (hstep_lt a b hlt hb r hr)
    have h0m := (interleaves_iff_getD _ _).mp (hD_inter _ _ hshort)
    have hlen_ji : (occ w (l[j])).length ≤ (occ w (l[i]'(by omega))).length :=
      hstep_len i j (by omega) hj
    have hlen_i0 : (occ w (l[i]'(by omega))).length ≤ (occ w (l[0]'(by omega))).length :=
      hstep_len 0 i (by omega) (by omega)
    have hlen_mj : (occ w (l[l.length - 1]'(by omega))).length ≤ (occ w (l[j])).length :=
      hstep_len j (l.length - 1) (by omega) (by omega)
    have hlen_ij1 : (occ w (l[i]'(by omega))).length ≤ (occ w (l[j])).length + 1 := by
      have := h0m.2.1; omega
    have hint_ij : Interleaves (occ w (l[i]'(by omega))) (occ w (l[j])) := by
      rw [interleaves_iff_getD]
      refine ⟨hlen_ji, hlen_ij1, ?_, ?_⟩
      · intro r hr; exact hstep_lt i j hij hj r hr
      · intro r hr
        have hr_m : r < (occ w (l[l.length - 1]'(by omega))).length := by
          have := h0m.2.1; omega
        have hr1_0 : r + 1 < (occ w (l[0]'(by omega))).length := by omega
        have h1 : (occ w (l[j])).getD r 0 ≤ (occ w (l[l.length - 1]'(by omega))).getD r 0 :=
          hstep_le j (l.length - 1) (by omega) (by omega) r hr_m
        have h2 : (occ w (l[l.length - 1]'(by omega))).getD r 0 <
            (occ w (l[0]'(by omega))).getD (r + 1) 0 := h0m.2.2.2 r hr1_0
        have h3 : (occ w (l[0]'(by omega))).getD (r + 1) 0 ≤
            (occ w (l[i]'(by omega))).getD (r + 1) 0 :=
          hstep_le 0 i (by omega) (by omega) (r + 1) hr
        omega
    have hfirst_ij : first (l[i]'(by omega)) < first (l[j]) :=
      hstep_lt i j hij hj 0 (List.length_pos_of_ne_nil (occ_nonempty (hw_mem _)))
    have hne_ij : l[i]'(by omega) ≠ l[j] := fun h => lt_irrefl _ (h ▸ hfirst_ij)
    refine ⟨?_, hfirst_ij⟩
    exact (hw_alt _ _ hne_ij).mpr ((alternates_iff_interleaves hne_ij (hw_mem _) (hw_mem _)).mpr (Or.inl hint_ij))

private lemma semiTransitive_of_induced {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : IsSemiTransitive G) (hsub : HasInducedSubgraph G H) : IsSemiTransitive H := by
  obtain ⟨D, hD_adj, hD_cov, hD_asym, hD_acyc, hD_short⟩ := hG
  obtain ⟨f, hf⟩ := hsub
  refine ⟨fun u v => D (f u) (f v), ?_, ?_, ?_, ?_, ?_⟩
  · intro u v h; exact (hf u v).mpr (hD_adj _ _ h)
  · intro u v h; exact hD_cov _ _ ((hf u v).mp h)
  · intro u v h; exact hD_asym _ _ h
  · intro l hlen hpath heq
    have hmap := hD_acyc (l.map f) (by simp; omega) (by
      intro i hi; simp only [List.getElem_map]; exact hpath i (by simpa using hi))
    simp only [List.length_map, List.getElem_map] at hmap
    exact hmap (congrArg f heq)
  · intro l hlen hpath hshort i j hij hj
    have hmap := hD_short (l.map f) (by simp; omega)
      (by intro k hk; simp only [List.getElem_map]; exact hpath k (by simpa using hk))
      (by simp only [List.length_map, List.getElem_map]; exact hshort)
      i j hij (by simp; exact hj)
    simpa only [List.getElem_map] using hmap

/-! ### 2. Semi-transitivity on `mkSplitGraph` implies Kitaev–Pyatkin Theorem 2.5 -/

private def isContig (pos : List ℕ) : Option (ℕ × ℕ) :=
  match pos with
  | [] => none
  | a :: rest =>
    let b := (a :: rest).getLast (List.cons_ne_nil a rest)
    if (a :: rest) == (List.range (b + 1 - a)).map (· + a) then some (a, b) else none

private def classifyIndep (k : ℕ) (pos : List ℕ) : ℕ × ℕ × ℕ :=
  if pos.isEmpty then (0, 0, 0)
  else match isContig pos with
  | some (a, b) => (1, a, b)
  | none =>
    let gaps := (List.range k).filter (fun i => !pos.contains i)
    match isContig gaps with
    | some (g1, g2) =>
      if 0 < g1 && g2 + 1 < k then (2, g1 - 1, g2 + 1) else (3, 0, 0)
    | none => (3, 0, 0)

private def kpValid (e : ℕ) (cols : List ℕ) (p : List ℕ) : Bool :=
  let k := p.length
  let types := (List.range e).map fun i =>
    let pos := (List.range k).filter fun idx =>
      let j := p.getD idx 0
      ((cols.getD j 0) >>> i) % 2 == 1
    classifyIndep k pos
  types.all (fun t => t.1 != 3) &&
  (List.range e).all fun i =>
    let ti := types.getD i (3, 0, 0)
    if ti.1 == 2 then
      let a2 := ti.2.1; let b2 := ti.2.2
      (List.range e).all fun j =>
        if i == j then true
        else
          let tj := types.getD j (3, 0, 0)
          if tj.1 == 1 then (tj.2.1 > a2) || (tj.2.2 < b2)
          else if tj.1 == 2 then (a2 < tj.2.2) && (tj.2.1 < b2)
          else true
    else true

private def insertEverywhere (x : ℕ) : List ℕ → List (List ℕ)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertEverywhere x ys).map (y :: ·)

private def allPerms : List ℕ → List (List ℕ)
  | [] => [[]]
  | x :: xs => (allPerms xs).flatMap (insertEverywhere x)

private lemma perm_mem_allPerms (l p : List ℕ) (hp : p.Perm l) : p ∈ allPerms l := by
  induction l generalizing p with
  | nil =>
    have := List.perm_nil.mp hp
    subst this; simp [allPerms]
  | cons x xs ih =>
    have hx : x ∈ p := hp.mem_iff.mpr (List.mem_cons_self ..)
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hx
    have hrest : (l1 ++ l2).Perm xs := by
      have h1 : (x :: (l1 ++ l2)).Perm (l1 ++ x :: l2) := List.perm_middle.symm
      exact (List.perm_cons x).mp (h1.trans hp)
    have hmem : l1 ++ l2 ∈ allPerms xs := ih _ hrest
    rw [allPerms, List.mem_flatMap]
    refine ⟨l1 ++ l2, hmem, ?_⟩
    clear hp hrest hmem ih hx
    induction l1 with
    | nil => cases l2 <;> simp [insertEverywhere]
    | cons a as iha =>
      simp only [List.cons_append, insertEverywhere, List.mem_cons, List.mem_map]
      exact Or.inr ⟨as ++ x :: l2, iha, rfl⟩

private lemma isContig_range (a b : ℕ) (hab : a ≤ b) :
    isContig ((List.range (b + 1 - a)).map (· + a)) = some (a, b) := by
  cases hlen : b + 1 - a with
  | zero => omega
  | succ m =>
    have hm : a + m = b := by omega
    have hcons : (List.range (m + 1)).map (· + a) = a :: (List.range m).map (fun x => (x + 1) + a) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]; simp
    have hlast : ((List.range (m + 1)).map (· + a)).getLast (by simp) = b := by
      rw [List.getLast_map, List.getLast_range]; omega
    unfold isContig
    split
    · next h => exact absurd h (by simp)
    · next hd tl heq =>
      have hhd : hd = a := by
        have := congrArg List.head? (heq.symm.trans hcons)
        simpa using this
      subst hhd
      have hlast' : (hd :: tl).getLast (List.cons_ne_nil _ _) = b := by
        simpa [heq] using hlast
      rw [hlast']
      have hsame : (hd :: tl == (List.range (b + 1 - hd)).map (· + hd)) = true := by
        rw [beq_iff_eq, hlen, ← heq]
      simp [hsame]

private lemma isContig_none_of_gap {pos : List ℕ} {x y z : ℕ}
    (hx : x ∈ pos) (hz : z ∈ pos) (hxy : x < y) (hyz : y < z) (hy : y ∉ pos) :
    isContig pos = none := by
  cases pos with
  | nil => simp at hx
  | cons a rest =>
    unfold isContig
    simp only
    split_ifs with heq
    · exfalso
      have hpeq := beq_iff_eq.mp heq
      have hxm : x ∈ (List.range ((a :: rest).getLast (List.cons_ne_nil a rest) + 1 - a)).map (· + a) :=
        hpeq ▸ hx
      have hzm : z ∈ (List.range ((a :: rest).getLast (List.cons_ne_nil a rest) + 1 - a)).map (· + a) :=
        hpeq ▸ hz
      simp only [List.mem_map, List.mem_range] at hxm hzm
      obtain ⟨tx, _, rfl⟩ := hxm
      obtain ⟨tz, htz, rfl⟩ := hzm
      have hym : y ∈ (List.range ((a :: rest).getLast (List.cons_ne_nil a rest) + 1 - a)).map (· + a) := by
        simp only [List.mem_map, List.mem_range]
        exact ⟨y - a, by omega, by omega⟩
      exact hy (hpeq.symm ▸ hym)
    · rfl

private lemma list_eq_of_perm_of_pairwise_lt {l1 l2 : List ℕ}
    (hp : l1.Perm l2) (h1 : l1.Pairwise (· < ·)) (h2 : l2.Pairwise (· < ·)) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => exact (List.perm_nil.mp hp.symm).symm
  | cons a as ih =>
    cases l2 with
    | nil => exact absurd hp.length_eq (by simp)
    | cons b bs =>
      rw [List.pairwise_cons] at h1 h2
      have hab : a = b := by
        have ha_mem : a ∈ b :: bs := hp.mem_iff.mp (List.mem_cons_self ..)
        have hb_mem : b ∈ a :: as := hp.symm.mem_iff.mp (List.mem_cons_self ..)
        simp only [List.mem_cons] at ha_mem hb_mem
        rcases ha_mem with rfl | ha_bs
        · rfl
        · rcases hb_mem with rfl | hb_as
          · rfl
          · have hlt1 := h2.1 a ha_bs
            have hlt2 := h1.1 b hb_as
            omega
      subst hab
      congr 1
      exact ih ((List.perm_cons a).mp hp) h1.2 h2.2

private lemma list_contains_iff_mem (l : List ℕ) (x : ℕ) : l.contains x = true ↔ x ∈ l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.contains, List.elem_cons, List.mem_cons]
    cases h : (x == a)
    · simp only [beq_eq_false_iff_ne] at h
      rw [show List.elem x t = t.contains x from rfl, ih]; tauto
    · simp only [beq_iff_eq] at h; simp [h]

private lemma filter_range_eq_interval (k a b : ℕ) (hab : a ≤ b) (hb : b < k) (P : ℕ → Bool)
    (hP : ∀ i < k, P i = true ↔ a ≤ i ∧ i ≤ b) :
    (List.range k).filter P = (List.range (b + 1 - a)).map (· + a) := by
  have h1 : ((List.range k).filter P).Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
  have h2 : ((List.range (b + 1 - a)).map (· + a)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp (fun h => by omega)
  have hmem : ∀ x, x ∈ (List.range k).filter P ↔ x ∈ (List.range (b + 1 - a)).map (· + a) := by
    intro x
    simp only [List.mem_filter, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨hxk, hpx⟩
      have ⟨h1, h2⟩ := (hP x hxk).mp hpx
      exact ⟨x - a, by omega, by omega⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by omega, (hP (t + a) (by omega)).mpr ⟨by omega, by omega⟩⟩
  have hperm : ((List.range k).filter P).Perm ((List.range (b + 1 - a)).map (· + a)) :=
    (List.perm_ext_iff_of_nodup (h1.imp ne_of_lt) (h2.imp ne_of_lt)).mpr hmem
  exact list_eq_of_perm_of_pairwise_lt hperm h1 h2

private lemma semiTransitive_mkSplitGraph_imp_kp (e k : ℕ) (cols : List ℕ)
    (hno_full : ∀ i : Fin e, ∃ j : Fin k, ((cols.getD j.val 0) >>> i.val) % 2 ≠ 1)
    (hST : IsSemiTransitive (mkSplitGraph e k cols)) :
    (allPerms (List.range k)).any (kpValid e cols) = true := by
  obtain ⟨D, hD_adj, hD_cov, hD_asym, hD_acyc, hD_short⟩ := hST
  let kv : Fin k → Fin (e + k) := fun j => ⟨e + j.val, by omega⟩
  let iv : Fin e → Fin (e + k) := fun i => ⟨i.val, by omega⟩
  have hE_indep : ∀ i1 i2 : Fin e, ¬ (mkSplitGraph e k cols).Adj (iv i1) (iv i2) := by
    intro i1 i2 ⟨_, h⟩
    rcases h with ⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> dsimp [iv] at * <;> omega
  have hK_adj : ∀ j1 j2 : Fin k, j1 ≠ j2 → (mkSplitGraph e k cols).Adj (kv j1) (kv j2) := by
    intro j1 j2 hne
    refine ⟨fun h => hne (Fin.ext (by have := congrArg Fin.val h; dsimp [kv] at this; omega)),
      Or.inl ⟨by dsimp [kv]; omega, by dsimp [kv]; omega⟩⟩
  have hD_trans_K : ∀ a b c : Fin k, D (kv a) (kv b) → D (kv b) (kv c) → D (kv a) (kv c) := by
    intro a b c hab hbc
    have hac_ne : a ≠ c := by rintro rfl; exact hD_asym _ _ hab hbc
    rcases hD_cov _ _ (hK_adj a c hac_ne) with h1 | h2
    · exact h1
    · exfalso
      exact hD_acyc [kv a, kv b, kv c, kv a] (by simp) (by
        intro idx hidx; simp only [List.length_cons, List.length_nil] at hidx
        have hlt3 : idx < 3 := by omega
        interval_cases idx; exacts [hab, hbc, h2]) rfl
  have hD_irrefl : ∀ x, ¬ D x x := fun x h => hD_asym x x h h
  classical
  let rk : Fin k → ℕ := fun j => (Finset.univ.filter (fun i : Fin k => D (kv i) (kv j))).card
  have hrk_lt : ∀ j : Fin k, rk j < k := by
    intro j
    have hsub : Finset.univ.filter (fun i : Fin k => D (kv i) (kv j)) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have : j ∈ Finset.univ.filter (fun i : Fin k => D (kv i) (kv j)) := by rw [h]; exact Finset.mem_univ j
      exact hD_irrefl (kv j) (Finset.mem_filter.mp this).2
    simpa [rk] using Finset.card_lt_card hsub
  have hrk_mono : ∀ a b : Fin k, D (kv a) (kv b) → rk a < rk b := by
    intro a b hab
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, hD_trans_K x a b hx.2 hab⟩
    · intro heq
      have ha : a ∈ Finset.univ.filter (fun i : Fin k => D (kv i) (kv b)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
      rw [← heq, Finset.mem_filter] at ha
      exact hD_irrefl (kv a) ha.2
  have hrk_inj : Function.Injective (fun j : Fin k => (⟨rk j, hrk_lt j⟩ : Fin k)) := by
    intro a b h
    by_contra hne
    have hval : rk a = rk b := congrArg Fin.val h
    rcases hD_cov _ _ (hK_adj a b hne) with hab | hba
    · exact absurd hval (ne_of_lt (hrk_mono a b hab))
    · exact absurd hval (ne_of_gt (hrk_mono b a hba))
  let rkEquiv : Fin k ≃ Fin k := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hrk_inj)
  let ord : Fin k → Fin k := rkEquiv.symm
  have hord_D : ∀ a b : Fin k, a.val < b.val → D (kv (ord a)) (kv (ord b)) := by
    intro a b hlt
    have hne : ord a ≠ ord b := fun h => by have := rkEquiv.symm.injective h; omega
    rcases hD_cov _ _ (hK_adj (ord a) (ord b) hne) with h1 | h2
    · exact h1
    · exfalso
      have hgt := hrk_mono (ord b) (ord a) h2
      have h1 : rk (ord a) = a.val := congrArg Fin.val (rkEquiv.apply_symm_apply a)
      have h2' : rk (ord b) = b.val := congrArg Fin.val (rkEquiv.apply_symm_apply b)
      omega
  let p : List ℕ := (List.finRange k).map (fun idx => (ord idx).val)
  have hp_len : p.length = k := by simp [p]
  have hp_perm : p.Perm (List.range k) := by
    have hnd : p.Nodup := by
      refine List.Nodup.map ?_ (List.nodup_finRange k)
      intro a b h; exact rkEquiv.symm.injective (Fin.ext h)
    refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).mpr fun x => ?_
    simp only [p, List.mem_map, List.mem_finRange, true_and, List.mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact (ord i).isLt
    · intro hx; exact ⟨rkEquiv ⟨x, hx⟩, by simp [ord]⟩
  rw [List.any_eq_true]
  refine ⟨p, perm_mem_allPerms (List.range k) p hp_perm, ?_⟩
  have hp_getD : ∀ idx (hidx : idx < k), p.getD idx 0 = (ord ⟨idx, hidx⟩).val := by
    intro idx hidx
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp [p]
  have hadj_bit : ∀ (i : Fin e) (idx : Fin k),
      (mkSplitGraph e k cols).Adj (iv i) (kv (ord idx)) ↔
      ((cols.getD (p.getD idx.val 0) 0) >>> i.val) % 2 = 1 := by
    intro i idx
    rw [hp_getD idx.val idx.isLt]
    simp only [mkSplitGraph, iv, kv]
    constructor
    · rintro ⟨_, h⟩
      rcases h with ⟨h1, _⟩ | ⟨_, _, h3⟩ | ⟨h1, _, _⟩
      · omega
      · simpa [Nat.add_sub_cancel_left] using h3
      · omega
    · intro hbit
      refine ⟨fun h => by have hv := congrArg Fin.val h; dsimp only at hv; have := i.isLt; omega,
        Or.inr (Or.inl ⟨i.isLt, by omega, by simpa [Nat.add_sub_cancel_left] using hbit⟩)⟩
  have hOut_contig : ∀ (i : Fin e) (a t b : Fin k), a.val < t.val → t.val < b.val →
      D (iv i) (kv (ord a)) → D (iv i) (kv (ord b)) → D (iv i) (kv (ord t)) := by
    intro i a t b hat htb ha hb
    exact hD_short [iv i, kv (ord a), kv (ord t), kv (ord b)] (by simp) (by
      intro idx hidx; simp only [List.length_cons, List.length_nil] at hidx
      have hlt3 : idx < 3 := by omega
      interval_cases idx; exacts [ha, hord_D a t hat, hord_D t b htb])
      hb 0 2 (by decide) (by simp)
  have hIn_contig : ∀ (i : Fin e) (a t b : Fin k), a.val < t.val → t.val < b.val →
      D (kv (ord a)) (iv i) → D (kv (ord b)) (iv i) → D (kv (ord t)) (iv i) := by
    intro i a t b hat htb ha hb
    exact hD_short [kv (ord a), kv (ord t), kv (ord b), iv i] (by simp) (by
      intro idx hidx; simp only [List.length_cons, List.length_nil] at hidx
      have hlt3 : idx < 3 := by omega
      interval_cases idx; exacts [hord_D a t hat, hord_D t b htb, hb])
      ha 1 3 (by decide) (by simp)
  have hNo_out_before_in : ∀ (i : Fin e) (a b : Fin k), a.val < b.val →
      D (iv i) (kv (ord a)) → D (kv (ord b)) (iv i) → False := by
    intro i a b hab ha hb
    exact hD_acyc [iv i, kv (ord a), kv (ord b), iv i] (by simp) (by
      intro idx hidx; simp only [List.length_cons, List.length_nil] at hidx
      have hlt3 : idx < 3 := by omega
      interval_cases idx; exacts [ha, hord_D a b hab, hb]) rfl
  have hIn_prefix : ∀ (i : Fin e) (t a b : Fin k), t.val < a.val → a.val < b.val →
      D (kv (ord a)) (iv i) → D (iv i) (kv (ord b)) → D (kv (ord t)) (iv i) := by
    intro i t a b hta hab ha hb
    exact hD_short [kv (ord t), kv (ord a), iv i, kv (ord b)] (by simp) (by
      intro idx hidx; simp only [List.length_cons, List.length_nil] at hidx
      have hlt3 : idx < 3 := by omega
      interval_cases idx; exacts [hord_D t a hta, ha, hb])
      (hord_D t b (by omega)) 0 2 (by decide) (by simp)
  have hOut_suffix : ∀ (i : Fin e) (a b t : Fin k), a.val < b.val → b.val < t.val →
      D (kv (ord a)) (iv i) → D (iv i) (kv (ord b)) → D (iv i) (kv (ord t)) := by
    intro i a b t hab hbt ha hb
    exact hD_short [kv (ord a), iv i, kv (ord b), kv (ord t)] (by simp) (by
      intro idx hidx; simp only [List.length_cons, List.length_nil] at hidx
      have hlt3 : idx < 3 := by omega
      interval_cases idx; exacts [ha, hb, hord_D b t hbt])
      (hord_D a t (by omega)) 1 3 (by decide) (by simp)
  let posOf : Fin e → List ℕ := fun i =>
    (List.range k).filter fun idx => ((cols.getD (p.getD idx 0) 0) >>> i.val) % 2 == 1
  have hpos_mem : ∀ (i : Fin e) (idx : Fin k),
      idx.val ∈ posOf i ↔ (mkSplitGraph e k cols).Adj (iv i) (kv (ord idx)) := by
    intro i idx
    simp only [posOf, List.mem_filter, List.mem_range, idx.isLt, true_and, beq_iff_eq]
    exact (hadj_bit i idx).symm
  have hclass : ∀ i : Fin e,
      let c := classifyIndep k (posOf i)
      (c.1 = 0) ∨
      (c.1 = 1 ∧ c.2.1 ≤ c.2.2 ∧ c.2.2 < k ∧
        ((∀ idx : Fin k, c.2.1 ≤ idx.val ∧ idx.val ≤ c.2.2 → D (iv i) (kv (ord idx))) ∨
         (∀ idx : Fin k, c.2.1 ≤ idx.val ∧ idx.val ≤ c.2.2 → D (kv (ord idx)) (iv i)))) ∨
      (c.1 = 2 ∧ c.2.1 < c.2.2 ∧ c.2.2 < k ∧
        (∀ idx : Fin k, idx.val ≤ c.2.1 → D (kv (ord idx)) (iv i)) ∧
        (∀ idx : Fin k, c.2.2 ≤ idx.val → D (iv i) (kv (ord idx)))) := by
    intro i
    by_cases hIn : ∃ idx : Fin k, D (kv (ord idx)) (iv i)
    · by_cases hOut : ∃ idx : Fin k, D (iv i) (kv (ord idx))
      · -- Type C
        let SIn := Finset.univ.filter (fun idx : Fin k => D (kv (ord idx)) (iv i))
        let SOut := Finset.univ.filter (fun idx : Fin k => D (iv i) (kv (ord idx)))
        have hIn_ne : SIn.Nonempty := by obtain ⟨x, hx⟩ := hIn; exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
        have hOut_ne : SOut.Nonempty := by obtain ⟨x, hx⟩ := hOut; exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
        let a := SIn.max' hIn_ne
        let b := SOut.min' hOut_ne
        have ha_in : D (kv (ord a)) (iv i) := (Finset.mem_filter.mp (Finset.max'_mem SIn hIn_ne)).2
        have hb_out : D (iv i) (kv (ord b)) := (Finset.mem_filter.mp (Finset.min'_mem SOut hOut_ne)).2
        have hab : a.val < b.val := by
          by_contra hge
          rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
          · have hab_eq : a = b := Fin.ext heq.symm
            rw [hab_eq] at ha_in; exact hD_asym _ _ ha_in hb_out
          · exact hNo_out_before_in i b a hgt hb_out ha_in
        have hall_in : ∀ idx : Fin k, idx.val ≤ a.val → D (kv (ord idx)) (iv i) := by
          intro idx hle
          rcases eq_or_lt_of_le hle with heq | hlt
          · have : idx = a := Fin.ext heq; rw [this]; exact ha_in
          · exact hIn_prefix i idx a b hlt hab ha_in hb_out
        have hall_out : ∀ idx : Fin k, b.val ≤ idx.val → D (iv i) (kv (ord idx)) := by
          intro idx hge
          rcases eq_or_lt_of_le hge with heq | hlt
          · have : idx = b := Fin.ext heq.symm; rw [this]; exact hb_out
          · exact hOut_suffix i a b idx hab hlt ha_in hb_out
        have hmem_iff : ∀ idx : Fin k, (mkSplitGraph e k cols).Adj (iv i) (kv (ord idx)) ↔
            idx.val ≤ a.val ∨ b.val ≤ idx.val := by
          intro idx
          constructor
          · intro hadj
            rcases hD_cov _ _ hadj with hout | hin
            · right; exact Finset.min'_le SOut idx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout⟩)
            · left; exact Finset.le_max' SIn idx (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩)
          · rintro (hle | hge)
            · exact (hD_adj _ _ (hall_in idx hle)).symm
            · exact hD_adj _ _ (hall_out idx hge)
        have hgap : a.val + 1 < b.val := by
          by_contra hle
          obtain ⟨j0, hj0⟩ := hno_full i
          let idx0 : Fin k := rkEquiv j0
          have hord0 : ord idx0 = j0 := rkEquiv.symm_apply_apply j0
          have hadj0 : (mkSplitGraph e k cols).Adj (iv i) (kv (ord idx0)) :=
            (hmem_iff idx0).mpr (by omega)
          have hbit0 := (hadj_bit i idx0).mp hadj0
          rw [hp_getD idx0.val idx0.isLt, hord0] at hbit0
          exact hj0 hbit0
        have ha_mem : a.val ∈ posOf i := (hpos_mem i a).mpr ((hmem_iff a).mpr (Or.inl le_rfl))
        have hb_mem : b.val ∈ posOf i := (hpos_mem i b).mpr ((hmem_iff b).mpr (Or.inr le_rfl))
        have hg_notmem : a.val + 1 ∉ posOf i := by
          intro h
          have h1 := (hmem_iff ⟨a.val + 1, by omega⟩).mp ((hpos_mem i ⟨a.val + 1, by omega⟩).mp h)
          dsimp only at h1
          omega
        have hne_empty : (posOf i).isEmpty = false := by
          cases hpe : posOf i with
          | nil => rw [hpe] at ha_mem; simp at ha_mem
          | cons _ _ => rfl
        have hnot_contig : isContig (posOf i) = none :=
          isContig_none_of_gap ha_mem hb_mem (by omega) hgap hg_notmem
        have hgaps_eq : (List.range k).filter (fun idx => !(posOf i).contains idx) =
            (List.range ((b.val - 1) + 1 - (a.val + 1))).map (· + (a.val + 1)) := by
          refine filter_range_eq_interval k (a.val + 1) (b.val - 1) (by omega) (by omega) _ ?_
          intro idx hidx
          have hcf : (posOf i).contains idx = false ↔ idx ∉ posOf i := by
            rw [← Bool.not_eq_true, list_contains_iff_mem]
          simp only [Bool.not_eq_true', hcf]
          rw [show idx = (⟨idx, hidx⟩ : Fin k).val from rfl, hpos_mem i ⟨idx, hidx⟩, hmem_iff ⟨idx, hidx⟩]
          dsimp only
          omega
        have hc_eq : classifyIndep k (posOf i) = (2, a.val, b.val) := by
          unfold classifyIndep
          simp only [hne_empty, Bool.false_eq_true, ↓reduceIte, hnot_contig, hgaps_eq,
              isContig_range (a.val + 1) (b.val - 1) (by omega)]
          have hc1 : (0 < a.val + 1 && (b.val - 1) + 1 < k) = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
          simp only [hc1, ↓reduceIte]
          refine Prod.ext rfl (Prod.ext ?_ ?_)
          · change (a.val + 1) - 1 = a.val; omega
          · change (b.val - 1) + 1 = b.val; omega
        right; right
        rw [hc_eq]
        exact ⟨rfl, hab, b.isLt, hall_in, hall_out⟩
      · -- Type B: incoming only
        push Not at hOut
        let SIn := Finset.univ.filter (fun idx : Fin k => D (kv (ord idx)) (iv i))
        have hIn_ne : SIn.Nonempty := by obtain ⟨x, hx⟩ := hIn; exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
        let a := SIn.min' hIn_ne
        let b := SIn.max' hIn_ne
        have ha_in : D (kv (ord a)) (iv i) := (Finset.mem_filter.mp (Finset.min'_mem SIn hIn_ne)).2
        have hb_in : D (kv (ord b)) (iv i) := (Finset.mem_filter.mp (Finset.max'_mem SIn hIn_ne)).2
        have hab : a.val ≤ b.val := Finset.min'_le SIn b (Finset.max'_mem SIn hIn_ne)
        have hall_in : ∀ idx : Fin k, a.val ≤ idx.val ∧ idx.val ≤ b.val → D (kv (ord idx)) (iv i) := by
          intro idx ⟨h1, h2⟩
          rcases eq_or_lt_of_le h1 with heq1 | hlt1
          · have : idx = a := Fin.ext heq1.symm; rw [this]; exact ha_in
          · rcases eq_or_lt_of_le h2 with heq2 | hlt2
            · have : idx = b := Fin.ext heq2; rw [this]; exact hb_in
            · exact hIn_contig i a idx b hlt1 hlt2 ha_in hb_in
        have hpos_eq : posOf i = (List.range (b.val + 1 - a.val)).map (· + a.val) := by
          refine filter_range_eq_interval k a.val b.val hab b.isLt _ ?_
          intro idx hidx
          rw [beq_iff_eq, ← hadj_bit i ⟨idx, hidx⟩]
          constructor
          · intro hadj
            have hin : D (kv (ord ⟨idx, hidx⟩)) (iv i) := (hD_cov _ _ hadj).resolve_left (hOut _)
            have hmem : (⟨idx, hidx⟩ : Fin k) ∈ SIn := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hin⟩
            exact ⟨Finset.min'_le SIn _ hmem, Finset.le_max' SIn _ hmem⟩
          · intro hr; exact (hD_adj _ _ (hall_in ⟨idx, hidx⟩ hr)).symm
        have hne_empty : (posOf i).isEmpty = false := by
          rw [hpos_eq]; cases h : b.val + 1 - a.val with
          | zero => omega
          | succ m => rw [List.range_succ_eq_map]; simp
        have hc_eq : classifyIndep k (posOf i) = (1, a.val, b.val) := by
          unfold classifyIndep
          rw [hne_empty]
          simp only [Bool.false_eq_true, ↓reduceIte, hpos_eq, isContig_range a.val b.val hab]
        right; left
        rw [hc_eq]
        exact ⟨rfl, hab, b.isLt, Or.inr hall_in⟩
    · push Not at hIn
      by_cases hOut : ∃ idx : Fin k, D (iv i) (kv (ord idx))
      · -- Type A: outgoing only
        let SOut := Finset.univ.filter (fun idx : Fin k => D (iv i) (kv (ord idx)))
        have hOut_ne : SOut.Nonempty := by obtain ⟨x, hx⟩ := hOut; exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
        let a := SOut.min' hOut_ne
        let b := SOut.max' hOut_ne
        have ha_out : D (iv i) (kv (ord a)) := (Finset.mem_filter.mp (Finset.min'_mem SOut hOut_ne)).2
        have hb_out : D (iv i) (kv (ord b)) := (Finset.mem_filter.mp (Finset.max'_mem SOut hOut_ne)).2
        have hab : a.val ≤ b.val := Finset.min'_le SOut b (Finset.max'_mem SOut hOut_ne)
        have hall_out : ∀ idx : Fin k, a.val ≤ idx.val ∧ idx.val ≤ b.val → D (iv i) (kv (ord idx)) := by
          intro idx ⟨h1, h2⟩
          rcases eq_or_lt_of_le h1 with heq1 | hlt1
          · have : idx = a := Fin.ext heq1.symm; rw [this]; exact ha_out
          · rcases eq_or_lt_of_le h2 with heq2 | hlt2
            · have : idx = b := Fin.ext heq2; rw [this]; exact hb_out
            · exact hOut_contig i a idx b hlt1 hlt2 ha_out hb_out
        have hpos_eq : posOf i = (List.range (b.val + 1 - a.val)).map (· + a.val) := by
          refine filter_range_eq_interval k a.val b.val hab b.isLt _ ?_
          intro idx hidx
          rw [beq_iff_eq, ← hadj_bit i ⟨idx, hidx⟩]
          constructor
          · intro hadj
            have hout : D (iv i) (kv (ord ⟨idx, hidx⟩)) := (hD_cov _ _ hadj).resolve_right (hIn _)
            have hmem : (⟨idx, hidx⟩ : Fin k) ∈ SOut := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout⟩
            exact ⟨Finset.min'_le SOut _ hmem, Finset.le_max' SOut _ hmem⟩
          · intro hr; exact hD_adj _ _ (hall_out ⟨idx, hidx⟩ hr)
        have hne_empty : (posOf i).isEmpty = false := by
          rw [hpos_eq]; cases h : b.val + 1 - a.val with
          | zero => omega
          | succ m => rw [List.range_succ_eq_map]; simp
        have hc_eq : classifyIndep k (posOf i) = (1, a.val, b.val) := by
          unfold classifyIndep
          rw [hne_empty]
          simp only [Bool.false_eq_true, ↓reduceIte, hpos_eq, isContig_range a.val b.val hab]
        right; left
        rw [hc_eq]
        exact ⟨rfl, hab, b.isLt, Or.inl hall_out⟩
      · -- Empty
        push Not at hOut
        have hpos_empty : posOf i = [] := by
          rw [List.eq_nil_iff_forall_not_mem]
          intro idx hmem
          have hlt : idx < k := (List.mem_range.mp (List.mem_filter.mp hmem).1)
          have hadj := (hpos_mem i ⟨idx, hlt⟩).mp hmem
          rcases hD_cov _ _ hadj with h1 | h2
          · exact hOut _ h1
          · exact hIn _ h2
        left
        simp [classifyIndep, hpos_empty]
  -- Now verify `kpValid e cols p = true`
  unfold kpValid
  rw [hp_len]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map, List.mem_range, bne_iff_ne, ne_eq]
  have hgetD_types : ∀ (i : Fin e),
      ((List.range e).map (fun r => classifyIndep k ((List.range k).filter fun idx =>
        ((cols.getD (p.getD idx 0) 0) >>> r) % 2 == 1))).getD i.val (3, 0, 0) =
      classifyIndep k (posOf i) := by
    intro i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
    simp [posOf]
  constructor
  · rintro _ ⟨i, hi, rfl⟩
    rcases hclass ⟨i, hi⟩ with h0 | ⟨h1, _⟩ | ⟨h2, _⟩ <;> dsimp only [posOf] at * <;> omega
  · intro i hi
    rw [hgetD_types ⟨i, hi⟩]
    by_cases hc2 : (classifyIndep k (posOf ⟨i, hi⟩)).1 = 2
    · simp only [hc2, beq_self_eq_true, ↓reduceIte, List.all_eq_true, List.mem_range]
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · simp only [beq_false_of_ne hij, Bool.false_eq_true, ↓reduceIte, hgetD_types ⟨j, hj⟩]
        rcases hclass ⟨i, hi⟩ with h0 | ⟨h1, _⟩ | ⟨_, hab2, hb2k, hin2, hout2⟩
        · omega
        · omega
        · set a2 := (classifyIndep k (posOf ⟨i, hi⟩)).2.1
          set b2 := (classifyIndep k (posOf ⟨i, hi⟩)).2.2
          have ha2_in : D (kv (ord ⟨a2, by omega⟩)) (iv ⟨i, hi⟩) := hin2 ⟨a2, by omega⟩ le_rfl
          have hb2_out : D (iv ⟨i, hi⟩) (kv (ord ⟨b2, hb2k⟩)) := hout2 ⟨b2, hb2k⟩ le_rfl
          have hforb_out : D (iv ⟨j, hj⟩) (kv (ord ⟨a2, by omega⟩)) →
              D (iv ⟨j, hj⟩) (kv (ord ⟨b2, hb2k⟩)) → False := by
            intro hja hjb
            have hDji := hD_short [iv ⟨j, hj⟩, kv (ord ⟨a2, by omega⟩), iv ⟨i, hi⟩, kv (ord ⟨b2, hb2k⟩)]
              (by simp) (by intro idx hidx; simp only [List.length_cons, List.length_nil] at hidx
                            have hlt3 : idx < 3 := by omega
                            interval_cases idx; exacts [hja, ha2_in, hb2_out])
              hjb 0 2 (by decide) (by simp)
            exact hE_indep ⟨j, hj⟩ ⟨i, hi⟩ (hD_adj _ _ hDji)
          have hforb_in : D (kv (ord ⟨a2, by omega⟩)) (iv ⟨j, hj⟩) →
              D (kv (ord ⟨b2, hb2k⟩)) (iv ⟨j, hj⟩) → False := by
            intro hja hjb
            have hDij := hD_short [kv (ord ⟨a2, by omega⟩), iv ⟨i, hi⟩, kv (ord ⟨b2, hb2k⟩), iv ⟨j, hj⟩]
              (by simp) (by intro idx hidx; simp only [List.length_cons, List.length_nil] at hidx
                            have hlt3 : idx < 3 := by omega
                            interval_cases idx; exacts [ha2_in, hb2_out, hjb])
              hja 1 3 (by decide) (by simp)
            exact hE_indep ⟨i, hi⟩ ⟨j, hj⟩ (hD_adj _ _ hDij)
          have ha2_lt_b2 : a2 < b2 := hab2
          rcases hclass ⟨j, hj⟩ with hj0 | ⟨hj1, hjab, hjbk, hAB⟩ | ⟨hj2, hjab, hjbk, hjin, hjout⟩
          · simp [hj0]
          · simp only [hj1, beq_self_eq_true, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq]
            by_contra hnot
            push Not at hnot
            rcases hAB with hA | hB
            · exact hforb_out (hA ⟨a2, by omega⟩ ⟨hnot.1, by dsimp only; omega⟩) (hA ⟨b2, hb2k⟩ ⟨by dsimp only; omega, hnot.2⟩)
            · exact hforb_in (hB ⟨a2, by omega⟩ ⟨hnot.1, by dsimp only; omega⟩) (hB ⟨b2, hb2k⟩ ⟨by dsimp only; omega, hnot.2⟩)
          · simp only [hj2, show (2 == 1) = false from rfl, beq_self_eq_true, Bool.false_eq_true,
              ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · by_contra hle; push Not at hle
              exact hforb_out (hjout ⟨a2, by omega⟩ hle) (hjout ⟨b2, hb2k⟩ (by dsimp only; omega))
            · by_contra hle; push Not at hle
              exact hforb_in (hjin ⟨a2, by omega⟩ (by dsimp only; omega)) (hjin ⟨b2, hb2k⟩ hle)
    · simp [beq_false_of_ne hc2]

private lemma not_st_T1 : ¬ IsSemiTransitive graphT1 := fun h => by
  have h1 := semiTransitive_mkSplitGraph_imp_kp 3 4 [5, 3, 6, 0] (by decide) h
  revert h1; decide

private lemma not_st_T2 : ¬ IsSemiTransitive graphT2 := fun h => by
  have h1 := semiTransitive_mkSplitGraph_imp_kp 3 4 [7, 1, 2, 4] (by decide) h
  revert h1; decide

private lemma not_st_T3 : ¬ IsSemiTransitive graphT3 := fun h => by
  have h1 := semiTransitive_mkSplitGraph_imp_kp 3 4 [5, 3, 7, 6] (by decide) h
  revert h1; decide

private lemma not_st_T4 : ¬ IsSemiTransitive graphT4 := fun h => by
  have h1 := semiTransitive_mkSplitGraph_imp_kp 4 4 [9, 3, 15, 6] (by decide) h
  revert h1; decide

private lemma not_st_T5 : ¬ IsSemiTransitive graphT5 := fun h => by
  have h1 := semiTransitive_mkSplitGraph_imp_kp 4 5 [9, 3, 6, 12, 0] (by decide) h
  revert h1; decide

private lemma not_st_T6 : ¬ IsSemiTransitive graphT6 := fun h => by
  have h1 := semiTransitive_mkSplitGraph_imp_kp 4 5 [1, 11, 7, 4, 8] (by decide) h
  revert h1; decide

private lemma not_st_T7 : ¬ IsSemiTransitive graphT7 := fun h => by
  have h1 := semiTransitive_mkSplitGraph_imp_kp 4 5 [9, 3, 5, 10, 12] (by decide) h
  revert h1; decide

private lemma not_st_T8 : ¬ IsSemiTransitive graphT8 := fun h => by
  have h1 := semiTransitive_mkSplitGraph_imp_kp 4 5 [11, 7, 9, 5, 2] (by decide) h
  revert h1; decide

private lemma semiTransitive_mkSplitGraph_imp_kp_exists (e k : ℕ) (cols : List ℕ)
    (hno_full : ∀ i : Fin e, ∃ j : Fin k, ((cols.getD j.val 0) >>> i.val) % 2 ≠ 1)
    (hST : IsSemiTransitive (mkSplitGraph e k cols)) :
    ∃ p : List ℕ, p.Perm (List.range k) ∧ kpValid e cols p = true := by
  have h := semiTransitive_mkSplitGraph_imp_kp e k cols hno_full hST
  rw [List.any_eq_true] at h
  obtain ⟨p, hp_mem, hp_ok⟩ := h
  have hperm_all : ∀ l q, q ∈ allPerms l → q.Perm l := by
    intro l
    induction l with
    | nil => intro q hq; simp [allPerms] at hq; subst hq; exact List.Perm.refl []
    | cons x xs ih =>
      intro q hq
      rw [allPerms, List.mem_flatMap] at hq
      obtain ⟨r, hr_mem, hq_ins⟩ := hq
      have hrp := ih r hr_mem
      have hins : ∀ (ys zs : List ℕ), zs ∈ insertEverywhere x ys → zs.Perm (x :: ys) := by
        intro ys
        induction ys with
        | nil => intro zs hzs; simp [insertEverywhere] at hzs; subst hzs; exact List.Perm.refl _
        | cons y ys' ihy =>
          intro zs hzs
          simp only [insertEverywhere, List.mem_cons, List.mem_map] at hzs
          rcases hzs with rfl | ⟨w, hw, rfl⟩
          · exact List.Perm.refl _
          · exact ((ihy w hw).cons y).trans (List.Perm.swap x y ys')
      exact (hins r q hq_ins).trans (hrp.cons x)
  exact ⟨p, hperm_all _ _ hp_mem, hp_ok⟩

private lemma not_kp_D1_split :
    (List.range 6).all (fun a => (allPerms ((List.range 6).erase a)).all
      (fun rest => !kpValid 4 [3, 2, 5, 4, 9, 8] (a :: rest))) = true := by
  decide

private lemma not_st_D1 : ¬ IsSemiTransitive graphD1 := by
  intro h
  obtain ⟨p, hp_perm, hp_ok⟩ := semiTransitive_mkSplitGraph_imp_kp_exists 4 6 [3, 2, 5, 4, 9, 8] (by decide) h
  cases p with
  | nil => exact absurd hp_perm.length_eq (by decide)
  | cons a rest =>
    have ha_mem : a ∈ List.range 6 := hp_perm.mem_iff.mp (List.mem_cons_self ..)
    have hrest_perm : rest.Perm ((List.range 6).erase a) := by
      have h1 : (List.range 6).Perm (a :: (List.range 6).erase a) := List.perm_cons_erase ha_mem
      exact (List.perm_cons a).mp (hp_perm.trans h1)
    have hrest_in : rest ∈ allPerms ((List.range 6).erase a) := perm_mem_allPerms _ _ hrest_perm
    have hbad := List.all_eq_true.mp (List.all_eq_true.mp not_kp_D1_split a ha_mem) rest hrest_in
    simp [hp_ok] at hbad

/-! ### 3. Forbidden-free implies word-representable via 976-leaf certificate & 22 words -/

private def s4Perms : List (List ℕ) :=
  [[0, 1, 2, 3],
  [0, 1, 3, 2],
  [0, 2, 1, 3],
  [0, 2, 3, 1],
  [0, 3, 1, 2],
  [0, 3, 2, 1],
  [1, 0, 2, 3],
  [1, 0, 3, 2],
  [1, 2, 0, 3],
  [1, 2, 3, 0],
  [1, 3, 0, 2],
  [1, 3, 2, 0],
  [2, 0, 1, 3],
  [2, 0, 3, 1],
  [2, 1, 0, 3],
  [2, 1, 3, 0],
  [2, 3, 0, 1],
  [2, 3, 1, 0],
  [3, 0, 1, 2],
  [3, 0, 2, 1],
  [3, 1, 0, 2],
  [3, 1, 2, 0],
  [3, 2, 0, 1],
  [3, 2, 1, 0]]

private def permCol (pi c : ℕ) : ℕ :=
  let p := s4Perms.getD pi [0, 1, 2, 3]
  ((if (c >>> 0) % 2 == 1 then 1 <<< (p.getD 0 0) else 0) +
   (if (c >>> 1) % 2 == 1 then 1 <<< (p.getD 1 0) else 0) +
   (if (c >>> 2) % 2 == 1 then 1 <<< (p.getD 2 0) else 0) +
   (if (c >>> 3) % 2 == 1 then 1 <<< (p.getD 3 0) else 0))

private def permMask (pi M : ℕ) : ℕ :=
  (List.range 16).foldl (fun acc c => if (M >>> c) % 2 == 1 then acc ||| (1 <<< permCol pi c) else acc) 0

private def orbitCols : List (List ℕ) :=
  [[1, 9, 8, 0, 4, 6, 2, 3],
  [0, 2, 3, 7, 5, 1, 9, 8],
  [0, 2, 6, 7, 3, 1, 9, 8],
  [1, 9, 8, 0, 4, 6, 7, 3],
  [1, 5, 4, 6, 2, 10, 8, 9],
  [1, 5, 7, 3, 2, 10, 8, 9],
  [1, 5, 7, 6, 2, 10, 8, 9],
  [0, 1, 9, 11, 3, 7, 5, 4],
  [0, 1, 9, 11, 3, 7, 6, 2],
  [0, 1, 9, 11, 3, 7, 6, 4],
  [0, 4, 5, 7, 3, 11, 9, 8],
  [0, 4, 6, 7, 3, 11, 9, 8],
  [3, 7, 5, 4, 12, 8, 9, 11],
  [3, 7, 6, 4, 12, 8, 9, 11],
  [0, 1, 5, 7, 15, 11, 3, 2],
  [0, 1, 3, 11, 15, 7, 5, 4],
  [0, 2, 3, 11, 15, 7, 5, 4],
  [0, 1, 9, 11, 15, 7, 5, 4],
  [0, 1, 9, 11, 15, 7, 6, 2],
  [0, 1, 9, 11, 15, 7, 6, 4],
  [0, 4, 5, 7, 15, 11, 9, 8],
  [0, 4, 6, 7, 15, 11, 9, 8]]

private def orbitWords : List (List ℕ) :=
  [[1, 4, 3, 5, 6, 3, 7, 2, 8, 9, 2, 10, 0, 11, 4, 5, 0, 6, 3, 7, 8, 1, 9, 2, 10, 11],
  [3, 4, 1, 5, 0, 6, 2, 7, 8, 2, 9, 10, 0, 11, 4, 1, 5, 6, 7, 1, 8, 2, 9, 3, 10, 0, 11],
  [3, 4, 1, 5, 2, 6, 0, 7, 8, 9, 10, 0, 11, 4, 1, 5, 2, 6, 7, 2, 8, 1, 9, 3, 10, 0, 11],
  [1, 4, 3, 5, 6, 3, 7, 2, 8, 9, 0, 10, 11, 4, 5, 0, 6, 3, 7, 2, 8, 1, 9, 10, 2, 11],
  [3, 4, 2, 5, 6, 1, 7, 8, 9, 1, 10, 0, 11, 4, 2, 5, 6, 7, 2, 8, 3, 9, 1, 10, 0, 11, 4, 5, 0, 6, 7, 2, 8, 3, 9, 1, 10, 11],
  [3, 4, 2, 5, 1, 6, 7, 8, 9, 1, 10, 0, 11, 4, 2, 5, 6, 2, 7, 0, 8, 3, 9, 1, 10, 11],
  [3, 4, 2, 5, 1, 6, 7, 8, 9, 1, 10, 0, 11, 4, 2, 5, 6, 7, 2, 8, 3, 9, 1, 10, 0, 11, 4, 5, 6, 0, 7, 2, 8, 3, 9, 1, 10, 11],
  [2, 4, 0, 5, 3, 6, 1, 7, 8, 9, 1, 10, 0, 11, 4, 5, 3, 6, 7, 3, 8, 2, 9, 1, 10, 0, 11],
  [4, 0, 5, 3, 6, 1, 7, 8, 2, 9, 10, 2, 11, 1, 4, 0, 5, 3, 6, 7, 3, 8, 9, 0, 10, 2, 11, 1],
  [2, 4, 0, 5, 3, 6, 1, 7, 8, 9, 10, 1, 11, 4, 0, 5, 3, 6, 7, 3, 8, 2, 9, 0, 10, 1, 11],
  [3, 4, 2, 5, 0, 6, 1, 7, 8, 9, 1, 10, 0, 11, 4, 2, 5, 6, 7, 2, 8, 3, 9, 1, 10, 0, 11],
  [3, 4, 2, 5, 1, 6, 0, 7, 8, 9, 10, 0, 11, 4, 2, 5, 1, 6, 7, 8, 3, 9, 1, 10, 0, 11, 4, 2, 5, 6, 7, 2, 8, 3, 9, 1, 10, 0, 11],
  [3, 4, 2, 5, 6, 7, 8, 2, 9, 0, 10, 1, 11, 4, 5, 1, 6, 0, 7, 3, 8, 2, 9, 10, 11],
  [3, 4, 2, 5, 6, 7, 8, 2, 9, 0, 10, 1, 11, 4, 5, 6, 1, 7, 3, 8, 2, 9, 0, 10, 11, 4, 5, 0, 6, 1, 7, 3, 8, 2, 9, 10, 11],
  [1, 4, 0, 5, 2, 6, 7, 3, 8, 9, 3, 10, 0, 11, 4, 5, 2, 6, 1, 7, 8, 2, 9, 3, 10, 0, 11],
  [2, 4, 0, 5, 1, 6, 3, 7, 8, 3, 9, 1, 10, 0, 11, 4, 5, 6, 7, 2, 8, 3, 9, 1, 10, 0, 11],
  [2, 4, 1, 5, 0, 6, 3, 7, 8, 3, 9, 10, 0, 11, 4, 1, 5, 6, 7, 2, 8, 3, 9, 1, 10, 0, 11],
  [2, 4, 0, 5, 3, 6, 1, 7, 8, 9, 1, 10, 0, 11, 4, 5, 3, 6, 7, 2, 8, 3, 9, 1, 10, 0, 11],
  [4, 0, 5, 3, 6, 1, 7, 2, 8, 9, 10, 2, 11, 1, 4, 0, 5, 3, 6, 7, 8, 3, 9, 0, 10, 2, 11, 1],
  [2, 4, 0, 5, 3, 6, 1, 7, 8, 9, 10, 1, 11, 4, 0, 5, 3, 6, 7, 2, 8, 3, 9, 0, 10, 1, 11],
  [3, 4, 2, 5, 0, 6, 1, 7, 8, 9, 1, 10, 0, 11, 4, 2, 5, 6, 7, 3, 8, 2, 9, 1, 10, 0, 11],
  [3, 4, 2, 5, 1, 6, 0, 7, 8, 9, 10, 0, 11, 4, 2, 5, 1, 6, 7, 3, 8, 9, 1, 10, 0, 11, 4, 2, 5, 6, 7, 3, 8, 2, 9, 1, 10, 0, 11]]

private def orbitMask (oidx : ℕ) : ℕ :=
  (orbitCols.getD oidx []).foldl (fun acc c => acc ||| (1 <<< c)) 0

private def forbCols : List (ℕ × List ℕ) :=
  [(3, [5, 3, 6, 0]), (3, [7, 1, 2, 4]), (3, [5, 3, 7, 6]),
   (4, [9, 3, 15, 6]), (4, [9, 3, 6, 12, 0]), (4, [1, 11, 7, 4, 8]),
   (4, [9, 3, 5, 10, 12]), (4, [11, 7, 9, 5, 2]), (4, [3, 2, 5, 4, 9, 8]),
   (4, [7, 11, 13])]

private def forbSat (mOn kind pi : ℕ) : Bool :=
  let (ne, cols) := forbCols.getD kind (4, [])
  let p := s4Perms.getD pi [0, 1, 2, 3]
  if ne == 3 then
    let miss := 1 <<< (p.getD 3 0)
    cols.all fun c =>
      let cm :=
        (if (c >>> 0) % 2 == 1 then 1 <<< (p.getD 0 0) else 0) +
        (if (c >>> 1) % 2 == 1 then 1 <<< (p.getD 1 0) else 0) +
        (if (c >>> 2) % 2 == 1 then 1 <<< (p.getD 2 0) else 0)
      ((mOn >>> cm) % 2 == 1) || ((mOn >>> (cm ||| miss)) % 2 == 1)
  else
    cols.all fun c => (mOn >>> permCol pi c) % 2 == 1

private inductive BitTree
  | F (kind pi : ℕ)
  | C (oidx pi : ℕ)
  | B (bit : ℕ) (onTree offTree : BitTree)

private def checkTree (mOn mOff : ℕ) : BitTree → Bool
  | .F kind pi => kind < 10 && pi < 24 && forbSat mOn kind pi
  | .C oidx pi =>
    oidx < 22 && pi < 24 &&
    ((65535 ^^^ mOff) &&& (65535 ^^^ permMask pi (orbitMask oidx))) == 0
  | .B bit t1 t0 =>
    bit < 16 &&
    checkTree (mOn ||| (1 <<< bit)) mOff t1 &&
    checkTree mOn (mOff ||| (1 <<< bit)) t0

private def treeNode_0 : BitTree := .B 14 (.B 8 (.F 0 0) (.B 9 (.F 1 9) (.B 7 (.F 2 0) (.B 0 (.F 0 0) (.B 11 (.B 13 (.F 2 1) (.B 2 (.F 0 3) (.B 6 (.B 12 (.F 1 1) (.C 12 10)) (.C 13 11)))) (.B 13 (.B 4 (.F 0 1) (.B 6 (.B 10 (.F 1 3) (.C 12 16)) (.C 13 17))) (.B 6 (.B 10 (.B 12 (.F 2 9) (.C 5 9)) (.C 5 15)) (.C 6 9)))))))) (.B 6 (.B 8 (.F 0 0) (.B 0 (.F 0 0) (.B 7 (.F 2 0) (.B 10 (.B 12 (.F 6 7) (.B 13 (.F 1 3) (.B 9 (.F 6 3) (.C 5 7)))) (.B 12 (.B 11 (.F 1 1) (.B 9 (.F 6 1) (.C 5 13))) (.B 1 (.B 11 (.B 13 (.F 0 9) (.C 5 1)) (.C 5 3)) (.C 12 4))))))) (.B 11 (.B 13 (.B 8 (.F 7 4) (.B 10 (.F 2 1) (.B 12 (.F 2 3) (.B 7 (.F 9 0) (.B 1 (.B 2 (.B 4 (.F 5 4) (.C 7 4)) (.C 7 5)) (.C 10 4)))))) (.B 2 (.B 12 (.F 0 3) (.B 8 (.F 1 1) (.B 9 (.B 7 (.F 7 0) (.B 10 (.F 2 1) (.C 1 1))) (.B 1 (.B 4 (.B 7 (.F 1 0) (.C 2 1)) (.C 8 1)) (.C 9 6))))) (.B 10 (.B 9 (.F 2 1) (.B 12 (.B 0 (.F 0 3) (.B 1 (.B 7 (.F 0 9) (.C 6 4)) (.C 13 1))) (.B 1 (.B 4 (.B 7 (.F 1 0) (.C 3 1)) (.C 9 1)) (.C 11 1)))) (.B 0 (.B 12 (.F 0 3) (.B 1 (.B 4 (.B 7 (.B 8 (.F 5 0) (.C 7 0)) (.C 1 4)) (.C 7 1)) (.C 10 0))) (.B 1 (.B 7 (.B 12 (.F 0 9) (.B 4 (.B 8 (.F 5 0) (.C 7 0)) (.C 7 1))) (.C 5 4)) (.C 12 0)))))) (.B 9 (.B 12 (.B 10 (.F 6 0) (.B 2 (.F 0 3) (.B 13 (.F 2 3) (.B 0 (.F 0 3) (.C 5 2))))) (.B 4 (.B 10 (.F 0 1) (.B 2 (.B 7 (.F 1 0) (.B 8 (.F 8 0) (.C 1 3))) (.B 13 (.B 7 (.F 7 2) (.B 8 (.F 1 3) (.C 1 3))) (.C 1 2)))) (.B 0 (.B 10 (.F 0 1) (.B 1 (.B 2 (.B 7 (.B 8 (.B 13 (.F 5 2) (.C 1 0)) (.C 7 2)) (.C 1 5)) (.C 7 3)) (.C 10 2))) (.B 1 (.B 7 (.B 13 (.B 10 (.F 0 9) (.B 2 (.B 8 (.F 5 2) (.C 7 2)) (.C 7 3))) (.C 5 0)) (.C 5 5)) (.C 12 2))))) (.B 10 (.B 13 (.B 4 (.F 0 1) (.B 0 (.F 0 1) (.B 1 (.B 7 (.F 0 9) (.C 6 5)) (.C 13 3)))) (.B 12 (.B 0 (.F 4 1) (.B 1 (.B 7 (.F 0 9) (.C 4 4)) (.C 6 8))) (.B 1 (.B 4 (.B 7 (.F 1 0) (.C 0 1)) (.C 2 6)) (.C 3 6)))) (.B 2 (.B 4 (.B 7 (.B 1 (.F 1 0) (.B 8 (.B 13 (.F 1 3) (.C 3 12)) (.C 9 12))) (.B 8 (.B 13 (.F 1 3) (.C 0 3)) (.C 2 3))) (.B 1 (.B 7 (.B 12 (.F 1 0) (.B 8 (.B 13 (.F 5 2) (.C 1 0)) (.C 7 2))) (.C 3 3)) (.C 11 3))) (.B 4 (.B 8 (.B 13 (.F 1 3) (.C 2 12)) (.C 8 3)) (.C 9 3)))))))
private def treeNode_1 : BitTree := .B 14 (.B 7 (.F 2 0) (.B 11 (.F 2 1) (.B 15 (.F 2 0) (.B 0 (.F 0 0) (.B 4 (.F 0 1) (.B 8 (.F 0 0) (.B 6 (.B 10 (.F 1 3) (.C 13 16)) (.C 12 22)))))))) (.B 6 (.B 8 (.F 0 0) (.B 10 (.F 1 3) (.B 15 (.F 2 0) (.B 7 (.F 2 0) (.B 0 (.F 0 0) (.B 1 (.B 11 (.F 0 9) (.C 6 3)) (.C 13 5))))))) (.B 10 (.B 4 (.F 0 1) (.B 15 (.F 2 1) (.B 11 (.F 2 1) (.B 0 (.F 0 1) (.B 7 (.B 1 (.F 0 9) (.B 9 (.B 12 (.F 1 0) (.C 12 2)) (.C 13 3))) (.C 5 19)))))) (.B 7 (.B 11 (.F 9 0) (.B 9 (.B 4 (.F 7 2) (.B 12 (.F 2 3) (.B 1 (.B 2 (.B 8 (.F 5 2) (.C 17 2)) (.C 17 3)) (.C 20 2)))) (.B 8 (.B 4 (.F 1 3) (.B 1 (.B 2 (.F 5 2) (.C 19 3)) (.C 21 3))) (.B 1 (.B 2 (.B 12 (.F 1 0) (.B 4 (.F 1 0) (.C 15 2))) (.C 18 3)) (.C 19 12))))) (.B 4 (.B 8 (.F 1 3) (.B 15 (.B 9 (.F 1 9) (.B 1 (.B 2 (.F 1 0) (.C 19 5)) (.C 21 5))) (.B 1 (.B 2 (.B 11 (.F 5 4) (.C 3 5)) (.C 9 5)) (.C 11 5)))) (.B 12 (.B 15 (.B 9 (.F 3 5) (.B 1 (.B 2 (.F 1 0) (.C 18 5)) (.C 19 18))) (.B 1 (.B 2 (.B 11 (.F 1 1) (.C 2 5)) (.C 8 5)) (.C 9 18))) (.B 1 (.B 2 (.B 8 (.B 11 (.F 1 1) (.B 15 (.F 1 1) (.C 1 5))) (.C 15 4)) (.C 14 4)) (.C 16 4)))))))
private def treeNode_2 : BitTree := .B 9 (.B 15 (.B 12 (.F 3 5) (.B 10 (.F 2 1) (.B 4 (.F 1 9) (.B 14 (.F 2 1) (.B 6 (.F 3 0) (.B 1 (.B 2 (.B 8 (.F 1 1) (.C 14 1)) (.C 15 1)) (.C 16 1))))))) (.B 14 (.B 4 (.F 0 1) (.B 11 (.F 2 1) (.B 0 (.F 0 1) (.B 7 (.B 2 (.F 0 3) (.B 10 (.B 12 (.F 1 0) (.C 12 8)) (.C 13 9))) (.B 6 (.B 10 (.B 12 (.F 2 9) (.C 5 11)) (.C 6 11)) (.C 5 21)))))) (.B 10 (.B 4 (.F 0 1) (.B 0 (.F 0 1) (.B 11 (.F 2 1) (.B 12 (.B 7 (.F 1 0) (.B 6 (.F 6 6) (.C 5 19))) (.C 5 6))))) (.B 7 (.B 12 (.B 2 (.F 0 3) (.B 0 (.F 0 3) (.B 1 (.B 11 (.F 0 9) (.C 6 2)) (.C 13 0)))) (.B 2 (.B 4 (.F 1 0) (.B 1 (.B 8 (.B 11 (.F 1 1) (.C 2 0)) (.C 8 0)) (.C 9 7))) (.B 1 (.B 8 (.B 11 (.B 4 (.F 5 0) (.B 6 (.F 1 1) (.C 7 1))) (.C 3 0)) (.C 9 0)) (.C 11 0)))) (.B 6 (.B 12 (.B 0 (.F 4 0) (.B 1 (.B 11 (.F 0 9) (.C 4 2)) (.C 6 10))) (.B 1 (.B 8 (.B 11 (.F 1 1) (.C 0 0)) (.C 2 7)) (.C 3 7))) (.B 1 (.B 2 (.B 8 (.B 11 (.F 1 1) (.C 0 5)) (.B 11 (.B 12 (.F 1 1) (.C 1 1)) (.C 0 5))) (.C 2 18)) (.C 3 18))))))) (.B 7 (.B 11 (.B 14 (.F 9 6) (.B 12 (.B 15 (.F 2 3) (.B 0 (.F 0 3) (.B 1 (.F 0 9) (.B 2 (.F 0 3) (.C 12 6))))) (.B 4 (.B 8 (.B 15 (.F 1 3) (.B 1 (.F 5 0) (.B 2 (.F 5 6) (.C 10 6)))) (.B 10 (.B 1 (.F 1 0) (.B 15 (.F 1 3) (.C 7 6))) (.B 1 (.B 2 (.F 1 0) (.C 16 6)) (.C 15 6)))) (.B 6 (.B 1 (.B 8 (.F 1 1) (.B 10 (.F 7 6) (.C 14 6))) (.B 8 (.B 15 (.F 1 3) (.C 7 7)) (.B 10 (.B 15 (.F 1 3) (.C 7 6)) (.C 14 6)))) (.B 1 (.B 2 (.B 8 (.F 1 1) (.C 14 7)) (.C 16 7)) (.C 15 7)))))) (.B 10 (.B 12 (.B 15 (.F 2 9) (.B 1 (.F 0 9) (.B 14 (.F 2 9) (.B 0 (.F 0 9) (.C 5 8))))) (.B 4 (.B 14 (.F 7 8) (.B 15 (.F 1 3) (.B 1 (.F 1 0) (.C 1 8)))) (.B 6 (.B 15 (.F 1 3) (.B 1 (.B 2 (.B 8 (.B 14 (.F 5 8) (.C 1 6)) (.C 7 8)) (.C 10 8)) (.C 7 9))) (.B 1 (.B 2 (.B 8 (.B 14 (.F 5 8) (.B 15 (.F 1 1) (.C 1 6))) (.C 17 8)) (.C 20 8)) (.C 17 9))))) (.B 8 (.B 4 (.B 15 (.F 1 3) (.B 14 (.F 1 9) (.B 1 (.B 2 (.F 1 0) (.C 3 14)) (.C 2 14)))) (.B 6 (.B 15 (.F 1 3) (.B 1 (.B 2 (.B 12 (.F 1 0) (.B 14 (.F 5 8) (.C 1 6))) (.C 11 9)) (.C 9 9))) (.B 1 (.B 2 (.B 12 (.F 1 0) (.B 14 (.F 5 8) (.B 15 (.F 1 1) (.C 1 0)))) (.C 21 9)) (.C 19 9)))) (.B 12 (.B 1 (.B 2 (.F 1 0) (.B 6 (.B 15 (.F 1 1) (.C 9 14)) (.C 19 14))) (.B 6 (.B 15 (.F 3 9) (.C 8 9)) (.C 18 9))) (.B 1 (.B 2 (.B 4 (.F 1 0) (.C 15 8)) (.C 16 8)) (.C 14 8)))))) (.B 6 (.B 15 (.B 12 (.F 3 9) (.B 8 (.F 1 3) (.B 10 (.F 1 3) (.B 1 (.B 2 (.B 4 (.F 1 0) (.C 17 10)) (.C 20 10)) (.C 17 11))))) (.B 11 (.B 12 (.B 1 (.F 0 9) (.B 14 (.F 2 9) (.B 0 (.F 0 9) (.C 5 10)))) (.B 8 (.B 14 (.F 7 10) (.B 1 (.F 1 1) (.C 1 10))) (.B 1 (.B 2 (.B 4 (.B 14 (.F 5 10) (.C 1 7)) (.C 7 10)) (.C 10 10)) (.C 7 11)))) (.B 10 (.B 12 (.B 1 (.F 0 9) (.B 14 (.F 2 9) (.B 0 (.F 0 9) (.C 5 8)))) (.B 4 (.B 8 (.B 1 (.F 8 6) (.B 14 (.F 1 9) (.C 1 8))) (.C 1 9)) (.C 1 11))) (.B 4 (.B 8 (.B 14 (.F 1 9) (.C 0 9)) (.C 2 9)) (.C 3 9))))) (.B 4 (.B 15 (.B 8 (.F 1 3) (.B 10 (.F 1 3) (.B 1 (.B 2 (.F 1 0) (.C 21 11)) (.C 19 11)))) (.B 8 (.B 14 (.F 1 9) (.B 1 (.B 2 (.B 11 (.F 1 1) (.C 0 11)) (.C 3 20)) (.C 2 20))) (.B 1 (.B 2 (.B 11 (.B 12 (.F 1 1) (.B 14 (.F 5 10) (.C 1 7))) (.C 3 11)) (.C 11 11)) (.C 9 11)))) (.B 12 (.B 15 (.B 10 (.F 3 11) (.B 1 (.B 2 (.F 1 0) (.C 19 20)) (.C 18 11))) (.B 1 (.B 2 (.B 11 (.F 1 1) (.C 2 11)) (.C 9 20)) (.C 8 11))) (.B 1 (.B 2 (.B 8 (.B 11 (.F 1 1) (.B 15 (.F 1 1) (.C 1 11))) (.C 15 10)) (.C 16 10)) (.C 14 10))))))
private def treeNode_3 : BitTree := .B 13 (.F 9 0) (.B 14 (.F 9 6) (.B 12 (.B 15 (.F 2 3) (.B 0 (.F 0 3) (.B 1 (.F 0 9) (.B 2 (.F 0 3) (.B 5 (.B 6 (.F 1 1) (.B 9 (.B 10 (.F 1 0) (.C 12 0)) (.C 13 1))) (.B 9 (.B 10 (.F 1 0) (.C 13 0)) (.C 12 6))))))) (.B 5 (.B 6 (.F 2 0) (.B 9 (.B 2 (.F 7 0) (.B 10 (.F 2 1) (.B 1 (.B 4 (.B 8 (.F 5 0) (.C 17 0)) (.C 17 1)) (.C 20 0)))) (.B 8 (.B 2 (.F 1 1) (.B 1 (.B 4 (.F 5 0) (.C 19 1)) (.C 21 1))) (.B 1 (.B 4 (.B 10 (.F 1 0) (.B 2 (.F 1 0) (.C 15 0))) (.C 18 1)) (.C 19 6))))) (.B 10 (.B 9 (.F 2 1) (.B 1 (.B 4 (.F 1 0) (.B 6 (.F 7 6) (.B 2 (.B 8 (.F 1 1) (.C 14 7)) (.C 16 7)))) (.B 2 (.B 4 (.B 8 (.F 5 6) (.C 17 6)) (.C 17 7)) (.C 20 6)))) (.B 4 (.B 8 (.B 1 (.F 5 0) (.B 2 (.F 5 6) (.C 21 0))) (.B 2 (.B 9 (.F 1 0) (.B 1 (.F 1 0) (.C 15 6))) (.C 19 0))) (.B 1 (.B 6 (.B 8 (.F 1 1) (.C 18 0)) (.B 2 (.B 8 (.F 1 1) (.C 14 1)) (.C 15 1))) (.C 19 7)))))))
private def treeNode_4 : BitTree := .B 13 (.B 14 (.F 9 12) (.B 10 (.B 15 (.F 2 1) (.B 0 (.F 0 1) (.B 1 (.F 0 9) (.B 4 (.F 0 1) (.B 9 (.B 12 (.F 1 0) (.C 13 2)) (.C 12 12)))))) (.B 12 (.B 9 (.F 2 3) (.B 1 (.B 2 (.F 1 0) (.B 6 (.F 7 12) (.B 4 (.B 8 (.F 1 3) (.C 14 13)) (.C 16 13)))) (.B 2 (.B 4 (.B 8 (.F 5 12) (.B 5 (.B 15 (.F 1 1) (.C 7 12)) (.C 17 12))) (.B 5 (.B 15 (.F 1 1) (.C 10 12)) (.C 20 12))) (.B 5 (.B 6 (.B 15 (.F 1 1) (.C 7 13)) (.C 15 13)) (.C 17 13))))) (.B 2 (.B 8 (.B 1 (.F 5 2) (.B 4 (.F 5 12) (.B 5 (.B 15 (.F 1 1) (.C 11 2)) (.C 21 2)))) (.B 9 (.B 4 (.F 1 0) (.B 5 (.B 15 (.F 1 9) (.C 9 2)) (.C 19 2))) (.B 1 (.B 4 (.F 1 0) (.C 16 12)) (.C 15 12)))) (.B 6 (.B 1 (.B 8 (.F 1 3) (.B 5 (.B 9 (.B 15 (.F 3 2) (.C 8 2)) (.C 14 12)) (.C 18 2))) (.B 5 (.B 15 (.B 8 (.F 1 1) (.B 9 (.F 3 2) (.C 14 12))) (.C 9 13)) (.C 19 13))) (.B 1 (.B 4 (.B 8 (.F 1 3) (.C 14 3)) (.C 15 3)) (.C 16 3))))))) (.B 9 (.B 14 (.B 15 (.F 2 1) (.B 0 (.F 0 1) (.B 2 (.F 0 3) (.B 4 (.F 0 1) (.B 10 (.B 12 (.F 1 0) (.C 13 8)) (.C 12 14)))))) (.B 10 (.B 4 (.F 0 1) (.B 15 (.F 2 1) (.B 12 (.F 1 0) (.B 0 (.F 0 1) (.C 6 0))))) (.B 12 (.B 2 (.F 0 3) (.B 15 (.F 2 3) (.B 0 (.F 0 3) (.C 5 12)))) (.B 2 (.B 4 (.F 1 0) (.B 15 (.B 5 (.F 1 9) (.B 1 (.B 8 (.F 1 1) (.C 18 0)) (.C 19 7))) (.C 3 2))) (.B 6 (.B 15 (.B 5 (.F 3 2) (.B 1 (.B 8 (.F 1 1) (.C 18 2)) (.C 19 13))) (.C 2 2)) (.B 1 (.B 4 (.B 8 (.B 15 (.F 1 3) (.C 1 2)) (.C 14 3)) (.C 15 3)) (.C 16 3))))))) (.B 1 (.B 12 (.B 10 (.F 0 9) (.B 2 (.F 1 0) (.B 6 (.B 15 (.F 1 1) (.B 4 (.B 8 (.B 14 (.F 5 14) (.C 1 12)) (.C 7 14)) (.C 10 14))) (.B 4 (.B 8 (.B 14 (.F 5 14) (.B 15 (.F 1 3) (.C 1 12))) (.C 17 14)) (.C 20 14))))) (.B 2 (.B 4 (.F 1 0) (.B 8 (.B 15 (.F 1 1) (.B 14 (.F 5 8) (.C 3 8))) (.B 6 (.B 10 (.B 15 (.F 1 3) (.C 9 8)) (.C 16 14)) (.C 19 8)))) (.B 4 (.B 10 (.F 1 0) (.B 8 (.B 15 (.F 1 3) (.B 14 (.F 5 14) (.C 1 12))) (.C 15 14))) (.B 6 (.B 15 (.B 8 (.F 1 1) (.B 10 (.F 1 3) (.C 15 14))) (.C 11 8)) (.C 21 8))))) (.B 5 (.B 12 (.B 15 (.B 10 (.F 2 9) (.B 2 (.F 1 1) (.B 6 (.F 1 1) (.C 17 15)))) (.B 14 (.B 2 (.F 7 14) (.B 10 (.F 2 9) (.C 7 15))) (.B 0 (.B 10 (.F 0 9) (.C 1 14)) (.C 5 14)))) (.B 15 (.B 2 (.B 8 (.F 1 1) (.B 6 (.B 10 (.F 3 8) (.C 14 14)) (.C 18 8))) (.B 6 (.B 8 (.F 1 1) (.B 10 (.F 3 8) (.C 14 14))) (.C 19 15))) (.B 2 (.B 8 (.B 14 (.F 1 9) (.C 2 8)) (.C 8 8)) (.C 9 15)))) (.B 10 (.B 12 (.B 14 (.F 2 9) (.B 15 (.F 2 9) (.B 0 (.F 0 9) (.C 5 8)))) (.B 2 (.B 4 (.B 8 (.B 14 (.F 1 9) (.B 15 (.F 1 9) (.C 1 8))) (.C 14 9)) (.C 15 9)) (.C 16 9))) (.B 2 (.B 4 (.B 8 (.B 14 (.F 1 9) (.B 15 (.F 1 9) (.C 1 14))) (.C 14 15)) (.C 16 15)) (.C 15 15))))))
private def treeNode_5 : BitTree := .B 6 (.B 15 (.B 9 (.F 3 2) (.B 11 (.F 2 0) (.B 10 (.F 3 8) (.B 8 (.F 1 1) (.B 12 (.F 1 1) (.B 1 (.B 2 (.B 4 (.F 1 0) (.C 20 16)) (.C 17 16)) (.C 17 17))))))) (.B 11 (.B 8 (.F 0 0) (.B 12 (.F 1 1) (.B 0 (.F 0 0) (.B 13 (.B 14 (.F 2 3) (.B 1 (.F 0 9) (.C 13 4))) (.B 2 (.B 14 (.F 0 3) (.C 6 1)) (.C 13 10)))))) (.B 13 (.B 14 (.B 9 (.F 2 3) (.B 8 (.F 7 16) (.B 10 (.F 2 9) (.B 1 (.B 2 (.B 4 (.F 5 16) (.C 10 16)) (.C 7 16)) (.C 7 17))))) (.B 10 (.B 1 (.F 0 9) (.B 0 (.F 0 9) (.B 9 (.B 12 (.F 2 3) (.C 6 16)) (.C 5 16)))) (.B 12 (.B 9 (.F 2 3) (.B 1 (.B 8 (.F 1 3) (.C 1 13)) (.C 1 16))) (.B 1 (.B 8 (.F 1 3) (.C 2 13)) (.C 3 13))))) (.B 12 (.B 10 (.B 9 (.F 6 12) (.B 1 (.F 0 9) (.B 14 (.F 2 9) (.B 0 (.F 0 9) (.C 5 14))))) (.B 2 (.B 9 (.F 0 3) (.B 8 (.B 1 (.F 8 12) (.B 14 (.F 1 9) (.C 1 14))) (.C 1 15))) (.B 0 (.B 9 (.F 0 3) (.C 1 17)) (.C 5 17)))) (.B 9 (.B 0 (.B 14 (.F 0 3) (.B 10 (.F 4 2) (.C 0 2))) (.B 2 (.B 14 (.F 0 3) (.C 4 0)) (.C 6 17))) (.B 2 (.B 8 (.B 14 (.F 1 9) (.C 0 8)) (.C 2 15)) (.C 3 15))))))) (.B 11 (.B 14 (.B 13 (.F 2 3) (.B 15 (.F 2 0) (.B 0 (.F 0 0) (.B 2 (.F 0 3) (.B 8 (.F 0 0) (.C 12 20)))))) (.B 12 (.B 2 (.F 0 3) (.B 15 (.F 2 3) (.B 13 (.F 2 3) (.B 0 (.F 0 3) (.C 5 18))))) (.B 2 (.B 8 (.F 1 1) (.B 15 (.B 9 (.F 1 9) (.B 1 (.B 4 (.F 1 0) (.C 19 4)) (.C 21 4))) (.B 1 (.B 4 (.B 13 (.F 5 4) (.C 3 4)) (.C 9 4)) (.C 11 4)))) (.B 10 (.B 15 (.B 9 (.F 3 4) (.B 1 (.B 4 (.F 1 0) (.C 18 4)) (.C 19 19))) (.B 1 (.B 4 (.B 13 (.F 1 3) (.C 2 4)) (.C 8 4)) (.C 9 19))) (.B 1 (.B 4 (.B 8 (.B 13 (.F 1 3) (.B 15 (.F 1 3) (.C 1 4))) (.C 15 5)) (.C 14 5)) (.C 16 5)))))) (.B 2 (.B 9 (.B 14 (.F 0 3) (.B 15 (.F 1 9) (.B 12 (.F 0 3) (.B 1 (.B 4 (.B 8 (.B 13 (.F 1 3) (.C 0 4)) (.B 10 (.B 13 (.F 1 3) (.C 0 4)) (.C 1 3))) (.C 2 19)) (.C 3 19))))) (.B 15 (.B 8 (.F 1 1) (.B 12 (.F 1 1) (.B 1 (.B 4 (.F 1 0) (.C 21 17)) (.C 19 17)))) (.B 8 (.B 14 (.F 1 9) (.B 1 (.B 4 (.B 13 (.F 1 3) (.C 0 17)) (.C 3 22)) (.C 2 22))) (.B 1 (.B 4 (.B 13 (.B 10 (.F 1 3) (.B 14 (.F 5 16) (.C 1 13))) (.C 3 17)) (.C 11 17)) (.C 9 17))))) (.B 9 (.B 15 (.B 12 (.F 2 3) (.B 10 (.F 3 4) (.B 14 (.F 2 3) (.B 1 (.B 4 (.B 8 (.F 1 3) (.C 14 3)) (.C 14 5)) (.C 16 3))))) (.B 14 (.B 13 (.F 2 3) (.B 0 (.F 0 3) (.C 5 23))) (.B 12 (.B 13 (.F 2 3) (.B 0 (.F 0 3) (.C 5 18))) (.B 1 (.B 4 (.B 8 (.B 13 (.F 1 3) (.C 0 4)) (.B 10 (.B 13 (.F 1 3) (.C 0 4)) (.C 1 3))) (.C 2 19)) (.C 3 19))))) (.B 10 (.B 15 (.B 12 (.F 3 17) (.B 1 (.B 4 (.F 1 0) (.C 19 22)) (.C 18 17))) (.B 1 (.B 4 (.B 13 (.F 1 3) (.C 2 17)) (.C 9 22)) (.C 8 17))) (.B 1 (.B 4 (.B 8 (.B 13 (.F 1 3) (.B 15 (.F 1 3) (.C 1 17))) (.C 15 16)) (.C 16 16)) (.C 14 16))))))
private def treeNode_6 : BitTree := .B 11 (.B 13 (.B 14 (.F 9 18) (.B 6 (.B 15 (.F 2 0) (.B 0 (.F 0 0) (.B 1 (.F 0 9) (.B 8 (.F 0 0) (.C 12 18))))) (.B 1 (.B 2 (.B 4 (.F 5 4) (.B 12 (.F 1 1) (.B 8 (.F 1 1) (.C 16 18)))) (.B 10 (.B 4 (.F 1 3) (.B 12 (.F 7 18) (.C 14 18))) (.B 4 (.B 8 (.F 1 3) (.C 16 19)) (.C 14 19)))) (.B 2 (.B 4 (.B 8 (.F 5 18) (.B 9 (.B 15 (.F 1 0) (.C 10 18)) (.C 20 18))) (.B 9 (.B 12 (.B 15 (.F 1 0) (.C 7 18)) (.C 15 18)) (.C 17 18))) (.B 4 (.B 9 (.B 10 (.B 15 (.F 1 0) (.C 7 19)) (.C 15 19)) (.C 17 19)) (.B 9 (.B 10 (.B 12 (.B 15 (.F 1 0) (.C 7 18)) (.C 14 18)) (.C 14 19)) (.C 17 18))))))) (.B 1 (.B 12 (.B 6 (.F 0 9) (.B 2 (.F 1 1) (.B 10 (.B 15 (.F 1 0) (.B 4 (.B 8 (.B 14 (.F 5 20) (.C 1 18)) (.C 10 20)) (.C 7 20))) (.B 4 (.B 8 (.B 14 (.F 5 20) (.B 15 (.F 1 3) (.C 1 18))) (.C 20 20)) (.C 17 20))))) (.B 2 (.B 8 (.F 1 1) (.B 4 (.B 15 (.F 1 0) (.B 14 (.F 5 10) (.C 3 10))) (.B 6 (.B 10 (.B 15 (.F 1 3) (.C 9 10)) (.C 19 10)) (.C 16 20)))) (.B 6 (.B 8 (.F 1 1) (.B 10 (.B 15 (.F 1 3) (.C 11 10)) (.C 21 10))) (.B 4 (.B 8 (.B 15 (.F 1 3) (.B 14 (.F 5 20) (.C 1 18))) (.B 10 (.B 15 (.F 1 0) (.C 10 20)) (.C 20 20))) (.C 15 20))))) (.B 9 (.B 12 (.B 15 (.B 6 (.F 2 9) (.B 2 (.F 1 0) (.B 10 (.F 1 0) (.C 17 21)))) (.B 14 (.B 2 (.F 7 20) (.B 6 (.F 2 9) (.C 7 21))) (.B 0 (.B 6 (.F 0 9) (.C 1 20)) (.C 5 20)))) (.B 15 (.B 2 (.B 4 (.F 1 0) (.B 6 (.B 10 (.F 3 10) (.C 18 10)) (.C 14 20))) (.B 10 (.B 4 (.F 1 0) (.B 6 (.F 3 10) (.C 14 20))) (.C 19 21))) (.B 2 (.B 4 (.B 14 (.F 1 9) (.C 2 10)) (.C 8 10)) (.C 9 21)))) (.B 6 (.B 12 (.B 14 (.F 2 9) (.B 15 (.F 2 9) (.B 0 (.F 0 9) (.C 5 10)))) (.B 2 (.B 4 (.B 8 (.B 14 (.F 1 9) (.B 15 (.F 1 9) (.C 1 10))) (.C 15 11)) (.C 14 11)) (.C 16 11))) (.B 2 (.B 4 (.B 8 (.B 14 (.F 1 9) (.B 15 (.F 1 9) (.C 1 20))) (.C 16 21)) (.C 14 21)) (.C 15 21)))))) (.B 1 (.B 10 (.B 15 (.B 4 (.F 1 0) (.B 6 (.F 1 3) (.B 12 (.F 1 0) (.B 2 (.B 8 (.F 1 1) (.C 20 22)) (.C 17 22))))) (.B 13 (.B 6 (.F 0 9) (.B 4 (.F 1 3) (.B 2 (.B 8 (.B 14 (.F 5 22) (.C 1 19)) (.C 10 22)) (.C 7 22)))) (.B 12 (.B 6 (.F 0 9) (.B 2 (.B 4 (.B 9 (.F 8 18) (.B 8 (.B 14 (.F 1 9) (.C 0 11)) (.C 3 11))) (.C 1 21)) (.C 1 23))) (.B 2 (.B 4 (.B 8 (.B 14 (.F 1 9) (.C 0 10)) (.B 9 (.B 14 (.F 1 9) (.C 0 10)) (.C 1 9))) (.C 2 21)) (.C 3 21))))) (.B 2 (.B 15 (.B 12 (.F 1 0) (.B 4 (.F 1 0) (.B 8 (.F 1 1) (.C 21 16)))) (.B 4 (.B 8 (.B 13 (.F 1 3) (.B 14 (.F 1 9) (.C 0 16))) (.B 14 (.B 9 (.F 1 9) (.B 13 (.F 5 16) (.C 1 15))) (.C 3 16))) (.B 8 (.B 13 (.B 6 (.F 1 3) (.B 14 (.F 5 22) (.C 1 19))) (.C 3 23)) (.C 11 16)))) (.B 6 (.B 15 (.B 8 (.F 1 1) (.B 12 (.F 1 1) (.C 19 16))) (.B 8 (.B 13 (.F 1 3) (.C 2 23)) (.C 9 16))) (.B 4 (.B 8 (.B 13 (.F 1 3) (.B 15 (.F 1 3) (.C 1 23))) (.C 16 22)) (.C 15 22))))) (.B 9 (.B 10 (.B 15 (.B 6 (.F 3 10) (.B 4 (.F 1 0) (.B 12 (.F 1 0) (.C 17 23)))) (.B 13 (.B 14 (.B 4 (.F 7 22) (.B 6 (.F 2 9) (.C 7 23))) (.B 0 (.B 6 (.F 0 9) (.C 1 22)) (.C 5 22))) (.B 6 (.B 12 (.B 14 (.F 2 9) (.B 0 (.F 0 9) (.C 5 20))) (.B 2 (.B 4 (.B 14 (.F 1 9) (.C 0 10)) (.C 2 21)) (.C 3 21))) (.B 2 (.B 4 (.B 14 (.F 1 9) (.C 1 20)) (.C 1 21)) (.C 1 23))))) (.B 15 (.B 2 (.B 4 (.F 1 0) (.B 12 (.F 1 0) (.C 19 23))) (.B 6 (.B 12 (.F 3 16) (.C 18 16)) (.C 14 22))) (.B 2 (.B 4 (.B 14 (.F 1 9) (.C 2 16)) (.C 9 23)) (.C 8 16)))) (.B 6 (.B 10 (.B 12 (.B 14 (.F 2 9) (.B 15 (.F 2 9) (.B 0 (.F 0 9) (.C 5 16)))) (.B 13 (.B 14 (.F 2 9) (.B 15 (.F 2 9) (.B 0 (.F 0 9) (.C 5 16)))) (.B 2 (.B 4 (.B 8 (.B 14 (.F 1 9) (.B 15 (.F 1 9) (.C 0 8))) (.C 14 9)) (.C 14 11)) (.C 16 9)))) (.B 2 (.B 4 (.B 8 (.B 14 (.F 1 9) (.B 15 (.F 1 9) (.C 1 16))) (.C 15 17)) (.C 16 17)) (.C 14 17))) (.B 2 (.B 4 (.B 8 (.B 14 (.F 1 9) (.B 15 (.F 1 9) (.C 1 22))) (.C 16 23)) (.C 15 23)) (.C 14 23)))))
private def treeNode_7 : BitTree := .B 3 (.B 5 (.B 15 (.B 6 (.F 2 0) (.B 10 (.F 3 1) (.B 14 (.F 2 0) (.B 12 (.F 3 3) (.B 8 (.F 1 9) (.B 9 (.F 1 9) (.B 11 (.B 13 (.B 7 (.F 2 9) (.B 1 (.B 2 (.B 4 (.F 1 0) (.C 17 4)) (.C 17 5)) (.C 20 4))) (.B 1 (.B 2 (.B 4 (.F 1 0) (.C 14 0)) (.C 15 0)) (.C 16 0))) (.B 1 (.B 2 (.B 4 (.F 1 0) (.C 15 2)) (.C 14 2)) (.C 16 2))))))))) (treeNode_0)) (.B 13 (treeNode_1) (treeNode_2))) (.B 7 (.B 11 (treeNode_3) (treeNode_4)) (.B 5 (treeNode_5) (treeNode_6)))
private def mainTree : BitTree := treeNode_7

private lemma mainTree_ok : checkTree 0 0 mainTree = true := by decide

private lemma bit_test_le (M mOn mOff : ℕ) (_hM : M < 65536) :
    (∀ b < 16, (mOn >>> b) % 2 = 1 → (M >>> b) % 2 = 1) →
    (∀ b < 16, (mOff >>> b) % 2 = 1 → (M >>> b) % 2 = 0) →
    ∀ t : BitTree, checkTree mOn mOff t = true →
      (∃ kind < 10, ∃ pi < 24, forbSat M kind pi = true) ∨
      (∃ oidx < 22, ∃ pi < 24, ∀ c < 16, (M >>> c) % 2 = 1 → (permMask pi (orbitMask oidx) >>> c) % 2 = 1) := by
  intro hOn hOff t
  induction t generalizing mOn mOff with
  | F kind pi =>
    intro h
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
    left
    refine ⟨kind, h.1.1, pi, h.1.2, ?_⟩
    have hmono : ∀ a b, (∀ c < 16, (a >>> c) % 2 = 1 → (b >>> c) % 2 = 1) →
        forbSat a kind pi = true → forbSat b kind pi = true := by
      intro a b hab hfa
      unfold forbSat at hfa ⊢
      have hne_lt : ∀ x < 16, (a >>> x) % 2 = 1 → (b >>> x) % 2 = 1 := hab
      have hp_lt : ∀ idx < 4, (s4Perms.getD pi [0, 1, 2, 3]).getD idx 0 < 4 := by
        have : ∀ q < 24, ∀ idx < 4, (s4Perms.getD q [0, 1, 2, 3]).getD idx 0 < 4 := by decide
        exact this pi h.1.2
      have hpc_lt : ∀ c < 16, permCol pi c < 16 := by
        have : ∀ q < 24, ∀ c < 16, permCol q c < 16 := by decide
        exact this pi h.1.2
      have hfc_lt : ∀ c ∈ (forbCols.getD kind (4, [])).2, c < 16 := by
        have : ∀ k < 10, ∀ c ∈ (forbCols.getD k (4, [])).2, c < 16 := by decide
        exact this kind h.1.1
      rcases hfc_eq : forbCols.getD kind (4, []) with ⟨ne, cols⟩
      rw [hfc_eq] at hfa hfc_lt
      dsimp only at hfa hfc_lt ⊢
      split_ifs at hfa ⊢
      · simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hfa ⊢
        intro c hc
        have hlt_cm : ((if (c >>> 0) % 2 == 1 then 1 <<< ((s4Perms.getD pi [0, 1, 2, 3]).getD 0 0) else 0) +
            (if (c >>> 1) % 2 == 1 then 1 <<< ((s4Perms.getD pi [0, 1, 2, 3]).getD 1 0) else 0) +
            (if (c >>> 2) % 2 == 1 then 1 <<< ((s4Perms.getD pi [0, 1, 2, 3]).getD 2 0) else 0)) < 16 := by
          have : ∀ q < 24, ∀ cc < 16,
              ((if (cc >>> 0) % 2 == 1 then 1 <<< ((s4Perms.getD q [0, 1, 2, 3]).getD 0 0) else 0) +
               (if (cc >>> 1) % 2 == 1 then 1 <<< ((s4Perms.getD q [0, 1, 2, 3]).getD 1 0) else 0) +
               (if (cc >>> 2) % 2 == 1 then 1 <<< ((s4Perms.getD q [0, 1, 2, 3]).getD 2 0) else 0)) < 16 := by decide
          exact this pi h.1.2 c (hfc_lt c hc)
        have hlt_or : (((if (c >>> 0) % 2 == 1 then 1 <<< ((s4Perms.getD pi [0, 1, 2, 3]).getD 0 0) else 0) +
            (if (c >>> 1) % 2 == 1 then 1 <<< ((s4Perms.getD pi [0, 1, 2, 3]).getD 1 0) else 0) +
            (if (c >>> 2) % 2 == 1 then 1 <<< ((s4Perms.getD pi [0, 1, 2, 3]).getD 2 0) else 0)) |||
            (1 <<< ((s4Perms.getD pi [0, 1, 2, 3]).getD 3 0))) < 16 := by
          have : ∀ q < 24, ∀ cc < 16,
              (((if (cc >>> 0) % 2 == 1 then 1 <<< ((s4Perms.getD q [0, 1, 2, 3]).getD 0 0) else 0) +
                (if (cc >>> 1) % 2 == 1 then 1 <<< ((s4Perms.getD q [0, 1, 2, 3]).getD 1 0) else 0) +
                (if (cc >>> 2) % 2 == 1 then 1 <<< ((s4Perms.getD q [0, 1, 2, 3]).getD 2 0) else 0)) |||
                (1 <<< ((s4Perms.getD q [0, 1, 2, 3]).getD 3 0))) < 16 := by decide
          exact this pi h.1.2 c (hfc_lt c hc)
        rcases hfa c hc with h1 | h2
        · exact Or.inl (hne_lt _ (by simpa only [beq_iff_eq] using hlt_cm) h1)
        · exact Or.inr (hne_lt _ (by simpa only [beq_iff_eq] using hlt_or) h2)
      · simp only [List.all_eq_true, beq_iff_eq] at hfa ⊢
        intro c hc
        exact hne_lt _ (hpc_lt c (hfc_lt c hc)) (hfa c hc)
    exact hmono mOn M hOn h.2
  | C oidx pi =>
    intro h
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    right
    refine ⟨oidx, h.1.1, pi, h.1.2, ?_⟩
    intro c hc hMc
    have hnotOff : (mOff >>> c) % 2 = 0 := by
      by_contra hne
      have h1 : (mOff >>> c) % 2 = 1 := by omega
      have := hOff c hc h1; omega
    have hbit : (((65535 ^^^ mOff) &&& (65535 ^^^ permMask pi (orbitMask oidx))).testBit c) = false := by
      rw [h.2]; simp
    have h65535 : (65535 : ℕ).testBit c = true := by
      have : ∀ x < 16, (65535 : ℕ).testBit x = true := by decide
      exact this c hc
    simp only [Nat.testBit_and, Nat.testBit_xor, h65535, Bool.true_xor, Bool.and_eq_false_iff,
      Bool.not_eq_false'] at hbit
    have hmOff_f : mOff.testBit c = false := by
      rw [Nat.testBit_eq_decide_div_mod_eq]; simp [Nat.shiftRight_eq_div_pow] at hnotOff ⊢; omega
    rcases hbit with h1 | h2
    · exact absurd h1 (by rw [hmOff_f]; decide)
    · rw [Nat.testBit_eq_decide_div_mod_eq] at h2
      simpa [Nat.shiftRight_eq_div_pow] using h2
  | B bit t1 t0 ih1 ih0 =>
    intro h
    simp only [checkTree, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hb : (M >>> bit) % 2 = 1
    · refine ih1 (mOn ||| (1 <<< bit)) mOff ?_ hOff h.1.2
      intro c hc hbit
      have htb : (mOn ||| (1 <<< bit)).testBit c = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq]; simpa [Nat.shiftRight_eq_div_pow] using hbit
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true] at htb
      rcases htb with h1 | h2
      · apply hOn c hc
        rw [Nat.testBit_eq_decide_div_mod_eq] at h1
        simpa [Nat.shiftRight_eq_div_pow] using h1
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero] at h2
        have hcb : c = bit := by omega
        subst hcb; exact hb
    · refine ih0 mOn (mOff ||| (1 <<< bit)) hOn ?_ h.2
      intro c hc hbit
      have htb : (mOff ||| (1 <<< bit)).testBit c = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq]; simpa [Nat.shiftRight_eq_div_pow] using hbit
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true] at htb
      rcases htb with h1 | h2
      · apply hOff c hc
        rw [Nat.testBit_eq_decide_div_mod_eq] at h1
        simpa [Nat.shiftRight_eq_div_pow] using h1
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_one_eq_true_iff_self_eq_zero] at h2
        have hcb : c = bit := by omega
        subst hcb; omega

private lemma mask_dichotomy (M : ℕ) (hM : M < 65536) :
    (∃ kind < 10, ∃ pi < 24, forbSat M kind pi = true) ∨
    (∃ oidx < 22, ∃ pi < 24, ∀ c < 16, (M >>> c) % 2 = 1 → (permMask pi (orbitMask oidx) >>> c) % 2 = 1) :=
  bit_test_le M 0 0 hM (fun _ _ h => by simp at h) (fun _ _ h => by simp at h) mainTree mainTree_ok

/-! ### 4. Verification of the 22 explicit words & `flatMap` expansion -/

private def noAdjEqBool : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => (a != b) && noAdjEqBool (b :: t)

private lemma noAdjEqBool_iff (l : List ℕ) : noAdjEqBool l = true ↔ NoAdjEq l := by
  induction l with
  | nil => simp [noAdjEqBool, NoAdjEq]
  | cons a t ih =>
    cases t with
    | nil => simp [noAdjEqBool, NoAdjEq]
    | cons b t' =>
      simp only [noAdjEqBool, Bool.and_eq_true, bne_iff_ne, ne_eq, NoAdjEq]
      rw [ih]

private def altBool (w : List ℕ) (x y : ℕ) : Bool :=
  noAdjEqBool (w.filter (fun z => (z == x) || (z == y)))

private lemma altBool_iff (w : List ℕ) (x y : ℕ) : altBool w x y = true ↔ Alternates w x y := by
  unfold altBool Alternates
  rw [noAdjEqBool_iff]
  have hf : w.filter (fun z => (z == x) || (z == y)) = w.filter (fun z => decide (z = x ∨ z = y)) := by
    congr 1; ext z; by_cases h1 : z = x <;> by_cases h2 : z = y <;> simp [h1, h2]
  rw [hf]

private def checkOrbitWord (oidx : ℕ) : Bool :=
  let cols := orbitCols.getD oidx []
  let w := orbitWords.getD oidx []
  let k := cols.length
  (k == 8) &&
  (List.range (4 + k)).all (fun v => w.contains v) &&
  w.all (fun v => v < 4 + k) &&
  (List.range 4).all (fun i => (List.range 4).all (fun j => i == j || !altBool w i j)) &&
  (List.range k).all (fun i => (List.range k).all (fun j => i == j || altBool w (4 + i) (4 + j))) &&
  (List.range 4).all (fun e => (List.range k).all (fun i =>
    altBool w e (4 + i) == (((cols.getD i 0) >>> e) % 2 == 1)))

private lemma all_orbitWords_ok : (List.range 22).all checkOrbitWord = true := by decide

private lemma filter_pair_singleton {β : Type*} [DecidableEq β] (l : List β) (u v : β)
    (hnd : l.Nodup) (hu : u ∈ l) (hv : v ∉ l) :
    l.filter (fun z => decide (z = u ∨ z = v)) = [u] := by
  induction l with
  | nil => simp at hu
  | cons hd tl ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons, not_or] at hu hv
    rw [List.filter_cons]
    rcases hu with rfl | htl
    · have hrest : tl.filter (fun z => decide (z = u ∨ z = v)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro z hz; simp only [decide_eq_true_eq, not_or]
        exact ⟨fun h => hnd.1 (h ▸ hz), fun h => hv.2 (h ▸ hz)⟩
      rw [hrest]; simp
    · have hne_u : hd ≠ u := fun h => hnd.1 (h ▸ htl)
      have hne_v : hd ≠ v := fun h => hv.1 h.symm
      rw [ih hnd.2 htl hv.2]; simp [hne_u, hne_v]

private lemma flatMap_filter_pair {α β : Type*} [DecidableEq α] [DecidableEq β]
    (w : List α) (f : α → List β) (u v : β) (a b : α)
    (hdisj : ∀ x y, x ≠ y → ∀ z ∈ f x, z ∉ f y)
    (hnodup : ∀ x, (f x).Nodup)
    (hu : u ∈ f a) (hv : v ∈ f b) (hab : a ≠ b) :
    (w.flatMap f).filter (fun z => decide (z = u ∨ z = v)) =
    (w.filter (fun x => decide (x = a ∨ x = b))).map (fun x => if x = a then u else v) := by
  induction w with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.filter_append, List.filter_cons, ih]
    by_cases hxa : x = a
    · subst hxa
      have hfx : (f x).filter (fun z => decide (z = u ∨ z = v)) = [u] :=
        filter_pair_singleton (f x) u v (hnodup x) hu (hdisj b x hab.symm v hv)
      rw [hfx]; simp
    · by_cases hxb : x = b
      · subst hxb
        have hfx : (f x).filter (fun z => decide (z = u ∨ z = v)) = [v] := by
          have hswap : (fun z : β => decide (z = u ∨ z = v)) = (fun z : β => decide (z = v ∨ z = u)) := by
            ext z; simp [or_comm]
          rw [hswap]
          exact filter_pair_singleton (f x) v u (hnodup x) hv (hdisj a x hab u hu)
        rw [hfx]; simp [hxa]
      · have hfx : (f x).filter (fun z => decide (z = u ∨ z = v)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro z hz; simp only [decide_eq_true_eq, not_or]
          exact ⟨fun h => hdisj a x (Ne.symm hxa) u hu (h ▸ hz),
                 fun h => hdisj b x (Ne.symm hxb) v hv (h ▸ hz)⟩
        rw [hfx]; simp [hxa, hxb]

private lemma filter_pair_double {β : Type*} [DecidableEq β] (l : List β) (u v : β)
    (hnd : l.Nodup) (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) :
    l.filter (fun z => decide (z = u ∨ z = v)) = [u, v] ∨
    l.filter (fun z => decide (z = u ∨ z = v)) = [v, u] := by
  induction l with
  | nil => simp at hu
  | cons hd tl ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.mem_cons] at hu hv
    rw [List.filter_cons]
    rcases hu with rfl | hu'
    · have hv' : v ∈ tl := hv.resolve_left huv.symm
      have hswap : (fun z : β => decide (z = u ∨ z = v)) = (fun z : β => decide (z = v ∨ z = u)) := by
        ext z; simp [or_comm]
      have htl : tl.filter (fun z => decide (z = u ∨ z = v)) = [v] := by
        rw [hswap]; exact filter_pair_singleton tl v u hnd.2 hv' hnd.1
      left; rw [htl]; simp
    · rcases hv with rfl | hv'
      · have htl : tl.filter (fun z => decide (z = u ∨ z = v)) = [u] :=
          filter_pair_singleton tl u v hnd.2 hu' hnd.1
        right; rw [htl]; simp
      · have hne1 : hd ≠ u := fun h => hnd.1 (h ▸ hu')
        have hne2 : hd ≠ v := fun h => hnd.1 (h ▸ hv')
        simp only [hne1, hne2, or_self, decide_false]
        exact ih hnd.2 hu' hv'

private lemma flatMap_same_alternates {α β : Type*} [DecidableEq α] [DecidableEq β]
    (w : List α) (f : α → List β) (u v : β) (a : α)
    (hdisj : ∀ x y, x ≠ y → ∀ z ∈ f x, z ∉ f y)
    (hnodup : ∀ x, (f x).Nodup)
    (hu : u ∈ f a) (hv : v ∈ f a) (huv : u ≠ v) :
    Alternates (w.flatMap f) u v := by
  have hfa := filter_pair_double (f a) u v (hnodup a) hu hv huv
  have hrep : ∀ (p q : β), p ≠ q → (f a).filter (fun z => decide (z = u ∨ z = v)) = [p, q] →
      NoAdjEq ((w.flatMap f).filter (fun z => decide (z = u ∨ z = v))) ∧
      (((w.flatMap f).filter (fun z => decide (z = u ∨ z = v))) = [] ∨
       ((w.flatMap f).filter (fun z => decide (z = u ∨ z = v))).head? = some p) := by
    intro p q hpq hpair
    induction w with
    | nil => simp [NoAdjEq]
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.filter_append]
      by_cases hxa : x = a
      · subst hxa
        rw [hpair]
        rcases ih.2 with hnil | hhd
        · rw [hnil]; simp [NoAdjEq, hpq]
        · cases hl : (xs.flatMap f).filter (fun z => decide (z = u ∨ z = v)) with
          | nil => simp [NoAdjEq, hpq]
          | cons hd tl =>
            rw [hl] at hhd ih
            have hhd_eq : hd = p := by simpa using hhd
            subst hhd_eq
            exact ⟨⟨hpq, hpq.symm, ih.1⟩, Or.inr rfl⟩
      · have hfx : (f x).filter (fun z => decide (z = u ∨ z = v)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro z hz; simp only [decide_eq_true_eq, not_or]
          exact ⟨fun h => hdisj a x (Ne.symm hxa) u hu (h ▸ hz),
                 fun h => hdisj a x (Ne.symm hxa) v hv (h ▸ hz)⟩
        rw [hfx, List.nil_append]; exact ih
  unfold Alternates
  rcases hfa with h1 | h2
  · exact (hrep u v huv h1).1
  · exact (hrep v u huv.symm h2).1

private lemma noAdjEq_map_iff {α β : Type*} {f : α → β} (l : List α)
    (hinj : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) :
    NoAdjEq (l.map f) ↔ NoAdjEq l := by
  induction l with
  | nil => simp [NoAdjEq]
  | cons a t ih =>
    cases t with
    | nil => simp [NoAdjEq]
    | cons b t' =>
      rw [List.map_cons, List.map_cons, NoAdjEq, NoAdjEq]
      have hne : f a ≠ f b ↔ a ≠ b :=
        ⟨fun h heq => h (congrArg f heq), fun h heq => h (hinj a (by simp) b (by simp) heq)⟩
      rw [hne, ← List.map_cons, ih (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))]

/-! ### 5. Main theorem -/

private lemma s4Perms_bij :
    ∀ pi < 24,
      (∀ i < 4, (s4Perms.getD pi [0, 1, 2, 3]).getD i 0 < 4) ∧
      (∀ i < 4, ∀ j < 4, (s4Perms.getD pi [0, 1, 2, 3]).getD i 0 =
        (s4Perms.getD pi [0, 1, 2, 3]).getD j 0 → i = j) := by
  decide

private lemma permCol_bit :
    ∀ pi < 24, ∀ c < 16, ∀ i < 4,
      ((permCol pi c) >>> ((s4Perms.getD pi [0, 1, 2, 3]).getD i 0)) % 2 = (c >>> i) % 2 := by
  decide

private lemma permMask_mem_iff :
    ∀ oidx < 22, ∀ pi < 24, ∀ c < 16,
      (permMask pi (orbitMask oidx) >>> c) % 2 = 1 →
      ∃ j < 8, permCol pi ((orbitCols.getD oidx []).getD j 0) = c := by
  decide

private lemma orbitCols_nodup :
    ∀ oidx < 22, ∀ j1 < 8, ∀ j2 < 8,
      (orbitCols.getD oidx []).getD j1 0 = (orbitCols.getD oidx []).getD j2 0 → j1 = j2 := by
  decide

private lemma orbitCols_lt16 :
    ∀ oidx < 22, ∀ j < 8, (orbitCols.getD oidx []).getD j 0 < 16 := by
  decide

private lemma main_proof :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsSplitGraphWithIndep4 G →
      (IsWordRepresentable G ↔
        ¬ HasInducedSubgraph G graphT1 ∧
        ¬ HasInducedSubgraph G graphT2 ∧
        ¬ HasInducedSubgraph G graphT3 ∧
        ¬ HasInducedSubgraph G graphT4 ∧
        ¬ HasInducedSubgraph G graphT5 ∧
        ¬ HasInducedSubgraph G graphT6 ∧
        ¬ HasInducedSubgraph G graphT7 ∧
        ¬ HasInducedSubgraph G graphT8 ∧
        ¬ HasInducedSubgraph G graphD1) := by
  intro V _ _ G hsplit
  constructor
  · intro hWR
    have hST := wordRep_imp_semiTransitive hWR
    exact ⟨fun h => not_st_T1 (semiTransitive_of_induced hST h),
           fun h => not_st_T2 (semiTransitive_of_induced hST h),
           fun h => not_st_T3 (semiTransitive_of_induced hST h),
           fun h => not_st_T4 (semiTransitive_of_induced hST h),
           fun h => not_st_T5 (semiTransitive_of_induced hST h),
           fun h => not_st_T6 (semiTransitive_of_induced hST h),
           fun h => not_st_T7 (semiTransitive_of_induced hST h),
           fun h => not_st_T8 (semiTransitive_of_induced hST h),
           fun h => not_st_D1 (semiTransitive_of_induced hST h)⟩
  · rintro ⟨hT1, hT2, hT3, hT4, hT5, hT6, hT7, hT8, hD1⟩
    classical
    obtain ⟨E, K, hEcard, hDisj, hUniv, hEindep, hKclique⟩ := hsplit
    let eEquiv : Fin 4 ≃ {x // x ∈ E} := (E.equivFinOfCardEq hEcard).symm
    let eV : Fin 4 → V := fun i => (eEquiv i).val
    have heV_mem : ∀ i : Fin 4, eV i ∈ E := fun i => (eEquiv i).property
    have heV_inj : Function.Injective eV := fun i j h => eEquiv.injective (Subtype.ext h)
    have hE_surj : ∀ v ∈ E, ∃ i : Fin 4, eV i = v := fun v hv =>
      ⟨eEquiv.symm ⟨v, hv⟩, congrArg Subtype.val (eEquiv.apply_symm_apply ⟨v, hv⟩)⟩
    let col : V → ℕ := fun v =>
      (if G.Adj (eV 0) v then 1 else 0) +
      (if G.Adj (eV 1) v then 2 else 0) +
      (if G.Adj (eV 2) v then 4 else 0) +
      (if G.Adj (eV 3) v then 8 else 0)
    have hcol_lt : ∀ v : V, col v < 16 := by
      intro v; dsimp only [col]; split_ifs <;> omega
    have hcol_bit : ∀ (v : V) (i : Fin 4), ((col v) >>> i.val) % 2 = 1 ↔ G.Adj (eV i) v := by
      intro v i
      fin_cases i <;> dsimp only [col] <;> split_ifs <;> simp_all
    let hasCol : ℕ → Bool := fun c => decide (∃ v ∈ K, col v = c)
    let M : ℕ := (List.range 16).foldl (fun acc c => if hasCol c then acc ||| (1 <<< c) else acc) 0
    have hM_spec : M < 65536 ∧ ∀ c < 16, (M >>> c) % 2 = 1 ↔ ∃ v ∈ K, col v = c := by
      have hfold : ∀ n (hn : n ≤ 16),
          let m := (List.range n).foldl (fun acc c => if hasCol c then acc ||| (1 <<< c) else acc) 0
          m < 2 ^ n ∧
          (∀ c < n, (m >>> c) % 2 = 1 ↔ hasCol c = true) ∧
          (∀ c ≥ n, (m >>> c) % 2 = 0) := by
        intro n hn
        induction n with
        | zero => simp
        | succ n ih =>
          obtain ⟨hlt, hlo, hhi⟩ := ih (by omega)
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          set m := (List.range n).foldl (fun acc c => if hasCol c then acc ||| (1 <<< c) else acc) 0
          have hm_lt : m < 2 ^ n := hlt
          by_cases hc : hasCol n = true
          · simp only [hc, ↓reduceIte]
            have hpow : 1 <<< n = 2 ^ n := by rw [Nat.shiftLeft_eq, one_mul]
            have hor_lt : m ||| (1 <<< n) < 2 ^ (n + 1) := by
              rw [hpow]
              exact Nat.or_lt_two_pow (lt_trans hm_lt (Nat.pow_lt_pow_right (by omega) (by omega)))
                (Nat.pow_lt_pow_right (by omega) (by omega))
            refine ⟨hor_lt, ?_, ?_⟩
            · intro c hcn
              have htb : (m ||| (1 <<< n)).testBit c = (m.testBit c || (1 <<< n).testBit c) := Nat.testBit_or m (1 <<< n) c
              rw [Nat.testBit_shiftLeft] at htb
              have hiff : ((m ||| (1 <<< n)) >>> c) % 2 = 1 ↔ (m ||| (1 <<< n)).testBit c = true := by
                rw [Nat.testBit_eq_decide_div_mod_eq]; simp [Nat.shiftRight_eq_div_pow]
              rw [hiff, htb, Bool.or_eq_true]
              by_cases hcn' : c = n
              · subst hcn'; simp [hc]
              · have hclt : c < n := by omega
                have hbit1 : (decide (c ≥ n) && (1 : ℕ).testBit (c - n)) = false := by
                  simp [show ¬ c ≥ n by omega]
                rw [hbit1]
                simp only [Bool.false_eq_true, or_false, Nat.testBit_eq_decide_div_mod_eq]
                simpa [Nat.shiftRight_eq_div_pow] using hlo c hclt
            · intro c hcn
              have htb : (m ||| (1 <<< n)).testBit c = false := by
                rw [Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_false_iff]
                constructor
                · rw [Nat.testBit_eq_decide_div_mod_eq]; simp only [decide_eq_false_iff_not]
                  have h0 := hhi c (by omega)
                  rw [Nat.shiftRight_eq_div_pow] at h0; omega
                · rw [Bool.and_eq_false_iff]; right
                  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
                  have hpow2 : 2 ≤ 2 ^ (c - n) := by
                    calc 2 = 2 ^ 1 := by norm_num
                      _ ≤ 2 ^ (c - n) := Nat.pow_le_pow_right (by omega) (by omega)
                  rw [Nat.div_eq_of_lt (by omega)]; omega
              rw [Nat.testBit_eq_decide_div_mod_eq] at htb
              simp only [decide_eq_false_iff_not] at htb
              rw [Nat.shiftRight_eq_div_pow]; omega
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]
            refine ⟨lt_trans hm_lt (Nat.pow_lt_pow_right (by omega) (by omega)), ?_, ?_⟩
            · intro c hcn
              by_cases hcn' : c = n
              · subst hcn'; rw [hhi c le_rfl]; simp [hc]
              · exact hlo c (by omega)
            · intro c hcn; exact hhi c (by omega)
      obtain ⟨hlt, hlo, _⟩ := hfold 16 le_rfl
      refine ⟨by simpa using hlt, fun c hc => ?_⟩
      rw [hlo c hc]; simp [hasCol]
    rcases mask_dichotomy M hM_spec.1 with ⟨kind, hkind, pi, hpi, hfsat⟩ | ⟨oidx, hoidx, pi, hpi, hcov⟩
    · -- Forbidden induced subgraph case: derive contradiction!
      exfalso
      have hp_bij := s4Perms_bij pi hpi
      let pFun : Fin 4 → Fin 4 := fun i => ⟨(s4Perms.getD pi [0, 1, 2, 3]).getD i.val 0, hp_bij.1 i.val i.isLt⟩
      have hpFun_inj : Function.Injective pFun := fun i j h =>
        Fin.ext (hp_bij.2 i.val i.isLt j.val j.isLt (congrArg Fin.val h))
      -- Helper to build `HasInducedSubgraph G (mkSplitGraph e k cols)` when `e = 3` or `e = 4`
      have hbuild3 : ∀ (cols : List ℕ) (k : ℕ), cols.length = k →
          (∀ c ∈ cols, c < 8) →
          (∀ j : Fin k, ∃ v ∈ K, ∀ i : Fin 3, G.Adj (eV (pFun ⟨i.val, by omega⟩)) v ↔
            ((cols.getD j.val 0) >>> i.val) % 2 = 1) →
          (∀ j1 j2 : Fin k, j1 ≠ j2 → cols.getD j1.val 0 ≠ cols.getD j2.val 0) →
          HasInducedSubgraph G (mkSplitGraph 3 k cols) := by
        intro cols k hlen hclt hwit hcdist
        choose vK hvK_mem hvK_adj using hwit
        have hvK_inj : Function.Injective vK := by
          intro j1 j2 heq
          by_contra hne
          have hcd := hcdist j1 j2 hne
          apply hcd
          have hlt1 : cols.getD j1.val 0 < 8 := hclt _ (by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _)
          have hlt2 : cols.getD j2.val 0 < 8 := hclt _ (by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _)
          have hb : ∀ i < 3, ((cols.getD j1.val 0) >>> i) % 2 = ((cols.getD j2.val 0) >>> i) % 2 := by
            intro i hi
            have h1 := hvK_adj j1 ⟨i, hi⟩
            have h2 := hvK_adj j2 ⟨i, hi⟩
            rw [heq] at h1
            have hiff := h1.symm.trans h2
            by_cases hm : ((cols.getD j1.val 0) >>> i) % 2 = 1
            · rw [hm, hiff.mp hm]
            · have hm0 : ((cols.getD j1.val 0) >>> i) % 2 = 0 := by omega
              have hm2 : ((cols.getD j2.val 0) >>> i) % 2 ≠ 1 := fun h => hm (hiff.mpr h)
              omega
          have hb0 := hb 0 (by omega); have hb1 := hb 1 (by omega); have hb2 := hb 2 (by omega)
          simp only [Nat.shiftRight_eq_div_pow] at hb0 hb1 hb2
          omega
        let f : Fin (3 + k) → V := fun x =>
          if h : x.val < 3 then eV (pFun ⟨x.val, by omega⟩) else vK ⟨x.val - 3, by omega⟩
        have hf_inj : Function.Injective f := by
          intro x y hxy
          dsimp only [f] at hxy
          split_ifs at hxy with hx hy hy
          · have := hpFun_inj (heV_inj hxy); exact Fin.ext (by have hval := congrArg Fin.val this; dsimp only at hval; omega)
          · exact absurd (hvK_mem _) (Finset.disjoint_left.mp hDisj (hxy ▸ heV_mem _))
          · exact absurd (hvK_mem _) (Finset.disjoint_left.mp hDisj (hxy.symm ▸ heV_mem _))
          · have := hvK_inj hxy; exact Fin.ext (by have hval := congrArg Fin.val this; dsimp only at hval; omega)
        refine ⟨⟨f, hf_inj⟩, fun u v => ?_⟩
        simp only [Function.Embedding.coeFn_mk]
        dsimp only [mkSplitGraph, f]
        by_cases hu : u.val < 3 <;> by_cases hv : v.val < 3
        · rw [dif_pos hu, dif_pos hv]
          constructor
          · rintro ⟨_, h⟩; rcases h with ⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> omega
          · intro hadj; exact absurd hadj (hEindep _ (heV_mem _) _ (heV_mem _))
        · rw [dif_pos hu, dif_neg hv]
          have hne : u ≠ v := fun h => hv (h ▸ hu)
          have hge : 3 ≤ v.val := by omega
          have hiff := hvK_adj ⟨v.val - 3, by omega⟩ ⟨u.val, hu⟩
          constructor
          · rintro ⟨_, h⟩
            rcases h with ⟨h1, _⟩ | ⟨_, _, h3⟩ | ⟨h1, _, _⟩
            · omega
            · exact hiff.mpr h3
            · omega
          · intro hadj
            exact ⟨hne, Or.inr (Or.inl ⟨hu, hge, hiff.mp hadj⟩)⟩
        · rw [dif_neg hu, dif_pos hv]
          have hne : u ≠ v := fun h => hu (h ▸ hv)
          have hge : 3 ≤ u.val := by omega
          have hiff := hvK_adj ⟨u.val - 3, by omega⟩ ⟨v.val, hv⟩
          constructor
          · rintro ⟨_, h⟩
            rcases h with ⟨_, h2⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
            · omega
            · omega
            · exact SimpleGraph.Adj.symm (hiff.mpr h3)
          · intro hadj
            exact ⟨hne, Or.inr (Or.inr ⟨hv, hge, hiff.mp (SimpleGraph.Adj.symm hadj)⟩)⟩
        · rw [dif_neg hu, dif_neg hv]
          have hgeu : 3 ≤ u.val := by omega
          have hgev : 3 ≤ v.val := by omega
          constructor
          · rintro ⟨hne, _⟩
            exact hKclique _ (hvK_mem _) _ (hvK_mem _) (fun h => hne (hf_inj (by dsimp only [f]; rw [dif_neg hu, dif_neg hv]; exact h)))
          · intro hadj
            exact ⟨fun h => by subst h; exact G.loopless.irrefl _ hadj, Or.inl ⟨hgeu, hgev⟩⟩
      have hbuild4 : ∀ (cols : List ℕ) (k : ℕ), cols.length = k →
          (∀ c ∈ cols, c < 16) →
          (∀ j : Fin k, ∃ v ∈ K, col v = permCol pi (cols.getD j.val 0)) →
          (∀ j1 j2 : Fin k, j1 ≠ j2 → cols.getD j1.val 0 ≠ cols.getD j2.val 0) →
          HasInducedSubgraph G (mkSplitGraph 4 k cols) := by
        intro cols k hlen hclt hwit hcdist
        choose vK hvK_mem hvK_col using hwit
        have hvK_adj : ∀ (j : Fin k) (i : Fin 4),
            G.Adj (eV (pFun i)) (vK j) ↔ ((cols.getD j.val 0) >>> i.val) % 2 = 1 := by
          intro j i
          rw [← hcol_bit (vK j) (pFun i), hvK_col j]
          have hclt_j : cols.getD j.val 0 < 16 := hclt _ (by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _)
          have hpb := permCol_bit pi hpi (cols.getD j.val 0) hclt_j i.val i.isLt
          dsimp only [pFun]; rw [hpb]
        have hvK_inj : Function.Injective vK := by
          intro j1 j2 heq
          by_contra hne
          have hcd := hcdist j1 j2 hne
          apply hcd
          have hlt1 : cols.getD j1.val 0 < 16 := hclt _ (by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _)
          have hlt2 : cols.getD j2.val 0 < 16 := hclt _ (by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _)
          have hb : ∀ i < 4, ((cols.getD j1.val 0) >>> i) % 2 = ((cols.getD j2.val 0) >>> i) % 2 := by
            intro i hi
            have h1 := hvK_adj j1 ⟨i, hi⟩
            have h2 := hvK_adj j2 ⟨i, hi⟩
            rw [heq] at h1
            have hiff := h1.symm.trans h2
            by_cases hm : ((cols.getD j1.val 0) >>> i) % 2 = 1
            · rw [hm, hiff.mp hm]
            · have hm2 : ((cols.getD j2.val 0) >>> i) % 2 ≠ 1 := fun h => hm (hiff.mpr h)
              omega
          have hb0 := hb 0 (by omega); have hb1 := hb 1 (by omega)
          have hb2 := hb 2 (by omega); have hb3 := hb 3 (by omega)
          simp only [Nat.shiftRight_eq_div_pow] at hb0 hb1 hb2 hb3
          omega
        let f : Fin (4 + k) → V := fun x =>
          if h : x.val < 4 then eV (pFun ⟨x.val, h⟩) else vK ⟨x.val - 4, by omega⟩
        have hf_inj : Function.Injective f := by
          intro x y hxy
          dsimp only [f] at hxy
          split_ifs at hxy with hx hy hy
          · have := hpFun_inj (heV_inj hxy); exact Fin.ext (by have hval := congrArg Fin.val this; dsimp only at hval; omega)
          · exact absurd (hvK_mem _) (Finset.disjoint_left.mp hDisj (hxy ▸ heV_mem _))
          · exact absurd (hvK_mem _) (Finset.disjoint_left.mp hDisj (hxy.symm ▸ heV_mem _))
          · have := hvK_inj hxy; exact Fin.ext (by have hval := congrArg Fin.val this; dsimp only at hval; omega)
        refine ⟨⟨f, hf_inj⟩, fun u v => ?_⟩
        simp only [Function.Embedding.coeFn_mk]
        dsimp only [mkSplitGraph, f]
        by_cases hu : u.val < 4 <;> by_cases hv : v.val < 4
        · rw [dif_pos hu, dif_pos hv]
          constructor
          · rintro ⟨_, h⟩; rcases h with ⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> omega
          · intro hadj; exact absurd hadj (hEindep _ (heV_mem _) _ (heV_mem _))
        · rw [dif_pos hu, dif_neg hv]
          have hne : u ≠ v := fun h => hv (h ▸ hu)
          have hge : 4 ≤ v.val := by omega
          have hiff := hvK_adj ⟨v.val - 4, by omega⟩ ⟨u.val, hu⟩
          constructor
          · rintro ⟨_, h⟩
            rcases h with ⟨h1, _⟩ | ⟨_, _, h3⟩ | ⟨h1, _, _⟩
            · omega
            · exact hiff.mpr h3
            · omega
          · intro hadj
            exact ⟨hne, Or.inr (Or.inl ⟨hu, hge, hiff.mp hadj⟩)⟩
        · rw [dif_neg hu, dif_pos hv]
          have hne : u ≠ v := fun h => hu (h ▸ hv)
          have hge : 4 ≤ u.val := by omega
          have hiff := hvK_adj ⟨u.val - 4, by omega⟩ ⟨v.val, hv⟩
          constructor
          · rintro ⟨_, h⟩
            rcases h with ⟨_, h2⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
            · omega
            · omega
            · exact SimpleGraph.Adj.symm (hiff.mpr h3)
          · intro hadj
            exact ⟨hne, Or.inr (Or.inr ⟨hv, hge, hiff.mp (SimpleGraph.Adj.symm hadj)⟩)⟩
        · rw [dif_neg hu, dif_neg hv]
          have hgeu : 4 ≤ u.val := by omega
          have hgev : 4 ≤ v.val := by omega
          constructor
          · rintro ⟨hne, _⟩
            exact hKclique _ (hvK_mem _) _ (hvK_mem _) (fun h => hne (hf_inj (by dsimp only [f]; rw [dif_neg hu, dif_neg hv]; exact h)))
          · intro hadj
            exact ⟨fun h => by subst h; exact G.loopless.irrefl _ hadj, Or.inl ⟨hgeu, hgev⟩⟩
      -- Helper to extract witness for `ne = 3` from `forbSat M kind pi = true`
      have hcm_bits : ∀ q < 24, ∀ c < 8,
          let p := s4Perms.getD q [0, 1, 2, 3]
          let cm :=
            (if (c >>> 0) % 2 == 1 then 1 <<< (p.getD 0 0) else 0) +
            (if (c >>> 1) % 2 == 1 then 1 <<< (p.getD 1 0) else 0) +
            (if (c >>> 2) % 2 == 1 then 1 <<< (p.getD 2 0) else 0)
          let miss := 1 <<< (p.getD 3 0)
          cm < 16 ∧ (cm ||| miss) < 16 ∧
          (∀ i < 3, (cm >>> (p.getD i 0)) % 2 = (c >>> i) % 2) ∧
          (∀ i < 3, ((cm ||| miss) >>> (p.getD i 0)) % 2 = (c >>> i) % 2) := by
        decide
      have hget3 : ∀ (cols : List ℕ) (k : ℕ), cols.length = k → (∀ c ∈ cols, c < 8) →
          (cols.all fun c =>
            let p := s4Perms.getD pi [0, 1, 2, 3]
            let miss := 1 <<< (p.getD 3 0)
            let cm :=
              (if (c >>> 0) % 2 == 1 then 1 <<< (p.getD 0 0) else 0) +
              (if (c >>> 1) % 2 == 1 then 1 <<< (p.getD 1 0) else 0) +
              (if (c >>> 2) % 2 == 1 then 1 <<< (p.getD 2 0) else 0)
            ((M >>> cm) % 2 == 1) || ((M >>> (cm ||| miss)) % 2 == 1)) = true →
          ∀ j : Fin k, ∃ v ∈ K, ∀ i : Fin 3, G.Adj (eV (pFun ⟨i.val, by omega⟩)) v ↔
            ((cols.getD j.val 0) >>> i.val) % 2 = 1 := by
        intro cols k hlen hclt hall j
        simp only [List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hall
        have hc_mem : cols.getD j.val 0 ∈ cols := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hlt := hclt _ hc_mem
        obtain ⟨hcm_lt, hor_lt, hcm_b, hor_b⟩ := hcm_bits pi hpi (cols.getD j.val 0) hlt
        simp only [beq_iff_eq] at hcm_lt hor_lt hcm_b hor_b
        rcases hall _ hc_mem with h1 | h2
        · obtain ⟨v, hvK, hvcol⟩ := (hM_spec.2 _ hcm_lt).mp h1
          refine ⟨v, hvK, fun i => ?_⟩
          rw [← hcol_bit v (pFun ⟨i.val, by omega⟩), hvcol]
          dsimp only [pFun]; rw [hcm_b i.val i.isLt]
        · obtain ⟨v, hvK, hvcol⟩ := (hM_spec.2 _ hor_lt).mp h2
          refine ⟨v, hvK, fun i => ?_⟩
          rw [← hcol_bit v (pFun ⟨i.val, by omega⟩), hvcol]
          dsimp only [pFun]; rw [hor_b i.val i.isLt]
      have hget4 : ∀ (cols : List ℕ) (k : ℕ), cols.length = k → (∀ c ∈ cols, c < 16) →
          (cols.all fun c => (M >>> permCol pi c) % 2 == 1) = true →
          ∀ j : Fin k, ∃ v ∈ K, col v = permCol pi (cols.getD j.val 0) := by
        intro cols k hlen hclt hall j
        simp only [List.all_eq_true, beq_iff_eq] at hall
        have hc_mem : cols.getD j.val 0 ∈ cols := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hpc_lt : permCol pi (cols.getD j.val 0) < 16 := by
          have : ∀ q < 24, ∀ c < 16, permCol q c < 16 := by decide
          exact this pi hpi _ (hclt _ hc_mem)
        exact (hM_spec.2 _ hpc_lt).mp (hall _ hc_mem)
      unfold forbSat at hfsat
      interval_cases kind
      · -- kind = 0: T1
        exact hT1 (hbuild3 [5, 3, 6, 0] 4 rfl (by decide) (hget3 [5, 3, 6, 0] 4 rfl (by decide) hfsat) (by decide))
      · -- kind = 1: T2
        exact hT2 (hbuild3 [7, 1, 2, 4] 4 rfl (by decide) (hget3 [7, 1, 2, 4] 4 rfl (by decide) hfsat) (by decide))
      · -- kind = 2: T3
        exact hT3 (hbuild3 [5, 3, 7, 6] 4 rfl (by decide) (hget3 [5, 3, 7, 6] 4 rfl (by decide) hfsat) (by decide))
      · -- kind = 3: T4
        exact hT4 (hbuild4 [9, 3, 15, 6] 4 rfl (by decide) (hget4 [9, 3, 15, 6] 4 rfl (by decide) hfsat) (by decide))
      · -- kind = 4: T5
        exact hT5 (hbuild4 [9, 3, 6, 12, 0] 5 rfl (by decide) (hget4 [9, 3, 6, 12, 0] 5 rfl (by decide) hfsat) (by decide))
      · -- kind = 5: T6
        exact hT6 (hbuild4 [1, 11, 7, 4, 8] 5 rfl (by decide) (hget4 [1, 11, 7, 4, 8] 5 rfl (by decide) hfsat) (by decide))
      · -- kind = 6: T7
        exact hT7 (hbuild4 [9, 3, 5, 10, 12] 5 rfl (by decide) (hget4 [9, 3, 5, 10, 12] 5 rfl (by decide) hfsat) (by decide))
      · -- kind = 7: T8
        exact hT8 (hbuild4 [11, 7, 9, 5, 2] 5 rfl (by decide) (hget4 [11, 7, 9, 5, 2] 5 rfl (by decide) hfsat) (by decide))
      · -- kind = 8: D1
        exact hD1 (hbuild4 [3, 2, 5, 4, 9, 8] 6 rfl (by decide) (hget4 [3, 2, 5, 4, 9, 8] 6 rfl (by decide) hfsat) (by decide))
      · -- kind = 9: T1swap (a moves to K, b,c,d stay in E)
        have hwit := hget4 [7, 11, 13] 3 rfl (by decide) hfsat
        obtain ⟨v7, hv7K, hv7c⟩ := hwit 0
        obtain ⟨v11, hv11K, hv11c⟩ := hwit 1
        obtain ⟨v13, hv13K, hv13c⟩ := hwit 2
        -- Map graphT1 (E=0..2, K=3..6 with cols [5,3,6,0]) to:
        -- 0 -> eV(pFun 1), 1 -> eV(pFun 2), 2 -> eV(pFun 3),
        -- 3 -> v11, 4 -> v7, 5 -> v13, 6 -> eV(pFun 0)
        have hadj_v : ∀ (v : V) (c : ℕ), c < 16 → col v = permCol pi c →
            ∀ i : Fin 4, G.Adj (eV (pFun i)) v ↔ (c >>> i.val) % 2 = 1 := by
          intro v c hclt hvc i
          rw [← hcol_bit v (pFun i), hvc]
          dsimp only [pFun]; rw [permCol_bit pi hpi c hclt i.val i.isLt]
        have h7_adj := hadj_v v7 7 (by decide) hv7c
        have h11_adj := hadj_v v11 11 (by decide) hv11c
        have h13_adj := hadj_v v13 13 (by decide) hv13c
        have hv11_ne_v7 : v11 ≠ v7 := fun h => by
          have := (h11_adj 2).mp (h ▸ (h7_adj 2).mpr (by decide)); revert this; decide
        have hv11_ne_v13 : v11 ≠ v13 := fun h => by
          have := (h13_adj 1).mp (h.symm ▸ (h11_adj 1).mpr (by decide)); revert this; decide
        have hv7_ne_v13 : v7 ≠ v13 := fun h => by
          have := (h7_adj 3).mp (h ▸ (h13_adj 3).mpr (by decide)); revert this; decide
        let e' : Fin 3 → V := fun i => eV (pFun ⟨i.val + 1, by omega⟩)
        let k' : Fin 4 → V := fun j =>
          if j.val = 0 then v11 else if j.val = 1 then v7 else if j.val = 2 then v13 else eV (pFun 0)
        have hf_ne_EK : ∀ (i : Fin 4) (v : V), v ∈ K → eV (pFun i) ≠ v := fun i v hvK h =>
          Finset.disjoint_left.mp hDisj (h ▸ heV_mem _) hvK
        have he'_indep : ∀ i1 i2 : Fin 3, ¬ G.Adj (e' i1) (e' i2) := fun i1 i2 =>
          hEindep _ (heV_mem _) _ (heV_mem _)
        have hk'_clique : ∀ j1 j2 : Fin 4, j1 ≠ j2 → G.Adj (k' j1) (k' j2) := by
          intro j1 j2 hne
          fin_cases j1 <;> fin_cases j2
          · exact absurd rfl hne
          · exact hKclique _ hv11K _ hv7K hv11_ne_v7
          · exact hKclique _ hv11K _ hv13K hv11_ne_v13
          · exact SimpleGraph.Adj.symm ((h11_adj 0).mpr (by decide))
          · exact hKclique _ hv7K _ hv11K hv11_ne_v7.symm
          · exact absurd rfl hne
          · exact hKclique _ hv7K _ hv13K hv7_ne_v13
          · exact SimpleGraph.Adj.symm ((h7_adj 0).mpr (by decide))
          · exact hKclique _ hv13K _ hv11K hv11_ne_v13.symm
          · exact hKclique _ hv13K _ hv7K hv7_ne_v13.symm
          · exact absurd rfl hne
          · exact SimpleGraph.Adj.symm ((h13_adj 0).mpr (by decide))
          · exact (h11_adj 0).mpr (by decide)
          · exact (h7_adj 0).mpr (by decide)
          · exact (h13_adj 0).mpr (by decide)
          · exact absurd rfl hne
        have hek'_adj : ∀ (j : Fin 4) (i : Fin 3),
            G.Adj (e' i) (k' j) ↔ (([5, 3, 6, 0].getD j.val 0) >>> i.val) % 2 = 1 := by
          intro j i
          fin_cases j
          · change G.Adj (eV (pFun ⟨i.val + 1, by omega⟩)) v11 ↔ _
            rw [h11_adj ⟨i.val + 1, by omega⟩]; dsimp only; fin_cases i <;> decide
          · change G.Adj (eV (pFun ⟨i.val + 1, by omega⟩)) v7 ↔ _
            rw [h7_adj ⟨i.val + 1, by omega⟩]; dsimp only; fin_cases i <;> decide
          · change G.Adj (eV (pFun ⟨i.val + 1, by omega⟩)) v13 ↔ _
            rw [h13_adj ⟨i.val + 1, by omega⟩]; dsimp only; fin_cases i <;> decide
          · change G.Adj (eV (pFun ⟨i.val + 1, by omega⟩)) (eV (pFun 0)) ↔ _
            constructor
            · intro h; exact absurd h (hEindep _ (heV_mem _) _ (heV_mem _))
            · intro h; exfalso; fin_cases i <;> revert h <;> decide
        have hek'_ne : ∀ (i : Fin 3) (j : Fin 4), e' i ≠ k' j := by
          intro i j hxy
          fin_cases j
          · exact hf_ne_EK _ _ hv11K hxy
          · exact hf_ne_EK _ _ hv7K hxy
          · exact hf_ne_EK _ _ hv13K hxy
          · have := hpFun_inj (heV_inj hxy)
            have hval := congrArg Fin.val this; dsimp only at hval; omega
        let f : Fin (3 + 4) → V := fun x =>
          if h : x.val < 3 then e' ⟨x.val, h⟩ else k' ⟨x.val - 3, by omega⟩
        have hf_inj : Function.Injective f := by
          intro x y hxy
          dsimp only [f] at hxy
          split_ifs at hxy with hx hy hy
          · have := hpFun_inj (heV_inj hxy)
            exact Fin.ext (by have hval := congrArg Fin.val this; dsimp only at hval; omega)
          · exact absurd hxy (hek'_ne _ _)
          · exact absurd hxy.symm (hek'_ne _ _)
          · have hkj : (⟨x.val - 3, by omega⟩ : Fin 4) = ⟨y.val - 3, by omega⟩ := by
              by_contra hne
              exact G.loopless.irrefl _ (hxy ▸ hk'_clique _ _ hne)
            exact Fin.ext (by have hval := congrArg Fin.val hkj; dsimp only at hval; omega)
        apply hT1
        refine ⟨⟨f, hf_inj⟩, fun u v => ?_⟩
        simp only [Function.Embedding.coeFn_mk]
        dsimp only [graphT1, mkSplitGraph, f]
        by_cases hu : u.val < 3 <;> by_cases hv : v.val < 3
        · rw [dif_pos hu, dif_pos hv]
          constructor
          · rintro ⟨_, h⟩; rcases h with ⟨h1, _⟩ | ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> omega
          · intro hadj; exact absurd hadj (he'_indep _ _)
        · rw [dif_pos hu, dif_neg hv]
          have hne : u ≠ v := fun h => hv (h ▸ hu)
          have hge : 3 ≤ v.val := by omega
          have hiff := hek'_adj ⟨v.val - 3, by omega⟩ ⟨u.val, hu⟩
          constructor
          · rintro ⟨_, h⟩
            rcases h with ⟨h1, _⟩ | ⟨_, _, h3⟩ | ⟨h1, _, _⟩
            · omega
            · exact hiff.mpr h3
            · omega
          · intro hadj
            exact ⟨hne, Or.inr (Or.inl ⟨hu, hge, hiff.mp hadj⟩)⟩
        · rw [dif_neg hu, dif_pos hv]
          have hne : u ≠ v := fun h => hu (h ▸ hv)
          have hge : 3 ≤ u.val := by omega
          have hiff := hek'_adj ⟨u.val - 3, by omega⟩ ⟨v.val, hv⟩
          constructor
          · rintro ⟨_, h⟩
            rcases h with ⟨_, h2⟩ | ⟨h1, _, _⟩ | ⟨_, _, h3⟩
            · omega
            · omega
            · exact SimpleGraph.Adj.symm (hiff.mpr h3)
          · intro hadj
            exact ⟨hne, Or.inr (Or.inr ⟨hv, hge, hiff.mp (SimpleGraph.Adj.symm hadj)⟩)⟩
        · rw [dif_neg hu, dif_neg hv]
          have hgeu : 3 ≤ u.val := by omega
          have hgev : 3 ≤ v.val := by omega
          constructor
          · rintro ⟨hne, _⟩
            exact hk'_clique _ _ (fun h => hne (Fin.ext (by have hval := congrArg Fin.val h; dsimp only at hval; omega)))
          · intro hadj
            exact ⟨fun h => by subst h; exact G.loopless.irrefl _ hadj, Or.inl ⟨hgeu, hgev⟩⟩
    · -- Covered by orbit `oidx` with permutation `pi`: construct representing word!
      have hp_bij := s4Perms_bij pi hpi
      let pFun : Fin 4 → Fin 4 := fun i => ⟨(s4Perms.getD pi [0, 1, 2, 3]).getD i.val 0, hp_bij.1 i.val i.isLt⟩
      have hpFun_inj : Function.Injective pFun := fun i j h =>
        Fin.ext (hp_bij.2 i.val i.isLt j.val j.isLt (congrArg Fin.val h))
      have hpFun_surj : Function.Surjective pFun := (Finite.injective_iff_surjective).mp hpFun_inj
      have horb := (List.all_eq_true.mp all_orbitWords_ok) oidx (List.mem_range.mpr hoidx)
      unfold checkOrbitWord at horb
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
        list_contains_iff_mem, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at horb
      obtain ⟨⟨⟨⟨⟨hk8, hw_cov⟩, hw_lt⟩, hE_alt⟩, hK_alt⟩, hEK_alt⟩ := horb
      let cols := orbitCols.getD oidx []
      let w0 := orbitWords.getD oidx []
      -- Map each letter `a : ℕ` (for `a < 12`) to a list of vertices in `V`:
      -- `a < 4` -> `[eV (pFun ⟨a, _⟩)]`
      -- `4 ≤ a < 12` -> `(K.toList).filter (fun v => col v == permCol pi (cols.getD (a - 4) 0))`
      let f : ℕ → List V := fun a =>
        if h : a < 4 then [eV (pFun ⟨a, h⟩)]
        else if a < 12 then K.toList.filter (fun v => col v == permCol pi (cols.getD (a - 4) 0))
        else []
      have hf_nodup : ∀ a, (f a).Nodup := by
        intro a; dsimp only [f]
        split_ifs
        · exact List.nodup_singleton _
        · exact List.Nodup.filter _ K.nodup_toList
        · exact List.nodup_nil
      have hpermCol_inj : ∀ j1 < 8, ∀ j2 < 8,
          permCol pi (cols.getD j1 0) = permCol pi (cols.getD j2 0) → j1 = j2 := by
        intro j1 hj1 j2 hj2 heq
        apply orbitCols_nodup oidx hoidx j1 hj1 j2 hj2
        have hlt1 := orbitCols_lt16 oidx hoidx j1 hj1
        have hlt2 := orbitCols_lt16 oidx hoidx j2 hj2
        have hb : ∀ i < 4, (((orbitCols.getD oidx []).getD j1 0) >>> i) % 2 = (((orbitCols.getD oidx []).getD j2 0) >>> i) % 2 := by
          intro i hi
          rw [← permCol_bit pi hpi _ hlt1 i hi, ← permCol_bit pi hpi _ hlt2 i hi]
          exact congrArg (fun x => (x >>> (s4Perms.getD pi [0, 1, 2, 3]).getD i 0) % 2) heq
        have h4 : ∀ a b : ℕ, a < 16 → b < 16 → (∀ i < 4, (a >>> i) % 2 = (b >>> i) % 2) → a = b := by
          intro a b ha hb hbit
          have h0 := hbit 0 (by omega); have h1 := hbit 1 (by omega)
          have h2 := hbit 2 (by omega); have h3 := hbit 3 (by omega)
          simp only [Nat.shiftRight_eq_div_pow] at h0 h1 h2 h3
          norm_num at h0 h1 h2 h3
          omega
        exact h4 _ _ hlt1 hlt2 hb
      have hf_disj : ∀ a b, a ≠ b → ∀ z ∈ f a, z ∉ f b := by
        intro a b hab z hza hzb
        dsimp only [f] at hza hzb
        split_ifs at hza hzb with ha4 hb4 hb12 ha12 hb4' hb12'
        · simp only [List.mem_singleton] at hza hzb
          have := hpFun_inj (heV_inj (hza.symm.trans hzb))
          exact hab (congrArg Fin.val this)
        · simp only [List.mem_singleton] at hza
          have hzK : z ∈ K := Finset.mem_toList.mp (List.mem_filter.mp hzb).1
          exact Finset.disjoint_left.mp hDisj (hza ▸ heV_mem _) hzK
        · simp at hzb
        · simp only [List.mem_singleton] at hzb
          have hzK : z ∈ K := Finset.mem_toList.mp (List.mem_filter.mp hza).1
          exact Finset.disjoint_left.mp hDisj (hzb ▸ heV_mem _) hzK
        · have hc1 : col z = permCol pi (cols.getD (a - 4) 0) := beq_iff_eq.mp (List.mem_filter.mp hza).2
          have hc2 : col z = permCol pi (cols.getD (b - 4) 0) := beq_iff_eq.mp (List.mem_filter.mp hzb).2
          have := hpermCol_inj (a - 4) (by omega) (b - 4) (by omega) (hc1.symm.trans hc2)
          omega
        · simp at hzb
        · simp at hza
        · simp at hza
        · simp at hza
      -- Every `v : V` belongs to `f a` for some `a < 12`!
      have hv_class : ∀ v : V, ∃ a < 12, v ∈ f a := by
        intro v
        have hvU : v ∈ E ∪ K := by rw [hUniv]; exact Finset.mem_univ v
        rcases Finset.mem_union.mp hvU with hvE | hvK
        · obtain ⟨i0, hi0⟩ := hE_surj v hvE
          obtain ⟨i, rfl⟩ := hpFun_surj i0
          refine ⟨i.val, by omega, ?_⟩
          simp [f, i.isLt, hi0]
        · have hMc : (M >>> col v) % 2 = 1 := (hM_spec.2 (col v) (hcol_lt v)).mpr ⟨v, hvK, rfl⟩
          have hpm := hcov (col v) (hcol_lt v) hMc
          obtain ⟨j, hj8, hj_eq⟩ := permMask_mem_iff oidx hoidx pi hpi (col v) (hcol_lt v) hpm
          refine ⟨4 + j, by omega, ?_⟩
          have hnot4 : ¬ (4 + j < 4) := by omega
          have hlt12 : 4 + j < 12 := by omega
          simp only [f, hnot4, hlt12, ↓reduceDIte, ↓reduceIte, List.mem_filter, Finset.mem_toList,
            beq_iff_eq, Nat.add_sub_cancel_left]
          exact ⟨hvK, hj_eq.symm⟩
      -- Present the expanded word `w0.flatMap f`!
      refine ⟨w0.flatMap f, ?_, ?_⟩
      · intro v
        obtain ⟨a, ha12, hva⟩ := hv_class v
        rw [List.mem_flatMap]
        exact ⟨a, hw_cov a (by omega), hva⟩
      · intro u v huv
        obtain ⟨a, ha12, hua⟩ := hv_class u
        obtain ⟨b, hb12, hvb⟩ := hv_class v
        by_cases hab : a = b
        · subst hab
          have hnot4 : ¬ a < 4 := by
            intro ha4
            simp only [f, ha4, ↓reduceDIte, List.mem_singleton] at hua hvb
            exact huv (hua.trans hvb.symm)
          have huK : u ∈ K := by
            simp only [f, hnot4, ha12, ↓reduceDIte, ↓reduceIte, List.mem_filter, Finset.mem_toList] at hua
            exact hua.1
          have hvK : v ∈ K := by
            simp only [f, hnot4, ha12, ↓reduceDIte, ↓reduceIte, List.mem_filter, Finset.mem_toList] at hvb
            exact hvb.1
          exact ⟨fun _ => flatMap_same_alternates w0 f u v a hf_disj hf_nodup hua hvb huv,
                 fun _ => hKclique u huK v hvK huv⟩
        · have halt_iff : Alternates (w0.flatMap f) u v ↔ altBool w0 a b = true := by
            rw [altBool_iff]
            unfold Alternates
            rw [flatMap_filter_pair w0 f u v a b hf_disj hf_nodup hua hvb hab]
            exact noAdjEq_map_iff _ (by
              intro x hx y hy hxy
              have hxm := (List.mem_filter.mp hx).2
              have hym := (List.mem_filter.mp hy).2
              simp only [decide_eq_true_eq] at hxm hym
              rcases hxm with rfl | rfl <;> rcases hym with rfl | rfl
              · rfl
              · simp [Ne.symm hab] at hxy; exact absurd hxy huv
              · simp [Ne.symm hab] at hxy; exact absurd hxy.symm huv
              · rfl)
          rw [halt_iff]
          by_cases ha4 : a < 4 <;> by_cases hb4 : b < 4
          · simp only [f, ha4, hb4, ↓reduceDIte, List.mem_singleton] at hua hvb
            subst hua; subst hvb
            have hno : altBool w0 a b = false := (hE_alt a ha4 b hb4).resolve_left hab
            rw [hno]; simp only [Bool.false_eq_true, iff_false]
            exact hEindep _ (heV_mem _) _ (heV_mem _)
          · simp only [f, ha4, hb4, hb12, ↓reduceDIte, ↓reduceIte, List.mem_singleton,
              List.mem_filter, Finset.mem_toList, beq_iff_eq] at hua hvb
            subst hua
            have halt_e := hEK_alt a ha4 (b - 4) (by omega)
            rw [show 4 + (b - 4) = b by omega] at halt_e
            rw [halt_e, beq_iff_eq, ← hcol_bit v (pFun ⟨a, ha4⟩), hvb.2]
            dsimp only [pFun]
            rw [permCol_bit pi hpi _ (orbitCols_lt16 oidx hoidx (b - 4) (by omega)) a ha4]
          · simp only [f, ha4, hb4, ha12, ↓reduceDIte, ↓reduceIte, List.mem_singleton,
              List.mem_filter, Finset.mem_toList, beq_iff_eq] at hua hvb
            subst hvb
            have halt_sym : altBool w0 a b = altBool w0 b a := by
              apply Bool.eq_iff_iff.mpr; rw [altBool_iff, altBool_iff]; unfold Alternates
              have : (fun z : ℕ => decide (z = a ∨ z = b)) = (fun z : ℕ => decide (z = b ∨ z = a)) := by
                ext z; simp [or_comm]
              rw [this]
            rw [halt_sym]
            have halt_e := hEK_alt b hb4 (a - 4) (by omega)
            rw [show 4 + (a - 4) = a by omega] at halt_e
            rw [halt_e, beq_iff_eq, G.adj_comm, ← hcol_bit u (pFun ⟨b, hb4⟩), hua.2]
            dsimp only [pFun]
            rw [permCol_bit pi hpi _ (orbitCols_lt16 oidx hoidx (a - 4) (by omega)) b hb4]
          · simp only [f, ha4, hb4, ha12, hb12, ↓reduceDIte, ↓reduceIte, List.mem_filter, Finset.mem_toList] at hua hvb
            have halt_k : altBool w0 (4 + (a - 4)) (4 + (b - 4)) = true :=
              (hK_alt (a - 4) (by omega) (b - 4) (by omega)).resolve_left (by omega)
            rw [show 4 + (a - 4) = a by omega, show 4 + (b - 4) = b by omega] at halt_k
            rw [halt_k]; simp only [iff_true]
            exact hKclique u hua.1 v hvb.1 huv

end OMA.P_arxiv_2507_08483

theorem OMA.solution : type_of% @OMA.S_arxiv_2507_08483.main :=
  OMA.P_arxiv_2507_08483.main_proof
