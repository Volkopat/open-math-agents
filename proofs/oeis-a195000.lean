import OMAStatements.S_oeis_a195000

namespace OMA.S_oeis_a195000

open Finset




/-! ## Arrays whose condition compares neighboring entries by their difference

The cells are 0..N-1 and the arrays are z : Fin N → ℕ. The search places cells N-1, N-2, ..., 0
(each new value first in a list, so z 0 is placed last); `back s` lists the steps j < s of the
neighbors already placed when the cell of step s is placed, and R is the condition on the
difference of two neighboring values. -/

section Arrays

variable (back : ℕ → List ℕ) (R : ℤ → Prop) [DecidablePred R]

/-- The value v of the cell of step t agrees with the values y placed before it (y 0 placed
last). -/
def Cn (t v : ℕ) (y : Fin t → ℕ) : Prop :=
  ∀ j ∈ back t, ∀ h : j < t, R ((v : ℤ) - y ⟨t - 1 - j, by omega⟩)

/-- All cells agree with their neighbors placed before them. -/
def V : (t : ℕ) → (Fin t → ℕ) → Prop
  | 0, _ => True
  | t + 1, z => V t (Fin.tail z) ∧ Cn back R t (z 0) (Fin.tail z)

lemma fin_val_eq {n : ℕ} (z : Fin n → ℕ) (a b : ℕ) (ha : a < n) (hb : b < n) (h : a = b) :
    z ⟨a, ha⟩ = z ⟨b, hb⟩ := by
  subst h
  rfl

lemma V_all : ∀ (L : ℕ) (z : Fin L → ℕ), V back R L z ↔
    ∀ s (hs : s < L), ∀ j ∈ back s, ∀ h : j < s,
      R ((z ⟨L - 1 - s, by omega⟩ : ℤ) - z ⟨L - 1 - j, by omega⟩)
  | 0, z => by simp [V]
  | L + 1, z => by
    rw [V, V_all L (Fin.tail z)]
    simp only [Cn, Fin.tail]
    constructor
    · rintro ⟨h1, h2⟩ s hs j hj hjs
      rcases Nat.lt_or_ge s L with h | h
      · have := h1 s h j hj hjs
        rw [fin_val_eq z (L + 1 - 1 - s) (L - 1 - s + 1) (by omega) (by omega) (by omega),
          fin_val_eq z (L + 1 - 1 - j) (L - 1 - j + 1) (by omega) (by omega) (by omega)]
        exact this
      · have hsL : s = L := by omega
        subst hsL
        have := h2 j hj hjs
        rw [fin_val_eq z (s + 1 - 1 - s) 0 (by omega) (by omega) (by omega),
          fin_val_eq z (s + 1 - 1 - j) (s - 1 - j + 1) (by omega) (by omega) (by omega)]
        exact this
    · intro H
      refine ⟨fun s hs j hj hjs => ?_, fun j hj hjs => ?_⟩
      · have := H s (by omega) j hj hjs
        rw [fin_val_eq z (L + 1 - 1 - s) (L - 1 - s + 1) (by omega) (by omega) (by omega),
          fin_val_eq z (L + 1 - 1 - j) (L - 1 - j + 1) (by omega) (by omega) (by omega)] at this
        exact this
      · have := H L (by omega) j hj hjs
        rw [fin_val_eq z (L + 1 - 1 - L) 0 (by omega) (by omega) (by omega),
          fin_val_eq z (L + 1 - 1 - j) (L - 1 - j + 1) (by omega) (by omega) (by omega)] at this
        exact this

instance (t v : ℕ) (y : Fin t → ℕ) : Decidable (Cn back R t v y) := by
  unfold Cn; infer_instance

instance decV : ∀ t, DecidablePred (V back R t)
  | 0 => fun _ => by unfold V; infer_instance
  | t + 1 => fun z => by
    unfold V
    haveI := decV t
    infer_instance

/-- The check of `Cn` that the search runs, on the list of the values placed (newest first). -/
def cB (t v : ℕ) (L : List ℕ) : Bool :=
  (back t).all (fun j => !(decide (j < t)) || decide (R ((v : ℤ) - L.getD (t - 1 - j) 0)))

lemma getD_ofFn {t : ℕ} (y : Fin t → ℕ) (i : ℕ) (h : i < t) : (List.ofFn y).getD i 0 = y ⟨i, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

lemma cB_iff (t v : ℕ) (y : Fin t → ℕ) : cB back R t v (List.ofFn y) = true ↔ Cn back R t v y := by
  unfold cB Cn
  rw [List.all_eq_true]
  constructor
  · intro H j hj hjt
    have := H j hj
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
      not_lt] at this
    rcases this with h | h
    · omega
    · rwa [getD_ofFn y (t - 1 - j) (by omega)] at h
  · intro H j hj
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
      not_lt]
    rcases Nat.lt_or_ge j t with h | h
    · right
      rw [getD_ofFn y (t - 1 - j) (by omega)]
      exact H j hj h
    · left
      exact h

/-- The number of ways to place the remaining r cells (values below M) after the list L. -/
def dfs (M : ℕ) : ℕ → ℕ → List ℕ → ℕ
  | 0, _, _ => 1
  | r + 1, t, L => ∑ v : Fin M, if cB back R t v L then dfs M r (t + 1) ((v : ℕ) :: L) else 0

lemma V_cons (t : ℕ) (v : ℕ) (y : Fin t → ℕ) :
    V back R (t + 1) (Fin.cons v y) ↔ V back R t y ∧ Cn back R t v y := by
  simp only [V, Fin.tail_cons, Fin.cons_zero]

lemma dfs_eq (M N : ℕ) : ∀ (r t : ℕ), t + r = N →
    ∑ y : Fin t → Fin M, (if V back R t (fun i => (y i : ℕ)) then
      dfs back R M r t (List.ofFn (fun i => (y i : ℕ))) else 0) =
    (univ.filter (fun z : Fin N → Fin M => V back R N (fun i => (z i : ℕ)))).card
  | 0, t, h => by
    subst h
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y _
    simp only [dfs, Nat.add_zero]
  | r + 1, t, h => by
    rw [← dfs_eq M N r (t + 1) (by omega), ← (Fin.consEquiv (fun _ => Fin M)).sum_comp,
      Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp only [dfs]
    have e1 : ∀ v : Fin M, (fun i => ((Fin.consEquiv (fun _ => Fin M) (v, y)) i : ℕ)) =
        Fin.cons (v : ℕ) (fun i => (y i : ℕ)) := by
      intro v
      funext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [Fin.consEquiv]
    simp only [e1, V_cons, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    by_cases hV : V back R t (fun i => (y i : ℕ))
    · simp only [hV, if_true, true_and]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hc : Cn back R t v (fun i => (y i : ℕ))
      · rw [if_pos ((cB_iff back R t v _).2 hc), if_pos hc]
      · rw [if_neg (fun h => hc ((cB_iff back R t v _).1 h)), if_neg hc]
    · simp only [hV, if_false, false_and]
      simp

/-- The arrays with values below M whose cells all agree with their neighbors, by the search. -/
lemma card_eq_dfs (M N : ℕ) :
    (univ.filter (fun z : Fin N → Fin M => V back R N (fun i => (z i : ℕ)))).card =
      dfs back R M N 0 [] := by
  rw [← dfs_eq back R M N N 0 (by omega)]
  rw [Fintype.sum_unique]
  simp [V]

/-- Adding a constant to every value keeps the condition. -/
lemma V_add (N k : ℕ) (z : Fin N → ℕ) : V back R N (fun i => z i + k) ↔ V back R N z := by
  rw [V_all, V_all]
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  apply forall_congr'
  intro j
  apply forall_congr'
  intro _
  apply forall_congr'
  intro _
  push_cast
  ring_nf

/-- Array positions a, b hold neighbors (one of them placed before the other). -/
def edge (N : ℕ) (a b : ℕ) : Prop :=
  (N - 1 - b ∈ back (N - 1 - a) ∧ N - 1 - b < N - 1 - a) ∨
    (N - 1 - a ∈ back (N - 1 - b) ∧ N - 1 - a < N - 1 - b)

instance (N a b : ℕ) : Decidable (edge back N a b) := by unfold edge; infer_instance

lemma V_edge (N : ℕ) (z : Fin N → ℕ) (hz : V back R N z) (a b : Fin N) (h : edge back N a b) :
    R ((z a : ℤ) - z b) ∨ R ((z b : ℤ) - z a) := by
  rw [V_all] at hz
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have := hz (N - 1 - a) (by omega) (N - 1 - b) h1 h2
    rwa [fin_val_eq z (N - 1 - (N - 1 - a)) a (by omega) a.2 (by omega),
      fin_val_eq z (N - 1 - (N - 1 - b)) b (by omega) b.2 (by omega)] at this
  · right
    have := hz (N - 1 - b) (by omega) (N - 1 - a) h1 h2
    rwa [fin_val_eq z (N - 1 - (N - 1 - b)) b (by omega) b.2 (by omega),
      fin_val_eq z (N - 1 - (N - 1 - a)) a (by omega) a.2 (by omega)] at this

/-- Values at distance at most dist a b along neighbors differ by at most d dist a b. -/
lemma bound (N d : ℕ) (dist : ℕ → ℕ → ℕ) (hR : ∀ δ, R δ → |δ| ≤ d)
    (hzero : ∀ a b : Fin N, dist a b = 0 → a = b)
    (hstep : ∀ a b : Fin N, 0 < dist a b → ∃ c : Fin N, edge back N a c ∧ dist c b + 1 = dist a b)
    (z : Fin N → ℕ) (hz : V back R N z) :
    ∀ k (a b : Fin N), dist a b = k → |(z a : ℤ) - z b| ≤ d * k := by
  intro k
  induction k with
  | zero =>
    intro a b h
    rw [hzero a b h]
    simp
  | succ k ih =>
    intro a b h
    obtain ⟨c, hc, hcb⟩ := hstep a b (by omega)
    have h1 := ih c b (by omega)
    have h2 : |(z a : ℤ) - z c| ≤ d := by
      rcases V_edge back R N z hz a c hc with h | h
      · exact hR _ h
      · have := hR _ h
        rwa [abs_sub_comm] at this
    calc |(z a : ℤ) - z b| = |((z a : ℤ) - z c) + ((z c : ℤ) - z b)| := by ring_nf
      _ ≤ |(z a : ℤ) - z c| + |(z c : ℤ) - z b| := abs_add_le _ _
      _ ≤ d + d * k := add_le_add h2 h1
      _ = d * (k + 1) := by ring
      _ = d * ((k + 1 : ℕ) : ℤ) := by push_cast; ring

/-- The arrays with values in 0..m. -/
def cnt (N m : ℕ) : ℕ :=
  (univ.filter (fun z : Fin N → Fin (m + 1) => V back R N (fun i => (z i : ℕ)))).card

/-- The arrays with values in 0..m that take the value 0. -/
def cnt0 (N m : ℕ) : ℕ :=
  (univ.filter (fun z : Fin N → Fin (m + 1) =>
    V back R N (fun i => (z i : ℕ)) ∧ ∃ i, z i = 0)).card

lemma cnt_succ (N m : ℕ) : cnt back R N (m + 1) = cnt back R N m + cnt0 back R N (m + 1) := by
  unfold cnt cnt0
  rw [← Finset.card_filter_add_card_filter_not (fun z : Fin N → Fin (m + 2) => ∃ i, z i = 0),
    Finset.filter_filter, Finset.filter_filter, add_comm]
  congr 1
  symm
  apply Finset.card_bij (fun y _ => fun i => (y i).succ)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    refine ⟨?_, fun ⟨i, hi⟩ => Fin.succ_ne_zero _ hi⟩
    have := (V_add back R N 1 (fun i => (y i : ℕ))).2 hy
    simpa using this
  · intro y _ y' _ h
    funext i
    exact Fin.succ_injective _ (congrFun h i)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hz
    obtain ⟨hV, h0⟩ := hz
    refine ⟨fun i => (z i).pred (h0 i), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← V_add back R N 1]
      convert hV using 2 with i
      rw [← Fin.val_succ, Fin.succ_pred]
    · funext i
      exact Fin.succ_pred (z i) (h0 i)

lemma cnt0_stable (N m D : ℕ) (hD : D ≤ m)
    (hb : ∀ z : Fin N → ℕ, V back R N z → ∀ a b : Fin N, (z a : ℤ) - z b ≤ D) :
    cnt0 back R N (m + 1) = cnt0 back R N m := by
  unfold cnt0
  symm
  apply Finset.card_bij (fun y _ => fun i => (y i).castSucc)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    obtain ⟨hV, i, hi⟩ := hy
    exact ⟨by simpa using hV, i, by rw [hi]; rfl⟩
  · intro y _ y' _ h
    funext i
    exact Fin.castSucc_injective _ (congrFun h i)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    obtain ⟨hV, i0, hi0⟩ := hz
    have hle : ∀ a, (z a : ℕ) < m + 1 := by
      intro a
      have := hb _ hV a i0
      rw [hi0] at this
      simp at this
      omega
    refine ⟨fun a => ⟨z a, hle a⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hV, i0, ?_⟩
      ext
      simp [hi0]
    · funext a
      ext
      simp

/-- From the first D values and the stability of the arrays taking the value 0. -/
lemma lin_of (c b : ℕ → ℕ) (D : ℕ) (hs : ∀ m, c (m + 1) = c m + b (m + 1))
    (hb : ∀ m, D ≤ m → b (m + 1) = b m) : ∀ p, c (D + p) = c D + p * b D := by
  have hb' : ∀ p, b (D + p) = b D := by
    intro p
    induction p with
    | zero => rfl
    | succ p ih => rw [← Nat.add_assoc, hb (D + p) (by omega), ih]
  intro p
  induction p with
  | zero => simp
  | succ p ih =>
    rw [← Nat.add_assoc, hs, ih, show D + p + 1 = D + (p + 1) by ring, hb' (p + 1)]
    ring

end Arrays

/-- For each step (cells placed from the last in row-major order), the steps of its
neighbors placed before it. -/
def backTab : List (List ℕ) :=
  [[], [0], [1], [2], [1], [2, 4], [3, 5], [5], [6, 7], [8]]

def bk (t : ℕ) : List ℕ := backTab.getD t []

def Rel (δ : ℤ) : Prop := δ.natAbs = 1

instance : DecidablePred Rel := fun δ => by unfold Rel; infer_instance

instance (p q : {p : Fin 4 × Fin 4 // p.2 ≤ p.1}) : Decidable (Nbr p q) := by unfold Nbr; infer_instance

/-- Distances in the neighbor graph, by row-major index. -/
def distTab : List (List ℕ) :=
  [[0, 1, 2, 2, 3, 4, 3, 4, 5, 6],
   [1, 0, 1, 1, 2, 3, 2, 3, 4, 5],
   [2, 1, 0, 2, 1, 2, 3, 2, 3, 4],
   [2, 1, 2, 0, 1, 2, 1, 2, 3, 4],
   [3, 2, 1, 1, 0, 1, 2, 1, 2, 3],
   [4, 3, 2, 2, 1, 0, 3, 2, 1, 2],
   [3, 2, 3, 1, 2, 3, 0, 1, 2, 3],
   [4, 3, 2, 2, 1, 2, 1, 0, 1, 2],
   [5, 4, 3, 3, 2, 1, 2, 1, 0, 1],
   [6, 5, 4, 4, 3, 2, 3, 2, 1, 0]]

def dst (a b : ℕ) : ℕ := (distTab.getD a []).getD b 0

/-- The row-major index of a cell. -/
def idx (p : {p : Fin 4 × Fin 4 // p.2 ≤ p.1}) : Fin 10 :=
  ⟨(p.1.1 * (p.1.1 + 1) / 2 + p.1.2) % 10, Nat.mod_lt _ (by norm_num)⟩

lemma idx_bij : Function.Bijective idx := by
  decide +kernel

noncomputable def eC : {p : Fin 4 × Fin 4 // p.2 ≤ p.1} ≃ Fin 10 := Equiv.ofBijective idx idx_bij

lemma tab_nbr : ∀ p q : {p : Fin 4 × Fin 4 // p.2 ≤ p.1}, Nbr p q ↔ edge bk 10 (idx p) (idx q) := by
  decide +kernel

lemma tab_zero : ∀ a b : Fin 10, dst a b = 0 → a = b := by
  decide +kernel

lemma tab_step : ∀ a b : Fin 10, 0 < dst a b →
    ∃ c : Fin 10, edge bk 10 a c ∧ dst c b + 1 = dst a b := by
  decide +kernel

lemma tab_diam : ∀ a b : Fin 10, dst a b ≤ 6 := by
  decide +kernel

lemma good_iff {n : ℕ} (x : {p : Fin 4 × Fin 4 // p.2 ≤ p.1} → Fin (n + 1)) :
    Good x ↔ V bk Rel 10 (fun i => (x (eC.symm i) : ℕ)) := by
  constructor
  · intro hx
    rw [V_all]
    intro s hs j hj hjs
    have he : edge bk 10 (idx (eC.symm ⟨10 - 1 - s, by omega⟩))
        (idx (eC.symm ⟨10 - 1 - j, by omega⟩)) := by
      have h1 : idx (eC.symm ⟨10 - 1 - s, by omega⟩) = ⟨10 - 1 - s, by omega⟩ := Equiv.ofBijective_apply_symm_apply idx idx_bij _
      have h2 : idx (eC.symm ⟨10 - 1 - j, by omega⟩) = ⟨10 - 1 - j, by omega⟩ := Equiv.ofBijective_apply_symm_apply idx idx_bij _
      rw [h1, h2]
      left
      refine ⟨?_, by simp only; omega⟩
      rw [show 10 - 1 - (10 - 1 - j) = j by omega, show 10 - 1 - (10 - 1 - s) = s by omega]
      exact hj
    exact hx _ _ ((tab_nbr _ _).2 he)
  · intro hV p q hpq
    have := V_edge bk Rel 10 _ hV (idx p) (idx q) ((tab_nbr p q).1 hpq)
    have hp : eC.symm (idx p) = p := Equiv.ofBijective_symm_apply_apply idx idx_bij p
    have hq : eC.symm (idx q) = q := Equiv.ofBijective_symm_apply_apply idx idx_bij q
    simp only [hp, hq, Rel] at this
    rcases this with h | h
    · exact h
    · have e := Int.natAbs_neg ((x q : ℤ) - x p)
      rw [neg_sub] at e
      rw [e]
      exact h

lemma a_cnt (n : ℕ) : a n = cnt bk Rel 10 n := by
  unfold a cnt
  rw [Nat.card_congr (Equiv.subtypeEquiv
    (q := fun z : Fin 10 → Fin (n + 1) => V bk Rel 10 (fun i => (z i : ℕ)))
    (Equiv.arrowCongr eC (Equiv.refl _)) (fun x => good_iff x)), Nat.card_eq_fintype_card,
    Fintype.card_subtype]

lemma diff_le (z : Fin 10 → ℕ) (hz : V bk Rel 10 z) (a b : Fin 10) : (z a : ℤ) - z b ≤ 6 := by
  have := bound bk Rel 10 1 dst
    (fun δ h => by unfold Rel at h; rw [Int.abs_eq_natAbs, h]) tab_zero tab_step z hz
    (dst a b) a b rfl
  have h2 := tab_diam a b
  have h3 := le_abs_self ((z a : ℤ) - z b)
  push_cast at this
  omega

lemma c0 : cnt bk Rel 10 0 = 0 := by
  rw [cnt, card_eq_dfs]
  decide +kernel

lemma c1 : cnt bk Rel 10 1 = 2 := by
  rw [cnt, card_eq_dfs]
  decide +kernel

lemma c2 : cnt bk Rel 10 2 = 80 := by
  rw [cnt, card_eq_dfs]
  decide +kernel

lemma c3 : cnt bk Rel 10 3 = 248 := by
  rw [cnt, card_eq_dfs]
  decide +kernel

lemma c4 : cnt bk Rel 10 4 = 458 := by
  rw [cnt, card_eq_dfs]
  decide +kernel

lemma c5 : cnt bk Rel 10 5 = 672 := by
  rw [cnt, card_eq_dfs]
  decide +kernel

lemma c6 : cnt bk Rel 10 6 = 888 := by
  rw [cnt, card_eq_dfs]
  decide +kernel

/-- a(n) for n ≥ 6. -/
theorem a_lin (p : ℕ) : a (6 + p) = 888 + p * 216 := by
  have h := lin_of (cnt bk Rel 10) (cnt0 bk Rel 10) 6 (cnt_succ bk Rel 10)
    (fun m hm => cnt0_stable bk Rel 10 m 6 hm diff_le) p
  have h0 : cnt0 bk Rel 10 6 = 216 := by
    have e := cnt_succ bk Rel 10 5
    rw [show (5 + 1 : ℕ) = 6 from rfl, c6, c5] at e
    omega
  rw [a_cnt, h, h0, c6]

/-- The values a(0..T). -/
theorem small : a 0 = 0 ∧ a 1 = 2 ∧ a 2 = 80 ∧ a 3 = 248 ∧ a 4 = 458 ∧ a 5 = 672 ∧ a 6 = 888 ∧ a 7 = 1104 ∧ a 8 = 1320 ∧ a 9 = 1536 ∧ a 10 = 1752 ∧ a 11 = 1968 ∧ a 12 = 2184 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_cnt]; exact c0
  · rw [a_cnt]; exact c1
  · rw [a_cnt]; exact c2
  · rw [a_cnt]; exact c3
  · rw [a_cnt]; exact c4
  · rw [a_cnt]; exact c5
  · rw [a_cnt]; exact c6
  · rw [show 7 = 6 + 1 from rfl, a_lin]
  · rw [show 8 = 6 + 2 from rfl, a_lin]
  · rw [show 9 = 6 + 3 from rfl, a_lin]
  · rw [show 10 = 6 + 4 from rfl, a_lin]
  · rw [show 11 = 6 + 5 from rfl, a_lin]
  · rw [show 12 = 6 + 6 from rfl, a_lin]

/-- Barker's closed form, for n > 4. -/
theorem closed (n : ℕ) (hn : 4 < n) : (a n : ℤ) = 24 * (9 * n - 17) := by
  rcases Nat.lt_or_ge n 6 with h | h
  · obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
    interval_cases n <;> simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] <;> norm_num
  · obtain ⟨p, rfl⟩ : ∃ p, n = 6 + p := ⟨n - 6, by omega⟩
    rw [a_lin]
    push_cast
    ring

/-- Barker's recurrence, for n > 6. -/
theorem recurrence (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  rcases Nat.lt_or_ge n 8 with h | h
  · obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
    interval_cases n <;> simp only [Nat.reduceSub, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12] <;> norm_num
  · obtain ⟨p, rfl⟩ : ∃ p, n = 6 + (2 + p) := ⟨n - (6 + 2), by omega⟩
    rw [show 6 + (2 + p) - 1 = 6 + (1 + p) by omega, show 6 + (2 + p) - 2 = 6 + (0 + p) by omega, a_lin, a_lin, a_lin]
    push_cast
    ring

open PowerSeries in
/-- Barker's g.f., with a(0) = 0. -/
theorem gf : mk (fun n => (a n : ℤ)) * (1 - X) ^ 2 = 2 * X * (1 + 38 * X + 45 * X ^ 2 + 21 * X ^ 3 + 2 * X ^ 4 + X ^ 5) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have hD : A * (1 - X) ^ 2 = A - C 2 * (A * X ^ 1) + A * X ^ 2 := by
    simp only [map_ofNat]; ring
  have hN : (2 * X * (1 + 38 * X + 45 * X ^ 2 + 21 * X ^ 3 + 2 * X ^ 4 + X ^ 5) : PowerSeries ℤ) =
      C 2 * X ^ 1 + C 76 * X ^ 2 + C 90 * X ^ 3 + C 42 * X ^ 4 + C 4 * X ^ 5 + C 2 * X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge n 13 with h | h
  · interval_cases n <;>
      simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, coeff_C, pow_zero, Nat.zero_le, Nat.sub_zero, Nat.sub_self, if_true, if_false] <;> norm_num
  · have hq := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show n ≠ 1 by omega, show n - 1 ≠ 0 by omega, show n ≠ 2 by omega, show n - 2 ≠ 0 by omega, show n ≠ 3 by omega, show 3 ≤ n by omega, show n - 3 ≠ 0 by omega, show n ≠ 4 by omega, show 4 ≤ n by omega, show n - 4 ≠ 0 by omega, show n ≠ 5 by omega, show 5 ≤ n by omega, show n - 5 ≠ 0 by omega, show n ≠ 6 by omega, show 6 ≤ n by omega, show n - 6 ≠ 0 by omega, coeff_C, if_true, if_false, ite_self]
    linear_combination hq

/-- Controls: the entry's terms a(1..12). -/
theorem controls : a 1 = 2 ∧ a 2 = 80 ∧ a 3 = 248 ∧ a 4 = 458 ∧ a 5 = 672 ∧ a 6 = 888 ∧ a 7 = 1104 ∧ a 8 = 1320 ∧ a 9 = 1536 ∧ a 10 = 1752 ∧ a 11 = 1968 ∧ a 12 = 2184 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩

/-- The problem as the site states it. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 2 = 2 * PowerSeries.X * (1 + 38 * PowerSeries.X + 45 * PowerSeries.X ^ 2 + 21 * PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 5) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 24 * (9 * n - 17)) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) :=
  ⟨gf, closed, recurrence⟩

end OMA.S_oeis_a195000

theorem OMA.solution : type_of% @OMA.S_oeis_a195000.main :=
  OMA.S_oeis_a195000.conjecture
