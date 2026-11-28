import OMAStatements.S_oeis_a229450

/-!
# Transfer systems whose states only move one way

A transfer system on a finite set of states `S` is a family of integer sequences `W m x` with
`W (m + 1) x = ∑ y, w x y * W m y`. Suppose every transition with `w x y ≠ 0` either stays at `x`,
with weight 0 or 1, or strictly raises a rank `ρ`. The transfer matrix is then triangular with
eigenvalues in {0, 1}, and every sequence `m ↦ W m x` agrees with a polynomial from some point on.
`transfer_poly` gives explicit bounds: if a loop count `L` and a nonloop count `N` drop along every
transition as stated there, the `L x`-th forward difference of `m ↦ W m x` vanishes at every
`m ≥ N x` (`PolyFrom`), so `m ↦ W m x` agrees with a polynomial of degree less than `L x` from
`N x` on (`PolyFrom.exists_poly`).

`RowAut` specializes this to deterministic automata that read the rows of an array from the top:
the number of accepted arrays with `n + 1` rows is a polynomial in `n` as soon as every move of the
automaton either keeps its state (for at most one row) or raises the rank (`RowAut.count_poly`).
-/

open Finset

namespace OMA.General

/-- `u` agrees with a polynomial of degree less than `d` from `a` on: its `d`-th forward difference
vanishes at every `m ≥ a`. -/
def PolyFrom (d a : ℕ) (u : ℕ → ℤ) : Prop := ∀ m, a ≤ m → ((fwdDiff 1)^[d] u) m = 0

lemma fwdDiff_iter_vanish {u : ℕ → ℤ} {a : ℕ} (h : ∀ m, a ≤ m → u m = 0) (j : ℕ) :
    ∀ m, a ≤ m → ((fwdDiff 1)^[j] u) m = 0 := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    intro m hm
    rw [Function.iterate_succ_apply', fwdDiff, ih (m + 1) (by omega), ih m hm, sub_zero]

lemma PolyFrom.mono {d a d' a' : ℕ} {u : ℕ → ℤ} (h : PolyFrom d a u) (hd : d ≤ d') (ha : a ≤ a') :
    PolyFrom d' a' u := by
  intro m hm
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  rw [add_comm, Function.iterate_add_apply]
  exact fwdDiff_iter_vanish (fun m hm' => h m hm') e m (by omega)

/-- **A sequence whose `d`-th difference vanishes is a polynomial.** If the `d`-th forward
difference of `n ↦ u (n + c)` vanishes from `a` on, then `u` agrees with a polynomial of degree
less than `d` from `a + c` on (Newton's forward difference formula). -/
theorem PolyFrom.exists_poly {d a : ℕ} (c : ℕ) {u : ℕ → ℤ} (h : PolyFrom d a (fun n => u (n + c))) :
    ∃ P : Polynomial ℚ, P.degree < d ∧ ∀ n, a + c ≤ n → (u n : ℚ) = P.eval (n : ℚ) := by
  set v : ℕ → ℤ := fun n => u (n + c)
  let B : ℕ → Polynomial ℚ := fun i =>
    (Polynomial.C ((i.factorial : ℚ)⁻¹) * descPochhammer ℚ i).comp
      (Polynomial.X - Polynomial.C ((a + c : ℕ) : ℚ))
  refine ⟨∑ i ∈ range d, Polynomial.C (((fwdDiff 1)^[i] v a : ℤ) : ℚ) * B i, ?_, ?_⟩
  · rw [← Polynomial.mem_degreeLT]
    refine Submodule.sum_mem _ (fun i hi => ?_)
    rw [Polynomial.mem_degreeLT]
    have hi' : i < d := Finset.mem_range.1 hi
    have h1 : (Polynomial.C (((fwdDiff 1)^[i] v a : ℤ) : ℚ) * B i).natDegree ≤ i := by
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      refine Polynomial.natDegree_comp_le.trans ?_
      have e1 := (Polynomial.natDegree_C_mul_le ((i.factorial : ℚ)⁻¹) (descPochhammer ℚ i)).trans
        (descPochhammer_natDegree (R := ℚ) i).le
      have e2 := Polynomial.natDegree_X_sub_C_le (((a + c : ℕ) : ℚ))
      calc _ ≤ i * 1 := Nat.mul_le_mul e1 e2
        _ = i := Nat.mul_one i
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast (show _ < d by omega))
  · intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hnewton := shift_eq_sum_fwdDiff_iter (1 : ℕ) v j a
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one] at hnewton
    -- differences of order ≥ d vanish at a
    have hz : ∀ i, d ≤ i → (fwdDiff 1)^[i] v a = 0 := by
      intro i hi
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hi
      rw [add_comm, Function.iterate_add_apply]
      exact fwdDiff_iter_vanish (fun m hm => h m hm) e a le_rfl
    have hsum : ∑ k ∈ range (j + 1), (j.choose k : ℤ) * (fwdDiff 1)^[k] v a =
        ∑ k ∈ range d, (j.choose k : ℤ) * (fwdDiff 1)^[k] v a := by
      have hs1 : ∀ s : Finset ℕ, s ⊆ range (j + 1 + d) →
          (∀ k ∈ range (j + 1 + d), k ∉ s → (j.choose k : ℤ) * (fwdDiff 1)^[k] v a = 0) →
          ∑ k ∈ s, (j.choose k : ℤ) * (fwdDiff 1)^[k] v a =
            ∑ k ∈ range (j + 1 + d), (j.choose k : ℤ) * (fwdDiff 1)^[k] v a :=
        fun s hs hz' => Finset.sum_subset hs hz'
      rw [hs1 (range (j + 1)) (Finset.range_subset_range.2 (by omega)) (fun k _ hk => by
          rw [Nat.choose_eq_zero_of_lt (by simp at hk; omega), Nat.cast_zero, zero_mul]),
        hs1 (range d) (Finset.range_subset_range.2 (by omega)) (fun k _ hk => by
          rw [hz k (by simp at hk; omega), mul_zero])]
    have hu : u (a + c + j) = v (a + j) := by simp only [v]; congr 1; omega
    rw [hu, show a + j = a + j by rfl, hnewton, hsum]
    push_cast
    rw [Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [B, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
      Polynomial.eval_X]
    have e : (a : ℚ) + c + j - ((a + c : ℕ) : ℚ) = (j : ℚ) := by push_cast; ring
    rw [e, descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
    push_cast
    field_simp

/-- A sequence whose `d`-th difference vanishes from `a` on, and which vanishes at the `d` points
`a, ..., a + d - 1`, vanishes from `a` on. -/
theorem PolyFrom.eq_zero {d a : ℕ} {w : ℕ → ℤ} (h : PolyFrom d a w) (h0 : ∀ i < d, w (a + i) = 0) :
    ∀ n, a ≤ n → w n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < a + d
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hn
      exact h0 i (by omega)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
      have hd := h m (by omega)
      rw [fwdDiff_iter_eq_sum_shift, Finset.sum_range_succ] at hd
      have hs : ∑ k ∈ range d, ((-1 : ℤ) ^ (d - k) * d.choose k) • w (m + k • 1) = 0 := by
        refine Finset.sum_eq_zero (fun k hk => ?_)
        have hk' := Finset.mem_range.1 hk
        simp only [smul_eq_mul, mul_one]
        rw [ih (m + k) (by omega) (by omega), mul_zero]
      rw [hs, zero_add] at hd
      simpa using hd

/-- **Lowering the degree from initial terms.** If `u` agrees with a polynomial of degree less than
`d` from `a` on, and its `e`-th difference vanishes at the `d - e` points `a, ..., a + d - e - 1`,
then `u` agrees with a polynomial of degree less than `e` from `a` on. -/
theorem PolyFrom.lower {d e a : ℕ} {u : ℕ → ℤ} (h : PolyFrom d a u) (hed : e ≤ d)
    (h0 : ∀ i < d - e, (fwdDiff 1)^[e] u (a + i) = 0) : PolyFrom e a u := by
  have hw : PolyFrom (d - e) a ((fwdDiff 1)^[e] u) := by
    intro m hm
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hed]
    exact h m hm
  exact fun m hm => hw.eq_zero h0 m hm

lemma fwdDiff_iter_sum {ι : Type*} (s : Finset ι) (c : ι → ℤ) (v : ι → ℕ → ℤ) (j : ℕ) :
    ∀ m, ((fwdDiff 1)^[j] (fun m => ∑ y ∈ s, c y * v y m)) m = ∑ y ∈ s, c y * ((fwdDiff 1)^[j] (v y)) m := by
  induction j with
  | zero => intro m; rfl
  | succ j ih =>
    intro m
    simp only [Function.iterate_succ_apply', fwdDiff, ih, mul_sub, Finset.sum_sub_distrib]

/-- **Transfer systems that only move one way.** -/
theorem transfer_poly {S : Type*} [Fintype S] [DecidableEq S] (w : S → S → ℤ) (W : ℕ → S → ℤ)
    (hW : ∀ m x, W (m + 1) x = ∑ y, w x y * W m y)
    (ρ : S → ℕ) (hρ : ∀ x y, w x y ≠ 0 → y ≠ x → ρ x < ρ y)
    (hloop : ∀ x, w x x = 0 ∨ w x x = 1) (L N : S → ℕ)
    (hL : ∀ x y, w x y ≠ 0 → y ≠ x → (if w x x = 1 then L y + 1 else L y) ≤ L x)
    (hN : ∀ x y, w x y ≠ 0 → y ≠ x → (if w x x = 1 then N y else N y + 1) ≤ N x)
    (hL1 : ∀ x, w x x = 1 → 1 ≤ L x) (hN1 : ∀ x, w x x = 0 → 1 ≤ N x) :
    ∀ x, PolyFrom (L x) (N x) (fun m => W m x) := by
  set R := univ.sup ρ + 1
  have hR : ∀ x, ρ x < R := fun x => Nat.lt_succ_of_le (Finset.le_sup (mem_univ x))
  have hsplit : ∀ m x, W (m + 1) x = w x x * W m x + ∑ y ∈ univ.erase x, w x y * W m y := by
    intro m x
    rw [hW, ← Finset.add_sum_erase _ _ (mem_univ x)]
  have key : ∀ k x, R - ρ x ≤ k → PolyFrom (L x) (N x) (fun m => W m x) := by
    intro k
    induction k with
    | zero => intro x hx; have := hR x; omega
    | succ k ih =>
      intro x _
      have hy : ∀ y, w x y ≠ 0 → y ≠ x → PolyFrom (L y) (N y) (fun m => W m y) :=
        fun y h1 h2 => ih y (by have := hρ x y h1 h2; have := hR y; omega)
      rcases hloop x with h0 | h1
      · intro m hm
        have hN' := hN1 x h0
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [← fwdDiff_iter_comp_add]
        have e : (fun r => W (r + 1) x) = fun r => ∑ y ∈ univ.erase x, w x y * W r y := by
          funext r
          rw [hsplit, h0, zero_mul, zero_add]
        rw [e, fwdDiff_iter_sum]
        refine Finset.sum_eq_zero (fun y hy' => ?_)
        by_cases hw : w x y = 0
        · rw [hw, zero_mul]
        · have hyx : y ≠ x := Finset.ne_of_mem_erase hy'
          have h1 := hL x y hw hyx
          have h2 := hN x y hw hyx
          rw [h0, if_neg (by norm_num)] at h1 h2
          rw [(hy y hw hyx).mono h1 le_rfl m' (by omega), mul_zero]
      · intro m hm
        obtain ⟨l, hl⟩ : ∃ l, L x = l + 1 := ⟨L x - 1, by have := hL1 x h1; omega⟩
        show ((fwdDiff 1)^[L x] (fun m => W m x)) m = 0
        rw [hl, Function.iterate_succ_apply]
        have e : fwdDiff 1 (fun r => W r x) = fun r => ∑ y ∈ univ.erase x, w x y * W r y := by
          funext r
          simp only [fwdDiff]
          rw [hsplit, h1, one_mul]
          ring
        rw [e, fwdDiff_iter_sum]
        refine Finset.sum_eq_zero (fun y hy' => ?_)
        by_cases hw : w x y = 0
        · rw [hw, zero_mul]
        · have hyx : y ≠ x := Finset.ne_of_mem_erase hy'
          have h1' := hL x y hw hyx
          have h2' := hN x y hw hyx
          rw [h1, if_pos rfl] at h1' h2'
          rw [(hy y hw hyx).mono (by omega) le_rfl m (by omega), mul_zero]
  exact fun x => key (R - ρ x) x le_rfl

/-! ## Row automata -/

/-- A deterministic automaton that reads the rows of an array from the top: the first row `s` is
allowed when `startOk s` and leads to the state `start s`; in state `q` the next row `s` is allowed
when `stepOk q s` and leads to `step q s`; an array is accepted when all its rows are allowed and
the last state satisfies `acc`. -/
structure RowAut (Row St : Type*) where
  startOk : Row → Bool
  start : Row → St
  stepOk : St → Row → Bool
  step : St → Row → St
  acc : St → Bool

namespace RowAut

variable {Row St : Type*} (A : RowAut Row St)

/-- The rows `f` may follow the state `q`. -/
def accFrom : (m : ℕ) → St → (Fin m → Row) → Bool
  | 0, q, _ => A.acc q
  | m + 1, q, f => A.stepOk q (f 0) && accFrom m (A.step q (f 0)) (Fin.tail f)

/-- The array with rows `x` is accepted. -/
def accepts : (n : ℕ) → (Fin n → Row) → Bool
  | 0, _ => true
  | n + 1, x => A.startOk (x 0) && A.accFrom n (A.start (x 0)) (Fin.tail x)

variable [Fintype Row] [DecidableEq Row]

/-- The number of ways to continue from the state `q` with `m` more rows. -/
def F (m : ℕ) (q : St) : ℕ := (univ.filter (fun f : Fin m → Row => A.accFrom m q f = true)).card

/-- The number of accepted arrays with `n` rows. -/
def count (n : ℕ) : ℕ := (univ.filter (fun x : Fin n → Row => A.accepts n x = true)).card

lemma card_by_head {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (Q : (Fin (m + 1) → α) → Prop) [DecidablePred Q] :
    (univ.filter Q).card = ∑ v : α, (univ.filter (fun h : Fin m → α => Q (Fin.cons v h))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (m + 1) → α => g 0) (t := univ)
    (by intro x _; simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  symm
  apply Finset.card_bij (fun h _ => (Fin.cons v h : Fin (m + 1) → α))
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨hh, by simp⟩
  · intro h₁ _ h₂ _ e
    simpa using congrArg Fin.tail e
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hq, h0⟩ := hg
    refine ⟨Fin.tail g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h0, Fin.cons_self_tail]
      exact hq
    · show Fin.cons v (Fin.tail g) = g
      rw [← h0, Fin.cons_self_tail]

lemma F_succ (m : ℕ) (q : St) :
    A.F (m + 1) q = ∑ s, if A.stepOk q s = true then A.F m (A.step q s) else 0 := by
  unfold F
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [accFrom, Fin.cons_zero, Fin.tail_cons, Bool.and_eq_true]
  split_ifs with h
  · simp only [h, true_and]
  · simp [h]

lemma count_succ (n : ℕ) :
    A.count (n + 1) = ∑ s, if A.startOk s = true then A.F n (A.start s) else 0 := by
  unfold count
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [accepts, Fin.cons_zero, Fin.tail_cons, Bool.and_eq_true]
  split_ifs with h
  · simp only [h, true_and]; rfl
  · simp [h]

/-- The state `q` has a row that keeps it. -/
def Loop (q : St) : Prop := ∃ s, A.stepOk q s = true ∧ A.step q s = q

instance decLoop [DecidableEq St] (q : St) : Decidable (A.Loop q) := by
  unfold Loop; infer_instance

/-- **Row automata that only move one way.** If every allowed move either keeps the state (for at
most one row) or raises the rank `ρ`, and the counts `L` (loop states) and `N` (other states) drop
along moves as stated, then from every state `q` the number of continuations by `m` rows agrees
with a polynomial in `m` of degree less than `L q` for `m ≥ N q`. -/
theorem F_poly [Fintype St] [DecidableEq St] (ρ : St → ℕ)
    (hρ : ∀ q s, A.stepOk q s = true → A.step q s ≠ q → ρ q < ρ (A.step q s))
    (hone : ∀ q s s', A.stepOk q s = true → A.step q s = q → A.stepOk q s' = true →
      A.step q s' = q → s = s')
    (L N : St → ℕ)
    (hL : ∀ q s, A.stepOk q s = true → A.step q s ≠ q →
      (if A.Loop q then L (A.step q s) + 1 else L (A.step q s)) ≤ L q)
    (hN : ∀ q s, A.stepOk q s = true → A.step q s ≠ q →
      (if A.Loop q then N (A.step q s) else N (A.step q s) + 1) ≤ N q)
    (hL1 : ∀ q, A.Loop q → 1 ≤ L q) (hN1 : ∀ q, ¬ A.Loop q → 1 ≤ N q) :
    ∀ q, PolyFrom (L q) (N q) (fun m => (A.F m q : ℤ)) := by
  classical
  let w : St → St → ℤ := fun q q' =>
    ((univ.filter (fun s => A.stepOk q s = true ∧ A.step q s = q')).card : ℤ)
  have hw0 : ∀ q q', w q q' ≠ 0 → ∃ s, A.stepOk q s = true ∧ A.step q s = q' := by
    intro q q' h
    by_contra hc
    push_neg at hc
    apply h
    simp only [w, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_and]
    exact hc
  have hww : ∀ q, w q q = if A.Loop q then 1 else 0 := by
    intro q
    split_ifs with hq
    · obtain ⟨s, hs1, hs2⟩ := hq
      have : univ.filter (fun s => A.stepOk q s = true ∧ A.step q s = q) = {s} := by
        ext s'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => hone q s' s h.1 h.2 hs1 hs2, fun h => h ▸ ⟨hs1, hs2⟩⟩
      simp only [w, this, Finset.card_singleton, Nat.cast_one]
    · simp only [w, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
        Finset.mem_univ, true_implies]
      exact fun s hs => hq ⟨s, hs⟩
  have hiff : ∀ q, w q q = 1 ↔ A.Loop q := by
    intro q; rw [hww]; split_ifs with h <;> simp [h]
  refine transfer_poly w (fun m q => (A.F m q : ℤ)) ?_ ρ ?_ ?_ L N ?_ ?_ ?_ ?_
  · intro m q
    rw [F_succ]
    push_cast
    rw [← Finset.sum_filter, ← Finset.sum_fiberwise' (univ.filter (fun s => A.stepOk q s = true))
      (A.step q) (fun q' => (A.F m q' : ℤ))]
    refine Finset.sum_congr rfl (fun q' _ => ?_)
    rw [Finset.sum_const, Finset.filter_filter, nsmul_eq_mul]
  · intro q q' h hne
    obtain ⟨s, hs1, rfl⟩ := hw0 q q' h
    exact hρ q s hs1 hne
  · intro q; rw [hww]; split_ifs <;> simp
  · intro q q' h hne
    obtain ⟨s, hs1, rfl⟩ := hw0 q q' h
    have := hL q s hs1 hne
    by_cases hq : A.Loop q
    · rw [if_pos ((hiff q).2 hq)]; rw [if_pos hq] at this; exact this
    · rw [if_neg (fun h => hq ((hiff q).1 h))]; rw [if_neg hq] at this; exact this
  · intro q q' h hne
    obtain ⟨s, hs1, rfl⟩ := hw0 q q' h
    have := hN q s hs1 hne
    by_cases hq : A.Loop q
    · rw [if_pos ((hiff q).2 hq)]; rw [if_pos hq] at this; exact this
    · rw [if_neg (fun h => hq ((hiff q).1 h))]; rw [if_neg hq] at this; exact this
  · intro q h; exact hL1 q ((hiff q).1 h)
  · intro q h
    refine hN1 q (fun hq => ?_)
    rw [hww, if_pos hq] at h
    exact one_ne_zero h

/-- The number of accepted arrays with `n + 1` rows agrees with a polynomial in `n` of degree less
than `d` from `a` on, when every allowed first row leads to a state `q` with `L q ≤ d` and
`N q ≤ a`. -/
theorem count_poly (L N : St → ℕ) (hF : ∀ q, PolyFrom (L q) (N q) (fun m => (A.F m q : ℤ)))
    (d a : ℕ) (hd : ∀ s, A.startOk s = true → L (A.start s) ≤ d)
    (ha : ∀ s, A.startOk s = true → N (A.start s) ≤ a) :
    PolyFrom d a (fun n => (A.count (n + 1) : ℤ)) := by
  intro m hm
  have e : (fun n => (A.count (n + 1) : ℤ)) =
      fun n => ∑ s ∈ univ.filter (fun s => A.startOk s = true), 1 * (A.F n (A.start s) : ℤ) := by
    funext n
    rw [count_succ, Finset.sum_filter]
    push_cast
    simp only [one_mul]
  rw [e, fwdDiff_iter_sum]
  refine Finset.sum_eq_zero (fun s hs => ?_)
  have hs' := (Finset.mem_filter.1 hs).2
  rw [(hF _).mono (hd s hs') (ha s hs') m hm, mul_zero]

/-! ### Reading two rows at a time

When the moves that keep the rank cycle with period 2 (for example column residues mod 3 that a
repeated row permutes), the automaton that reads two rows at a time only moves one way. -/

/-- The automaton that reads two rows at a time. -/
def pair : RowAut (Row × Row) St where
  startOk p := A.startOk p.1 && A.stepOk (A.start p.1) p.2
  start p := A.step (A.start p.1) p.2
  stepOk q p := A.stepOk q p.1 && A.stepOk (A.step q p.1) p.2
  step q p := A.step (A.step q p.1) p.2
  acc := A.acc

@[simp] lemma pair_stepOk (q : St) (p : Row × Row) :
    A.pair.stepOk q p = (A.stepOk q p.1 && A.stepOk (A.step q p.1) p.2) := rfl

@[simp] lemma pair_step (q : St) (p : Row × Row) : A.pair.step q p = A.step (A.step q p.1) p.2 := rfl

@[simp] lemma pair_acc : A.pair.acc = A.acc := rfl

lemma F_zero (q : St) : A.F 0 q = if A.acc q = true then 1 else 0 := by
  unfold F
  have hu : (univ : Finset (Fin 0 → Row)) = {Fin.elim0} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    funext i
    exact i.elim0
  rw [hu, Finset.filter_singleton]
  by_cases h : A.acc q = true <;> simp [accFrom, h]

lemma F_pair (m : ℕ) (q : St) : A.F (2 * m) q = A.pair.F m q := by
  induction m generalizing q with
  | zero => rw [Nat.mul_zero, F_zero, F_zero, pair_acc]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, F_succ, F_succ, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [F_succ]
    split_ifs with h
    · refine Finset.sum_congr rfl (fun s' _ => ?_)
      simp only [pair_stepOk, pair_step, h, Bool.true_and]
      split_ifs
      · rw [ih]
      · rfl
    · symm
      refine Finset.sum_eq_zero (fun s' _ => ?_)
      simp only [pair_stepOk, Bool.and_eq_true]
      exact if_neg (fun h' => h h'.1)

/-- Both parity classes of the number of accepted arrays are polynomials, when the automaton that
reads two rows at a time satisfies the hypotheses of `F_poly`. -/
theorem count_poly_two (L N : St → ℕ) (hF : ∀ q, PolyFrom (L q) (N q) (fun m => (A.pair.F m q : ℤ)))
    (d a : ℕ) (hd1 : ∀ s, A.startOk s = true → L (A.start s) ≤ d)
    (ha1 : ∀ s, A.startOk s = true → N (A.start s) ≤ a)
    (hd2 : ∀ s s', A.startOk s = true → A.stepOk (A.start s) s' = true →
      L (A.step (A.start s) s') ≤ d)
    (ha2 : ∀ s s', A.startOk s = true → A.stepOk (A.start s) s' = true →
      N (A.step (A.start s) s') ≤ a) :
    PolyFrom d a (fun n => (A.count (2 * n + 1) : ℤ)) ∧
      PolyFrom d a (fun n => (A.count (2 * n + 2) : ℤ)) := by
  constructor
  · intro m hm
    have e : (fun n => (A.count (2 * n + 1) : ℤ)) = fun n =>
        ∑ s ∈ univ.filter (fun s => A.startOk s = true), 1 * (A.pair.F n (A.start s) : ℤ) := by
      funext n
      rw [count_succ, Finset.sum_filter]
      push_cast
      simp only [one_mul, F_pair]
    rw [e, fwdDiff_iter_sum]
    refine Finset.sum_eq_zero (fun s hs => ?_)
    have hs' := (Finset.mem_filter.1 hs).2
    rw [(hF _).mono (hd1 s hs') (ha1 s hs') m hm, mul_zero]
  · intro m hm
    have e : (fun n => (A.count (2 * n + 2) : ℤ)) = fun n =>
        ∑ p ∈ univ.filter (fun p : Row × Row => A.startOk p.1 = true ∧
          A.stepOk (A.start p.1) p.2 = true), 1 * (A.pair.F n (A.step (A.start p.1) p.2) : ℤ) := by
      funext n
      rw [show 2 * n + 2 = 2 * n + 1 + 1 by ring, count_succ, Finset.sum_filter,
        Fintype.sum_prod_type]
      push_cast
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [F_succ]
      push_cast
      split_ifs with h
      · refine Finset.sum_congr rfl (fun s' _ => ?_)
        simp only [h, true_and, one_mul, F_pair]
      · symm
        refine Finset.sum_eq_zero (fun s' _ => ?_)
        simp [h]
    rw [e, fwdDiff_iter_sum]
    refine Finset.sum_eq_zero (fun p hp => ?_)
    have hp' := (Finset.mem_filter.1 hp).2
    rw [(hF _).mono (hd2 p.1 p.2 hp'.1 hp'.2) (ha2 p.1 p.2 hp'.1 hp'.2) m hm, mul_zero]

end RowAut

end OMA.General

/-! # Lexicographic order and column statuses, for any width -/

namespace OMA.General

/-- u ≤ v in the lexicographic order: u = v, or at the first index where they differ u is
smaller. -/
def lexLE {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  u = v ∨ ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance

/-- Strict lexicographic order. -/
def lexLT {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

lemma lexLT_cons {m q : ℕ} (a b : Fin q) (u v : Fin m → Fin q) :
    lexLT (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔ a < b ∨ (a = b ∧ lexLT u v) := by
  constructor
  · rintro ⟨i, hi, hlt⟩
    induction i using Fin.cases with
    | zero => left; simpa using hlt
    | succ i =>
      right
      have h0 := hi 0 (Fin.succ_pos i)
      simp only [Fin.cons_zero] at h0
      refine ⟨h0, i, fun j hj => ?_, by simpa using hlt⟩
      have := hi j.succ (Fin.succ_lt_succ_iff.2 hj)
      simpa using this
  · rintro (h | ⟨rfl, i, hi, hlt⟩)
    · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by simpa using h⟩
    · refine ⟨i.succ, fun j hj => ?_, by simpa using hlt⟩
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simpa using hi j (Fin.succ_lt_succ_iff.1 hj)

lemma lexLE_cons {m q : ℕ} (a b : Fin q) (u v : Fin m → Fin q) :
    lexLE (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔ a < b ∨ (a = b ∧ lexLE u v) := by
  have e : lexLE (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔
      (Fin.cons a u : Fin (m + 1) → Fin q) = Fin.cons b v ∨
        lexLT (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) := Iff.rfl
  rw [e, lexLT_cons, Fin.cons_inj]
  unfold lexLE
  change _ ↔ a < b ∨ (a = b ∧ (u = v ∨ lexLT u v))
  tauto

/-- The rank of a word in the lexicographic order: its value in base q, first letter most
significant. -/
def lexRank {q : ℕ} : (m : ℕ) → (Fin m → Fin q) → ℕ
  | 0, _ => 0
  | m + 1, u => (u 0 : ℕ) * q ^ m + lexRank m (Fin.tail u)

lemma lexRank_lt {q : ℕ} : ∀ (m : ℕ) (u : Fin m → Fin q), lexRank m u < q ^ m
  | 0, u => by
    have : 0 < q ^ 0 := by rw [pow_zero]; exact Nat.one_pos
    simpa [lexRank] using this
  | m + 1, u => by
    have h1 := lexRank_lt m (Fin.tail u)
    have h3 : ((u 0 : ℕ) + 1) * q ^ m ≤ q * q ^ m := Nat.mul_le_mul_right _ (u 0).isLt
    rw [lexRank, pow_succ]
    nlinarith

lemma lexRank_lt_of_lexLT {q : ℕ} : ∀ (m : ℕ) (u v : Fin m → Fin q), lexLT u v →
    lexRank m u < lexRank m v
  | 0, _, _, ⟨i, _, _⟩ => i.elim0
  | m + 1, u, v, h => by
    have e := lexLT_cons (u 0) (v 0) (Fin.tail u) (Fin.tail v)
    rw [Fin.cons_self_tail, Fin.cons_self_tail] at e
    rcases e.1 h with h0 | ⟨h0, h1⟩
    · have hu := lexRank_lt m (Fin.tail u)
      have h2 : ((u 0 : ℕ) + 1) * q ^ m ≤ (v 0 : ℕ) * q ^ m := Nat.mul_le_mul_right _ h0
      rw [lexRank, lexRank]
      nlinarith
    · rw [lexRank, lexRank, h0]
      have := lexRank_lt_of_lexLT m _ _ h1
      omega

lemma lexRank_le_of_lexLE {q m : ℕ} {u v : Fin m → Fin q} (h : lexLE u v) :
    lexRank m u ≤ lexRank m v := by
  rcases h with rfl | h
  · exact le_rfl
  · exact (lexRank_lt_of_lexLT m u v h).le

lemma lexLT_of_lexLE_ne {q m : ℕ} {u v : Fin m → Fin q} (h : lexLE u v) (hne : u ≠ v) :
    lexLT u v := h.resolve_left hne

/-- `ord c u v`: u ≤ v lexicographically, or v ≤ u when `c`. -/
def ord {m q : ℕ} : Bool → (Fin m → Fin q) → (Fin m → Fin q) → Prop
  | false, u, v => lexLE u v
  | true, u, v => lexLE v u

instance {m q : ℕ} (c : Bool) : DecidableRel (@ord m q c) := fun u v => by
  cases c <;> unfold ord <;> infer_instance

lemma ord_refl {m q : ℕ} (c : Bool) (u : Fin m → Fin q) : ord c u u := by
  cases c <;> exact Or.inl rfl

/-- The rank along which rows ordered by `ord c` increase. -/
def ordRank {q : ℕ} (c : Bool) (m : ℕ) (u : Fin m → Fin q) : ℕ :=
  if c then q ^ m - 1 - lexRank m u else lexRank m u

lemma ordRank_lt {q : ℕ} (c : Bool) (m : ℕ) (u : Fin m → Fin q) : ordRank c m u < q ^ m := by
  have := lexRank_lt m u
  unfold ordRank
  split_ifs <;> omega

lemma ordRank_le {q m : ℕ} {c : Bool} {u v : Fin m → Fin q} (h : ord c u v) :
    ordRank c m u ≤ ordRank c m v := by
  cases c
  · exact lexRank_le_of_lexLE h
  · have := lexRank_le_of_lexLE h
    have := lexRank_lt m u
    unfold ordRank
    simp only [if_true]
    omega

lemma ordRank_lt_of {q m : ℕ} {c : Bool} {u v : Fin m → Fin q} (h : ord c u v) (hne : u ≠ v) :
    ordRank c m u < ordRank c m v := by
  cases c
  · exact lexRank_lt_of_lexLT m u v (lexLT_of_lexLE_ne h hne)
  · have := lexRank_lt_of_lexLT m v u (lexLT_of_lexLE_ne h (Ne.symm hne))
    have := lexRank_lt m u
    unfold ordRank
    simp only [if_true]
    omega

/-! ## The status of a pair of columns -/

/-- z: the two columns have not differed yet; d: they have, in the right order. -/
inductive T2
  | z
  | d
  deriving DecidableEq

instance : Fintype T2 := ⟨{.z, .d}, fun t => by cases t <;> simp⟩

/-- The rest of two columns u, v after status t. -/
def PT {m q : ℕ} : T2 → (Fin m → Fin q) → (Fin m → Fin q) → Prop
  | .z, u, v => lexLE u v
  | .d, _, _ => True

def okT {q : ℕ} (t : T2) (x y : Fin q) : Prop := t = .z → x ≤ y

def stpT {q : ℕ} (t : T2) (x y : Fin q) : T2 := if x = y then t else .d

lemma stpT_comm {q : ℕ} (t : T2) (x y : Fin q) : stpT t x y = stpT t y x := by
  unfold stpT
  by_cases h : x = y
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

lemma PT_cons {m q : ℕ} (t : T2) (x y : Fin q) (u v : Fin m → Fin q) :
    PT t (Fin.cons x u : Fin (m + 1) → Fin q) (Fin.cons y v) ↔ okT t x y ∧ PT (stpT t x y) u v := by
  by_cases hxy : x = y
  · subst hxy
    rw [show stpT t x x = t from if_pos rfl]
    cases t <;> simp [PT, okT, lexLE_cons]
  · rw [show stpT t x y = .d from if_neg hxy]
    cases t
    · simp only [PT, okT, lexLE_cons, hxy, false_and, or_false, true_implies, and_true]
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hxy⟩
    · simp [PT, okT]

lemma PT_nil {q : ℕ} (t : T2) (u v : Fin 0 → Fin q) : PT t u v := by
  cases t
  · exact Or.inl (funext fun i => i.elim0)
  · trivial

/-- Column pair condition oriented by `c`: `PT t u v`, or `PT t v u` when `c`. -/
def PTo {m q : ℕ} (c : Bool) (t : T2) (u v : Fin m → Fin q) : Prop := if c then PT t v u else PT t u v

def okTo {q : ℕ} (c : Bool) (t : T2) (x y : Fin q) : Prop := if c then okT t y x else okT t x y

instance {q : ℕ} (c : Bool) (t : T2) (x y : Fin q) : Decidable (okTo c t x y) := by
  unfold okTo okT; infer_instance

lemma PTo_cons {m q : ℕ} (c : Bool) (t : T2) (x y : Fin q) (u v : Fin m → Fin q) :
    PTo c t (Fin.cons x u : Fin (m + 1) → Fin q) (Fin.cons y v) ↔
      okTo c t x y ∧ PTo c (stpT t x y) u v := by
  cases c
  · exact PT_cons t x y u v
  · simp only [PTo, okTo, if_true]
    rw [PT_cons, stpT_comm]

lemma PTo_nil {q : ℕ} (c : Bool) (t : T2) (u v : Fin 0 → Fin q) : PTo c t u v := by
  cases c <;> exact PT_nil _ _ _

lemma ord_iff_PTo {m q : ℕ} (c : Bool) (u v : Fin m → Fin q) : ord c u v ↔ PTo c .z u v := by
  cases c <;> rfl

/-! ## Status vectors for rows of length k + 1 -/

/-- Column j of the array f. -/
def col {m k q : ℕ} (f : Fin m → Fin k → Fin q) (j : Fin k) : Fin m → Fin q := fun i => f i j

lemma col_cons {m k q : ℕ} (s : Fin k → Fin q) (g : Fin m → Fin k → Fin q) (j : Fin k) :
    col (Fin.cons s g : Fin (m + 1) → Fin k → Fin q) j = Fin.cons (s j) (col g j) := by
  funext i
  induction i using Fin.cases <;> rfl

/-- The next row s is allowed by the statuses τ. -/
def okR {k q : ℕ} (c : Bool) (τ : Fin k → T2) (s : Fin (k + 1) → Fin q) : Prop :=
  ∀ j : Fin k, okTo c (τ j) (s j.castSucc) (s j.succ)

instance {k q : ℕ} (c : Bool) (τ : Fin k → T2) : DecidablePred (@okR k q c τ) := fun s => by
  unfold okR; infer_instance

/-- The statuses after the row s. -/
def stpR {k q : ℕ} (τ : Fin k → T2) (s : Fin (k + 1) → Fin q) : Fin k → T2 :=
  fun j => stpT (τ j) (s j.castSucc) (s j.succ)

/-- The number of decided column pairs. -/
def nd {k : ℕ} (τ : Fin k → T2) : ℕ := (Finset.univ.filter (fun j => τ j = .d)).card

lemma nd_le {k : ℕ} (τ : Fin k → T2) : nd τ ≤ k := by
  unfold nd
  calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := Finset.card_fin k

lemma stpR_idem {k q : ℕ} (τ : Fin k → T2) (s : Fin (k + 1) → Fin q) :
    stpR (stpR τ s) s = stpR τ s := by
  funext j
  unfold stpR stpT
  split_ifs <;> rfl

lemma okR_stpR {k q : ℕ} (c : Bool) (τ : Fin k → T2) (s : Fin (k + 1) → Fin q) :
    okR c (stpR τ s) s := by
  intro j
  unfold stpR stpT okTo okT
  by_cases h : s j.castSucc = s j.succ
  · rw [h]; cases c <;> simp
  · rw [if_neg h]; cases c <;> simp

lemma nd_stpR {k q : ℕ} (τ : Fin k → T2) (s : Fin (k + 1) → Fin q) (h : stpR τ s ≠ τ) :
    nd τ < nd (stpR τ s) := by
  unfold nd
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · obtain ⟨j, hj⟩ : ∃ j, stpR τ s j ≠ τ j := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      unfold stpR stpT at hj ⊢
      split_ifs at hj ⊢ with h'
      · exact absurd rfl hj
      · rfl
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hd
      apply hj
      unfold stpR stpT
      split_ifs
      · rfl
      · exact hd.symm
  · intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hd
    unfold stpR stpT
    split_ifs
    · exact hd
    · rfl

/-- Adjacent indices of `Fin (k + 1)` are `j.castSucc` and `j.succ` for some `j : Fin k`. -/
lemma adj_cases {k : ℕ} {j j' : Fin (k + 1)} (h : j.val + 1 = j'.val) :
    ∃ i : Fin k, j = i.castSucc ∧ j' = i.succ := by
  have hj : j.val < k := by have := j'.isLt; omega
  exact ⟨⟨j.val, hj⟩, Fin.ext rfl, Fin.ext (by simp; omega)⟩

end OMA.General

/-! # The tables A229445 and A229428: every column (and every row) is a polynomial

`T ch cv rdec cdec n k` counts n X k arrays x with entries 0..2 whose horizontal differences
x i (j + 1) - x i j are never ch mod 3, whose vertical differences x (i + 1) j - x i j are never cv
mod 3, whose rows are lexicographically ordered (nondecreasing from the top, or nonincreasing when
`rdec`) and whose columns are lexicographically ordered (nondecreasing from the left, or
nonincreasing when `cdec`). A229445 is `T 1 (-1) false false` and A229428 is `T 1 (-1) false true`;
transposing an array swaps (ch, rdec) with (cv, cdec).

Main results: for every width k + 1, `n ↦ T ch cv rdec cdec (n + 1) (k + 1)` is a polynomial in n of
degree less than 3 ^ (k + 1) whenever cv is not 0 mod 3 (`T_poly`); hence every column and every
row of A229445 and A229428 is a polynomial (`A229445_column`, `A229445_row`, `A229428_column`,
`A229428_row`).
-/

namespace OMA.General.Mod3

open OMA.General Finset

/-- The arrays counted by `T`. -/
def good (ch cv : ℤ) (rdec cdec : Bool) {n k : ℕ} (x : Fin n → Fin k → Fin 3) : Prop :=
  (∀ i : Fin n, ∀ j j' : Fin k, j.val + 1 = j'.val → ¬ ((x i j' : ℤ) - x i j ≡ ch [ZMOD 3])) ∧
  (∀ i i' : Fin n, ∀ j : Fin k, i.val + 1 = i'.val → ¬ ((x i' j : ℤ) - x i j ≡ cv [ZMOD 3])) ∧
  (∀ i i' : Fin n, i.val + 1 = i'.val → ord rdec (x i) (x i')) ∧
  (∀ j j' : Fin k, j.val + 1 = j'.val → ord cdec (fun i => x i j) (fun i => x i j'))

instance (ch cv : ℤ) (rdec cdec : Bool) {n k : ℕ} : DecidablePred (@good ch cv rdec cdec n k) :=
  fun x => by unfold good; infer_instance

/-- The number of good n X k arrays. -/
def T (ch cv : ℤ) (rdec cdec : Bool) (n k : ℕ) : ℕ :=
  (univ.filter (fun x : Fin n → Fin k → Fin 3 => good ch cv rdec cdec x)).card

lemma good_transpose (ch cv : ℤ) (rdec cdec : Bool) {n k : ℕ} (x : Fin n → Fin k → Fin 3) :
    good ch cv rdec cdec x ↔ good cv ch cdec rdec (fun j i => x i j) := by
  unfold good
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun j i i' hi => h2 i i' j hi, fun j j' i hj => h1 i j j' hj, h4, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun i j j' hj => h2 j j' i hj, fun i i' j hi => h1 j i i' hi, h4, h3⟩

lemma T_transpose (ch cv : ℤ) (rdec cdec : Bool) (n k : ℕ) :
    T ch cv rdec cdec n k = T cv ch cdec rdec k n := by
  unfold T
  apply Finset.card_bij (fun x _ => fun j i => x i j)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (good_transpose ch cv rdec cdec x).1 hx
  · intro x _ y _ e
    funext i j
    exact congrFun (congrFun e j) i
  · intro y hy
    refine ⟨fun i j => y j i, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact (good_transpose cv ch cdec rdec y).1 hy

section width

variable (ch cv : ℤ) (rdec cdec : Bool) {k : ℕ}

/-- The condition inside a row. -/
def hrow (s : Fin (k + 1) → Fin 3) : Prop :=
  ∀ j : Fin k, ¬ ((s j.succ : ℤ) - s j.castSucc ≡ ch [ZMOD 3])

/-- The conditions between a row r and the row s below it. -/
def vcond (r s : Fin (k + 1) → Fin 3) : Prop :=
  (∀ j, ¬ ((s j : ℤ) - r j ≡ cv [ZMOD 3])) ∧ ord rdec r s

instance : DecidablePred (@hrow ch k) := fun s => by unfold hrow; infer_instance

instance (r : Fin (k + 1) → Fin 3) : DecidablePred (@vcond cv rdec k r) := fun s => by
  unfold vcond; infer_instance

/-- Consecutive rows satisfy the conditions between rows. -/
def chain {m : ℕ} (y : Fin m → Fin (k + 1) → Fin 3) : Prop :=
  ∀ i i' : Fin m, i.val + 1 = i'.val → vcond cv rdec (y i) (y i')

/-- The arrays of the transfer, row by row. -/
def core {m : ℕ} (y : Fin m → Fin (k + 1) → Fin 3) : Prop :=
  (∀ i, hrow ch (y i)) ∧ chain cv rdec y ∧ ∀ j : Fin k, PTo cdec .z (col y j.castSucc) (col y j.succ)

/-- The rows f continue the row r validly, when the column pairs have statuses τ after r. -/
def Cont {m : ℕ} (τ : Fin k → T2) (r : Fin (k + 1) → Fin 3) (f : Fin m → Fin (k + 1) → Fin 3) :
    Prop :=
  chain cv rdec (Fin.cons r f : Fin (m + 1) → Fin (k + 1) → Fin 3) ∧ (∀ i, hrow ch (f i)) ∧
    ∀ j : Fin k, PTo cdec (τ j) (col f j.castSucc) (col f j.succ)

lemma good_iff_core {m : ℕ} (x : Fin m → Fin (k + 1) → Fin 3) :
    good ch cv rdec cdec x ↔ core ch cv rdec cdec x := by
  unfold good core chain hrow vcond col
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i j => h1 i j.castSucc j.succ (by simp),
      fun i i' hi => ⟨fun j => h2 i i' j hi, h3 i i' hi⟩,
      fun j => (ord_iff_PTo cdec _ _).1 (h4 j.castSucc j.succ (by simp))⟩
  · rintro ⟨h1, h2, h4⟩
    refine ⟨fun i j j' hj => ?_, fun i i' j hi => (h2 i i' hi).1 j, fun i i' hi => (h2 i i' hi).2,
      fun j j' hj => ?_⟩
    · obtain ⟨jj, rfl, rfl⟩ := adj_cases hj
      exact h1 i jj
    · obtain ⟨jj, rfl, rfl⟩ := adj_cases hj
      exact (ord_iff_PTo cdec _ _).2 (h4 jj)

lemma chain_cons2 {m : ℕ} (r s : Fin (k + 1) → Fin 3) (g : Fin m → Fin (k + 1) → Fin 3) :
    chain cv rdec (Fin.cons r (Fin.cons s g) : Fin (m + 2) → Fin (k + 1) → Fin 3) ↔
      vcond cv rdec r s ∧ chain cv rdec (Fin.cons s g : Fin (m + 1) → Fin (k + 1) → Fin 3) := by
  unfold chain
  constructor
  · intro h
    refine ⟨by simpa using h 0 1 (by simp), fun i j hij => ?_⟩
    have := h i.succ j.succ (by simp [hij])
    simpa using this
  · rintro ⟨h0, h⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j = 0 := by ext; simp at hij; omega
        subst hj
        simpa using h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_succ]
        exact h i j (by simp at hij; omega)

lemma chain_one (y : Fin 1 → Fin (k + 1) → Fin 3) : chain cv rdec y := by
  intro i i' h
  have := i'.isLt
  omega

lemma all_hrow_cons {m : ℕ} (s : Fin (k + 1) → Fin 3) (g : Fin m → Fin (k + 1) → Fin 3) :
    (∀ i, hrow ch ((Fin.cons s g : Fin (m + 1) → Fin (k + 1) → Fin 3) i)) ↔
      hrow ch s ∧ ∀ i, hrow ch (g i) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma Cont_cons {m : ℕ} (τ : Fin k → T2) (r s : Fin (k + 1) → Fin 3)
    (g : Fin m → Fin (k + 1) → Fin 3) :
    Cont ch cv rdec cdec τ r (Fin.cons s g) ↔
      (hrow ch s ∧ vcond cv rdec r s ∧ okR cdec τ s) ∧ Cont ch cv rdec cdec (stpR τ s) s g := by
  unfold Cont okR stpR
  rw [chain_cons2, all_hrow_cons]
  simp only [col_cons, PTo_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    exact ⟨⟨h3, h1, fun j => (h5 j).1⟩, h2, h4, fun j => (h5 j).2⟩
  · rintro ⟨⟨h3, h1, h5⟩, h2, h4, h6⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, fun j => ⟨h5 j, h6 j⟩⟩

lemma Cont_nil (τ : Fin k → T2) (r : Fin (k + 1) → Fin 3) (f : Fin 0 → Fin (k + 1) → Fin 3) :
    Cont ch cv rdec cdec τ r f :=
  ⟨chain_one cv rdec _, fun i => i.elim0, fun _ => PTo_nil _ _ _ _⟩

lemma core_cons {m : ℕ} (s : Fin (k + 1) → Fin 3) (g : Fin m → Fin (k + 1) → Fin 3) :
    core ch cv rdec cdec (Fin.cons s g : Fin (m + 1) → Fin (k + 1) → Fin 3) ↔
      (hrow ch s ∧ okR cdec (fun _ => .z) s) ∧ Cont ch cv rdec cdec (stpR (fun _ => .z) s) s g := by
  unfold core Cont okR stpR
  rw [all_hrow_cons]
  simp only [col_cons, PTo_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, fun j => (h4 j).1⟩, h3, h2, fun j => (h4 j).2⟩
  · rintro ⟨⟨h1, h4⟩, h3, h2, h5⟩
    exact ⟨⟨h1, h2⟩, h3, fun j => ⟨h4 j, h5 j⟩⟩

/-- The automaton: the state is the statuses of the column pairs and the last row. -/
def aut : RowAut (Fin (k + 1) → Fin 3) ((Fin k → T2) × (Fin (k + 1) → Fin 3)) where
  startOk s := decide (hrow ch s ∧ okR cdec (fun _ => .z) s)
  start s := (stpR (fun _ => .z) s, s)
  stepOk q s := decide (hrow ch s ∧ vcond cv rdec q.2 s ∧ okR cdec q.1 s)
  step q s := (stpR q.1 s, s)
  acc _ := true

@[simp] lemma aut_startOk (s : Fin (k + 1) → Fin 3) :
    (aut ch cv rdec cdec).startOk s = decide (hrow ch s ∧ okR cdec (fun _ => .z) s) := rfl

@[simp] lemma aut_start (s : Fin (k + 1) → Fin 3) :
    (aut ch cv rdec cdec).start s = (stpR (fun _ => .z) s, s) := rfl

@[simp] lemma aut_stepOk (q : (Fin k → T2) × (Fin (k + 1) → Fin 3)) (s : Fin (k + 1) → Fin 3) :
    (aut ch cv rdec cdec).stepOk q s = decide (hrow ch s ∧ vcond cv rdec q.2 s ∧ okR cdec q.1 s) :=
  rfl

@[simp] lemma aut_step (q : (Fin k → T2) × (Fin (k + 1) → Fin 3)) (s : Fin (k + 1) → Fin 3) :
    (aut ch cv rdec cdec).step q s = (stpR q.1 s, s) := rfl

@[simp] lemma aut_acc (q : (Fin k → T2) × (Fin (k + 1) → Fin 3)) :
    (aut ch cv rdec cdec).acc q = true := rfl

lemma accFrom_iff : ∀ (m : ℕ) (τ : Fin k → T2) (r : Fin (k + 1) → Fin 3)
    (f : Fin m → Fin (k + 1) → Fin 3),
    (aut ch cv rdec cdec).accFrom m (τ, r) f = true ↔ Cont ch cv rdec cdec τ r f
  | 0, τ, r, f => by
    simp only [RowAut.accFrom, aut_acc, true_iff]
    exact Cont_nil ch cv rdec cdec τ r f
  | m + 1, τ, r, f => by
    rw [← Fin.cons_self_tail f, Cont_cons]
    simp only [RowAut.accFrom, Fin.cons_zero, Fin.tail_cons, Bool.and_eq_true, decide_eq_true_eq,
      aut_stepOk, aut_step]
    rw [accFrom_iff m]

lemma accepts_iff (m : ℕ) (x : Fin (m + 1) → Fin (k + 1) → Fin 3) :
    (aut ch cv rdec cdec).accepts (m + 1) x = true ↔ good ch cv rdec cdec x := by
  rw [good_iff_core, ← Fin.cons_self_tail x, core_cons]
  simp only [RowAut.accepts, Fin.cons_zero, Fin.tail_cons, Bool.and_eq_true, decide_eq_true_eq,
    aut_startOk, aut_start]
  rw [accFrom_iff]

lemma T_eq_count (m : ℕ) :
    T ch cv rdec cdec (m + 1) (k + 1) = (aut ch cv rdec cdec (k := k)).count (m + 1) := by
  unfold T RowAut.count
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, accepts_iff]

/-- After any allowed row the automaton is in a state that the same row keeps. -/
lemma loop_step (hcv : ¬ (0 : ℤ) ≡ cv [ZMOD 3]) (τ : Fin k → T2) (s : Fin (k + 1) → Fin 3)
    (hs : hrow ch s) : (aut ch cv rdec cdec).Loop (stpR τ s, s) := by
  refine ⟨s, ?_, ?_⟩
  · simp only [aut_stepOk, decide_eq_true_eq]
    exact ⟨hs, ⟨fun j => by simpa using hcv, ord_refl rdec s⟩, okR_stpR cdec τ s⟩
  · simp only [aut_step, stpR_idem]

end width

/-- **Every column of the table is a polynomial.** For every width k + 1 (and cv not 0 mod 3),
`n ↦ T ch cv rdec cdec (n + 1) (k + 1)` agrees with a polynomial in n of degree less than
3 ^ (k + 1). -/
theorem T_poly (ch cv : ℤ) (rdec cdec : Bool) (hcv : ¬ (0 : ℤ) ≡ cv [ZMOD 3]) (k : ℕ) :
    PolyFrom (3 ^ (k + 1)) 0 (fun n => (T ch cv rdec cdec (n + 1) (k + 1) : ℤ)) := by
  classical
  set A := aut ch cv rdec cdec (k := k)
  let ρ : (Fin k → T2) × (Fin (k + 1) → Fin 3) → ℕ := fun q =>
    ordRank rdec (k + 1) q.2 * (k + 1) + nd q.1
  let L : (Fin k → T2) × (Fin (k + 1) → Fin 3) → ℕ := fun q =>
    3 ^ (k + 1) - ordRank rdec (k + 1) q.2
  let N : (Fin k → T2) × (Fin (k + 1) → Fin 3) → ℕ := fun q => if A.Loop q then 0 else 1
  have hok : ∀ q s, A.stepOk q s = true → hrow ch s ∧ vcond cv rdec q.2 s ∧ okR cdec q.1 s :=
    fun q s h => by simpa [A] using h
  have hstep : ∀ q s, A.step q s = (stpR q.1 s, s) := fun q s => rfl
  have hkeep : ∀ q s, A.step q s = q → s = q.2 ∧ stpR q.1 s = q.1 := by
    intro q s h
    rw [hstep] at h
    exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
  have hloopq : ∀ q, A.Loop q → stpR q.1 q.2 = q.1 := by
    rintro q ⟨s, _, hs⟩
    obtain ⟨h1, h2⟩ := hkeep q s hs
    rw [← h1]
    exact h2
  have hsucc : ∀ q s, A.stepOk q s = true → A.Loop (A.step q s) := fun q s h =>
    loop_step ch cv rdec cdec hcv q.1 s (hok q s h).1
  have h1 : ∀ q s, A.stepOk q s = true → A.step q s ≠ q → ρ q < ρ (A.step q s) := by
    rintro ⟨τ, r⟩ s hs hne
    have hord : ord rdec r s := (hok (τ, r) s hs).2.1.2
    rw [hstep] at hne ⊢
    simp only [ρ]
    by_cases hsr : s = r
    · subst hsr
      have hτ : stpR τ s ≠ τ := fun h => hne (by rw [h])
      have := nd_stpR τ s hτ
      omega
    · have hlt := ordRank_lt_of hord (Ne.symm hsr)
      have h2 := nd_le τ
      have h3 : (ordRank rdec (k + 1) r + 1) * (k + 1) ≤ ordRank rdec (k + 1) s * (k + 1) :=
        Nat.mul_le_mul_right _ hlt
      nlinarith [nd_le (stpR τ s)]
  have h2 : ∀ q s s', A.stepOk q s = true → A.step q s = q → A.stepOk q s' = true →
      A.step q s' = q → s = s' := by
    intro q s s' _ hs _ hs'
    rw [(hkeep q s hs).1, (hkeep q s' hs').1]
  have h3 : ∀ q s, A.stepOk q s = true → A.step q s ≠ q →
      (if A.Loop q then L (A.step q s) + 1 else L (A.step q s)) ≤ L q := by
    rintro ⟨τ, r⟩ s hs hne
    have hord : ord rdec r s := (hok (τ, r) s hs).2.1.2
    have hlt := ordRank_lt rdec (k + 1) s
    have hle := ordRank_le hord
    simp only [L, hstep]
    split_ifs with hq
    · have hsr : s ≠ r := by
        rintro rfl
        apply hne
        rw [hstep]
        have := hloopq (τ, s) hq
        simp only at this
        rw [this]
      have := ordRank_lt_of hord (Ne.symm hsr)
      omega
    · omega
  have h4 : ∀ q s, A.stepOk q s = true → A.step q s ≠ q →
      (if A.Loop q then N (A.step q s) else N (A.step q s) + 1) ≤ N q := by
    intro q s hs _
    have e : N (A.step q s) = 0 := if_pos (hsucc q s hs)
    by_cases hq : A.Loop q
    · rw [if_pos hq, e]
      exact Nat.zero_le _
    · rw [if_neg hq, e]
      exact (if_neg hq : N q = 1).ge
  have h5 : ∀ q, A.Loop q → 1 ≤ L q := by
    intro q _
    have := ordRank_lt rdec (k + 1) q.2
    simp only [L]
    omega
  have h6 : ∀ q, ¬ A.Loop q → 1 ≤ N q := by
    intro q hq
    simp only [N]
    rw [if_neg hq]
  have hF := A.F_poly ρ h1 h2 L N h3 h4 h5 h6
  have hc := A.count_poly L N hF (3 ^ (k + 1)) 0 (fun s _ => Nat.sub_le _ _) (fun s hs => by
    have hs0 : hrow ch s ∧ okR cdec (fun _ => .z) s := by simpa [A] using hs
    show (if A.Loop (stpR (fun _ => T2.z) s, s) then 0 else 1) ≤ 0
    rw [if_pos (loop_step ch cv rdec cdec hcv _ s hs0.1)])
  have e : (fun n => (T ch cv rdec cdec (n + 1) (k + 1) : ℤ)) = fun n => (A.count (n + 1) : ℤ) := by
    funext n
    rw [T_eq_count]
  rw [e]
  exact hc

/-- Every row of the table is a polynomial too (transpose; needs ch not 0 mod 3). -/
theorem T_poly_row (ch cv : ℤ) (rdec cdec : Bool) (hch : ¬ (0 : ℤ) ≡ ch [ZMOD 3]) (h : ℕ) :
    PolyFrom (3 ^ (h + 1)) 0 (fun n => (T ch cv rdec cdec (h + 1) (n + 1) : ℤ)) := by
  have e : (fun n => (T ch cv rdec cdec (h + 1) (n + 1) : ℤ)) =
      fun n => (T cv ch cdec rdec (n + 1) (h + 1) : ℤ) := by
    funext n
    rw [T_transpose]
  rw [e]
  exact T_poly cv ch cdec rdec hch h

lemma not_zero_modEq_one : ¬ (0 : ℤ) ≡ 1 [ZMOD 3] := by decide

lemma not_zero_modEq_neg_one : ¬ (0 : ℤ) ≡ -1 [ZMOD 3] := by decide

/-- A229445: every column, n X (k + 1) arrays, is a polynomial in n of degree < 3 ^ (k + 1). -/
theorem A229445_column (k : ℕ) :
    PolyFrom (3 ^ (k + 1)) 0 (fun n => (T 1 (-1) false false (n + 1) (k + 1) : ℤ)) :=
  T_poly 1 (-1) false false not_zero_modEq_neg_one k

/-- A229445: every row, (h + 1) X n arrays, is a polynomial in n of degree < 3 ^ (h + 1). -/
theorem A229445_row (h : ℕ) :
    PolyFrom (3 ^ (h + 1)) 0 (fun n => (T 1 (-1) false false (h + 1) (n + 1) : ℤ)) :=
  T_poly_row 1 (-1) false false not_zero_modEq_one h

/-- A229428: every column is a polynomial in n of degree < 3 ^ (k + 1). -/
theorem A229428_column (k : ℕ) :
    PolyFrom (3 ^ (k + 1)) 0 (fun n => (T 1 (-1) false true (n + 1) (k + 1) : ℤ)) :=
  T_poly 1 (-1) false true not_zero_modEq_neg_one k

/-- A229428: every row is a polynomial in n of degree < 3 ^ (h + 1). -/
theorem A229428_row (h : ℕ) :
    PolyFrom (3 ^ (h + 1)) 0 (fun n => (T 1 (-1) false true (h + 1) (n + 1) : ℤ)) :=
  T_poly_row 1 (-1) false true not_zero_modEq_one h

/-- The polynomials explicitly: for every width k + 1 there is a polynomial P of degree less than
3 ^ (k + 1) with A229445(n, k + 1) = P(n) for every n ≥ 1. -/
theorem A229445_column_poly (k : ℕ) : ∃ P : Polynomial ℚ, P.degree < (3 ^ (k + 1) : ℕ) ∧
    ∀ n, 1 ≤ n → (T 1 (-1) false false n (k + 1) : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨P, hP, hv⟩ :=
    (A229445_column k).exists_poly (u := fun n => (T 1 (-1) false false n (k + 1) : ℤ)) 1
  exact ⟨P, hP, fun n hn => by have := hv n (by omega); push_cast at this; exact this⟩

/-- For every number of rows h + 1 there is a polynomial P of degree less than 3 ^ (h + 1) with
A229445(h + 1, n) = P(n) for every n ≥ 1. -/
theorem A229445_row_poly (h : ℕ) : ∃ P : Polynomial ℚ, P.degree < (3 ^ (h + 1) : ℕ) ∧
    ∀ n, 1 ≤ n → (T 1 (-1) false false (h + 1) n : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨P, hP, hv⟩ :=
    (A229445_row h).exists_poly (u := fun n => (T 1 (-1) false false (h + 1) n : ℤ)) 1
  exact ⟨P, hP, fun n hn => by have := hv n (by omega); push_cast at this; exact this⟩

/-- For every width k + 1 there is a polynomial P of degree less than 3 ^ (k + 1) with
A229428(n, k + 1) = P(n) for every n ≥ 1. -/
theorem A229428_column_poly (k : ℕ) : ∃ P : Polynomial ℚ, P.degree < (3 ^ (k + 1) : ℕ) ∧
    ∀ n, 1 ≤ n → (T 1 (-1) false true n (k + 1) : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨P, hP, hv⟩ :=
    (A229428_column k).exists_poly (u := fun n => (T 1 (-1) false true n (k + 1) : ℤ)) 1
  exact ⟨P, hP, fun n hn => by have := hv n (by omega); push_cast at this; exact this⟩

/-- For every number of rows h + 1 there is a polynomial P of degree less than 3 ^ (h + 1) with
A229428(h + 1, n) = P(n) for every n ≥ 1. -/
theorem A229428_row_poly (h : ℕ) : ∃ P : Polynomial ℚ, P.degree < (3 ^ (h + 1) : ℕ) ∧
    ∀ n, 1 ≤ n → (T 1 (-1) false true (h + 1) n : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨P, hP, hv⟩ :=
    (A229428_row h).exists_poly (u := fun n => (T 1 (-1) false true (h + 1) n : ℤ)) 1
  exact ⟨P, hP, fun n hn => by have := hv n (by omega); push_cast at this; exact this⟩

end OMA.General.Mod3

/-! # Transfer systems with an invariant

The same statements as `transfer_poly` and `RowAut.F_poly`, with every hypothesis required only on
the states of an invariant set that the moves preserve (for example the states reachable from the
first row). -/

namespace OMA.General

open Finset

theorem transfer_poly_inv {S : Type*} [Fintype S] [DecidableEq S] (w : S → S → ℤ) (W : ℕ → S → ℤ)
    (hW : ∀ m x, W (m + 1) x = ∑ y, w x y * W m y)
    (I : S → Prop) (hI : ∀ x y, I x → w x y ≠ 0 → I y)
    (ρ : S → ℕ) (hρ : ∀ x y, I x → w x y ≠ 0 → y ≠ x → ρ x < ρ y)
    (hloop : ∀ x, w x x = 0 ∨ w x x = 1) (L N : S → ℕ)
    (hL : ∀ x y, I x → w x y ≠ 0 → y ≠ x → (if w x x = 1 then L y + 1 else L y) ≤ L x)
    (hN : ∀ x y, I x → w x y ≠ 0 → y ≠ x → (if w x x = 1 then N y else N y + 1) ≤ N x)
    (hL1 : ∀ x, I x → w x x = 1 → 1 ≤ L x) (hN1 : ∀ x, I x → w x x = 0 → 1 ≤ N x) :
    ∀ x, I x → PolyFrom (L x) (N x) (fun m => W m x) := by
  set R := univ.sup ρ + 1
  have hR : ∀ x, ρ x < R := fun x => Nat.lt_succ_of_le (Finset.le_sup (mem_univ x))
  have hsplit : ∀ m x, W (m + 1) x = w x x * W m x + ∑ y ∈ univ.erase x, w x y * W m y := by
    intro m x
    rw [hW, ← Finset.add_sum_erase _ _ (mem_univ x)]
  have key : ∀ k x, I x → R - ρ x ≤ k → PolyFrom (L x) (N x) (fun m => W m x) := by
    intro k
    induction k with
    | zero => intro x _ hx; have := hR x; omega
    | succ k ih =>
      intro x hIx _
      have hy : ∀ y, w x y ≠ 0 → y ≠ x → PolyFrom (L y) (N y) (fun m => W m y) :=
        fun y h1 h2 => ih y (hI x y hIx h1) (by have := hρ x y hIx h1 h2; have := hR y; omega)
      rcases hloop x with h0 | h1
      · intro m hm
        have hN' := hN1 x hIx h0
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [← fwdDiff_iter_comp_add]
        have e : (fun r => W (r + 1) x) = fun r => ∑ y ∈ univ.erase x, w x y * W r y := by
          funext r
          rw [hsplit, h0, zero_mul, zero_add]
        rw [e, fwdDiff_iter_sum]
        refine Finset.sum_eq_zero (fun y hy' => ?_)
        by_cases hw : w x y = 0
        · rw [hw, zero_mul]
        · have hyx : y ≠ x := Finset.ne_of_mem_erase hy'
          have h1 := hL x y hIx hw hyx
          have h2 := hN x y hIx hw hyx
          rw [h0, if_neg (by norm_num)] at h1 h2
          rw [(hy y hw hyx).mono h1 le_rfl m' (by omega), mul_zero]
      · intro m hm
        obtain ⟨l, hl⟩ : ∃ l, L x = l + 1 := ⟨L x - 1, by have := hL1 x hIx h1; omega⟩
        show ((fwdDiff 1)^[L x] (fun m => W m x)) m = 0
        rw [hl, Function.iterate_succ_apply]
        have e : fwdDiff 1 (fun r => W r x) = fun r => ∑ y ∈ univ.erase x, w x y * W r y := by
          funext r
          simp only [fwdDiff]
          rw [hsplit, h1, one_mul]
          ring
        rw [e, fwdDiff_iter_sum]
        refine Finset.sum_eq_zero (fun y hy' => ?_)
        by_cases hw : w x y = 0
        · rw [hw, zero_mul]
        · have hyx : y ≠ x := Finset.ne_of_mem_erase hy'
          have h1' := hL x y hIx hw hyx
          have h2' := hN x y hIx hw hyx
          rw [h1, if_pos rfl] at h1' h2'
          rw [(hy y hw hyx).mono (by omega) le_rfl m (by omega), mul_zero]
  exact fun x hx => key (R - ρ x) x hx le_rfl

namespace RowAut

variable {Row St : Type*} (A : RowAut Row St) [Fintype Row] [DecidableEq Row]

theorem F_poly_inv [Fintype St] [DecidableEq St] (I : St → Prop)
    (hI : ∀ q s, I q → A.stepOk q s = true → I (A.step q s)) (ρ : St → ℕ)
    (hρ : ∀ q s, I q → A.stepOk q s = true → A.step q s ≠ q → ρ q < ρ (A.step q s))
    (hone : ∀ q s s', A.stepOk q s = true → A.step q s = q → A.stepOk q s' = true →
      A.step q s' = q → s = s')
    (L N : St → ℕ)
    (hL : ∀ q s, I q → A.stepOk q s = true → A.step q s ≠ q →
      (if A.Loop q then L (A.step q s) + 1 else L (A.step q s)) ≤ L q)
    (hN : ∀ q s, I q → A.stepOk q s = true → A.step q s ≠ q →
      (if A.Loop q then N (A.step q s) else N (A.step q s) + 1) ≤ N q)
    (hL1 : ∀ q, I q → A.Loop q → 1 ≤ L q) (hN1 : ∀ q, I q → ¬ A.Loop q → 1 ≤ N q) :
    ∀ q, I q → PolyFrom (L q) (N q) (fun m => (A.F m q : ℤ)) := by
  classical
  let w : St → St → ℤ := fun q q' =>
    ((univ.filter (fun s => A.stepOk q s = true ∧ A.step q s = q')).card : ℤ)
  have hw0 : ∀ q q', w q q' ≠ 0 → ∃ s, A.stepOk q s = true ∧ A.step q s = q' := by
    intro q q' h
    by_contra hc
    push_neg at hc
    apply h
    simp only [w, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
      Finset.mem_univ, true_implies, not_and]
    exact hc
  have hww : ∀ q, w q q = if A.Loop q then 1 else 0 := by
    intro q
    split_ifs with hq
    · obtain ⟨s, hs1, hs2⟩ := hq
      have : univ.filter (fun s => A.stepOk q s = true ∧ A.step q s = q) = {s} := by
        ext s'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨fun h => hone q s' s h.1 h.2 hs1 hs2, fun h => h ▸ ⟨hs1, hs2⟩⟩
      simp only [w, this, Finset.card_singleton, Nat.cast_one]
    · simp only [w, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
        Finset.mem_univ, true_implies]
      exact fun s hs => hq ⟨s, hs⟩
  have hiff : ∀ q, w q q = 1 ↔ A.Loop q := by
    intro q; rw [hww]; split_ifs with h <;> simp [h]
  refine transfer_poly_inv w (fun m q => (A.F m q : ℤ)) ?_ I ?_ ρ ?_ ?_ L N ?_ ?_ ?_ ?_
  · intro m q
    rw [F_succ]
    push_cast
    rw [← Finset.sum_filter, ← Finset.sum_fiberwise' (univ.filter (fun s => A.stepOk q s = true))
      (A.step q) (fun q' => (A.F m q' : ℤ))]
    refine Finset.sum_congr rfl (fun q' _ => ?_)
    rw [Finset.sum_const, Finset.filter_filter, nsmul_eq_mul]
  · intro q q' hq h
    obtain ⟨s, hs1, rfl⟩ := hw0 q q' h
    exact hI q s hq hs1
  · intro q q' hq h hne
    obtain ⟨s, hs1, rfl⟩ := hw0 q q' h
    exact hρ q s hq hs1 hne
  · intro q; rw [hww]; split_ifs <;> simp
  · intro q q' hq h hne
    obtain ⟨s, hs1, rfl⟩ := hw0 q q' h
    have := hL q s hq hs1 hne
    by_cases hl : A.Loop q
    · rw [if_pos ((hiff q).2 hl)]; rw [if_pos hl] at this; exact this
    · rw [if_neg (fun h => hl ((hiff q).1 h))]; rw [if_neg hl] at this; exact this
  · intro q q' hq h hne
    obtain ⟨s, hs1, rfl⟩ := hw0 q q' h
    have := hN q s hq hs1 hne
    by_cases hl : A.Loop q
    · rw [if_pos ((hiff q).2 hl)]; rw [if_pos hl] at this; exact this
    · rw [if_neg (fun h => hl ((hiff q).1 h))]; rw [if_neg hl] at this; exact this
  · intro q hq h; exact hL1 q hq ((hiff q).1 h)
  · intro q hq h
    refine hN1 q hq (fun hl => ?_)
    rw [hww, if_pos hl] at h
    exact one_ne_zero h

/-- The number of accepted arrays with `n + 1` rows is a polynomial when the continuations from
every allowed first row are. -/
theorem count_poly_of (d a : ℕ)
    (hF : ∀ s, A.startOk s = true → PolyFrom d a (fun m => (A.F m (A.start s) : ℤ))) :
    PolyFrom d a (fun n => (A.count (n + 1) : ℤ)) := by
  intro m hm
  have e : (fun n => (A.count (n + 1) : ℤ)) =
      fun n => ∑ s ∈ univ.filter (fun s => A.startOk s = true), 1 * (A.F n (A.start s) : ℤ) := by
    funext n
    rw [count_succ, Finset.sum_filter]
    push_cast
    simp only [one_mul]
  rw [e, fwdDiff_iter_sum]
  refine Finset.sum_eq_zero (fun s hs => ?_)
  rw [hF s (Finset.mem_filter.1 hs).2 m hm, mul_zero]

end RowAut

end OMA.General

/-! # Index helpers and the recurrence form of `PolyFrom` -/

namespace OMA.General

open Finset

lemma succ_mk {k : ℕ} (j : ℕ) (h : j < k) :
    (Fin.succ ⟨j, h⟩ : Fin (k + 1)) = ⟨j + 1, by omega⟩ := Fin.ext rfl

lemma castSucc_mk {k : ℕ} (j : ℕ) (h : j < k) :
    (Fin.castSucc ⟨j, h⟩ : Fin (k + 1)) = ⟨j, by omega⟩ := Fin.ext rfl

/-- A `PolyFrom D 0` statement about `n ↦ u (n + 1)` written as the linear recurrence with
characteristic polynomial (x - 1)^D, valid from n = 1 on. -/
lemma recurrence_of_polyFrom {D : ℕ} {u : ℕ → ℤ} (h : PolyFrom D 0 (fun n => u (n + 1))) (n : ℕ)
    (hn : 1 ≤ n) : ∑ j ∈ range (D + 1), (-1 : ℤ) ^ j * (D.choose j : ℤ) * u (n + j) = 0 := by
  have h0 := h (n - 1) (Nat.zero_le _)
  rw [fwdDiff_iter_eq_sum_shift] at h0
  simp only [smul_eq_mul, mul_one] at h0
  have e : ∑ j ∈ range (D + 1), (-1 : ℤ) ^ j * (D.choose j : ℤ) * u (n + j) =
      (-1) ^ D * ∑ j ∈ range (D + 1), (-1 : ℤ) ^ (D - j) * (D.choose j : ℤ) * u (n - 1 + j + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjD : j ≤ D := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have e1 : n - 1 + j + 1 = n + j := by omega
    have e2 : (-1 : ℤ) ^ j = (-1) ^ D * (-1) ^ (D - j) := by
      rw [← pow_add, show D + (D - j) = j + 2 * (D - j) by omega, pow_add, pow_mul]
      norm_num
    rw [e1, e2]
    ring
  rw [e, h0, mul_zero]

end OMA.General

/-! # The rows of A229445 have degree at most their height

Row h of A229445 counts h X n arrays; transposed, these are n X h arrays whose horizontal
differences are never -1 and vertical differences never 1 mod 3, with rows and columns
lexicographically nondecreasing (`T (-1) 1 false false`). Going right such a row stays or steps
up by 1 mod 3, going down an entry stays or steps down by 1 mod 3, so the first entry where the
next row differs must go from 0 to 2. On rows made of a block of 2s followed by a nondecreasing
part (`JInv`: true for every first row and kept by moves) that entry is the first one after the
block of 2s, so every move to a different row makes the block longer (`lead2_drop`), and a chain
of loop states has at most h + 1 states. -/

namespace OMA.General.Mod3

open OMA.General Finset

section rows

variable {k : ℕ}

/-- Once an entry other than 2 has appeared, the row is nondecreasing. -/
def JInv (r : Fin (k + 1) → Fin 3) : Prop :=
  ∀ i : Fin k, (∃ i' : Fin (k + 1), i' ≤ i.castSucc ∧ r i' ≠ 2) → r i.castSucc ≤ r i.succ

/-- The length of the block of 2s at the start of the row. -/
def lead2 (r : Fin (k + 1) → Fin 3) : ℕ := (univ.filter (fun i => ∀ i' ≤ i, r i' = 2)).card

lemma lead2_le (r : Fin (k + 1) → Fin 3) : lead2 r ≤ k + 1 := by
  unfold lead2
  calc _ ≤ (univ : Finset (Fin (k + 1))).card := Finset.card_filter_le _ _
    _ = k + 1 := Finset.card_fin _

lemma rres_step : ∀ a b : Fin 3, ¬ ((b : ℤ) - a ≡ -1 [ZMOD 3]) → b = 2 → a ≠ 2 → a = 1 := by
  decide

lemma rres_wrap : ∀ a b : Fin 3, ¬ ((b : ℤ) - a ≡ -1 [ZMOD 3]) → a ≤ b ∨ (a = 2 ∧ b = 0) := by
  decide

lemma rres_j0 : ∀ a c : Fin 3, ¬ ((c : ℤ) - a ≡ 1 [ZMOD 3]) → a < c → a = 0 ∧ c = 2 := by
  decide

lemma rres_v0 : ∀ a c : Fin 3, ¬ ((c : ℤ) - a ≡ 1 [ZMOD 3]) → c = 0 → a ≤ 1 := by decide

lemma rres_v1 : ∀ a c : Fin 3, ¬ ((c : ℤ) - a ≡ 1 [ZMOD 3]) → c = 1 → 1 ≤ a := by decide

lemma rres_v2 : ∀ a c : Fin 3, ¬ ((c : ℤ) - a ≡ 1 [ZMOD 3]) → c = 2 → a = 2 ∨ a = 0 := by decide

lemma rres_20 : ∀ a : Fin 3, ¬ (((2 : Fin 3) : ℤ) - a ≡ -1 [ZMOD 3]) → a ≠ 0 := by decide

lemma JInv_mono (r : Fin (k + 1) → Fin 3) (hJ : JInv r) (j0 : ℕ) (hj0 : j0 ≤ k)
    (h2 : r ⟨j0, by omega⟩ ≠ 2) :
    ∀ d a (ha : j0 ≤ a) (hb : a + d ≤ k), r ⟨a, by omega⟩ ≤ r ⟨a + d, by omega⟩ := by
  intro d
  induction d with
  | zero => intro a _ _; exact le_rfl
  | succ d ih =>
    intro a ha hb
    have h1 := ih a ha (by omega)
    have h3 := hJ ⟨a + d, by omega⟩ ⟨⟨j0, by omega⟩, by
      simp only [Fin.le_iff_val_le_val, Fin.val_castSucc]; omega, h2⟩
    rw [succ_mk _ (by omega), castSucc_mk _ (by omega)] at h3
    exact h1.trans h3

lemma pre_two (r s : Fin (k + 1) → Fin 3) (hJ : JInv r) (hs : hrow (-1) s) (j0 : Fin (k + 1))
    (hpre : ∀ i < j0, r i = s i) (hr0 : r j0 = 0) (hs0 : s j0 = 2) : ∀ i < j0, r i = 2 := by
  intro i hi
  by_contra hne
  have hi' : i.val < j0.val := hi
  have hp := hJ ⟨j0.val - 1, by omega⟩ ⟨i, by
    simp only [Fin.le_iff_val_le_val, Fin.val_castSucc]; omega, hne⟩
  rw [succ_mk _ (by omega), castSucc_mk _ (by omega)] at hp
  have e : (⟨j0.val - 1 + 1, by omega⟩ : Fin (k + 1)) = j0 := Fin.ext (by simp; omega)
  rw [e, hr0] at hp
  have hz : r ⟨j0.val - 1, by omega⟩ = 0 := le_antisymm hp (Fin.zero_le _)
  have hlt : (⟨j0.val - 1, by omega⟩ : Fin (k + 1)) < j0 := by
    simp only [Fin.lt_iff_val_lt_val]; omega
  have hs' := hs ⟨j0.val - 1, by omega⟩
  rw [succ_mk _ (by omega), castSucc_mk _ (by omega), e, hs0, ← hpre _ hlt, hz] at hs'
  exact hs' (by decide)

lemma lead2_drop (r s : Fin (k + 1) → Fin 3) (hJ : JInv r) (hs : hrow (-1) s)
    (hv : ∀ j, ¬ ((s j : ℤ) - r j ≡ 1 [ZMOD 3])) (hlex : lexLE r s) (hne : s ≠ r) :
    lead2 r + 1 ≤ lead2 s := by
  obtain ⟨j0, hpre, hlt⟩ := lexLT_of_lexLE_ne hlex (Ne.symm hne)
  obtain ⟨hr0, hs0⟩ := rres_j0 _ _ (hv j0) hlt
  have h2 := pre_two r s hJ hs j0 hpre hr0 hs0
  unfold lead2
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨j0, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i' hi'
      rcases lt_or_eq_of_le hi' with h | rfl
      · rw [← hpre i' h]; exact h2 i' h
      · exact hs0
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall]
      exact ⟨j0, le_rfl, by rw [hr0]; decide⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro i' hi'
    have hij : i < j0 := by
      by_contra hc
      push_neg at hc
      have := hi j0 hc
      rw [hr0] at this
      exact absurd this (by decide)
    rw [← hpre i' (lt_of_le_of_lt hi' hij)]
    exact hi i' hi'

lemma JInv_step (r s : Fin (k + 1) → Fin 3) (hJ : JInv r) (hs : hrow (-1) s)
    (hv : ∀ j, ¬ ((s j : ℤ) - r j ≡ 1 [ZMOD 3])) (hlex : lexLE r s) : JInv s := by
  by_cases hne : s = r
  · rw [hne]; exact hJ
  obtain ⟨j0, hpre, hlt⟩ := lexLT_of_lexLE_ne hlex (Ne.symm hne)
  obtain ⟨hr0, hs0⟩ := rres_j0 _ _ (hv j0) hlt
  have h2 := pre_two r s hJ hs j0 hpre hr0 hs0
  have hs2 : ∀ i ≤ j0, s i = 2 := fun i hi => by
    rcases lt_or_eq_of_le hi with h | rfl
    · rw [← hpre i h]; exact h2 i h
    · exact hs0
  rintro c ⟨i', hi', hne'⟩
  rcases rres_wrap _ _ (hs c) with hle | ⟨hc2, hc0⟩
  · exact hle
  · exfalso
    have hij : j0.val < i'.val := by
      by_contra h
      push_neg at h
      exact hne' (hs2 i' (Fin.le_iff_val_le_val.2 h))
    have hic : i'.val ≤ c.val := by
      have := Fin.le_iff_val_le_val.1 hi'
      simpa using this
    have hex : ∃ m, i'.val ≤ m ∧ ∃ hm : m ≤ c.val, s ⟨m, by omega⟩ = 2 := by
      refine ⟨c.val, hic, le_rfl, ?_⟩
      have e : (⟨c.val, by omega⟩ : Fin (k + 1)) = c.castSucc := Fin.ext rfl
      rw [e]
      exact hc2
    classical
    obtain ⟨hm1, hm2, hm3⟩ := Nat.find_spec hex
    set m := Nat.find hex with hmdef
    have hmi : i'.val < m := by
      rcases lt_or_eq_of_le hm1 with h | h
      · exact h
      · exfalso
        apply hne'
        have e : i' = ⟨m, by omega⟩ := Fin.ext h
        rw [e]
        exact hm3
    have hprev : s ⟨m - 1, by omega⟩ ≠ 2 := fun h =>
      Nat.find_min hex (show m - 1 < m by omega) ⟨by omega, by omega, h⟩
    have hh := hs ⟨m - 1, by omega⟩
    rw [succ_mk _ (by omega), castSucc_mk _ (by omega)] at hh
    have em : (⟨m - 1 + 1, by omega⟩ : Fin (k + 1)) = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
    rw [em] at hh
    have h1 : s ⟨m - 1, by omega⟩ = 1 := rres_step _ _ hh hm3 hprev
    have va := rres_v1 _ _ (hv ⟨m - 1, by omega⟩) h1
    have vb := rres_v2 _ _ (hv ⟨m, by omega⟩) hm3
    have vc := rres_v0 _ _ (hv c.succ) hc0
    have mono := JInv_mono r hJ j0.val (by omega) (by
      have : (⟨j0.val, by omega⟩ : Fin (k + 1)) = j0 := Fin.ext rfl
      rw [this, hr0]; decide)
    have m1 := mono 1 (m - 1) (by omega) (by omega)
    have m2 := mono (c.val + 1 - m) m (by omega) (by omega)
    have e1 : (⟨m - 1 + 1, by omega⟩ : Fin (k + 1)) = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
    have e2 : (⟨m + (c.val + 1 - m), by omega⟩ : Fin (k + 1)) = c.succ := Fin.ext (by simp; omega)
    rw [e1] at m1
    rw [e2] at m2
    have hrm : r ⟨m, by omega⟩ = 2 := by
      rcases vb with h | h
      · exact h
      · exfalso
        rw [h] at m1
        have := le_trans va m1
        exact absurd this (by decide)
    rw [hrm] at m2
    have := le_trans m2 vc
    exact absurd this (by decide)

lemma JInv_start (s : Fin (k + 1) → Fin 3) (h0 : okR false (fun _ => .z) s) : JInv s := by
  intro i _
  have := h0 i
  simpa [okTo, okT] using this

end rows

/-- **The rows of A229445 have degree at most their height.** In transposed form: for every
height k + 1, `n ↦ T (-1) 1 false false (n + 1) (k + 1)` agrees with a polynomial in n of degree at
most k + 1. -/
theorem T_poly_rows_sharp (k : ℕ) :
    PolyFrom (k + 2) 0 (fun n => (T (-1) 1 false false (n + 1) (k + 1) : ℤ)) := by
  classical
  set A := aut (-1) 1 false false (k := k)
  have hcv : ¬ (0 : ℤ) ≡ 1 [ZMOD 3] := by decide
  let I : (Fin k → T2) × (Fin (k + 1) → Fin 3) → Prop := fun q => hrow (-1) q.2 ∧ JInv q.2
  let ρ : (Fin k → T2) × (Fin (k + 1) → Fin 3) → ℕ := fun q =>
    ordRank false (k + 1) q.2 * (k + 1) + nd q.1
  let L : (Fin k → T2) × (Fin (k + 1) → Fin 3) → ℕ := fun q => (k + 1 - lead2 q.2) + 1
  let N : (Fin k → T2) × (Fin (k + 1) → Fin 3) → ℕ := fun q => if A.Loop q then 0 else 1
  have hok : ∀ q s, A.stepOk q s = true →
      hrow (-1) s ∧ vcond 1 false q.2 s ∧ okR false q.1 s := fun q s h => by simpa [A] using h
  have hstep : ∀ q s, A.step q s = (stpR q.1 s, s) := fun q s => rfl
  have hkeep : ∀ q s, A.step q s = q → s = q.2 ∧ stpR q.1 s = q.1 := by
    intro q s h
    rw [hstep] at h
    exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
  have hloopq : ∀ q, A.Loop q → stpR q.1 q.2 = q.1 := by
    rintro q ⟨s, _, hs⟩
    obtain ⟨h1, h2⟩ := hkeep q s hs
    rw [← h1]
    exact h2
  have hsucc : ∀ q s, A.stepOk q s = true → A.Loop (A.step q s) := fun q s h =>
    loop_step (-1) 1 false false hcv q.1 s (hok q s h).1
  have hI : ∀ q s, I q → A.stepOk q s = true → I (A.step q s) := by
    rintro ⟨τ, r⟩ s ⟨_, hJ⟩ hs
    obtain ⟨h1, ⟨h2, h3⟩, -⟩ := hok (τ, r) s hs
    exact ⟨h1, JInv_step r s hJ h1 h2 h3⟩
  have h1 : ∀ q s, I q → A.stepOk q s = true → A.step q s ≠ q → ρ q < ρ (A.step q s) := by
    rintro ⟨τ, r⟩ s _ hs hne
    have hord : ord false r s := (hok (τ, r) s hs).2.1.2
    rw [hstep] at hne ⊢
    simp only [ρ]
    by_cases hsr : s = r
    · subst hsr
      have hτ : stpR τ s ≠ τ := fun h => hne (by rw [h])
      have := nd_stpR τ s hτ
      omega
    · have hlt := ordRank_lt_of hord (Ne.symm hsr)
      have h2 := nd_le τ
      have h3 : (ordRank false (k + 1) r + 1) * (k + 1) ≤ ordRank false (k + 1) s * (k + 1) :=
        Nat.mul_le_mul_right _ hlt
      nlinarith [nd_le (stpR τ s)]
  have h2 : ∀ q s s', A.stepOk q s = true → A.step q s = q → A.stepOk q s' = true →
      A.step q s' = q → s = s' := by
    intro q s s' _ hs _ hs'
    rw [(hkeep q s hs).1, (hkeep q s' hs').1]
  have h3 : ∀ q s, I q → A.stepOk q s = true → A.step q s ≠ q →
      (if A.Loop q then L (A.step q s) + 1 else L (A.step q s)) ≤ L q := by
    rintro ⟨τ, r⟩ s ⟨_, hJ⟩ hs hne
    obtain ⟨hs1, ⟨hv, hlex⟩, -⟩ := hok (τ, r) s hs
    have hl := lead2_le s
    simp only [L, hstep]
    split_ifs with hq
    · have hsr : s ≠ r := by
        rintro rfl
        apply hne
        rw [hstep]
        have := hloopq (τ, s) hq
        simp only at this
        rw [this]
      have := lead2_drop r s hJ hs1 hv hlex hsr
      omega
    · by_cases hsr : s = r
      · subst hsr; omega
      · have := lead2_drop r s hJ hs1 hv hlex hsr
        omega
  have h4 : ∀ q s, I q → A.stepOk q s = true → A.step q s ≠ q →
      (if A.Loop q then N (A.step q s) else N (A.step q s) + 1) ≤ N q := by
    intro q s _ hs _
    have e : N (A.step q s) = 0 := if_pos (hsucc q s hs)
    by_cases hq : A.Loop q
    · rw [if_pos hq, e]
      exact Nat.zero_le _
    · rw [if_neg hq, e]
      exact (if_neg hq : N q = 1).ge
  have h5 : ∀ q, I q → A.Loop q → 1 ≤ L q := fun q _ _ => by simp only [L]; omega
  have h6 : ∀ q, I q → ¬ A.Loop q → 1 ≤ N q := by
    intro q _ hq
    simp only [N]
    rw [if_neg hq]
  have hF := A.F_poly_inv I hI ρ h1 h2 L N h3 h4 h5 h6
  have hc := A.count_poly_of (k + 2) 0 (fun s hs => by
    have hs0 : hrow (-1) s ∧ okR false (fun _ => .z) s := by simpa [A] using hs
    have hIs : I (A.start s) := ⟨hs0.1, JInv_start s hs0.2⟩
    refine (hF (A.start s) hIs).mono ?_ ?_
    · show k + 1 - lead2 s + 1 ≤ k + 2
      omega
    · show (if A.Loop (stpR (fun _ => T2.z) s, s) then 0 else 1) ≤ 0
      rw [if_pos (loop_step (-1) 1 false false hcv _ s hs0.1)])
  have e : (fun n => (T (-1) 1 false false (n + 1) (k + 1) : ℤ)) =
      fun n => (A.count (n + 1) : ℤ) := by
    funext n
    rw [T_eq_count]
  rw [e]
  exact hc

/-- A229445: row h + 1 (that is, (h + 1) X n arrays) is a polynomial in n of degree at most h + 1,
for every n ≥ 1. -/
theorem A229445_row_sharp (h : ℕ) : ∃ P : Polynomial ℚ, P.degree < (h + 2 : ℕ) ∧
    ∀ n, 1 ≤ n → (T 1 (-1) false false (h + 1) n : ℚ) = P.eval (n : ℚ) := by
  obtain ⟨P, hP, hv⟩ :=
    (T_poly_rows_sharp h).exists_poly (u := fun n => (T (-1) 1 false false n (h + 1) : ℤ)) 1
  refine ⟨P, hP, fun n hn => ?_⟩
  rw [T_transpose]
  have := hv n (by omega)
  push_cast at this
  exact this

/-- A229445, every row h + 1: Σ_{j=0}^{h+2} (-1)^j C(h + 2, j) A229445(h + 1, n + j) = 0 for every
n ≥ 1 (characteristic polynomial (x - 1)^(h+2)), the entry's "Empirical for row n" recurrences
for all rows at once. -/
theorem A229445_row_recurrence (h n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ range (h + 2 + 1), (-1 : ℤ) ^ j * ((h + 2).choose j : ℤ) *
      (T 1 (-1) false false (h + 1) (n + j) : ℤ) = 0 := by
  have e : ∀ m, (T 1 (-1) false false (h + 1) m : ℤ) = (T (-1) 1 false false m (h + 1) : ℤ) := by
    intro m; rw [T_transpose]
  simp only [e]
  exact recurrence_of_polyFrom (u := fun n => (T (-1) 1 false false n (h + 1) : ℤ))
    (T_poly_rows_sharp h) n hn

end OMA.General.Mod3

namespace OMA.S_oeis_a229450

open PowerSeries Finset


instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance


instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance


/-! ## Lexicographic order on `Fin.cons` -/

/-- Strict lexicographic order. -/
def lexLT {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

lemma lexLT_cons {m q : ℕ} (a b : Fin q) (u v : Fin m → Fin q) :
    lexLT (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔ a < b ∨ (a = b ∧ lexLT u v) := by
  constructor
  · rintro ⟨i, hi, hlt⟩
    induction i using Fin.cases with
    | zero => left; simpa using hlt
    | succ i =>
      right
      have h0 := hi 0 (Fin.succ_pos i)
      simp only [Fin.cons_zero] at h0
      refine ⟨h0, i, fun j hj => ?_, by simpa using hlt⟩
      have := hi j.succ (Fin.succ_lt_succ_iff.2 hj)
      simpa using this
  · rintro (h | ⟨rfl, i, hi, hlt⟩)
    · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by simpa using h⟩
    · refine ⟨i.succ, fun j hj => ?_, by simpa using hlt⟩
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simpa using hi j (Fin.succ_lt_succ_iff.1 hj)

lemma lexLE_cons {m q : ℕ} (a b : Fin q) (u v : Fin m → Fin q) :
    lexLE (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔ a < b ∨ (a = b ∧ lexLE u v) := by
  have e : lexLE (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔
      (Fin.cons a u : Fin (m + 1) → Fin q) = Fin.cons b v ∨
        lexLT (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) := Iff.rfl
  rw [e, lexLT_cons, Fin.cons_inj]
  unfold lexLE
  change _ ↔ a < b ∨ (a = b ∧ (u = v ∨ lexLT u v))
  tauto

/-! ## The status of a pair of columns -/

/-- z: the two columns have not differed yet; d: they have, in the right order. -/
inductive T2
  | z
  | d
  deriving DecidableEq

instance : Fintype T2 := ⟨{.z, .d}, fun t => by cases t <;> simp⟩

/-- The condition that the rest (u, v) of a pair of columns must satisfy after the status t. -/
def PT {m : ℕ} : T2 → (Fin m → Fin 3) → (Fin m → Fin 3) → Prop
  | .z, u, v => lexLE u v
  | .d, _, _ => True

instance {m : ℕ} (t : T2) (u v : Fin m → Fin 3) : Decidable (PT t u v) := by
  cases t <;> unfold PT <;> infer_instance

/-- The entries (x, y) of the next row in the two columns are allowed after the status t. -/
def okT (t : T2) (x y : Fin 3) : Prop := t = .z → x ≤ y

instance (t : T2) (x y : Fin 3) : Decidable (okT t x y) := by
  unfold okT; infer_instance

/-- The status after the entries (x, y). -/
def stpT (t : T2) (x y : Fin 3) : T2 := if x = y then t else .d

lemma PT_cons {m : ℕ} (t : T2) (x y : Fin 3) (u v : Fin m → Fin 3) :
    PT t (Fin.cons x u : Fin (m + 1) → Fin 3) (Fin.cons y v) ↔ okT t x y ∧ PT (stpT t x y) u v := by
  by_cases hxy : x = y
  · subst hxy
    rw [show stpT t x x = t from if_pos rfl]
    cases t <;> simp [PT, okT, lexLE_cons]
  · rw [show stpT t x y = .d from if_neg hxy]
    cases t
    · simp only [PT, okT, lexLE_cons, hxy, false_and, or_false, true_implies, and_true]
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hxy⟩
    · simp [PT, okT]

lemma PT_nil (t : T2) (u v : Fin 0 → Fin 3) : PT t u v := by
  cases t
  · exact Or.inl (funext fun i => i.elim0)
  · trivial

/-! ## The arrays the proof counts -/

/-- The condition inside a row. -/
def hrow (r : Fin 7 → Fin 3) : Prop :=
  ∀ j : Fin 6, ¬ ((r j.succ : ℤ) - r j.castSucc ≡ -1 [ZMOD 3])

/-- The conditions between a row r and the row s below it. -/
def vcond (r s : Fin 7 → Fin 3) : Prop :=
  (∀ j : Fin 7, ¬ ((s j : ℤ) - r j ≡ 1 [ZMOD 3])) ∧ lexLE r s

instance (r : Fin 7 → Fin 3) : Decidable (hrow r) := by unfold hrow; infer_instance

instance (r s : Fin 7 → Fin 3) : Decidable (vcond r s) := by unfold vcond; infer_instance

/-- Column j of the array f. -/
def col {m : ℕ} (f : Fin m → Fin 7 → Fin 3) (j : Fin 7) : Fin m → Fin 3 := fun i => f i j

/-- Consecutive rows satisfy the conditions between rows. -/
def chain {m : ℕ} (y : Fin m → Fin 7 → Fin 3) : Prop :=
  ∀ i i' : Fin m, i.val + 1 = i'.val → vcond (y i) (y i')

instance {m : ℕ} : DecidablePred (@chain m) := fun y => by unfold chain; infer_instance

/-- The arrays counted by the proof. -/
def core {m : ℕ} (y : Fin m → Fin 7 → Fin 3) : Prop :=
  (∀ i, hrow (y i)) ∧ chain y ∧ ∀ j : Fin 6, PT .z (col y j.castSucc) (col y j.succ)

instance {m : ℕ} : DecidablePred (@core m) := fun y => by unfold core; infer_instance

/-- The rows f continue the row r validly, when the column pairs have statuses τ after r. -/
def Cont {m : ℕ} (τ : Fin 6 → T2) (r : Fin 7 → Fin 3) (f : Fin m → Fin 7 → Fin 3) : Prop :=
  chain (Fin.cons r f : Fin (m + 1) → Fin 7 → Fin 3) ∧
    (∀ i, hrow (f i)) ∧ ∀ j : Fin 6, PT (τ j) (col f j.castSucc) (col f j.succ)

instance {m : ℕ} (τ : Fin 6 → T2) (r : Fin 7 → Fin 3) : DecidablePred (@Cont m τ r) :=
  fun f => by unfold Cont; infer_instance

/-- The next row s is allowed by the statuses τ. -/
def okR (τ : Fin 6 → T2) (s : Fin 7 → Fin 3) : Prop :=
  ∀ j : Fin 6, okT (τ j) (s j.castSucc) (s j.succ)

instance (τ : Fin 6 → T2) : DecidablePred (okR τ) := fun s => by unfold okR; infer_instance

/-- The statuses after the row s. -/
def stpR (τ : Fin 6 → T2) (s : Fin 7 → Fin 3) : Fin 6 → T2 :=
  fun j => stpT (τ j) (s j.castSucc) (s j.succ)

lemma col_cons {m : ℕ} (s : Fin 7 → Fin 3) (g : Fin m → Fin 7 → Fin 3) (j : Fin 7) :
    col (Fin.cons s g : Fin (m + 1) → Fin 7 → Fin 3) j = Fin.cons (s j) (col g j) := by
  funext i
  induction i using Fin.cases <;> rfl

lemma chain_cons2 {m : ℕ} (r s : Fin 7 → Fin 3) (g : Fin m → Fin 7 → Fin 3) :
    chain (Fin.cons r (Fin.cons s g) : Fin (m + 2) → Fin 7 → Fin 3) ↔
      vcond r s ∧ chain (Fin.cons s g : Fin (m + 1) → Fin 7 → Fin 3) := by
  unfold chain
  constructor
  · intro h
    refine ⟨by simpa using h 0 1 (by simp), fun i j hij => ?_⟩
    have := h i.succ j.succ (by simp [hij])
    simpa using this
  · rintro ⟨h0, h⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j = 0 := by ext; simp at hij; omega
        subst hj
        simpa using h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_succ]
        exact h i j (by simp at hij; omega)

lemma all_hrow_cons {m : ℕ} (s : Fin 7 → Fin 3) (g : Fin m → Fin 7 → Fin 3) :
    (∀ i, hrow ((Fin.cons s g : Fin (m + 1) → Fin 7 → Fin 3) i)) ↔ hrow s ∧ ∀ i, hrow (g i) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma Cont_cons {m : ℕ} (τ : Fin 6 → T2) (r s : Fin 7 → Fin 3) (g : Fin m → Fin 7 → Fin 3) :
    Cont τ r (Fin.cons s g) ↔ (hrow s ∧ vcond r s) ∧ okR τ s ∧ Cont (stpR τ s) s g := by
  unfold Cont okR stpR
  rw [chain_cons2, all_hrow_cons]
  simp only [col_cons, PT_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    exact ⟨⟨h3, h1⟩, fun j => (h5 j).1, h2, h4, fun j => (h5 j).2⟩
  · rintro ⟨⟨h3, h1⟩, h5, h2, h4, h6⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, fun j => ⟨h5 j, h6 j⟩⟩

lemma Cont_nil (τ : Fin 6 → T2) (r : Fin 7 → Fin 3) (f : Fin 0 → Fin 7 → Fin 3) :
    Cont τ r f := by
  refine ⟨fun i i' h => ?_, fun i => i.elim0, fun j => PT_nil _ _ _⟩
  have := i'.isLt
  have := i.isLt
  omega

lemma core_cons {m : ℕ} (s : Fin 7 → Fin 3) (g : Fin m → Fin 7 → Fin 3) :
    core (Fin.cons s g : Fin (m + 1) → Fin 7 → Fin 3) ↔
      (hrow s ∧ okR (fun _ => .z) s) ∧ Cont (stpR (fun _ => .z) s) s g := by
  unfold core Cont okR stpR
  rw [all_hrow_cons]
  simp only [col_cons, PT_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, fun j => (h4 j).1⟩, h3, h2, fun j => (h4 j).2⟩
  · rintro ⟨⟨h1, h4⟩, h3, h2, h5⟩
    exact ⟨⟨h1, h2⟩, h3, fun j => ⟨h4 j, h5 j⟩⟩

/-! ## Counting by the first row -/

lemma card_by_head {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (Q : (Fin (m + 1) → α) → Prop) [DecidablePred Q] :
    (univ.filter Q).card = ∑ v : α, (univ.filter (fun h : Fin m → α => Q (Fin.cons v h))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (m + 1) → α => g 0) (t := univ)
    (by intro x _; simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  symm
  apply Finset.card_bij (fun h _ => (Fin.cons v h : Fin (m + 1) → α))
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨hh, by simp⟩
  · intro h₁ _ h₂ _ e
    simpa using congrArg Fin.tail e
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hq, h0⟩ := hg
    refine ⟨Fin.tail g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h0, Fin.cons_self_tail]
      exact hq
    · show Fin.cons v (Fin.tail g) = g
      rw [← h0, Fin.cons_self_tail]

/-- F(m, τ, r): the number of ways to continue the row r by m more rows, statuses τ after r. -/
def F (m : ℕ) (τ : Fin 6 → T2) (r : Fin 7 → Fin 3) : ℕ :=
  (univ.filter (fun f : Fin m → Fin 7 → Fin 3 => Cont τ r f)).card

lemma F_succ (m : ℕ) (τ : Fin 6 → T2) (r : Fin 7 → Fin 3) :
    F (m + 1) τ r = ∑ s : Fin 7 → Fin 3,
      if (hrow s ∧ vcond r s) ∧ okR τ s then F m (stpR τ s) s else 0 := by
  unfold F
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [Cont_cons]
  split_ifs with h
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hg => hg.2.2, fun hg => ⟨h.1, h.2, hg⟩⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact fun hg => h ⟨hg.1, hg.2.1⟩

lemma F_zero (τ : Fin 6 → T2) (r : Fin 7 → Fin 3) : F 0 τ r = 1 := by
  unfold F
  have hu : (univ : Finset (Fin 0 → Fin 7 → Fin 3)) = {Fin.elim0} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    funext i
    exact i.elim0
  rw [hu, Finset.filter_singleton, if_pos (Cont_nil _ _ _)]
  rfl

lemma good_iff_core {n : ℕ} (x : Fin 7 → Fin n → Fin 3) :
    good x ↔ core (fun j i => x i j) := by
  unfold good core chain hrow vcond col
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun j i => h2 i.castSucc i.succ j (by simp), fun j j' hj => ⟨fun i => h1 i j j' hj, h4 j j' hj⟩,
      fun i => h3 i.castSucc i.succ (by simp)⟩
  · rintro ⟨h1, h2, h4⟩
    refine ⟨fun i j j' hj => (h2 j j' hj).1 i, fun i i' j hi => ?_, fun i i' hi => ?_,
      fun j j' hj => (h2 j j' hj).2⟩
    · have hj3 : i.val < 6 := by have := i'.isLt; omega
      have e1 : i = (⟨i.val, hj3⟩ : Fin 6).castSucc := Fin.ext rfl
      have e2 : i' = (⟨i.val, hj3⟩ : Fin 6).succ := Fin.ext (by simp; omega)
      rw [e1, e2]
      exact h1 j _
    · have hj3 : i.val < 6 := by have := i'.isLt; omega
      have e1 : i = (⟨i.val, hj3⟩ : Fin 6).castSucc := Fin.ext rfl
      have e2 : i' = (⟨i.val, hj3⟩ : Fin 6).succ := Fin.ext (by simp; omega)
      rw [e1, e2]
      exact h4 _

lemma a_eq (n : ℕ) : a n = (univ.filter (fun y : Fin n → Fin 7 → Fin 3 => core y)).card := by
  unfold a
  apply Finset.card_bij (fun x _ => (fun j i => x i j : Fin n → Fin 7 → Fin 3))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (good_iff_core x).1 hx
  · intro x₁ _ x₂ _ e
    funext i j
    exact congrFun (congrFun e j) i
  · intro y hy
    refine ⟨fun i j => y j i, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact (good_iff_core _).2 hy

lemma a_succ (m : ℕ) : a (m + 1) = ∑ s : Fin 7 → Fin 3,
    if hrow s ∧ okR (fun _ => .z) s then F m (stpR (fun _ => .z) s) s else 0 := by
  rw [a_eq, card_by_head]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [core_cons]
  split_ifs with h
  · unfold F
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hg => hg.2, fun hg => ⟨h, hg⟩⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact fun hg => h hg.1

/-! ## The count the kernel evaluates -/

/-- Pass the status through a match, so that the kernel sees a constructor. -/
def mk2 (t : T2) (f : T2 → ℕ) : ℕ :=
  match t with
  | .z => f .z
  | .d => f .d

lemma mk2_eq (t : T2) (f : T2 → ℕ) : mk2 t f = f t := by cases t <;> rfl

/-- Digit j of the code c of a row: the entry in column j. -/
def dg (c j : ℕ) : ℕ := c / 3 ^ j % 3

def okB (t : T2) (x y : ℕ) : Bool :=
  match t with
  | .z => Nat.ble x y
  | .d => true

def stpB (t : T2) (x y : ℕ) : T2 := if Nat.beq x y then t else .d

/-- (b - a) mod 3 = k, for digits a, b. -/
def mdB (b a k : ℕ) : Bool := Nat.beq ((b + 3 - a) % 3) k

lemma md_one : ∀ a b : Fin 3, mdB b a 1 = true ↔ ((b : ℤ) - a ≡ 1 [ZMOD 3]) := by decide

lemma md_two : ∀ a b : Fin 3, mdB b a 2 = true ↔ ((b : ℤ) - a ≡ -1 [ZMOD 3]) := by decide

/-- The row with code c satisfies the condition inside a row. -/
def hrowB (c : ℕ) : Bool := !mdB (dg c 1) (dg c 0) 2 && !mdB (dg c 2) (dg c 1) 2 && !mdB (dg c 3) (dg c 2) 2 && !mdB (dg c 4) (dg c 3) 2 && !mdB (dg c 5) (dg c 4) 2 && !mdB (dg c 6) (dg c 5) 2

/-- Lexicographic order on digit lists. -/
def lexB : List ℕ → List ℕ → Bool
  | x :: xs, y :: ys => Nat.blt x y || (Nat.beq x y && lexB xs ys)
  | _, _ => true

/-- The rows with codes r (above) and s (below) satisfy the conditions between rows. -/
def vB (r s : ℕ) : Bool :=
  (!mdB (dg s 0) (dg r 0) 1 && !mdB (dg s 1) (dg r 1) 1 && !mdB (dg s 2) (dg r 2) 1 && !mdB (dg s 3) (dg r 3) 1 && !mdB (dg s 4) (dg r 4) 1 && !mdB (dg s 5) (dg r 5) 1 && !mdB (dg s 6) (dg r 6) 1) && lexB [dg r 0, dg r 1, dg r 2, dg r 3, dg r 4, dg r 5, dg r 6] [dg s 0, dg s 1, dg s 2, dg s 3, dg s 4, dg s 5, dg s 6]

/-- A sum over a list, by plain recursion (cheap for the kernel). -/
def sumL {α : Type} : List α → (α → ℕ) → ℕ
  | [], _ => 0
  | x :: l, f => f x + sumL l f

lemma sumL_eq {α : Type} (l : List α) (f : α → ℕ) : sumL l f = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [sumL, ih]

lemma sumL_filter {α : Type} (l : List α) (p : α → Bool) (f : α → ℕ) :
    sumL (l.filter p) f = sumL l (fun x => if p x = true then f x else 0) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x = true
    · simp [List.filter_cons, h, sumL, ih]
    · simp [List.filter_cons, h, sumL, ih]

/-- All row codes, and the rows satisfying the condition inside a row. -/
def allRows : List (Fin (3 ^ 7)) := List.finRange (3 ^ 7)

def validRows : List (Fin (3 ^ 7)) := allRows.filter (fun c => hrowB c)

lemma sumL_allRows (g : Fin (3 ^ 7) → ℕ) : sumL allRows g = ∑ s, g s := by
  rw [sumL_eq, allRows, Fin.sum_univ_def]

/-- The rows that may follow the row r. -/
def succL (r : Fin (3 ^ 7)) : List (Fin (3 ^ 7)) := validRows.filter (fun s => vB r s)

/-- W(m, t, r) through the status machine; the kernel evaluates each state once. -/
def cnt : ℕ → T2 → T2 → T2 → T2 → T2 → T2 → Fin (3 ^ 7) → ℕ
  | 0, t0, t1, t2, t3, t4, t5, _ => 1
  | m + 1, t0, t1, t2, t3, t4, t5, r =>
      sumL (succL r) (fun s : Fin (3 ^ 7) =>
        if okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4) && okB t4 (dg s 4) (dg s 5) && okB t5 (dg s 5) (dg s 6) then
          mk2 (stpB t0 (dg s 0) (dg s 1)) (fun u0 => mk2 (stpB t1 (dg s 1) (dg s 2)) (fun u1 => mk2 (stpB t2 (dg s 2) (dg s 3)) (fun u2 => mk2 (stpB t3 (dg s 3) (dg s 4)) (fun u3 => mk2 (stpB t4 (dg s 4) (dg s 5)) (fun u4 => mk2 (stpB t5 (dg s 5) (dg s 6)) (fun u5 => cnt m u0 u1 u2 u3 u4 u5 s))))))
        else 0)

lemma ite_band (b c : Bool) (x : ℕ) :
    (if b = true then (if c = true then x else 0) else 0) = if (b && c) = true then x else 0 := by
  cases b <;> cases c <;> rfl

/-- The row with code c. -/
def dec : Fin (3 ^ 7) ≃ (Fin 7 → Fin 3) := finFunctionFinEquiv.symm

lemma dec_val (c : Fin (3 ^ 7)) (j : Fin 7) : (dec c j : ℕ) = dg c j :=
  finFunctionFinEquiv_symm_apply_val c j

lemma okB_iff (t : T2) (x y : Fin 3) : okB t x y = true ↔ okT t x y := by
  cases t
  · show Nat.ble (x : ℕ) (y : ℕ) = true ↔ (T2.z = T2.z → x ≤ y)
    rw [Nat.ble_eq]
    exact ⟨fun h _ => h, fun h => h rfl⟩
  · exact ⟨fun _ h => absurd h (by decide), fun _ => rfl⟩

lemma stpB_eq (t : T2) (x y : Fin 3) : stpB t x y = stpT t x y := by
  unfold stpB stpT
  simp only [Nat.beq_eq, Fin.ext_iff]

lemma lexB_iff : ∀ (m : ℕ) (u v : Fin m → Fin 3),
    lexB (List.ofFn (fun i => (u i : ℕ))) (List.ofFn (fun i => (v i : ℕ))) = true ↔ lexLE u v
  | 0, u, v => by
    simp only [List.ofFn_zero, lexB, true_iff]
    exact Or.inl (funext fun i => i.elim0)
  | m + 1, u, v => by
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [lexB, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq]
    rw [lexB_iff m (fun i => u i.succ) (fun i => v i.succ)]
    conv_rhs => rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v]
    rw [lexLE_cons]
    simp only [Fin.lt_def, Fin.ext_iff]
    rfl

lemma hrow_iff (r : Fin 7 → Fin 3) : hrow r ↔ ¬ ((r 1 : ℤ) - r 0 ≡ -1 [ZMOD 3]) ∧ ¬ ((r 2 : ℤ) - r 1 ≡ -1 [ZMOD 3]) ∧ ¬ ((r 3 : ℤ) - r 2 ≡ -1 [ZMOD 3]) ∧ ¬ ((r 4 : ℤ) - r 3 ≡ -1 [ZMOD 3]) ∧ ¬ ((r 5 : ℤ) - r 4 ≡ -1 [ZMOD 3]) ∧ ¬ ((r 6 : ℤ) - r 5 ≡ -1 [ZMOD 3]) := by
  unfold hrow
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

lemma vert_iff (r s : Fin 7 → Fin 3) :
    (∀ j : Fin 7, ¬ ((s j : ℤ) - r j ≡ 1 [ZMOD 3])) ↔ ¬ ((s 0 : ℤ) - r 0 ≡ 1 [ZMOD 3]) ∧ ¬ ((s 1 : ℤ) - r 1 ≡ 1 [ZMOD 3]) ∧ ¬ ((s 2 : ℤ) - r 2 ≡ 1 [ZMOD 3]) ∧ ¬ ((s 3 : ℤ) - r 3 ≡ 1 [ZMOD 3]) ∧ ¬ ((s 4 : ℤ) - r 4 ≡ 1 [ZMOD 3]) ∧ ¬ ((s 5 : ℤ) - r 5 ≡ 1 [ZMOD 3]) ∧ ¬ ((s 6 : ℤ) - r 6 ≡ 1 [ZMOD 3]) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6

lemma hrowB_iff (c : Fin (3 ^ 7)) : hrowB c = true ↔ hrow (dec c) := by
  rw [hrow_iff]
  have c0 : dg c 0 = (dec c 0 : ℕ) := (dec_val c 0).symm
  have c1 : dg c 1 = (dec c 1 : ℕ) := (dec_val c 1).symm
  have c2 : dg c 2 = (dec c 2 : ℕ) := (dec_val c 2).symm
  have c3 : dg c 3 = (dec c 3 : ℕ) := (dec_val c 3).symm
  have c4 : dg c 4 = (dec c 4 : ℕ) := (dec_val c 4).symm
  have c5 : dg c 5 = (dec c 5 : ℕ) := (dec_val c 5).symm
  have c6 : dg c 6 = (dec c 6 : ℕ) := (dec_val c 6).symm
  simp only [hrowB, c0, c1, c2, c3, c4, c5, c6, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    md_two, and_assoc]

lemma vB_iff (r s : Fin (3 ^ 7)) : vB r s = true ↔ vcond (dec r) (dec s) := by
  have e : ∀ c : Fin (3 ^ 7), [dg c 0, dg c 1, dg c 2, dg c 3, dg c 4, dg c 5, dg c 6] =
      List.ofFn (fun i => (dec c i : ℕ)) := fun c => by
    simp only [List.ofFn_succ, List.ofFn_zero, dec_val]
    rfl
  unfold vB vcond
  rw [e, e, Bool.and_eq_true, lexB_iff, vert_iff]
  have r0 : dg r 0 = (dec r 0 : ℕ) := (dec_val r 0).symm
  have s0 : dg s 0 = (dec s 0 : ℕ) := (dec_val s 0).symm
  have r1 : dg r 1 = (dec r 1 : ℕ) := (dec_val r 1).symm
  have s1 : dg s 1 = (dec s 1 : ℕ) := (dec_val s 1).symm
  have r2 : dg r 2 = (dec r 2 : ℕ) := (dec_val r 2).symm
  have s2 : dg s 2 = (dec s 2 : ℕ) := (dec_val s 2).symm
  have r3 : dg r 3 = (dec r 3 : ℕ) := (dec_val r 3).symm
  have s3 : dg s 3 = (dec s 3 : ℕ) := (dec_val s 3).symm
  have r4 : dg r 4 = (dec r 4 : ℕ) := (dec_val r 4).symm
  have s4 : dg s 4 = (dec s 4 : ℕ) := (dec_val s 4).symm
  have r5 : dg r 5 = (dec r 5 : ℕ) := (dec_val r 5).symm
  have s5 : dg s 5 = (dec s 5 : ℕ) := (dec_val s 5).symm
  have r6 : dg r 6 = (dec r 6 : ℕ) := (dec_val r 6).symm
  have s6 : dg s 6 = (dec s 6 : ℕ) := (dec_val s 6).symm
  simp only [r0, s0, r1, s1, r2, s2, r3, s3, r4, s4, r5, s5, r6, s6, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, md_one,
    and_assoc]

lemma okR_iff (τ : Fin 6 → T2) (s : Fin 7 → Fin 3) :
    okR τ s ↔ okT (τ 0) (s 0) (s 1) ∧ okT (τ 1) (s 1) (s 2) ∧ okT (τ 2) (s 2) (s 3) ∧ okT (τ 3) (s 3) (s 4) ∧ okT (τ 4) (s 4) (s 5) ∧ okT (τ 5) (s 5) (s 6) := by
  unfold okR
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

lemma cnt_eq : ∀ (m : ℕ) (t0 t1 t2 t3 t4 t5 : T2) (r : Fin (3 ^ 7)),
    cnt m t0 t1 t2 t3 t4 t5 r = F m ![t0, t1, t2, t3, t4, t5] (dec r)
  | 0, t0, t1, t2, t3, t4, t5, r => by
    rw [cnt, F_zero]
  | m + 1, t0, t1, t2, t3, t4, t5, r => by
    rw [cnt, succL, validRows]
    simp only [sumL_filter]
    rw [sumL_allRows, F_succ, ← Equiv.sum_comp dec]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [ite_band]
    simp only [mk2_eq, cnt_eq m]
    have d0 : dg s 0 = (dec s 0 : ℕ) := (dec_val s 0).symm
    have d1 : dg s 1 = (dec s 1 : ℕ) := (dec_val s 1).symm
    have d2 : dg s 2 = (dec s 2 : ℕ) := (dec_val s 2).symm
    have d3 : dg s 3 = (dec s 3 : ℕ) := (dec_val s 3).symm
    have d4 : dg s 4 = (dec s 4 : ℕ) := (dec_val s 4).symm
    have d5 : dg s 5 = (dec s 5 : ℕ) := (dec_val s 5).symm
    have d6 : dg s 6 = (dec s 6 : ℕ) := (dec_val s 6).symm
    rw [d0, d1, d2, d3, d4, d5, d6]
    simp only [stpB_eq]
    have hst : stpR ![t0, t1, t2, t3, t4, t5] (dec s) =
        ![stpT t0 (dec s 0) (dec s 1), stpT t1 (dec s 1) (dec s 2), stpT t2 (dec s 2) (dec s 3), stpT t3 (dec s 3) (dec s 4), stpT t4 (dec s 4) (dec s 5), stpT t5 (dec s 5) (dec s 6)] := by
      funext j
      fin_cases j <;> rfl
    have hc : (hrowB s && (vB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && okB t2 (dec s 2) (dec s 3) && okB t3 (dec s 3) (dec s 4) && okB t4 (dec s 4) (dec s 5) && okB t5 (dec s 5) (dec s 6)))) = true ↔
          (hrow (dec s) ∧ vcond (dec r) (dec s)) ∧ okR ![t0, t1, t2, t3, t4, t5] (dec s) := by
      rw [okR_iff]
      simp only [Bool.and_eq_true, vB_iff, hrowB_iff, okB_iff, and_assoc]
      try exact Iff.rfl
    rw [hst]
    by_cases h : (hrowB s && (vB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && okB t2 (dec s 2) (dec s 3) && okB t3 (dec s 3) (dec s 4) && okB t4 (dec s 4) (dec s 5) && okB t5 (dec s 5) (dec s 6)))) = true
    · rw [if_pos h, if_pos (hc.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

lemma cnt_succ (m : ℕ) (t0 t1 t2 t3 t4 t5 : T2) (r : Fin (3 ^ 7)) :
    cnt (m + 1) t0 t1 t2 t3 t4 t5 r = ∑ s : Fin (3 ^ 7),
      if (hrowB s && (vB r s && (okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4) && okB t4 (dg s 4) (dg s 5) && okB t5 (dg s 5) (dg s 6)))) = true then
        cnt m (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (stpB t2 (dg s 2) (dg s 3)) (stpB t3 (dg s 3) (dg s 4)) (stpB t4 (dg s 4) (dg s 5)) (stpB t5 (dg s 5) (dg s 6)) s
      else 0 := by
  rw [cnt, succL, validRows]
  simp only [sumL_filter]
  rw [sumL_allRows]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [ite_band, mk2_eq]

def Sa (m : ℕ) : ℕ := sumL validRows (fun s : Fin (3 ^ 7) =>
    if okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) && okB .z (dg s 2) (dg s 3) && okB .z (dg s 3) (dg s 4) && okB .z (dg s 4) (dg s 5) && okB .z (dg s 5) (dg s 6) then
      cnt m (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (stpB .z (dg s 2) (dg s 3)) (stpB .z (dg s 3) (dg s 4)) (stpB .z (dg s 4) (dg s 5)) (stpB .z (dg s 5) (dg s 6)) s
    else 0)

lemma a_succ' (m : ℕ) : a (m + 1) = Sa m := by
  unfold Sa
  rw [validRows, sumL_filter, sumL_allRows, a_succ, ← Equiv.sum_comp dec]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [ite_band, cnt_eq]
  have d0 : dg s 0 = (dec s 0 : ℕ) := (dec_val s 0).symm
  have d1 : dg s 1 = (dec s 1 : ℕ) := (dec_val s 1).symm
  have d2 : dg s 2 = (dec s 2 : ℕ) := (dec_val s 2).symm
  have d3 : dg s 3 = (dec s 3 : ℕ) := (dec_val s 3).symm
  have d4 : dg s 4 = (dec s 4 : ℕ) := (dec_val s 4).symm
  have d5 : dg s 5 = (dec s 5 : ℕ) := (dec_val s 5).symm
  have d6 : dg s 6 = (dec s 6 : ℕ) := (dec_val s 6).symm
  rw [d0, d1, d2, d3, d4, d5, d6]
  simp only [stpB_eq]
  have hst : stpR (fun _ => .z) (dec s) =
      ![stpT .z (dec s 0) (dec s 1), stpT .z (dec s 1) (dec s 2), stpT .z (dec s 2) (dec s 3), stpT .z (dec s 3) (dec s 4), stpT .z (dec s 4) (dec s 5), stpT .z (dec s 5) (dec s 6)] := by
    funext j
    fin_cases j <;> rfl
  have hc : (hrowB s && (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2) && okB .z (dec s 2) (dec s 3) && okB .z (dec s 3) (dec s 4) && okB .z (dec s 4) (dec s 5) && okB .z (dec s 5) (dec s 6))) = true ↔ hrow (dec s) ∧ okR (fun _ => .z) (dec s) := by
    rw [okR_iff]
    simp only [Bool.and_eq_true, hrowB_iff, okB_iff, and_assoc]
    try exact Iff.rfl
  rw [hst]
  by_cases h : (hrowB s && (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2) && okB .z (dec s 2) (dec s 3) && okB .z (dec s 3) (dec s 4) && okB .z (dec s 4) (dec s 5) && okB .z (dec s 5) (dec s 6))) = true
  · rw [if_pos h, if_pos (hc.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

/-! ## The initial terms, from the kernel -/

/-- The first values a(1..8). -/
def fS : Bool := Sa 0 == 30 && Sa 1 == 142 && Sa 2 == 625 && Sa 3 == 2402 && Sa 4 == 8024 && Sa 5 == 23610 &&
  Sa 6 == 62205 && Sa 7 == 149031

lemma fS_true : fS = true := by decide +kernel

lemma kernel_facts : Sa 0 = 30 ∧ Sa 1 = 142 ∧ Sa 2 = 625 ∧ Sa 3 = 2402 ∧ Sa 4 = 8024 ∧ Sa 5 = 23610 ∧ Sa 6 = 62205 ∧
    Sa 7 = 149031 := by
  have h := fS_true
  simp only [fS, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ## Barker's recurrence and g.f., from the general theorem -/

/-- The entry counts the arrays of the general table `OMA.General.Mod3.T`. -/
lemma a_eq_T (n : ℕ) : a n = OMA.General.Mod3.T (-1) 1 false false n 7 := by
  rw [OMA.General.Mod3.T_transpose]
  unfold a OMA.General.Mod3.T
  congr 1

/-- The general theorem for this entry: the 8-th difference of n ↦ a (n + 1) vanishes. -/
lemma a_rel (n : ℕ) : a (n + 9) + 28 * a (n + 7) + 70 * a (n + 5) + 28 * a (n + 3) + a (n + 1) =
    8 * a (n + 8) + 56 * a (n + 6) + 56 * a (n + 4) + 8 * a (n + 2) := by
  have h := OMA.General.Mod3.T_poly_rows_sharp 6 n (Nat.zero_le n)
  rw [fwdDiff_iter_eq_sum_shift] at h
  norm_num [Finset.sum_range_succ, ← a_eq_T, add_assoc, show Nat.choose 8 0 = 1 from rfl, show Nat.choose 8 1 = 8 from rfl, show Nat.choose 8 2 = 28 from rfl, show Nat.choose 8 3 = 56 from rfl, show Nat.choose 8 4 = 70 from rfl, show Nat.choose 8 5 = 56 from rfl, show Nat.choose 8 6 = 28 from rfl, show Nat.choose 8 7 = 8 from rfl, show Nat.choose 8 8 = 1 from rfl] at h
  have h2 : (a (n + 9) : ℤ) + 28 * a (n + 7) + 70 * a (n + 5) + 28 * a (n + 3) + a (n + 1) = 8 * (a (n + 8) : ℤ) + 56 * a (n + 6) + 56 * a (n + 4) + 8 * a (n + 2) := by linarith
  exact_mod_cast h2

lemma a_v1 : a 1 = 30 := (a_succ' 0).trans kernel_facts.1
lemma a_v2 : a 2 = 142 := (a_succ' 1).trans kernel_facts.2.1
lemma a_v3 : a 3 = 625 := (a_succ' 2).trans kernel_facts.2.2.1
lemma a_v4 : a 4 = 2402 := (a_succ' 3).trans kernel_facts.2.2.2.1
lemma a_v5 : a 5 = 8024 := (a_succ' 4).trans kernel_facts.2.2.2.2.1
lemma a_v6 : a 6 = 23610 := (a_succ' 5).trans kernel_facts.2.2.2.2.2.1
lemma a_v7 : a 7 = 62205 := (a_succ' 6).trans kernel_facts.2.2.2.2.2.2.1
lemma a_v8 : a 8 = 149031 := (a_succ' 7).trans kernel_facts.2.2.2.2.2.2.2

/-- Barker's recurrence, for n > 8. -/
theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  have h := a_rel k
  simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega]
  have h' : (a (k + 9) : ℤ) + 28 * a (k + 7) + 70 * a (k + 5) + 28 * a (k + 3) + a (k + 1) =
      8 * (a (k + 8) : ℤ) + 56 * a (k + 6) + 56 * a (k + 4) + 8 * a (k + 2) := by exact_mod_cast h
  linarith

/-- Barker's g.f.: (Sum_{n >= 1} a(n) x^n) (1 - x)^8 = numerator. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (30 - 98 * X + 329 * X ^ 2 - 302 * X ^ 3 + 456 * X ^ 4 - 66 * X ^ 5 + 123 * X ^ 6 + 3 * X ^ 7) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 8 =
      A - C 8 * (A * X ^ 1) + C 28 * (A * X ^ 2) - C 56 * (A * X ^ 3) + C 70 * (A * X ^ 4) - C 56 * (A * X ^ 5) + C 28 * (A * X ^ 6) - C 8 * (A * X ^ 7) + A * X ^ 8 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (30 - 98 * X + 329 * X ^ 2 - 302 * X ^ 3 + 456 * X ^ 4 - 66 * X ^ 5 + 123 * X ^ 6 + 3 * X ^ 7) : ℚ⟦X⟧) =
      X ^ 1 * C 30 - X ^ 2 * C 98 + X ^ 3 * C 329 - X ^ 4 * C 302 + X ^ 5 * C 456 - X ^ 6 * C 66 + X ^ 7 * C 123 + X ^ 8 * C 3 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    hc]
  have v1 := a_v1
  have v2 := a_v2
  have v3 := a_v3
  have v4 := a_v4
  have v5 := a_v5
  have v6 := a_v6
  have v7 := a_v7
  have v8 := a_v8
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp_all <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have h := a_rel k
    have hq : (a (k + 9) : ℚ) + 28 * a (k + 7) + 70 * a (k + 5) + 28 * a (k + 3) + a (k + 1) =
        8 * (a (k + 8) : ℚ) + 56 * a (k + 6) + 56 * a (k + 4) + 8 * a (k + 2) := by exact_mod_cast h
    simp only [show k + 9 - 1 = k + 8 by omega,
      show k + 9 - 2 = k + 7 by omega,
      show k + 9 - 3 = k + 6 by omega,
      show k + 9 - 4 = k + 5 by omega,
      show k + 9 - 5 = k + 4 by omega,
      show k + 9 - 6 = k + 3 by omega,
      show k + 9 - 7 = k + 2 by omega,
      show k + 9 - 8 = k + 1 by omega,
      show ¬ k + 9 = 0 by omega,
      show ¬ k + 8 = 0 by omega,
      show ¬ k + 7 = 0 by omega,
      show ¬ k + 6 = 0 by omega,
      show ¬ k + 5 = 0 by omega,
      show ¬ k + 4 = 0 by omega,
      show ¬ k + 3 = 0 by omega,
      show ¬ k + 2 = 0 by omega,
      show ¬ k + 1 = 0 by omega,
      show 1 ≤ k + 9 by omega,
      show 2 ≤ k + 9 by omega,
      show 3 ≤ k + 9 by omega,
      show 4 ≤ k + 9 by omega,
      show 5 ≤ k + 9 by omega,
      show 6 ≤ k + 9 by omega,
      show 7 ≤ k + 9 by omega,
      show 8 ≤ k + 9 by omega,
      show ¬ k + 9 = 1 by omega,
      show ¬ k + 9 = 2 by omega,
      show ¬ k + 9 = 3 by omega,
      show ¬ k + 9 = 4 by omega,
      show ¬ k + 9 = 5 by omega,
      show ¬ k + 9 = 6 by omega,
      show ¬ k + 9 = 7 by omega,
      show ¬ k + 9 = 8 by omega, if_true, if_false]
    linear_combination hq

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (30 - 98 * X + 329 * X ^ 2 - 302 * X ^ 3 + 456 * X ^ 4 - 66 * X ^ 5 + 123 * X ^ 6 + 3 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) :=
  ⟨gf, recurrence⟩

/-- Controls: the entry's data a(1..27), from a(1..8) and the relation (proved for an
abstract sequence f, so that no tactic unfolds `a`). -/
theorem controls :
    a 1 = 30 ∧ a 2 = 142 ∧ a 3 = 625 ∧ a 4 = 2402 ∧ a 5 = 8024 ∧ a 6 = 23610 ∧ a 7 = 62205 ∧
    a 8 = 149031 ∧ a 9 = 329106 ∧ a 10 = 677706 ∧ a 11 = 1314145 ∧ a 12 = 2419348 ∧ a 13 = 4257692 ∧
    a 14 = 7203590 ∧ a 15 = 11773293 ∧ a 16 = 18662385 ∧ a 17 = 28789446 ∧ a 18 = 43346358 ∧
    a 19 = 63855729 ∧ a 20 = 92235910 ∧ a 21 = 130874080 ∧ a 22 = 182707874 ∧ a 23 = 251316029 ∧
    a 24 = 341018523 ∧ a 25 = 456986682 ∧ a 26 = 605363730 ∧ a 27 = 793396257 := by
  have key : ∀ f : ℕ → ℕ, f 1 = 30 → f 2 = 142 → f 3 = 625 → f 4 = 2402 → f 5 = 8024 → f 6 = 23610 → f 7 = 62205 → f 8 = 149031 →
      (∀ n, f (n + 9) + 28 * f (n + 7) + 70 * f (n + 5) + 28 * f (n + 3) + f (n + 1) = 8 * f (n + 8) + 56 * f (n + 6) + 56 * f (n + 4) + 8 * f (n + 2)) →
        f 1 = 30 ∧ f 2 = 142 ∧ f 3 = 625 ∧ f 4 = 2402 ∧ f 5 = 8024 ∧ f 6 = 23610 ∧ f 7 = 62205 ∧
        f 8 = 149031 ∧ f 9 = 329106 ∧ f 10 = 677706 ∧ f 11 = 1314145 ∧ f 12 = 2419348 ∧
        f 13 = 4257692 ∧ f 14 = 7203590 ∧ f 15 = 11773293 ∧ f 16 = 18662385 ∧ f 17 = 28789446 ∧
        f 18 = 43346358 ∧ f 19 = 63855729 ∧ f 20 = 92235910 ∧ f 21 = 130874080 ∧ f 22 = 182707874 ∧
        f 23 = 251316029 ∧ f 24 = 341018523 ∧ f 25 = 456986682 ∧ f 26 = 605363730 ∧ f 27 = 793396257 := by
    intro f h1 h2 h3 h4 h5 h6 h7 h8 hr
    have h9 : f 9 = 329106 := by
      have r := hr 0
      simp only [Nat.reduceAdd, Nat.reduceMul, h1, h2, h3, h4, h5, h6, h7, h8] at r
      omega
    have h10 : f 10 = 677706 := by
      have r := hr 1
      simp only [Nat.reduceAdd, Nat.reduceMul, h2, h3, h4, h5, h6, h7, h8, h9] at r
      omega
    have h11 : f 11 = 1314145 := by
      have r := hr 2
      simp only [Nat.reduceAdd, Nat.reduceMul, h3, h4, h5, h6, h7, h8, h9, h10] at r
      omega
    have h12 : f 12 = 2419348 := by
      have r := hr 3
      simp only [Nat.reduceAdd, Nat.reduceMul, h4, h5, h6, h7, h8, h9, h10, h11] at r
      omega
    have h13 : f 13 = 4257692 := by
      have r := hr 4
      simp only [Nat.reduceAdd, Nat.reduceMul, h5, h6, h7, h8, h9, h10, h11, h12] at r
      omega
    have h14 : f 14 = 7203590 := by
      have r := hr 5
      simp only [Nat.reduceAdd, Nat.reduceMul, h6, h7, h8, h9, h10, h11, h12, h13] at r
      omega
    have h15 : f 15 = 11773293 := by
      have r := hr 6
      simp only [Nat.reduceAdd, Nat.reduceMul, h7, h8, h9, h10, h11, h12, h13, h14] at r
      omega
    have h16 : f 16 = 18662385 := by
      have r := hr 7
      simp only [Nat.reduceAdd, Nat.reduceMul, h8, h9, h10, h11, h12, h13, h14, h15] at r
      omega
    have h17 : f 17 = 28789446 := by
      have r := hr 8
      simp only [Nat.reduceAdd, Nat.reduceMul, h9, h10, h11, h12, h13, h14, h15, h16] at r
      omega
    have h18 : f 18 = 43346358 := by
      have r := hr 9
      simp only [Nat.reduceAdd, Nat.reduceMul, h10, h11, h12, h13, h14, h15, h16, h17] at r
      omega
    have h19 : f 19 = 63855729 := by
      have r := hr 10
      simp only [Nat.reduceAdd, Nat.reduceMul, h11, h12, h13, h14, h15, h16, h17, h18] at r
      omega
    have h20 : f 20 = 92235910 := by
      have r := hr 11
      simp only [Nat.reduceAdd, Nat.reduceMul, h12, h13, h14, h15, h16, h17, h18, h19] at r
      omega
    have h21 : f 21 = 130874080 := by
      have r := hr 12
      simp only [Nat.reduceAdd, Nat.reduceMul, h13, h14, h15, h16, h17, h18, h19, h20] at r
      omega
    have h22 : f 22 = 182707874 := by
      have r := hr 13
      simp only [Nat.reduceAdd, Nat.reduceMul, h14, h15, h16, h17, h18, h19, h20, h21] at r
      omega
    have h23 : f 23 = 251316029 := by
      have r := hr 14
      simp only [Nat.reduceAdd, Nat.reduceMul, h15, h16, h17, h18, h19, h20, h21, h22] at r
      omega
    have h24 : f 24 = 341018523 := by
      have r := hr 15
      simp only [Nat.reduceAdd, Nat.reduceMul, h16, h17, h18, h19, h20, h21, h22, h23] at r
      omega
    have h25 : f 25 = 456986682 := by
      have r := hr 16
      simp only [Nat.reduceAdd, Nat.reduceMul, h17, h18, h19, h20, h21, h22, h23, h24] at r
      omega
    have h26 : f 26 = 605363730 := by
      have r := hr 17
      simp only [Nat.reduceAdd, Nat.reduceMul, h18, h19, h20, h21, h22, h23, h24, h25] at r
      omega
    have h27 : f 27 = 793396257 := by
      have r := hr 18
      simp only [Nat.reduceAdd, Nat.reduceMul, h19, h20, h21, h22, h23, h24, h25, h26] at r
      omega
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  exact key a a_v1 a_v2 a_v3 a_v4 a_v5 a_v6 a_v7 a_v8 a_rel


end OMA.S_oeis_a229450

theorem OMA.solution : type_of% @OMA.S_oeis_a229450.main :=
  OMA.S_oeis_a229450.conjecture
