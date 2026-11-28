import OMAStatements.S_oeis_a225661
import Mathlib

/-
A225661 (base 3): if `a n > 6` then `a n` is odd.

Every trajectory used here reaches the 2-cycle (1,2) -> (0,1,1) or the 6-cycle
(2,2) -> (0,0,2) -> (2,0,1) -> (1,1,1) -> (0,3) -> (1,0,0,1). `Cyc` lists these 8 vectors: it is closed under `F`
and `F^[6]` fixes each of them. If the trajectory of `V` first meets `Cyc` at step `k` (`Hit V k`), then `k` is
the least index with a later repeat (`sInf_eq_of_hit`). For `n > 0`, `F (digs n)` has length 2 or 3, and every
vector of length 2 or 3 meets `Cyc` after at most 5 steps or after an even number of steps (`good_2`, `good_3`),
so `a n` is at most 6 or odd. The large cases use the two-step formula `FF` and induction on the largest entry,
which drops by 1 every 2 steps; the small cases are finite checks by `decide`.
-/

namespace OMA.A225661Proof

open OMA.S_oeis_a225661

-- The maximum `foldr max 0`.

theorem le_fmax {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons y t ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with h | h
    · rw [h]
      exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem fmax_le {l : List ℕ} {M : ℕ} (h : ∀ x ∈ l, x ≤ M) : l.foldr max 0 ≤ M := by
  induction l with
  | nil => simp
  | cons y t ih =>
    rw [List.foldr_cons]
    exact max_le (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem fmax_eq {l : List ℕ} {M : ℕ} (h1 : ∀ x ∈ l, x ≤ M) (h2 : M ∈ l) : l.foldr max 0 = M :=
  le_antisymm (fmax_le h1) (le_fmax h2)

theorem fmax_perm {l l' : List ℕ} (h : List.Perm l l') : l.foldr max 0 = l'.foldr max 0 :=
  le_antisymm (fmax_le fun _ hx => le_fmax (h.mem_iff.mp hx))
    (fmax_le fun _ hx => le_fmax (h.mem_iff.mpr hx))

-- Basic facts on `F`.

theorem length_F (s : List ℕ) : (F s).length = s.foldr max 0 + 1 := by
  simp [F]

theorem len_F_ge {s : List ℕ} {x : ℕ} (hx : x ∈ s) : x + 1 ≤ (F s).length := by
  rw [length_F]
  exact Nat.succ_le_succ (le_fmax hx)

theorem F_perm {l l' : List ℕ} (h : List.Perm l l') : F l = F l' := by
  unfold F
  rw [fmax_perm h]
  apply List.map_congr_left
  intro i _
  exact h.count_eq i

theorem perm_pqp (p q : ℕ) : List.Perm [p, q, p] [p, p, q] :=
  List.Perm.cons p (List.Perm.swap p q [])

theorem perm_qpp (p q : ℕ) : List.Perm [q, p, p] [p, p, q] :=
  (List.Perm.swap p q [p]).trans (perm_pqp p q)

theorem count_map_eq (f : ℕ → ℕ) (c : ℕ) (l : List ℕ) :
    (l.map f).count c = l.countP (fun i => decide (f i = c)) := by
  induction l with
  | nil => rfl
  | cons y t ih =>
    rw [List.map_cons, List.count_cons, List.countP_cons, ih]
    all_goals (by_cases h : f y = c <;> simp [h])

theorem count_F (s : List ℕ) (c : ℕ) :
    (F s).count c = (List.range (s.foldr max 0 + 1)).countP (fun i => decide (s.count i = c)) :=
  count_map_eq (fun i => s.count i) c _

theorem countP_split (l s : List ℕ) :
    l.countP (fun i => decide (s.count i = 0)) + l.countP (fun i => decide (0 < s.count i)) =
      l.length := by
  induction l with
  | nil => rfl
  | cons y t ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    rcases Nat.eq_zero_or_pos (s.count y) with h | h
    · have h1 : decide (s.count y = 0) = true := decide_eq_true h
      have h2 : ¬ (decide (0 < s.count y) = true) := fun hd => by
        have := of_decide_eq_true hd
        omega
      rw [if_pos h1, if_neg h2]
      omega
    · have h1 : ¬ (decide (s.count y = 0) = true) := fun hd => by
        have := of_decide_eq_true hd
        omega
      have h2 : decide (0 < s.count y) = true := decide_eq_true h
      rw [if_neg h1, if_pos h2]
      omega

theorem count_F_pos (s D : List ℕ) (hD : D.Nodup) (hmem : ∀ x, x ∈ D ↔ x ∈ s) (c : ℕ)
    (hc : c ≠ 0) : (F s).count c = D.countP (fun i => decide (s.count i = c)) := by
  rw [count_F, List.countP_eq_length_filter, List.countP_eq_length_filter]
  apply List.Perm.length_eq
  refine (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range)
    (List.Nodup.filter _ hD)).mpr ?_
  intro x
  simp only [List.mem_filter, List.mem_range, hmem, decide_eq_true_eq]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨List.count_pos_iff.mp (by omega), h⟩
  · rintro ⟨hx, h⟩
    exact ⟨Nat.lt_succ_of_le (le_fmax hx), h⟩

theorem count_F_zero (s D : List ℕ) (hD : D.Nodup) (hmem : ∀ x, x ∈ D ↔ x ∈ s) :
    (F s).count 0 = s.foldr max 0 + 1 - D.length := by
  have h1 := countP_split (List.range (s.foldr max 0 + 1)) s
  have h2 : (List.range (s.foldr max 0 + 1)).countP (fun i => decide (0 < s.count i)) =
      D.length := by
    rw [List.countP_eq_length_filter]
    apply List.Perm.length_eq
    refine (List.perm_ext_iff_of_nodup (List.Nodup.filter _ List.nodup_range) hD).mpr ?_
    intro x
    simp only [List.mem_filter, List.mem_range, hmem, decide_eq_true_eq, List.count_pos_iff]
    exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le (le_fmax h), h⟩⟩
  rw [List.length_range] at h1
  rw [count_F]
  omega

/-- The two-step formula: `F (F s)` from the entries of `s` (listed without repeats in `D`) and their
multiplicities. -/
theorem FF (s D : List ℕ) (M E j : ℕ) (hM : s.foldr max 0 = M) (hD : D.Nodup)
    (hmem : ∀ x, x ∈ D ↔ x ∈ s) (hE : ∀ i, s.count i ≤ E) (hj : s.count j = E) (hE0 : 0 < E) :
    F (F s) = (List.range (E + 1)).map
      (fun c => if c = 0 then M + 1 - D.length else D.countP (fun i => decide (s.count i = c))) := by
  have hmax : (F s).foldr max 0 = E := by
    apply fmax_eq
    · intro x hx
      unfold F at hx
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      exact hE i
    · rw [← hj]
      unfold F
      exact List.mem_map.mpr
        ⟨j, List.mem_range.mpr (Nat.lt_succ_of_le (le_fmax (List.count_pos_iff.mp (by omega)))), rfl⟩
  show (List.range ((F s).foldr max 0 + 1)).map (fun c => (F s).count c) = _
  rw [hmax]
  apply List.map_congr_left
  intro c _
  split_ifs with hc
  · subst hc
    rw [count_F_zero s D hD hmem, hM]
  · exact count_F_pos s D hD hmem c hc

theorem range2 : List.range (1 + 1) = [0, 1] := rfl

theorem range3 : List.range (2 + 1) = [0, 1, 2] := rfl

theorem range4 : List.range (3 + 1) = [0, 1, 2, 3] := rfl

theorem FF2 {p q M : ℕ} (hpq : p ≠ q) (hp : p ≤ M) (hq : q ≤ M) (hM : p = M ∨ q = M) :
    F (F [p, q]) = [M - 1, 2] := by
  have hqp : q ≠ p := Ne.symm hpq
  have hmax : [p, q].foldr max 0 = M :=
    fmax_eq (by simp [hp, hq]) (by rcases hM with h | h <;> simp [h])
  have hnd : [p, q].Nodup := by simp [hpq]
  have hE : ∀ i, [p, q].count i ≤ 1 := fun i => List.nodup_iff_count_le_one.mp hnd i
  have hj : [p, q].count p = 1 := by simp [hqp]
  rw [FF [p, q] [p, q] M 1 p hmax hnd (fun _ => Iff.rfl) hE hj one_pos, range2]
  simp [List.countP_cons, List.count_cons, hpq, hqp]

theorem FF2e (p : ℕ) : F (F [p, p]) = [p, 0, 1] := by
  have hmax : [p, p].foldr max 0 = p := fmax_eq (by simp) (by simp)
  have hj : [p, p].count p = 2 := by simp
  rw [FF [p, p] [p] p 2 p hmax (by simp) (fun _ => by simp)
    (fun _ => le_trans List.count_le_length (by simp)) hj two_pos, range3]
  simp [List.countP_cons, List.count_cons]

theorem FF3 {x y z M : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hx : x ≤ M) (hy : y ≤ M)
    (hz : z ≤ M) (hM : x = M ∨ y = M ∨ z = M) : F (F [x, y, z]) = [M - 2, 3] := by
  have hyx : y ≠ x := Ne.symm hxy
  have hzx : z ≠ x := Ne.symm hxz
  have hzy : z ≠ y := Ne.symm hyz
  have hmax : [x, y, z].foldr max 0 = M :=
    fmax_eq (by simp [hx, hy, hz]) (by rcases hM with h | h | h <;> simp [h])
  have hnd : [x, y, z].Nodup := by simp [hxy, hxz, hyz]
  have hE : ∀ i, [x, y, z].count i ≤ 1 := fun i => List.nodup_iff_count_le_one.mp hnd i
  have hj : [x, y, z].count x = 1 := by simp [hyx, hzx]
  rw [FF [x, y, z] [x, y, z] M 1 x hmax hnd (fun _ => Iff.rfl) hE hj one_pos, range2]
  simp [List.countP_cons, List.count_cons, hxy, hxz, hyz, hyx, hzx, hzy]

theorem FF4 {p q M : ℕ} (hpq : p ≠ q) (hp : p ≤ M) (hq : q ≤ M) (hM : p = M ∨ q = M) :
    F (F [p, p, q]) = [M - 1, 1, 1] := by
  have hqp : q ≠ p := Ne.symm hpq
  have hmax : [p, p, q].foldr max 0 = M :=
    fmax_eq (by simp [hp, hq]) (by rcases hM with h | h <;> simp [h])
  have hnd : [p, q].Nodup := by simp [hpq]
  have hE : ∀ i, [p, p, q].count i ≤ 2 := by
    intro i
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega
  have hj : [p, p, q].count p = 2 := by simp [hqp]
  rw [FF [p, p, q] [p, q] M 2 p hmax hnd (fun _ => by simp) hE hj two_pos, range3]
  simp [List.countP_cons, List.count_cons, hpq, hqp]

theorem FF4' {V : List ℕ} {p q M : ℕ} (hV : List.Perm V [p, p, q]) (hpq : p ≠ q) (hp : p ≤ M)
    (hq : q ≤ M) (hM : p = M ∨ q = M) : F (F V) = [M - 1, 1, 1] := by
  rw [F_perm hV]
  exact FF4 hpq hp hq hM

theorem FF5 (p : ℕ) : F (F [p, p, p]) = [p, 0, 0, 1] := by
  have hmax : [p, p, p].foldr max 0 = p := fmax_eq (by simp) (by simp)
  have hj : [p, p, p].count p = 3 := by simp
  rw [FF [p, p, p] [p] p 3 p hmax (by simp) (fun _ => by simp)
    (fun _ => le_trans List.count_le_length (by simp)) hj (by norm_num), range4]
  simp [List.countP_cons, List.count_cons]

theorem FF6 {p : ℕ} (hp : 2 ≤ p) : F (F [p, 0, 0, 1]) = [p - 2, 2, 1] := by
  have h0 : p ≠ 0 := by omega
  have h1 : p ≠ 1 := by omega
  have h0' : (0 : ℕ) ≠ p := Ne.symm h0
  have h1' : (1 : ℕ) ≠ p := Ne.symm h1
  have hmax : [p, 0, 0, 1].foldr max 0 = p := fmax_eq (by simp; omega) (by simp)
  have hnd : [p, 0, 1].Nodup := by simp [h0, h1]
  have hE : ∀ i, [p, 0, 0, 1].count i ≤ 2 := by
    intro i
    simp only [List.count_cons, List.count_nil, beq_iff_eq]
    split_ifs <;> omega
  have hj : [p, 0, 0, 1].count 0 = 2 := by simp [h0]
  rw [FF [p, 0, 0, 1] [p, 0, 1] p 2 0 hmax hnd (fun _ => by simp) hE hj two_pos, range3]
  simp [List.countP_cons, List.count_cons, h0, h1, h0', h1']

-- The two cycles and the hitting time.

/-- The 2-cycle (1,2) -> (0,1,1) and the 6-cycle (2,2) -> (0,0,2) -> (2,0,1) -> (1,1,1) -> (0,3) ->
(1,0,0,1). -/
def Cyc : List (List ℕ) :=
  [[1, 2], [0, 1, 1], [2, 2], [0, 0, 2], [2, 0, 1], [1, 1, 1], [0, 3], [1, 0, 0, 1]]

theorem cyc_closed : ∀ W ∈ Cyc, F W ∈ Cyc := by decide

theorem cyc_period : ∀ W ∈ Cyc, F^[6] W = W := by decide

theorem cyc_iter (t : ℕ) : ∀ W ∈ Cyc, F^[t] W ∈ Cyc := by
  induction t with
  | zero => exact fun W h => h
  | succ t ih => exact fun W h => ih (F W) (cyc_closed W h)

theorem not_cyc_big {V : List ℕ} {x : ℕ} (hx : x ∈ V) (h4 : 4 ≤ x) : V ∉ Cyc := by
  intro h
  have hb : ∀ W ∈ Cyc, ∀ y ∈ W, y ≤ 3 := by decide
  have := hb V h x hx
  omega

theorem not_cyc_len {V : List ℕ} (h5 : 5 ≤ V.length) : V ∉ Cyc := by
  intro h
  have hb : ∀ W ∈ Cyc, W.length ≤ 4 := by decide
  have := hb V h
  omega

/-- `Hit V k`: the trajectory of `V` first meets `Cyc` at step `k`. -/
def Hit (V : List ℕ) (k : ℕ) : Prop := F^[k] V ∈ Cyc ∧ ∀ i < k, F^[i] V ∉ Cyc

theorem hit_zero {V : List ℕ} (h : V ∈ Cyc) : Hit V 0 :=
  ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem hit_succ {V : List ℕ} {k : ℕ} (hV : V ∉ Cyc) (h : Hit (F V) k) : Hit V (k + 1) := by
  refine ⟨h.1, ?_⟩
  intro i hi
  cases i with
  | zero => exact hV
  | succ j => exact h.2 j (by omega)

/-- If the trajectory first meets `Cyc` at step `k`, then `k` is the least index with a later repeat. -/
theorem sInf_eq_of_hit {V : List ℕ} {k : ℕ} (h : Hit V k) :
    sInf {i | ∃ j, i < j ∧ F^[i] V = F^[j] V} = k := by
  have hmem : k ∈ {i | ∃ j, i < j ∧ F^[i] V = F^[j] V} := by
    refine ⟨k + 6, by omega, ?_⟩
    rw [Nat.add_comm, Function.iterate_add_apply, cyc_period _ h.1]
  have hnot : ∀ i < k, i ∉ {i | ∃ j, i < j ∧ F^[i] V = F^[j] V} := by
    rintro i hi ⟨j, hij, hj⟩
    have hp : F^[j - i] (F^[i] V) = F^[i] V := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
      exact hj.symm
    have hN : F^[(j - i) * k] (F^[i] V) = F^[i] V := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hp k
    have hk : k ≤ (j - i) * k := by
      have h1 : 1 ≤ j - i := by omega
      have := Nat.mul_le_mul h1 (le_refl k)
      simpa using this
    obtain ⟨t, ht1, ht2⟩ : ∃ t, k ≤ t ∧ F^[t] (F^[i] V) = F^[i] V := ⟨_, hk, hN⟩
    have e : F^[t] (F^[i] V) = F^[t - k + i] (F^[k] V) := by
      rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
        show t - k + i + k = t + i by omega]
    have hc : F^[i] V ∈ Cyc := by
      rw [← ht2, e]
      exact cyc_iter _ _ h.1
    exact h.2 i hi hc
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · apply le_csInf ⟨k, hmem⟩
    intro i hi
    by_contra hlt
    exact hnot i (by omega) hi

theorem a_eq {n k : ℕ} (h : Hit (digs n) k) : a n = k := by
  unfold a
  exact sInf_eq_of_hit h

/-- Hitting time with fuel, used only for finite checks by `decide`. -/
def ht : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | f + 1, V => if V ∈ Cyc then 0 else ht f (F V) + 1

theorem hit_ht (f : ℕ) : ∀ V : List ℕ, F^[ht f V] V ∈ Cyc → Hit V (ht f V) := by
  induction f with
  | zero => exact fun V h => hit_zero h
  | succ f ih =>
    intro V h
    by_cases hV : V ∈ Cyc
    · have e : ht (f + 1) V = 0 := by simp [ht, hV]
      rw [e]
      exact hit_zero hV
    · have e : ht (f + 1) V = ht f (F V) + 1 := by simp [ht, hV]
      rw [e] at h ⊢
      exact hit_succ hV (ih (F V) h)

/-- `V` meets `Cyc` after an even number of steps. -/
def EvenH (V : List ℕ) : Prop := ∃ k, Hit V k ∧ Even k

/-- `V` meets `Cyc` after at most 5 steps or after an even number of steps. -/
def GoodP (V : List ℕ) : Prop := ∃ k, Hit V k ∧ (k ≤ 5 ∨ Even k)

theorem good_of_even {V : List ℕ} (h : EvenH V) : GoodP V := by
  obtain ⟨k, hk, he⟩ := h
  exact ⟨k, hk, Or.inr he⟩

theorem even_of_check (V : List ℕ) (h : F^[ht 40 V] V ∈ Cyc ∧ ht 40 V % 2 = 0) : EvenH V :=
  ⟨ht 40 V, hit_ht 40 V h.1, Nat.even_iff.mpr h.2⟩

theorem good_of_check (V : List ℕ)
    (h : F^[ht 40 V] V ∈ Cyc ∧ (ht 40 V ≤ 5 ∨ ht 40 V % 2 = 0)) : GoodP V :=
  ⟨ht 40 V, hit_ht 40 V h.1, h.2.imp id Nat.even_iff.mpr⟩

theorem even_two_step {V : List ℕ} (h1 : V ∉ Cyc) (h2 : F V ∉ Cyc) (h : EvenH (F (F V))) :
    EvenH V := by
  obtain ⟨k, hk, r, hr⟩ := h
  exact ⟨k + 2, hit_succ h1 (hit_succ h2 hk), r + 1, by omega⟩

theorem even_two_big {V : List ℕ} {x : ℕ} (hx : x ∈ V) (h4 : 4 ≤ x) (h : EvenH (F (F V))) :
    EvenH V :=
  even_two_step (not_cyc_big hx h4) (not_cyc_len (le_trans (by omega) (len_F_ge hx))) h

-- Finite checks.

set_option maxRecDepth 100000 in
theorem base_m2 : ∀ m < 4, F^[ht 40 [m, 2]] [m, 2] ∈ Cyc ∧ ht 40 [m, 2] % 2 = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem base_x3 : ∀ x < 4, F^[ht 40 [x, 3]] [x, 3] ∈ Cyc ∧ ht 40 [x, 3] % 2 = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem base_r11 : ∀ r < 4, F^[ht 40 [r, 1, 1]] [r, 1, 1] ∈ Cyc ∧ ht 40 [r, 1, 1] % 2 = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem base_x21 : ∀ x < 4, 1 ≤ x →
    F^[ht 40 [x, 2, 1]] [x, 2, 1] ∈ Cyc ∧ ht 40 [x, 2, 1] % 2 = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem base_2 : ∀ p < 4, ∀ q < 4,
    F^[ht 40 [p, q]] [p, q] ∈ Cyc ∧ (ht 40 [p, q] ≤ 5 ∨ ht 40 [p, q] % 2 = 0) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem base_3 : ∀ x < 4, ∀ y < 4, ∀ z < 4,
    F^[ht 40 [x, y, z]] [x, y, z] ∈ Cyc ∧ (ht 40 [x, y, z] ≤ 5 ∨ ht 40 [x, y, z] % 2 = 0) := by
  decide

-- The parametric families.

theorem even_m2 (m : ℕ) : EvenH [m, 2] := by
  induction m with
  | zero => exact even_of_check _ (base_m2 0 (by norm_num))
  | succ m ih =>
    rcases Nat.lt_or_ge (m + 1) 4 with hm | hm
    · exact even_of_check _ (base_m2 (m + 1) hm)
    · refine even_two_big (V := [m + 1, 2]) (x := m + 1) (by simp) hm ?_
      rw [FF2 (p := m + 1) (q := 2) (M := m + 1) (by omega) le_rfl (by omega) (Or.inl rfl)]
      simpa using ih

theorem even_x3 (x : ℕ) : EvenH [x, 3] := by
  rcases Nat.lt_or_ge x 4 with hx | hx
  · exact even_of_check _ (base_x3 x hx)
  · refine even_two_big (V := [x, 3]) (x := x) (by simp) hx ?_
    rw [FF2 (p := x) (q := 3) (M := x) (by omega) le_rfl (by omega) (Or.inl rfl)]
    exact even_m2 _

theorem even_r11 (r : ℕ) : EvenH [r, 1, 1] := by
  induction r with
  | zero => exact even_of_check _ (base_r11 0 (by norm_num))
  | succ r ih =>
    rcases Nat.lt_or_ge (r + 1) 4 with hr | hr
    · exact even_of_check _ (base_r11 (r + 1) hr)
    · refine even_two_big (V := [r + 1, 1, 1]) (x := r + 1) (by simp) hr ?_
      rw [FF4' (perm_qpp 1 (r + 1)) (p := 1) (q := r + 1) (M := r + 1) (by omega) (by omega) le_rfl
        (Or.inr rfl)]
      simpa using ih

theorem even_x21 (x : ℕ) (hx : 1 ≤ x) : EvenH [x, 2, 1] := by
  rcases Nat.lt_or_ge x 4 with h | h
  · exact even_of_check _ (base_x21 x h hx)
  · refine even_two_big (V := [x, 2, 1]) (x := x) (by simp) h ?_
    rw [FF3 (x := x) (y := 2) (z := 1) (M := x) (by omega) (by omega) (by omega) le_rfl (by omega)
      (by omega) (Or.inl rfl)]
    exact even_x3 _

theorem good_2 (p q : ℕ) : GoodP [p, q] := by
  by_cases hs : 4 ≤ max p q
  · apply good_of_even
    by_cases hpq : p = q
    · rw [← hpq]
      have hp : 4 ≤ p := by omega
      refine even_two_big (V := [p, p]) (x := p) (by simp) hp ?_
      rw [FF2e]
      refine even_two_big (V := [p, 0, 1]) (x := p) (by simp) hp ?_
      rw [FF3 (x := p) (y := 0) (z := 1) (M := p) (by omega) (by omega) (by omega) le_rfl (by omega)
        (by omega) (Or.inl rfl)]
      exact even_x3 _
    · rcases le_total p q with h | h
      · refine even_two_big (V := [p, q]) (x := q) (by simp) (by omega) ?_
        rw [FF2 (p := p) (q := q) (M := q) hpq h le_rfl (Or.inr rfl)]
        exact even_m2 _
      · refine even_two_big (V := [p, q]) (x := p) (by simp) (by omega) ?_
        rw [FF2 (p := p) (q := q) (M := p) hpq le_rfl h (Or.inl rfl)]
        exact even_m2 _
  · exact good_of_check _ (base_2 p (by omega) q (by omega))

theorem even_3_big (x y z M : ℕ) (hxM : x ≤ M) (hyM : y ≤ M) (hzM : z ≤ M)
    (hM : x = M ∨ y = M ∨ z = M) (hs : 4 ≤ M) : EvenH [x, y, z] := by
  have hMmem : M ∈ [x, y, z] := by rcases hM with h | h | h <;> simp [h]
  refine even_two_big (V := [x, y, z]) (x := M) hMmem hs ?_
  by_cases hxy : x = y
  · by_cases hyz : y = z
    · rw [← hyz, ← hxy, FF5]
      refine even_two_big (V := [x, 0, 0, 1]) (x := x) (by simp) (by omega) ?_
      rw [FF6 (p := x) (by omega)]
      exact even_x21 _ (by omega)
    · rw [← hxy, FF4 (p := x) (q := z) (M := M) (by omega) hxM hzM (by omega)]
      exact even_r11 _
  · by_cases hxz : x = z
    · rw [← hxz, FF4' (perm_pqp x y) (p := x) (q := y) (M := M) hxy hxM hyM (by omega)]
      exact even_r11 _
    · by_cases hyz : y = z
      · rw [← hyz, FF4' (perm_qpp y x) (p := y) (q := x) (M := M) (by omega) hyM hxM (by omega)]
        exact even_r11 _
      · rw [FF3 (x := x) (y := y) (z := z) (M := M) hxy hxz hyz hxM hyM hzM hM]
        exact even_x3 _

theorem good_3 (x y z : ℕ) : GoodP [x, y, z] := by
  by_cases hs : 4 ≤ max x (max y z)
  · exact good_of_even (even_3_big x y z (max x (max y z)) (by omega) (by omega) (by omega)
      (by omega) hs)
  · exact good_of_check _ (base_3 x (by omega) y (by omega) z (by omega))

-- The digit vector.

theorem good_F_digs (n : ℕ) (hn : n ≠ 0) : GoodP (F (digs n)) := by
  have hd : digs n = (Nat.digits 3 n).reverse := by simp [digs, hn]
  have hle : ∀ x ∈ digs n, x ≤ 2 := by
    intro x hx
    rw [hd, List.mem_reverse] at hx
    have := Nat.digits_lt_base (by norm_num) hx
    omega
  have hne : Nat.digits 3 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hlast : (Nat.digits 3 n).getLast hne ∈ digs n := by
    rw [hd, List.mem_reverse]
    exact List.getLast_mem hne
  have hpos : (Nat.digits 3 n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 3 hn
  have h1 : 1 ≤ (digs n).foldr max 0 :=
    le_trans (Nat.one_le_iff_ne_zero.mpr hpos) (le_fmax hlast)
  have h2 : (digs n).foldr max 0 ≤ 2 := fmax_le hle
  have hlen := length_F (digs n)
  rcases (show (digs n).foldr max 0 = 1 ∨ (digs n).foldr max 0 = 2 by omega) with h | h
  · obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp (show (F (digs n)).length = 2 by omega)
    rw [hpq]
    exact good_2 p q
  · obtain ⟨x, y, z, hxyz⟩ := List.length_eq_three.mp (show (F (digs n)).length = 3 by omega)
    rw [hxyz]
    exact good_3 x y z

theorem main_proof : ∀ n : ℕ, 6 < a n → Odd (a n) := by
  intro n hn
  by_cases h0 : n = 0
  · have hd0 : digs n = [0] := by simp [digs, h0]
    have hh : Hit (digs n) 6 := by
      rw [hd0]
      unfold Hit
      decide
    rw [a_eq hh] at hn
    omega
  · obtain ⟨k, hk, hpar⟩ := good_F_digs n h0
    by_cases hc : digs n ∈ Cyc
    · rw [a_eq (hit_zero hc)] at hn
      omega
    · rw [a_eq (hit_succ hc hk)] at hn ⊢
      rcases hpar with h | h
      · omega
      · exact h.add_one

end OMA.A225661Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a225661.main := by
  exact OMA.A225661Proof.main_proof
