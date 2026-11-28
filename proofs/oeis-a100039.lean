import OMAStatements.S_oeis_a100039
import Mathlib

namespace OMA.A100039Proof

open OMA.S_oeis_a100039

/-! ## Block starts `P k = 2k^2 + k + 1` and the block contents `g k r = b (P k + r)` -/

def P (k : ℕ) : ℕ := 2 * k ^ 2 + k + 1

lemma P_succ (k : ℕ) : P (k + 1) = P k + 4 * k + 3 := by unfold P; ring

lemma P_mono {a c : ℕ} (h : a ≤ c) : P a ≤ P c := by unfold P; gcongr

lemma P_ge (k : ℕ) : k + 1 ≤ P k := by unfold P; omega

lemma P_one : P 1 = 4 := by unfold P; norm_num

lemma P_ge4 {k : ℕ} (hk : 1 ≤ k) : 4 ≤ P k := by
  have h := P_mono hk
  rw [P_one] at h
  exact h

lemma P_lt {a c : ℕ} (h : a < c) : P a + 4 * a + 3 ≤ P c := by
  have h1 := P_mono (show a + 1 ≤ c by omega)
  rw [P_succ] at h1
  exact h1

/-- Block `k` (positions `P k + 1 .. P k + 4k + 3`) reads `A, v0, B, X1, v1, ..., X(2k), v(2k)` with
`A = 2k+2`, `B = 2k+3`, `vj = 2k+1-j`, `Xj = A` for odd `j`, `B` for even `j`; offset `0` is the `1`
at `P k`. -/
def g (k r : ℕ) : ℕ :=
  if r = 0 then 1
  else if r = 1 then 2 * k + 2
  else if r = 2 then 2 * k + 1
  else if r = 3 then 2 * k + 3
  else if r % 2 = 0 then (if r % 4 = 0 then 2 * k + 2 else 2 * k + 3)
  else 2 * k + 1 - (r - 3) / 2

lemma g_le (k r : ℕ) : g k r ≤ 2 * k + 3 := by unfold g; split_ifs <;> omega

lemma g_pos (k r : ℕ) (hr : r ≤ 4 * k + 3) : 1 ≤ g k r := by unfold g; split_ifs <;> omega

lemma g_end (k : ℕ) (hk : 1 ≤ k) : g k (4 * k + 3) = 1 := by unfold g; split_ifs <;> omega

lemma g_occ (k r v : ℕ) (hr : r ≤ 4 * k + 3) (hv : 2 ≤ v) (hvk : v ≤ 2 * k) :
    g k r = v ↔ r = 4 * k + 5 - 2 * v := by
  unfold g; split_ifs <;> omega

lemma g0 (k : ℕ) : g k 0 = 1 := by simp [g]
lemma g1 (k : ℕ) : g k 1 = 2 * k + 2 := by simp [g]
lemma g2 (k : ℕ) : g k 2 = 2 * k + 1 := by simp [g]
lemma g3 (k : ℕ) : g k 3 = 2 * k + 3 := by simp [g]
lemma g4 (k : ℕ) : g k 4 = 2 * k + 2 := by simp [g]

lemma gA (k r : ℕ) (h4 : 4 ≤ r) (h : r % 4 = 0) : g k r = 2 * k + 2 := by
  unfold g; split_ifs <;> omega

lemma gB (k r : ℕ) (h4 : 4 ≤ r) (h : r % 4 = 2) : g k r = 2 * k + 3 := by
  unfold g; split_ifs <;> omega

lemma gV (k r : ℕ) (h5 : 5 ≤ r) (h : r % 2 = 1) : g k r = 2 * k + 1 - (r - 3) / 2 := by
  unfold g; split_ifs <;> omega

lemma g_one (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ 4 * k + 2) (h : g k r = 1) : r = 0 := by
  by_contra hne
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ (4 ≤ r ∧ r % 4 = 0) ∨ (4 ≤ r ∧ r % 4 = 2) ∨
      (5 ≤ r ∧ r % 2 = 1) by omega) with h' | h' | h' | h' | h' | h'
  · subst h'
    rw [g1] at h
    omega
  · subst h'
    rw [g2] at h
    omega
  · subst h'
    rw [g3] at h
    omega
  · rw [gA k r h'.1 h'.2] at h
    omega
  · rw [gB k r h'.1 h'.2] at h
    omega
  · rw [gV k r h'.1 h'.2] at h
    omega

lemma g_pair (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ 4 * k + 2) :
    (r = 0 ∧ g k r = 1 ∧ g k (r + 1) = 2 * k + 2) ∨
    (r = 1 ∧ g k r = 2 * k + 2 ∧ g k (r + 1) = 2 * k + 1) ∨
    (r = 2 ∧ g k r = 2 * k + 1 ∧ g k (r + 1) = 2 * k + 3) ∨
    (r = 3 ∧ g k r = 2 * k + 3 ∧ g k (r + 1) = 2 * k + 2) ∨
    ((4 ≤ r ∧ r % 4 = 0) ∧ g k r = 2 * k + 2 ∧ g k (r + 1) = 2 * k + 1 - (r - 2) / 2) ∨
    ((4 ≤ r ∧ r % 4 = 2) ∧ g k r = 2 * k + 3 ∧ g k (r + 1) = 2 * k + 1 - (r - 2) / 2) ∨
    ((5 ≤ r ∧ r % 4 = 1) ∧ g k r = 2 * k + 1 - (r - 3) / 2 ∧ g k (r + 1) = 2 * k + 3) ∨
    ((5 ≤ r ∧ r % 4 = 3) ∧ g k r = 2 * k + 1 - (r - 3) / 2 ∧ g k (r + 1) = 2 * k + 2) := by
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ (4 ≤ r ∧ r % 4 = 0) ∨ (4 ≤ r ∧ r % 4 = 2) ∨
      (5 ≤ r ∧ r % 4 = 1) ∨ (5 ≤ r ∧ r % 4 = 3) by omega) with h | h | h | h | h | h | h | h
  · subst h
    exact Or.inl ⟨rfl, g0 k, g1 k⟩
  · subst h
    exact Or.inr <| Or.inl ⟨rfl, g1 k, g2 k⟩
  · subst h
    exact Or.inr <| Or.inr <| Or.inl ⟨rfl, g2 k, g3 k⟩
  · subst h
    exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, g3 k, g4 k⟩
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h, gA k r h.1 h.2, ?_⟩
    rw [gV k (r + 1) (by omega) (by omega)]
    omega
  · refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h, gB k r h.1 h.2, ?_⟩
    rw [gV k (r + 1) (by omega) (by omega)]
    omega
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨h, gV k r h.1 (by omega), gB k (r + 1) (by omega) (by omega)⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
      ⟨h, gV k r h.1 (by omega), gA k (r + 1) (by omega) (by omega)⟩

/-! ## The time `T x y` at which the pair `{x, y}` is used: `{b (T x y), b (T x y + 1)} = {x, y}` -/

/-- Offset in block `k` of the pair `{lo, hi}` with `lo < hi` and `hi ∈ {2k+2, 2k+3}`. -/
def O (k lo hi : ℕ) : ℕ :=
  if hi = 2 * k + 2 then
    (if lo = 1 then 0
     else if lo = 2 * k + 1 then 1
     else if (2 * k + 1 - lo) % 2 = 1 then 2 * (2 * k + 1 - lo) + 2
     else 2 * (2 * k + 1 - lo) + 3)
  else
    (if lo = 2 * k + 2 then 3
     else if lo = 2 * k + 1 then 2
     else if lo = 1 then 4 * k + 2
     else if (2 * k + 1 - lo) % 2 = 1 then 2 * (2 * k + 1 - lo) + 3
     else 2 * (2 * k + 1 - lo) + 2)

def T (x y : ℕ) : ℕ :=
  if max x y ≤ 3 then (if min x y = 1 ∧ max x y = 2 then 1 else if min x y = 2 then 2 else 3)
  else P ((max x y - 2) / 2) + O ((max x y - 2) / 2) (min x y) (max x y)

lemma O_le (k lo hi : ℕ) (hk : 1 ≤ k) (hlo : 1 ≤ lo) (hlh : lo < hi)
    (hhi : hi = 2 * k + 2 ∨ hi = 2 * k + 3) : O k lo hi ≤ 4 * k + 2 := by
  unfold O; split_ifs <;> omega

lemma T_symm (x y : ℕ) : T x y = T y x := by unfold T; rw [min_comm, max_comm]

lemma T_block (k x y : ℕ) (hk : 1 ≤ k) (hm : max x y = 2 * k + 2 ∨ max x y = 2 * k + 3) :
    T x y = P k + O k (min x y) (max x y) := by
  have h3 : ¬ (max x y ≤ 3) := by omega
  have h : (max x y - 2) / 2 = k := by omega
  unfold T
  rw [if_neg h3, h]

lemma T_bound (x y : ℕ) (hxy : x ≠ y) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 ≤ T x y ∧ T x y < P ((max x y - 2) / 2 + 1) := by
  by_cases h : max x y ≤ 3
  · have h2 : (max x y - 2) / 2 + 1 = 1 := by omega
    rw [h2, P_one]
    unfold T
    rw [if_pos h]
    split_ifs <;> omega
  · set k := (max x y - 2) / 2 with hk
    have hk1 : 1 ≤ k := by omega
    have hm : max x y = 2 * k + 2 ∨ max x y = 2 * k + 3 := by omega
    rw [T_block k x y hk1 hm, P_succ]
    have h1 := O_le k (min x y) (max x y) hk1 (by omega) (by omega) hm
    have h2 := P_ge k
    omega

lemma T12 : T 1 2 = 1 := by decide
lemma T13 : T 1 3 = 3 := by decide
lemma T23 : T 2 3 = 2 := by decide

/-! ## The explicit sequence `f` -/

def blk (m : ℕ) : ℕ := Nat.findGreatest (fun k => P k ≤ m) m

def f (m : ℕ) : ℕ := if m ≤ 3 then m else g (blk m) (m - P (blk m))

lemma blk_eq (k r : ℕ) (hr : r ≤ 4 * k + 2) : blk (P k + r) = k := by
  unfold blk
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun _ => ?_, fun n hn _ => ?_⟩
  · have := P_ge k
    omega
  · omega
  · have := P_lt hn
    omega

lemma f_small {m : ℕ} (h : m ≤ 3) : f m = m := by unfold f; rw [if_pos h]

lemma f_blk (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ 4 * k + 3) : f (P k + r) = g k r := by
  rcases Nat.lt_or_ge r (4 * k + 3) with h | h
  · have h4 := P_ge4 hk
    have h3 : ¬ (P k + r ≤ 3) := by omega
    unfold f
    rw [if_neg h3, blk_eq k r (by omega)]
    congr 1
    omega
  · have hr' : r = 4 * k + 3 := by omega
    subst hr'
    have e : P k + (4 * k + 3) = P (k + 1) + 0 := by
      have := P_succ k
      omega
    have h4 := P_ge4 (show 1 ≤ k + 1 by omega)
    have h3 : ¬ (P (k + 1) + 0 ≤ 3) := by omega
    rw [e, g_end k hk]
    unfold f
    rw [if_neg h3, blk_eq (k + 1) 0 (by omega)]
    simp [g]

lemma f1 : f 1 = 1 := f_small (by norm_num)
lemma f2 : f 2 = 2 := f_small (by norm_num)
lemma f3 : f 3 = 3 := f_small (by norm_num)
lemma f4 : f 4 = 1 := by
  have h := f_blk 1 0 le_rfl (by norm_num)
  rw [P_one] at h
  simpa [g] using h

lemma L_dec (m : ℕ) (hm : 4 ≤ m) : ∃ k r, 1 ≤ k ∧ r ≤ 4 * k + 2 ∧ m = P k + r := by
  have hP1 : P 1 ≤ m := by rw [P_one]; exact hm
  have key := (Nat.findGreatest_eq_iff (P := fun k => P k ≤ m) (k := m) (m := blk m)).1 rfl
  have hspec : P (blk m) ≤ m :=
    Nat.findGreatest_spec (P := fun k => P k ≤ m) (by omega : 1 ≤ m) hP1
  have h1 : 1 ≤ blk m := Nat.le_findGreatest (P := fun k => P k ≤ m) (by omega : 1 ≤ m) hP1
  have h2 : ¬ P (blk m + 1) ≤ m := by
    intro h
    by_cases hb : blk m + 1 ≤ m
    · exact key.2.2 (show blk m < blk m + 1 by omega) hb h
    · have := P_ge (blk m + 1)
      omega
  rw [P_succ] at h2
  exact ⟨blk m, m - P (blk m), h1, by omega, by omega⟩

lemma f_blk' (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ 4 * k + 2) : f (P k + r + 1) = g k (r + 1) := by
  rw [Nat.add_assoc]
  exact f_blk k (r + 1) hk (by omega)

/-! ## Each step uses a new pair, at time `t`; and every pair is used, at time `T` -/

lemma e_blk (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ 4 * k + 2) :
    T (g k r) (g k (r + 1)) = P k + r ∧ g k r ≠ g k (r + 1) ∧ 1 ≤ g k r ∧ 1 ≤ g k (r + 1) := by
  have hm : max (g k r) (g k (r + 1)) = 2 * k + 2 ∨ max (g k r) (g k (r + 1)) = 2 * k + 3 := by
    rcases g_pair k r hk hr with ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ |
        ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ <;>
    (rw [e1, e2]; omega)
  rw [T_block k _ _ hk hm]
  rcases g_pair k r hk hr with ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ |
      ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ <;>
  (rw [e1, e2]; refine ⟨?_, by omega, by omega, by omega⟩; unfold O; split_ifs <;> omega)

lemma L_e (m : ℕ) (hm : 1 ≤ m) :
    T (f m) (f (m + 1)) = m ∧ f m ≠ f (m + 1) ∧ 1 ≤ f m ∧ 1 ≤ f (m + 1) := by
  by_cases h3 : m ≤ 3
  · have hf : f m = m := f_small h3
    rw [hf]
    rcases Nat.lt_or_ge m 3 with h | h
    · rw [f_small (show m + 1 ≤ 3 by omega)]
      interval_cases m <;> decide
    · obtain rfl : m = 3 := by omega
      rw [show (3 : ℕ) + 1 = 4 from rfl, f4]
      decide
  · obtain ⟨k, r, hk, hr, rfl⟩ := L_dec m (by omega)
    rw [f_blk k r hk (by omega), f_blk' k r hk hr]
    exact e_blk k r hk hr

lemma L_inv_lt (x y : ℕ) (hx : 1 ≤ x) (hxy : x < y) :
    1 ≤ T x y ∧ ((f (T x y) = x ∧ f (T x y + 1) = y) ∨ (f (T x y) = y ∧ f (T x y + 1) = x)) := by
  by_cases h : y ≤ 3
  · have hx3 : x ≤ 2 := by omega
    interval_cases x <;> interval_cases y <;> simp [T12, T13, T23, f1, f2, f3, f4]
  · set k := (y - 2) / 2 with hk
    have hk1 : 1 ≤ k := by omega
    have hhi : y = 2 * k + 2 ∨ y = 2 * k + 3 := by omega
    have hmax : max x y = y := max_eq_right hxy.le
    have hmin : min x y = x := min_eq_left hxy.le
    rw [T_block k x y hk1 (by omega), hmin, hmax]
    have hO := O_le k x y hk1 hx hxy hhi
    have hP := P_ge k
    refine ⟨by omega, ?_⟩
    rw [f_blk k (O k x y) hk1 (by omega), Nat.add_assoc, f_blk k (O k x y + 1) hk1 (by omega)]
    rcases g_pair k (O k x y) hk1 hO with ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ |
        ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ <;>
    (rw [e1, e2]; simp only [O] at hc ⊢; split_ifs at hc ⊢ <;> omega)

lemma L_inv (x y : ℕ) (hxy : x ≠ y) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 ≤ T x y ∧ ((f (T x y) = x ∧ f (T x y + 1) = y) ∨ (f (T x y) = y ∧ f (T x y + 1) = x)) := by
  rcases Nat.lt_or_gt_of_ne hxy with h | h
  · exact L_inv_lt x y hx h
  · obtain ⟨h1, h2⟩ := L_inv_lt y x hy h
    rw [T_symm x y]
    exact ⟨h1, h2.symm⟩

/-! ## The list `L t = [f 1, ..., f t]` and its adjacent pairs -/

def L (t : ℕ) : List ℕ := (List.range t).map (fun i => f (i + 1))

lemma getL (t i x : ℕ) : (L t)[i]? = some x ↔ i < t ∧ f (i + 1) = x := by
  unfold L
  rw [List.getElem?_map]
  by_cases h : i < t
  · rw [List.getElem?_range h]
    simp [h]
  · have h' : (List.range t).length ≤ i := by
      rw [List.length_range]
      omega
    rw [List.getElem?_eq_none h']
    simp [h]

lemma L_succ (t : ℕ) : L (t + 1) = L t ++ [f (t + 1)] := by
  unfold L
  rw [show List.range (t + 1) = List.range t ++ [t] from List.range_succ, List.map_append]
  rfl

lemma L_last (t : ℕ) : (L (t + 1)).getLastD 0 = f (t + 1) := by
  rw [L_succ, List.getLastD_concat]

lemma L_used (t x y : ℕ) : IsAdj (L t) x y ↔ (x ≠ y ∧ 1 ≤ x ∧ 1 ≤ y ∧ T x y < t) := by
  constructor
  · rintro ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · simp only [getL] at h1 h2
      obtain ⟨hi1, rfl⟩ := h1
      obtain ⟨hi2, rfl⟩ := h2
      obtain ⟨e1, e2, e3, e4⟩ := L_e (i + 1) (by omega)
      exact ⟨e2, e3, e4, by omega⟩
    · simp only [getL] at h1 h2
      obtain ⟨hi1, rfl⟩ := h1
      obtain ⟨hi2, rfl⟩ := h2
      obtain ⟨e1, e2, e3, e4⟩ := L_e (i + 1) (by omega)
      refine ⟨Ne.symm e2, e4, e3, ?_⟩
      rw [T_symm]
      omega
  · rintro ⟨hne, hx, hy, hT⟩
    obtain ⟨hT1, h⟩ := L_inv x y hne hx hy
    obtain ⟨m, hm⟩ : ∃ m, T x y = m + 1 := ⟨T x y - 1, by omega⟩
    rw [hm] at h hT
    refine ⟨m, ?_⟩
    simp only [getL]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨⟨by omega, h1⟩, ⟨by omega, h2⟩⟩
    · exact Or.inr ⟨⟨by omega, h1⟩, ⟨by omega, h2⟩⟩

/-! ## Every pair preferred to the next term is already used -/

lemma Cblk (k r y : ℕ) (hk : 1 ≤ k) (hr : r ≤ 4 * k + 2) (hy : 1 ≤ y) (hne : y ≠ g k r)
    (hb : (g k (r + 1) < y ∧ y < g k r) ∨ (g k r < g k (r + 1) ∧ y < g k (r + 1))) :
    T (g k r) y < P k + r := by
  have hg1 := g_le k r
  have hg2 := g_le k (r + 1)
  have hg0 := g_pos k r (by omega)
  by_cases hm : max (g k r) y ≤ 2 * k + 1
  · obtain ⟨_, h2⟩ := T_bound (g k r) y (Ne.symm hne) hg0 hy
    have h3 : P ((max (g k r) y - 2) / 2 + 1) ≤ P k := P_mono (by omega)
    omega
  · rw [T_block k (g k r) y hk (by omega)]
    suffices O k (min (g k r) y) (max (g k r) y) < r by omega
    rcases g_pair k r hk hr with ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ |
        ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ | ⟨hc, e1, e2⟩ <;>
    (rw [e1, e2] at hb; rw [e1] at hne hm ⊢; unfold O; split_ifs <;> omega)

lemma C_all (t : ℕ) (ht : 1 ≤ t) (y : ℕ) (hy : 1 ≤ y) (hne : y ≠ f t)
    (hb : (f (t + 1) < y ∧ y < f t) ∨ (f t < f (t + 1) ∧ y < f (t + 1))) : T (f t) y < t := by
  by_cases h3 : t ≤ 3
  · have hf : f t = t := f_small h3
    rw [hf] at hne hb ⊢
    rcases Nat.lt_or_ge t 3 with h | h
    · rw [f_small (show t + 1 ≤ 3 by omega)] at hb
      obtain rfl : t = 2 := by omega
      obtain rfl : y = 1 := by omega
      decide
    · have h4 : f (t + 1) = 1 := by
        rw [show t + 1 = 4 by omega]
        exact f4
      rw [h4] at hb
      obtain rfl : t = 3 := by omega
      obtain rfl : y = 2 := by omega
      decide
  · obtain ⟨k, r, hk, hr, rfl⟩ := L_dec t (by omega)
    rw [f_blk k r hk (by omega)] at hne hb ⊢
    rw [f_blk' k r hk hr] at hb
    exact Cblk k r y hk hr hy hne hb

/-! ## The greedy step, and `pre t = L t` -/

lemma nextTerm_eq (l : List ℕ) (x w : ℕ) (hx : l.getLastD 0 = x) (hw1 : 1 ≤ w) (hwx : w ≠ x)
    (hnew : ¬ IsAdj l x w)
    (hbet : ∀ y, 1 ≤ y → y ≠ x → ((w < y ∧ y < x) ∨ (x < w ∧ y < w)) → IsAdj l x y) :
    nextTerm l = w := by
  unfold nextTerm
  rw [hx]
  split_ifs with h
  · have hwx' : w < x := by
      by_contra hc
      obtain ⟨y, hy1, hyx, hyn⟩ := h
      exact hyn (hbet y hy1 (by omega) (Or.inr ⟨by omega, by omega⟩))
    apply IsGreatest.csSup_eq
    refine ⟨⟨hw1, hwx', hnew⟩, ?_⟩
    rintro y ⟨hy1, hyx, hyn⟩
    by_contra hc
    exact hyn (hbet y hy1 (by omega) (Or.inl ⟨by omega, hyx⟩))
  · have hxw : x < w := by
      by_contra hc
      exact h ⟨w, hw1, by omega, hnew⟩
    apply IsLeast.csInf_eq
    refine ⟨⟨hxw, hnew⟩, ?_⟩
    rintro y ⟨hxy, hyn⟩
    by_contra hc
    exact hyn (hbet y (by omega) (by omega) (Or.inr ⟨hxw, by omega⟩))

lemma L_step (t : ℕ) (ht : 1 ≤ t) : nextTerm (L t) = f (t + 1) := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  obtain ⟨hT, hne, h1, h2⟩ := L_e (u + 1) (by omega)
  apply nextTerm_eq (L (u + 1)) (f (u + 1)) (f (u + 1 + 1)) (L_last u) h2 (Ne.symm hne)
  · rw [L_used]
    omega
  · intro y hy hyx hb
    rw [L_used]
    exact ⟨Ne.symm hyx, h1, hy, C_all (u + 1) (by omega) y hy hyx hb⟩

lemma pre_eq : ∀ t, pre t = L t
  | 0 => by simp [pre, L]
  | t + 1 => by
    have h : (if t = 0 then 1 else nextTerm (L t)) = f (t + 1) := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        simp [f1]
      · have h0' : t ≠ 0 := by omega
        rw [if_neg h0']
        exact L_step t h0
    rw [pre, pre_eq t, h, L_succ]

lemma b_eq (n : ℕ) (hn : 1 ≤ n) : b n = f n := by
  obtain ⟨u, rfl⟩ : ∃ u, n = u + 1 := ⟨n - 1, by omega⟩
  unfold b
  rw [pre_eq, L_last]

lemma b_zero : b 0 = 0 := by
  unfold b
  rw [pre_eq]
  rfl

lemma b_blk (k r : ℕ) (hk : 1 ≤ k) (hr : r ≤ 4 * k + 3) : b (P k + r) = g k r := by
  have := P_ge k
  rw [b_eq (P k + r) (by omega), f_blk k r hk hr]

/-- The value `1` occurs exactly at the block starts `P k`. -/
lemma ones (m : ℕ) : b m = 1 ↔ ∃ k, m = P k := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      rw [b_zero] at h
      omega
    · rw [b_eq m h0] at h
      by_cases h3 : m ≤ 3
      · rw [f_small h3] at h
        exact ⟨0, by simp only [P]; omega⟩
      · obtain ⟨k, r, hk, hr, rfl⟩ := L_dec m (by omega)
        rw [f_blk k r hk (by omega)] at h
        have := g_one k r hk hr h
        exact ⟨k, by omega⟩
  · rintro ⟨k, rfl⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [show P 0 = 1 from rfl, b_eq 1 le_rfl, f1]
    · have := b_blk k 0 h0 (by omega)
      rw [Nat.add_zero] at this
      rw [this]
      simp [g]

lemma next_occ (p q v : ℕ) (hpq : p < q) (hq : b q = v) (hne : ∀ m, p < m → m < q → b m ≠ v) :
    sInf {m : ℕ | p < m ∧ b m = v} = q := by
  apply IsLeast.csInf_eq
  refine ⟨⟨hpq, hq⟩, ?_⟩
  rintro m ⟨h1, h2⟩
  by_contra hc
  exact hne m h1 (by omega) h2

/-! ## A100039 -/

lemma s1_eq : s 1 = 22 := by
  have h22 : b 22 = 1 := (ones 22).2 ⟨3, rfl⟩
  have hcount : Nat.count (fun m => b m = 1) 22 = 3 := by
    rw [Nat.count_eq_card_filter_range]
    have hfil : (Finset.range 22).filter (fun m => b m = 1) = {1, 4, 11} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, ones]
      constructor
      · rintro ⟨hm, k, rfl⟩
        have hk : k < 3 := by
          by_contra hc
          have h1 := P_mono (show 3 ≤ k by omega)
          have h2 : P 3 = 22 := rfl
          omega
        interval_cases k <;> simp [P]
      · rintro (rfl | rfl | rfl)
        · exact ⟨by norm_num, 0, rfl⟩
        · exact ⟨by norm_num, 1, rfl⟩
        · exact ⟨by norm_num, 2, rfl⟩
    rw [hfil]
    rfl
  have h := Nat.nth_count (p := fun m => b m = 1) h22
  rw [hcount] at h
  rw [s, if_pos rfl]
  exact h

lemma s_succ (n : ℕ) (hn : 1 ≤ n) : s (n + 1) = sInf {m : ℕ | s n < m ∧ b m = n + 1} := by
  have h : n ≠ 0 := by omega
  rw [s, if_neg h]

lemma s_formula (n : ℕ) : s (n + 1) = 2 * (n + 1) ^ 2 + 7 * (n + 1) + 13 := by
  induction n with
  | zero =>
    show s 1 = 22
    exact s1_eq
  | succ n ih =>
    rw [s_succ (n + 1) (by omega), ih]
    have hQ1 : 2 * (n + 1) ^ 2 + 7 * (n + 1) + 13 = P (n + 2) + 2 * n + 11 := by unfold P; ring
    have hQ2 : 2 * (n + 1 + 1) ^ 2 + 7 * (n + 1 + 1) + 13 = P (n + 3) + (2 * n + 13) := by
      unfold P; ring
    have hPs : P (n + 3) = P (n + 2) + 4 * (n + 2) + 3 := P_succ (n + 2)
    rw [hQ1, hQ2]
    apply next_occ
    · omega
    · rw [b_blk (n + 3) (2 * n + 13) (by omega) (by omega),
        g_occ (n + 3) (2 * n + 13) (n + 1 + 1) (by omega) (by omega) (by omega)]
      omega
    · intro m h1 h2 hbm
      rcases Nat.lt_or_ge m (P (n + 3)) with h3 | h3
      · obtain ⟨r, rfl⟩ : ∃ r, m = P (n + 2) + r := ⟨m - P (n + 2), by omega⟩
        rw [b_blk (n + 2) r (by omega) (by omega),
          g_occ (n + 2) r (n + 1 + 1) (by omega) (by omega) (by omega)] at hbm
        omega
      · obtain ⟨r, rfl⟩ : ∃ r, m = P (n + 3) + r := ⟨m - P (n + 3), by omega⟩
        rw [b_blk (n + 3) r (by omega) (by omega),
          g_occ (n + 3) r (n + 1 + 1) (by omega) (by omega) (by omega)] at hbm
        omega

end OMA.A100039Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a100039.main := by
  intro n hn
  obtain ⟨u, rfl⟩ : ∃ u, n = u + 1 := ⟨n - 1, by omega⟩
  exact OMA.A100039Proof.s_formula u
