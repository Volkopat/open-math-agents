import OMAStatements.S_oeis_a270167
import Mathlib
/-!
Proof of the conjectures of the statement oeis-a270167 (OEIS A270167), Rule 107.

Method: stage t of the automaton is described exactly by an explicit region of the plane
(defined by linear inequalities and a parity condition); one step of the rule maps the description
at t to the one at t + 1 (a case split on the five cells of the neighbourhood, closed by omega).
The ON cells of the square are then counted row by row in closed form, and every conjecture
reduces to a polynomial identity in n and (-1)^n.
-/

namespace OMA.CA_a270167

open OMA.S_oeis_a270167 PowerSeries

abbrev P := ℤ × ℤ

/-- A pattern: background `b` everywhere except on the finite list `L`, where the value is `!b`. -/
def pic (b : Bool) (L : List P) : ℤ → ℤ → Bool := fun i j => if (i, j) ∈ L then !b else b

/-- One synchronous step of the automaton with Wolfram code `code`. -/
def nxt (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

theorem cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i j
  rfl

theorem cell_zero (code : ℕ) : cell code 0 = pic false [(0, 0)] := by
  funext i j
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · have h' : (i, j) ∉ [((0 : ℤ), (0 : ℤ))] := by
      simp only [List.mem_singleton, Prod.mk.injEq]
      exact h
    simp only [cell, pic, if_neg h']
    exact decide_eq_false h

/-- Every point of the list lies in the square `[-R, R]²`. -/
def inR (R : ℕ) (L : List P) : Prop :=
  ∀ p ∈ L, -(R : ℤ) ≤ p.1 ∧ p.1 ≤ R ∧ -(R : ℤ) ≤ p.2 ∧ p.2 ≤ R

instance (R : ℕ) (L : List P) : Decidable (inR R L) := by
  unfold inR
  infer_instance

theorem pic_far {R : ℕ} {L : List P} (hL : inR R L) (b : Bool) (u v : ℤ)
    (h : ¬(-(R : ℤ) ≤ u ∧ u ≤ R ∧ -(R : ℤ) ≤ v ∧ v ≤ R)) : pic b L u v = b := by
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp only [pic, if_neg hm]

/-- The coordinates `-(R+1), ..., R+1`. -/
def box (R : ℕ) : List ℤ := List.map (fun k : ℕ => (k : ℤ) - ((R : ℤ) + 1)) (List.range (2 * R + 3))

theorem mem_box (R : ℕ) (x : ℤ) (h1 : -((R : ℤ) + 1) ≤ x) (h2 : x ≤ R + 1) : x ∈ box R := by
  have e : (((x + R + 1).toNat : ℕ) : ℤ) = x + R + 1 := Int.toNat_of_nonneg (by omega)
  refine List.mem_map.mpr ⟨(x + R + 1).toNat, List.mem_range.mpr ?_, ?_⟩
  · have : (((x + R + 1).toNat : ℕ) : ℤ) < ((2 * R + 3 : ℕ) : ℤ) := by push_cast; omega
    exact_mod_cast this
  · omega

theorem step {code R : ℕ} {b b' : Bool} {L L' : List P} (hL : inR R L) (hL' : inR R L')
    (hbg : code.testBit (b.toNat + 2 * (b.toNat + b.toNat + b.toNat + b.toNat)) = b')
    (hbox : ∀ x ∈ box R, ∀ y ∈ box R, nxt code (pic b L) x y = pic b' L' x y) :
    nxt code (pic b L) = pic b' L' := by
  funext x y
  by_cases h : (-((R : ℤ) + 1) ≤ x ∧ x ≤ R + 1) ∧ (-((R : ℤ) + 1) ≤ y ∧ y ≤ R + 1)
  · exact hbox x (mem_box R x h.1.1 h.1.2) y (mem_box R y h.2.1 h.2.2)
  · rw [pic_far hL' b' x y (by omega)]
    simp only [nxt]
    rw [pic_far hL b x y (by omega), pic_far hL b (x + 1) y (by omega),
      pic_far hL b (x - 1) y (by omega), pic_far hL b x (y + 1) (by omega),
      pic_far hL b x (y - 1) (by omega)]
    exact hbg

theorem sum_single (t : ℕ) (p : P) (h : -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if ((i : ℤ) - t, (j : ℤ) - t) = p then (1 : ℤ) else 0) = 1 := by
  obtain ⟨p1, p2⟩ := p
  simp only at h
  rw [Finset.sum_eq_single (p1 + t).toNat, Finset.sum_eq_single (p2 + t).toNat]
  · rw [if_pos]
    simp only [Prod.mk.injEq]
    constructor <;> omega
  · intro j _ hj
    rw [if_neg]
    simp only [Prod.mk.injEq, not_and]
    intro _ h2
    omega
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    simp only [Prod.mk.injEq, not_and]
    intro h1
    omega
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

theorem sum_mem (t : ℕ) (L : List P) (hn : L.Nodup) (hb : inR t L) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if ((i : ℤ) - t, (j : ℤ) - t) ∈ L then (1 : ℤ) else 0) = L.length := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hn).1
    have e : ∀ i j : ℕ, (if ((i : ℤ) - t, (j : ℤ) - t) ∈ p :: L then (1 : ℤ) else 0) =
        (if ((i : ℤ) - t, (j : ℤ) - t) = p then 1 else 0) +
        (if ((i : ℤ) - t, (j : ℤ) - t) ∈ L then 1 else 0) := by
      intro i j
      by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) = p
      · rw [h1]
        simp [hp]
      · simp [h1]
    simp only [e, Finset.sum_add_distrib]
    rw [sum_single t p (hb p List.mem_cons_self),
      ih (List.nodup_cons.mp hn).2 (fun q hq => hb q (List.mem_cons_of_mem _ hq))]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

theorem count_false (code t : ℕ) (L : List P) (hn : L.Nodup) (hb : inR t L)
    (h : cell code t = pic false L) : (onCount code t : ℤ) = L.length := by
  rw [← sum_mem t L hn hb]
  simp only [onCount, h, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [pic, hm]

theorem count_true (code t : ℕ) (L : List P) (hn : L.Nodup) (hb : inR t L)
    (h : cell code t = pic true L) :
    (onCount code t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - L.length := by
  have hs : (onCount code t : ℤ) = ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      ((1 : ℤ) - (if ((i : ℤ) - t, (j : ℤ) - t) ∈ L then (1 : ℤ) else 0)) := by
    simp only [onCount, h, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [pic, hm]
  rw [hs]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  rw [sum_mem t L hn hb]
  push_cast
  ring

def L0 : List P := [(0, 0)]
def L1 : List P := [(-1, 0), (0, -1), (0, 1), (1, 0)]
def L2 : List P := [(-1, -1), (-1, 1), (0, 0), (1, -1), (1, 1)]
def L3 : List P := [(-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)]
def L4 : List P := [(-2, -2), (-2, 0), (-2, 2), (-1, -1), (-1, 1), (0, -2), (0, 2), (1, -1), (1, 1), (2, -2), (2, 0), (2, 2)]
def L5 : List P := [(-3, -2), (-3, 0), (-3, 2), (-2, -3), (-2, 3), (0, -3), (0, 3), (2, -3), (2, 3), (3, -2), (3, 0), (3, 2)]
def L6 : List P := [(-3, -3), (-3, -1), (-3, 1), (-3, 3), (-2, -2), (-2, 2), (-1, -3), (-1, 3), (1, -3), (1, 3), (2, -2), (2, 2), (3, -3), (3, -1), (3, 1), (3, 3)]
def L7 : List P := [(-4, -3), (-4, -1), (-4, 1), (-4, 3), (-3, -4), (-3, 0), (-3, 4), (-2, -1), (-2, 1), (-1, -4), (-1, -2), (-1, 2), (-1, 4), (0, -3), (0, 3), (1, -4), (1, -2), (1, 2), (1, 4), (2, -1), (2, 1), (3, -4), (3, 0), (3, 4), (4, -3), (4, -1), (4, 1), (4, 3)]
def L8 : List P := [(-4, -4), (-4, -2), (-4, 0), (-4, 2), (-4, 4), (-3, -3), (-3, -1), (-3, 1), (-3, 3), (-2, -4), (-2, -2), (-2, 0), (-2, 2), (-2, 4), (-1, -3), (-1, -1), (-1, 1), (-1, 3), (0, -4), (0, -2), (0, 2), (0, 4), (1, -3), (1, -1), (1, 1), (1, 3), (2, -4), (2, -2), (2, 0), (2, 2), (2, 4), (3, -3), (3, -1), (3, 1), (3, 3), (4, -4), (4, -2), (4, 0), (4, 2), (4, 4)]

theorem lay0 : cell 107 0 = pic false L0 := cell_zero 107

theorem lay1 : cell 107 1 = pic true L1 := by
  rw [cell_succ, lay0]
  exact step (R := 8) (by decide) (by decide) (by decide) (by decide)

theorem lay2 : cell 107 2 = pic false L2 := by
  rw [cell_succ, lay1]
  exact step (R := 8) (by decide) (by decide) (by decide) (by decide)

theorem lay3 : cell 107 3 = pic true L3 := by
  rw [cell_succ, lay2]
  exact step (R := 8) (by decide) (by decide) (by decide) (by decide)

theorem lay4 : cell 107 4 = pic false L4 := by
  rw [cell_succ, lay3]
  exact step (R := 8) (by decide) (by decide) (by decide) (by decide)

theorem lay5 : cell 107 5 = pic true L5 := by
  rw [cell_succ, lay4]
  exact step (R := 8) (by decide) (by decide) (by decide) (by decide)

theorem lay6 : cell 107 6 = pic false L6 := by
  rw [cell_succ, lay5]
  exact step (R := 8) (by decide) (by decide) (by decide) (by decide)

theorem lay7 : cell 107 7 = pic true L7 := by
  rw [cell_succ, lay6]
  exact step (R := 8) (by decide) (by decide) (by decide) (by decide)

theorem lay8 : cell 107 8 = pic false L8 := by
  rw [cell_succ, lay7]
  exact step (R := 8) (by decide) (by decide) (by decide) (by decide)

/-- The square `[-k, k]²`. -/
abbrev Bx (k : ℤ) (x y : ℤ) : Prop := -k ≤ x ∧ x ≤ k ∧ -k ≤ y ∧ y ≤ k

/-- Stage `2m` (for `m ≥ 4`): the even cells of the square `[-m, m]²` except the origin. -/
def FE (m : ℕ) (x y : ℤ) : Bool := decide (Bx m x y ∧ (x + y) % 2 = 0 ∧ ¬(x = 0 ∧ y = 0))

/-- Stage `2m+1` (for `m ≥ 4`): every cell is ON except the odd cells of the square `[-(m-1), m-1]²`
outside `[-1, 1]²` and the odd cells of the frame `[-(m+1), m+1]² \ [-m, m]²`. -/
def FO (m : ℕ) (x y : ℤ) : Bool :=
  decide (¬((x + y) % 2 = 1 ∧ ((Bx ((m : ℤ) - 1) x y ∧ ¬Bx 1 x y) ∨ (Bx ((m : ℤ) + 1) x y ∧ ¬Bx m x y))))

set_option maxHeartbeats 4000000 in
theorem stepE (m : ℕ) (hm : 4 ≤ m) (x y : ℤ) : nxt 107 (FE m) x y = FO m x y := by
  simp only [nxt]
  cases h0 : FE m x y <;> cases h1 : FE m (x + 1) y <;> cases h2 : FE m (x - 1) y <;>
    cases h3 : FE m x (y + 1) <;> cases h4 : FE m x (y - 1) <;>
    simp only [FE, FO, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true,
      Bool.toNat_false, Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 h3 h4 ⊢ <;>
    norm_num <;> push_cast at * <;> omega

set_option maxHeartbeats 4000000 in
theorem stepO (m : ℕ) (hm : 4 ≤ m) (x y : ℤ) : nxt 107 (FO m) x y = FE (m + 1) x y := by
  simp only [nxt]
  cases h0 : FO m x y <;> cases h1 : FO m (x + 1) y <;> cases h2 : FO m (x - 1) y <;>
    cases h3 : FO m x (y + 1) <;> cases h4 : FO m x (y - 1) <;>
    simp only [FE, FO, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true,
      Bool.toNat_false, Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 h3 h4 ⊢ <;>
    norm_num <;> push_cast at * <;> omega

theorem base8 : cell 107 8 = FE 4 := by
  rw [lay8]
  funext x y
  by_cases h : (-((8 : ℕ) : ℤ) - 1 ≤ x ∧ x ≤ (8 : ℕ) + 1) ∧ (-((8 : ℕ) : ℤ) - 1 ≤ y ∧ y ≤ (8 : ℕ) + 1)
  · have hb : ∀ x ∈ box 8, ∀ y ∈ box 8, pic false L8 x y = FE 4 x y := by decide
    exact hb x (mem_box 8 x (by omega) h.1.2) y (mem_box 8 y (by omega) h.2.2)
  · rw [pic_far (R := 8) (by decide) false x y (by omega)]
    simp only [FE, Bx]
    symm
    apply decide_eq_false
    push_cast
    omega

theorem cellEO (k : ℕ) : cell 107 (2 * (4 + k)) = FE (4 + k) ∧
    cell 107 (2 * (4 + k) + 1) = FO (4 + k) := by
  induction k with
  | zero =>
    refine ⟨base8, ?_⟩
    rw [cell_succ, base8]
    funext x y
    exact stepE 4 (by norm_num) x y
  | succ k ih =>
    have h0 : cell 107 (2 * (4 + (k + 1))) = FE (4 + (k + 1)) := by
      rw [show 2 * (4 + (k + 1)) = 2 * (4 + k) + 1 + 1 by ring, cell_succ, ih.2]
      funext x y
      exact stepO (4 + k) (by omega) x y
    refine ⟨h0, ?_⟩
    rw [cell_succ, h0]
    funext x y
    exact stepE (4 + (k + 1)) (by omega) x y

theorem cellE (m : ℕ) (hm : 4 ≤ m) : cell 107 (2 * m) = FE m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 + k := ⟨m - 4, by omega⟩
  exact (cellEO k).1

theorem cellO (m : ℕ) (hm : 4 ≤ m) : cell 107 (2 * m + 1) = FO m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 4 + k := ⟨m - 4, by omega⟩
  exact (cellEO k).2

/-- The number of `j < N` with `lo ≤ j ≤ hi` and `j % 2 = p`. -/
def cntc (lo hi p N : ℕ) : ℕ := (max (min N (hi + 1)) lo + 1 - p) / 2 - (lo + 1 - p) / 2

theorem cnt (lo hi p N : ℕ) (hp : p < 2) :
    ∑ j ∈ Finset.range N, (if lo ≤ j ∧ j ≤ hi ∧ j % 2 = p then 1 else 0) = cntc lo hi p N := by
  induction N with
  | zero => simp only [cntc, Finset.range_zero, Finset.sum_empty]; omega
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [cntc]
    split_ifs <;> omega

theorem outer (lo hi N : ℕ) (g : ℕ → ℕ) :
    ∑ i ∈ Finset.range N, (if lo ≤ i ∧ i ≤ hi then g (i % 2) else 0) =
      g 0 * cntc lo hi 0 N + g 1 * cntc lo hi 1 N := by
  have e : ∀ i : ℕ, (if lo ≤ i ∧ i ≤ hi then g (i % 2) else 0) =
      g 0 * (if lo ≤ i ∧ i ≤ hi ∧ i % 2 = 0 then 1 else 0) +
      g 1 * (if lo ≤ i ∧ i ≤ hi ∧ i % 2 = 1 then 1 else 0) := by
    intro i
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · by_cases hb : lo ≤ i ∧ i ≤ hi
      · rw [if_pos hb, if_pos ⟨hb.1, hb.2, h⟩, if_neg (by omega), h]
        ring
      · rw [if_neg hb, if_neg (by omega), if_neg (by omega)]
        ring
    · by_cases hb : lo ≤ i ∧ i ≤ hi
      · rw [if_pos hb, if_neg (by omega), if_pos ⟨hb.1, hb.2, h⟩, h]
        ring
      · rw [if_neg hb, if_neg (by omega), if_neg (by omega)]
        ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [cnt lo hi 0 N (by norm_num), cnt lo hi 1 N (by norm_num)]

/-- The cells of parity `p` of the square of half-width `k` centred at `(t, t)`, in index coordinates. -/
abbrev RP (t k p i j : ℕ) : Prop := t - k ≤ i ∧ i ≤ t + k ∧ t - k ≤ j ∧ j ≤ t + k ∧ (i + j) % 2 = p

theorem rowRP (t k p i : ℕ) (hp : p < 2) :
    ∑ j ∈ Finset.range (2 * t + 1), (if RP t k p i j then 1 else 0) =
      if t - k ≤ i ∧ i ≤ t + k then cntc (t - k) (t + k) ((p + i % 2) % 2) (2 * t + 1) else 0 := by
  split_ifs with hb
  · rw [← cnt _ _ ((p + i % 2) % 2) _ (by omega)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [RP]
    split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)
  · refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [if_neg]
    simp only [RP]
    omega

theorem sqN (t k p : ℕ) (hk : k ≤ t) (hp : p < 2) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1), (if RP t k p i j then 1 else 0) =
      2 * k ^ 2 + 2 * k + 1 - p := by
  rw [Finset.sum_congr rfl (fun i _ => rowRP t k p i hp)]
  rw [outer _ _ _ (fun r => cntc (t - k) (t + k) ((p + r) % 2) (2 * t + 1))]
  have key : (cntc (t - k) (t + k) 0 (2 * t + 1) = k + 1 ∧ cntc (t - k) (t + k) 1 (2 * t + 1) = k) ∨
      (cntc (t - k) (t + k) 0 (2 * t + 1) = k ∧ cntc (t - k) (t + k) 1 (2 * t + 1) = k + 1) := by
    simp only [cntc]
    omega
  interval_cases p <;> simp only [Nat.add_zero, Nat.zero_add, Nat.zero_mod, Nat.one_mod,
    show (1 + 1) % 2 = 0 by norm_num] <;>
    rcases key with ⟨k0, k1⟩ | ⟨k0, k1⟩ <;> rw [k0, k1] <;> ring_nf <;> omega

theorem sqZ (t k p : ℕ) (hk : k ≤ t) (hp : p < 2) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1), (if RP t k p i j then (1 : ℤ) else 0) =
      2 * (k : ℤ) ^ 2 + 2 * k + 1 - p := by
  have h := congrArg (fun z : ℕ => (z : ℤ)) (sqN t k p hk hp)
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at h
  rw [h]
  push_cast [show p ≤ 2 * k ^ 2 + 2 * k + 1 by omega]
  ring

theorem cntE (m : ℕ) (hm : 4 ≤ m) : (onCount 107 (2 * m) : ℤ) = 2 * (m : ℤ) ^ 2 + 2 * m := by
  have hs : (onCount 107 (2 * m) : ℤ) = ∑ i ∈ Finset.range (2 * (2 * m) + 1), ∑ j ∈ Finset.range (2 * (2 * m) + 1),
      ((if RP (2 * m) m 0 i j then (1 : ℤ) else 0) - (if RP (2 * m) 0 0 i j then (1 : ℤ) else 0)) := by
    simp only [onCount, cellE m hm, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [FE, Bx, RP, decide_eq_true_eq]
    push_cast
    split_ifs <;> omega
  rw [hs]
  simp only [Finset.sum_sub_distrib]
  rw [sqZ _ _ _ (by omega) (by norm_num), sqZ _ _ _ (by omega) (by norm_num)]
  push_cast
  ring

theorem cntO (m : ℕ) (hm : 4 ≤ m) :
    (onCount 107 (2 * m + 1) : ℤ) = (4 * (m : ℤ) + 3) ^ 2 - (2 * (m : ℤ) ^ 2 + 2 * m) := by
  have hs : (onCount 107 (2 * m + 1) : ℤ) =
      ∑ i ∈ Finset.range (2 * (2 * m + 1) + 1), ∑ j ∈ Finset.range (2 * (2 * m + 1) + 1),
      ((1 : ℤ) - ((if RP (2 * m + 1) (m - 1) 1 i j then (1 : ℤ) else 0) -
        (if RP (2 * m + 1) 1 1 i j then (1 : ℤ) else 0) +
        (if RP (2 * m + 1) (m + 1) 1 i j then (1 : ℤ) else 0) -
        (if RP (2 * m + 1) m 1 i j then (1 : ℤ) else 0))) := by
    simp only [onCount, cellO m hm, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [FO, Bx, RP, decide_eq_true_eq]
    push_cast
    split_ifs <;> omega
  rw [hs]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  rw [sqZ _ _ _ (by omega) (by norm_num), sqZ _ _ _ (by omega) (by norm_num),
    sqZ _ _ _ (by omega) (by norm_num), sqZ _ _ _ (by omega) (by norm_num)]
  push_cast [show 1 ≤ m by omega]
  ring

theorem cE (m : ℕ) (hm : 4 ≤ m) : (onCount 107 (2 * m) : ℚ) = 2 * (m : ℚ) ^ 2 + 2 * m := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (cntE m hm)
  push_cast at h
  exact h

theorem cO (m : ℕ) (hm : 4 ≤ m) :
    (onCount 107 (2 * m + 1) : ℚ) = (4 * (m : ℚ) + 3) ^ 2 - (2 * (m : ℚ) ^ 2 + 2 * m) := by
  have h := congrArg (fun z : ℤ => (z : ℚ)) (cntO m hm)
  push_cast at h
  exact h

theorem cV0 : (onCount 107 0 : ℚ) = 1 := by
  have := count_false 107 0 L0 (by decide) (by decide) lay0
  have h2 : ((onCount 107 0 : ℤ) : ℚ) = 1 := by
    rw [this]
    norm_num [L0]
  exact_mod_cast h2

theorem cV1 : (onCount 107 1 : ℚ) = 5 := by
  have := count_true 107 1 L1 (by decide) (by decide) lay1
  have h2 : ((onCount 107 1 : ℤ) : ℚ) = 5 := by
    rw [this]
    norm_num [L1]
  exact_mod_cast h2

theorem cV2 : (onCount 107 2 : ℚ) = 5 := by
  have := count_false 107 2 L2 (by decide) (by decide) lay2
  have h2 : ((onCount 107 2 : ℤ) : ℚ) = 5 := by
    rw [this]
    norm_num [L2]
  exact_mod_cast h2

theorem cV3 : (onCount 107 3 : ℚ) = 41 := by
  have := count_true 107 3 L3 (by decide) (by decide) lay3
  have h2 : ((onCount 107 3 : ℤ) : ℚ) = 41 := by
    rw [this]
    norm_num [L3]
  exact_mod_cast h2

theorem cV4 : (onCount 107 4 : ℚ) = 12 := by
  have := count_false 107 4 L4 (by decide) (by decide) lay4
  have h2 : ((onCount 107 4 : ℤ) : ℚ) = 12 := by
    rw [this]
    norm_num [L4]
  exact_mod_cast h2

theorem cV5 : (onCount 107 5 : ℚ) = 109 := by
  have := count_true 107 5 L5 (by decide) (by decide) lay5
  have h2 : ((onCount 107 5 : ℤ) : ℚ) = 109 := by
    rw [this]
    norm_num [L5]
  exact_mod_cast h2

theorem cV6 : (onCount 107 6 : ℚ) = 16 := by
  have := count_false 107 6 L6 (by decide) (by decide) lay6
  have h2 : ((onCount 107 6 : ℤ) : ℚ) = 16 := by
    rw [this]
    norm_num [L6]
  exact_mod_cast h2

theorem cV7 : (onCount 107 7 : ℚ) = 197 := by
  have := count_true 107 7 L7 (by decide) (by decide) lay7
  have h2 : ((onCount 107 7 : ℤ) : ℚ) = 197 := by
    rw [this]
    norm_num [L7]
  exact_mod_cast h2

theorem cV8 : (onCount 107 8 : ℚ) = 40 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, cE 4 (by norm_num)]
  try norm_num

theorem cV9 : (onCount 107 9 : ℚ) = 321 := by
  rw [show (9 : ℕ) = 2 * 4 + 1 by norm_num, cO 4 (by norm_num)]
  try norm_num

theorem cV10 : (onCount 107 10 : ℚ) = 60 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, cE 5 (by norm_num)]
  try norm_num

theorem cV11 : (onCount 107 11 : ℚ) = 469 := by
  rw [show (11 : ℕ) = 2 * 5 + 1 by norm_num, cO 5 (by norm_num)]
  try norm_num

theorem cV12 : (onCount 107 12 : ℚ) = 84 := by
  rw [show (12 : ℕ) = 2 * 6 by norm_num, cE 6 (by norm_num)]
  try norm_num

theorem cV13 : (onCount 107 13 : ℚ) = 645 := by
  rw [show (13 : ℕ) = 2 * 6 + 1 by norm_num, cO 6 (by norm_num)]
  try norm_num

theorem cV14 : (onCount 107 14 : ℚ) = 112 := by
  rw [show (14 : ℕ) = 2 * 7 by norm_num, cE 7 (by norm_num)]
  try norm_num

theorem cV15 : (onCount 107 15 : ℚ) = 849 := by
  rw [show (15 : ℕ) = 2 * 7 + 1 by norm_num, cO 7 (by norm_num)]
  try norm_num

theorem cV16 : (onCount 107 16 : ℚ) = 144 := by
  rw [show (16 : ℕ) = 2 * 8 by norm_num, cE 8 (by norm_num)]
  try norm_num

theorem cV17 : (onCount 107 17 : ℚ) = 1081 := by
  rw [show (17 : ℕ) = 2 * 8 + 1 by norm_num, cO 8 (by norm_num)]
  try norm_num

theorem cV18 : (onCount 107 18 : ℚ) = 180 := by
  rw [show (18 : ℕ) = 2 * 9 by norm_num, cE 9 (by norm_num)]
  try norm_num

theorem cV19 : (onCount 107 19 : ℚ) = 1341 := by
  rw [show (19 : ℕ) = 2 * 9 + 1 by norm_num, cO 9 (by norm_num)]
  try norm_num

theorem cV20 : (onCount 107 20 : ℚ) = 220 := by
  rw [show (20 : ℕ) = 2 * 10 by norm_num, cE 10 (by norm_num)]
  try norm_num

theorem cV21 : (onCount 107 21 : ℚ) = 1629 := by
  rw [show (21 : ℕ) = 2 * 10 + 1 by norm_num, cO 10 (by norm_num)]
  try norm_num

theorem cV22 : (onCount 107 22 : ℚ) = 264 := by
  rw [show (22 : ℕ) = 2 * 11 by norm_num, cE 11 (by norm_num)]
  try norm_num

theorem cV23 : (onCount 107 23 : ℚ) = 1945 := by
  rw [show (23 : ℕ) = 2 * 11 + 1 by norm_num, cO 11 (by norm_num)]
  try norm_num

theorem cV24 : (onCount 107 24 : ℚ) = 312 := by
  rw [show (24 : ℕ) = 2 * 12 by norm_num, cE 12 (by norm_num)]
  try norm_num

theorem cV25 : (onCount 107 25 : ℚ) = 2289 := by
  rw [show (25 : ℕ) = 2 * 12 + 1 by norm_num, cO 12 (by norm_num)]
  try norm_num

theorem cV26 : (onCount 107 26 : ℚ) = 364 := by
  rw [show (26 : ℕ) = 2 * 13 by norm_num, cE 13 (by norm_num)]
  try norm_num

theorem cV27 : (onCount 107 27 : ℚ) = 2661 := by
  rw [show (27 : ℕ) = 2 * 13 + 1 by norm_num, cO 13 (by norm_num)]
  try norm_num

theorem cV28 : (onCount 107 28 : ℚ) = 420 := by
  rw [show (28 : ℕ) = 2 * 14 by norm_num, cE 14 (by norm_num)]
  try norm_num

theorem cV29 : (onCount 107 29 : ℚ) = 3061 := by
  rw [show (29 : ℕ) = 2 * 14 + 1 by norm_num, cO 14 (by norm_num)]
  try norm_num

theorem cV30 : (onCount 107 30 : ℚ) = 480 := by
  rw [show (30 : ℕ) = 2 * 15 by norm_num, cE 15 (by norm_num)]
  try norm_num

def G (n : ℕ) : ℚ := (((9 : ℚ) / 2) * (n : ℚ) ^ 0 + (4 : ℚ) * (n : ℚ) ^ 1) + (-1 : ℚ) ^ n * (((9 : ℚ) / 2) * (n : ℚ) ^ 0 + (6 : ℚ) * (n : ℚ) ^ 1 + (3 : ℚ) * (n : ℚ) ^ 2)

theorem aG (n : ℕ) (hn : 8 ≤ n) : (a n : ℚ) = G n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have h := cE m (by omega)
    have h' := cO m (by omega)
    have h1 : (-1 : ℚ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    simp only [a, G, h1]
    push_cast
    rw [h, h']
    ring
  · have h := cO m (by omega)
    have h' := cE (m + 1) (by omega)
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] at h'
    push_cast at h'
    have h1 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    simp only [a, G, h1]
    push_cast
    rw [h, h']
    ring

theorem aV0 : (a 0 : ℚ) = 4 := by
  simp only [a]
  push_cast
  rw [cV1, cV0]
  norm_num

theorem aV1 : (a 1 : ℚ) = 0 := by
  simp only [a]
  push_cast
  rw [cV2, cV1]
  norm_num

theorem aV2 : (a 2 : ℚ) = 36 := by
  simp only [a]
  push_cast
  rw [cV3, cV2]
  norm_num

theorem aV3 : (a 3 : ℚ) = -29 := by
  simp only [a]
  push_cast
  rw [cV4, cV3]
  norm_num

theorem aV4 : (a 4 : ℚ) = 97 := by
  simp only [a]
  push_cast
  rw [cV5, cV4]
  norm_num

theorem aV5 : (a 5 : ℚ) = -93 := by
  simp only [a]
  push_cast
  rw [cV6, cV5]
  norm_num

theorem aV6 : (a 6 : ℚ) = 181 := by
  simp only [a]
  push_cast
  rw [cV7, cV6]
  norm_num

theorem aV7 : (a 7 : ℚ) = -157 := by
  simp only [a]
  push_cast
  rw [cV8, cV7]
  norm_num

theorem aV8 : (a 8 : ℚ) = 281 := by
  simp only [a]
  push_cast
  rw [cV9, cV8]
  norm_num

theorem aV9 : (a 9 : ℚ) = -261 := by
  simp only [a]
  push_cast
  rw [cV10, cV9]
  norm_num

theorem aV10 : (a 10 : ℚ) = 409 := by
  simp only [a]
  push_cast
  rw [cV11, cV10]
  norm_num

theorem aV11 : (a 11 : ℚ) = -385 := by
  rw [aG 11 (by norm_num)]
  norm_num [G]

theorem aV12 : (a 12 : ℚ) = 561 := by
  rw [aG 12 (by norm_num)]
  norm_num [G]

theorem aV13 : (a 13 : ℚ) = -533 := by
  rw [aG 13 (by norm_num)]
  norm_num [G]

theorem aV14 : (a 14 : ℚ) = 737 := by
  rw [aG 14 (by norm_num)]
  norm_num [G]

theorem aV15 : (a 15 : ℚ) = -705 := by
  rw [aG 15 (by norm_num)]
  norm_num [G]

theorem aV16 : (a 16 : ℚ) = 937 := by
  rw [aG 16 (by norm_num)]
  norm_num [G]

theorem aV17 : (a 17 : ℚ) = -901 := by
  rw [aG 17 (by norm_num)]
  norm_num [G]

theorem aV18 : (a 18 : ℚ) = 1161 := by
  rw [aG 18 (by norm_num)]
  norm_num [G]

theorem aV19 : (a 19 : ℚ) = -1121 := by
  rw [aG 19 (by norm_num)]
  norm_num [G]

theorem aV20 : (a 20 : ℚ) = 1409 := by
  rw [aG 20 (by norm_num)]
  norm_num [G]

theorem aV21 : (a 21 : ℚ) = -1365 := by
  rw [aG 21 (by norm_num)]
  norm_num [G]

theorem aV22 : (a 22 : ℚ) = 1681 := by
  rw [aG 22 (by norm_num)]
  norm_num [G]

theorem aV23 : (a 23 : ℚ) = -1633 := by
  rw [aG 23 (by norm_num)]
  norm_num [G]

theorem aV24 : (a 24 : ℚ) = 1977 := by
  rw [aG 24 (by norm_num)]
  norm_num [G]

theorem aV25 : (a 25 : ℚ) = -1925 := by
  rw [aG 25 (by norm_num)]
  norm_num [G]

theorem aV26 : (a 26 : ℚ) = 2297 := by
  rw [aG 26 (by norm_num)]
  norm_num [G]

theorem aV27 : (a 27 : ℚ) = -2241 := by
  rw [aG 27 (by norm_num)]
  norm_num [G]

theorem aV28 : (a 28 : ℚ) = 2641 := by
  rw [aG 28 (by norm_num)]
  norm_num [G]

end OMA.CA_a270167

open OMA.CA_a270167 OMA.S_oeis_a270167 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a270167.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn0
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23, aV24, aV25, aV26, aV27, aV28]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      push_cast
      ring
  · intro n hn0 hp
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23, aV24, aV25, aV26, aV27, aV28]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Even.neg_one_pow hp]
      push_cast
      ring
  · intro n hn0 hp
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23, aV24, aV25, aV26, aV27, aV28]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Odd.neg_one_pow hp]
      push_cast
      ring
  · intro n hn0
    rcases Nat.lt_or_ge n 13 with h | h
    · interval_cases n <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23, aV24, aV25, aV26, aV27, aV28]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
      rw [show k + 13 - 1 = k + 12 by omega]
      rw [show k + 13 - 2 = k + 11 by omega]
      rw [show k + 13 - 3 = k + 10 by omega]
      rw [show k + 13 - 4 = k + 9 by omega]
      rw [show k + 13 - 5 = k + 8 by omega]
      rw [aG (k + 13) (by omega), aG (k + 12) (by omega), aG (k + 11) (by omega), aG (k + 10) (by omega), aG (k + 9) (by omega), aG (k + 8) (by omega)]
      simp only [G]
      push_cast
      ring
  · have hL : mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 3 : PowerSeries ℚ) = mk (fun n => (a n : ℚ)) + X ^ 1 * mk (fun n => (a n : ℚ)) - C 2 * (X ^ 2 * mk (fun n => (a n : ℚ))) - C 2 * (X ^ 3 * mk (fun n => (a n : ℚ))) + X ^ 4 * mk (fun n => (a n : ℚ)) + X ^ 5 * mk (fun n => (a n : ℚ)) := by
      try simp only [map_ofNat]
      ring
    have hR : (4 + 4 * X + 28 * X ^ 2 - X ^ 3 - 6 * X ^ 5 - 12 * X ^ 6 + 23 * X ^ 7 + 16 * X ^ 8 - 24 * X ^ 9 - 12 * X ^ 10 + 8 * X ^ 11 + 4 * X ^ 12 : PowerSeries ℚ) = C 4 + C 4 * X ^ 1 + C 28 * X ^ 2 - X ^ 3 - C 6 * X ^ 5 - C 12 * X ^ 6 + C 23 * X ^ 7 + C 16 * X ^ 8 - C 24 * X ^ 9 - C 12 * X ^ 10 + C 8 * X ^ 11 + C 4 * X ^ 12 := by
      try simp only [map_ofNat]
      ring
    rw [hL, hR]
    ext k
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
    rcases Nat.lt_or_ge k 27 with h | h
    · interval_cases k <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23, aV24, aV25, aV26, aV27, aV28]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 27 := ⟨k - 27, by omega⟩
      rw [if_pos (show 1 ≤ j + 27 by omega)]
      rw [if_pos (show 2 ≤ j + 27 by omega)]
      rw [if_pos (show 3 ≤ j + 27 by omega)]
      rw [if_pos (show 4 ≤ j + 27 by omega)]
      rw [if_pos (show 5 ≤ j + 27 by omega)]
      rw [if_neg (show j + 27 ≠ 0 by omega)]
      rw [if_neg (show j + 27 ≠ 1 by omega)]
      rw [if_neg (show j + 27 ≠ 2 by omega)]
      rw [if_neg (show j + 27 ≠ 3 by omega)]
      rw [if_neg (show j + 27 ≠ 5 by omega)]
      rw [if_neg (show j + 27 ≠ 6 by omega)]
      rw [if_neg (show j + 27 ≠ 7 by omega)]
      rw [if_neg (show j + 27 ≠ 8 by omega)]
      rw [if_neg (show j + 27 ≠ 9 by omega)]
      rw [if_neg (show j + 27 ≠ 10 by omega)]
      rw [if_neg (show j + 27 ≠ 11 by omega)]
      rw [if_neg (show j + 27 ≠ 12 by omega)]
      rw [show j + 27 - 1 = j + 26 by omega]
      rw [show j + 27 - 2 = j + 25 by omega]
      rw [show j + 27 - 3 = j + 24 by omega]
      rw [show j + 27 - 4 = j + 23 by omega]
      rw [show j + 27 - 5 = j + 22 by omega]
      rw [aG (j + 27) (by omega), aG (j + 26) (by omega), aG (j + 25) (by omega), aG (j + 24) (by omega), aG (j + 23) (by omega), aG (j + 22) (by omega)]
      simp only [G]
      push_cast
      ring
