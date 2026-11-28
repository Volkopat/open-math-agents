import OMAStatements.S_arxiv_2512_20878
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_arxiv_2512_20878

open OMA.S_arxiv_2512_20878

/-! ### Part 1: Basic `ZMod n` arithmetic for `n ≥ 7` -/

private lemma zmod_ne_zero_of_pos_lt {n a : ℕ} (ha0 : 0 < a) (han : a < n) :
    (a : ZMod n) ≠ 0 := by
  have : NeZero n := ⟨by omega⟩
  intro h
  have hval := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_zero, Nat.mod_eq_of_lt han] at hval
  omega

private lemma zmod_const_ne {n : ℕ} (hn : 7 ≤ n) :
    ((1 : ZMod n) ≠ 0) ∧ ((3 : ZMod n) ≠ 0) ∧
    ((1 : ZMod n) ≠ -1) ∧ ((3 : ZMod n) ≠ -3) ∧
    ((1 : ZMod n) ≠ 3) ∧ ((1 : ZMod n) ≠ -3) ∧
    ((-1 : ZMod n) ≠ 3) ∧ ((-1 : ZMod n) ≠ -3) := by
  have h1 : (1 : ZMod n) ≠ 0 := by
    simpa using zmod_ne_zero_of_pos_lt (n := n) (a := 1) (by omega) (by omega)
  have h2 : (2 : ZMod n) ≠ 0 := by
    simpa using zmod_ne_zero_of_pos_lt (n := n) (a := 2) (by omega) (by omega)
  have h3 : (3 : ZMod n) ≠ 0 := by
    simpa using zmod_ne_zero_of_pos_lt (n := n) (a := 3) (by omega) (by omega)
  have h4 : (4 : ZMod n) ≠ 0 := by
    simpa using zmod_ne_zero_of_pos_lt (n := n) (a := 4) (by omega) (by omega)
  have h6 : (6 : ZMod n) ≠ 0 := by
    simpa using zmod_ne_zero_of_pos_lt (n := n) (a := 6) (by omega) (by omega)
  refine ⟨h1, h3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; apply h2; linear_combination h
  · intro h; apply h6; linear_combination h
  · intro h; apply h2; linear_combination -h
  · intro h; apply h4; linear_combination h
  · intro h; apply h4; linear_combination -h
  · intro h; apply h2; linear_combination h

private lemma adj_iff_mem {n : ℕ} (hn : 7 ≤ n) (u v : ZMod n) :
    (circulant13 n).Adj u v ↔ v = u + 1 ∨ v = u - 1 ∨ v = u + 3 ∨ v = u - 3 := by
  have ⟨h10, h30, _, _, _, _, _, _⟩ := zmod_const_ne hn
  constructor
  · rintro ⟨_, h | h | h | h⟩
    · left; linear_combination h
    · right; left; linear_combination -h
    · right; right; left; linear_combination h
    · right; right; right; linear_combination -h
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨fun h => h10 (by linear_combination -h), Or.inl (by ring)⟩
    · exact ⟨fun h => h10 (by linear_combination h), Or.inr (Or.inl (by ring))⟩
    · exact ⟨fun h => h30 (by linear_combination -h), Or.inr (Or.inr (Or.inl (by ring)))⟩
    · exact ⟨fun h => h30 (by linear_combination h), Or.inr (Or.inr (Or.inr (by ring)))⟩

private lemma four_edges_nodup {n : ℕ} (hn : 7 ≤ n) (u : ZMod n) :
    let e1 : (circulant13 n).edgeSet := ⟨s(u, u + 1), (adj_iff_mem hn u (u + 1)).mpr (Or.inl rfl)⟩
    let e2 : (circulant13 n).edgeSet := ⟨s(u - 1, u), (adj_iff_mem hn (u - 1) u).mpr (Or.inl (by ring))⟩
    let e3 : (circulant13 n).edgeSet := ⟨s(u, u + 3), (adj_iff_mem hn u (u + 3)).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
    let e4 : (circulant13 n).edgeSet := ⟨s(u - 3, u), (adj_iff_mem hn (u - 3) u).mpr (Or.inr (Or.inr (Or.inl (by ring))))⟩
    [e1, e2, e3, e4].Nodup := by
  have ⟨h10, h30, h1m1, h3m3, h13, h1m3, hm13, hm1m3⟩ := zmod_const_ne hn
  dsimp only
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro h; rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨h1, _⟩ | ⟨_, h2⟩
    · apply h10; linear_combination h1
    · apply h1m1; linear_combination h2
  · intro h; rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨_, h2⟩ | ⟨h1, _⟩
    · apply h13; linear_combination h2
    · apply h30; linear_combination -h1
  · intro h; rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨h1, _⟩ | ⟨_, h2⟩
    · apply h30; linear_combination h1
    · apply h1m3; linear_combination h2
  · intro h; rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨h1, _⟩ | ⟨h1, _⟩
    · apply h10; linear_combination -h1
    · apply hm13; linear_combination h1
  · intro h; rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨h1, _⟩ | ⟨h1, _⟩
    · apply hm1m3; linear_combination h1
    · apply h10; linear_combination -h1
  · intro h; rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with ⟨h1, _⟩ | ⟨_, h2⟩
    · apply h30; linear_combination h1
    · apply h3m3; linear_combination h2

/-! ### Part 2: Universal lower bound `χ''(C_n(1,3)) ≥ 5` for `n ≥ 7` -/

private lemma five_colors_injective {n k : ℕ} (hn : 7 ≤ n)
    {cv : ZMod n → Fin k} {ce : (circulant13 n).edgeSet → Fin k}
    (htc : IsTotalColoring (circulant13 n) k cv ce) (u : ZMod n) :
    let e1 : (circulant13 n).edgeSet := ⟨s(u, u + 1), (adj_iff_mem hn u (u + 1)).mpr (Or.inl rfl)⟩
    let e2 : (circulant13 n).edgeSet := ⟨s(u - 1, u), (adj_iff_mem hn (u - 1) u).mpr (Or.inl (by ring))⟩
    let e3 : (circulant13 n).edgeSet := ⟨s(u, u + 3), (adj_iff_mem hn u (u + 3)).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
    let e4 : (circulant13 n).edgeSet := ⟨s(u - 3, u), (adj_iff_mem hn (u - 3) u).mpr (Or.inr (Or.inr (Or.inl (by ring))))⟩
    Function.Injective (![cv u, ce e1, ce e2, ce e3, ce e4] : Fin 5 → Fin k) := by
  dsimp only
  rcases htc with ⟨_, hve, hee⟩
  let e1 : (circulant13 n).edgeSet := ⟨s(u, u + 1), (adj_iff_mem hn u (u + 1)).mpr (Or.inl rfl)⟩
  let e2 : (circulant13 n).edgeSet := ⟨s(u - 1, u), (adj_iff_mem hn (u - 1) u).mpr (Or.inl (by ring))⟩
  let e3 : (circulant13 n).edgeSet := ⟨s(u, u + 3), (adj_iff_mem hn u (u + 3)).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
  let e4 : (circulant13 n).edgeSet := ⟨s(u - 3, u), (adj_iff_mem hn (u - 3) u).mpr (Or.inr (Or.inr (Or.inl (by ring))))⟩
  have hnod := four_edges_nodup hn u
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true] at hnod
  rcases hnod with ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34⟩
  have hmem1 : u ∈ e1.val := Sym2.mem_mk_left _ _
  have hmem2 : u ∈ e2.val := Sym2.mem_mk_right _ _
  have hmem3 : u ∈ e3.val := Sym2.mem_mk_left _ _
  have hmem4 : u ∈ e4.val := Sym2.mem_mk_right _ _
  intro i j hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hij
  · exact absurd hij (hve u e1 hmem1)
  · exact absurd hij (hve u e2 hmem2)
  · exact absurd hij (hve u e3 hmem3)
  · exact absurd hij (hve u e4 hmem4)
  · exact absurd hij.symm (hve u e1 hmem1)
  · exact absurd hij (hee e1 e2 h12 ⟨u, hmem1, hmem2⟩)
  · exact absurd hij (hee e1 e3 h13 ⟨u, hmem1, hmem3⟩)
  · exact absurd hij (hee e1 e4 h14 ⟨u, hmem1, hmem4⟩)
  · exact absurd hij.symm (hve u e2 hmem2)
  · exact absurd hij.symm (hee e1 e2 h12 ⟨u, hmem1, hmem2⟩)
  · exact absurd hij (hee e2 e3 h23 ⟨u, hmem2, hmem3⟩)
  · exact absurd hij (hee e2 e4 h24 ⟨u, hmem2, hmem4⟩)
  · exact absurd hij.symm (hve u e3 hmem3)
  · exact absurd hij.symm (hee e1 e3 h13 ⟨u, hmem1, hmem3⟩)
  · exact absurd hij.symm (hee e2 e3 h23 ⟨u, hmem2, hmem3⟩)
  · exact absurd hij (hee e3 e4 h34 ⟨u, hmem3, hmem4⟩)
  · exact absurd hij.symm (hve u e4 hmem4)
  · exact absurd hij.symm (hee e1 e4 h14 ⟨u, hmem1, hmem4⟩)
  · exact absurd hij.symm (hee e2 e4 h24 ⟨u, hmem2, hmem4⟩)
  · exact absurd hij.symm (hee e3 e4 h34 ⟨u, hmem3, hmem4⟩)

private lemma not_hasTotalColoring_of_lt_five {n k : ℕ} (hn : 7 ≤ n) (hk : k < 5) :
    ¬ HasTotalColoring (circulant13 n) k := by
  rintro ⟨cv, ce, htc⟩
  have hle := Fintype.card_le_of_injective _ (five_colors_injective hn htc (0 : ZMod n))
  simp only [Fintype.card_fin] at hle
  omega

/-! ### Part 3: Building total colorings from `(cv, e1, e3)` functions -/

private lemma hasTotalColoring_of_fns {n k : ℕ} (hn : 7 ≤ n) (hk : 0 < k)
    (cv e1 e3 : ZMod n → Fin k)
    (hv1 : ∀ u, cv u ≠ cv (u + 1))
    (hv3 : ∀ u, cv u ≠ cv (u + 3))
    (hlocal : ∀ u, [cv u, e1 u, e1 (u - 1), e3 u, e3 (u - 3)].Nodup) :
    HasTotalColoring (circulant13 n) k := by
  classical
  have ⟨_, _, h1m1, h3m3, h13, h1m3, _, _⟩ := zmod_const_ne hn
  let g : ZMod n → ZMod n → Fin k := fun u v =>
    if v - u = 1 then e1 u
    else if u - v = 1 then e1 v
    else if v - u = 3 then e3 u
    else if u - v = 3 then e3 v
    else ⟨0, hk⟩
  have hgsym : ∀ u v, g u v = g v u := by
    intro u v
    dsimp only [g]
    by_cases h1 : v - u = 1
    · have h2 : u - v ≠ 1 := fun h => h1m1 (by linear_combination -h1 - h)
      simp [h1, h2]
    · by_cases h2 : u - v = 1
      · simp [h1, h2]
      · by_cases h3 : v - u = 3
        · have h4 : u - v ≠ 3 := fun h => h3m3 (by linear_combination -h3 - h)
          simp [h2, h3, h4]
        · by_cases h4 : u - v = 3
          · simp [h1, h3, h4]
          · simp [h1, h2, h3, h4]
  let ceSym : Sym2 (ZMod n) → Fin k := Sym2.lift ⟨g, hgsym⟩
  let ce : (circulant13 n).edgeSet → Fin k := fun e => ceSym e.val
  have hce1 : ∀ u, ceSym s(u, u + 1) = e1 u := fun u => by
    change g u (u + 1) = e1 u; dsimp only [g]; rw [if_pos (by ring)]
  have hce2 : ∀ u, ceSym s(u - 1, u) = e1 (u - 1) := fun u => by
    have : s(u - 1, u) = s(u - 1, (u - 1) + 1) := by congr 1; ring
    rw [this, hce1]
  have hce3 : ∀ u, ceSym s(u, u + 3) = e3 u := fun u => by
    change g u (u + 3) = e3 u; dsimp only [g]
    rw [if_neg (fun h => h13 (by linear_combination -h)),
        if_neg (fun h => h1m3 (by linear_combination -h)),
        if_pos (by ring)]
  have hce4 : ∀ u, ceSym s(u - 3, u) = e3 (u - 3) := fun u => by
    have : s(u - 3, u) = s(u - 3, (u - 3) + 3) := by congr 1; ring
    rw [this, hce3]
  have hedge_cases : ∀ (u : ZMod n) (e : (circulant13 n).edgeSet), u ∈ e.val →
      (e.val = s(u, u + 1) ∧ ce e = e1 u) ∨
      (e.val = s(u - 1, u) ∧ ce e = e1 (u - 1)) ∨
      (e.val = s(u, u + 3) ∧ ce e = e3 u) ∨
      (e.val = s(u - 3, u) ∧ ce e = e3 (u - 3)) := by
    intro u ⟨e, he⟩ hu
    induction e using Sym2.ind with
    | _ a b =>
      simp only [SimpleGraph.mem_edgeSet] at he
      rcases Sym2.mem_iff.mp hu with rfl | rfl
      · rcases (adj_iff_mem hn u b).mp he with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨rfl, hce1 u⟩
        · exact Or.inr (Or.inl ⟨Sym2.eq_swap, by change ceSym s(u, u - 1) = _; rw [Sym2.eq_swap, hce2]⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, hce3 u⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨Sym2.eq_swap, by change ceSym s(u, u - 3) = _; rw [Sym2.eq_swap, hce4]⟩))
      · rcases (adj_iff_mem hn u a).mp he.symm with rfl | rfl | rfl | rfl
        · exact Or.inl ⟨Sym2.eq_swap, by change ceSym s(u + 1, u) = _; rw [Sym2.eq_swap, hce1]⟩
        · exact Or.inr (Or.inl ⟨rfl, hce2 u⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨Sym2.eq_swap, by change ceSym s(u + 3, u) = _; rw [Sym2.eq_swap, hce3]⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, hce4 u⟩))
  refine ⟨cv, ce, ?_, ?_, ?_⟩
  · intro u v huv
    rcases (adj_iff_mem hn u v).mp huv with rfl | rfl | rfl | rfl
    · exact hv1 u
    · intro h; exact hv1 (u - 1) (by simpa [sub_add_cancel] using h.symm)
    · exact hv3 u
    · intro h; exact hv3 (u - 3) (by simpa [sub_add_cancel] using h.symm)
  · intro u e hu
    have hnd := hlocal u
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      and_true] at hnd
    rcases hedge_cases u e hu with ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ | ⟨_, hc⟩ <;> rw [hc]
    · exact hnd.1.1
    · exact hnd.1.2.1
    · exact hnd.1.2.2.1
    · exact hnd.1.2.2.2
  · rintro e₁ e₂ hne ⟨u, hu₁, hu₂⟩
    have hnd := hlocal u
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      not_false_eq_true, and_true] at hnd
    have hne_val : e₁.val ≠ e₂.val := fun h => hne (Subtype.ext h)
    rcases hedge_cases u e₁ hu₁ with ⟨hv1', hc1⟩ | ⟨hv1', hc1⟩ | ⟨hv1', hc1⟩ | ⟨hv1', hc1⟩ <;>
    rcases hedge_cases u e₂ hu₂ with ⟨hv2', hc2⟩ | ⟨hv2', hc2⟩ | ⟨hv2', hc2⟩ | ⟨hv2', hc2⟩ <;>
    rw [hc1, hc2]
    all_goals try (exact absurd (hv1'.trans hv2'.symm) hne_val)
    · exact hnd.2.1.1
    · exact hnd.2.1.2.1
    · exact hnd.2.1.2.2
    · exact fun h => hnd.2.1.1 h.symm
    · exact hnd.2.2.1.1
    · exact hnd.2.2.1.2
    · exact fun h => hnd.2.1.2.1 h.symm
    · exact fun h => hnd.2.2.1.1 h.symm
    · exact hnd.2.2.2
    · exact fun h => hnd.2.1.2.2 h.symm
    · exact fun h => hnd.2.2.1.2 h.symm
    · exact fun h => hnd.2.2.2 h.symm

/-! ### Part 4: Explicit 5-total-colorings & 6-total-colorings -/

private def natArrayValid (n k : ℕ) (v e1 e3 : List ℕ) : Bool :=
  (v.length == n) && (e1.length == n) && (e3.length == n) &&
  v.all (· < k) && e1.all (· < k) && e3.all (· < k) &&
  (List.range n).all fun i =>
    let vi := v.getD i 0
    let v1 := v.getD ((i + 1) % n) 0
    let v3 := v.getD ((i + 3) % n) 0
    let a1 := e1.getD i 0
    let a2 := e1.getD ((i + n - 1) % n) 0
    let a3 := e3.getD i 0
    let a4 := e3.getD ((i + n - 3) % n) 0
    (vi != v1) && (vi != v3) &&
    (vi != a1) && (vi != a2) && (vi != a3) && (vi != a4) &&
    (a1 != a2) && (a1 != a3) && (a1 != a4) &&
    (a2 != a3) && (a2 != a4) && (a3 != a4)

private lemma list_getD_lt {k : ℕ} (hk : 0 < k) {l : List ℕ} (hall : l.all (· < k) = true) (i : ℕ) :
    l.getD i 0 < k := by
  rw [List.all_eq_true] at hall
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < l.length
  · rw [List.getElem?_eq_getElem hi, Option.getD_some]
    simpa using hall l[i] (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt hi), Option.getD_none]
    exact hk

private lemma zmod_add_val {n a : ℕ} (hn : 0 < n) (u : ZMod n) :
    (u + (a : ZMod n)).val = (u.val + a) % n := by
  have : NeZero n := ⟨by omega⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val u, ← Nat.cast_add, ZMod.val_natCast]

private lemma zmod_sub_val {n a : ℕ} (hn : a ≤ n) (hpos : 0 < n) (u : ZMod n) :
    (u - (a : ZMod n)).val = (u.val + n - a) % n := by
  have : NeZero n := ⟨by omega⟩
  have heq : u - (a : ZMod n) = u + ((n - a : ℕ) : ZMod n) := by
    rw [Nat.cast_sub hn, ZMod.natCast_self, zero_sub, sub_eq_add_neg]
  rw [heq, zmod_add_val hpos]
  congr 1
  omega

private lemma hasTotalColoring_of_natFns {n k : ℕ} (hn : 7 ≤ n) (hk : 0 < k)
    (fv f1 f3 : ℕ → Fin k)
    (h : ∀ i < n,
      fv i ≠ fv ((i + 1) % n) ∧
      fv i ≠ fv ((i + 3) % n) ∧
      [fv i, f1 i, f1 ((i + n - 1) % n), f3 i, f3 ((i + n - 3) % n)].Nodup) :
    HasTotalColoring (circulant13 n) k := by
  have : NeZero n := ⟨by omega⟩
  refine hasTotalColoring_of_fns hn hk
    (fun u => fv u.val) (fun u => f1 u.val) (fun u => f3 u.val) ?_ ?_ ?_
  · intro u
    have h1 : (u + 1).val = (u.val + 1) % n := by
      simpa using zmod_add_val (n := n) (a := 1) (by omega) u
    rw [h1]; exact (h u.val u.val_lt).1
  · intro u
    have h3 : (u + 3).val = (u.val + 3) % n := by
      simpa using zmod_add_val (n := n) (a := 3) (by omega) u
    rw [h3]; exact (h u.val u.val_lt).2.1
  · intro u
    have hm1 : (u - 1).val = (u.val + n - 1) % n := by
      simpa using zmod_sub_val (n := n) (a := 1) (by omega) (by omega) u
    have hm3 : (u - 3).val = (u.val + n - 3) % n := by
      simpa using zmod_sub_val (n := n) (a := 3) (by omega) (by omega) u
    rw [hm1, hm3]; exact (h u.val u.val_lt).2.2

private lemma hasTotalColoring_of_natArray {n k : ℕ} (hn : 7 ≤ n) (hk : 0 < k)
    (v e1 e3 : List ℕ)
    (hvalid : natArrayValid n k v e1 e3 = true) :
    HasTotalColoring (circulant13 n) k := by
  unfold natArrayValid at hvalid
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hvalid
  have hv_lt : ∀ i, v.getD i 0 < k := list_getD_lt hk (List.all_eq_true.mpr hvalid.1.1.1.2)
  have h1_lt : ∀ i, e1.getD i 0 < k := list_getD_lt hk (List.all_eq_true.mpr hvalid.1.1.2)
  have h3_lt : ∀ i, e3.getD i 0 < k := list_getD_lt hk (List.all_eq_true.mpr hvalid.1.2)
  have mkNe : ∀ {a b : ℕ}, a < k → b < k → a ≠ b →
      (⟨a % k, Nat.mod_lt _ hk⟩ : Fin k) ≠ ⟨b % k, Nat.mod_lt _ hk⟩ := by
    intro a b ha hb hab h
    have hv := congrArg Fin.val h; dsimp only at hv
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
    exact hab hv
  refine hasTotalColoring_of_natFns hn hk
    (fun i => ⟨v.getD i 0 % k, Nat.mod_lt _ hk⟩)
    (fun i => ⟨e1.getD i 0 % k, Nat.mod_lt _ hk⟩)
    (fun i => ⟨e3.getD i 0 % k, Nat.mod_lt _ hk⟩) ?_
  intro i hi
  have h := hvalid.2 i hi
  simp only [bne_iff_ne] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩
  refine ⟨mkNe (hv_lt _) (hv_lt _) a1, mkNe (hv_lt _) (hv_lt _) a2, ?_⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
    not_false_eq_true, and_true]
  exact ⟨⟨mkNe (hv_lt _) (h1_lt _) a3, mkNe (hv_lt _) (h1_lt _) a4,
          mkNe (hv_lt _) (h3_lt _) a5, mkNe (hv_lt _) (h3_lt _) a6⟩,
         ⟨mkNe (h1_lt _) (h1_lt _) a7, mkNe (h1_lt _) (h3_lt _) a8,
          mkNe (h1_lt _) (h3_lt _) a9⟩,
         ⟨mkNe (h1_lt _) (h3_lt _) a10, mkNe (h1_lt _) (h3_lt _) a11⟩,
          mkNe (h3_lt _) (h3_lt _) a12⟩

private def b5v : List ℕ := [0, 1, 2, 3, 4]
private def b5e1 : List ℕ := [3, 4, 0, 1, 2]
private def b5e3 : List ℕ := [4, 0, 1, 2, 3]

private lemma five_tc_mult5 (q : ℕ) (hq : 2 ≤ q) :
    HasTotalColoring (circulant13 (5 * q)) 5 := by
  have hn : 7 ≤ 5 * q := by omega
  refine hasTotalColoring_of_natFns hn (by omega)
    (fun i => ⟨i % 5, Nat.mod_lt _ (by omega)⟩)
    (fun i => ⟨(i + 3) % 5, Nat.mod_lt _ (by omega)⟩)
    (fun i => ⟨(i + 4) % 5, Nat.mod_lt _ (by omega)⟩) ?_
  intro i hi
  have hm1 : (i + 1) % (5 * q) % 5 = (i + 1) % 5 :=
    Nat.mod_mod_of_dvd _ (dvd_mul_right 5 q)
  have hm3 : (i + 3) % (5 * q) % 5 = (i + 3) % 5 :=
    Nat.mod_mod_of_dvd _ (dvd_mul_right 5 q)
  have hsub1 : (i + 5 * q - 1) % (5 * q) % 5 = (i + 4) % 5 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 5 q)]; omega
  have hsub3 : (i + 5 * q - 3) % (5 * q) % 5 = (i + 2) % 5 := by
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right 5 q)]; omega
  have hs1 : ((i + 5 * q - 1) % (5 * q) + 3) % 5 = (i + 2) % 5 := by
    rw [Nat.add_mod, hsub1]; omega
  have hs3 : ((i + 5 * q - 3) % (5 * q) + 4) % 5 = (i + 1) % 5 := by
    rw [Nat.add_mod, hsub3]; omega
  refine ⟨?_, ?_, ?_⟩
  · intro h; have := congrArg Fin.val h; dsimp only at this; rw [hm1] at this; omega
  · intro h; have := congrArg Fin.val h; dsimp only at this; rw [hm3] at this; omega
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
      not_false_eq_true, and_true, Fin.mk.injEq, hs1, hs3]
    omega

private lemma splice_5tc_ge2 (L : ℕ) (hL : 7 ≤ L)
    (fv f1 f3 : ℕ → Fin 5)
    (hlocal_ext : ∀ j < L + 5,
      fv j ≠ fv ((j + 1) % (L + 5)) ∧
      fv j ≠ fv ((j + 3) % (L + 5)) ∧
      [fv j, f1 j, f1 ((j + (L + 5) - 1) % (L + 5)),
       f3 j, f3 ((j + (L + 5) - 3) % (L + 5))].Nodup)
    (hperV : ∀ i, L ≤ i → fv i = ⟨(i - L) % 5, Nat.mod_lt _ (by omega)⟩)
    (hper1 : ∀ i, L ≤ i → f1 i = ⟨(i - L + 3) % 5, Nat.mod_lt _ (by omega)⟩)
    (hper3 : ∀ i, L ≤ i → f3 i = ⟨(i - L + 4) % 5, Nat.mod_lt _ (by omega)⟩)
    (m' : ℕ) : HasTotalColoring (circulant13 (L + 5 * (m' + 2))) 5 := by
  set n := L + 5 * (m' + 2)
  have hn : 7 ≤ n := by omega
  refine hasTotalColoring_of_natFns hn (by omega) fv f1 f3 ?_
  intro i hi
  by_cases hA : i < L
  · have he := hlocal_ext i (by omega)
    have ha1 : (i + 1) % n = (i + 1) % (L + 5) := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have ha3 : (i + 3) % n = (i + 3) % (L + 5) := by
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    have hm1 : f1 ((i + n - 1) % n) = f1 ((i + (L + 5) - 1) % (L + 5)) := by
      by_cases hi0 : i = 0
      · subst hi0
        rw [show (0 + n - 1) % n = n - 1 by rw [zero_add, Nat.mod_eq_of_lt (by omega)],
            show (0 + (L + 5) - 1) % (L + 5) = L + 4 by
              rw [zero_add, Nat.mod_eq_of_lt (by omega)]; omega]
        rw [hper1 (n - 1) (by omega), hper1 (L + 4) (by omega)]
        ext; dsimp only; omega
      · rw [show (i + n - 1) % n = i - 1 by
              rw [show i + n - 1 = (i - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)],
            show (i + (L + 5) - 1) % (L + 5) = i - 1 by
              rw [show i + (L + 5) - 1 = (i - 1) + (L + 5) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
    have hm3 : f3 ((i + n - 3) % n) = f3 ((i + (L + 5) - 3) % (L + 5)) := by
      by_cases hi3 : i < 3
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hper3 (i + n - 3) (by omega), hper3 (i + (L + 5) - 3) (by omega)]
        ext; dsimp only; omega
      · rw [show (i + n - 3) % n = i - 3 by
              rw [show i + n - 3 = (i - 3) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)],
            show (i + (L + 5) - 3) % (L + 5) = i - 3 by
              rw [show i + (L + 5) - 3 = (i - 3) + (L + 5) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
    rw [ha1, ha3, hm1, hm3]
    exact he
  · by_cases hB : i < n - 3
    · have hv1_eq : fv ((i + 1) % n) = ⟨(i + 1 - L) % 5, Nat.mod_lt _ (by omega)⟩ := by
        rw [Nat.mod_eq_of_lt (by omega), hperV (i + 1) (by omega)]
      have hv3_eq : fv ((i + 3) % n) = ⟨(i + 3 - L) % 5, Nat.mod_lt _ (by omega)⟩ := by
        rw [Nat.mod_eq_of_lt (by omega), hperV (i + 3) (by omega)]
      refine ⟨?_, ?_, ?_⟩
      · rw [hperV i (by omega), hv1_eq]; intro h; have := congrArg Fin.val h; dsimp only at this; omega
      · rw [hperV i (by omega), hv3_eq]; intro h; have := congrArg Fin.val h; dsimp only at this; omega
      · by_cases hB1 : i < L + 3
        · have he := (hlocal_ext i (by omega)).2.2
          have hm1 : (i + n - 1) % n = (i + (L + 5) - 1) % (L + 5) := by
            rw [show i + n - 1 = (i - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
                show i + (L + 5) - 1 = (i - 1) + (L + 5) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hm3 : (i + n - 3) % n = (i + (L + 5) - 3) % (L + 5) := by
            rw [show i + n - 3 = (i - 3) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
                show i + (L + 5) - 3 = (i - 3) + (L + 5) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hm1, hm3]; exact he
        · rw [show (i + n - 1) % n = i - 1 by
                rw [show i + n - 1 = (i - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)],
              show (i + n - 3) % n = i - 3 by
                rw [show i + n - 3 = (i - 3) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
          rw [hperV i (by omega), hper1 i (by omega), hper1 (i - 1) (by omega),
              hper3 i (by omega), hper3 (i - 3) (by omega)]
          simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
            List.nodup_nil, not_false_eq_true, and_true, Fin.mk.injEq]
          omega
    · set j := i - (5 * (m' + 1))
      have hj : L + 2 ≤ j ∧ j < L + 5 := by omega
      have he := hlocal_ext j (by omega)
      have hfv_ij : fv i = fv j := by
        rw [hperV i (by omega), hperV j (by omega)]; ext; dsimp only; omega
      have hfv1_ij : fv ((i + 1) % n) = fv ((j + 1) % (L + 5)) := by
        by_cases hlt : i + 1 < n
        · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega),
              hperV (i + 1) (by omega), hperV (j + 1) (by omega)]
          ext; dsimp only; omega
        · have hi1 : i + 1 = n := by omega
          have hj1 : j + 1 = L + 5 := by omega
          rw [hi1, Nat.mod_self, hj1, Nat.mod_self]
      have hfv3_ij : fv ((i + 3) % n) = fv ((j + 3) % (L + 5)) := by
        rw [Nat.mod_eq_sub_mod (by omega : n ≤ i + 3), Nat.mod_eq_of_lt (by omega),
            Nat.mod_eq_sub_mod (by omega : L + 5 ≤ j + 3), Nat.mod_eq_of_lt (by omega),
            show i + 3 - n = j + 3 - (L + 5) by omega]
      refine ⟨?_, ?_, ?_⟩
      · rw [hfv_ij, hfv1_ij]; exact he.1
      · rw [hfv_ij, hfv3_ij]; exact he.2.1
      · rw [show (i + n - 1) % n = i - 1 by
              rw [show i + n - 1 = (i - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)],
            show (i + n - 3) % n = i - 3 by
              rw [show i + n - 3 = (i - 3) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
        rw [hperV i (by omega), hper1 i (by omega), hper1 (i - 1) (by omega),
            hper3 i (by omega), hper3 (i - 3) (by omega)]
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          List.nodup_nil, not_false_eq_true, and_true, Fin.mk.injEq]
        omega

private lemma splice_5tc (L : ℕ) (hL : 7 ≤ L) (vB e1B e3B : List ℕ)
    (h0 : natArrayValid L 5 vB e1B e3B = true)
    (h1 : natArrayValid (L + 5) 5 (vB ++ b5v) (e1B ++ b5e1) (e3B ++ b5e3) = true) :
    ∀ q : ℕ, HasTotalColoring (circulant13 (L + 5 * q)) 5 := by
  intro q
  cases q with
  | zero =>
    simpa using hasTotalColoring_of_natArray hL (by omega : 0 < 5) vB e1B e3B h0
  | succ m =>
    cases m with
    | zero =>
      simpa using hasTotalColoring_of_natArray (by omega : 7 ≤ L + 5) (by omega : 0 < 5)
        (vB ++ b5v) (e1B ++ b5e1) (e3B ++ b5e3) h1
    | succ m' =>
      unfold natArrayValid at h1
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h1
      have hlenV : vB.length = L := by have := h1.1.1.1.1.1.1; simp [b5v] at this; omega
      have hlen1 : e1B.length = L := by have := h1.1.1.1.1.1.2; simp [b5e1] at this; omega
      have hlen3 : e3B.length = L := by have := h1.1.1.1.1.2; simp [b5e3] at this; omega
      have hv_lt : ∀ i, (vB ++ b5v).getD i 0 < 5 := list_getD_lt (by omega) (List.all_eq_true.mpr h1.1.1.1.2)
      have h1_lt : ∀ i, (e1B ++ b5e1).getD i 0 < 5 := list_getD_lt (by omega) (List.all_eq_true.mpr h1.1.1.2)
      have h3_lt : ∀ i, (e3B ++ b5e3).getD i 0 < 5 := list_getD_lt (by omega) (List.all_eq_true.mpr h1.1.2)
      let fv : ℕ → Fin 5 := fun i =>
        if i < L then ⟨vB.getD i 0 % 5, Nat.mod_lt _ (by omega)⟩ else ⟨(i - L) % 5, Nat.mod_lt _ (by omega)⟩
      let f1 : ℕ → Fin 5 := fun i =>
        if i < L then ⟨e1B.getD i 0 % 5, Nat.mod_lt _ (by omega)⟩ else ⟨(i - L + 3) % 5, Nat.mod_lt _ (by omega)⟩
      let f3 : ℕ → Fin 5 := fun i =>
        if i < L then ⟨e3B.getD i 0 % 5, Nat.mod_lt _ (by omega)⟩ else ⟨(i - L + 4) % 5, Nat.mod_lt _ (by omega)⟩
      have hgetV : ∀ i < L + 5, (vB ++ b5v).getD i 0 = (fv i).val := by
        intro i hi
        by_cases hil : i < L
        · have hlt5 := hv_lt i
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < vB.length)] at hlt5 ⊢
          simp only [fv, if_pos hil, List.getD_eq_getElem?_getD]
          exact (Nat.mod_eq_of_lt hlt5).symm
        · simp only [fv, if_neg hil, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by omega : vB.length ≤ i), hlenV]
          have hlt : i - L < 5 := by omega
          interval_cases (i - L) <;> rfl
      have hget1 : ∀ i < L + 5, (e1B ++ b5e1).getD i 0 = (f1 i).val := by
        intro i hi
        by_cases hil : i < L
        · have hlt5 := h1_lt i
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < e1B.length)] at hlt5 ⊢
          simp only [f1, if_pos hil, List.getD_eq_getElem?_getD]
          exact (Nat.mod_eq_of_lt hlt5).symm
        · simp only [f1, if_neg hil, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by omega : e1B.length ≤ i), hlen1]
          have hlt : i - L < 5 := by omega
          interval_cases (i - L) <;> rfl
      have hget3 : ∀ i < L + 5, (e3B ++ b5e3).getD i 0 = (f3 i).val := by
        intro i hi
        by_cases hil : i < L
        · have hlt5 := h3_lt i
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < e3B.length)] at hlt5 ⊢
          simp only [f3, if_pos hil, List.getD_eq_getElem?_getD]
          exact (Nat.mod_eq_of_lt hlt5).symm
        · simp only [f3, if_neg hil, List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by omega : e3B.length ≤ i), hlen3]
          have hlt : i - L < 5 := by omega
          interval_cases (i - L) <;> rfl
      have hlocal_ext : ∀ j < L + 5,
          fv j ≠ fv ((j + 1) % (L + 5)) ∧
          fv j ≠ fv ((j + 3) % (L + 5)) ∧
          [fv j, f1 j, f1 ((j + (L + 5) - 1) % (L + 5)),
           f3 j, f3 ((j + (L + 5) - 3) % (L + 5))].Nodup := by
        intro j hj
        have h := h1.2 j hj
        simp only [bne_iff_ne] at h
        have hv0 := hgetV j hj
        have hv1 := hgetV ((j + 1) % (L + 5)) (Nat.mod_lt _ (by omega))
        have hv3 := hgetV ((j + 3) % (L + 5)) (Nat.mod_lt _ (by omega))
        have he10 := hget1 j hj
        have he1m := hget1 ((j + (L + 5) - 1) % (L + 5)) (Nat.mod_lt _ (by omega))
        have he30 := hget3 j hj
        have he3m := hget3 ((j + (L + 5) - 3) % (L + 5)) (Nat.mod_lt _ (by omega))
        rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩
        have ofV : ∀ {x y : Fin 5}, x.val ≠ y.val → x ≠ y := fun hxy h => hxy (congrArg Fin.val h)
        rw [hv0, hv1] at a1; rw [hv0, hv3] at a2
        rw [hv0, he10] at a3; rw [hv0, he1m] at a4; rw [hv0, he30] at a5; rw [hv0, he3m] at a6
        rw [he10, he1m] at a7; rw [he10, he30] at a8; rw [he10, he3m] at a9
        rw [he1m, he30] at a10; rw [he1m, he3m] at a11; rw [he30, he3m] at a12
        refine ⟨ofV a1, ofV a2, ?_⟩
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil,
          not_false_eq_true, and_true]
        exact ⟨⟨ofV a3, ofV a4, ofV a5, ofV a6⟩, ⟨ofV a7, ofV a8, ofV a9⟩, ⟨ofV a10, ofV a11⟩, ofV a12⟩
      exact splice_5tc_ge2 L hL fv f1 f3 hlocal_ext
        (fun i hi => by dsimp only [fv]; rw [if_neg (by omega)])
        (fun i hi => by dsimp only [f1]; rw [if_neg (by omega)])
        (fun i hi => by dsimp only [f3]; rw [if_neg (by omega)]) m'

private lemma five_tc_mod4 (q : ℕ) : HasTotalColoring (circulant13 (9 + 5 * q)) 5 :=
  splice_5tc 9 (by omega)
    [0, 1, 0, 1, 2, 3, 4, 0, 1]
    [3, 4, 2, 3, 4, 2, 3, 4, 2]
    [4, 0, 1, 0, 1, 0, 1, 2, 3]
    (by decide) (by decide) q

private lemma five_tc_11 : HasTotalColoring (circulant13 11) 5 :=
  hasTotalColoring_of_natArray (by omega) (by omega : 0 < 5)
    [0, 2, 0, 2, 1, 4, 0, 4, 2, 4, 3]
    [1, 3, 1, 0, 3, 1, 3, 1, 3, 1, 2]
    [3, 4, 2, 4, 2, 0, 2, 0, 4, 0, 4]
    (by decide)

private lemma five_tc_mod1 (q : ℕ) : HasTotalColoring (circulant13 (16 + 5 * q)) 5 :=
  splice_5tc 16 (by omega)
    [0, 1, 2, 3, 2, 0, 1, 0, 4, 2, 1, 2, 3, 4, 0, 1]
    [3, 0, 1, 0, 1, 3, 4, 1, 3, 4, 3, 4, 2, 3, 4, 2]
    [4, 4, 4, 2, 3, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 3]
    (by decide) (by decide) q

private lemma five_tc_mod3 (q : ℕ) : HasTotalColoring (circulant13 (18 + 5 * q)) 5 :=
  splice_5tc 18 (by omega)
    [0, 1, 2, 3, 2, 3, 1, 0, 4, 2, 3, 0, 1, 2, 3, 4, 0, 1]
    [3, 0, 1, 0, 1, 0, 4, 1, 0, 1, 4, 2, 3, 4, 2, 3, 4, 2]
    [4, 4, 4, 2, 3, 2, 3, 2, 3, 4, 0, 1, 0, 1, 0, 1, 2, 3]
    (by decide) (by decide) q

private lemma five_tc_mod2 (q : ℕ) : HasTotalColoring (circulant13 (22 + 5 * q)) 5 :=
  splice_5tc 22 (by omega)
    [0, 1, 2, 3, 2, 0, 1, 4, 3, 2, 0, 2, 4, 2, 4, 3, 1, 0, 2, 4, 3, 1]
    [3, 0, 1, 0, 1, 3, 0, 1, 0, 1, 3, 0, 1, 3, 0, 4, 3, 4, 3, 0, 4, 2]
    [4, 4, 4, 2, 3, 2, 4, 2, 4, 3, 4, 1, 2, 0, 2, 1, 2, 1, 0, 1, 2, 3]
    (by decide) (by decide) q

private lemma five_tc_general {n : ℕ} (hn : 7 ≤ n)
    (hnot : ¬ (n = 7 ∨ n = 8 ∨ n = 12 ∨ n = 13 ∨ n = 17)) :
    HasTotalColoring (circulant13 n) 5 := by
  have hmod : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hmod with h0 | h1 | h2 | h3 | h4
  · rw [show n = 5 * (n / 5) by omega]
    exact five_tc_mult5 (n / 5) (by omega)
  · by_cases h11 : n = 11
    · subst h11; exact five_tc_11
    · rw [show n = 16 + 5 * ((n - 16) / 5) by omega]
      exact five_tc_mod1 ((n - 16) / 5)
  · rw [show n = 22 + 5 * ((n - 22) / 5) by omega]
    exact five_tc_mod2 ((n - 22) / 5)
  · rw [show n = 18 + 5 * ((n - 18) / 5) by omega]
    exact five_tc_mod3 ((n - 18) / 5)
  · rw [show n = 9 + 5 * ((n - 9) / 5) by omega]
    exact five_tc_mod4 ((n - 9) / 5)

private lemma six_tc_7 : HasTotalColoring (circulant13 7) 6 :=
  hasTotalColoring_of_natArray (by omega) (by omega : 0 < 6)
    [0, 2, 1, 4, 1, 0, 2]
    [1, 0, 3, 0, 4, 3, 4]
    [2, 3, 2, 1, 5, 5, 5]
    (by decide)

private lemma six_tc_8 : HasTotalColoring (circulant13 8) 6 :=
  hasTotalColoring_of_natArray (by omega) (by omega : 0 < 6)
    [0, 2, 1, 4, 5, 4, 5, 3]
    [1, 0, 3, 0, 1, 3, 0, 4]
    [2, 3, 2, 1, 2, 5, 4, 5]
    (by decide)

private lemma six_tc_12 : HasTotalColoring (circulant13 12) 6 :=
  hasTotalColoring_of_natArray (by omega) (by omega : 0 < 6)
    [0, 2, 1, 4, 1, 0, 2, 3, 2, 1, 4, 3]
    [1, 0, 3, 0, 4, 3, 0, 4, 3, 0, 2, 4]
    [2, 3, 2, 1, 2, 1, 4, 1, 0, 5, 5, 5]
    (by decide)

private lemma six_tc_13 : HasTotalColoring (circulant13 13) 6 :=
  hasTotalColoring_of_natArray (by omega) (by omega : 0 < 6)
    [0, 2, 1, 4, 1, 0, 2, 3, 2, 1, 4, 5, 2]
    [1, 0, 3, 0, 4, 3, 0, 4, 0, 2, 0, 1, 4]
    [2, 3, 2, 1, 2, 1, 4, 1, 3, 3, 3, 4, 5]
    (by decide)

private lemma six_tc_17 : HasTotalColoring (circulant13 17) 6 :=
  hasTotalColoring_of_natArray (by omega) (by omega : 0 < 6)
    [0, 2, 1, 4, 1, 0, 2, 3, 2, 1, 0, 1, 2, 4, 5, 3, 5]
    [1, 0, 3, 0, 4, 3, 0, 4, 0, 2, 4, 0, 1, 0, 1, 0, 3]
    [2, 3, 2, 1, 2, 1, 4, 1, 3, 3, 3, 2, 4, 2, 4, 5, 4]
    (by decide)

/-! ### Part 5: Non-existence of 5-total-colorings for `n ∈ {7, 8, 12, 13, 17}` -/

private lemma card_even_of_fpf_invol {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α → α) (hmem : ∀ x ∈ S, f x ∈ S) (hne : ∀ x ∈ S, f x ≠ x)
    (hinvol : ∀ x ∈ S, f (f x) = x) : Even S.card := by
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h k ih =>
    by_cases hS : S = ∅
    · subst hS; exact ⟨0, by simp at hn; omega⟩
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hfx : f x ∈ S := hmem x hx
      have hne_x : f x ≠ x := hne x hx
      let S' := (S.erase x).erase (f x)
      have hfx_er : f x ∈ S.erase x := Finset.mem_erase.mpr ⟨hne_x, hfx⟩
      have hcard' : S'.card + 2 = S.card := by
        have h1 : (S.erase x).card + 1 = S.card := Finset.card_erase_add_one hx
        have h2 : S'.card + 1 = (S.erase x).card := Finset.card_erase_add_one hfx_er
        omega
      have hsub : S' ⊆ S := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hev : Even S'.card := by
        refine ih S'.card (by omega) S' ?_ ?_ ?_ rfl
        · intro y hy
          have hyS : y ∈ S := hsub hy
          have hy_ne_fx : y ≠ f x := (Finset.mem_erase.mp hy).1
          have hy_ne_x : y ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hmem y hyS⟩⟩
          · intro h; exact hy_ne_x (by rw [← hinvol y hyS, h, hinvol x hx])
          · intro h; exact hy_ne_fx (by rw [← hinvol y hyS, h])
        · intro y hy; exact hne y (hsub hy)
        · intro y hy; exact hinvol y (hsub hy)
      rcases hev with ⟨m, hm⟩
      exact ⟨m + 1, by omega⟩

private lemma exists_unique_mate {n : ℕ} (hn : 7 ≤ n)
    {cv : ZMod n → Fin 5} {ce : (circulant13 n).edgeSet → Fin 5}
    (htc : IsTotalColoring (circulant13 n) 5 cv ce) (c : Fin 5) {u : ZMod n} (hu : cv u ≠ c) :
    ∃! v : ZMod n, ∃ h : (circulant13 n).Adj u v, ce ⟨s(u, v), h⟩ = c := by
  let e1 : (circulant13 n).edgeSet := ⟨s(u, u + 1), (adj_iff_mem hn u (u + 1)).mpr (Or.inl rfl)⟩
  let e2 : (circulant13 n).edgeSet := ⟨s(u - 1, u), (adj_iff_mem hn (u - 1) u).mpr (Or.inl (by ring))⟩
  let e3 : (circulant13 n).edgeSet := ⟨s(u, u + 3), (adj_iff_mem hn u (u + 3)).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩
  let e4 : (circulant13 n).edgeSet := ⟨s(u - 3, u), (adj_iff_mem hn (u - 3) u).mpr (Or.inr (Or.inr (Or.inl (by ring))))⟩
  let f : Fin 5 → Fin 5 := ![cv u, ce e1, ce e2, ce e3, ce e4]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨five_colors_injective hn htc u, rfl⟩
  obtain ⟨i, hi⟩ := hbij.2 c
  have hex : ∃ v : ZMod n, ∃ h : (circulant13 n).Adj u v, ce ⟨s(u, v), h⟩ = c := by
    fin_cases i
    · exact absurd hi hu
    · exact ⟨u + 1, (adj_iff_mem hn u (u + 1)).mpr (Or.inl rfl), hi⟩
    · refine ⟨u - 1, (adj_iff_mem hn u (u - 1)).mpr (Or.inr (Or.inl rfl)), ?_⟩
      have heq : (⟨s(u, u - 1), (adj_iff_mem hn u (u - 1)).mpr (Or.inr (Or.inl rfl))⟩ : (circulant13 n).edgeSet) = e2 :=
        Subtype.ext Sym2.eq_swap
      rw [heq]; exact hi
    · exact ⟨u + 3, (adj_iff_mem hn u (u + 3)).mpr (Or.inr (Or.inr (Or.inl rfl))), hi⟩
    · refine ⟨u - 3, (adj_iff_mem hn u (u - 3)).mpr (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
      have heq : (⟨s(u, u - 3), (adj_iff_mem hn u (u - 3)).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩ : (circulant13 n).edgeSet) = e4 :=
        Subtype.ext Sym2.eq_swap
      rw [heq]; exact hi
  obtain ⟨v, hv, hce⟩ := hex
  refine ⟨v, ⟨hv, hce⟩, ?_⟩
  rintro w ⟨hw, hcew⟩
  by_contra hne
  have he_ne : (⟨s(u, w), hw⟩ : (circulant13 n).edgeSet) ≠ ⟨s(u, v), hv⟩ := by
    intro heq
    have hval := congrArg Subtype.val heq
    rcases Sym2.eq_iff.mp hval with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hne h2
    · exact hv.ne h1
  exact htc.2.2 _ _ he_ne ⟨u, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩ (hcew.trans hce.symm)

private noncomputable def colorMate {n : ℕ} (hn : 7 ≤ n)
    {cv : ZMod n → Fin 5} {ce : (circulant13 n).edgeSet → Fin 5}
    (htc : IsTotalColoring (circulant13 n) 5 cv ce) (c : Fin 5) (u : ZMod n) : ZMod n :=
  if h : cv u ≠ c then Classical.choose (exists_unique_mate hn htc c h) else u

private lemma colorMate_spec {n : ℕ} (hn : 7 ≤ n)
    {cv : ZMod n → Fin 5} {ce : (circulant13 n).edgeSet → Fin 5}
    (htc : IsTotalColoring (circulant13 n) 5 cv ce) (c : Fin 5) {u : ZMod n} (hu : cv u ≠ c) :
    ∃ h : (circulant13 n).Adj u (colorMate hn htc c u),
      ce ⟨s(u, colorMate hn htc c u), h⟩ = c := by
  dsimp only [colorMate]
  rw [dif_pos hu]
  exact (Classical.choose_spec (exists_unique_mate hn htc c hu)).1

private lemma colorMate_ne_color {n : ℕ} (hn : 7 ≤ n)
    {cv : ZMod n → Fin 5} {ce : (circulant13 n).edgeSet → Fin 5}
    (htc : IsTotalColoring (circulant13 n) 5 cv ce) (c : Fin 5) {u : ZMod n} (hu : cv u ≠ c) :
    cv (colorMate hn htc c u) ≠ c := by
  obtain ⟨hadj, hce⟩ := colorMate_spec hn htc c hu
  have hne := htc.2.1 (colorMate hn htc c u) ⟨s(u, colorMate hn htc c u), hadj⟩ (Sym2.mem_mk_right _ _)
  rw [hce] at hne
  exact hne

private lemma colorMate_invol {n : ℕ} (hn : 7 ≤ n)
    {cv : ZMod n → Fin 5} {ce : (circulant13 n).edgeSet → Fin 5}
    (htc : IsTotalColoring (circulant13 n) 5 cv ce) (c : Fin 5) {u : ZMod n} (hu : cv u ≠ c) :
    colorMate hn htc c (colorMate hn htc c u) = u := by
  have hv := colorMate_ne_color hn htc c hu
  obtain ⟨hadj, hce⟩ := colorMate_spec hn htc c hu
  generalize colorMate hn htc c u = v at hv hadj hce ⊢
  have huniq := (Classical.choose_spec (exists_unique_mate hn htc c hv)).2
  unfold colorMate
  rw [dif_pos hv]
  refine (huniq u ⟨hadj.symm, ?_⟩).symm
  have heq : (⟨s(v, u), hadj.symm⟩ : (circulant13 n).edgeSet) =
      ⟨s(u, v), hadj⟩ := Subtype.ext Sym2.eq_swap
  rw [heq]; exact hce

private lemma colorClass_parity {n : ℕ} (hn : 7 ≤ n) [NeZero n]
    {cv : ZMod n → Fin 5} {ce : (circulant13 n).edgeSet → Fin 5}
    (htc : IsTotalColoring (circulant13 n) 5 cv ce) (c : Fin 5) :
    (Finset.univ.filter (fun u : ZMod n => cv u = c)).card % 2 = n % 2 := by
  let Ic := Finset.univ.filter (fun u : ZMod n => cv u = c)
  let Cc := Finset.univ.filter (fun u : ZMod n => cv u ≠ c)
  have hsum : Ic.card + Cc.card = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (ZMod n)))
      (p := fun u => cv u = c)
    simpa [Ic, Cc, ZMod.card] using this
  have hev : Even Cc.card := by
    refine card_even_of_fpf_invol Cc (colorMate hn htc c) ?_ ?_ ?_
    · intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, colorMate_ne_color hn htc c (Finset.mem_filter.mp hu).2⟩
    · intro u hu
      obtain ⟨hadj, _⟩ := colorMate_spec hn htc c (Finset.mem_filter.mp hu).2
      exact hadj.ne.symm
    · intro u hu
      exact colorMate_invol hn htc c (Finset.mem_filter.mp hu).2
  rcases hev with ⟨m, hm⟩
  change Ic.card % 2 = n % 2
  omega

private lemma sum_colorClass_card {n : ℕ} [NeZero n] (cv : ZMod n → Fin 5) :
    ∑ c : Fin 5, (Finset.univ.filter (fun u : ZMod n => cv u = c)).card = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := cv) (s := (Finset.univ : Finset (ZMod n)))
    (t := (Finset.univ : Finset (Fin 5))) (fun _ _ => Finset.mem_univ _)
  simpa [ZMod.card] using h.symm

/-! #### Case `n = 7` -/

private lemma indep_le_two_7 :
    ∀ u v w : ZMod 7, u ≠ v → u ≠ w → v ≠ w →
      (circulant13 7).Adj u v ∨ (circulant13 7).Adj u w ∨ (circulant13 7).Adj v w := by
  dsimp only [circulant13]; decide

private lemma no_5tc_7 : ¬ HasTotalColoring (circulant13 7) 5 := by
  rintro ⟨cv, ce, htc⟩
  have hle1 : ∀ c : Fin 5, (Finset.univ.filter (fun u : ZMod 7 => cv u = c)).card ≤ 1 := by
    intro c
    set Ic := Finset.univ.filter (fun u : ZMod 7 => cv u = c)
    have hpar : Ic.card % 2 = 1 := colorClass_parity (by omega : 7 ≤ 7) htc c
    have hle2 : Ic.card ≤ 2 := by
      by_contra hgt
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < Ic.card)
      have h1 := Finset.card_erase_add_one hu
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (Ic.erase u).card)
      have h2 := Finset.card_erase_add_one hv
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < ((Ic.erase u).erase v).card)
      have huv : v ≠ u := (Finset.mem_erase.mp hv).1
      have hvI : v ∈ Ic := (Finset.mem_erase.mp hv).2
      have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
      have hwu : w ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
      have hwI : w ∈ Ic := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2
      have hcu : cv u = c := (Finset.mem_filter.mp hu).2
      have hcv : cv v = c := (Finset.mem_filter.mp hvI).2
      have hcw : cv w = c := (Finset.mem_filter.mp hwI).2
      rcases indep_le_two_7 u v w huv.symm hwu.symm hwv.symm with h | h | h
      · exact htc.1 u v h (hcu.trans hcv.symm)
      · exact htc.1 u w h (hcu.trans hcw.symm)
      · exact htc.1 v w h (hcv.trans hcw.symm)
    omega
  have hsum := sum_colorClass_card cv
  have hbd : ∑ c : Fin 5, (Finset.univ.filter (fun u : ZMod 7 => cv u = c)).card ≤ ∑ _c : Fin 5, 1 :=
    Finset.sum_le_sum fun c _ => hle1 c
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hbd
  omega

/-! #### Cases `n = 8` and `n = 12` (bipartite balance) -/

private lemma bipartite_color_balance {n : ℕ} (hn : 7 ≤ n) [NeZero n]
    (hflip : ∀ u v : ZMod n, (circulant13 n).Adj u v → u.val % 2 ≠ v.val % 2)
    (heq_eo : (Finset.univ.filter (fun u : ZMod n => u.val % 2 = 0)).card =
              (Finset.univ.filter (fun u : ZMod n => u.val % 2 = 1)).card)
    {cv : ZMod n → Fin 5} {ce : (circulant13 n).edgeSet → Fin 5}
    (htc : IsTotalColoring (circulant13 n) 5 cv ce) (c : Fin 5) :
    (Finset.univ.filter (fun u : ZMod n => cv u = c ∧ u.val % 2 = 0)).card =
    (Finset.univ.filter (fun u : ZMod n => cv u = c ∧ u.val % 2 = 1)).card := by
  let E := Finset.univ.filter (fun u : ZMod n => u.val % 2 = 0)
  let O := Finset.univ.filter (fun u : ZMod n => u.val % 2 = 1)
  let CE := Finset.univ.filter (fun u : ZMod n => cv u ≠ c ∧ u.val % 2 = 0)
  let CO := Finset.univ.filter (fun u : ZMod n => cv u ≠ c ∧ u.val % 2 = 1)
  have hCE_CO : CE.card = CO.card := by
    refine Finset.card_bij (fun u _ => colorMate hn htc c u) ?_ ?_ ?_
    · intro u hu
      have ⟨hne, hev⟩ := (Finset.mem_filter.mp hu).2
      obtain ⟨hadj, _⟩ := colorMate_spec hn htc c hne
      have hne' := colorMate_ne_color hn htc c hne
      have hfl := hflip u _ hadj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne', by omega⟩
    · intro u₁ hu₁ u₂ hu₂ heq
      have h1 := (Finset.mem_filter.mp hu₁).2.1
      have h2 := (Finset.mem_filter.mp hu₂).2.1
      rw [← colorMate_invol hn htc c h1, ← colorMate_invol hn htc c h2, heq]
    · intro v hv
      have ⟨hne, hodd⟩ := (Finset.mem_filter.mp hv).2
      obtain ⟨hadj, _⟩ := colorMate_spec hn htc c hne
      have hne' := colorMate_ne_color hn htc c hne
      have hfl := hflip v _ hadj
      refine ⟨colorMate hn htc c v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne', by omega⟩,
        colorMate_invol hn htc c hne⟩
  have hE : (Finset.univ.filter (fun u : ZMod n => cv u = c ∧ u.val % 2 = 0)).card + CE.card = E.card := by
    have h := Finset.card_filter_add_card_filter_not (s := E) (p := fun u => cv u = c)
    have h1 : E.filter (fun u => cv u = c) = Finset.univ.filter (fun u : ZMod n => cv u = c ∧ u.val % 2 = 0) := by
      ext u; simp [E, and_comm]
    have h2 : E.filter (fun u => ¬ cv u = c) = CE := by
      ext u; simp [E, CE, and_comm]
    rw [h1, h2] at h; exact h
  have hO : (Finset.univ.filter (fun u : ZMod n => cv u = c ∧ u.val % 2 = 1)).card + CO.card = O.card := by
    have h := Finset.card_filter_add_card_filter_not (s := O) (p := fun u => cv u = c)
    have h1 : O.filter (fun u => cv u = c) = Finset.univ.filter (fun u : ZMod n => cv u = c ∧ u.val % 2 = 1) := by
      ext u; simp [O, and_comm]
    have h2 : O.filter (fun u => ¬ cv u = c) = CO := by
      ext u; simp [O, CO, and_comm]
    rw [h1, h2] at h; exact h
  have hEO : E.card = O.card := heq_eo
  omega

private lemma no_5tc_8 : ¬ HasTotalColoring (circulant13 8) 5 := by
  rintro ⟨cv, ce, htc⟩
  have hflip : ∀ u v : ZMod 8, (circulant13 8).Adj u v → u.val % 2 ≠ v.val % 2 := by
    dsimp only [circulant13]; decide
  have heo : (Finset.univ.filter (fun u : ZMod 8 => u.val % 2 = 0)).card =
             (Finset.univ.filter (fun u : ZMod 8 => u.val % 2 = 1)).card := by decide
  have hall_adj : ∀ u v : ZMod 8, u.val % 2 = 0 → v.val % 2 = 1 → (circulant13 8).Adj u v := by
    dsimp only [circulant13]; decide
  have hzero : ∀ c : Fin 5, (Finset.univ.filter (fun u : ZMod 8 => cv u = c ∧ u.val % 2 = 0)).card = 0 := by
    intro c
    have hbal := bipartite_color_balance (by omega : 7 ≤ 8) hflip heo htc c
    by_contra hne
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun u : ZMod 8 => cv u = c ∧ u.val % 2 = 0)).card)
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun u : ZMod 8 => cv u = c ∧ u.val % 2 = 1)).card)
    have ⟨hcu, heu⟩ := (Finset.mem_filter.mp hu).2
    have ⟨hcv, hov⟩ := (Finset.mem_filter.mp hv).2
    exact htc.1 u v (hall_adj u v heu hov) (hcu.trans hcv.symm)
  have hsum : ∑ c : Fin 5, (Finset.univ.filter (fun u : ZMod 8 => cv u = c ∧ u.val % 2 = 0)).card =
      (Finset.univ.filter (fun u : ZMod 8 => u.val % 2 = 0)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := cv)
      (s := Finset.univ.filter (fun u : ZMod 8 => u.val % 2 = 0))
      (t := (Finset.univ : Finset (Fin 5))) (fun _ _ => Finset.mem_univ _)
    rw [h]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1; ext u; simp [and_comm]
  have h4 : (Finset.univ.filter (fun u : ZMod 8 => u.val % 2 = 0)).card = 4 := by decide
  simp only [hzero, Finset.sum_const_zero] at hsum
  omega

private lemma no_k22_nonadj_12 :
    ∀ u₁ u₂ v₁ v₂ : ZMod 12,
      u₁.val % 2 = 0 → u₂.val % 2 = 0 → u₁ ≠ u₂ →
      v₁.val % 2 = 1 → v₂.val % 2 = 1 → v₁ ≠ v₂ →
      (circulant13 12).Adj u₁ v₁ ∨ (circulant13 12).Adj u₁ v₂ ∨
      (circulant13 12).Adj u₂ v₁ ∨ (circulant13 12).Adj u₂ v₂ := by
  dsimp only [circulant13]; decide

private lemma no_5tc_12 : ¬ HasTotalColoring (circulant13 12) 5 := by
  rintro ⟨cv, ce, htc⟩
  have hflip : ∀ u v : ZMod 12, (circulant13 12).Adj u v → u.val % 2 ≠ v.val % 2 := by
    dsimp only [circulant13]; decide
  have heo : (Finset.univ.filter (fun u : ZMod 12 => u.val % 2 = 0)).card =
             (Finset.univ.filter (fun u : ZMod 12 => u.val % 2 = 1)).card := by decide
  have hle1 : ∀ c : Fin 5, (Finset.univ.filter (fun u : ZMod 12 => cv u = c ∧ u.val % 2 = 0)).card ≤ 1 := by
    intro c
    have hbal := bipartite_color_balance (by omega : 7 ≤ 12) hflip heo htc c
    by_contra hgt
    obtain ⟨u₁, hu₁, u₂, hu₂, hu_ne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun u : ZMod 12 => cv u = c ∧ u.val % 2 = 0)).card)
    obtain ⟨v₁, hv₁, v₂, hv₂, hv_ne⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter (fun u : ZMod 12 => cv u = c ∧ u.val % 2 = 1)).card)
    have ⟨hcu1, heu1⟩ := (Finset.mem_filter.mp hu₁).2
    have ⟨hcu2, heu2⟩ := (Finset.mem_filter.mp hu₂).2
    have ⟨hcv1, hov1⟩ := (Finset.mem_filter.mp hv₁).2
    have ⟨hcv2, hov2⟩ := (Finset.mem_filter.mp hv₂).2
    rcases no_k22_nonadj_12 u₁ u₂ v₁ v₂ heu1 heu2 hu_ne hov1 hov2 hv_ne with h | h | h | h
    · exact htc.1 u₁ v₁ h (hcu1.trans hcv1.symm)
    · exact htc.1 u₁ v₂ h (hcu1.trans hcv2.symm)
    · exact htc.1 u₂ v₁ h (hcu2.trans hcv1.symm)
    · exact htc.1 u₂ v₂ h (hcu2.trans hcv2.symm)
  have hsum : ∑ c : Fin 5, (Finset.univ.filter (fun u : ZMod 12 => cv u = c ∧ u.val % 2 = 0)).card =
      (Finset.univ.filter (fun u : ZMod 12 => u.val % 2 = 0)).card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := cv)
      (s := Finset.univ.filter (fun u : ZMod 12 => u.val % 2 = 0))
      (t := (Finset.univ : Finset (Fin 5))) (fun _ _ => Finset.mem_univ _)
    rw [h]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1; ext u; simp [and_comm]
  have h6 : (Finset.univ.filter (fun u : ZMod 12 => u.val % 2 = 0)).card = 6 := by decide
  have hbd : ∑ c : Fin 5, (Finset.univ.filter (fun u : ZMod 12 => cv u = c ∧ u.val % 2 = 0)).card ≤ ∑ _c : Fin 5, 1 :=
    Finset.sum_le_sum fun c _ => hle1 c
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hbd
  omega

/-! #### Shared Odd-Gap Shift Lemma for `n = 13` and `n = 17` -/

private lemma indep_odd_shift {n : ℕ} (hn : 7 ≤ n) (hn_odd : n % 2 = 1) [NeZero n]
    (S : Finset (ZMod n)) (hindep : ∀ u ∈ S, ∀ v ∈ S, ¬ (circulant13 n).Adj u v)
    (hcard : 3 ≤ S.card) (hno3odd : n < 15 + 2 * (S.card - 3)) :
    ∃ r ∈ S, ∀ x ∈ S, (x - r).val % 2 = 0 ∧ (x - r).val ≤ n - 5 := by
  let V := S.image ZMod.val
  have hVcard : V.card = S.card :=
    Finset.card_image_of_injective S (ZMod.val_injective n)
  let L := V.sort (· ≤ ·)
  have hLlen : L.length = S.card := by rw [Finset.length_sort, hVcard]
  have hLsorted : L.Pairwise (· < ·) :=
    List.pairwise_iff_getElem.mpr fun i j hi hj hij =>
      lt_of_le_of_ne
        (List.pairwise_iff_getElem.mp (V.pairwise_sort (· ≤ ·)) i j hi hj hij)
        (List.pairwise_iff_getElem.mp (V.sort_nodup (· ≤ ·)) i j hi hj hij)
  have hLmem : ∀ i (hi : i < L.length), (L[i] : ZMod n) ∈ S ∧ L[i] < n := by
    intro i hi
    have hmemV : L[i] ∈ V := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hi)
    obtain ⟨u, huS, huval⟩ := Finset.mem_image.mp hmemV
    rw [← huval]
    exact ⟨by simpa [ZMod.natCast_zmod_val] using huS, u.val_lt⟩
  let k := L.length
  have hk3 : 3 ≤ k := by omega
  let a : ℕ → ℕ := fun i => L.getD i 0
  have ha_eq : ∀ i (hi : i < k), a i = L[i] := fun i hi => by
    simp [a, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have ha_lt : ∀ i j, i < j → j < k → a i < a j := fun i j hij hjk => by
    rw [ha_eq i (by omega), ha_eq j hjk]
    exact List.pairwise_iff_getElem.mp hLsorted i j (by omega) hjk hij
  have ha_mem : ∀ i < k, (a i : ZMod n) ∈ S ∧ a i < n := fun i hi => by
    rw [ha_eq i hi]; exact hLmem i hi
  let gap : ℕ → ℕ := fun i => if i + 1 < k then a (i + 1) - a i else n + a 0 - a (k - 1)
  have hgap_sum : ∑ i ∈ Finset.range k, gap i = n := by
    have hsplit : Finset.range k = insert (k - 1) (Finset.range (k - 1)) := by
      ext i; simp only [Finset.mem_range, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have hlast : gap (k - 1) = n + a 0 - a (k - 1) := by dsimp only [gap]; rw [if_neg (by omega)]
    have hrest : ∑ i ∈ Finset.range (k - 1), gap i = a (k - 1) - a 0 := by
      have hcongr : ∑ i ∈ Finset.range (k - 1), gap i = ∑ i ∈ Finset.range (k - 1), (a (i + 1) - a i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        dsimp only [gap]; rw [if_pos (by have := Finset.mem_range.mp hi; omega)]
      rw [hcongr]
      have htele : ∀ m, m < k → ∑ i ∈ Finset.range m, (a (i + 1) - a i) = a m - a 0 := by
        intro m hm
        induction m with
        | zero => simp
        | succ m' ih =>
          rw [Finset.sum_range_succ, ih (by omega)]
          have hle1 : a 0 ≤ a m' := by
            by_cases hm0 : m' = 0
            · subst hm0; exact le_rfl
            · exact (ha_lt 0 m' (by omega) (by omega)).le
          have hle2 : a m' ≤ a (m' + 1) := (ha_lt m' (m' + 1) (by omega) hm).le
          omega
      exact htele (k - 1) (by omega)
    rw [hlast, hrest]
    have h0lt : a 0 < a (k - 1) := ha_lt 0 (k - 1) (by omega) (by omega)
    have hkn : a (k - 1) < n := (ha_mem (k - 1) (by omega)).2
    omega
  have hgap_ge2 : ∀ i < k, 2 ≤ gap i ∧ gap i ≠ 3 := by
    intro i hi
    by_cases hlast : i + 1 < k
    · have h1 := ha_mem i hi
      have h2 := ha_mem (i + 1) hlast
      have hlt := ha_lt i (i + 1) (by omega) hlast
      have hg : gap i = a (i + 1) - a i := by dsimp only [gap]; rw [if_pos hlast]
      rw [hg]
      constructor
      · by_contra hle
        have heq1 : a (i + 1) = a i + 1 := by omega
        have hadj : (circulant13 n).Adj (a i : ZMod n) (a (i + 1) : ZMod n) :=
          (adj_iff_mem hn _ _).mpr (Or.inl (by rw [heq1]; push_cast; rfl))
        exact hindep _ h1.1 _ h2.1 hadj
      · intro heq3
        have heq : a (i + 1) = a i + 3 := by omega
        have hadj : (circulant13 n).Adj (a i : ZMod n) (a (i + 1) : ZMod n) :=
          (adj_iff_mem hn _ _).mpr (Or.inr (Or.inr (Or.inl (by rw [heq]; push_cast; rfl))))
        exact hindep _ h1.1 _ h2.1 hadj
    · have hik : i = k - 1 := by omega
      subst hik
      have h1 := ha_mem (k - 1) (by omega)
      have h2 := ha_mem 0 (by omega)
      have hlt := ha_lt 0 (k - 1) (by omega) (by omega)
      have hg : gap (k - 1) = n + a 0 - a (k - 1) := by dsimp only [gap]; rw [if_neg (by omega)]
      rw [hg]
      constructor
      · by_contra hle
        have heq1 : a (k - 1) + 1 = n + a 0 := by omega
        have hcast : ((a (k - 1) : ZMod n) + 1) = (a 0 : ZMod n) := by
          have := congrArg (Nat.cast (R := ZMod n)) heq1
          simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add] at this
          exact this
        exact hindep _ h1.1 _ h2.1 ((adj_iff_mem hn _ _).mpr (Or.inl hcast.symm))
      · intro heq3
        have heq : a (k - 1) + 3 = n + a 0 := by omega
        have hcast : ((a (k - 1) : ZMod n) + 3) = (a 0 : ZMod n) := by
          have := congrArg (Nat.cast (R := ZMod n)) heq
          simp only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self, zero_add] at this
          exact this
        exact hindep _ h1.1 _ h2.1 ((adj_iff_mem hn _ _).mpr (Or.inr (Or.inr (Or.inl hcast.symm))))
  let odds := (Finset.range k).filter (fun i => gap i % 2 = 1)
  have hodd_ge5 : ∀ i ∈ odds, 5 ≤ gap i := by
    intro i hi
    have ⟨hir, ho⟩ := Finset.mem_filter.mp hi
    have ⟨hg2, hg3⟩ := hgap_ge2 i (Finset.mem_range.mp hir)
    omega
  have hodd_card_odd : odds.card % 2 = 1 := by
    have hsum_mod : (∑ i ∈ Finset.range k, gap i) % 2 = (∑ i ∈ Finset.range k, gap i % 2) % 2 := by
      clear hgap_sum hgap_ge2 hodd_ge5
      induction (Finset.range k) using Finset.induction_on with
      | empty => simp
      | @insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx]; omega
    have hsum_odd : ∑ i ∈ Finset.range k, gap i % 2 = odds.card := by
      have h1 : ∀ i ∈ Finset.range k, gap i % 2 = if gap i % 2 = 1 then 1 else 0 := by
        intro i _; split_ifs with h <;> omega
      rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    rw [hgap_sum, hsum_odd] at hsum_mod
    omega
  have hodd_lt3 : odds.card < 3 := by
    by_contra hge
    have h3 : 3 ≤ odds.card := by omega
    have hsub : odds ⊆ Finset.range k := Finset.filter_subset _ _
    have hlb : ∑ i ∈ Finset.range k \ odds, 2 + ∑ i ∈ odds, 5 ≤ ∑ i ∈ Finset.range k, gap i := by
      rw [← Finset.sum_sdiff hsub]
      exact add_le_add
        (Finset.sum_le_sum fun i hi => (hgap_ge2 i (Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1)).1)
        (Finset.sum_le_sum fun i hi => hodd_ge5 i hi)
    simp only [Finset.sum_const, smul_eq_mul] at hlb
    have hsd : (Finset.range k \ odds).card = k - odds.card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_range]
    rw [hsd, hgap_sum] at hlb
    have hle_k : odds.card ≤ k := by
      have := Finset.card_le_card hsub; rw [Finset.card_range] at this; exact this
    omega
  have hodd_one : odds.card = 1 := by omega
  obtain ⟨j, hj_eq⟩ := Finset.card_eq_one.mp hodd_one
  have hj_mem : j ∈ odds := by rw [hj_eq]; exact Finset.mem_singleton_self j
  have hjk : j < k := Finset.mem_range.mp (Finset.mem_filter.mp hj_mem).1
  have hj_ge5 : 5 ≤ gap j := hodd_ge5 j hj_mem
  have heven_other : ∀ i < k, i ≠ j → gap i % 2 = 0 := by
    intro i hi hij
    by_contra hne
    have : i ∈ odds := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, by omega⟩
    rw [hj_eq, Finset.mem_singleton] at this
    exact hij this
  -- Choose `r = a ((j + 1) % k)`!
  let j1 := (j + 1) % k
  have hj1 : j1 < k := Nat.mod_lt _ (by omega)
  refine ⟨(a j1 : ZMod n), (ha_mem j1 hj1).1, ?_⟩
  intro x hxS
  have hxV : x.val ∈ V := Finset.mem_image.mpr ⟨x, hxS, rfl⟩
  have hxL : x.val ∈ L := (Finset.mem_sort (· ≤ ·)).mpr hxV
  obtain ⟨m, hm, hLm⟩ := List.getElem_of_mem hxL
  have ham : a m = x.val := by rw [ha_eq m hm, hLm]
  have hx_eq : x = (a m : ZMod n) := by rw [ham, ZMod.natCast_zmod_val]
  -- Compute `(x - r).val` explicitly in terms of partial sums of even gaps!
  by_cases hj_last : j + 1 = k
  · -- `j = k - 1`, so `j1 = 0`, `r = a 0`, and `gap (k - 1) = n + a 0 - a (k - 1) ≥ 5`!
    have hj1_0 : j1 = 0 := by dsimp only [j1]; rw [hj_last, Nat.mod_self]
    have h0m : a 0 ≤ a m := by
      by_cases hm0 : m = 0
      · subst hm0; exact le_rfl
      · exact (ha_lt 0 m (by omega) hm).le
    have hmk : a m ≤ a (k - 1) := by
      by_cases hmk' : m = k - 1
      · subst hmk'; exact le_rfl
      · exact (ha_lt m (k - 1) (by omega) (by omega)).le
    have hdiff_val : (x - (a j1 : ZMod n)).val = a m - a 0 := by
      rw [hx_eq, hj1_0, ← Nat.cast_sub h0m, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := (ha_mem m hm).2; omega)]
    rw [hdiff_val]
    have hgap_last : gap j = n + a 0 - a (k - 1) := by dsimp only [gap]; rw [if_neg (by omega)]
    have hsub_ev : ∀ t ≤ m, (a t - a 0) % 2 = 0 := by
      intro t ht
      induction t with
      | zero => simp
      | succ t' ih =>
        have hstep : a (t' + 1) - a t' = gap t' := by dsimp only [gap]; rw [if_pos (by omega)]
        have hev' := heven_other t' (by omega) (by omega)
        have hle1 : a 0 ≤ a t' := by
          by_cases ht0 : t' = 0
          · subst ht0; exact le_rfl
          · exact (ha_lt 0 t' (by omega) (by omega)).le
        have hle2 : a t' ≤ a (t' + 1) := (ha_lt t' (t' + 1) (by omega) (by omega)).le
        have := ih (by omega)
        omega
    exact ⟨hsub_ev m le_rfl, by omega⟩
  · -- `j + 1 < k`, so `j1 = j + 1`, `r = a (j + 1)`, and `gap j = a (j + 1) - a j ≥ 5`!
    have hj1_eq : j1 = j + 1 := Nat.mod_eq_of_lt (by omega)
    have hgap_j : gap j = a (j + 1) - a j := by dsimp only [gap]; rw [if_pos (by omega)]
    by_cases hge : j + 1 ≤ m
    · have hle : a (j + 1) ≤ a m := by
        by_cases heq : m = j + 1
        · subst heq; exact le_rfl
        · exact (ha_lt (j + 1) m (by omega) hm).le
      have hdiff_val : (x - (a j1 : ZMod n)).val = a m - a (j + 1) := by
        rw [hx_eq, hj1_eq, ← Nat.cast_sub hle, ZMod.val_natCast,
            Nat.mod_eq_of_lt (by have := (ha_mem m hm).2; omega)]
      rw [hdiff_val]
      have hsub_ev : ∀ t, j + 1 ≤ t → t ≤ m → (a t - a (j + 1)) % 2 = 0 := by
        intro t ht1 ht2
        induction t with
        | zero => omega
        | succ t' ih =>
          by_cases ht' : t' = j
          · subst ht'; simp
          · have hstep : a (t' + 1) - a t' = gap t' := by dsimp only [gap]; rw [if_pos (by omega)]
            have hev' := heven_other t' (by omega) (by omega)
            have hle1 : a (j + 1) ≤ a t' := by
              by_cases heq : t' = j + 1
              · subst heq; exact le_rfl
              · exact (ha_lt (j + 1) t' (by omega) (by omega)).le
            have hle2 : a t' ≤ a (t' + 1) := (ha_lt t' (t' + 1) (by omega) (by omega)).le
            have := ih (by omega) (by omega)
            omega
      have ha_m_lt : a m < n := (ha_mem m hm).2
      have hle_j : a j + 5 ≤ a (j + 1) := by omega
      exact ⟨hsub_ev m hge le_rfl, by omega⟩
    · -- `m ≤ j`: wraps around `n`, so `(x - r).val = n + a m - a (j + 1)`!
      have hmj : m ≤ j := by omega
      have hlt_mr : a m < a (j + 1) := ha_lt m (j + 1) (by omega) (by omega)
      have hdiff_val : (x - (a j1 : ZMod n)).val = n + a m - a (j + 1) := by
        have hcast : ((n + a m - a (j + 1) : ℕ) : ZMod n) = (a m : ZMod n) - (a (j + 1) : ZMod n) := by
          have hle1 : a (j + 1) ≤ n + a m := by have := (ha_mem (j + 1) (by omega)).2; omega
          rw [Nat.cast_sub hle1, Nat.cast_add, ZMod.natCast_self, zero_add]
        rw [hx_eq, hj1_eq, ← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      rw [hdiff_val]
      -- `n + a m - a (j + 1) = (a (k - 1) - a (j + 1)) + gap (k - 1) + (a m - a 0)`, all three even!
      have hpart1 : ∀ t, j + 1 ≤ t → t < k → (a t - a (j + 1)) % 2 = 0 := by
        intro t ht1 ht2
        induction t with
        | zero => omega
        | succ t' ih =>
          by_cases ht' : t' = j
          · subst ht'; simp
          · have hstep : a (t' + 1) - a t' = gap t' := by dsimp only [gap]; rw [if_pos (by omega)]
            have hev' := heven_other t' (by omega) (by omega)
            have hle1 : a (j + 1) ≤ a t' := by
              by_cases heq : t' = j + 1
              · subst heq; exact le_rfl
              · exact (ha_lt (j + 1) t' (by omega) (by omega)).le
            have hle2 : a t' ≤ a (t' + 1) := (ha_lt t' (t' + 1) (by omega) (by omega)).le
            have := ih (by omega) (by omega)
            omega
      have hpart3 : ∀ t ≤ j, (a t - a 0) % 2 = 0 := by
        intro t ht
        induction t with
        | zero => simp
        | succ t' ih =>
          have hstep : a (t' + 1) - a t' = gap t' := by dsimp only [gap]; rw [if_pos (by omega)]
          have hev' := heven_other t' (by omega) (by omega)
          have hle1 : a 0 ≤ a t' := by
            by_cases ht0 : t' = 0
            · subst ht0; exact le_rfl
            · exact (ha_lt 0 t' (by omega) (by omega)).le
          have hle2 : a t' ≤ a (t' + 1) := (ha_lt t' (t' + 1) (by omega) (by omega)).le
          have := ih (by omega)
          omega
      have hp1 := hpart1 (k - 1) (by omega) (by omega)
      have hp2 : gap (k - 1) % 2 = 0 := heven_other (k - 1) (by omega) (by omega)
      have hp2_eq : gap (k - 1) = n + a 0 - a (k - 1) := by dsimp only [gap]; rw [if_neg (by omega)]
      have hp3 := hpart3 m hmj
      have hle_a0 : a 0 ≤ a m := by
        by_cases hm0 : m = 0
        · subst hm0; exact le_rfl
        · exact (ha_lt 0 m (by omega) hm).le
      have hle_am : a m ≤ a j := by
        by_cases hmeq : m = j
        · subst hmeq; exact le_rfl
        · exact (ha_lt m j (by omega) hjk).le
      have hle_j1k : a (j + 1) ≤ a (k - 1) := by
        by_cases heq : j + 1 = k - 1
        · rw [heq]
        · exact (ha_lt (j + 1) (k - 1) (by omega) (by omega)).le
      have hkn : a (k - 1) < n := (ha_mem (k - 1) (by omega)).2
      omega

private lemma shifted_adj {n : ℕ} (r u v : ZMod n) :
    (circulant13 n).Adj (u + r) (v + r) ↔ (circulant13 n).Adj u v := by
  simp only [circulant13, ne_eq, add_left_inj, add_sub_add_right_eq_sub]

private lemma odd_interior_neighbors_even {n : ℕ} (hn : 7 ≤ n) (u v : ZMod n)
    (huo : u.val % 2 = 1) (hu3 : 3 ≤ u.val) (hun : u.val + 3 < n)
    (hadj : (circulant13 n).Adj u v) : v.val % 2 = 0 := by
  have : NeZero n := ⟨by omega⟩
  rcases hadj.2 with h | h | h | h
  · have hv : v = u + 1 := by linear_combination h
    have hval : v.val = u.val + 1 := by
      rw [hv, show (u + 1).val = (u.val + 1) % n by simpa using zmod_add_val (n := n) (a := 1) (by omega) u]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hval]; omega
  · have hv : v = u - 1 := by linear_combination -h
    have hval : v.val = u.val - 1 := by
      rw [hv, show (u - 1).val = (u.val + n - 1) % n by simpa using zmod_sub_val (n := n) (a := 1) (by omega) (by omega) u,
          show u.val + n - 1 = (u.val - 1) + n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hval]; omega
  · have hv : v = u + 3 := by linear_combination h
    have hval : v.val = u.val + 3 := by
      rw [hv, show (u + 3).val = (u.val + 3) % n by simpa using zmod_add_val (n := n) (a := 3) (by omega) u]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hval]; omega
  · have hv : v = u - 3 := by linear_combination -h
    have hval : v.val = u.val - 3 := by
      rw [hv, show (u - 3).val = (u.val + n - 3) % n by simpa using zmod_sub_val (n := n) (a := 3) (by omega) (by omega) u,
          show u.val + n - 3 = (u.val - 3) + n by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hval]; omega

/-! #### Case `n = 17` -/

private lemma odd_interior_neighbors_even_17 :
    ∀ u v : ZMod 17, u.val % 2 = 1 → 3 ≤ u.val → u.val ≤ 13 →
      (circulant13 17).Adj u v → v.val % 2 = 0 := fun u v huo hu3 hu13 hadj =>
  odd_interior_neighbors_even (by omega : 7 ≤ 17) u v huo hu3 (by omega) hadj

private lemma no_5tc_17 : ¬ HasTotalColoring (circulant13 17) 5 := by
  rintro ⟨cv, ce, htc⟩
  have hle3 : ∀ c : Fin 5, (Finset.univ.filter (fun u : ZMod 17 => cv u = c)).card ≤ 3 := by
    intro c
    set Ic := Finset.univ.filter (fun u : ZMod 17 => cv u = c)
    have hpar : Ic.card % 2 = 1 := colorClass_parity (by omega : 7 ≤ 17) htc c
    by_contra hgt
    have h5 : 5 ≤ Ic.card := by omega
    have hindep : ∀ u ∈ Ic, ∀ v ∈ Ic, ¬ (circulant13 17).Adj u v := fun u hu v hv hadj =>
      htc.1 u v hadj ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
    obtain ⟨r, _, hr⟩ := indep_odd_shift (n := 17) (by omega) rfl Ic hindep (by omega) (by omega)
    let S' := Ic.image (· - r)
    have hS'card : S'.card = Ic.card :=
      Finset.card_image_of_injective Ic (fun a b h => by linear_combination h)
    have hS'sub : S' ⊆ Finset.univ.filter (fun u : ZMod 17 => u.val % 2 = 0) := by
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hr x hx).1⟩
    let OddInt := Finset.univ.filter (fun u : ZMod 17 => u.val % 2 = 1 ∧ 3 ≤ u.val ∧ u.val ≤ 13)
    let EvenRem := (Finset.univ.filter (fun u : ZMod 17 => u.val % 2 = 0)) \ S'
    let m' : ZMod 17 → ZMod 17 := fun u => colorMate (by omega : 7 ≤ 17) htc c (u + r) - r
    have hmaps : ∀ u ∈ OddInt, m' u ∈ EvenRem := by
      intro u hu
      have ⟨huo, hu3, hu13⟩ := (Finset.mem_filter.mp hu).2
      have hu_not_Ic : cv (u + r) ≠ c := by
        intro hcv
        have hxS : u + r ∈ Ic := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩
        have hev := (hr (u + r) hxS).1
        rw [add_sub_cancel_right] at hev
        omega
      obtain ⟨hadj, _⟩ := colorMate_spec (by omega : 7 ≤ 17) htc c hu_not_Ic
      have hne' := colorMate_ne_color (by omega : 7 ≤ 17) htc c hu_not_Ic
      have hadj' : (circulant13 17).Adj u (m' u) := by
        have := (shifted_adj r u (m' u)).mp (by simpa [m', sub_add_cancel] using hadj)
        exact this
      have hmev := odd_interior_neighbors_even_17 u (m' u) huo hu3 hu13 hadj'
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmev⟩, ?_⟩
      intro hmem
      obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hmem
      have : x = colorMate (by omega : 7 ≤ 17) htc c (u + r) := by
        dsimp only [m'] at hxeq; linear_combination hxeq
      rw [this] at hx
      exact hne' (Finset.mem_filter.mp hx).2
    have hinj : Set.InjOn m' (OddInt : Set (ZMod 17)) := by
      intro u₁ hu₁ u₂ hu₂ heq
      have hnot : ∀ u ∈ OddInt, cv (u + r) ≠ c := fun u hu hcv => by
        have hev := (hr (u + r) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩)).1
        rw [add_sub_cancel_right] at hev
        have := (Finset.mem_filter.mp hu).2.1
        omega
      have heq' : colorMate (by omega : 7 ≤ 17) htc c (u₁ + r) = colorMate (by omega : 7 ≤ 17) htc c (u₂ + r) := by
        dsimp only [m'] at heq; linear_combination heq
      have h1 := colorMate_invol (by omega : 7 ≤ 17) htc c (hnot u₁ hu₁)
      have h2 := colorMate_invol (by omega : 7 ≤ 17) htc c (hnot u₂ hu₂)
      have : u₁ + r = u₂ + r := by rw [← h1, heq', h2]
      linear_combination this
    have hcard_le := Finset.card_le_card_of_injOn m' (fun u hu => hmaps u hu) hinj
    have hOdd_card : OddInt.card = 6 := by decide
    have hEven_card : (Finset.univ.filter (fun u : ZMod 17 => u.val % 2 = 0)).card = 9 := by decide
    have hRem_card : EvenRem.card = 9 - Ic.card := by
      rw [Finset.card_sdiff_of_subset hS'sub, hEven_card, hS'card]
    omega
  have hsum := sum_colorClass_card cv
  have hbd : ∑ c : Fin 5, (Finset.univ.filter (fun u : ZMod 17 => cv u = c)).card ≤ ∑ _c : Fin 5, 3 :=
    Finset.sum_le_sum fun c _ => hle3 c
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hbd
  omega

/-! #### Case `n = 13` -/

private lemma odd_interior_neighbors_even_13 :
    ∀ u v : ZMod 13, u.val % 2 = 1 → 3 ≤ u.val → u.val ≤ 9 →
      (circulant13 13).Adj u v → v.val % 2 = 0 := fun u v huo hu3 hu9 hadj =>
  odd_interior_neighbors_even (by omega : 7 ≤ 13) u v huo hu3 (by omega) hadj

private lemma odd_neighbor_11_eq_1 :
    ∀ v : ZMod 13, (circulant13 13).Adj 11 v → v.val % 2 = 1 → v = 1 := by
  intro v hadj hodd
  rcases hadj.2 with h | h | h | h
  · have hv : v = 12 := by linear_combination h
    rw [hv] at hodd; exact absurd hodd (by decide)
  · have hv : v = 10 := by linear_combination -h
    rw [hv] at hodd; exact absurd hodd (by decide)
  · have h13 : (13 : ZMod 13) = 0 := by decide
    linear_combination h + h13
  · have hv : v = 8 := by linear_combination -h
    rw [hv] at hodd; exact absurd hodd (by decide)

private lemma odd_int_neighbor_12 :
    ∀ u : ZMod 13, u.val % 2 = 1 → 3 ≤ u.val → u.val ≤ 9 →
      (circulant13 13).Adj u 12 → u = 9 := by
  intro u huo _ hu9 hadj
  rcases hadj.2 with h | h | h | h
  · have hu : u = 11 := by linear_combination -h
    rw [hu] at hu9; exact absurd hu9 (by decide)
  · have h13 : (13 : ZMod 13) = 0 := by decide
    have hu : u = 0 := by linear_combination h + h13
    rw [hu] at huo; exact absurd huo (by decide)
  · linear_combination -h
  · have h13 : (13 : ZMod 13) = 0 := by decide
    have hu : u = 2 := by linear_combination h + h13
    rw [hu] at huo; exact absurd huo (by decide)

private lemma odd_int_neighbor_10 :
    ∀ u : ZMod 13, u.val % 2 = 1 → 3 ≤ u.val → u.val ≤ 9 → u ≠ 9 →
      (circulant13 13).Adj u 10 → u = 7 := by
  intro u huo _ hu9 h9 hadj
  rcases hadj.2 with h | h | h | h
  · exact absurd (by linear_combination -h) h9
  · have hu : u = 11 := by linear_combination h
    rw [hu] at hu9; exact absurd hu9 (by decide)
  · linear_combination -h
  · have h13 : (13 : ZMod 13) = 0 := by decide
    have hu : u = 0 := by linear_combination h + h13
    rw [hu] at huo; exact absurd huo (by decide)

private lemma odd_int_neighbor_8 :
    ∀ u : ZMod 13, u.val % 2 = 1 → 3 ≤ u.val → u.val ≤ 9 → u ≠ 9 → u ≠ 7 →
      (circulant13 13).Adj u 8 → u = 5 := by
  intro u _ _ hu9 h9 h7 hadj
  rcases hadj.2 with h | h | h | h
  · exact absurd (by linear_combination -h) h7
  · exact absurd (by linear_combination h) h9
  · linear_combination -h
  · have hu : u = 11 := by linear_combination h
    rw [hu] at hu9; exact absurd hu9 (by decide)

private lemma zmod13_four_triples_impossible :
    ∀ r : Fin 4 → ZMod 13,
      (∀ i j : Fin 4, i ≠ j →
        ∀ a ∈ ({7, 9, 11} : Finset (ZMod 13)),
        ∀ b ∈ ({7, 9, 11} : Finset (ZMod 13)), r i + a ≠ r j + b) →
      (∀ i j : Fin 4, i ≠ j → r i + 8 = r j →
        ∀ k : Fin 4, k ≠ i → ∀ b ∈ ({7, 9, 11} : Finset (ZMod 13)), r i + 5 ≠ r k + b) →
      False := by
  intro r hdisj hblock
  let t : Fin 4 → ZMod 13 := fun i => 7 * (r i + 7)
  let B : Fin 4 → Finset (ZMod 13) := fun i => {t i, t i + 1, t i + 2}
  have hBcard : ∀ i : Fin 4, (B i).card = 3 := fun i => by
    have h1 : t i ≠ t i + 1 := fun h => absurd (by linear_combination -h : (1 : ZMod 13) = 0) (by decide)
    have h2 : t i ≠ t i + 2 := fun h => absurd (by linear_combination -h : (2 : ZMod 13) = 0) (by decide)
    have h3 : t i + 1 ≠ t i + 2 := fun h => absurd (by linear_combination -h : (1 : ZMod 13) = 0) (by decide)
    simp [B, h1, h2, h3]
  have hBdisj : ∀ i j : Fin 4, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have h2 : ∀ z : ZMod 13, 2 * (7 * z) = z := fun z => by
      have : (2 : ZMod 13) * 7 = 1 := by decide
      calc 2 * (7 * z) = (2 * 7) * z := by ring
        _ = 1 * z := by rw [this]
        _ = z := one_mul z
    have hmem : ∀ (p : Fin 4), x ∈ B p → ∃ a ∈ ({7, 9, 11} : Finset (ZMod 13)), 2 * x = r p + a := by
      intro p hp
      simp only [B, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨7, by decide, by dsimp only [t]; rw [h2]⟩
      · refine ⟨9, by decide, ?_⟩
        dsimp only [t]; rw [mul_add, h2]; ring
      · refine ⟨11, by decide, ?_⟩
        dsimp only [t]; rw [mul_add, h2]; ring
    obtain ⟨a, ha, hxa⟩ := hmem i hxi
    obtain ⟨b, hb, hxb⟩ := hmem j hxj
    exact hdisj i j hij a ha b hb (hxa.symm.trans hxb)
  let U := Finset.univ.biUnion B
  have hUcard : U.card = 12 := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hBdisj i j hij)]
    simp [hBcard]
  have hcompl_card : (Finset.univ \ U).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card, hUcard]
  obtain ⟨u, hu_eq⟩ := Finset.card_eq_one.mp hcompl_card
  have hu_not_U : u ∉ U := by
    have : u ∈ Finset.univ \ U := by rw [hu_eq]; exact Finset.mem_singleton_self u
    exact (Finset.mem_sdiff.mp this).2
  have hcov : ∀ z : ZMod 13, z ≠ u → ∃ i : Fin 4, z ∈ B i := by
    intro z hzu
    by_contra hnot
    have hz_not_U : z ∉ U := by
      intro hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hmem
      exact hnot ⟨i, hi⟩
    have : z ∈ Finset.univ \ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz_not_U⟩
    rw [hu_eq, Finset.mem_singleton] at this
    exact hzu this
  have hno_u : ∀ i : Fin 4, u ∉ B i := fun i h => hu_not_U (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, h⟩)
  have hstart_step : ∀ (w : ZMod 13), (w ≠ u) → (∀ i : Fin 4, w - 1 ∉ B i) →
      ∃ i : Fin 4, t i = w := by
    intro w hwu hprev
    obtain ⟨i, hi⟩ := hcov w hwu
    refine ⟨i, ?_⟩
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h0 | h1 | h2
    · exact h0.symm
    · exfalso; apply hprev i
      have : w - 1 = t i := by linear_combination h1
      rw [this]; simp [B]
    · exfalso; apply hprev i
      have : w - 1 = t i + 1 := by linear_combination h2
      rw [this]; simp [B]
  obtain ⟨i₁, hi₁⟩ := hstart_step (u + 1)
    (fun h => absurd (by linear_combination h : (1 : ZMod 13) = 0) (by decide))
    (fun i => by simpa [add_sub_cancel_right] using hno_u i)
  have hB1 : B i₁ = {u + 1, u + 2, u + 3} := by
    dsimp only [B]; rw [hi₁, show u + 1 + 1 = u + 2 by ring, show u + 1 + 2 = u + 3 by ring]
  have hnot_u3 : ∀ j : Fin 4, j ≠ i₁ → u + 3 ∉ B j := fun j hj h =>
    Finset.disjoint_left.mp (hBdisj i₁ j hj.symm) (by rw [hB1]; simp) h
  obtain ⟨i₂, hi₂⟩ : ∃ i : Fin 4, t i = u + 4 := by
    obtain ⟨i₂, hi₂⟩ := hcov (u + 4) (fun h => absurd (by linear_combination h : (4 : ZMod 13) = 0) (by decide))
    have hne : i₂ ≠ i₁ := by
      intro h; subst h; rw [hB1] at hi₂
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi₂
      rcases hi₂ with h | h | h
      · exact absurd (by linear_combination h : (3 : ZMod 13) = 0) (by decide)
      · exact absurd (by linear_combination h : (2 : ZMod 13) = 0) (by decide)
      · exact absurd (by linear_combination h : (1 : ZMod 13) = 0) (by decide)
    refine ⟨i₂, ?_⟩
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hi₂
    rcases hi₂ with h0 | h1 | h2
    · exact h0.symm
    · exfalso; apply hnot_u3 i₂ hne
      have : u + 3 = t i₂ := by linear_combination h1
      rw [this]; simp [B]
    · exfalso; apply hnot_u3 i₂ hne
      have : u + 3 = t i₂ + 1 := by linear_combination h2
      rw [this]; simp [B]
  have hB2 : B i₂ = {u + 4, u + 5, u + 6} := by
    dsimp only [B]; rw [hi₂, show u + 4 + 1 = u + 5 by ring, show u + 4 + 2 = u + 6 by ring]
  have hnot_u6 : ∀ j : Fin 4, j ≠ i₂ → u + 6 ∉ B j := fun j hj h =>
    Finset.disjoint_left.mp (hBdisj i₂ j hj.symm) (by rw [hB2]; simp) h
  obtain ⟨i₃, hi₃⟩ : ∃ i : Fin 4, t i = u + 7 := by
    obtain ⟨i₃, hi₃⟩ := hcov (u + 7) (fun h => absurd (by linear_combination h : (7 : ZMod 13) = 0) (by decide))
    have hne : i₃ ≠ i₂ := by
      intro h; subst h; rw [hB2] at hi₃
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi₃
      rcases hi₃ with h | h | h
      · exact absurd (by linear_combination h : (3 : ZMod 13) = 0) (by decide)
      · exact absurd (by linear_combination h : (2 : ZMod 13) = 0) (by decide)
      · exact absurd (by linear_combination h : (1 : ZMod 13) = 0) (by decide)
    refine ⟨i₃, ?_⟩
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hi₃
    rcases hi₃ with h0 | h1 | h2
    · exact h0.symm
    · exfalso; apply hnot_u6 i₃ hne
      have : u + 6 = t i₃ := by linear_combination h1
      rw [this]; simp [B]
    · exfalso; apply hnot_u6 i₃ hne
      have : u + 6 = t i₃ + 1 := by linear_combination h2
      rw [this]; simp [B]
  have hB3 : B i₃ = {u + 7, u + 8, u + 9} := by
    dsimp only [B]; rw [hi₃, show u + 7 + 1 = u + 8 by ring, show u + 7 + 2 = u + 9 by ring]
  have hnot_u9 : ∀ j : Fin 4, j ≠ i₃ → u + 9 ∉ B j := fun j hj h =>
    Finset.disjoint_left.mp (hBdisj i₃ j hj.symm) (by rw [hB3]; simp) h
  obtain ⟨i₄, hi₄⟩ : ∃ i : Fin 4, t i = u + 10 := by
    obtain ⟨i₄, hi₄⟩ := hcov (u + 10) (fun h => absurd (by linear_combination h : (10 : ZMod 13) = 0) (by decide))
    have hne : i₄ ≠ i₃ := by
      intro h; subst h; rw [hB3] at hi₄
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi₄
      rcases hi₄ with h | h | h
      · exact absurd (by linear_combination h : (3 : ZMod 13) = 0) (by decide)
      · exact absurd (by linear_combination h : (2 : ZMod 13) = 0) (by decide)
      · exact absurd (by linear_combination h : (1 : ZMod 13) = 0) (by decide)
    refine ⟨i₄, ?_⟩
    simp only [B, Finset.mem_insert, Finset.mem_singleton] at hi₄
    rcases hi₄ with h0 | h1 | h2
    · exact h0.symm
    · exfalso; apply hnot_u9 i₄ hne
      have : u + 9 = t i₄ := by linear_combination h1
      rw [this]; simp [B]
    · exfalso; apply hnot_u9 i₄ hne
      have : u + 9 = t i₄ + 1 := by linear_combination h2
      rw [this]; simp [B]
  have hr_of_t : ∀ i : Fin 4, r i = 2 * t i - 7 := fun i => by
    dsimp only [t]
    have : (2 : ZMod 13) * 7 = 1 := by decide
    calc r i = 1 * (r i + 7) - 7 := by ring
      _ = (2 * 7) * (r i + 7) - 7 := by rw [this]
      _ = 2 * (7 * (r i + 7)) - 7 := by ring
  have h14_ne : i₄ ≠ i₁ := by
    intro h; rw [h, hi₁] at hi₄
    exact absurd (by linear_combination -hi₄ : (9 : ZMod 13) = 0) (by decide)
  have h34_ne : i₃ ≠ i₄ := by
    intro h; rw [h, hi₄] at hi₃
    exact absurd (by linear_combination hi₃ : (3 : ZMod 13) = 0) (by decide)
  have hr4_8 : r i₄ + 8 = r i₁ := by
    rw [hr_of_t i₄, hr_of_t i₁, hi₄, hi₁]
    have h13 : (13 : ZMod 13) = 0 := by decide
    linear_combination 2 * h13
  have hr4_5 : r i₄ + 5 = r i₃ + 11 := by
    rw [hr_of_t i₄, hr_of_t i₃, hi₄, hi₃]
    ring
  exact hblock i₄ i₁ h14_ne hr4_8 i₃ h34_ne 11 (by decide) hr4_5

private lemma no_5tc_13 : ¬ HasTotalColoring (circulant13 13) 5 := by
  rintro ⟨cv, ce, htc⟩
  have hle3 : ∀ c : Fin 5, (Finset.univ.filter (fun u : ZMod 13 => cv u = c)).card ≤ 3 := by
    intro c
    set Ic := Finset.univ.filter (fun u : ZMod 13 => cv u = c)
    have hpar : Ic.card % 2 = 1 := colorClass_parity (by omega : 7 ≤ 13) htc c
    by_contra hgt
    have h5 : 5 ≤ Ic.card := by omega
    have hindep : ∀ u ∈ Ic, ∀ v ∈ Ic, ¬ (circulant13 13).Adj u v := fun u hu v hv hadj =>
      htc.1 u v hadj ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
    obtain ⟨r, _, hr⟩ := indep_odd_shift (n := 13) (by omega) rfl Ic hindep (by omega) (by omega)
    let S' := Ic.image (· - r)
    have hS'card : S'.card = Ic.card :=
      Finset.card_image_of_injective Ic (fun a b h => by linear_combination h)
    have hS'sub : S' ⊆ Finset.univ.filter (fun u : ZMod 13 => u.val % 2 = 0) := by
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hr x hx).1⟩
    let OddInt := Finset.univ.filter (fun u : ZMod 13 => u.val % 2 = 1 ∧ 3 ≤ u.val ∧ u.val ≤ 9)
    let EvenRem := (Finset.univ.filter (fun u : ZMod 13 => u.val % 2 = 0)) \ S'
    let m' : ZMod 13 → ZMod 13 := fun u => colorMate (by omega : 7 ≤ 13) htc c (u + r) - r
    have hmaps : ∀ u ∈ OddInt, m' u ∈ EvenRem := by
      intro u hu
      have ⟨huo, hu3, hu9⟩ := (Finset.mem_filter.mp hu).2
      have hu_not : cv (u + r) ≠ c := fun hcv => by
        have hev := (hr (u + r) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩)).1
        rw [add_sub_cancel_right] at hev; omega
      obtain ⟨hadj, _⟩ := colorMate_spec (by omega : 7 ≤ 13) htc c hu_not
      have hne' := colorMate_ne_color (by omega : 7 ≤ 13) htc c hu_not
      have hadj' : (circulant13 13).Adj u (m' u) :=
        (shifted_adj r u (m' u)).mp (by simpa [m', sub_add_cancel] using hadj)
      have hmev := odd_interior_neighbors_even_13 u (m' u) huo hu3 hu9 hadj'
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmev⟩, ?_⟩
      intro hmem
      obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hmem
      have : x = colorMate (by omega : 7 ≤ 13) htc c (u + r) := by dsimp only [m'] at hxeq; linear_combination hxeq
      rw [this] at hx
      exact hne' (Finset.mem_filter.mp hx).2
    have hinj : Set.InjOn m' (OddInt : Set (ZMod 13)) := by
      intro u₁ hu₁ u₂ hu₂ heq
      have hnot : ∀ u ∈ OddInt, cv (u + r) ≠ c := fun u hu hcv => by
        have hev := (hr (u + r) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩)).1
        rw [add_sub_cancel_right] at hev; have := (Finset.mem_filter.mp hu).2.1; omega
      have heq' : colorMate (by omega : 7 ≤ 13) htc c (u₁ + r) = colorMate (by omega : 7 ≤ 13) htc c (u₂ + r) := by
        dsimp only [m'] at heq; linear_combination heq
      have h1 := colorMate_invol (by omega : 7 ≤ 13) htc c (hnot u₁ hu₁)
      have h2 := colorMate_invol (by omega : 7 ≤ 13) htc c (hnot u₂ hu₂)
      have : u₁ + r = u₂ + r := by rw [← h1, heq', h2]
      linear_combination this
    have hcard_le := Finset.card_le_card_of_injOn m' (fun u hu => hmaps u hu) hinj
    have hOdd_card : OddInt.card = 4 := by decide
    have hEven_card : (Finset.univ.filter (fun u : ZMod 13 => u.val % 2 = 0)).card = 7 := by decide
    have hRem_card : EvenRem.card = 7 - Ic.card := by
      rw [Finset.card_sdiff_of_subset hS'sub, hEven_card, hS'card]
    omega
  -- Forced `e3`-edges for every color `c` with `|I c| = 3`!
  have hforced : ∀ c : Fin 5, (Finset.univ.filter (fun u : ZMod 13 => cv u = c)).card = 3 →
      ∃ r : ZMod 13, cv r = c ∧
        (∀ a ∈ ({7, 9, 11} : Finset (ZMod 13)),
          ce ⟨s(r + a, r + a + 3), (adj_iff_mem (by omega : 7 ≤ 13) _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩ = c) ∧
        (cv (r + 8) ≠ c →
          ce ⟨s(r + 5, r + 5 + 3), (adj_iff_mem (by omega : 7 ≤ 13) _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩ = c) := by
    intro c hc3
    set Ic := Finset.univ.filter (fun u : ZMod 13 => cv u = c)
    have hindep : ∀ u ∈ Ic, ∀ v ∈ Ic, ¬ (circulant13 13).Adj u v := fun u hu v hv hadj =>
      htc.1 u v hadj ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
    obtain ⟨r, hrIc, hr⟩ := indep_odd_shift (n := 13) (by omega) rfl Ic hindep (by omega) (by omega)
    let S' := Ic.image (· - r)
    have hS'card : S'.card = 3 := by
      rw [Finset.card_image_of_injective Ic (fun a b h => by linear_combination h), hc3]
    have hS'sub : S' ⊆ Finset.univ.filter (fun u : ZMod 13 => u.val % 2 = 0) := by
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hr x hx).1⟩
    let OddInt := Finset.univ.filter (fun u : ZMod 13 => u.val % 2 = 1 ∧ 3 ≤ u.val ∧ u.val ≤ 9)
    let EvenRem := (Finset.univ.filter (fun u : ZMod 13 => u.val % 2 = 0)) \ S'
    let m' : ZMod 13 → ZMod 13 := fun u => colorMate (by omega : 7 ≤ 13) htc c (u + r) - r
    have hnot_odd : ∀ u : ZMod 13, u.val % 2 = 1 → cv (u + r) ≠ c := fun u hu hcv => by
      have hev := (hr (u + r) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv⟩)).1
      rw [add_sub_cancel_right] at hev; omega
    have hmaps : ∀ u ∈ OddInt, m' u ∈ EvenRem := by
      intro u hu
      have ⟨huo, hu3, hu9⟩ := (Finset.mem_filter.mp hu).2
      have hu_not := hnot_odd u huo
      obtain ⟨hadj, _⟩ := colorMate_spec (by omega : 7 ≤ 13) htc c hu_not
      have hne' := colorMate_ne_color (by omega : 7 ≤ 13) htc c hu_not
      have hadj' : (circulant13 13).Adj u (m' u) :=
        (shifted_adj r u (m' u)).mp (by simpa [m', sub_add_cancel] using hadj)
      have hmev := odd_interior_neighbors_even_13 u (m' u) huo hu3 hu9 hadj'
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmev⟩, ?_⟩
      intro hmem
      obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hmem
      have : x = colorMate (by omega : 7 ≤ 13) htc c (u + r) := by dsimp only [m'] at hxeq; linear_combination hxeq
      rw [this] at hx
      exact hne' (Finset.mem_filter.mp hx).2
    have hinj : Set.InjOn m' (OddInt : Set (ZMod 13)) := by
      intro u₁ hu₁ u₂ hu₂ heq
      have h1 := colorMate_invol (by omega : 7 ≤ 13) htc c (hnot_odd u₁ (Finset.mem_filter.mp hu₁).2.1)
      have h2 := colorMate_invol (by omega : 7 ≤ 13) htc c (hnot_odd u₂ (Finset.mem_filter.mp hu₂).2.1)
      have heq' : colorMate (by omega : 7 ≤ 13) htc c (u₁ + r) = colorMate (by omega : 7 ≤ 13) htc c (u₂ + r) := by
        dsimp only [m'] at heq; linear_combination heq
      have : u₁ + r = u₂ + r := by rw [← h1, heq', h2]
      linear_combination this
    have hOdd_card : OddInt.card = 4 := by decide
    have hEven_card : (Finset.univ.filter (fun u : ZMod 13 => u.val % 2 = 0)).card = 7 := by decide
    have hRem_card : EvenRem.card = 4 := by
      rw [Finset.card_sdiff_of_subset hS'sub, hEven_card, hS'card]
    have himg_eq : OddInt.image m' = EvenRem := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro y hy; obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy; exact hmaps u hu
      · rw [Finset.card_image_of_injOn hinj, hOdd_card, hRem_card]
    have hsurj : ∀ y ∈ EvenRem, ∃ u ∈ OddInt, m' u = y := fun y hy => by
      rw [← himg_eq] at hy; exact Finset.mem_image.mp hy
    have hmate_ce : ∀ u : ZMod 13, u.val % 2 = 1 → ∀ v : ZMod 13, m' u = v →
        ∀ h : (circulant13 13).Adj (r + u) (r + v), ce ⟨s(r + u, r + v), h⟩ = c := by
      intro u huo v hmv hadj_rv
      have hu_not := hnot_odd u huo
      obtain ⟨hadj, hce⟩ := colorMate_spec (by omega : 7 ≤ 13) htc c hu_not
      have hv_eq : colorMate (by omega : 7 ≤ 13) htc c (u + r) = r + v := by
        dsimp only [m'] at hmv; linear_combination hmv
      have he_eq : (⟨s(r + u, r + v), hadj_rv⟩ : (circulant13 13).edgeSet) =
          ⟨s(u + r, colorMate (by omega : 7 ≤ 13) htc c (u + r)), hadj⟩ := by
        apply Subtype.ext; dsimp only; rw [hv_eq, add_comm r u]
      rw [he_eq]; exact hce
    -- 1) `m' 11 = 1`
    have hm11 : m' 11 = 1 := by
      have h11not := hnot_odd 11 (by decide)
      obtain ⟨hadj11, _⟩ := colorMate_spec (by omega : 7 ≤ 13) htc c h11not
      have hne11 := colorMate_ne_color (by omega : 7 ≤ 13) htc c h11not
      have hadj11' : (circulant13 13).Adj 11 (m' 11) :=
        (shifted_adj r 11 (m' 11)).mp (by simpa [m', sub_add_cancel] using hadj11)
      have h11odd : (m' 11).val % 2 = 1 := by
        by_contra hev
        have hmem_rem : m' 11 ∈ EvenRem := by
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, ?_⟩
          intro hm
          obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hm
          have : x = colorMate (by omega : 7 ≤ 13) htc c (11 + r) := by dsimp only [m'] at hxeq; linear_combination hxeq
          rw [this] at hx; exact hne11 (Finset.mem_filter.mp hx).2
        obtain ⟨u, hu, hmu⟩ := hsurj (m' 11) hmem_rem
        have heq' : colorMate (by omega : 7 ≤ 13) htc c (u + r) = colorMate (by omega : 7 ≤ 13) htc c (11 + r) := by
          dsimp only [m'] at hmu; linear_combination hmu
        have h1 := colorMate_invol (by omega : 7 ≤ 13) htc c (hnot_odd u (Finset.mem_filter.mp hu).2.1)
        have h2 := colorMate_invol (by omega : 7 ≤ 13) htc c h11not
        have hu11 : u = 11 := by
          have : u + r = 11 + r := by rw [← h1, heq', h2]
          linear_combination this
        have hu9 := (Finset.mem_filter.mp hu).2.2.2
        rw [hu11] at hu9
        exact absurd hu9 (by decide)
      exact odd_neighbor_11_eq_1 (m' 11) hadj11' h11odd
    -- 2) `m' 9 = 12`
    have h12_rem : (12 : ZMod 13) ∈ EvenRem := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩, ?_⟩
      intro hm; obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hm
      have hle8 := (hr x hx).2
      rw [hxeq] at hle8
      exact absurd hle8 (by decide)
    have hm9 : m' 9 = 12 := by
      obtain ⟨u, hu, hmu⟩ := hsurj 12 h12_rem
      have ⟨huo, hu3, hu9⟩ := (Finset.mem_filter.mp hu).2
      obtain ⟨hadj, _⟩ := colorMate_spec (by omega : 7 ≤ 13) htc c (hnot_odd u huo)
      have hadj' : (circulant13 13).Adj u 12 := by
        rw [← hmu]
        exact (shifted_adj r u (m' u)).mp (by simpa [m', sub_add_cancel] using hadj)
      have hu_eq := odd_int_neighbor_12 u huo hu3 hu9 hadj'
      rw [← hu_eq]; exact hmu
    -- 3) `m' 7 = 10`
    have h10_rem : (10 : ZMod 13) ∈ EvenRem := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩, ?_⟩
      intro hm; obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hm
      have hle8 := (hr x hx).2
      rw [hxeq] at hle8
      exact absurd hle8 (by decide)
    have hm7 : m' 7 = 10 := by
      obtain ⟨u, hu, hmu⟩ := hsurj 10 h10_rem
      have ⟨huo, hu3, hu9⟩ := (Finset.mem_filter.mp hu).2
      have hne9 : u ≠ 9 := fun h => by rw [h, hm9] at hmu; exact absurd hmu (by decide)
      obtain ⟨hadj, _⟩ := colorMate_spec (by omega : 7 ≤ 13) htc c (hnot_odd u huo)
      have hadj' : (circulant13 13).Adj u 10 := by
        rw [← hmu]
        exact (shifted_adj r u (m' u)).mp (by simpa [m', sub_add_cancel] using hadj)
      have hu_eq := odd_int_neighbor_10 u huo hu3 hu9 hne9 hadj'
      rw [← hu_eq]; exact hmu
    -- 4) If `cv (r + 8) ≠ c`, then `m' 5 = 8`!
    refine ⟨r, (Finset.mem_filter.mp hrIc).2, ?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · simpa only [show r + 7 + 3 = r + 10 by ring] using hmate_ce 7 (by decide) 10 hm7 _
      · simpa only [show r + 9 + 3 = r + 12 by ring] using hmate_ce 9 (by decide) 12 hm9 _
      · have h11_3 : (11 : ZMod 13) + 3 = 1 := by decide
        have heq : r + 11 + 3 = r + 1 := by rw [add_assoc, h11_3]
        simpa only [heq] using hmate_ce 11 (by decide) 1 hm11 _
    · intro h8not
      have h8_rem : (8 : ZMod 13) ∈ EvenRem := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide⟩, ?_⟩
        intro hm; obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hm
        have : x = r + 8 := by linear_combination hxeq
        rw [this] at hx
        exact h8not (Finset.mem_filter.mp hx).2
      have hm5 : m' 5 = 8 := by
        obtain ⟨u, hu, hmu⟩ := hsurj 8 h8_rem
        have ⟨huo, hu3, hu9⟩ := (Finset.mem_filter.mp hu).2
        have hne9 : u ≠ 9 := fun h => by rw [h, hm9] at hmu; exact absurd hmu (by decide)
        have hne7 : u ≠ 7 := fun h => by rw [h, hm7] at hmu; exact absurd hmu (by decide)
        obtain ⟨hadj, _⟩ := colorMate_spec (by omega : 7 ≤ 13) htc c (hnot_odd u huo)
        have hadj' : (circulant13 13).Adj u 8 := by
          rw [← hmu]
          exact (shifted_adj r u (m' u)).mp (by simpa [m', sub_add_cancel] using hadj)
        have hu_eq := odd_int_neighbor_8 u huo hu3 hu9 hne9 hne7 hadj'
        rw [← hu_eq]; exact hmu
      simpa only [show r + 5 + 3 = r + 8 by ring] using hmate_ce 5 (by decide) 8 hm5 _
  -- Since `∑ |I c| = 13` and each `|I c| ∈ {1, 3}`, exactly 4 colors have `|I c| = 3`!
  let Big := Finset.univ.filter (fun c : Fin 5 => (Finset.univ.filter (fun u : ZMod 13 => cv u = c)).card = 3)
  have hBig_ge4 : 4 ≤ Big.card := by
    have hsum := sum_colorClass_card cv
    have hsplit : ∑ c : Fin 5, (Finset.univ.filter (fun u : ZMod 13 => cv u = c)).card =
        ∑ c ∈ Big, (Finset.univ.filter (fun u : ZMod 13 => cv u = c)).card +
        ∑ c ∈ Finset.univ \ Big, (Finset.univ.filter (fun u : ZMod 13 => cv u = c)).card := by
      rw [← Finset.sum_sdiff (Finset.subset_univ Big), add_comm]
    have h1 : ∑ c ∈ Big, (Finset.univ.filter (fun u : ZMod 13 => cv u = c)).card = 3 * Big.card := by
      rw [Finset.sum_congr rfl fun c hc => (Finset.mem_filter.mp hc).2]
      simp only [Finset.sum_const, smul_eq_mul]; ring
    have h2 : ∑ c ∈ Finset.univ \ Big, (Finset.univ.filter (fun u : ZMod 13 => cv u = c)).card ≤
        (Finset.univ \ Big).card := by
      calc _ ≤ ∑ _c ∈ Finset.univ \ Big, 1 := Finset.sum_le_sum fun c hc => by
            have hle := hle3 c
            have hpar := colorClass_parity (by omega : 7 ≤ 13) htc c
            have hne3 : (Finset.univ.filter (fun u : ZMod 13 => cv u = c)).card ≠ 3 := by
              intro h; exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
            omega
        _ = _ := by simp
    have h3 : (Finset.univ \ Big).card = 5 - Big.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have h4 : Big.card ≤ 5 := by
      have := Finset.card_le_univ Big; simp at this; exact this
    omega
  obtain ⟨S4, hS4sub, hS4card⟩ := Finset.exists_subset_card_eq hBig_ge4
  have heq4 : Fintype.card S4 = 4 := by rw [Fintype.card_coe, hS4card]
  let e : Fin 4 ≃ S4 := (Fintype.equivFinOfCardEq heq4).symm
  let col : Fin 4 → Fin 5 := fun i => (e i).val
  have hcol_inj : Function.Injective col := fun i j h => e.injective (Subtype.ext h)
  have hcol3 : ∀ i : Fin 4, (Finset.univ.filter (fun u : ZMod 13 => cv u = col i)).card = 3 := fun i =>
    (Finset.mem_filter.mp (hS4sub (e i).property)).2
  choose r hr_cv hr_tri hr_five using fun i : Fin 4 => hforced (col i) (hcol3 i)
  refine zmod13_four_triples_impossible r ?_ ?_
  · intro i j hij a ha b hb heq
    have hci := hr_tri i a ha
    have hcj := hr_tri j b hb
    have hedge_eq : (⟨s(r i + a, r i + a + 3), (adj_iff_mem (by omega : 7 ≤ 13) _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩ : (circulant13 13).edgeSet) =
        ⟨s(r j + b, r j + b + 3), (adj_iff_mem (by omega : 7 ≤ 13) _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩ := by
      apply Subtype.ext; rw [heq]
    rw [hedge_eq] at hci
    exact hij (hcol_inj (hci.symm.trans hcj))
  · intro i j hij hr8 k hki b hb heq
    have h8not : cv (r i + 8) ≠ col i := by
      rw [hr8, hr_cv j]; exact fun h => hij.symm (hcol_inj h)
    have hci := hr_five i h8not
    have hck := hr_tri k b hb
    have hedge_eq : (⟨s(r i + 5, r i + 5 + 3), (adj_iff_mem (by omega : 7 ≤ 13) _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩ : (circulant13 13).edgeSet) =
        ⟨s(r k + b, r k + b + 3), (adj_iff_mem (by omega : 7 ≤ 13) _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))⟩ := by
      apply Subtype.ext; rw [heq]
    rw [hedge_eq] at hci
    exact hki (hcol_inj (hck.symm.trans hci))

/-! ### Part 6: Assemble the full theorem -/

private lemma hasTotalColoring_mono {V : Type*} {G : SimpleGraph V} {k₁ k₂ : ℕ}
    (h : HasTotalColoring G k₁) (hle : k₁ ≤ k₂) : HasTotalColoring G k₂ := by
  obtain ⟨cv, ce, hvv, hve, hee⟩ := h
  refine ⟨fun u => Fin.castLE hle (cv u), fun e => Fin.castLE hle (ce e), ?_, ?_, ?_⟩
  · intro u v huv hc; exact hvv u v huv (Fin.castLE_injective hle hc)
  · intro u e hu hc; exact hve u e hu (Fin.castLE_injective hle hc)
  · intro e₁ e₂ hne hsh hc; exact hee e₁ e₂ hne hsh (Fin.castLE_injective hle hc)

private theorem prove_main : type_of% @OMA.S_arxiv_2512_20878.main := by
  intro n hn
  dsimp only
  by_cases hex : n = 7 ∨ n = 8 ∨ n = 12 ∨ n = 13 ∨ n = 17
  · rw [if_pos hex]
    refine ⟨?_, ?_⟩
    · rcases hex with rfl | rfl | rfl | rfl | rfl
      · exact six_tc_7
      · exact six_tc_8
      · exact six_tc_12
      · exact six_tc_13
      · exact six_tc_17
    · intro k hk hcol
      have h5 : HasTotalColoring (circulant13 n) 5 := hasTotalColoring_mono hcol (by omega)
      rcases hex with rfl | rfl | rfl | rfl | rfl
      · exact no_5tc_7 h5
      · exact no_5tc_8 h5
      · exact no_5tc_12 h5
      · exact no_5tc_13 h5
      · exact no_5tc_17 h5
  · rw [if_neg hex]
    exact ⟨five_tc_general hn hex, fun k hk => not_hasTotalColoring_of_lt_five hn hk⟩

end OMA.P_arxiv_2512_20878

theorem OMA.solution : type_of% @OMA.S_arxiv_2512_20878.main :=
  OMA.P_arxiv_2512_20878.prove_main
