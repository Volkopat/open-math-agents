import OMAStatements.S_arxiv_1812_11360
import Mathlib

namespace OddPrism

open SimpleGraph

abbrev V (n : ℕ) := Fin (2 * n + 1) × Fin 2

abbrev graph (n : ℕ) : SimpleGraph (V n) := cycleGraph (2 * n + 1) □ ⊤

def top {n : ℕ} (i : Fin (2 * n + 1)) : Sym2 (V n) := s((i, 0), (i + 1, 0))

def bottom {n : ℕ} (i : Fin (2 * n + 1)) : Sym2 (V n) := s((i, 1), (i + 1, 1))

def rung {n : ℕ} (i : Fin (2 * n + 1)) : Sym2 (V n) := s((i, 0), (i, 1))

private theorem cycle_adj_iff {N : ℕ} [NeZero N] (h : 2 ≤ N) {i j : Fin N} :
    (cycleGraph N).Adj i j ↔ j = i + 1 ∨ i = j + 1 := by
  cases N with
  | zero => omega
  | succ N =>
    cases N with
    | zero => omega
    | succ N =>
      rw [cycleGraph_adj, sub_eq_iff_eq_add', sub_eq_iff_eq_add', or_comm]

theorem top_mem {n : ℕ} (hn : 1 ≤ n) (i : Fin (2 * n + 1)) : top i ∈ (graph n).edgeSet := by
  rw [top, mem_edgeSet, boxProd_adj_left]
  exact (cycle_adj_iff (by omega)).mpr (Or.inl rfl)

theorem bottom_mem {n : ℕ} (hn : 1 ≤ n) (i : Fin (2 * n + 1)) : bottom i ∈ (graph n).edgeSet := by
  rw [bottom, mem_edgeSet, boxProd_adj_left]
  exact (cycle_adj_iff (by omega)).mpr (Or.inl rfl)

theorem rung_mem {n : ℕ} (i : Fin (2 * n + 1)) : rung i ∈ (graph n).edgeSet := by
  rw [rung, mem_edgeSet, boxProd_adj_right]
  decide

theorem edge_cases {n : ℕ} (hn : 1 ≤ n) : ∀ e ∈ (graph n).edgeSet,
    ∃ i : Fin (2 * n + 1), e = top i ∨ e = bottom i ∨ e = rung i := by
  rw [Sym2.forall]
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  have hadj : (graph n).Adj (i,a) (j,b) := he
  rcases boxProd_adj.mp hadj with ⟨hij, hab⟩ | ⟨hab, hij⟩
  · change a = b at hab
    subst b
    rcases (cycle_adj_iff (by omega : 2 ≤ 2 * n + 1)).mp hij with rfl | rfl
    · fin_cases a
      · exact ⟨i, Or.inl rfl⟩
      · exact ⟨i, Or.inr (Or.inl rfl)⟩
    · fin_cases a
      · exact ⟨j, Or.inl Sym2.eq_swap⟩
      · exact ⟨j, Or.inr (Or.inl Sym2.eq_swap)⟩
  · change i = j at hij
    subst j
    have ne : a ≠ b := by simpa using hab
    fin_cases a <;> fin_cases b
    · exact (ne rfl).elim
    · exact ⟨i, Or.inr (Or.inr rfl)⟩
    · exact ⟨i, Or.inr (Or.inr Sym2.eq_swap)⟩
    · exact (ne rfl).elim

def neg {W : Type*} (marks : Sym2 W → Bool) (x : W → Bool) (u v : W) : Bool :=
  Bool.xor (Bool.xor (marks s(u, v)) (x u)) (x v)

def switchedEdges {W : Type*} (G : SimpleGraph W) (S : Set (Sym2 W)) (x : W → Bool) :
    Set (Sym2 W) :=
  {e | e ∈ G.edgeSet ∧ ∃ u v, e = s(u, v) ∧ (e ∈ S ↔ (x u = true ↔ x v = true))}

private theorem xor_true_iff (a b c : Bool) :
    (a = true ↔ (b = true ↔ c = true)) ↔ Bool.xor (Bool.xor a b) c = true := by
  cases a <;> cases b <;> cases c <;> decide

theorem mem_switchedEdges_iff {W : Type*} (G : SimpleGraph W) {S : Set (Sym2 W)}
    {marks : Sym2 W → Bool} (hmarks : ∀ e, e ∈ S ↔ marks e = true)
    (x : W → Bool) (u v : W) :
    s(u, v) ∈ switchedEdges G S x ↔ G.Adj u v ∧ neg marks x u v = true := by
  change (_ ∧ (∃ a b, s(u, v) = s(a, b) ∧ _)) ↔ _
  rw [mem_edgeSet]
  constructor
  · rintro ⟨hadj, a, b, he, hs⟩
    refine ⟨hadj, (xor_true_iff _ _ _).mp ?_⟩
    rw [← hmarks]
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hs
    · exact hs.trans Iff.comm
  · rintro ⟨hadj, hneg⟩
    refine ⟨hadj, u, v, rfl, ?_⟩
    rw [hmarks]
    exact (xor_true_iff _ _ _).mpr hneg

theorem switched_ncard_le_of_edges {W : Type*} (G : SimpleGraph W) {S : Set (Sym2 W)}
    {marks : Sym2 W → Bool} (hmarks : ∀ e, e ∈ S ↔ marks e = true) (x : W → Bool)
    (edges : Finset (Sym2 W))
    (hcover : ∀ u v, G.Adj u v → neg marks x u v = true → s(u, v) ∈ edges) :
    (switchedEdges G S x).ncard ≤ edges.card := by
  have subset : switchedEdges G S x ⊆ (edges : Set (Sym2 W)) := by
    change ∀ e, e ∈ switchedEdges G S x → e ∈ (edges : Set (Sym2 W))
    rw [Sym2.forall]
    intro u v he
    obtain ⟨hadj, hneg⟩ := (mem_switchedEdges_iff G hmarks x u v).mp he
    exact hcover u v hadj hneg
  simpa using Set.ncard_le_ncard subset edges.finite_toSet

theorem switched_ncard_le_of_prism_edges {n : ℕ} (hn : 1 ≤ n)
    {S : Set (Sym2 (V n))} {marks : Sym2 (V n) → Bool}
    (hmarks : ∀ e, e ∈ S ↔ marks e = true) (x : V n → Bool)
    (edges : Finset (Sym2 (V n)))
    (htop : ∀ i : Fin (2 * n + 1),
      neg marks x (i, 0) (i + 1, 0) = true → top i ∈ edges)
    (hbottom : ∀ i : Fin (2 * n + 1),
      neg marks x (i, 1) (i + 1, 1) = true → bottom i ∈ edges)
    (hrung : ∀ i : Fin (2 * n + 1),
      neg marks x (i, 0) (i, 1) = true → rung i ∈ edges) :
    (switchedEdges (graph n) S x).ncard ≤ edges.card := by
  apply switched_ncard_le_of_edges (graph n) hmarks x edges
  intro u v hadj hneg
  have he : s(u, v) ∈ switchedEdges (graph n) S x :=
    (mem_switchedEdges_iff (graph n) hmarks x u v).mpr ⟨hadj, hneg⟩
  have hgraph : s(u, v) ∈ (graph n).edgeSet := hadj
  obtain ⟨i, hi | hi | hi⟩ := edge_cases hn _ hgraph
  · rw [hi] at he ⊢
    exact htop i ((mem_switchedEdges_iff (graph n) hmarks x (i, 0) (i + 1, 0)).mp he).2
  · rw [hi] at he ⊢
    exact hbottom i ((mem_switchedEdges_iff (graph n) hmarks x (i, 1) (i + 1, 1)).mp he).2
  · rw [hi] at he ⊢
    exact hrung i ((mem_switchedEdges_iff (graph n) hmarks x (i, 0) (i, 1)).mp he).2

theorem switched_ncard_le_count {n : ℕ} (hn : 1 ≤ n)
    {S : Set (Sym2 (V n))} {marks : Sym2 (V n) → Bool}
    (hmarks : ∀ e, e ∈ S ↔ marks e = true) (x : V n → Bool)
    (topMark bottomMark rungMark : Fin (2 * n + 1) → Bool)
    (htop : ∀ i, topMark i = neg marks x (i, 0) (i + 1, 0))
    (hbottom : ∀ i, bottomMark i = neg marks x (i, 1) (i + 1, 1))
    (hrung : ∀ i, rungMark i = neg marks x (i, 0) (i, 1)) :
    (switchedEdges (graph n) S x).ncard ≤
      ∑ i, ((topMark i).toNat + (bottomMark i).toNat + (rungMark i).toNat) := by
  classical
  let cols (mark : Fin (2 * n + 1) → Bool) : Finset (Fin (2 * n + 1)) :=
    Finset.univ.filter fun i => mark i = true
  let edges := (cols topMark).image top ∪ (cols bottomMark).image bottom ∪
    (cols rungMark).image rung
  have memImage (mark : Fin (2 * n + 1) → Bool) (edge : Fin (2 * n + 1) → Sym2 (V n))
      (i : Fin (2 * n + 1)) (hi : mark i = true) : edge i ∈ (cols mark).image edge :=
    Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
  have countCols (mark : Fin (2 * n + 1) → Bool) : (cols mark).card = ∑ i, (mark i).toNat := by
    dsimp only [cols]
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases mark i <;> decide
  calc
    _ ≤ edges.card := by
      apply switched_ncard_le_of_prism_edges hn hmarks x edges
      · intro i hi
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (memImage topMark top i
          ((htop i).trans hi)))
      · intro i hi
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (memImage bottomMark bottom i
          ((hbottom i).trans hi)))
      · intro i hi
        exact Finset.mem_union_right _ (memImage rungMark rung i ((hrung i).trans hi))
    _ ≤ ((cols topMark).image top).card + ((cols bottomMark).image bottom).card +
        ((cols rungMark).image rung).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ (cols topMark).card + (cols bottomMark).card + (cols rungMark).card :=
      Nat.add_le_add (Nat.add_le_add Finset.card_image_le Finset.card_image_le) Finset.card_image_le
    _ = _ := by simp only [countCols, Finset.sum_add_distrib]

end OddPrism

namespace OddPrism

open scoped BigOperators

def edgeCost (face upper : Bool) : ℕ :=
  upper.toNat + (face ^^ upper).toNat

def pairCost (left right middle upperLeft upperRight : Bool) : ℕ :=
  middle.toNat + edgeCost (left ^^ middle) upperLeft + edgeCost (right ^^ middle) upperRight

def upperAt {n : ℕ} (parity : Bool) (anchor spot : Option (Fin n × Bool)) : Bool :=
  if anchor = spot then parity else false

private theorem pair_stable : ∀ (f g a b : Bool),
    (a = true → (f ^^ (f && g)) = true) →
    (b = true → (g ^^ (f && g)) = true) → pairCost f g (f && g) a b ≤ 1 := by
  decide

private theorem edge_stable : ∀ (f a : Bool), (a = true → f = true) → edgeCost f a ≤ 1 := by
  decide

private theorem paired : ∀ (f g : Bool), (f ^^ (f && g)) = false →
    (g ^^ (f && g)) = false → f = (f && g) ∧ g = (f && g) := by
  decide

private theorem pivot_cost : ∀ (a b : Bool), pairCost true true false a b = 2 := by
  decide

private theorem edge_cost_bound : ∀ (f a : Bool), edgeCost f a ≤ 2 := by
  decide

theorem chooseSwitches (n : ℕ) (hn : 1 ≤ n) (left right : Fin n → Bool) (last parity : Bool) :
    ∃ middle : Fin n → Bool, ∃ anchor : Option (Fin n × Bool),
      (∑ j, pairCost (left j) (right j) (middle j)
        (upperAt parity anchor (some (j, false))) (upperAt parity anchor (some (j, true)))) +
        edgeCost last (upperAt parity anchor none) ≤ n+1 := by
  classical
  let both (j : Fin n) := left j && right j
  let visible : Option (Fin n × Bool) → Bool
    | none => last
    | some (j, false) => left j ^^ both j
    | some (j, true) => right j ^^ both j
  by_cases existsVisible : ∃ spot, visible spot = true
  · obtain ⟨anchor, ha⟩ := existsVisible
    refine ⟨both, anchor, ?_⟩
    have available (spot) (hu : upperAt parity anchor spot = true) : visible spot = true := by
      by_cases he : anchor = spot
      · exact he ▸ ha
      · simp [upperAt, he] at hu
    have hp (j : Fin n) : pairCost (left j) (right j) (both j)
        (upperAt parity anchor (some (j, false))) (upperAt parity anchor (some (j, true))) ≤ 1 :=
      pair_stable _ _ _ _ (available (some (j, false))) (available (some (j, true)))
    have hl : edgeCost last (upperAt parity anchor none) ≤ 1 := edge_stable _ _ (available none)
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) fun j _ => hp j
    have hn' : (∑ _j : Fin n, (1 : ℕ)) = n := by simp
    rw [hn'] at hs
    omega
  · have invisible (spot) : visible spot = false := by
      cases he : visible spot
      · rfl
      · exact (existsVisible ⟨spot, he⟩).elim
    have hlast : last = false := invisible none
    have hpaired (j : Fin n) : left j = both j ∧ right j = both j :=
      paired _ _ (invisible (some (j, false))) (invisible (some (j, true)))
    by_cases existsPair : ∃ j, both j = true
    · obtain ⟨pivot, hpivot⟩ := existsPair
      let anchor : Option (Fin n × Bool) := some (pivot, false)
      let middle (j : Fin n) := if j = pivot then false else both j
      refine ⟨middle, anchor, ?_⟩
      have bound (j : Fin n) : pairCost (left j) (right j) (middle j)
          (upperAt parity anchor (some (j, false))) (upperAt parity anchor (some (j, true))) ≤
          1 + (if j = pivot then 1 else 0) := by
        by_cases hj : j = pivot
        · subst j
          rw [(hpaired pivot).1, (hpaired pivot).2, hpivot]
          simp only [middle, if_pos rfl, pivot_cost]
          decide
        · have hne : pivot ≠ j := Ne.symm hj
          simpa [middle, hj, upperAt, anchor, hne] using pair_stable (left j) (right j)
            false false (by simp) (by simp)
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) fun j _ => bound j
      have hsum : (∑ j : Fin n, (1 + if j = pivot then 1 else 0)) = n+1 := by
        rw [Finset.sum_add_distrib]
        simp
      have hzero : edgeCost last (upperAt parity anchor none) = 0 := by
        simp [edgeCost, hlast, upperAt, anchor]
      rw [hzero, Nat.add_zero]
      exact hs.trans_eq hsum
    · have middleFalse (j : Fin n) : both j = false := by
        cases he : both j
        · rfl
        · exact (existsPair ⟨j, he⟩).elim
      refine ⟨fun _ => false, none, ?_⟩
      have zero (j : Fin n) : pairCost (left j) (right j) false
          (upperAt parity none (some (j, false))) (upperAt parity none (some (j, true))) = 0 := by
        rw [(hpaired j).1, (hpaired j).2, middleFalse]
        simp [pairCost, edgeCost, upperAt]
      simp only [zero, Finset.sum_const_zero, zero_add]
      exact (edge_cost_bound _ _).trans (by omega)

end OddPrism

namespace OddPrism

def position (n : ℕ) : Option (Fin n × Bool) → Fin (2*n+1)
  | none => ⟨2*n, by omega⟩
  | some (j, b) => ⟨2*j.val+b.toNat, by
      have := j.isLt
      cases b <;> simp⟩

theorem position_injective (n : ℕ) : Function.Injective (position n) := by
  rintro (_ | ⟨i, a⟩) (_ | ⟨j, b⟩) h
  · rfl
  · have hv : 2*n = 2*j.val+b.toNat := congrArg Fin.val h
    have := j.isLt
    cases b <;> simp at hv <;> omega
  · have hv : 2*i.val+a.toNat = 2*n := congrArg Fin.val h
    have := i.isLt
    cases a <;> simp at hv <;> omega
  · have hv : 2*i.val+a.toNat = 2*j.val+b.toNat := congrArg Fin.val h
    cases a <;> cases b <;> simp at hv ⊢
    all_goals first | exact Fin.ext (by omega) | omega

theorem position_surjective (n : ℕ) : Function.Surjective (position n) := by
  intro i
  have hi := i.isLt
  by_cases h : i.val = 2*n
  · exact ⟨none, Fin.ext h.symm⟩
  let j : Fin n := ⟨i.val/2, by omega⟩
  rcases Nat.mod_two_eq_zero_or_one i.val with e | o
  · exact ⟨some (j, false), Fin.ext (by change 2*(i.val/2)+0 = i.val; omega)⟩
  · exact ⟨some (j, true), Fin.ext (by change 2*(i.val/2)+1 = i.val; omega)⟩

noncomputable def positionEquiv (n : ℕ) : Option (Fin n × Bool) ≃ Fin (2*n+1) :=
  Equiv.ofBijective (position n) ⟨position_injective n, position_surjective n⟩

private theorem oneVal {n : ℕ} (hn : 1 ≤ n) : (1 : Fin (2*n+1)).val = 1 := by
  have h : 1 < 2*n+1 := by omega
  simp [Nat.mod_eq_of_lt h]

theorem cyclicNext {n : ℕ} (hn : 1 ≤ n) (i : Fin (2*n+1)) :
    (i+1).val = if i.val < 2*n then i.val+1 else 0 := by
  rw [Fin.val_add, oneVal hn]
  split
  · exact Nat.mod_eq_of_lt (by omega)
  · have hi := i.isLt
    have eq : i.val+1 = 2*n+1 := by omega
    rw [eq, Nat.mod_self]

def middleAt {n : ℕ} (middle : Fin n → Bool) (i : Fin (2*n+1)) : Bool :=
  if h : i.val%2 = 1 ∧ i.val/2 < n then middle ⟨i.val/2, h.2⟩ else false

theorem middle_close {n : ℕ} (middle : Fin n → Bool) :
    middleAt middle (position n none) = false := by
  simp [middleAt, position]

theorem middle_close_succ {n : ℕ} (hn : 1 ≤ n) (middle : Fin n → Bool) :
    middleAt middle (position n none+1) = false := by
  have hi : (position n none : Fin (2*n+1)).val = 2*n := rfl
  have hh : (position n none+1).val = 0 := by simp [cyclicNext hn, hi]
  simp [middleAt, hh]

theorem middle_left {n : ℕ} (middle : Fin n → Bool) (j : Fin n) :
    middleAt middle (position n (some (j, false))) = false := by
  simp [middleAt, position]

theorem middle_right {n : ℕ} (middle : Fin n → Bool) (j : Fin n) :
    middleAt middle (position n (some (j, true))) = middle j := by
  have hi : (position n (some (j, true))).val = 2*j.val+1 := rfl
  have hm : (2*j.val+1)%2 = 1 := by omega
  have hd : (2*j.val+1)/2 = j.val := by omega
  simp [middleAt, hi, hm, hd, j.isLt]

theorem left_succ {n : ℕ} (hn : 1 ≤ n) (j : Fin n) :
    position n (some (j, false))+1 = position n (some (j, true)) := by
  apply Fin.ext
  rw [cyclicNext hn]
  have hi : (position n (some (j, false))).val = 2*j.val := rfl
  have hj : (position n (some (j, true))).val = 2*j.val+1 := rfl
  rw [hi, hj, if_pos (by have := j.isLt; omega)]

theorem middle_right_succ {n : ℕ} (hn : 1 ≤ n) (middle : Fin n → Bool) (j : Fin n) :
    middleAt middle (position n (some (j, true))+1) = false := by
  have hi : (position n (some (j, true))).val = 2*j.val+1 := rfl
  have hh : (position n (some (j, true))+1).val = 2*j.val+2 := by
    rw [cyclicNext hn, hi, if_pos (by have := j.isLt; omega)]
  simp [middleAt, hh]

def pathMark {n : ℕ} (top : Fin (2*n+1) → Bool) : ℕ → Bool
  | 0 => false
  | k+1 => if h : k < 2*n+1 then pathMark top k ^^ top ⟨k,h⟩ else false

def period {n : ℕ} (top : Fin (2*n+1) → Bool) : Bool :=
  top (position n none) ^^ pathMark top (2*n)

def upperGauge {n : ℕ} (top : Fin (2*n+1) → Bool) (target i : Fin (2*n+1)) : Bool :=
  pathMark top i.val ^^ (period top && decide (target.val < i.val))

private theorem compareXor (s i : ℕ) :
    (decide (s < i) ^^ decide (s < i+1)) = decide (s = i) := by
  rcases lt_trichotomy s i with lt | eq | gt
  · have hs : s < i+1 := by omega
    simp [lt, hs, ne_of_lt lt]
  · subst s
    simp
  · have hy : ¬ s < i+1 := by omega
    simp [not_lt_of_gt gt, hy, ne_of_gt gt]

private theorem combine : ∀ a u v p b c : Bool,
    ((a ^^ (u ^^ (p && b))) ^^ (v ^^ (p && c))) =
      (((a ^^ u) ^^ v) ^^ (p && (b ^^ c))) := by decide

private theorem cancel_path : ∀ a u : Bool, ((a ^^ u) ^^ (u ^^ a)) = false := by decide

theorem upperGauge_mark {n : ℕ} (hn : 1 ≤ n) (top : Fin (2*n+1) → Bool)
    (target i : Fin (2*n+1)) :
    ((top i ^^ upperGauge top target i) ^^ upperGauge top target (i+1)) =
      if target = i then period top else false := by
  rw [upperGauge, upperGauge, combine]
  have same : (target.val = i.val) ↔ target = i := Fin.val_inj
  by_cases hi : i.val < 2*n
  · have h : (i+1).val = i.val+1 := by simp [cyclicNext hn, hi]
    have hp : pathMark top (i.val+1) = (pathMark top i.val ^^ top i) := by
      simp [pathMark, i.isLt]
    rw [h, hp, cancel_path, compareXor]
    by_cases eq : target = i <;> simp [same, eq]
  · have h : (i+1).val = 0 := by simp [cyclicNext hn, hi]
    have hn' := i.isLt
    have he : i.val = 2*n := by omega
    have close : position n none = i := Fin.ext he.symm
    have hperiod : ((top i ^^ pathMark top i.val) ^^ pathMark top 0) = period top := by
      simp [period, close, he, pathMark]
    rw [h, hperiod]
    have hlt : target.val < i.val ↔ target ≠ i := by
      have ht := target.isLt
      constructor
      · exact fun lt eq => (ne_of_lt lt) (congrArg Fin.val eq)
      · intro neq
        have hne : target.val ≠ i.val := fun hh => neq (Fin.ext hh)
        omega
    by_cases eq : target = i <;> simp [hlt, eq]

end OddPrism

namespace OddPrism

open scoped BigOperators

private def faceAt {n : ℕ} (a b c : Fin (2*n+1) → Bool) (i : Fin (2*n+1)) : Bool :=
  ((a i ^^ b i) ^^ c i) ^^ c (i+1)

private def upperMark {n : ℕ} (parity : Bool) (anchor : Option (Fin n × Bool))
    (i : Fin (2*n+1)) : Bool :=
  if position n anchor = i then parity else false

private theorem upperMark_position {n : ℕ} (parity : Bool) (anchor spot : Option (Fin n × Bool)) :
    upperMark parity anchor (position n spot) = upperAt parity anchor spot := by
  simp [upperMark, upperAt, (position_injective n).eq_iff]

private def lowerMark {n : ℕ} (face : Fin (2*n+1) → Bool) (middle : Fin n → Bool)
    (parity : Bool) (anchor : Option (Fin n × Bool)) (i : Fin (2*n+1)) : Bool :=
  ((face i ^^ middleAt middle i) ^^ middleAt middle (i+1)) ^^ upperMark parity anchor i

private theorem sum_positions {n : ℕ} (f : Fin (2*n+1) → ℕ) :
    (∑ i, f i) = (∑ j : Fin n,
      (f (position n (some (j, false))) + f (position n (some (j, true))))) +
      f (position n none) := by
  have h : (∑ s : Option (Fin n × Bool), f (position n s)) = ∑ i, f i :=
    Fintype.sum_equiv (positionEquiv n) _ f (fun _ => rfl)
  rw [← h, Fintype.sum_option, Fintype.sum_prod_type]
  simp [Nat.add_comm]

private theorem total_bound {n : ℕ} (hn : 1 ≤ n)
    (face : Fin (2*n+1) → Bool) (parity : Bool) :
    ∃ middle : Fin n → Bool, ∃ anchor : Option (Fin n × Bool),
      (∑ i, ((upperMark parity anchor i).toNat +
        (lowerMark face middle parity anchor i).toNat + (middleAt middle i).toNat)) ≤ n+1 := by
  obtain ⟨middle, anchor, bound⟩ := chooseSwitches n hn
    (fun j => face (position n (some (j, false))))
    (fun j => face (position n (some (j, true))))
    (face (position n none)) parity
  refine ⟨middle, anchor, ?_⟩
  rw [sum_positions]
  have hpair (j : Fin n) :
      (upperMark parity anchor (position n (some (j, false)))).toNat +
        (lowerMark face middle parity anchor (position n (some (j, false)))).toNat +
        (middleAt middle (position n (some (j, false)))).toNat +
      ((upperMark parity anchor (position n (some (j, true)))).toNat +
        (lowerMark face middle parity anchor (position n (some (j, true)))).toNat +
        (middleAt middle (position n (some (j, true)))).toNat) =
      pairCost (face (position n (some (j, false)))) (face (position n (some (j, true)))) (middle j)
        (upperAt parity anchor (some (j, false))) (upperAt parity anchor (some (j, true))) := by
    simp only [lowerMark, left_succ hn, middle_left, middle_right, middle_right_succ hn,
      upperMark_position, pairCost, edgeCost, Bool.xor_false, Bool.toNat_false,
      Nat.add_zero]
    omega
  have hclose :
      (upperMark parity anchor (position n none)).toNat +
        (lowerMark face middle parity anchor (position n none)).toNat +
        (middleAt middle (position n none)).toNat =
      edgeCost (face (position n none)) (upperAt parity anchor none) := by
    simp [lowerMark, middle_close, middle_close_succ hn, upperMark_position, edgeCost]
  simpa only [hpair, hclose] using bound

private def assignment {n : ℕ} (a c : Fin (2*n+1) → Bool)
    (middle : Fin n → Bool) (anchor : Option (Fin n × Bool)) (v : V n) : Bool :=
  let u := upperGauge a (position n anchor) v.1
  if v.2 = 0 then u else (u ^^ c v.1) ^^ middleAt middle v.1

private theorem lower_switch :
    ∀ a b c d g h r s : Bool,
      ((b ^^ ((g ^^ c) ^^ r)) ^^ ((h ^^ d) ^^ s)) =
        ((((((a ^^ b) ^^ c) ^^ d) ^^ r) ^^ s) ^^ ((a ^^ g) ^^ h)) := by
  decide

private theorem rung_switch : ∀ c g r : Bool, ((c ^^ g) ^^ ((g ^^ c) ^^ r)) = r := by decide

theorem solution : type_of% @OMA.S_arxiv_1812_11360.main := by
  classical
  intro n hn S _hS
  let marks : Sym2 (V n) → Bool := fun e => if e ∈ S then true else false
  have hmarks (e : Sym2 (V n)) : e ∈ S ↔ marks e = true := by
    by_cases h : e ∈ S <;> simp [marks, h]
  let a (i : Fin (2*n+1)) := marks (top i)
  let b (i : Fin (2*n+1)) := marks (bottom i)
  let c (i : Fin (2*n+1)) := marks (rung i)
  obtain ⟨middle, anchor, count⟩ := total_bound hn (faceAt a b c) (period a)
  let x := assignment a c middle anchor
  have htop (i : Fin (2*n+1)) :
      neg marks x (i, 0) (i+1, 0) = upperMark (period a) anchor i := by
    simpa only [neg, x, assignment, if_true, a, top, upperMark] using
      upperGauge_mark hn a (position n anchor) i
  have hbottom (i : Fin (2*n+1)) :
      neg marks x (i, 1) (i+1, 1) = lowerMark (faceAt a b c) middle (period a) anchor i := by
    have hno : (1 : Fin 2) ≠ 0 := by decide
    simp only [neg, x, assignment, if_neg hno, lowerMark, faceAt]
    change ((b i ^^ ((upperGauge a (position n anchor) i ^^ c i) ^^ middleAt middle i)) ^^
        ((upperGauge a (position n anchor) (i+1) ^^ c (i+1)) ^^ middleAt middle (i+1))) = _
    rw [lower_switch (a i), upperGauge_mark hn, upperMark]
  have hrung (i : Fin (2*n+1)) :
      neg marks x (i, 0) (i, 1) = middleAt middle i := by
    have hno : (1 : Fin 2) ≠ 0 := by decide
    simp only [neg, x, assignment, if_true, if_neg hno]
    change ((c i ^^ upperGauge a (position n anchor) i) ^^
      ((upperGauge a (position n anchor) i ^^ c i) ^^ middleAt middle i)) = _
    exact rung_switch _ _ _
  refine ⟨{v | x v = true}, ?_⟩
  change (switchedEdges (graph n) S x).ncard ≤ n+1
  exact (switched_ncard_le_count hn hmarks x _ _ _ (fun i => (htop i).symm)
    (fun i => (hbottom i).symm) (fun i => (hrung i).symm)).trans count

end OddPrism

theorem OMA.solution : type_of% @OMA.S_arxiv_1812_11360.main :=
  OddPrism.solution