import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1_H1_R1
import Mathlib

/-! Cover connected nine-vertex graphs through two ordered neighborhoods. -/
namespace OMA.NineVertexCover

private abbrev V := Fin 9

private def ends : Fin 36 → V × V :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(3,4),(3,5),(3,6),(3,7),(3,8),(4,5),(4,6),(4,7),(4,8),(5,6),(5,7),(5,8),(6,7),(6,8),(7,8)]

private def edgeEnds (i : ℕ) : V × V := ends (Fin.ofNat 36 i)

private def ones (n : ℕ) : ℕ := (1 <<< n) - 1

private def join (width low high : ℕ) : ℕ :=
  (low &&& ones width) ||| (high <<< width)

private def plane (depth index : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun previous bits =>
      if index = previous then join (2 ^ previous) 0 (ones (2 ^ previous))
      else join (2 ^ previous) bits bits) depth

private def exactWeight : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n+1, k => if k > n+1 then 0 else
      join (2 ^ n) (exactWeight n k) (if k = 0 then 0 else exactWeight n (k-1))

private def forbidden (p q : V) : Bool :=
  (2251801971660822 : ℕ).testBit ((min p q).val * 9 + (max p q).val)

private def permOf (code : ℕ) (i : V) : V :=
  Fin.ofNat 9 ((code >>> (4*i.val)) % 16)

private structure Witness where
  absent : ℕ
  code : ℕ

private def forbiddenEdge (row : Witness) (index : ℕ) : Bool :=
  let pair := edgeEnds index
  forbidden (permOf row.code pair.1) (permOf row.code pair.2)

private def valid (fixed : ℕ) (row : Witness) : Prop :=
  Function.Injective (permOf row.code) ∧
  (∀ i : Fin 15, fixed.testBit i.val = true → forbiddenEdge row i.val = false) ∧
  (∀ i : Fin 21, forbiddenEdge row (i.val+15) = row.absent.testBit i.val)

private instance (fixed : ℕ) (row : Witness) : Decidable (valid fixed row) := by
  unfold valid
  infer_instance

private def topCount (top : ℕ) : ℕ :=
  ∑ j ∈ Finset.range 5, (top.testBit j).toNat

private def allowedLanes (absent top : ℕ) : ℕ :=
  if (absent >>> 16) &&& top = 0 then
    ((List.range 16).filter absent.testBit).foldr
      (fun i rest => (ones (2^16) ^^^ plane 16 i) &&& rest) (ones (2^16))
  else 0

private def covers (ms : List ℕ) (weight top : ℕ) : Prop :=
  let exact := if topCount top ≤ weight then exactWeight 16 (weight - topCount top) else 0
  ms.foldr (fun mask others => allowedLanes mask top ||| others) 0 &&& exact = exact

private instance (ms : List ℕ) (weight top : ℕ) : Decidable (covers ms weight top) := by
  unfold covers
  infer_instance

private abbrev Bit (m j : ℕ) := m.testBit j = true

private theorem ones_bit {n j} : Bit (ones n) j ↔ j < n := by
  simp [Bit, ones, Nat.shiftLeft_eq]

private theorem up_bit {a w j} : Bit (a <<< w) j ↔ w ≤ j ∧ Bit a (j-w) := by
  simp [Bit]

private theorem and_bit {a b j} : Bit (a &&& b) j ↔ Bit a j ∧ Bit b j := by simp [Bit]
private theorem or_bit {a b j} : Bit (a ||| b) j ↔ Bit a j ∨ Bit b j := by simp [Bit]

private theorem join_low {w l r j} (h : j < w) : Bit (join w l r) j ↔ Bit l j := by
  simp [join, or_bit, and_bit, ones_bit, up_bit, h, Nat.not_le_of_gt h]

private theorem join_high {w l r j} (h : w ≤ j) : Bit (join w l r) j ↔ Bit r (j-w) := by
  simp [join, or_bit, and_bit, ones_bit, up_bit, h, Nat.not_lt_of_ge h]

private theorem plane_step (k j : ℕ) : plane (k+1) j =
    (if j = k then join (2^k) 0 (ones (2^k)) else join (2^k) (plane k j) (plane k j)) := rfl

private theorem realizes (f : ℕ → Prop) (k : ℕ) :
    ∃ t < 2^k, ∀ j < k, Bit (plane k j) t ↔ f j := by
  induction k with
  | zero => exact ⟨0, by decide, by simp⟩
  | succ k ih =>
    obtain ⟨t, ht, H⟩ := ih
    by_cases hk : f k
    · refine ⟨2^k+t, by rw [Nat.pow_succ]; omega, ?_⟩
      intro j hj
      have ht' : 2^k ≤ 2^k+t := by omega
      by_cases hjk : j = k
      · subst j
        simpa [plane_step, ones_bit, join_high ht', hk] using ht
      · simpa [plane_step, hjk, join_high ht'] using H j (by omega)
    · refine ⟨t, by rw [Nat.pow_succ]; omega, ?_⟩
      intro j hj
      by_cases hjk : j = k
      · subst j
        rw [plane_step, if_pos rfl, join_low ht]
        simp [Bit, hk]
      · simpa [plane_step, hjk, join_low ht] using H j (by omega)

private def laneCount (n t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if Bit (plane n j) t then 1 else 0

private theorem laneCount_le (n t : ℕ) : laneCount n t ≤ n := by
  unfold laneCount
  calc
    _ ≤ ∑ _j ∈ Finset.range n, (1 : ℕ) :=
      Finset.sum_le_sum fun j _ => by split <;> omega
    _ = n := by simp

private theorem laneCount_succ_low {n t : ℕ} (ht : t < 2^n) :
    laneCount (n+1) t = laneCount n t := by
  unfold laneCount
  rw [Finset.sum_range_succ, plane_step, if_pos rfl]
  have hn : ¬ Bit (join (2^n) 0 (ones (2^n))) t := by rw [join_low ht]; simp [Bit]
  simp only [hn, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hne : j ≠ n := by have := Finset.mem_range.mp hj; omega
  simp only [plane_step, if_neg hne, join_low ht]

private theorem laneCount_succ_high {n t : ℕ} (ht : 2^n ≤ t) (hu : t < 2^(n+1)) :
    laneCount (n+1) t = laneCount n (t-2^n) + 1 := by
  have hsub : t-2^n < 2^n := by rw [Nat.pow_succ] at hu; omega
  unfold laneCount
  rw [Finset.sum_range_succ, plane_step, if_pos rfl]
  have hn : Bit (join (2^n) 0 (ones (2^n))) t := by
    rw [join_high ht, ones_bit]
    exact hsub
  rw [if_pos hn]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hne : j ≠ n := by have := Finset.mem_range.mp hj; omega
  simp only [plane_step, if_neg hne, join_high ht]

private theorem exactWeight_at {n k t : ℕ} (ht : t < 2^n) :
    Bit (exactWeight n k) t ↔ laneCount n t = k := by
  induction n generalizing k t with
  | zero =>
    have h : t = 0 := by simpa using ht
    subst t
    by_cases hk : k = 0 <;> simp [exactWeight, laneCount, Bit, hk, eq_comm]
  | succ n ih =>
    rw [exactWeight]
    by_cases hk : k > n+1
    · rw [if_pos hk]
      simp only [Bit, Nat.zero_testBit, Bool.false_eq_true, false_iff]
      have := laneCount_le (n+1) t
      omega
    · rw [if_neg hk]
      by_cases hl : t < 2^n
      · rw [join_low hl, laneCount_succ_low hl]
        exact ih hl
      · have hh : 2^n ≤ t := by omega
        have hs : t-2^n < 2^n := by rw [Nat.pow_succ] at ht; omega
        rw [join_high hh, laneCount_succ_high hh ht]
        by_cases h0 : k = 0
        · rw [if_pos h0, h0]; simp [Bit]
        · rw [if_neg h0, ih hs]
          omega

private def apart (side : ℕ) (index : ℕ) : Prop :=
  side.testBit (edgeEnds index).1.val ≠ side.testBit (edgeEnds index).2.val

private instance (side index : ℕ) : Decidable (apart side index) := by
  unfold apart
  infer_instance

private def cutValid (fixed side free : ℕ) : Prop :=
  (∃ u v : V, side.testBit u.val ≠ side.testBit v.val) ∧
  (∀ i : Fin 15, fixed.testBit i.val = true → ¬apart side i.val) ∧
  (∀ i : Fin 21, apart side (i.val+15) ↔ free.testBit i.val = true)

private instance (fixed side free : ℕ) : Decidable (cutValid fixed side free) := by
  unfold cutValid
  infer_instance

private theorem ends_onto : ∀ i j : V, i ≠ j →
    ∃ t : Fin 36, ends t = (i,j) ∨ ends t = (j,i) := by decide

private theorem cut_separates (G : SimpleGraph V) (fixed side free : ℕ)
    (valid : cutValid fixed side free)
    (known : ∀ t : Fin 15, G.Adj (edgeEnds t.val).1 (edgeEnds t.val).2 → fixed.testBit t.val = true)
    (absent : ∀ t : Fin 21, free.testBit t.val = true →
      ¬G.Adj (edgeEnds (t.val+15)).1 (edgeEnds (t.val+15)).2) : ¬G.Connected := by
  intro connected
  obtain ⟨⟨u,v,different⟩, hf, hr⟩ := valid
  have fixedSide (t : Fin 36) (h : G.Adj (ends t).1 (ends t).2) :
      side.testBit (ends t).1.val = side.testBit (ends t).2.val := by
    have ht : Fin.ofNat 36 t.val = t := by apply Fin.ext; simp
    have he : edgeEnds t.val = ends t := by simp only [edgeEnds, ht]
    have ha : G.Adj (edgeEnds t.val).1 (edgeEnds t.val).2 := by rw [he]; exact h
    by_contra hd
    have ha' : apart side t.val := by simpa only [apart, he] using hd
    by_cases small : t.val < 15
    · exact hf ⟨t.val, small⟩ (known ⟨t.val, small⟩ ha) ha'
    · let q : Fin 21 := ⟨t.val-15, by have := t.isLt; omega⟩
      have hq : q.val+15 = t.val := by dsimp [q]; omega
      exact absent q ((hr q).mp (hq ▸ ha')) (hq ▸ ha)
  have edgeConst (a b : V) (h : G.Adj a b) : side.testBit a.val = side.testBit b.val := by
    obtain ⟨t, eq | eq⟩ := ends_onto a b h.ne
    · have h' := fixedSide t (by simpa only [eq] using h)
      simpa only [eq] using h'
    · have h' := fixedSide t (by simpa only [eq] using h.symm)
      simpa only [eq] using h'.symm
  have walkConst {a b : V} (walk : G.Walk a b) : side.testBit a.val = side.testBit b.val := by
    induction walk with
    | nil => rfl
    | cons edge _ ih => exact (edgeConst _ _ edge).trans ih
  exact different (walkConst (connected.preconnected u v).some)

theorem two_pivot_component (G : SimpleGraph V)
    (known : ∀ t : Fin 15, G.Adj (edgeEnds t.val).1 (edgeEnds t.val).2 → (1 : ℕ).testBit t.val = true) :
    ¬G.Connected := by
  apply cut_separates G 1 3 0 (by decide +kernel) known
  simp

theorem isolated_vertex_seven (G : SimpleGraph V)
    (known : ∀ t : Fin 15, G.Adj (edgeEnds t.val).1 (edgeEnds t.val).2 → (7937 : ℕ).testBit t.val = true)
    (absent : ∀ t : Fin 21, (1384976 : ℕ).testBit t.val = true →
      ¬G.Adj (edgeEnds (t.val+15)).1 (edgeEnds (t.val+15)).2) : ¬G.Connected :=
  cut_separates G 7937 128 1384976 (by decide +kernel) known absent

theorem four_vertex_component (G : SimpleGraph V)
    (known : ∀ t : Fin 15, G.Adj (edgeEnds t.val).1 (edgeEnds t.val).2 → (775 : ℕ).testBit t.val = true)
    (absent : ∀ t : Fin 21, (2046 : ℕ).testBit t.val = true →
      ¬G.Adj (edgeEnds (t.val+15)).1 (edgeEnds (t.val+15)).2) : ¬G.Connected :=
  cut_separates G 775 15 2046 (by decide +kernel) known absent

private def edgeAt (t : Fin 36) : Sym2 V := s((ends t).1, (ends t).2)

private theorem edges_inj : Function.Injective edgeAt := by decide

private abbrev adjAt (G : SimpleGraph V) (i : ℕ) : Prop :=
  G.Adj (edgeEnds i).1 (edgeEnds i).2

private theorem edge_sum (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ j ∈ Finset.range 36, if adjAt G j then 1 else 0) = G.edgeFinset.card := by
  let selected := Finset.univ.filter fun t : Fin 36 => G.Adj (ends t).1 (ends t).2
  have himage : selected.image edgeAt = G.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | h i j =>
      simp only [Finset.mem_image, SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨t, ht, he⟩
        rw [← he]
        exact (Finset.mem_filter.mp ht).2
      · intro ha
        have ha' : G.Adj i j := ha
        obtain ⟨t, ht | ht⟩ := ends_onto i j ha'.ne
        · exact ⟨t, by simpa [selected, ht] using ha', by simp [edgeAt, ht]⟩
        · exact ⟨t, by simpa [selected, ht] using ha'.symm, by simp [edgeAt, ht, Sym2.eq_swap]⟩
  have hcount : (∑ t : Fin 36, if G.Adj (ends t).1 (ends t).2 then 1 else 0) =
      G.edgeFinset.card := by
    rw [Finset.sum_boole]
    change selected.card = _
    rw [← Finset.card_image_of_injective _ edges_inj, himage]
  rw [← hcount, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have h : Fin.ofNat 36 i.val = i := by apply Fin.ext; simp
  simp only [adjAt, edgeEnds, h]

private theorem sum_range_shift (a b : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range (a+b), f i) =
      (∑ i ∈ Finset.range a, f i) + ∑ i ∈ Finset.range b, f (i+a) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a+(b+1) = a+b+1 by omega, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    rw [Nat.add_comm a b, Nat.add_assoc]

private theorem list_left {L R : List V} (h : (L ++ R).Nodup) (i : ℕ)
    (hi : i < (L ++ R).length) : (L ++ R)[i] ∈ L ↔ i < L.length := by
  by_cases hL : i < L.length
  · rw [List.getElem_append_left hL]
    exact ⟨fun _ => hL, fun _ => List.getElem_mem hL⟩
  · have hR : L.length ≤ i := by omega
    rw [List.getElem_append_right hR]
    have hmem : R[i-L.length]'(by simp only [List.length_append] at hi; omega) ∈ R := List.getElem_mem _
    exact ⟨fun hm => (List.disjoint_left.mp h.disjoint hm hmem).elim,
      fun hh => (hL hh).elim⟩

private theorem nodup_filter_pair (S : Finset V) (p : V → Prop) [DecidablePred p] :
    ((S.filter p).toList ++ (S.filter (fun i => ¬p i)).toList).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, List.disjoint_left.mpr ?_⟩
  intro w hA hB
  simp only [Finset.mem_toList, Finset.mem_filter] at hA hB
  exact hB.2 hA.2

private theorem mem_filter_pair (S : Finset V) (p : V → Prop) [DecidablePred p] (i : V) :
    i ∈ (S.filter p).toList ++ (S.filter (fun i => ¬p i)).toList ↔ i ∈ S := by
  by_cases h : p i <;> simp [h]

private theorem normalize (G : SimpleGraph V) [DecidableRel G.Adj]
    (connected : G.Connected) (size : G.edgeFinset.card = 16) :
    ∃ (π : Equiv.Perm V) (d a b : ℕ), 1 ≤ d ∧ d ≤ 3 ∧ a < d ∧ b ≤ 8-d ∧ d ≤ 1+a+b ∧
      (∀ j : V, 0 < j.val → (G.Adj (π 0) (π j) ↔ j.val ≤ d)) ∧
      (∀ j : V, 2 ≤ j.val → j.val ≤ d → (G.Adj (π 1) (π j) ↔ j.val ≤ a+1)) ∧
      (∀ j : V, d < j.val → (G.Adj (π 1) (π j) ↔ j.val ≤ d+b)) := by
  have hsum : ∑ v, G.degree v = 32 := by rw [G.sum_degrees_eq_twice_card_edges, size]
  obtain ⟨v, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset V)
    (fun v => G.degree v) Finset.univ_nonempty
  have hmin' (w : V) : G.degree v ≤ G.degree w := hmin w (Finset.mem_univ _)
  let N := G.neighborFinset v
  let d := N.card
  have hpos : 1 ≤ d := connected.preconnected.degree_pos_of_nontrivial v
  have hd : d ≤ 3 := by
    by_contra! h
    have lower : (∑ _ : V, (4 : ℕ)) ≤ ∑ w, G.degree w :=
      Finset.sum_le_sum fun w _ => le_trans h (hmin' w)
    rw [hsum] at lower
    norm_num [V] at lower
  have hNv : v ∉ N := by simp [N]
  have hNlen : 0 < N.toList.length := by rw [Finset.length_toList]; exact hpos
  let u : V := N.toList[0]
  have huN : u ∈ N := Finset.mem_toList.mp (List.getElem_mem hNlen)
  have huv : u ≠ v := fun h => hNv (h ▸ huN)
  let S := N.erase u
  let T := Finset.univ \ insert v N
  let A := S.filter (G.Adj u)
  let B := S.filter (fun j => ¬G.Adj u j)
  let C := T.filter (G.Adj u)
  let D := T.filter (fun j => ¬G.Adj u j)
  let X := A.toList ++ B.toList
  let Y := C.toList ++ D.toList
  let P := [v,u] ++ X
  let L := P ++ Y
  let a := A.card
  let b := C.card
  have hS : S.card = d-1 := Finset.card_erase_of_mem huN
  have hT : T.card = 8-d := by
    dsimp [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_insert_of_notMem hNv]
    simp only [Finset.card_univ, Fintype.card_fin, V]
    change 9-(d+1) = 8-d
    omega
  have ha : a < d := by
    have h : a ≤ S.card := Finset.card_filter_le _ _
    rw [hS] at h
    omega
  have hb : b ≤ 8-d := hT ▸ Finset.card_filter_le _ _
  have hX : X.length = d-1 := by
    simpa [X, ← hS] using Finset.card_filter_add_card_filter_not (s := S) (G.Adj u)
  have hY : Y.length = 8-d := by
    simpa [Y, ← hT] using Finset.card_filter_add_card_filter_not (s := T) (G.Adj u)
  have hP : P.length = d+1 := by
    simp only [P, List.length_append, List.length_cons, List.length_nil, hX]
    omega
  have hL : L.length = 9 := by simp only [L, List.length_append, hP, hY]; omega
  have hXm (w : V) : w ∈ X ↔ w ∈ S := mem_filter_pair S (G.Adj u) w
  have hYm (w : V) : w ∈ Y ↔ w ∈ T := mem_filter_pair T (G.Adj u) w
  have hSm (w : V) : w ∈ S ↔ w ≠ u ∧ w ∈ N := Finset.mem_erase
  have hTm (w : V) : w ∈ T ↔ w ≠ v ∧ w ∉ N := by simp [T, not_or]
  have hPm (w : V) : w ∈ P ↔ w = v ∨ w ∈ N := by
    by_cases h : w = u
    · subst w; simp [P, huN]
    · simp [P, hXm, hSm, h]
  have hXn : X.Nodup := nodup_filter_pair S (G.Adj u)
  have hYn : Y.Nodup := nodup_filter_pair T (G.Adj u)
  have hPn : P.Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨by simp [huv.symm], hXn, List.disjoint_left.mpr ?_⟩
    intro w hw hx
    obtain ⟨hne,hn⟩ := (hSm w).mp ((hXm w).mp hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hNv hn
    · exact hne rfl
  have hLn : L.Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨hPn, hYn, List.disjoint_left.mpr ?_⟩
    intro w hw hy
    obtain ⟨ne,hn⟩ := (hTm w).mp ((hYm w).mp hy)
    exact ((hPm w).mp hw).elim ne hn
  have Hu : G.neighborFinset u = insert v (A ∪ C) := by
    ext w
    by_cases hv : w = v
    · subst w; simp [G.mem_neighborFinset, ((G.mem_neighborFinset v u).mp huN).symm]
    · by_cases he : w = u
      · subst w; simp [hv, A, C]
      · by_cases hn : w ∈ N
        · simp [G.mem_neighborFinset, A, C, hv, hSm, hTm, he, hn]
        · simp [G.mem_neighborFinset, A, C, hv, hSm, hTm, he, hn]
  have union : Disjoint A C := by
    apply Finset.disjoint_left.mpr
    intro w hm hn
    exact ((hTm w).mp (Finset.mem_filter.mp hn).1).2
      ((hSm w).mp (Finset.mem_filter.mp hm).1).2
  have vout : v ∉ A ∪ C := by simp [A,C,hSm,hTm,hNv]
  have huCount : G.degree u = 1+a+b := by
    rw [← G.card_neighborFinset_eq_degree, Hu, Finset.card_insert_of_notMem vout,
      Finset.card_union_of_disjoint union]
    change a+b+1 = 1+a+b
    omega
  let f (i : V) : V := L[i.val]'(by rw [hL]; exact i.isLt)
  let π : Equiv.Perm V := Equiv.ofBijective f
    (Finite.injective_iff_bijective.mp (fun _ _ h => Fin.ext (hLn.getElem_inj_iff.mp h)))
  have hπ (i : V) : π i = f i := rfl
  have h0 : π 0 = v := by
    rw [hπ]; dsimp [f,L]
    rw [List.getElem_append_left (by rw [hP]; omega)]
    rfl
  have h1 : π 1 = u := by
    rw [hπ]; dsimp [f,L]
    rw [List.getElem_append_left (by rw [hP]; omega)]
    rfl
  refine ⟨π,d,a,b,hpos,hd,ha,hb,huCount ▸ hmin' u,?_,?_,?_⟩
  · intro j hj
    have hne : π j ≠ v := fun h => by
      have eq := π.injective (h.trans h0.symm)
      have : j.val = 0 := congrArg Fin.val eq
      omega
    have hm : π j ∈ P ↔ j.val < d+1 := by
      rw [hπ]
      simpa only [hP] using list_left hLn j.val (by rw [hL]; exact j.isLt)
    have hmem : π j ∈ N ↔ j.val < d+1 := by simpa [hPm, hne] using hm
    rw [h0, ← G.mem_neighborFinset]
    change π j ∈ N ↔ j.val ≤ d
    exact hmem.trans (by omega)
  · intro j hj hjd
    have hq : j.val-2 < X.length := by rw [hX]; omega
    have hf : π j = X[j.val-2] := by
      rw [hπ]; dsimp [f,L]
      rw [List.getElem_append_left (by rw [hP]; omega)]
      exact List.getElem_append_right hj
    have hs : π j ∈ S := (hXm _).mp (hf ▸ List.getElem_mem hq)
    have hm : π j ∈ A ↔ j.val-2 < a := by
      rw [hf]
      simpa only [Finset.mem_toList, Finset.length_toList] using list_left hXn (j.val-2) hq
    rw [h1]
    have hmem : π j ∈ A ↔ G.Adj u (π j) := by simp [A, hs]
    exact hmem.symm.trans (hm.trans (by omega))
  · intro j hj
    have hj' : P.length ≤ j.val := by rw [hP]; omega
    have hq : j.val-P.length < Y.length := by rw [hY,hP]; have := j.isLt; omega
    have hf : π j = Y[j.val-P.length] := by
      rw [hπ]; dsimp [f,L]
      exact List.getElem_append_right hj'
    have hr : π j ∈ T := (hYm _).mp (hf ▸ List.getElem_mem hq)
    have hm : π j ∈ C ↔ j.val-P.length < b := by
      rw [hf]
      simpa only [Finset.mem_toList,Finset.length_toList] using list_left hYn (j.val-P.length) hq
    rw [h1]
    have hmem : π j ∈ C ↔ G.Adj u (π j) := by simp [C,hr]
    exact hmem.symm.trans (hm.trans (by rw [hP]; omega))

private theorem top_bits : ∀ (t : Fin 32) (i : Fin 5),
    Bit (plane 5 i.val) t.val ↔ t.val.testBit i.val = true := by decide

private theorem search_at {ms : List ℕ} {weight top low : ℕ}
    (covered : covers ms weight top) (hl : low < 2^16)
    (count : laneCount 16 low + topCount top = weight) :
    ∃ m ∈ ms, Bit (allowedLanes m top) low := by
  have hp : topCount top ≤ weight := by omega
  have hv : laneCount 16 low = weight-topCount top := by omega
  have hx := (exactWeight_at hl).mpr hv
  unfold covers at covered
  simp only [if_pos hp] at covered
  have hh := and_bit.mp (show Bit
    ((ms.foldr (fun mask others => allowedLanes mask top ||| others) 0) &&&
      exactWeight 16 (weight-topCount top)) low from covered.symm ▸ hx)
  clear covered hx
  induction ms with
  | nil => simp [Bit] at hh
  | cons m ms ih =>
    have h := or_bit.mp hh.1
    rcases h with h | h
    · exact ⟨m, List.mem_cons_self, h⟩
    · obtain ⟨k,hk,hp⟩ := ih ⟨h,hh.2⟩
      exact ⟨k, List.mem_cons_of_mem _ hk, hp⟩

private theorem low_forbidden {m top low i : ℕ}
    (ht : low < 2^16) (hi : i < 16) (hm : Bit m i)
    (h : Bit (allowedLanes m top) low) : ¬Bit (plane 16 i) low := by
  unfold allowedLanes at h
  split at h
  next =>
    have hmem : i ∈ (List.range 16).filter m.testBit := by simp [hi, hm]
    generalize (List.range 16).filter m.testBit = is at hmem h
    let mask (j : ℕ) := ones (2^16) ^^^ plane 16 j
    have hb : Bit (mask i) low := by
      induction is with
      | nil => simp at hmem
      | cons j is ih =>
        have hp := and_bit.mp h
        rcases List.mem_cons.mp hmem with he | he
        · subst j; exact hp.1
        · exact ih he hp.2
    have hu := ones_bit.mpr ht
    change (ones (2^16)).testBit low = true at hu
    change (ones (2^16) ^^^ plane 16 i).testBit low = true at hb
    rw [Nat.testBit_xor, hu] at hb
    intro hh
    change (plane 16 i).testBit low = true at hh
    rw [hh] at hb
    contradiction
  next => simp [Bit] at h

private theorem high_forbidden {m top low i : ℕ}
    (hm : Bit m (i+16)) (h : Bit (allowedLanes m top) low) :
    top.testBit i = false := by
  unfold allowedLanes at h
  split at h
  next hp =>
    have hb : ((m >>> 16) &&& top).testBit i = false := by simp [hp]
    have hm' : m.testBit (16+i) = true := by simpa only [Nat.add_comm i 16] using hm
    simpa only [Nat.testBit_and, Nat.testBit_shiftRight, hm', Bool.true_and] using hb
  next => simp [Bit] at h

private structure Cut where
  side : ℕ
  absent : ℕ

private structure Packet where
  degree : ℕ
  near : ℕ
  far : ℕ
  fixed : ℕ
  residual : ℕ
  rows : List Witness
  cuts : List Cut

private def masks (packet : Packet) : List ℕ :=
  packet.rows.map Witness.absent ++ packet.cuts.map Cut.absent

private def pattern (d a b : ℕ) (p : V × V) : Bool :=
  if p.1 = 0 then decide (p.2.val ≤ d)
  else if p.2.val ≤ d then decide (p.2.val ≤ a+1)
  else decide (p.2.val ≤ d+b)

private def shape (packet : Packet) : Prop :=
  (∀ t : Fin 15, packet.fixed.testBit t.val =
      pattern packet.degree packet.near packet.far (edgeEnds t.val)) ∧
    (∑ j ∈ Finset.range 15, if Bit packet.fixed j then 1 else 0) + packet.residual = 16

private instance (packet : Packet) : Decidable (shape packet) := by unfold shape; infer_instance

private def fitted (packet : Packet) : Prop :=
  shape packet ∧ (∀ w ∈ packet.rows, valid packet.fixed w) ∧
    (∀ c ∈ packet.cuts, cutValid packet.fixed c.side c.absent)

private instance (packet : Packet) : Decidable (fitted packet) := by unfold fitted; infer_instance

private theorem decode (G : SimpleGraph V) [DecidableRel G.Adj] (conn : G.Connected)
    (size : G.edgeFinset.card = 16) (packet : Packet)
    (known : ∀ t : Fin 15, adjAt G t.val ↔ Bit packet.fixed t.val)
    (validPacket : fitted packet)
    (all : ∀ top : Fin 32, covers (masks packet) packet.residual top.val) :
    ∃ m ∈ [2251801971660822], ∃ e : V ↪ V, ∀ i j, G.Adj i j →
      m.testBit ((min (e i) (e j)).val*9+(max (e i) (e j)).val) = false := by
  obtain ⟨⟨_, packetSize⟩, validRows, validCuts⟩ := validPacket
  obtain ⟨lo, hlo, hL⟩ := realizes (fun j => adjAt G (j+15)) 16
  obtain ⟨hi, hhi, hH⟩ := realizes (fun j => adjAt G (j+31)) 5
  have hHI (j : ℕ) (hj : j < 5) : hi.testBit j = true ↔ adjAt G (j+31) :=
    (top_bits ⟨hi,hhi⟩ ⟨j,hj⟩).symm.trans (hH j hj)
  have first : (∑ j ∈ Finset.range 15, if adjAt G j then 1 else 0) =
      ∑ j ∈ Finset.range 15, if Bit packet.fixed j then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [known ⟨j, Finset.mem_range.mp hj⟩]
  have middle : (∑ j ∈ Finset.range 16, if adjAt G (j+15) then 1 else 0) = laneCount 16 lo := by
    unfold laneCount
    apply Finset.sum_congr rfl
    intro j hj
    simp only [hL j (Finset.mem_range.mp hj)]
  have final : (∑ j ∈ Finset.range 5, if adjAt G (j+31) then 1 else 0) = topCount hi := by
    unfold topCount
    apply Finset.sum_congr rfl
    intro j hj
    simp only [← hHI j (Finset.mem_range.mp hj)]
    cases hi.testBit j <;> decide
  have total := edge_sum G
  change (∑ j ∈ Finset.range ((15+16)+5), if adjAt G j then 1 else 0) = _ at total
  rw [sum_range_shift, sum_range_shift 15 16, first, middle, final, size] at total
  have count : laneCount 16 lo + topCount hi = packet.residual := by omega
  obtain ⟨m, hm, hmask⟩ := search_at (all ⟨hi,hhi⟩) hlo count
  have avoiding (j : Fin 21) (h : Bit m j.val) : ¬ adjAt G (j.val+15) := by
    intro edge
    by_cases hj : j.val < 16
    · exact low_forbidden hlo hj h hmask ((hL _ hj).mpr edge)
    · let k := j.val-16
      have hk : k < 5 := by dsimp [k]; have := j.isLt; omega
      have hkle : k+16 = j.val := by dsimp [k]; omega
      have heq : j.val+15 = k+31 := by omega
      have hf := high_forbidden (i := k) (hkle.symm ▸ h) hmask
      exact Bool.false_ne_true (hf.symm.trans ((hHI k hk).mpr (heq ▸ edge)))
  simp only [masks, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨w, hw, rfl⟩ | ⟨c, hc, rfl⟩
  · obtain ⟨inj, goodFixed, goodFree⟩ := validRows w hw
    refine ⟨2251801971660822, by simp, ⟨permOf w.code, inj⟩, ?_⟩
    have onEdge (i : Fin 36) (h : G.Adj (ends i).1 (ends i).2) : forbiddenEdge w i.val = false := by
      have hi : Fin.ofNat 36 i.val = i := by apply Fin.ext; simp
      have hh : adjAt G i.val := by simpa only [adjAt, edgeEnds, hi] using h
      by_cases hlt : i.val < 15
      · exact goodFixed ⟨i.val,hlt⟩ ((known ⟨i.val,hlt⟩).mp hh)
      · let j : Fin 21 := ⟨i.val-15, by have := i.isLt; omega⟩
        have hj : j.val+15 = i.val := by dsimp [j]; omega
        rw [← hj, goodFree j]
        exact Bool.eq_false_iff.mpr (fun h' => avoiding j h' (hj ▸ hh))
    intro i j edge
    obtain ⟨t, ht | ht⟩ := ends_onto i j edge.ne
    · have hr := onEdge t (by simpa only [ht] using edge)
      have he : Fin.ofNat 36 t.val = t := by apply Fin.ext; simp
      simpa only [forbiddenEdge, forbidden, edgeEnds, he, ht, Function.Embedding.coeFn_mk] using hr
    · have hr := onEdge t (by simpa only [ht] using edge.symm)
      have he : Fin.ofNat 36 t.val = t := by apply Fin.ext; simp
      simpa only [forbiddenEdge, forbidden, edgeEnds, he, ht, Function.Embedding.coeFn_mk,
        min_comm (permOf w.code j) (permOf w.code i), max_comm (permOf w.code j) (permOf w.code i)] using hr
  · exact (cut_separates G packet.fixed c.side c.absent (validCuts c hc)
      (fun t => (known t).mp) avoiding conn).elim

private def p0 : Packet :=
  ⟨1, 0, 0, 1, 15, [
    ], [⟨3,0⟩]⟩

private def p1 : Packet :=
  ⟨1, 0, 1, 257, 14, [
    ⟨1638400,9955477296⟩,
    ⟨425984,5991860016⟩,
    ⟨25600,10276378416⟩,
    ⟨6656,35752339236⟩,
    ⟨416,23673116196⟩,
    ⟨88,35172737346⟩,
    ⟨1048582,23222841666⟩,
    ⟨524293,23726588226⟩,
    ⟨65539,35825844546⟩,
    ⟨282624,5993826096⟩,
    ⟨141312,5975148336⟩,
    ⟨34304,12975609636⟩,
    ⟨1048896,23144175396⟩,
    ⟨524336,10222073136⟩,
    ⟨65672,35250439716⟩,
    ⟨147968,5774534436⟩,
    ⟨45056,17538647856⟩,
    ⟨276,35249414466⟩,
    ⟨194,19446179376⟩,
    ⟨262184,26076542256⟩,
    ⟨136192,6529877796⟩,
    ⟨51200,5474780976⟩,
    ⟨1048593,4907820336⟩,
    ⟨524546,15056832036⟩,
    ⟨100,15150178626⟩,
    ⟨270464,34683774756⟩,
    ⟨68608,22415435556⟩,
    ⟨521,17557824816⟩,
    ⟨66112,17852421936⟩,
    ⟨262162,17742329136⟩,
    ⟨1049608,5193008676⟩,
    ⟨526464,23724230436⟩,
    ⟨131105,9799427376⟩,
    ⟨73984,34715232036⟩,
    ⟨4108,19367294256⟩,
    ⟨32912,35753756196⟩,
    ⟨16449,5510420016⟩,
    ⟨1049120,22087669296⟩,
    ⟨264448,35187459876⟩,
    ⟨16394,5477922096⟩,
    ⟨525376,9689257776⟩,
    ⟨8708,34751055396⟩,
    ⟨32802,15122592066⟩,
    ⟨4353,19368334896⟩,
    ⟨1179776,8931272496⟩,
    ⟨327684,17739314736⟩,
    ⟨655368,9749165616⟩,
    ⟨1156,5508638256⟩,
    ⟨196624,5706905136⟩,
    ⟨786944,5675444016⟩,
    ⟨10241,35282572836⟩,
    ⟨20512,22573905456⟩,
    ⟨49408,23642638116⟩,
    ⟨34880,19346581296⟩,
    ⟨12304,18547373616⟩,
    ⟨18448,14361392676⟩,
    ⟨1027,5510669616⟩,
    ⟨1310784,13162080036⟩,
    ⟨102400,17534715696⟩,
    ⟨565248,14244284196⟩,
    ⟨770,35172718116⟩,
    ⟨263424,5994194736⟩,
    ⟨528386,5411010096⟩,
    ⟨1064964,5239764516⟩,
    ⟨2088,15038050626⟩,
    ⟨139328,22420719396⟩,
    ⟨656,18657781296⟩,
    ⟨32897,19346708016⟩,
    ⟨73760,21880665636⟩,
    ⟨133122,5505381936⟩,
    ⟨540800,6498051876⟩,
    ⟨1072,10276508976⟩,
    ⟨1056776,13245642276⟩,
    ⟨1054720,23135880996⟩,
    ⟨196864,12970387236⟩,
    ⟨32788,18809910576⟩,
    ⟨4288,19350574896⟩,
    ⟨1288,5461452336⟩,
    ⟨262161,17742390576⟩,
    ⟨525056,5943875376⟩,
    ⟨82944,5777852196⟩,
    ⟨270338,17742263856⟩,
    ⟨1081856,13244040996⟩,
    ⟨131077,5505508656⟩,
    ⟨2084,26979956016⟩,
    ⟨2116,19450172976⟩,
    ⟨1057792,10008008496⟩,
    ⟨1064962,8934225456⟩,
    ⟨266272,22305338916⟩,
    ⟨98312,17534842416⟩,
    ⟨262784,17740355376⟩,
    ⟨655364,9686251056⟩,
    ⟨8202,17557517616⟩,
    ⟨262153,17490732336⟩,
    ⟨16390,5509379376⟩,
    ⟨4368,35726231076⟩,
    ⟨16480,22690272816⟩,
    ⟨1605632,8948844336⟩,
    ⟨65569,14368047426⟩,
    ⟨24584,12977272356⟩,
    ⟨33028,19366614576⟩,
    ⟨8705,17858385456⟩,
    ⟨3584,13024761636⟩,
    ⟨66050,34749089316⟩,
    ⟨4168,19418715696⟩,
    ⟨131089,22421111106⟩,
    ⟨409600,5740988196⟩,
    ⟨529408,9756350256⟩,
    ⟨2432,19349776176⟩,
    ⟨592,18663679536⟩,
    ⟨524,35752730946⟩,
    ⟨1310752,22033233456⟩,
    ⟨131232,22685357616⟩,
    ⟨2072,35170709826⟩,
    ⟨1179904,5184710436⟩,
    ⟨1118208,13237651236⟩,
    ⟨786496,12910421796⟩,
    ⟨33856,15122568996⟩,
    ⟨73856,17856292656⟩,
    ⟨542720,9687107376⟩,
    ⟨294914,35182179876⟩,
    ⟨4130,26868872496⟩,
    ⟨33056,23642703396⟩,
    ⟨82432,21881030436⟩,
    ⟨132098,6563366436⟩,
    ⟨67585,35283555876⟩,
    ⟨524321,9689326896⟩,
    ⟨2066,18925909296⟩,
    ⟨392,19412756016⟩,
    ⟨4164,36294428196⟩,
    ⟨525328,5696325156⟩,
    ⟨1183744,5184587556⟩,
    ⟨8712,34719598116⟩,
    ⟨16417,9805325616⟩,
    ⟨540688,5695895076⟩,
    ⟨3200,5508572976⟩,
    ⟨655361,6493263396⟩,
    ⟨1036,23673135426⟩,
    ⟨1310724,13159134756⟩,
    ⟨8272,18663740976⟩,
    ⟨1114368,13237774116⟩,
    ⟨24832,12977268516⟩,
    ⟨2144,23742973476⟩,
    ⟨37376,35721864996⟩,
    ⟨1065472,10007701296⟩,
    ⟨329728,17739188016⟩,
    ⟨180224,9769682736⟩,
    ⟨4354,19368580656⟩,
    ⟨4101,36326211906⟩,
    ⟨524324,9687299376⟩,
    ⟨328704,21794154276⟩,
    ⟨8736,21885027876⟩,
    ⟨168,15038112066⟩,
    ⟨74,19435492656⟩,
    ⟨65856,35758544676⟩,
    ⟨1146880,4938041136⟩,
    ⟨147584,9803228976⟩,
    ⟨1581056,9953511216⟩,
    ⟨4120,18832520496⟩,
    ⟨1050688,23222880036⟩,
    ⟨397312,22303246116⟩,
    ⟨294916,17487656496⟩,
    ⟨197120,5706901296⟩,
    ⟨1083392,23136864036⟩,
    ⟨132608,10269251376⟩,
    ⟨90112,5710710576⟩,
    ⟨70144,34715600676⟩,
    ⟨8240,26382267696⟩], []⟩

private def p2 : Packet :=
  ⟨1, 0, 2, 769, 13, [
    ⟨1638400,9955477296⟩,
    ⟨425984,5991860016⟩,
    ⟨25600,21818926896⟩,
    ⟨6656,35752339236⟩,
    ⟨416,23673116226⟩,
    ⟨88,35172737346⟩,
    ⟨1048582,23222841666⟩,
    ⟨65541,17585104176⟩,
    ⟨786434,12910425636⟩,
    ⟨147457,6563059266⟩,
    ⟨45056,17538647856⟩,
    ⟨3328,15038027586⟩,
    ⟨648,35249395266⟩,
    ⟨608,22421706306⟩,
    ⟨2096,13024784706⟩,
    ⟨4288,19350574896⟩,
    ⟨1310721,13162206786⟩,
    ⟨655364,9686251056⟩,
    ⟨98306,35166451236⟩,
    ⟨8960,17825879856⟩,
    ⟨20488,5461145136⟩,
    ⟨1168,14361761346⟩,
    ⟨557057,15049643586⟩,
    ⟨10248,35249026596⟩,
    ⟨344064,21794031396⟩,
    ⟨274,35256295746⟩,
    ⟨1179712,5234845476⟩,
    ⟨262180,14328295746⟩,
    ⟨197632,21813028656⟩,
    ⟨1097728,5190485796⟩,
    ⟨8195,17590019376⟩,
    ⟨324,36294366786⟩,
    ⟨528416,22590617136⟩,
    ⟨18560,5508327216⟩,
    ⟨34304,12975609666⟩,
    ⟨131112,9765942576⟩,
    ⟨266256,18564085296⟩,
    ⟨73856,17856292656⟩,
    ⟨1034,23680016706⟩,
    ⟨2113,19445995056⟩,
    ⟨541184,5695891236⟩,
    ⟨32788,18809910576⟩,
    ⟨4353,19368334896⟩,
    ⟨1056800,22087300656⟩,
    ⟨133122,5505381936⟩,
    ⟨525376,9689257776⟩,
    ⟨1048588,23136334146⟩,
    ⟨270400,17742260016⟩,
    ⟨66304,17818998576⟩,
    ⟨1179776,8931272496⟩,
    ⟨16390,5509379376⟩,
    ⟨524312,5943883056⟩,
    ⟨32808,26878702896⟩,
    ⟨262528,17488697136⟩,
    ⟨1048593,4907820336⟩,
    ⟨67648,17584973616⟩,
    ⟨263680,26328192816⟩,
    ⟨196624,5706905136⟩,
    ⟨4130,26868872496⟩,
    ⟨534528,22380906276⟩,
    ⟨16704,5477914416⟩,
    ⟨12292,35170383396⟩,
    ⟨32960,19346642736⟩,
    ⟨262153,17490732336⟩,
    ⟨37888,23642269476⟩,
    ⟨642,35282818626⟩,
    ⟨16417,9805325616⟩,
    ⟨1312768,13159008036⟩,
    ⟨655616,9749161776⟩,
    ⟨1118208,13237651236⟩,
    ⟨2177,19446978096⟩,
    ⟨522,35759612226⟩,
    ⟨1540,13024826946⟩,
    ⟨98560,17534838576⟩,
    ⟨147472,5774538276⟩,
    ⟨8240,26382267696⟩,
    ⟨1573120,8947001136⟩,
    ⟨524300,5409109296⟩,
    ⟨163872,22568007216⟩,
    ⟨66049,17852487216⟩,
    ⟨132097,9799423536⟩,
    ⟨1064976,10007705136⟩,
    ⟨528386,5411010096⟩,
    ⟨131084,5472023856⟩,
    ⟨786560,12907472676⟩,
    ⟨1049856,8963774256⟩,
    ⟨224,23742912066⟩,
    ⟨35328,35753322276⟩,
    ⟨65546,35758567746⟩,
    ⟨4672,18815801136⟩,
    ⟨262161,17742390576⟩,
    ⟨20484,15037724196⟩,
    ⟨143360,22286534436⟩,
    ⟨68608,22415435556⟩,
    ⟨34818,19346585136⟩,
    ⟨66816,14233900866⟩,
    ⟨24580,13024458276⟩,
    ⟨565248,14244284196⟩,
    ⟨1179904,5184710436⟩,
    ⟨660,21882155106⟩,
    ⟨1057792,22087296816⟩,
    ⟨540736,9689196336⟩,
    ⟨294928,18557204016⟩,
    ⟨33160,27970180176⟩,
    ⟨66624,14367594306⟩,
    ⟨36992,19366242096⟩,
    ⟨2068,18926892336⟩,
    ⟨1573376,9953634096⟩,
    ⟨294976,35182176036⟩,
    ⟨524324,9687299376⟩,
    ⟨196640,21813032496⟩,
    ⟨73792,17852360496⟩,
    ⟨132228,10338374736⟩,
    ⟨17504,14637208656⟩,
    ⟨8784,26716804176⟩], []⟩

private def p3 : Packet :=
  ⟨1, 0, 3, 1793, 12, [
    ⟨1581056,9953511216⟩,
    ⟨344064,21794031396⟩,
    ⟨167936,5455120176⟩,
    ⟨3584,13024761666⟩,
    ⟨416,23673116226⟩,
    ⟨88,35172737346⟩,
    ⟨131078,5505447216⟩,
    ⟨32773,19346711856⟩,
    ⟨528386,5411010096⟩,
    ⟨1310721,13162206786⟩,
    ⟨73792,17852360496⟩,
    ⟨18448,14361392706⟩,
    ⟨1160,15116736066⟩,
    ⟨552,14235951426⟩,
    ⟨1296,14235932226⟩,
    ⟨655361,6493263426⟩,
    ⟨1065024,8934221616⟩,
    ⟨294914,35182179906⟩,
    ⟨12292,35170383426⟩,
    ⟨66304,17818998576⟩,
    ⟨1116160,4904617776⟩,
    ⟨17024,22414759746⟩,
    ⟨786436,12907476516⟩,
    ⟨10272,22414456386⟩,
    ⟨65584,26375386416⟩,
    ⟨266304,17490601776⟩,
    ⟨24832,12977268546⟩,
    ⟨32960,19346642736⟩,
    ⟨1179656,5184714276⟩,
    ⟨6145,36289205826⟩,
    ⟨558080,22583732016⟩,
    ⟨1048594,4907758896⟩,
    ⟨100,15150178626⟩,
    ⟨65665,17585100336⟩,
    ⟨1282,15040058946⟩,
    ⟨2816,35170686786⟩,
    ⟨98312,17534842416⟩,
    ⟨132608,10269251376⟩,
    ⟨16396,23673073986⟩,
    ⟨262161,17742390576⟩,
    ⟨133184,5505378096⟩,
    ⟨655488,9686247216⟩,
    ⟨20481,15039813186⟩,
    ⟨1310848,13159130916⟩,
    ⟨524297,5411136816⟩,
    ⟨32816,12975632706⟩,
    ⟨270338,17742263856⟩,
    ⟨1048610,8934290736⟩,
    ⟨524308,22381359426⟩,
    ⟨172032,14228555556⟩,
    ⟨4736,35249329986⟩,
    ⟨263424,26076534576⟩,
    ⟨67586,17584977456⟩,
    ⟨13312,22288623426⟩,
    ⟨10248,35249026626⟩,
    ⟨540736,9689196336⟩,
    ⟨1048612,8932324656⟩,
    ⟨1049152,4907751216⟩,
    ⟨131112,9765942576⟩,
    ⟨400,35752711746⟩,
    ⟨1538,13026793026⟩,
    ⟨1573120,8947001136⟩,
    ⟨1168,14361761346⟩,
    ⟨51200,26862782256⟩,
    ⟨131840,22286964546⟩,
    ⟨200704,12970264356⟩,
    ⟨294928,18557204016⟩,
    ⟨24577,13026547266⟩,
    ⟨33025,19362436656⟩,
    ⟨2179,23741006946⟩,
    ⟨7168,23672743746⟩,
    ⟨4144,12977598786⟩,
    ⟨114688,22281619236⟩,
    ⟨8576,35752646466⟩,
    ⟨1048588,23136334146⟩,
    ⟨65572,26107999536⟩,
    ⟨786944,5675444016⟩,
    ⟨131201,5505504816⟩,
    ⟨196624,5706905136⟩,
    ⟨8770,26448434256⟩,
    ⟨329,27958456656⟩,
    ⟨544776,10259362896⟩,
    ⟨6528,23643490146⟩,
    ⟨16459,19418780256⟩,
    ⟨20800,18832627536⟩], []⟩

private def p4 : Packet :=
  ⟨1, 0, 4, 3841, 11, [
    ⟨1574912,5105944386⟩,
    ⟨327808,17739310896⟩,
    ⟨172032,14228555586⟩,
    ⟨20992,14235559746⟩,
    ⟨1296,14235932226⟩,
    ⟨104,15040078146⟩,
    ⟨1310724,13159134786⟩,
    ⟨540674,9689200176⟩,
    ⟨196609,13020649026⟩,
    ⟨12289,35172472386⟩,
    ⟨1538,13026793026⟩,
    ⟨2096,13024784706⟩,
    ⟨772,35170752066⟩,
    ⟨152,35170771266⟩,
    ⟨98368,35166447426⟩,
    ⟨262401,17490728496⟩,
    ⟨1049728,8932316976⟩,
    ⟨524324,9687299376⟩,
    ⟨24584,12977272386⟩,
    ⟨266242,17490605616⟩,
    ⟨528448,5411006256⟩,
    ⟨1048610,8934290736⟩,
    ⟨296960,17487529776⟩,
    ⟨3328,15038027586⟩,
    ⟨1065024,8934221616⟩,
    ⟨655488,9686247216⟩,
    ⟨131096,22286987586⟩,
    ⟨98305,35166574146⟩,
    ⟨270400,17742260016⟩,
    ⟨20484,15037724226⟩,
    ⟨163841,15033914946⟩,
    ⟨200704,12970264386⟩,
    ⟨24704,13024454466⟩,
    ⟨1540,13024826946⟩,
    ⟨1048594,4907758896⟩,
    ⟨800,22288995906⟩,
    ⟨198,23741083746⟩,
    ⟨524297,5411136816⟩,
    ⟨65576,14233923906⟩,
    ⟨1049216,4905785136⟩,
    ⟨262161,17742390576⟩,
    ⟨75778,26442167376⟩,
    ⟨32782,27952182096⟩,
    ⟨32816,12975632706⟩,
    ⟨2179,23741006946⟩,
    ⟨2117,23741022306⟩,
    ⟨13312,22288623426⟩,
    ⟨196864,12970387266⟩,
    ⟨168,15038112066⟩,
    ⟨2816,35170686786⟩,
    ⟨525376,9689257776⟩,
    ⟨12292,35170383426⟩,
    ⟨1671168,9399863061⟩,
    ⟨17474,10342306896⟩,
    ⟨262720,17742321456⟩,
    ⟨1050144,13531288656⟩,
    ⟨4544,27955115856⟩,
    ⟨16422,10339054416⟩,
    ⟨811008,12925044501⟩,
    ⟨165120,5707925346⟩,
    ⟨8273,21885042786⟩,
    ⟨98306,35166451266⟩,
    ⟨330,23646711906⟩,
    ⟨1331200,13428360981⟩,
    ⟨262424,26365870416⟩,
    ⟨20608,15037720386⟩,
    ⟨1050128,9504756816⟩,
    ⟨141318,18659570016⟩,
    ⟨655364,9686251056⟩], []⟩

private def p5 : Packet :=
  ⟨1, 0, 5, 7937, 10, [
    ⟨788480,12907349826⟩,
    ⟨200704,12970264386⟩,
    ⟨57344,12975179586⟩,
    ⟨1544,12977641026⟩,
    ⟨304,12977660226⟩,
    ⟨786560,12907472706⟩,
    ⟨196672,13020522306⟩,
    ⟨24580,13024458306⟩,
    ⟨1538,13026793026⟩,
    ⟨32816,12975632706⟩,
    ⟨4169,23646650466⟩,
    ⟨33029,23642702946⟩,
    ⟨2179,23741006946⟩,
    ⟨6528,23643490146⟩,
    ⟨330,23646711906⟩,
    ⟨4144,12977598786⟩,
    ⟨36870,23642272866⟩,
    ⟨196616,12970391106⟩,
    ⟨4355,23646635106⟩,
    ⟨3584,13024761666⟩,
    ⟨17600,10339039056⟩,
    ⟨786496,12910421826⟩,
    ⟨8896,26445166416⟩,
    ⟨2117,23741022306⟩,
    ⟨6156,23643517026⟩,
    ⟨34826,23642533986⟩,
    ⟨24577,13026547266⟩,
    ⟨35136,23642507106⟩,
    ⟨131236,10338386256⟩,
    ⟨65684,26444513616⟩,
    ⟨32905,23642718306⟩,
    ⟨524330,10226004816⟩,
    ⟨262170,26332132176⟩,
    ⟨37056,23642261346⟩,
    ⟨688384,10252470096⟩,
    ⟨267008,26365663056⟩,
    ⟨132101,5774967906⟩,
    ⟨75778,26442167376⟩,
    ⟨66053,21881095266⟩,
    ⟨149506,10336040016⟩,
    ⟨396,23643762786⟩,
    ⟨360704,26358597456⟩,
    ⟨529664,10259535696⟩,
    ⟨198,23741083746⟩,
    ⟨1671169,5105014386⟩,
    ⟨1474561,5167928946⟩,
    ⟨1574936,5105943666⟩,
    ⟨1312808,5173051506⟩,
    ⟨1185,10339430736⟩,
    ⟨544832,10225928016⟩,
    ⟨274496,26332055376⟩,
    ⟨657,26445558096⟩,
    ⟨1585156,5105813106⟩,
    ⟨1331204,5172659826⟩,
    ⟨1190144,5184448626⟩,
    ⟨1132800,5188380786⟩,
    ⟨1098304,5190469746⟩,
    ⟨1090624,5190715506⟩,
    ⟨24704,13024454466⟩,
    ⟨16419,10342187856⟩,
    ⟨8211,26448315216⟩,
    ⟨557092,5692223586⟩,
    ⟨294932,21798350946⟩,
    ⟨524329,10226189136⟩,
    ⟨333824,21793900386⟩,
    ⟨184320,5707433826⟩,
    ⟨1573634,5109007986⟩,
    ⟨270346,21802021986⟩,
    ⟨262424,26365870416⟩,
    ⟨98328,21814079586⟩,
    ⟨661504,5687773026⟩,
    ⟨1312002,5176100466⟩,
    ⟨655372,5688030306⟩,
    ⟨1114212,5239038066⟩,
    ⟨17411,5778900066⟩,
    ⟨19136,18657519456⟩,
    ⟨11456,18657458016⟩,
    ⟨131110,10336105296⟩,
    ⟨98944,26377459536⟩,
    ⟨1310824,5176123506⟩,
    ⟨307200,26361300816⟩,
    ⟨196864,12970387266⟩,
    ⟨13056,21818967906⟩,
    ⟨558208,5692196706⟩,
    ⟨1089570,5190746226⟩,
    ⟨1572952,5109015666⟩,
    ⟨1115266,5239015026⟩,
    ⟨1180290,5234837106⟩,
    ⟨1671232,5104822386⟩,
    ⟨1331201,5175793266⟩,
    ⟨1179732,5234844786⟩,
    ⟨1118244,5188780146⟩,
    ⟨720932,14296838496⟩,
    ⟨548898,14302736736⟩,
    ⟨525857,14303043936⟩,
    ⟨276480,26327877456⟩,
    ⟨297344,35738883936⟩,
    ⟨168320,23675017056⟩,
    ⟨104704,35754428256⟩], [⟨128,1384976⟩]⟩

private def p6 : Packet :=
  ⟨1, 0, 6, 16129, 9, [
    ⟨333824,21793900386⟩,
    ⟨33029,23642702946⟩,
    ⟨594,21885104226⟩,
    ⟨270346,21802021986⟩,
    ⟨73920,21880653666⟩,
    ⟨13056,21818967906⟩,
    ⟨98328,21814079586⟩,
    ⟨2179,23741006946⟩,
    ⟨295552,21798324066⟩,
    ⟨4169,23646650466⟩,
    ⟨10260,21881909346⟩,
    ⟨396,23643762786⟩,
    ⟨262417,21802467426⟩,
    ⟨36870,23642272866⟩,
    ⟨66053,21881095266⟩,
    ⟨35136,23642507106⟩,
    ⟨1573016,5106066546⟩,
    ⟨198146,5506401906⟩,
    ⟨396352,5741217906⟩,
    ⟨57392,5459116146⟩,
    ⟨18980,5775777906⟩,
    ⟨4355,23646635106⟩,
    ⟨606528,5693786226⟩,
    ⟨266258,21802283106⟩,
    ⟨1189896,5184456306⟩,
    ⟨294932,21798350946⟩,
    ⟨1119360,5188749426⟩,
    ⟨1057860,5239998066⟩,
    ⟨139425,5774917746⟩,
    ⟨575489,6496999026⟩,
    ⟨66856,5711081586⟩,
    ⟨266816,21802256226⟩,
    ⟨1671170,5104830066⟩,
    ⟨655884,5688026226⟩,
    ⟨6528,23643490146⟩,
    ⟨37056,23642261346⟩,
    ⟨262665,21802452066⟩,
    ⟨196720,5506424946⟩,
    ⟨811012,5424318066⟩,
    ⟨8707,21885027426⟩,
    ⟨1051665,5240128626⟩,
    ⟨655746,6493128306⟩,
    ⟨327692,21794157666⟩,
    ⟨10880,21881882466⟩,
    ⟨1065234,5192574066⟩,
    ⟨163944,6513057906⟩,
    ⟨20648,6515023986⟩,
    ⟨1314048,5173020786⟩,
    ⟨221185,5506094706⟩,
    ⟨660,21882155106⟩,
    ⟨198,23741083746⟩,
    ⟨661520,5687772786⟩,
    ⟨173312,5707794546⟩,
    ⟨1065544,5192566386⟩,
    ⟨278625,5746409586⟩,
    ⟨73734,21880665186⟩,
    ⟨184832,5707425906⟩,
    ⟨527402,15055798896⟩,
    ⟨136197,6529877106⟩,
    ⟨32905,23642718306⟩,
    ⟨395298,5741248626⟩,
    ⟨655760,5688018546⟩,
    ⟨1585153,5108946546⟩,
    ⟨1114404,5188903026⟩,
    ⟨34352,5459423346⟩,
    ⟨1132552,5188388466⟩,
    ⟨540996,6498043506⟩,
    ⟨68160,21880899426⟩,
    ⟨811136,5424310386⟩,
    ⟨983041,5419587186⟩,
    ⟨9512,5713047666⟩,
    ⟨33890,6532903026⟩,
    ⟨545816,14537540976⟩,
    ⟨263332,5742538866⟩,
    ⟨67602,21880926306⟩,
    ⟨541777,14571087216⟩,
    ⟨1312002,5176100466⟩,
    ⟨1575680,5105928306⟩,
    ⟨221192,5455775346⟩,
    ⟨1183764,5184586866⟩,
    ⟨565284,5692096626⟩,
    ⟨83105,14635245936⟩,
    ⟨1184384,5184571506⟩,
    ⟨1671232,5104822386⟩,
    ⟨1474562,5167744626⟩,
    ⟨1572952,5109015666⟩,
    ⟨133410,6529769586⟩,
    ⟨1595396,13980829296⟩,
    ⟨19600,5775754866⟩,
    ⟨1081889,5190991986⟩,
    ⟨1511456,13507134576⟩,
    ⟨24880,5461205106⟩,
    ⟨1082385,5190976626⟩,
    ⟨58880,5459085426⟩,
    ⟨1131586,10072822896⟩,
    ⟨658696,10793391216⟩,
    ⟨720937,10223108976⟩,
    ⟨1851404,13193479536⟩,
    ⟨1208448,8930945136⟩,
    ⟨1846272,13445187696⟩,
    ⟨1593601,14000674416⟩,
    ⟨1574403,13229237616⟩,
    ⟨1057833,10008007536⟩,
    ⟨938000,14264927856⟩,
    ⟨730240,14296684656⟩,
    ⟨1595904,9953306736⟩,
    ⟨1574956,13981090416⟩], []⟩

private def p7 : Packet :=
  ⟨1, 0, 7, 32513, 8, [
    ⟨1671232,5104822386⟩,
    ⟨409606,5740987506⟩,
    ⟨13336,21818990706⟩,
    ⟨1051169,5240143986⟩,
    ⟨328096,21794145906⟩,
    ⟨524948,21848666226⟩,
    ⟨49289,23642652786⟩,
    ⟨165122,6513034866⟩,
    ⟨661505,6493066866⟩,
    ⟨270660,34683766386⟩,
    ⟨68168,34715469426⟩,
    ⟨1065234,5192574066⟩,
    ⟨5284,6530936946⟩,
    ⟨57392,5459116146⟩,
    ⟨787970,5427758706⟩,
    ⟨1189896,5184456306⟩,
    ⟨70149,34715599986⟩,
    ⟨196720,5506424946⟩,
    ⟨1331328,5172652146⟩,
    ⟨532769,5696274546⟩,
    ⟨295956,21798346866⟩,
    ⟨164392,5707948146⟩,
    ⟨82947,5777851506⟩,
    ⟨6544,35723085426⟩,
    ⟨1048774,23220990066⟩,
    ⟨576000,5691697266⟩,
    ⟨1052745,23110828146⟩,
    ⟨221440,5455767666⟩,
    ⟨270474,34683774066⟩,
    ⟨3368,6515208306⟩,
    ⟨593954,5694062706⟩,
    ⟨393489,21800435826⟩,
    ⟨1090624,5190715506⟩,
    ⟨655436,6493135986⟩,
    ⟨305153,34682721906⟩,
    ⟨26116,5508367986⟩,
    ⟨788528,5424709746⟩,
    ⟨1115272,5188879986⟩,
    ⟨131666,21884055666⟩,
    ⟨1085446,23105406066⟩,
    ⟨278625,5746409586⟩,
    ⟨598208,21847099506⟩,
    ⟨334848,21793892466⟩,
    ⟨1573636,5106058866⟩,
    ⟨37088,23642261106⟩,
    ⟨541008,5695882866⟩,
    ⟨1671169,5105014386⟩,
    ⟨139425,5774917746⟩,
    ⟨99074,34698757746⟩,
    ⟨19600,5775754866⟩,
    ⟨144128,21816871026⟩,
    ⟨344076,21794030706⟩,
    ⟨526467,23724229746⟩,
    ⟨74758,21880661106⟩,
    ⟨184336,5707433586⟩,
    ⟨21032,5712863346⟩,
    ⟨396352,5741217906⟩,
    ⟨35152,35722102386⟩,
    ⟨1180290,5234837106⟩,
    ⟨1114404,5188903026⟩,
    ⟨811009,5427451506⟩,
    ⟨8588,35723292786⟩,
    ⟨49413,23642637426⟩,
    ⟨1310824,5176123506⟩,
    ⟨69777,34715615346⟩,
    ⟨266820,34684012146⟩,
    ⟨526405,23724245106⟩,
    ⟨133410,6529769586⟩,
    ⟨202240,5456136306⟩,
    ⟨1053713,5192942706⟩,
    ⟨305184,21797832306⟩,
    ⟨533017,26667651696⟩,
    ⟨33897,6532903536⟩,
    ⟨591890,21847375986⟩,
    ⟨1181072,10000807536⟩,
    ⟨393861,18626388336⟩,
    ⟨545154,6482515056⟩,
    ⟨295299,35485263216⟩,
    ⟨176140,18827542896⟩,
    ⟨150084,6043096176⟩,
    ⟨76546,34998539376⟩,
    ⟨1198102,14060519541⟩,
    ⟨1540136,13155861621⟩,
    ⟨1017344,12904188021⟩,
    ⟨92212,17551294581⟩], []⟩

private def p8 : Packet :=
  ⟨2, 0, 1, 515, 13, [
    ⟨1638400,9955477296⟩,
    ⟨425984,5991860016⟩,
    ⟨25600,21818926896⟩,
    ⟨6656,35752339236⟩,
    ⟨416,23673116226⟩,
    ⟨88,35172737316⟩,
    ⟨1048582,23222841636⟩,
    ⟨65541,17585104176⟩,
    ⟨786434,12910425636⟩,
    ⟨147457,6563059266⟩,
    ⟨45056,17538647856⟩,
    ⟨3328,15038027586⟩,
    ⟨648,35249395266⟩,
    ⟨608,22421706306⟩,
    ⟨2096,13024784676⟩,
    ⟨4288,19350574896⟩,
    ⟨1310721,13162206786⟩,
    ⟨655364,9686251056⟩,
    ⟨98306,35166451236⟩,
    ⟨8960,17825879856⟩,
    ⟨20488,5461145136⟩,
    ⟨1168,14361761346⟩,
    ⟨557057,15049643586⟩,
    ⟨10248,35249026596⟩,
    ⟨344064,21794031396⟩,
    ⟨274,35256295716⟩,
    ⟨1179712,5234845476⟩,
    ⟨262180,14328295716⟩,
    ⟨197632,21813028656⟩,
    ⟨1097728,5190485796⟩,
    ⟨8195,17590019376⟩,
    ⟨324,36294366786⟩,
    ⟨528416,22590617136⟩,
    ⟨18560,5508327216⟩,
    ⟨34304,12975609666⟩,
    ⟨131112,9765942576⟩,
    ⟨266256,18564085296⟩,
    ⟨73856,17856292656⟩,
    ⟨1034,23680016676⟩,
    ⟨2113,19445995056⟩,
    ⟨541184,5695891236⟩,
    ⟨32788,18809910576⟩,
    ⟨4353,19368334896⟩,
    ⟨1056800,22087300656⟩,
    ⟨133122,5505381936⟩,
    ⟨525376,9689257776⟩,
    ⟨1048588,23136334116⟩,
    ⟨270400,17742260016⟩,
    ⟨66304,17818998576⟩,
    ⟨1179776,8931272496⟩,
    ⟨16390,5509379376⟩,
    ⟨524312,5943883056⟩,
    ⟨32808,26878702896⟩,
    ⟨262528,17488697136⟩,
    ⟨1048593,4907820336⟩,
    ⟨67648,17584973616⟩,
    ⟨263680,26328192816⟩,
    ⟨196624,5706905136⟩,
    ⟨4130,26868872496⟩,
    ⟨534528,22380906276⟩,
    ⟨16704,5477914416⟩,
    ⟨12292,35170383396⟩,
    ⟨32960,19346642736⟩,
    ⟨262153,17490732336⟩,
    ⟨37888,23642269476⟩,
    ⟨642,35282818626⟩,
    ⟨16417,9805325616⟩,
    ⟨1312768,13159008036⟩,
    ⟨655616,9749161776⟩,
    ⟨1118208,13237651236⟩,
    ⟨2177,19446978096⟩,
    ⟨522,35759612196⟩,
    ⟨1540,13024826946⟩,
    ⟨98560,17534838576⟩,
    ⟨147472,5774538276⟩,
    ⟨8240,26382267696⟩,
    ⟨1573120,8947001136⟩,
    ⟨524300,5409109296⟩,
    ⟨163872,22568007216⟩,
    ⟨66049,17852487216⟩,
    ⟨132097,9799423536⟩,
    ⟨1064976,10007705136⟩,
    ⟨528386,5411010096⟩,
    ⟨131084,5472023856⟩,
    ⟨786560,12907472676⟩,
    ⟨1049856,8963774256⟩,
    ⟨224,23742912066⟩,
    ⟨35328,35753322276⟩,
    ⟨65546,35758567716⟩,
    ⟨4672,18815801136⟩,
    ⟨262161,17742390576⟩,
    ⟨20484,15037724196⟩,
    ⟨143360,22286534436⟩,
    ⟨68608,22415435556⟩,
    ⟨34818,19346585136⟩,
    ⟨66816,14233900866⟩,
    ⟨24580,13024458276⟩,
    ⟨565248,14244284196⟩,
    ⟨1179904,5184710436⟩,
    ⟨660,22414824546⟩,
    ⟨1057792,22087296816⟩,
    ⟨540736,9689196336⟩,
    ⟨294928,18557204016⟩,
    ⟨36992,19366242096⟩,
    ⟨66624,14367594306⟩,
    ⟨33920,26862966576⟩,
    ⟨2068,18926892336⟩,
    ⟨1573376,9953634096⟩,
    ⟨294976,35182176036⟩,
    ⟨196640,21813032496⟩,
    ⟨172032,14228555556⟩,
    ⟨598016,21847115556⟩,
    ⟨8209,17858389296⟩,
    ⟨525056,5943875376⟩,
    ⟨409600,5740988196⟩], []⟩

private def p9 : Packet :=
  ⟨2, 0, 2, 1539, 12, [
    ⟨1581056,9953511216⟩,
    ⟨344064,21794031396⟩,
    ⟨167936,5455120176⟩,
    ⟨3584,13024761666⟩,
    ⟨416,23673116226⟩,
    ⟨1048600,4937250096⟩,
    ⟨131078,5505447216⟩,
    ⟨524297,5411136816⟩,
    ⟨270400,17742260016⟩,
    ⟨98368,35166447426⟩,
    ⟨4116,35249352996⟩,
    ⟨18433,15149913666⟩,
    ⟨1282,15040058946⟩,
    ⟨642,35282818626⟩,
    ⟨548,14361780516⟩,
    ⟨655376,5688030756⟩,
    ⟨5248,15116670786⟩,
    ⟨1310721,13162206786⟩,
    ⟨24584,12977272386⟩,
    ⟨2088,15038050596⟩,
    ⟨66304,17818998576⟩,
    ⟨1065024,8934221616⟩,
    ⟨294928,18557204016⟩,
    ⟨557060,5408060976⟩,
    ⟨204800,5706778416⟩,
    ⟨528448,5411006256⟩,
    ⟨10496,35249022786⟩,
    ⟨132097,9799423536⟩,
    ⟨1048610,8934290736⟩,
    ⟨65553,17852491056⟩,
    ⟨262156,17488704816⟩,
    ⟨131264,5505439536⟩,
    ⟨20992,14235559746⟩,
    ⟨34818,19346585136⟩,
    ⟨786464,21781575216⟩,
    ⟨33025,19362436656⟩,
    ⟨1116160,4904617776⟩,
    ⟨1168,14361761346⟩,
    ⟨12289,35172472386⟩,
    ⟨1179904,5184710436⟩,
    ⟨540674,9689200176⟩,
    ⟨1544,12977641026⟩,
    ⟨268288,17488512816⟩,
    ⟨65572,26107999536⟩,
    ⟨32816,12975632676⟩,
    ⟨33408,18809902896⟩,
    ⟨262464,17490663216⟩,
    ⟨24580,13024458306⟩,
    ⟨65548,17551619376⟩,
    ⟨262154,17490670896⟩,
    ⟨131120,10269259056⟩,
    ⟨524672,5409101616⟩,
    ⟨1056832,4907689776⟩,
    ⟨525376,9689257776⟩,
    ⟨86016,14233470786⟩,
    ⟨33920,26862966576⟩,
    ⟨73730,17852364336⟩,
    ⟨2072,35170709796⟩,
    ⟨1049089,4907816496⟩,
    ⟨1311744,22033229616⟩,
    ⟨16396,23673073956⟩,
    ⟨770,35172718146⟩,
    ⟨180224,22567880496⟩,
    ⟨2117,23742973026⟩,
    ⟨262784,17740355376⟩,
    ⟨36928,19362309936⟩,
    ⟨66112,17852421936⟩,
    ⟨524321,9689326896⟩,
    ⟨8204,35752669476⟩,
    ⟨262162,17742329136⟩,
    ⟨65576,14233923876⟩,
    ⟨20496,14235563586⟩,
    ⟨1048960,23136311106⟩,
    ⟨1538,13026793026⟩,
    ⟨542720,9687107376⟩,
    ⟨262180,14328295716⟩,
    ⟨787456,21781571376⟩,
    ⟨172032,14228555556⟩,
    ⟨137216,5471831856⟩,
    ⟨1296,14235932226⟩,
    ⟨148608,14632097616⟩,
    ⟨4169,23680058466⟩,
    ⟨21760,5712840546⟩,
    ⟨2070,26979955536⟩,
    ⟨1310728,4920473136⟩,
    ⟨2147,19450172256⟩,
    ⟨76288,26711508816⟩], []⟩

private def p10 : Packet :=
  ⟨2, 0, 3, 3587, 11, [
    ⟨1574912,5105944386⟩,
    ⟨327808,17739310896⟩,
    ⟨172032,14228555586⟩,
    ⟨20992,14235559746⟩,
    ⟨1296,14235932226⟩,
    ⟨1048612,8932324656⟩,
    ⟨524298,5411075376⟩,
    ⟨262153,17490732336⟩,
    ⟨196672,13020522306⟩,
    ⟨24577,13026547266⟩,
    ⟨3584,13024761666⟩,
    ⟨32816,12975632676⟩,
    ⟨12292,35170383426⟩,
    ⟨770,35172718146⟩,
    ⟨786496,12910421826⟩,
    ⟨1049728,8932316976⟩,
    ⟨98305,35166574146⟩,
    ⟨16408,22288953636⟩,
    ⟨266242,17490605616⟩,
    ⟨524672,5409101616⟩,
    ⟨8232,14235889956⟩,
    ⟨655364,9686251056⟩,
    ⟨1181696,8931149616⟩,
    ⟨1049152,4907751216⟩,
    ⟨294916,17487656496⟩,
    ⟨20608,15037720386⟩,
    ⟨524321,9689326896⟩,
    ⟨3328,15038027586⟩,
    ⟨1048594,4907758896⟩,
    ⟨198,23742911586⟩,
    ⟨114688,22281619266⟩,
    ⟨131840,22286964546⟩,
    ⟨4144,12977598756⟩,
    ⟨163841,15033914946⟩,
    ⟨272384,17740171056⟩,
    ⟨196610,13020526146⟩,
    ⟨525376,9689257776⟩,
    ⟨2117,23742973026⟩,
    ⟨12416,35170379586⟩,
    ⟨1540,13024826946⟩,
    ⟨262464,17490663216⟩,
    ⟨65576,14233923876⟩,
    ⟨2179,23741006946⟩,
    ⟨2816,35170686786⟩,
    ⟨1064962,8934225456⟩,
    ⟨38976,27952105296⟩,
    ⟨16434,9772823376⟩,
    ⟨156,35170771476⟩,
    ⟨1900544,5138576976⟩,
    ⟨262784,17740355376⟩,
    ⟨4169,23680058466⟩,
    ⟨542720,9687107376⟩,
    ⟨13312,22288623426⟩,
    ⟨163880,14228681826⟩,
    ⟨75840,26442155856⟩,
    ⟨20484,15037724226⟩,
    ⟨131096,22286987556⟩,
    ⟨1188,14361760866⟩,
    ⟨8273,22421767266⟩,
    ⟨196656,12970390626⟩,
    ⟨98306,35166451266⟩,
    ⟨1573632,9402074901⟩,
    ⟨16481,14368703586⟩,
    ⟨24580,13024458306⟩,
    ⟨98328,22281745506⟩,
    ⟨19520,10339161936⟩,
    ⟨21760,5712840546⟩,
    ⟨1049664,8934283056⟩,
    ⟨133154,14362375266⟩,
    ⟨180,13024846356⟩,
    ⟨1966080,13191640656⟩], []⟩

private def p11 : Packet :=
  ⟨2, 0, 4, 7683, 10, [
    ⟨788480,12907349826⟩,
    ⟨200704,12970264386⟩,
    ⟨57344,12975179586⟩,
    ⟨1544,12977641026⟩,
    ⟨786560,12907472706⟩,
    ⟨196864,12970387266⟩,
    ⟨24580,13024458306⟩,
    ⟨1538,13026793026⟩,
    ⟨113,13026873876⟩,
    ⟨6528,23643490146⟩,
    ⟨33029,23642702946⟩,
    ⟨330,23679997026⟩,
    ⟨32820,12991361556⟩,
    ⟨2179,23741006946⟩,
    ⟨1572888,13495726101⟩,
    ⟨1310760,9469194261⟩,
    ⟨1065536,9536816721⟩,
    ⟨1057856,9537062481⟩,
    ⟨528418,14252274786⟩,
    ⟨266258,22305338466⟩,
    ⟨196609,13020649026⟩,
    ⟨37056,23642261346⟩,
    ⟨6156,23672747106⟩,
    ⟨3584,13024761666⟩,
    ⟨305,12994433556⟩,
    ⟨133154,14362375266⟩,
    ⟨396,23673115746⟩,
    ⟨198,23742911586⟩,
    ⟨21760,5712840546⟩,
    ⟨1671168,9399989841⟩,
    ⟨13056,21818967906⟩,
    ⟨98328,22281745506⟩,
    ⟨1474560,9462904401⟩,
    ⟨24704,13024454466⟩,
    ⟨2117,23742973026⟩,
    ⟨35136,23642507106⟩,
    ⟨786496,12910421826⟩,
    ⟨1114148,9500651541⟩,
    ⟨32905,23674160226⟩,
    ⟨1179668,13527183381⟩,
    ⟨4169,23680058466⟩,
    ⟨67602,22415438946⟩,
    ⟨34826,23673730146⟩,
    ⟨1049121,9504768021⟩,
    ⟨163880,14228681826⟩,
    ⟨65681,22415869026⟩,
    ⟨1188,14361760866⟩,
    ⟨4355,23646635106⟩,
    ⟨688256,10221012816⟩,
    ⟨17411,5778900066⟩,
    ⟨10816,26445289296⟩,
    ⟨19520,10339161936⟩,
    ⟨364544,26358351696⟩,
    ⟨262665,21802452066⟩,
    ⟨660,22414824546⟩,
    ⟨655372,5688030306⟩,
    ⟨1312000,9471198801⟩,
    ⟨661504,5687773026⟩,
    ⟨270656,21802010466⟩,
    ⟨114,13026812436⟩,
    ⟨524329,10226189136⟩,
    ⟨312,12977660436⟩,
    ⟨5632,12977575746⟩,
    ⟨36870,23642272866⟩,
    ⟨295552,21798324066⟩,
    ⟨1049617,13531299861⟩,
    ⟨1573632,9404106321⟩,
    ⟨327692,21794157666⟩,
    ⟨1075200,4970477136⟩,
    ⟨66240,26442217296⟩,
    ⟨134272,10338178896⟩,
    ⟨1064978,13531115541⟩,
    ⟨8211,26448315216⟩,
    ⟨21312,18547418976⟩,
    ⟨1115264,9534113361⟩,
    ⟨557092,14244410466⟩,
    ⟨12312,22288626786⟩,
    ⟨270346,21802021986⟩,
    ⟨147648,5774526306⟩,
    ⟨525696,10222057296⟩,
    ⟨66053,21881095266⟩,
    ⟨536896,18580903776⟩,
    ⟨1212466,8964572016⟩,
    ⟨262499,18882831216⟩,
    ⟨164121,26882872176⟩,
    ⟨102442,18829378416⟩,
    ⟨98601,18829808496⟩,
    ⟨1574152,14001050976⟩,
    ⟨1966080,13443298896⟩,
    ⟨1331200,9470768721⟩], []⟩

private def p12 : Packet :=
  ⟨2, 0, 5, 15875, 9, [
    ⟨1900544,9416767056⟩,
    ⟨184320,10807703121⟩,
    ⟨10880,21881882466⟩,
    ⟨330,23679997026⟩,
    ⟨294932,22297474146⟩,
    ⟨66053,21881095266⟩,
    ⟨1057856,9537062481⟩,
    ⟨525696,10758862416⟩,
    ⟨67602,22415438946⟩,
    ⟨6156,23672747106⟩,
    ⟨32905,23674160226⟩,
    ⟨266816,21802256226⟩,
    ⟨221184,9801070161⟩,
    ⟨4355,23646635106⟩,
    ⟨1180288,9529935441⟩,
    ⟨575488,10791974481⟩,
    ⟨12312,22288626786⟩,
    ⟨134208,10858268241⟩,
    ⟨262417,22305768546⟩,
    ⟨198,23742911586⟩,
    ⟨1189888,9529751121⟩,
    ⟨1050368,8934340176⟩,
    ⟨811008,9722426961⟩,
    ⟨110592,21813561186⟩,
    ⟨98328,22281745506⟩,
    ⟨19584,10859251281⟩,
    ⟨8707,21885027426⟩,
    ⟨327692,21794157666⟩,
    ⟨544832,10761750096⟩,
    ⟨688384,10789275216⟩,
    ⟨65681,22415869026⟩,
    ⟨787968,9722857041⟩,
    ⟨18724,15116362866⟩,
    ⟨266258,22305338466⟩,
    ⟨1065536,9536816721⟩,
    ⟨5284,15116670066⟩,
    ⟨33029,23642702946⟩,
    ⟨147648,10858022481⟩,
    ⟨528930,14252270706⟩,
    ⟨1312808,13159007346⟩,
    ⟨270346,21802021986⟩,
    ⟨33890,15122568306⟩,
    ⟨396,23673115746⟩,
    ⟨661504,10788042321⟩,
    ⟨26112,9805432401⟩,
    ⟨1089570,13243548786⟩,
    ⟨66856,14233900146⟩,
    ⟨655436,6493135986⟩,
    ⟨328064,21794146146⟩,
    ⟨133666,14362371186⟩,
    ⟨1053713,5192942706⟩,
    ⟨1573632,9404106321⟩,
    ⟨1130531,10072703856⟩,
    ⟨8273,22421767266⟩,
    ⟨656516,15102055776⟩,
    ⟨196720,13020521586⟩,
    ⟨527369,6498419826⟩,
    ⟨262665,21802452066⟩,
    ⟨1065106,5239759986⟩,
    ⟨1585152,9403922001⟩,
    ⟨1331200,9470768721⟩,
    ⟨529472,10795353681⟩,
    ⟨557604,14244406386⟩,
    ⟨147718,6529508466⟩,
    ⟨395298,14328824946⟩,
    ⟨50179,6532826226⟩,
    ⟨1114140,22080418656⟩,
    ⟨787491,10293089136⟩,
    ⟨4169,23680058466⟩,
    ⟨24880,12977267826⟩,
    ⟨34352,12975608946⟩,
    ⟨2117,23742973026⟩,
    ⟨1573172,8947000176⟩,
    ⟨1310824,13162079346⟩,
    ⟨548905,10226058096⟩,
    ⟨1147520,22082492256⟩,
    ⟨136197,6529877106⟩,
    ⟨1181752,8931148656⟩,
    ⟨1049107,22153532256⟩,
    ⟨1441829,10034365296⟩,
    ⟨471296,26362333296⟩], []⟩

private def p13 : Packet :=
  ⟨2, 0, 6, 32259, 8, [
    ⟨1966096,13443298656⟩,
    ⟨115456,21813921906⟩,
    ⟨10436,35553219936⟩,
    ⟨1053217,13246006386⟩,
    ⟨271370,21802017906⟩,
    ⟨595008,5694031986⟩,
    ⟨133410,15117345906⟩,
    ⟨49289,23674094706⟩,
    ⟨132740,5505496416⟩,
    ⟨565284,14244283506⟩,
    ⟨333840,34947233121⟩,
    ⟨1048906,23144174706⟩,
    ⟨139345,22420718706⟩,
    ⟨21776,5712840306⟩,
    ⟨1132548,18121520481⟩,
    ⟨787201,17507493216⟩,
    ⟨33362,35255227506⟩,
    ⟨1115296,9534113121⟩,
    ⟨169992,19364148576⟩,
    ⟨278625,14336197746⟩,
    ⟨526467,23724229746⟩,
    ⟨221186,13023475041⟩,
    ⟨295300,35486373216⟩,
    ⟨1585160,14000616801⟩,
    ⟨3632,13024760946⟩,
    ⟨327756,34678858866⟩,
    ⟨1085446,23105406066⟩,
    ⟨655776,10788226401⟩,
    ⟨74369,35283805536⟩,
    ⟨541194,5695890546⟩,
    ⟨1090624,5190715506⟩,
    ⟨1331328,5172652146⟩,
    ⟨99352,22281741426⟩,
    ⟨24880,12977267826⟩,
    ⟨136197,6529877106⟩,
    ⟨2840,35170686066⟩,
    ⟨540996,6498043506⟩,
    ⟨37088,23642261106⟩,
    ⟨1314048,5173020786⟩,
    ⟨1245728,9530983776⟩,
    ⟨274946,35189310816⟩,
    ⟨69891,35725182066⟩,
    ⟨527369,6498419826⟩,
    ⟨147664,5774526066⟩,
    ⟨305153,34682721906⟩,
    ⟨786608,12907471986⟩,
    ⟨1179924,5184709746⟩,
    ⟨18980,14361388146⟩,
    ⟨396352,5741217906⟩,
    ⟨1050256,4970722656⟩,
    ⟨86056,14233470066⟩,
    ⟨50179,6532826226⟩,
    ⟨598022,21847114866⟩,
    ⟨1056930,13292823666⟩,
    ⟨144128,21816871026⟩,
    ⟨1671169,5105014386⟩,
    ⟨575496,15066232161⟩,
    ⟨529476,6498289266⟩,
    ⟨328072,35203253601⟩,
    ⟨164392,14228677746⟩,
    ⟨68162,35554198881⟩,
    ⟨397330,22303245426⟩,
    ⟨1052745,23144236146⟩,
    ⟨9512,14235866226⟩,
    ⟨1181710,23154754416⟩,
    ⟨558210,6497306226⟩,
    ⟨720917,21846573936⟩,
    ⟨264261,35805791346⟩,
    ⟨360964,35184395616⟩,
    ⟨19616,10859251041⟩,
    ⟨1073232,4973610336⟩,
    ⟨66856,14233900146⟩,
    ⟨1474624,5167736946⟩,
    ⟨1055104,23106619506⟩,
    ⟨811024,17775490401⟩,
    ⟨263266,14336136306⟩,
    ⟨12821,35001799536⟩,
    ⟨1853696,8915339376⟩,
    ⟨1770368,13222938741⟩,
    ⟨1511552,4919281776⟩], []⟩

private def p14 : Packet :=
  ⟨2, 1, 0, 259, 13, [
    ⟨1638400,9955477296⟩,
    ⟨425984,5991860016⟩,
    ⟨25600,10276378416⟩,
    ⟨6656,35752339236⟩,
    ⟨416,23673116196⟩,
    ⟨82,18932176176⟩,
    ⟨524300,5409109296⟩,
    ⟨65541,17585104176⟩,
    ⟨1310728,4920473136⟩,
    ⟨147457,6563059236⟩,
    ⟨45056,17538647856⟩,
    ⟨3328,15038027556⟩,
    ⟨656,18657781296⟩,
    ⟨608,22421706276⟩,
    ⟨2178,19447223856⟩,
    ⟨786433,12910548516⟩,
    ⟨1179652,8931276336⟩,
    ⟨98312,17534842416⟩,
    ⟨4354,19368580656⟩,
    ⟨1072,10276508976⟩,
    ⟨8512,17557509936⟩,
    ⟨344064,21794031396⟩,
    ⟨4288,19350574896⟩,
    ⟨10272,22414456356⟩,
    ⟨1097728,5190485796⟩,
    ⟨1538,13026792996⟩,
    ⟨655376,5688030756⟩,
    ⟨1033,5478229296⟩,
    ⟨262164,17740363056⟩,
    ⟨204800,5706778416⟩,
    ⟨34880,19346581296⟩,
    ⟨20512,22573905456⟩,
    ⟨776,17541047856⟩,
    ⟨1048593,4907820336⟩,
    ⟨524322,9689265456⟩,
    ⟨1156,5508638256⟩,
    ⟨8195,17590019376⟩,
    ⟨18440,15116367396⟩,
    ⟨557568,14244407076⟩,
    ⟨132160,9799358256⟩,
    ⟨270464,34683774756⟩,
    ⟨33028,19366614576⟩,
    ⟨1053696,5192943396⟩,
    ⟨67600,18658457136⟩,
    ⟨131112,9765942576⟩,
    ⟨16452,15155136036⟩,
    ⟨540800,6498051876⟩,
    ⟨32897,19346708016⟩,
    ⟨1049090,13295224356⟩,
    ⟨331776,17802102576⟩,
    ⟨8216,17825887536⟩,
    ⟨8708,34751055396⟩,
    ⟨262464,17490663216⟩,
    ⟨196864,12970387236⟩,
    ⟨528385,15056524836⟩,
    ⟨1312768,13159008036⟩,
    ⟨4102,19350582576⟩,
    ⟨1114144,22080419376⟩,
    ⟨33040,35722298916⟩,
    ⟨74,19435492656⟩,
    ⟨657408,9686124336⟩,
    ⟨1065216,5192574756⟩,
    ⟨545,26114204976⟩,
    ⟨533504,5696259876⟩,
    ⟨4120,18832520496⟩,
    ⟨32804,26862974256⟩,
    ⟨2113,19445995056⟩,
    ⟨16402,5981238576⟩,
    ⟨393728,21800421156⟩,
    ⟨66624,14367594276⟩,
    ⟨1056896,13292824356⟩,
    ⟨295936,22297470756⟩,
    ⟨82432,21881030436⟩,
    ⟨4356,36261004836⟩,
    ⟨131202,15151203876⟩,
    ⟨1572928,5109016356⟩,
    ⟨262402,35189491236⟩,
    ⟨133121,15150896676⟩,
    ⟨97,26985178416⟩,
    ⟨164864,9770112816⟩,
    ⟨279040,21802387236⟩,
    ⟨65672,35250439716⟩,
    ⟨143360,22286534436⟩,
    ⟨2068,18926892336⟩,
    ⟨786464,21781575216⟩,
    ⟨65542,17585042736⟩,
    ⟨524545,5411132976⟩,
    ⟨36865,36258731556⟩,
    ⟨527360,6498420516⟩,
    ⟨4368,35726231076⟩,
    ⟨73792,17852360496⟩,
    ⟨32778,19362379056⟩,
    ⟨147584,9803228976⟩,
    ⟨1060,9804649776⟩,
    ⟨1085440,23105406756⟩,
    ⟨73984,34715232036⟩,
    ⟨16417,9805325616⟩,
    ⟨529408,9756350256⟩,
    ⟨1179712,5234845476⟩,
    ⟨788480,12907349796⟩,
    ⟨164352,14228678436⟩,
    ⟨1049728,8932316976⟩,
    ⟨524608,5411067696⟩,
    ⟨2084,26979956016⟩,
    ⟨1049152,4907751216⟩,
    ⟨271360,21802018596⟩,
    ⟨593920,14250182436⟩,
    ⟨200,36325824036⟩,
    ⟨1083392,23136864036⟩,
    ⟨20608,15037720356⟩,
    ⟨327712,21794158116⟩], []⟩

private def p15 : Packet :=
  ⟨2, 1, 1, 771, 12, [
    ⟨1638400,9955477296⟩,
    ⟨425984,5991860016⟩,
    ⟨25600,21818926896⟩,
    ⟨6656,35752339236⟩,
    ⟨416,23673116226⟩,
    ⟨1048600,4937250096⟩,
    ⟨65542,17585042736⟩,
    ⟨16449,5510420016⟩,
    ⟨524300,5409109296⟩,
    ⟨8209,17858389296⟩,
    ⟨263232,14336137026⟩,
    ⟨133122,5505381936⟩,
    ⟨36992,19366242096⟩,
    ⟨33536,18825631536⟩,
    ⟨1048612,8932324656⟩,
    ⟨131712,5975332656⟩,
    ⟨67592,35250009636⟩,
    ⟨524322,9689265456⟩,
    ⟨20736,5461141296⟩,
    ⟨8512,17557509936⟩,
    ⟨132097,9799423536⟩,
    ⟨262164,17740363056⟩,
    ⟨1310722,13162083876⟩,
    ⟨65584,26375386416⟩,
    ⟨559104,5407934256⟩,
    ⟨12296,17540740656⟩,
    ⟨262657,17742386736⟩,
    ⟨1154,15150159426⟩,
    ⟨18560,5508327216⟩,
    ⟨655424,6493136676⟩,
    ⟨32808,26878702896⟩,
    ⟨1296,14235932226⟩,
    ⟨1049152,4907751216⟩,
    ⟨2053,19446981936⟩,
    ⟨200704,12970264356⟩,
    ⟨16402,5981238576⟩,
    ⟨73856,17856292656⟩,
    ⟨528385,15056524866⟩,
    ⟨270368,21802022436⟩,
    ⟨1540,13024826946⟩,
    ⟨1179904,5184710436⟩,
    ⟨200,36325824066⟩,
    ⟨114688,22281619236⟩,
    ⟨541184,5695891236⟩,
    ⟨36928,19362309936⟩,
    ⟨1049601,8934348336⟩,
    ⟨147464,6529512996⟩,
    ⟨786560,12907472676⟩,
    ⟨1089536,13243549476⟩,
    ⟨770,35172718146⟩,
    ⟨208,35822507586⟩,
    ⟨262401,17490728496⟩,
    ⟨7168,23672743716⟩,
    ⟨131120,10269259056⟩,
    ⟨32778,19362379056⟩,
    ⟨10752,18657470256⟩,
    ⟨4130,26868872496⟩,
    ⟨67072,26375378736⟩,
    ⟨147460,9803232816⟩,
    ⟨528400,14252275236⟩,
    ⟨65572,26107999536⟩,
    ⟨1064968,5192578596⟩,
    ⟨2368,19429218096⟩,
    ⟨32897,19346708016⟩,
    ⟨10244,17587926576⟩,
    ⟨4105,19368338736⟩,
    ⟨204800,5706778416⟩,
    ⟨263424,26076534576⟩,
    ⟨8198,17588974896⟩,
    ⟨1310752,22033233456⟩,
    ⟨262720,17742321456⟩,
    ⟨65553,17852491056⟩,
    ⟨1181696,8931149616⟩,
    ⟨2051,19445998896⟩,
    ⟨557060,5408060976⟩,
    ⟨524312,5943883056⟩,
    ⟨331776,17802102576⟩,
    ⟨1183744,5184587556⟩,
    ⟨1584,12977640546⟩], []⟩

private def p16 : Packet :=
  ⟨2, 1, 2, 1795, 11, [
    ⟨1581056,9953511216⟩,
    ⟨344064,21794031396⟩,
    ⟨167936,5455120176⟩,
    ⟨3584,13024761666⟩,
    ⟨416,23673116226⟩,
    ⟨1048600,4937250096⟩,
    ⟨131078,5505447216⟩,
    ⟨524297,5411136816⟩,
    ⟨270400,17742260016⟩,
    ⟨98368,35166447426⟩,
    ⟨20484,15037724226⟩,
    ⟨1296,14235932226⟩,
    ⟨642,35282818626⟩,
    ⟨1048609,8934352176⟩,
    ⟨71680,17551427376⟩,
    ⟨51200,26862782256⟩,
    ⟨524336,10222073136⟩,
    ⟨131840,22286964546⟩,
    ⟨1160,15116736066⟩,
    ⟨294916,17487656496⟩,
    ⟨24577,13026547266⟩,
    ⟨266242,17490605616⟩,
    ⟨131264,5505439536⟩,
    ⟨73730,17852364336⟩,
    ⟨524608,5411067696⟩,
    ⟨65541,17585104176⟩,
    ⟨131112,9765942576⟩,
    ⟨1049664,8934283056⟩,
    ⟨10496,35249022786⟩,
    ⟨262161,17742390576⟩,
    ⟨34304,12975609666⟩,
    ⟨12292,35170383426⟩,
    ⟨1574912,5105944356⟩,
    ⟨1064962,8934225456⟩,
    ⟨4736,35249329986⟩,
    ⟨34818,19346585136⟩,
    ⟨800,22288995906⟩,
    ⟨196624,5706905136⟩,
    ⟨24584,12977272386⟩,
    ⟨525313,9689323056⟩,
    ⟨10272,22414456386⟩,
    ⟨262156,17488704816⟩,
    ⟨32777,19362440496⟩,
    ⟨18448,14361392706⟩,
    ⟨557184,5408057136⟩,
    ⟨65572,26107999536⟩,
    ⟨1122,14368642146⟩,
    ⟨1310848,13159130916⟩,
    ⟨1048596,4905792816⟩,
    ⟨4169,23680058466⟩,
    ⟨655872,5688026916⟩,
    ⟨1114368,13237774116⟩,
    ⟨524312,5943883056⟩,
    ⟨263424,26076534576⟩,
    ⟨1168,14361761346⟩,
    ⟨1049152,4907751216⟩,
    ⟨540674,9689200176⟩,
    ⟨1187840,10000697136⟩,
    ⟨17411,5778900066⟩,
    ⟨524324,9687299376⟩,
    ⟨4179,35524842336⟩], []⟩

private def p17 : Packet :=
  ⟨2, 1, 3, 3843, 10, [
    ⟨1574912,5105944386⟩,
    ⟨327808,17739310896⟩,
    ⟨172032,14228555586⟩,
    ⟨20992,14235559746⟩,
    ⟨1296,14235932226⟩,
    ⟨1048612,8932324656⟩,
    ⟨524298,5411075376⟩,
    ⟨262153,17490732336⟩,
    ⟨196672,13020522306⟩,
    ⟨24577,13026547266⟩,
    ⟨3584,13024761666⟩,
    ⟨266304,17490601776⟩,
    ⟨98306,35166451266⟩,
    ⟨524672,5409101616⟩,
    ⟨1048594,4907758896⟩,
    ⟨12320,22288627266⟩,
    ⟨772,35170752066⟩,
    ⟨163841,15033914946⟩,
    ⟨1049728,8932316976⟩,
    ⟨524324,9687299376⟩,
    ⟨24584,12977272386⟩,
    ⟨20484,15037724226⟩,
    ⟨800,22288995906⟩,
    ⟨262164,17740363056⟩,
    ⟨98368,35166447426⟩,
    ⟨2179,23741006946⟩,
    ⟨12289,35172472386⟩,
    ⟨296960,17487529776⟩,
    ⟨1122,14368642146⟩,
    ⟨196616,12970391106⟩,
    ⟨540736,9689196336⟩,
    ⟨660,22414824546⟩,
    ⟨525313,9689323056⟩,
    ⟨1067008,8932132656⟩,
    ⟨330,23679997026⟩,
    ⟨133154,14362375266⟩,
    ⟨1048632,4905792261⟩,
    ⟨396,23673115746⟩,
    ⟨270338,17742263856⟩,
    ⟨39040,27954071376⟩,
    ⟨262784,17740355376⟩,
    ⟨537,26382635856⟩,
    ⟨20496,14235563586⟩,
    ⟨3284,18926876016⟩,
    ⟨99328,22281742146⟩,
    ⟨1049152,4907751216⟩,
    ⟨266242,17490605616⟩,
    ⟨134272,10338178896⟩,
    ⟨24624,12977271906⟩,
    ⟨692224,10252224336⟩,
    ⟨328448,26613389136⟩,
    ⟨133329,18927920496⟩,
    ⟨67809,26980984176⟩], []⟩

private def p18 : Packet :=
  ⟨2, 1, 4, 7939, 9, [
    ⟨788480,12907349826⟩,
    ⟨200704,12970264386⟩,
    ⟨57344,12975179586⟩,
    ⟨1544,12977641026⟩,
    ⟨198,23742911586⟩,
    ⟨786433,12910548546⟩,
    ⟨196864,12970387266⟩,
    ⟨24832,12977268546⟩,
    ⟨3584,13024761666⟩,
    ⟨34826,23673730146⟩,
    ⟨33029,23642702946⟩,
    ⟨4169,23680058466⟩,
    ⟨528418,14252274786⟩,
    ⟨65681,22415869026⟩,
    ⟨262172,26328200016⟩,
    ⟨131233,14362805346⟩,
    ⟨594,22421705826⟩,
    ⟨37056,23642261346⟩,
    ⟨18468,14361392226⟩,
    ⟨1122,14368642146⟩,
    ⟨660,22414824546⟩,
    ⟨529664,10259535696⟩,
    ⟨10260,22414455906⟩,
    ⟨267008,26365663056⟩,
    ⟨196672,13020522306⟩,
    ⟨1310888,13159130226⟩,
    ⟨35136,23642507106⟩,
    ⟨557092,14244410466⟩,
    ⟨6528,23643490146⟩,
    ⟨24704,13024454466⟩,
    ⟨17411,5778900066⟩,
    ⟨36870,23642272866⟩,
    ⟨1572952,5109015666⟩,
    ⟨8707,21885027426⟩,
    ⟨1312002,5176100466⟩,
    ⟨1053713,5192942706⟩,
    ⟨786560,12907472706⟩,
    ⟨524577,14252704866⟩,
    ⟨1312808,13159007346⟩,
    ⟨32905,23674160226⟩,
    ⟨1540,13024826946⟩,
    ⟨540682,5695894626⟩,
    ⟨98328,22281745506⟩,
    ⟨1212466,8964572016⟩,
    ⟨396,23673115746⟩,
    ⟨274496,26332055376⟩,
    ⟨2179,23741006946⟩,
    ⟨67602,22415438946⟩,
    ⟨262976,26332116816⟩,
    ⟨163880,14228681826⟩,
    ⟨1053217,13246006386⟩,
    ⟨6156,23672747106⟩,
    ⟨2117,23742973026⟩,
    ⟨1056930,13292823666⟩,
    ⟨1311028,4920468336⟩,
    ⟨688384,10252470096⟩,
    ⟨196609,13020649026⟩,
    ⟨34304,12975609666⟩,
    ⟨262417,22305768546⟩,
    ⟨1114212,13287908466⟩,
    ⟨24626,12994113861⟩,
    ⟨1575680,5105928306⟩,
    ⟨1409029,18004600176⟩,
    ⟨1198090,14060520816⟩], []⟩

private def p19 : Packet :=
  ⟨2, 1, 5, 16131, 8, [
    ⟨333824,21793900386⟩,
    ⟨33029,23642702946⟩,
    ⟨594,22421705826⟩,
    ⟨270346,21802021986⟩,
    ⟨73920,21880653666⟩,
    ⟨6528,23643490146⟩,
    ⟨98328,22281745506⟩,
    ⟨295552,21798324066⟩,
    ⟨4169,23680058466⟩,
    ⟨10260,22414455906⟩,
    ⟨66053,21881095266⟩,
    ⟨262417,22305768546⟩,
    ⟨36870,23642272866⟩,
    ⟨13056,21818967906⟩,
    ⟨2179,23741006946⟩,
    ⟨35136,23642507106⟩,
    ⟨396,23673115746⟩,
    ⟨983104,5419395186⟩,
    ⟨26120,5461182066⟩,
    ⟨1053713,5192942706⟩,
    ⟨133666,14362371186⟩,
    ⟨263332,14328271986⟩,
    ⟨57392,12975178866⟩,
    ⟨66856,14233900146⟩,
    ⟨1572952,5109015666⟩,
    ⟨1671170,5104830066⟩,
    ⟨1065540,5239752306⟩,
    ⟨139425,14362739826⟩,
    ⟨1312002,5176100466⟩,
    ⟨575489,6496999026⟩,
    ⟨6156,23672747106⟩,
    ⟨1065106,5239759986⟩,
    ⟨82017,14367655026⟩,
    ⟨200752,12970263666⟩,
    ⟨396352,5741217906⟩,
    ⟨164392,14228677746⟩,
    ⟨811012,5424318066⟩,
    ⟨566400,5692065906⟩,
    ⟨1132800,5188380786⟩,
    ⟨675843,15053514096⟩,
    ⟨788528,12907349106⟩,
    ⟨37056,23642261346⟩,
    ⟨1057860,5239998066⟩,
    ⟨657168,14248584816⟩,
    ⟨1180296,5184702066⟩,
    ⟨1474561,5167928946⟩,
    ⟨656706,15053694576⟩,
    ⟨606218,5693801586⟩,
    ⟨34826,23673730146⟩,
    ⟨1585280,5105805426⟩,
    ⟨579072,10255161456⟩,
    ⟨526625,15054799986⟩,
    ⟨557156,15049516146⟩,
    ⟨21776,5712840306⟩,
    ⟨19600,5775754866⟩,
    ⟨279555,5746394226⟩,
    ⟨147718,6529508466⟩,
    ⟨1283072,13239732336⟩,
    ⟨1966596,9417803376⟩,
    ⟨1081889,13244040306⟩,
    ⟨1355776,22066333536⟩,
    ⟨1852032,13445126256⟩,
    ⟨1246214,13290063216⟩,
    ⟨156752,14365628016⟩], []⟩

private def p20 : Packet :=
  ⟨2, 1, 6, 32515, 7, [
    ⟨1671232,5104822386⟩,
    ⟨409606,5740987506⟩,
    ⟨13336,22288622706⟩,
    ⟨1051169,13293192306⟩,
    ⟨328096,21794145906⟩,
    ⟨524948,22381335666⟩,
    ⟨49289,23674094706⟩,
    ⟨165122,6513034866⟩,
    ⟨661505,6493066866⟩,
    ⟨270660,34683766386⟩,
    ⟨68168,34715469426⟩,
    ⟨1065234,5192574066⟩,
    ⟨5284,15116670066⟩,
    ⟨57392,12975178866⟩,
    ⟨787970,5427758706⟩,
    ⟨1189896,5184456306⟩,
    ⟨70149,34715599986⟩,
    ⟨196720,13020521586⟩,
    ⟨1052745,23144236146⟩,
    ⟨281728,5742200946⟩,
    ⟨532769,14252639346⟩,
    ⟨184832,5707425906⟩,
    ⟨295956,22297470066⟩,
    ⟨598022,21847114866⟩,
    ⟨266386,35187090546⟩,
    ⟨1575680,5105928306⟩,
    ⟨221185,5506094706⟩,
    ⟨3368,15038026866⟩,
    ⟨1048774,23222817906⟩,
    ⟨164392,14228677746⟩,
    ⟨541008,5695882866⟩,
    ⟨111616,21813553266⟩,
    ⟨21032,14235559026⟩,
    ⟨139345,22420718706⟩,
    ⟨1574936,5105943666⟩,
    ⟨66658,14367593586⟩,
    ⟨1179924,5184709746⟩,
    ⟨305153,34682721906⟩,
    ⟨147656,6529500786⟩,
    ⟨26116,5508367986⟩,
    ⟨102411,36009231216⟩,
    ⟨1585280,5105805426⟩,
    ⟨1115272,5188879986⟩,
    ⟨35110,19413427056⟩,
    ⟨278625,14336197746⟩,
    ⟨426384,18559276656⟩,
    ⟨68626,22415434866⟩,
    ⟨1425664,22063499376⟩,
    ⟨571424,22583412336⟩,
    ⟨18661,18925953141⟩,
    ⟨1312322,5176108656⟩,
    ⟨564416,18841995381⟩], []⟩

private def p21 : Packet :=
  ⟨3, 0, 2, 3079, 11, [
    ⟨1574912,5105944386⟩,
    ⟨327808,17739310896⟩,
    ⟨172032,14228555586⟩,
    ⟨20992,14235559746⟩,
    ⟨1296,14235932196⟩,
    ⟨104,15040139556⟩,
    ⟨1310724,13159134786⟩,
    ⟨540674,9689200176⟩,
    ⟨1538,13026858276⟩,
    ⟨12292,35170383426⟩,
    ⟨1048593,4907820336⟩,
    ⟨196864,12970387266⟩,
    ⟨296960,17487529776⟩,
    ⟨524321,9689326896⟩,
    ⟨152,35171815716⟩,
    ⟨98368,35166447426⟩,
    ⟨772,35171800356⟩,
    ⟨1049728,8932316976⟩,
    ⟨270400,17742260016⟩,
    ⟨24584,12977272386⟩,
    ⟨4144,12977598756⟩,
    ⟨655364,9686251056⟩,
    ⟨1048610,8934290736⟩,
    ⟨262153,17490732336⟩,
    ⟨524672,5409101616⟩,
    ⟨163842,15033792066⟩,
    ⟨1067008,8932132656⟩,
    ⟨196672,13020522306⟩,
    ⟨99328,22281742146⟩,
    ⟨24704,13024454466⟩,
    ⟨528448,5411006256⟩,
    ⟨20484,15037724226⟩,
    ⟨552,14235951396⟩,
    ⟨262162,17742329136⟩,
    ⟨1282,15040124196⟩,
    ⟨1049152,4907751216⟩,
    ⟨112,13026873636⟩,
    ⟨524297,5411136816⟩,
    ⟨262657,17742386736⟩,
    ⟨6528,23672735586⟩,
    ⟨98306,35166451266⟩,
    ⟨132101,14365954086⟩,
    ⟨13312,22288623426⟩,
    ⟨10260,22414455906⟩,
    ⟨163904,15033788226⟩,
    ⟨542720,9687107376⟩,
    ⟨8707,22421966886⟩,
    ⟨196616,12970391106⟩,
    ⟨2246,28035919941⟩,
    ⟨18468,14361392226⟩,
    ⟨1058816,4905600816⟩,
    ⟨88,35172798756⟩,
    ⟨3712,13024765716⟩,
    ⟨98336,22281745986⟩,
    ⟨266242,17490605616⟩,
    ⟨1851392,13195568976⟩,
    ⟨168,15039156516⟩,
    ⟨16481,14368899366⟩,
    ⟨65681,22419013926⟩,
    ⟨330,23646711846⟩,
    ⟨1284,15039141156⟩,
    ⟨13056,22288615266⟩,
    ⟨34304,12975609636⟩,
    ⟨196656,12970390626⟩,
    ⟨1049216,4905785136⟩,
    ⟨262401,17490728496⟩,
    ⟨20545,15039878721⟩,
    ⟨163880,14228681826⟩,
    ⟨525313,9689323056⟩,
    ⟨786456,17773916421⟩,
    ⟨133154,14362375266⟩,
    ⟨2944,35170690836⟩,
    ⟨524324,9687299376⟩,
    ⟨5187,23696974086⟩,
    ⟨530432,5408917296⟩], []⟩

private def p22 : Packet :=
  ⟨3, 0, 3, 7175, 10, [
    ⟨788480,12907349826⟩,
    ⟨200704,12970264386⟩,
    ⟨57344,12975179586⟩,
    ⟨1544,12994417956⟩,
    ⟨304,12994433316⟩,
    ⟨786560,12907472706⟩,
    ⟨196672,13020522306⟩,
    ⟨24580,13024458306⟩,
    ⟨1538,13026858276⟩,
    ⟨176,13025890596⟩,
    ⟨36870,23642272866⟩,
    ⟨6528,23672735586⟩,
    ⟨1049617,9504752661⟩,
    ⟨34826,23673730146⟩,
    ⟨1049121,9504768021⟩,
    ⟨786496,12910421826⟩,
    ⟨6156,23672747106⟩,
    ⟨196864,12970387266⟩,
    ⟨37056,23642261346⟩,
    ⟨35136,23673718626⟩,
    ⟨24584,12977272386⟩,
    ⟨1179668,9529943121⟩,
    ⟨132101,14365954086⟩,
    ⟨66053,22419017766⟩,
    ⟨1114148,9500651541⟩,
    ⟨16482,10342318341⟩,
    ⟨8274,26448445701⟩,
    ⟨1573632,9404106321⟩,
    ⟨1312000,9469167381⟩,
    ⟨525321,14303039526⟩,
    ⟨262665,22356103206⟩,
    ⟨1064978,9536824401⟩,
    ⟨1056802,9504583701⟩,
    ⟨19584,14361380706⟩,
    ⟨98328,22281745506⟩,
    ⟨8896,26445166416⟩,
    ⟨163880,14228681826⟩,
    ⟨397,27968082516⟩,
    ⟨21760,14235551586⟩,
    ⟨276480,26327877456⟩,
    ⟨1585152,9403918161⟩,
    ⟨263040,26328184656⟩,
    ⟨147462,5774537826⟩,
    ⟨73734,21880665186⟩,
    ⟨112,13026873636⟩,
    ⟨524577,14303035686⟩,
    ⟨1331200,9470764881⟩,
    ⟨331,27974963796⟩,
    ⟨690176,10220767056⟩,
    ⟨65684,26444513541⟩,
    ⟨525632,10225989456⟩,
    ⟨8707,22421966886⟩,
    ⟨270656,21802010466⟩,
    ⟨546816,10221750096⟩,
    ⟨266258,22305338466⟩,
    ⟨1188,5776027686⟩,
    ⟨1115264,9500624661⟩,
    ⟨655372,5688030306⟩,
    ⟨1065536,9536816721⟩,
    ⟨362496,26326894416⟩,
    ⟨594,21885104166⟩,
    ⟨131233,14365950246⟩,
    ⟨110592,21813561186⟩,
    ⟨294932,22297474146⟩,
    ⟨1572888,9404114001⟩,
    ⟨540682,5695894626⟩,
    ⟨1189888,9529747281⟩,
    ⟨1310760,9469194261⟩,
    ⟨17411,14368903206⟩,
    ⟨270346,21802021986⟩,
    ⟨13056,22288615266⟩,
    ⟨540992,5695883106⟩,
    ⟨184320,5707433826⟩,
    ⟨2246,28035919941⟩,
    ⟨557092,14244410466⟩,
    ⟨1553,17826263301⟩,
    ⟨34184,19362428256⟩,
    ⟨4202,19351622496⟩,
    ⟨1671168,9399986001⟩,
    ⟨327692,21794157666⟩,
    ⟨266816,22305326946⟩,
    ⟨37762,35468424816⟩,
    ⟨262537,35489521926⟩,
    ⟨558208,14244398946⟩,
    ⟨1049697,14100537606⟩,
    ⟨575488,5691705186⟩,
    ⟨182272,10270902096⟩,
    ⟨11456,18657458016⟩,
    ⟨983040,9714558801⟩,
    ⟨531136,26928625776⟩,
    ⟨268326,18875581296⟩,
    ⟨167962,26882442096⟩,
    ⟨33220,36257936736⟩,
    ⟨132480,10269243216⟩,
    ⟨559126,26929628016⟩,
    ⟨530454,26928644976⟩,
    ⟨296998,18876564336⟩,
    ⟨269504,18875562096⟩,
    ⟨102442,18829378416⟩], []⟩

private def p23 : Packet :=
  ⟨3, 0, 4, 15367, 9, [
    ⟨1900544,9416763216⟩,
    ⟨184320,10807699281⟩,
    ⟨10880,22414444386⟩,
    ⟨1320,10276515861⟩,
    ⟨1179668,9529943121⟩,
    ⟨17474,10342306821⟩,
    ⟨266258,22305338466⟩,
    ⟨35136,23673718626⟩,
    ⟨73734,21880665186⟩,
    ⟨655744,10788226641⟩,
    ⟨98328,22281745506⟩,
    ⟨6156,23672747106⟩,
    ⟨1584,9773199381⟩,
    ⟨1335296,9470830416⟩,
    ⟨524330,10761823056⟩,
    ⟨266816,22305326946⟩,
    ⟨215040,9801131856⟩,
    ⟨1188,10339430421⟩,
    ⟨1585152,9403918161⟩,
    ⟨295552,22297462626⟩,
    ⟨73920,21880653666⟩,
    ⟨526080,9689314896⟩,
    ⟨1065536,9536816721⟩,
    ⟨305152,21797832546⟩,
    ⟨16434,9805325136⟩,
    ⟨37056,23642261346⟩,
    ⟨270656,21802010466⟩,
    ⟨655372,10788234321⟩,
    ⟨397,27968082516⟩,
    ⟨6528,23672735586⟩,
    ⟨131110,10856194896⟩,
    ⟨13056,22288615266⟩,
    ⟨1572888,9404114001⟩,
    ⟨67602,22415438946⟩,
    ⟨1277952,8929175376⟩,
    ⟨575488,10791970641⟩,
    ⟨132736,9799415376⟩,
    ⟨16497,14368899606⟩,
    ⟨661504,10788038481⟩,
    ⟨1049123,14100529686⟩,
    ⟨811008,9722423121⟩,
    ⟨1049873,14051385366⟩,
    ⟨327692,21794157666⟩,
    ⟨34826,23673730146⟩,
    ⟨524581,15105196566⟩,
    ⟨131241,15120925206⟩,
    ⟨333824,21793900386⟩,
    ⟨132165,15154356246⟩,
    ⟨110592,21813561186⟩,
    ⟨36870,23642272866⟩,
    ⟨328064,21794146146⟩,
    ⟨595,26716672596⟩,
    ⟨525385,15107170326⟩,
    ⟨1189888,9529747281⟩,
    ⟨17923,14368907286⟩,
    ⟨1048628,8997266256⟩,
    ⟨1049745,14098571286⟩,
    ⟨99072,22281733986⟩,
    ⟨68160,22415427426⟩,
    ⟨24602,21818930016⟩,
    ⟨1122,10342379541⟩,
    ⟨1049129,14051377686⟩,
    ⟨131124,9799426896⟩,
    ⟨17539,15155339286⟩,
    ⟨1064978,9536824401⟩,
    ⟨132357,15120932886⟩,
    ⟨1310824,13162079346⟩,
    ⟨540992,10795107921⟩,
    ⟨12312,22288626786⟩,
    ⟨983040,9714558801⟩,
    ⟨16485,15155331606⟩,
    ⟨1057058,13245637746⟩,
    ⟨1050240,8997254736⟩,
    ⟨1474560,9462900561⟩,
    ⟨1314048,13158991986⟩,
    ⟨499712,22299314016⟩,
    ⟨197504,21813016416⟩,
    ⟨263056,34918053216⟩], []⟩

private def p24 : Packet :=
  ⟨3, 0, 5, 31751, 8, [
    ⟨1966592,13443290976⟩,
    ⟨114712,22281618546⟩,
    ⟨6592,36289193556⟩,
    ⟨132134,10856190816⟩,
    ⟨1124356,18121586016⟩,
    ⟨566400,14244268146⟩,
    ⟨8786,26179940421⟩,
    ⟨1331232,9470768481⟩,
    ⟨524588,6480679776⟩,
    ⟨328066,34678851186⟩,
    ⟨134216,15117338226⟩,
    ⟨184832,5707425906⟩,
    ⟨1050384,4907808096⟩,
    ⟨294996,35182175346⟩,
    ⟨593954,14250181746⟩,
    ⟨1083402,23136863346⟩,
    ⟨12440,35170378866⟩,
    ⟨221440,5455767666⟩,
    ⟨18980,14361388146⟩,
    ⟨811072,12960552801⟩,
    ⟨334848,21793892466⟩,
    ⟨66244,34747987296⟩,
    ⟨1065106,5239759986⟩,
    ⟨690432,6479435616⟩,
    ⟨4366,36276622176⟩,
    ⟨295584,22297462386⟩,
    ⟨1057864,13245630066⟩,
    ⟨196720,13020521586⟩,
    ⟨541706,10795111521⟩,
    ⟨1183764,5184586866⟩,
    ⟨13088,22288615026⟩,
    ⟨788528,12907349106⟩,
    ⟨157824,5505242976⟩,
    ⟨1671232,5104822386⟩,
    ⟨17760,10811946336⟩,
    ⟨401418,21799928946⟩,
    ⟨787972,12907464306⟩,
    ⟨164008,15034963041⟩,
    ⟨47108,35452581216⟩,
    ⟨1119360,13237635186⟩,
    ⟨262936,26080653381⟩,
    ⟨1312004,13159122546⟩,
    ⟨591890,22381888626⟩,
    ⟨1089570,13243548786⟩,
    ⟨529488,14252263026⟩,
    ⟨1133056,13556275041⟩,
    ⟨2246,28035919941⟩,
    ⟨99074,35166439026⟩,
    ⟨344076,21794030706⟩,
    ⟨655760,5688018546⟩,
    ⟨1597952,13497358176⟩,
    ⟨266824,35205956961⟩,
    ⟨19600,14361380466⟩,
    ⟨1189920,9529750881⟩,
    ⟨307216,34951230816⟩,
    ⟨33220,36257936736⟩,
    ⟨198152,12970378866⟩,
    ⟨16490,6517052256⟩,
    ⟨1475584,9462896481⟩,
    ⟨547072,6480418656⟩,
    ⟨1050272,8997254496⟩,
    ⟨68192,22415427186⟩,
    ⟨65716,17585099616⟩,
    ⟨147718,6529508466⟩,
    ⟨305408,35198883681⟩,
    ⟨983168,12954654561⟩,
    ⟨563328,19379869536⟩,
    ⟨1180296,5184702066⟩,
    ⟨74758,21880661106⟩,
    ⟨1572920,5109146196⟩,
    ⟨5442,19351614816⟩,
    ⟨675848,15070229856⟩,
    ⟨26176,13026534996⟩,
    ⟨270688,21802010226⟩,
    ⟨17458,9805321056⟩,
    ⟨1083712,23136847986⟩,
    ⟨10882,35282634081⟩,
    ⟨364548,34680894816⟩,
    ⟨528546,15054431346⟩,
    ⟨211200,17535494256⟩,
    ⟨3497,15038030196⟩,
    ⟨575490,15099655521⟩,
    ⟨169986,19347436896⟩,
    ⟨1331202,13967193441⟩,
    ⟨1049140,4970730336⟩,
    ⟨153632,10805802336⟩,
    ⟨221186,13023475041⟩,
    ⟨3268,19446969696⟩,
    ⟨1671184,13489436001⟩,
    ⟨526088,5411124576⟩,
    ⟨18912,23690622576⟩,
    ⟨98392,35166446706⟩], []⟩

private def p25 : Packet :=
  ⟨3, 1, 1, 1287, 11, [
    ⟨1581056,9953511216⟩,
    ⟨344064,21794031396⟩,
    ⟨167936,5455120176⟩,
    ⟨3584,13024761636⟩,
    ⟨416,23673116196⟩,
    ⟨1048600,4937250096⟩,
    ⟨131078,5505447216⟩,
    ⟨524297,5411136816⟩,
    ⟨270400,17742260016⟩,
    ⟨98368,35166447426⟩,
    ⟨20484,15037724226⟩,
    ⟨1296,14235932196⟩,
    ⟨1049089,4907816496⟩,
    ⟨34818,19346585136⟩,
    ⟨524336,10222073136⟩,
    ⟨1160,15116736036⟩,
    ⟨71680,17551427376⟩,
    ⟨147520,9799296816⟩,
    ⟨772,35170752036⟩,
    ⟨266242,17490605616⟩,
    ⟨24704,13024454466⟩,
    ⟨131105,9799427376⟩,
    ⟨294916,17487656496⟩,
    ⟨73730,17852364336⟩,
    ⟨1049664,8934283056⟩,
    ⟨524928,22381336356⟩,
    ⟨18688,15116363586⟩,
    ⟨32808,26878702896⟩,
    ⟨65553,17852491056⟩,
    ⟨1312768,13159008036⟩,
    ⟨12320,22288627266⟩,
    ⟨655616,9749161776⟩,
    ⟨32897,19346708016⟩,
    ⟨65572,26107999536⟩,
    ⟨540674,9689200176⟩,
    ⟨10248,35249026626⟩,
    ⟨197120,5706901296⟩,
    ⟨262161,17742390576⟩,
    ⟨34304,12975609636⟩,
    ⟨528448,5411006256⟩,
    ⟨131264,5505439536⟩,
    ⟨1064962,8934225456⟩,
    ⟨262156,17488704816⟩,
    ⟨1048596,4905792816⟩,
    ⟨66816,14233900836⟩,
    ⟨648,35249395236⟩,
    ⟨24584,12977272386⟩,
    ⟨12416,35170379586⟩,
    ⟨1061,10339422981⟩,
    ⟨800,22288995876⟩,
    ⟨197632,21813028656⟩,
    ⟨4171,27975090501⟩,
    ⟨18448,14361392706⟩,
    ⟨524672,5409101616⟩,
    ⟨672,22414824996⟩,
    ⟨8275,26716799301⟩,
    ⟨67648,17584973616⟩,
    ⟨1187840,10000697136⟩,
    ⟨657408,9686124336⟩,
    ⟨1576960,8946878256⟩,
    ⟨12312,22288626786⟩,
    ⟨32773,19346711856⟩,
    ⟨20992,14235559746⟩], []⟩

private def p26 : Packet :=
  ⟨3, 1, 2, 3335, 10, [
    ⟨1574912,5105944386⟩,
    ⟨327808,17739310896⟩,
    ⟨172032,14228555586⟩,
    ⟨20992,14235559746⟩,
    ⟨1296,14235932196⟩,
    ⟨1048612,8932324656⟩,
    ⟨524298,5411075376⟩,
    ⟨262153,17490732336⟩,
    ⟨196672,13020522306⟩,
    ⟨24704,13024454466⟩,
    ⟨34304,12975609636⟩,
    ⟨524321,9689326896⟩,
    ⟨266304,17490601776⟩,
    ⟨1048594,4907758896⟩,
    ⟨12292,35170383426⟩,
    ⟨800,22288995876⟩,
    ⟨114688,22281619266⟩,
    ⟨655364,9686251056⟩,
    ⟨1049601,8934348336⟩,
    ⟨272384,17740171056⟩,
    ⟨163842,15033792066⟩,
    ⟨6528,23672735586⟩,
    ⟨1544,12977640996⟩,
    ⟨98368,35166447426⟩,
    ⟨540736,9689196336⟩,
    ⟨262164,17740363056⟩,
    ⟨1049089,4907816496⟩,
    ⟨20520,14235563106⟩,
    ⟨67602,22415438946⟩,
    ⟨1179776,8931272496⟩,
    ⟨199,28037882196⟩,
    ⟨281,26885952261⟩,
    ⟨66816,14233900836⟩,
    ⟨18468,14361392226⟩,
    ⟨12320,22288627266⟩,
    ⟨35136,23673718626⟩,
    ⟨134208,14362363746⟩,
    ⟨557184,5408057136⟩,
    ⟨6156,23672747106⟩,
    ⟨561,17826255621⟩,
    ⟨24584,12977272386⟩,
    ⟨200704,12970264386⟩,
    ⟨262528,17488697136⟩,
    ⟨8896,26445166416⟩,
    ⟨1189,14630199636⟩,
    ⟨34826,23673730146⟩,
    ⟨525440,9687291696⟩,
    ⟨270338,17742263856⟩,
    ⟨1067008,8932132656⟩,
    ⟨20608,15037720386⟩,
    ⟨133134,23691621216⟩,
    ⟨10260,22414455906⟩,
    ⟨296960,17487529776⟩,
    ⟨133824,22684972896⟩,
    ⟨1900544,5138573136⟩,
    ⟨4928,26885568336⟩,
    ⟨2530,27985589616⟩], []⟩

private def p27 : Packet :=
  ⟨3, 1, 3, 7431, 9, [
    ⟨788480,12907349826⟩,
    ⟨200704,12970264386⟩,
    ⟨57344,12975179586⟩,
    ⟨1049617,9504752661⟩,
    ⟨786560,12907472706⟩,
    ⟨196864,12970387266⟩,
    ⟨1602,13026797076⟩,
    ⟨24584,12977272386⟩,
    ⟨6528,23672735586⟩,
    ⟨1048628,4970734416⟩,
    ⟨34826,23673730146⟩,
    ⟨1541,13025879316⟩,
    ⟨528418,14252274786⟩,
    ⟨37056,23642261346⟩,
    ⟨1049121,13531284501⟩,
    ⟨262172,26328200016⟩,
    ⟨35136,23673718626⟩,
    ⟨8214,26445181776⟩,
    ⟨163880,14228681826⟩,
    ⟨1115264,9500624661⟩,
    ⟨540992,5695883106⟩,
    ⟨133154,14362375266⟩,
    ⟨270656,21802010466⟩,
    ⟨1180288,13527156501⟩,
    ⟨98328,22281745506⟩,
    ⟨68160,22415427426⟩,
    ⟨21760,14235551586⟩,
    ⟨1073,9773191941⟩,
    ⟨36870,23642272866⟩,
    ⟨199,28037882196⟩,
    ⟨1310760,13430645841⟩,
    ⟨13056,22288615266⟩,
    ⟨655372,5688030306⟩,
    ⟨18468,14361392226⟩,
    ⟨1064978,9536824401⟩,
    ⟨557092,14244410466⟩,
    ⟨266816,22305326946⟩,
    ⟨1057856,9504556821⟩,
    ⟨10880,22414444386⟩,
    ⟨73920,21880653666⟩,
    ⟨19584,14361380706⟩,
    ⟨786434,12910425666⟩,
    ⟨66432,26375370576⟩,
    ⟨6156,23672747106⟩,
    ⟨331,27974967636⟩,
    ⟨1474560,9462900561⟩,
    ⟨1056802,13563356241⟩,
    ⟨147648,5774526306⟩,
    ⟨1572888,9404114001⟩,
    ⟨295552,22297462626⟩,
    ⟨692224,10252224336⟩,
    ⟨397,27968086356⟩,
    ⟨364544,26358351696⟩,
    ⟨147462,5774537826⟩,
    ⟨266258,22305338466⟩,
    ⟨65588,17852490576⟩,
    ⟨655744,5688018786⟩,
    ⟨628736,18574575456⟩,
    ⟨1179668,9529943121⟩,
    ⟨34182,19346634096⟩,
    ⟨1123,14637080916⟩,
    ⟨137242,26865730416⟩], []⟩

private def p28 : Packet :=
  ⟨3, 1, 4, 15623, 8, [
    ⟨1900544,9416763216⟩,
    ⟨184320,10807699281⟩,
    ⟨10880,22414444386⟩,
    ⟨1048632,8934351696⟩,
    ⟨270656,21802010466⟩,
    ⟨131110,10856194896⟩,
    ⟨540682,10795115601⟩,
    ⟨99072,22281733986⟩,
    ⟨6156,23672747106⟩,
    ⟨266258,22305338466⟩,
    ⟨73920,21880653666⟩,
    ⟨690176,10757629776⟩,
    ⟨68160,22415427426⟩,
    ⟨1179668,9529943121⟩,
    ⟨1077248,8934090576⟩,
    ⟨295552,22297462626⟩,
    ⟨328064,21794146146⟩,
    ⟨16434,9805325136⟩,
    ⟨524332,10758873936⟩,
    ⟨35136,23673718626⟩,
    ⟨529488,14252263026⟩,
    ⟨305152,21797832546⟩,
    ⟨6528,23672735586⟩,
    ⟨13056,22288615266⟩,
    ⟨199,28037882196⟩,
    ⟨198152,12970378866⟩,
    ⟨73734,21880665186⟩,
    ⟨266816,22305326946⟩,
    ⟨173312,14228539506⟩,
    ⟨134216,15117338226⟩,
    ⟨1312002,13162071666⟩,
    ⟨558224,14244398706⟩,
    ⟨215040,9801131856⟩,
    ⟨37056,23642261346⟩,
    ⟨787972,12907464306⟩,
    ⟨1115266,13287900786⟩,
    ⟨1065540,5239752306⟩,
    ⟨655760,5688018546⟩,
    ⟨811008,9722423121⟩,
    ⟨524330,10761823056⟩,
    ⟨397,27968086356⟩,
    ⟨1049137,13531283781⟩,
    ⟨16483,14637203781⟩,
    ⟨327692,21794157666⟩,
    ⟨575488,10791970641⟩,
    ⟨147656,6529500786⟩,
    ⟨1585152,9403918161⟩,
    ⟨17764,10810897776⟩,
    ⟨26116,13024446066⟩,
    ⟨1057875,18094358901⟩,
    ⟨281728,14327826546⟩,
    ⟨524585,14537916741⟩,
    ⟨1132544,9533679441⟩,
    ⟨165122,15033779826⟩,
    ⟨206865,17854195056⟩,
    ⟨1578624,8946858096⟩,
    ⟨33052,35468563296⟩,
    ⟨1474560,9462900561⟩,
    ⟨1836553,4888986741⟩,
    ⟨263779,14336139636⟩,
    ⟨622614,26124518256⟩], []⟩

private def p29 : Packet :=
  ⟨3, 1, 5, 32007, 7, [
    ⟨1966592,13443290976⟩,
    ⟨114712,22281618546⟩,
    ⟨6560,23672735346⟩,
    ⟨1057860,13292815986⟩,
    ⟨558210,15049508466⟩,
    ⟨147718,6529508466⟩,
    ⟨8754,17858384736⟩,
    ⟨333888,35483965281⟩,
    ⟨163944,15033787506⟩,
    ⟨262428,34666402656⟩,
    ⟨553984,9689061216⟩,
    ⟨1132672,18121512801⟩,
    ⟨6668,35752338546⟩,
    ⟨368896,35199932256⟩,
    ⟨147664,5774526066⟩,
    ⟨1118244,13237650546⟩,
    ⟨270474,34683774066⟩,
    ⟨1083712,23136847986⟩,
    ⟨198152,12970378866⟩,
    ⟨788528,12907349106⟩,
    ⟨557604,14244406386⟩,
    ⟨267282,22305334386⟩,
    ⟨606528,5693786226⟩,
    ⟨1573016,5106066546⟩,
    ⟨206851,17585825136⟩,
    ⟨311936,22297331826⟩,
    ⟨144128,22286518386⟩,
    ⟨17450,10811954016⟩,
    ⟨2134,35552121696⟩,
    ⟨165136,14228670066⟩,
    ⟨1585155,17993721201⟩,
    ⟨73952,21880653426⟩,
    ⟨1312808,13159007346⟩,
    ⟨655436,6493135986⟩,
    ⟨99074,35166439026⟩,
    ⟨11284,22414451826⟩,
    ⟨1474565,13961291121⟩,
    ⟨1065544,5192566386⟩,
    ⟨133666,14362371186⟩,
    ⟨787972,12907464306⟩,
    ⟨529488,14252263026⟩,
    ⟨983073,9714558321⟩,
    ⟨307264,34682853216⟩,
    ⟨12440,35170378866⟩,
    ⟨1312002,13162071666⟩,
    ⟨157729,9799165296⟩,
    ⟨1049140,4970730336⟩,
    ⟨576512,10791966561⟩,
    ⟨1119360,13237635186⟩,
    ⟨266514,35205960801⟩,
    ⟨524588,6480679776⟩,
    ⟨811264,12927129441⟩,
    ⟨108608,34698581856⟩,
    ⟨806915,5427586416⟩,
    ⟨66873,14233899636⟩], []⟩

private def p30 : Packet :=
  ⟨3, 2, 0, 775, 11, [
    ⟨1638400,9955477296⟩,
    ⟨425984,5991860016⟩,
    ⟨25600,21818926896⟩,
    ⟨6656,35752339236⟩,
    ⟨1048616,8963781936⟩,
    ⟨524672,5409101616⟩,
    ⟨65554,17852429616⟩,
    ⟨131077,5505508656⟩,
    ⟨262464,17490663216⟩,
    ⟨32960,19346642736⟩,
    ⟨16420,9804281136⟩,
    ⟨8209,17858389296⟩,
    ⟨2058,19429225776⟩,
    ⟨529408,22590613296⟩,
    ⟨262784,17740355376⟩,
    ⟨33536,18825631536⟩,
    ⟨1069056,8963589936⟩,
    ⟨68608,22415435556⟩,
    ⟨8226,26113897776⟩,
    ⟨1048596,4905792816⟩,
    ⟨196616,12970391076⟩,
    ⟨16449,5510420016⟩,
    ⟨12292,35170383396⟩,
    ⟨131120,10269259056⟩,
    ⟨262153,17490732336⟩,
    ⟨559104,5407934256⟩,
    ⟨1179650,5234849316⟩,
    ⟨4480,19367286576⟩,
    ⟨524312,5943883056⟩,
    ⟨1049601,8934348336⟩,
    ⟨66112,17852421936⟩,
    ⟨280576,14327842596⟩,
    ⟨32774,19346650416⟩,
    ⟨133184,5505378096⟩,
    ⟨524321,9689326896⟩,
    ⟨10496,35249022756⟩,
    ⟨16394,5477922096⟩,
    ⟨36880,35721868836⟩,
    ⟨132608,10269251376⟩,
    ⟨65665,17585100336⟩,
    ⟨3136,26978965296⟩,
    ⟨327712,21794158116⟩,
    ⟨541184,5695891236⟩,
    ⟨1056776,13245642276⟩,
    ⟨34048,26878695216⟩,
    ⟨4099,19351627056⟩,
    ⟨786496,12910421796⟩,
    ⟨2688,18926884656⟩,
    ⟨4136,26885584176⟩,
    ⟨262164,17740363056⟩,
    ⟨8512,17557509936⟩,
    ⟨1310722,13162083876⟩,
    ⟨74752,21880661796⟩,
    ⟨1817,22288998726⟩,
    ⟨1083392,23136864036⟩,
    ⟨1223,23742914886⟩,
    ⟨534528,22380906276⟩,
    ⟨397312,22303246116⟩,
    ⟨98560,17534838576⟩,
    ⟨921,35170754886⟩,
    ⟨1065472,10007701296⟩], [⟨15,2046⟩]⟩

private def p31 : Packet :=
  ⟨3, 2, 1, 1799, 10, [
    ⟨1581056,9953511216⟩,
    ⟨344064,21794031396⟩,
    ⟨167936,5455120176⟩,
    ⟨1049856,8963774256⟩,
    ⟨524336,10222073136⟩,
    ⟨10248,35249026626⟩,
    ⟨262784,17740355376⟩,
    ⟨65542,17585042736⟩,
    ⟨147520,9799296816⟩,
    ⟨32897,19346708016⟩,
    ⟨6656,35752339266⟩,
    ⟨262153,17490732336⟩,
    ⟨33088,19362371376⟩,
    ⟨1048612,8932324656⟩,
    ⟨13312,22288623426⟩,
    ⟨133122,5505381936⟩,
    ⟨65560,17819006256⟩,
    ⟨540674,9689200176⟩,
    ⟨66049,17852487216⟩,
    ⟨262164,17740363056⟩,
    ⟨131456,5472016176⟩,
    ⟨525376,9689257776⟩,
    ⟨1048594,4907758896⟩,
    ⟨24832,12977268546⟩,
    ⟨32808,26878702896⟩,
    ⟨20608,15037720386⟩,
    ⟨10272,22414456386⟩,
    ⟨132608,10269251376⟩,
    ⟨266304,17490601776⟩,
    ⟨524300,5409109296⟩,
    ⟨18448,14361392706⟩,
    ⟨4138,18832520016⟩,
    ⟨1049664,8934283056⟩,
    ⟨524545,5411132976⟩,
    ⟨17984,9772808016⟩,
    ⟨71680,17551427376⟩,
    ⟨8896,26445166416⟩,
    ⟨2496,27986573136⟩,
    ⟨8242,17825887056⟩,
    ⟨34048,26878695216⟩,
    ⟨1049152,4907751216⟩,
    ⟨797,35170751046⟩,
    ⟨131105,9799427376⟩,
    ⟨1191,15150158406⟩,
    ⟨270338,17742263856⟩,
    ⟨603,35256275556⟩], []⟩

private def p32 : Packet :=
  ⟨3, 2, 2, 3847, 9, [
    ⟨1574912,5105944386⟩,
    ⟨327808,17739310896⟩,
    ⟨172032,14228555586⟩,
    ⟨20992,14235559746⟩,
    ⟨1049664,8934283056⟩,
    ⟨524545,5411132976⟩,
    ⟨262164,17740363056⟩,
    ⟨196616,12970391106⟩,
    ⟨12320,22288627266⟩,
    ⟨98306,35166451266⟩,
    ⟨262154,17490670896⟩,
    ⟨24704,13024454466⟩,
    ⟨1048609,8934352176⟩,
    ⟨525376,9689257776⟩,
    ⟨163856,14228682306⟩,
    ⟨6528,23672735586⟩,
    ⟨524324,9687299376⟩,
    ⟨9024,26382251856⟩,
    ⟨1048596,4905792816⟩,
    ⟨262657,17742386736⟩,
    ⟨18468,14361392226⟩,
    ⟨196610,13020526146⟩,
    ⟨34176,18825623376⟩,
    ⟨6156,23672747106⟩,
    ⟨24832,12977268546⟩,
    ⟨8218,26382267216⟩,
    ⟨147648,5774526306⟩,
    ⟨98328,22281745506⟩,
    ⟨16434,9772823376⟩,
    ⟨132736,9765926736⟩,
    ⟨67200,17818990416⟩,
    ⟨163904,15033788226⟩,
    ⟨603,35256275556⟩,
    ⟨557184,5408057136⟩,
    ⟨1385,15040061766⟩,
    ⟨1049216,4905785136⟩,
    ⟨3158,26978964336⟩,
    ⟨1310724,13159134786⟩,
    ⟨20496,14235563586⟩,
    ⟨11456,18657458016⟩,
    ⟨68160,22415427426⟩,
    ⟨131795,26714579316⟩,
    ⟨133134,23691621216⟩], []⟩

private def p33 : Packet :=
  ⟨3, 2, 3, 7943, 8, [
    ⟨788480,12907349826⟩,
    ⟨200704,12970264386⟩,
    ⟨57344,12975179586⟩,
    ⟨525696,10222057296⟩,
    ⟨262172,26328200016⟩,
    ⟨196672,13020522306⟩,
    ⟨16426,10276139856⟩,
    ⟨37056,23642261346⟩,
    ⟨13056,22288615266⟩,
    ⟨8214,26445181776⟩,
    ⟨19584,14361380706⟩,
    ⟨557092,14244410466⟩,
    ⟨262976,26332116816⟩,
    ⟨34826,23673730146⟩,
    ⟨529472,14252263266⟩,
    ⟨66432,26375370576⟩,
    ⟨24584,12977272386⟩,
    ⟨133154,14362375266⟩,
    ⟨786434,12910425666⟩,
    ⟨165120,14228670306⟩,
    ⟨6156,23672747106⟩,
    ⟨67602,22415438946⟩,
    ⟨8896,26445166416⟩,
    ⟨98328,22281745506⟩,
    ⟨1065540,5239752306⟩,
    ⟨1114404,13237773426⟩,
    ⟨1180296,5184702066⟩,
    ⟨1331217,13430449521⟩,
    ⟨276480,26327877456⟩,
    ⟨1589,13024825926⟩,
    ⟨1056930,13292823666⟩,
    ⟨36870,23642272866⟩,
    ⟨540992,5695883106⟩,
    ⟨1057864,13245630066⟩,
    ⟨1179924,5184709746⟩,
    ⟨163880,14228681826⟩,
    ⟨21760,14235551586⟩,
    ⟨295552,22297462626⟩,
    ⟨1254401,9530791536⟩,
    ⟨1585280,5105805426⟩,
    ⟨1223,23742914916⟩,
    ⟨1049266,4972630896⟩,
    ⟨1090624,13243533426⟩,
    ⟨1133057,13556274801⟩,
    ⟨1310888,13159130226⟩,
    ⟨1097746,5190485106⟩,
    ⟨9577,14504239476⟩,
    ⟨1851409,13447226736⟩,
    ⟨6528,23672735586⟩,
    ⟨524957,26659525236⟩,
    ⟨1181332,9496433781⟩,
    ⟨263589,14579933556⟩], []⟩

private def p34 : Packet :=
  ⟨3, 2, 4, 16135, 7, [
    ⟨333824,21793900386⟩,
    ⟨295552,22297462626⟩,
    ⟨73734,21880665186⟩,
    ⟨35136,23673718626⟩,
    ⟨12312,22288626786⟩,
    ⟨270656,21802010466⟩,
    ⟨98328,22281745506⟩,
    ⟨528930,14252270706⟩,
    ⟨1065106,5239759986⟩,
    ⟨655436,6493135986⟩,
    ⟨10880,22414444386⟩,
    ⟨21764,15037711986⟩,
    ⟨305152,21797832546⟩,
    ⟨196912,12970386546⟩,
    ⟨1115272,13237765746⟩,
    ⟨1065540,5239752306⟩,
    ⟨693249,10789082736⟩,
    ⟨395298,14328824946⟩,
    ⟨541194,5695890546⟩,
    ⟨37056,23642261346⟩,
    ⟨1573636,5106058866⟩,
    ⟨134224,14362363506⟩,
    ⟨429,23673115236⟩,
    ⟨1138721,9533744496⟩,
    ⟨165122,15033779826⟩,
    ⟨786544,12910421106⟩,
    ⟨20648,15037719666⟩,
    ⟨266258,22305338466⟩,
    ⟨1198085,14095050096⟩,
    ⟨164392,14228677746⟩,
    ⟨606528,5693786226⟩,
    ⟨67602,22415438946⟩,
    ⟨812033,9722418801⟩,
    ⟨565284,14244283506⟩,
    ⟨1057864,13245630066⟩,
    ⟨6528,23672735586⟩,
    ⟨327692,21794157666⟩,
    ⟨202240,12970248306⟩,
    ⟨576513,10791966321⟩,
    ⟨1966337,13191632496⟩,
    ⟨132336,10336089456⟩,
    ⟨1310748,22033232736⟩,
    ⟨66787,14634983796⟩,
    ⟨34357,12991337076⟩,
    ⟨1332992,13428332661⟩], []⟩

private def p35 : Packet :=
  ⟨3, 2, 5, 32519, 6, [
    ⟨1671232,5104822386⟩,
    ⟨409606,5740987506⟩,
    ⟨13336,22288622706⟩,
    ⟨10912,22414444146⟩,
    ⟨1314048,13158991986⟩,
    ⟨655760,5688018546⟩,
    ⟨86056,14233470066⟩,
    ⟨37382,35721864306⟩,
    ⟨163944,15033787506⟩,
    ⟨73990,34715231346⟩,
    ⟨311936,22297331826⟩,
    ⟨786544,12910421106⟩,
    ⟨68626,22415434866⟩,
    ⟨1204737,13560272496⟩,
    ⟨1054732,23135880306⟩,
    ⟨540996,6498043506⟩,
    ⟨202240,12970248306⟩,
    ⟨57392,12975178866⟩,
    ⟨270474,34683774066⟩,
    ⟨35338,35753321586⟩,
    ⟨328096,21794145906⟩,
    ⟨1198209,14095046256⟩,
    ⟨491537,17737213296⟩,
    ⟨1057860,13292815986⟩,
    ⟨661569,19377837681⟩,
    ⟨1065234,5192574066⟩,
    ⟨566400,14244268146⟩,
    ⟨525868,10222064496⟩,
    ⟨6544,35752330866⟩,
    ⟨337985,35233355376⟩,
    ⟨1316480,4920326256⟩,
    ⟨1585665,13497292401⟩,
    ⟨99224,26577736821⟩], []⟩

private def bank : Fin 36 → Packet := ![p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31, p32, p33, p34, p35]

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f0 : PLift (fitted p0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_0 : PLift (covers (masks p0) 15 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_1 : PLift (covers (masks p0) 15 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_2 : PLift (covers (masks p0) 15 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_3 : PLift (covers (masks p0) 15 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_4 : PLift (covers (masks p0) 15 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_5 : PLift (covers (masks p0) 15 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_6 : PLift (covers (masks p0) 15 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_7 : PLift (covers (masks p0) 15 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_8 : PLift (covers (masks p0) 15 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_9 : PLift (covers (masks p0) 15 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_10 : PLift (covers (masks p0) 15 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_11 : PLift (covers (masks p0) 15 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_12 : PLift (covers (masks p0) 15 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_13 : PLift (covers (masks p0) 15 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_14 : PLift (covers (masks p0) 15 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_15 : PLift (covers (masks p0) 15 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_16 : PLift (covers (masks p0) 15 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_17 : PLift (covers (masks p0) 15 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_18 : PLift (covers (masks p0) 15 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_19 : PLift (covers (masks p0) 15 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_20 : PLift (covers (masks p0) 15 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_21 : PLift (covers (masks p0) 15 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_22 : PLift (covers (masks p0) 15 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_23 : PLift (covers (masks p0) 15 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_24 : PLift (covers (masks p0) 15 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_25 : PLift (covers (masks p0) 15 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_26 : PLift (covers (masks p0) 15 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_27 : PLift (covers (masks p0) 15 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_28 : PLift (covers (masks p0) 15 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_29 : PLift (covers (masks p0) 15 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_30 : PLift (covers (masks p0) 15 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c0_31 : PLift (covers (masks p0) 15 31) := ⟨by decide +kernel⟩

private theorem c0 (i : Fin 32) : covers (masks p0) p0.residual i.val := by
  fin_cases i
  · exact c0_0.down
  · exact c0_1.down
  · exact c0_2.down
  · exact c0_3.down
  · exact c0_4.down
  · exact c0_5.down
  · exact c0_6.down
  · exact c0_7.down
  · exact c0_8.down
  · exact c0_9.down
  · exact c0_10.down
  · exact c0_11.down
  · exact c0_12.down
  · exact c0_13.down
  · exact c0_14.down
  · exact c0_15.down
  · exact c0_16.down
  · exact c0_17.down
  · exact c0_18.down
  · exact c0_19.down
  · exact c0_20.down
  · exact c0_21.down
  · exact c0_22.down
  · exact c0_23.down
  · exact c0_24.down
  · exact c0_25.down
  · exact c0_26.down
  · exact c0_27.down
  · exact c0_28.down
  · exact c0_29.down
  · exact c0_30.down
  · exact c0_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f1 : PLift (fitted p1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_0 : PLift (covers (masks p1) 14 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_1 : PLift (covers (masks p1) 14 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_2 : PLift (covers (masks p1) 14 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_3 : PLift (covers (masks p1) 14 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_4 : PLift (covers (masks p1) 14 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_5 : PLift (covers (masks p1) 14 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_6 : PLift (covers (masks p1) 14 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_7 : PLift (covers (masks p1) 14 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_8 : PLift (covers (masks p1) 14 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_9 : PLift (covers (masks p1) 14 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_10 : PLift (covers (masks p1) 14 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_11 : PLift (covers (masks p1) 14 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_12 : PLift (covers (masks p1) 14 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_13 : PLift (covers (masks p1) 14 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_14 : PLift (covers (masks p1) 14 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_15 : PLift (covers (masks p1) 14 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_16 : PLift (covers (masks p1) 14 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_17 : PLift (covers (masks p1) 14 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_18 : PLift (covers (masks p1) 14 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_19 : PLift (covers (masks p1) 14 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_20 : PLift (covers (masks p1) 14 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_21 : PLift (covers (masks p1) 14 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_22 : PLift (covers (masks p1) 14 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_23 : PLift (covers (masks p1) 14 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_24 : PLift (covers (masks p1) 14 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_25 : PLift (covers (masks p1) 14 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_26 : PLift (covers (masks p1) 14 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_27 : PLift (covers (masks p1) 14 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_28 : PLift (covers (masks p1) 14 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_29 : PLift (covers (masks p1) 14 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_30 : PLift (covers (masks p1) 14 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c1_31 : PLift (covers (masks p1) 14 31) := ⟨by decide +kernel⟩

private theorem c1 (i : Fin 32) : covers (masks p1) p1.residual i.val := by
  fin_cases i
  · exact c1_0.down
  · exact c1_1.down
  · exact c1_2.down
  · exact c1_3.down
  · exact c1_4.down
  · exact c1_5.down
  · exact c1_6.down
  · exact c1_7.down
  · exact c1_8.down
  · exact c1_9.down
  · exact c1_10.down
  · exact c1_11.down
  · exact c1_12.down
  · exact c1_13.down
  · exact c1_14.down
  · exact c1_15.down
  · exact c1_16.down
  · exact c1_17.down
  · exact c1_18.down
  · exact c1_19.down
  · exact c1_20.down
  · exact c1_21.down
  · exact c1_22.down
  · exact c1_23.down
  · exact c1_24.down
  · exact c1_25.down
  · exact c1_26.down
  · exact c1_27.down
  · exact c1_28.down
  · exact c1_29.down
  · exact c1_30.down
  · exact c1_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f2 : PLift (fitted p2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_0 : PLift (covers (masks p2) 13 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_1 : PLift (covers (masks p2) 13 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_2 : PLift (covers (masks p2) 13 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_3 : PLift (covers (masks p2) 13 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_4 : PLift (covers (masks p2) 13 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_5 : PLift (covers (masks p2) 13 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_6 : PLift (covers (masks p2) 13 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_7 : PLift (covers (masks p2) 13 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_8 : PLift (covers (masks p2) 13 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_9 : PLift (covers (masks p2) 13 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_10 : PLift (covers (masks p2) 13 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_11 : PLift (covers (masks p2) 13 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_12 : PLift (covers (masks p2) 13 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_13 : PLift (covers (masks p2) 13 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_14 : PLift (covers (masks p2) 13 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_15 : PLift (covers (masks p2) 13 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_16 : PLift (covers (masks p2) 13 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_17 : PLift (covers (masks p2) 13 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_18 : PLift (covers (masks p2) 13 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_19 : PLift (covers (masks p2) 13 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_20 : PLift (covers (masks p2) 13 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_21 : PLift (covers (masks p2) 13 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_22 : PLift (covers (masks p2) 13 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_23 : PLift (covers (masks p2) 13 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_24 : PLift (covers (masks p2) 13 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_25 : PLift (covers (masks p2) 13 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_26 : PLift (covers (masks p2) 13 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_27 : PLift (covers (masks p2) 13 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_28 : PLift (covers (masks p2) 13 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_29 : PLift (covers (masks p2) 13 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_30 : PLift (covers (masks p2) 13 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c2_31 : PLift (covers (masks p2) 13 31) := ⟨by decide +kernel⟩

private theorem c2 (i : Fin 32) : covers (masks p2) p2.residual i.val := by
  fin_cases i
  · exact c2_0.down
  · exact c2_1.down
  · exact c2_2.down
  · exact c2_3.down
  · exact c2_4.down
  · exact c2_5.down
  · exact c2_6.down
  · exact c2_7.down
  · exact c2_8.down
  · exact c2_9.down
  · exact c2_10.down
  · exact c2_11.down
  · exact c2_12.down
  · exact c2_13.down
  · exact c2_14.down
  · exact c2_15.down
  · exact c2_16.down
  · exact c2_17.down
  · exact c2_18.down
  · exact c2_19.down
  · exact c2_20.down
  · exact c2_21.down
  · exact c2_22.down
  · exact c2_23.down
  · exact c2_24.down
  · exact c2_25.down
  · exact c2_26.down
  · exact c2_27.down
  · exact c2_28.down
  · exact c2_29.down
  · exact c2_30.down
  · exact c2_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f3 : PLift (fitted p3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_0 : PLift (covers (masks p3) 12 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_1 : PLift (covers (masks p3) 12 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_2 : PLift (covers (masks p3) 12 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_3 : PLift (covers (masks p3) 12 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_4 : PLift (covers (masks p3) 12 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_5 : PLift (covers (masks p3) 12 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_6 : PLift (covers (masks p3) 12 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_7 : PLift (covers (masks p3) 12 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_8 : PLift (covers (masks p3) 12 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_9 : PLift (covers (masks p3) 12 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_10 : PLift (covers (masks p3) 12 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_11 : PLift (covers (masks p3) 12 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_12 : PLift (covers (masks p3) 12 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_13 : PLift (covers (masks p3) 12 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_14 : PLift (covers (masks p3) 12 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_15 : PLift (covers (masks p3) 12 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_16 : PLift (covers (masks p3) 12 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_17 : PLift (covers (masks p3) 12 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_18 : PLift (covers (masks p3) 12 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_19 : PLift (covers (masks p3) 12 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_20 : PLift (covers (masks p3) 12 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_21 : PLift (covers (masks p3) 12 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_22 : PLift (covers (masks p3) 12 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_23 : PLift (covers (masks p3) 12 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_24 : PLift (covers (masks p3) 12 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_25 : PLift (covers (masks p3) 12 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_26 : PLift (covers (masks p3) 12 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_27 : PLift (covers (masks p3) 12 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_28 : PLift (covers (masks p3) 12 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_29 : PLift (covers (masks p3) 12 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_30 : PLift (covers (masks p3) 12 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c3_31 : PLift (covers (masks p3) 12 31) := ⟨by decide +kernel⟩

private theorem c3 (i : Fin 32) : covers (masks p3) p3.residual i.val := by
  fin_cases i
  · exact c3_0.down
  · exact c3_1.down
  · exact c3_2.down
  · exact c3_3.down
  · exact c3_4.down
  · exact c3_5.down
  · exact c3_6.down
  · exact c3_7.down
  · exact c3_8.down
  · exact c3_9.down
  · exact c3_10.down
  · exact c3_11.down
  · exact c3_12.down
  · exact c3_13.down
  · exact c3_14.down
  · exact c3_15.down
  · exact c3_16.down
  · exact c3_17.down
  · exact c3_18.down
  · exact c3_19.down
  · exact c3_20.down
  · exact c3_21.down
  · exact c3_22.down
  · exact c3_23.down
  · exact c3_24.down
  · exact c3_25.down
  · exact c3_26.down
  · exact c3_27.down
  · exact c3_28.down
  · exact c3_29.down
  · exact c3_30.down
  · exact c3_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f4 : PLift (fitted p4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_0 : PLift (covers (masks p4) 11 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_1 : PLift (covers (masks p4) 11 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_2 : PLift (covers (masks p4) 11 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_3 : PLift (covers (masks p4) 11 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_4 : PLift (covers (masks p4) 11 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_5 : PLift (covers (masks p4) 11 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_6 : PLift (covers (masks p4) 11 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_7 : PLift (covers (masks p4) 11 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_8 : PLift (covers (masks p4) 11 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_9 : PLift (covers (masks p4) 11 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_10 : PLift (covers (masks p4) 11 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_11 : PLift (covers (masks p4) 11 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_12 : PLift (covers (masks p4) 11 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_13 : PLift (covers (masks p4) 11 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_14 : PLift (covers (masks p4) 11 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_15 : PLift (covers (masks p4) 11 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_16 : PLift (covers (masks p4) 11 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_17 : PLift (covers (masks p4) 11 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_18 : PLift (covers (masks p4) 11 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_19 : PLift (covers (masks p4) 11 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_20 : PLift (covers (masks p4) 11 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_21 : PLift (covers (masks p4) 11 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_22 : PLift (covers (masks p4) 11 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_23 : PLift (covers (masks p4) 11 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_24 : PLift (covers (masks p4) 11 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_25 : PLift (covers (masks p4) 11 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_26 : PLift (covers (masks p4) 11 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_27 : PLift (covers (masks p4) 11 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_28 : PLift (covers (masks p4) 11 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_29 : PLift (covers (masks p4) 11 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_30 : PLift (covers (masks p4) 11 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c4_31 : PLift (covers (masks p4) 11 31) := ⟨by decide +kernel⟩

private theorem c4 (i : Fin 32) : covers (masks p4) p4.residual i.val := by
  fin_cases i
  · exact c4_0.down
  · exact c4_1.down
  · exact c4_2.down
  · exact c4_3.down
  · exact c4_4.down
  · exact c4_5.down
  · exact c4_6.down
  · exact c4_7.down
  · exact c4_8.down
  · exact c4_9.down
  · exact c4_10.down
  · exact c4_11.down
  · exact c4_12.down
  · exact c4_13.down
  · exact c4_14.down
  · exact c4_15.down
  · exact c4_16.down
  · exact c4_17.down
  · exact c4_18.down
  · exact c4_19.down
  · exact c4_20.down
  · exact c4_21.down
  · exact c4_22.down
  · exact c4_23.down
  · exact c4_24.down
  · exact c4_25.down
  · exact c4_26.down
  · exact c4_27.down
  · exact c4_28.down
  · exact c4_29.down
  · exact c4_30.down
  · exact c4_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f5 : PLift (fitted p5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_0 : PLift (covers (masks p5) 10 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_1 : PLift (covers (masks p5) 10 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_2 : PLift (covers (masks p5) 10 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_3 : PLift (covers (masks p5) 10 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_4 : PLift (covers (masks p5) 10 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_5 : PLift (covers (masks p5) 10 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_6 : PLift (covers (masks p5) 10 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_7 : PLift (covers (masks p5) 10 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_8 : PLift (covers (masks p5) 10 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_9 : PLift (covers (masks p5) 10 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_10 : PLift (covers (masks p5) 10 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_11 : PLift (covers (masks p5) 10 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_12 : PLift (covers (masks p5) 10 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_13 : PLift (covers (masks p5) 10 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_14 : PLift (covers (masks p5) 10 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_15 : PLift (covers (masks p5) 10 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_16 : PLift (covers (masks p5) 10 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_17 : PLift (covers (masks p5) 10 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_18 : PLift (covers (masks p5) 10 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_19 : PLift (covers (masks p5) 10 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_20 : PLift (covers (masks p5) 10 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_21 : PLift (covers (masks p5) 10 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_22 : PLift (covers (masks p5) 10 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_23 : PLift (covers (masks p5) 10 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_24 : PLift (covers (masks p5) 10 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_25 : PLift (covers (masks p5) 10 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_26 : PLift (covers (masks p5) 10 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_27 : PLift (covers (masks p5) 10 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_28 : PLift (covers (masks p5) 10 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_29 : PLift (covers (masks p5) 10 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_30 : PLift (covers (masks p5) 10 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c5_31 : PLift (covers (masks p5) 10 31) := ⟨by decide +kernel⟩

private theorem c5 (i : Fin 32) : covers (masks p5) p5.residual i.val := by
  fin_cases i
  · exact c5_0.down
  · exact c5_1.down
  · exact c5_2.down
  · exact c5_3.down
  · exact c5_4.down
  · exact c5_5.down
  · exact c5_6.down
  · exact c5_7.down
  · exact c5_8.down
  · exact c5_9.down
  · exact c5_10.down
  · exact c5_11.down
  · exact c5_12.down
  · exact c5_13.down
  · exact c5_14.down
  · exact c5_15.down
  · exact c5_16.down
  · exact c5_17.down
  · exact c5_18.down
  · exact c5_19.down
  · exact c5_20.down
  · exact c5_21.down
  · exact c5_22.down
  · exact c5_23.down
  · exact c5_24.down
  · exact c5_25.down
  · exact c5_26.down
  · exact c5_27.down
  · exact c5_28.down
  · exact c5_29.down
  · exact c5_30.down
  · exact c5_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f6 : PLift (fitted p6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_0 : PLift (covers (masks p6) 9 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_1 : PLift (covers (masks p6) 9 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_2 : PLift (covers (masks p6) 9 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_3 : PLift (covers (masks p6) 9 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_4 : PLift (covers (masks p6) 9 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_5 : PLift (covers (masks p6) 9 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_6 : PLift (covers (masks p6) 9 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_7 : PLift (covers (masks p6) 9 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_8 : PLift (covers (masks p6) 9 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_9 : PLift (covers (masks p6) 9 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_10 : PLift (covers (masks p6) 9 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_11 : PLift (covers (masks p6) 9 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_12 : PLift (covers (masks p6) 9 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_13 : PLift (covers (masks p6) 9 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_14 : PLift (covers (masks p6) 9 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_15 : PLift (covers (masks p6) 9 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_16 : PLift (covers (masks p6) 9 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_17 : PLift (covers (masks p6) 9 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_18 : PLift (covers (masks p6) 9 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_19 : PLift (covers (masks p6) 9 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_20 : PLift (covers (masks p6) 9 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_21 : PLift (covers (masks p6) 9 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_22 : PLift (covers (masks p6) 9 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_23 : PLift (covers (masks p6) 9 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_24 : PLift (covers (masks p6) 9 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_25 : PLift (covers (masks p6) 9 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_26 : PLift (covers (masks p6) 9 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_27 : PLift (covers (masks p6) 9 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_28 : PLift (covers (masks p6) 9 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_29 : PLift (covers (masks p6) 9 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_30 : PLift (covers (masks p6) 9 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c6_31 : PLift (covers (masks p6) 9 31) := ⟨by decide +kernel⟩

private theorem c6 (i : Fin 32) : covers (masks p6) p6.residual i.val := by
  fin_cases i
  · exact c6_0.down
  · exact c6_1.down
  · exact c6_2.down
  · exact c6_3.down
  · exact c6_4.down
  · exact c6_5.down
  · exact c6_6.down
  · exact c6_7.down
  · exact c6_8.down
  · exact c6_9.down
  · exact c6_10.down
  · exact c6_11.down
  · exact c6_12.down
  · exact c6_13.down
  · exact c6_14.down
  · exact c6_15.down
  · exact c6_16.down
  · exact c6_17.down
  · exact c6_18.down
  · exact c6_19.down
  · exact c6_20.down
  · exact c6_21.down
  · exact c6_22.down
  · exact c6_23.down
  · exact c6_24.down
  · exact c6_25.down
  · exact c6_26.down
  · exact c6_27.down
  · exact c6_28.down
  · exact c6_29.down
  · exact c6_30.down
  · exact c6_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f7 : PLift (fitted p7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_0 : PLift (covers (masks p7) 8 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_1 : PLift (covers (masks p7) 8 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_2 : PLift (covers (masks p7) 8 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_3 : PLift (covers (masks p7) 8 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_4 : PLift (covers (masks p7) 8 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_5 : PLift (covers (masks p7) 8 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_6 : PLift (covers (masks p7) 8 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_7 : PLift (covers (masks p7) 8 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_8 : PLift (covers (masks p7) 8 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_9 : PLift (covers (masks p7) 8 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_10 : PLift (covers (masks p7) 8 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_11 : PLift (covers (masks p7) 8 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_12 : PLift (covers (masks p7) 8 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_13 : PLift (covers (masks p7) 8 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_14 : PLift (covers (masks p7) 8 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_15 : PLift (covers (masks p7) 8 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_16 : PLift (covers (masks p7) 8 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_17 : PLift (covers (masks p7) 8 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_18 : PLift (covers (masks p7) 8 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_19 : PLift (covers (masks p7) 8 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_20 : PLift (covers (masks p7) 8 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_21 : PLift (covers (masks p7) 8 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_22 : PLift (covers (masks p7) 8 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_23 : PLift (covers (masks p7) 8 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_24 : PLift (covers (masks p7) 8 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_25 : PLift (covers (masks p7) 8 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_26 : PLift (covers (masks p7) 8 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_27 : PLift (covers (masks p7) 8 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_28 : PLift (covers (masks p7) 8 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_29 : PLift (covers (masks p7) 8 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_30 : PLift (covers (masks p7) 8 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c7_31 : PLift (covers (masks p7) 8 31) := ⟨by decide +kernel⟩

private theorem c7 (i : Fin 32) : covers (masks p7) p7.residual i.val := by
  fin_cases i
  · exact c7_0.down
  · exact c7_1.down
  · exact c7_2.down
  · exact c7_3.down
  · exact c7_4.down
  · exact c7_5.down
  · exact c7_6.down
  · exact c7_7.down
  · exact c7_8.down
  · exact c7_9.down
  · exact c7_10.down
  · exact c7_11.down
  · exact c7_12.down
  · exact c7_13.down
  · exact c7_14.down
  · exact c7_15.down
  · exact c7_16.down
  · exact c7_17.down
  · exact c7_18.down
  · exact c7_19.down
  · exact c7_20.down
  · exact c7_21.down
  · exact c7_22.down
  · exact c7_23.down
  · exact c7_24.down
  · exact c7_25.down
  · exact c7_26.down
  · exact c7_27.down
  · exact c7_28.down
  · exact c7_29.down
  · exact c7_30.down
  · exact c7_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f8 : PLift (fitted p8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_0 : PLift (covers (masks p8) 13 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_1 : PLift (covers (masks p8) 13 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_2 : PLift (covers (masks p8) 13 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_3 : PLift (covers (masks p8) 13 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_4 : PLift (covers (masks p8) 13 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_5 : PLift (covers (masks p8) 13 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_6 : PLift (covers (masks p8) 13 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_7 : PLift (covers (masks p8) 13 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_8 : PLift (covers (masks p8) 13 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_9 : PLift (covers (masks p8) 13 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_10 : PLift (covers (masks p8) 13 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_11 : PLift (covers (masks p8) 13 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_12 : PLift (covers (masks p8) 13 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_13 : PLift (covers (masks p8) 13 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_14 : PLift (covers (masks p8) 13 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_15 : PLift (covers (masks p8) 13 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_16 : PLift (covers (masks p8) 13 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_17 : PLift (covers (masks p8) 13 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_18 : PLift (covers (masks p8) 13 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_19 : PLift (covers (masks p8) 13 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_20 : PLift (covers (masks p8) 13 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_21 : PLift (covers (masks p8) 13 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_22 : PLift (covers (masks p8) 13 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_23 : PLift (covers (masks p8) 13 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_24 : PLift (covers (masks p8) 13 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_25 : PLift (covers (masks p8) 13 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_26 : PLift (covers (masks p8) 13 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_27 : PLift (covers (masks p8) 13 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_28 : PLift (covers (masks p8) 13 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_29 : PLift (covers (masks p8) 13 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_30 : PLift (covers (masks p8) 13 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c8_31 : PLift (covers (masks p8) 13 31) := ⟨by decide +kernel⟩

private theorem c8 (i : Fin 32) : covers (masks p8) p8.residual i.val := by
  fin_cases i
  · exact c8_0.down
  · exact c8_1.down
  · exact c8_2.down
  · exact c8_3.down
  · exact c8_4.down
  · exact c8_5.down
  · exact c8_6.down
  · exact c8_7.down
  · exact c8_8.down
  · exact c8_9.down
  · exact c8_10.down
  · exact c8_11.down
  · exact c8_12.down
  · exact c8_13.down
  · exact c8_14.down
  · exact c8_15.down
  · exact c8_16.down
  · exact c8_17.down
  · exact c8_18.down
  · exact c8_19.down
  · exact c8_20.down
  · exact c8_21.down
  · exact c8_22.down
  · exact c8_23.down
  · exact c8_24.down
  · exact c8_25.down
  · exact c8_26.down
  · exact c8_27.down
  · exact c8_28.down
  · exact c8_29.down
  · exact c8_30.down
  · exact c8_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f9 : PLift (fitted p9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_0 : PLift (covers (masks p9) 12 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_1 : PLift (covers (masks p9) 12 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_2 : PLift (covers (masks p9) 12 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_3 : PLift (covers (masks p9) 12 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_4 : PLift (covers (masks p9) 12 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_5 : PLift (covers (masks p9) 12 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_6 : PLift (covers (masks p9) 12 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_7 : PLift (covers (masks p9) 12 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_8 : PLift (covers (masks p9) 12 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_9 : PLift (covers (masks p9) 12 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_10 : PLift (covers (masks p9) 12 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_11 : PLift (covers (masks p9) 12 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_12 : PLift (covers (masks p9) 12 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_13 : PLift (covers (masks p9) 12 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_14 : PLift (covers (masks p9) 12 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_15 : PLift (covers (masks p9) 12 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_16 : PLift (covers (masks p9) 12 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_17 : PLift (covers (masks p9) 12 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_18 : PLift (covers (masks p9) 12 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_19 : PLift (covers (masks p9) 12 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_20 : PLift (covers (masks p9) 12 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_21 : PLift (covers (masks p9) 12 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_22 : PLift (covers (masks p9) 12 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_23 : PLift (covers (masks p9) 12 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_24 : PLift (covers (masks p9) 12 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_25 : PLift (covers (masks p9) 12 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_26 : PLift (covers (masks p9) 12 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_27 : PLift (covers (masks p9) 12 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_28 : PLift (covers (masks p9) 12 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_29 : PLift (covers (masks p9) 12 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_30 : PLift (covers (masks p9) 12 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c9_31 : PLift (covers (masks p9) 12 31) := ⟨by decide +kernel⟩

private theorem c9 (i : Fin 32) : covers (masks p9) p9.residual i.val := by
  fin_cases i
  · exact c9_0.down
  · exact c9_1.down
  · exact c9_2.down
  · exact c9_3.down
  · exact c9_4.down
  · exact c9_5.down
  · exact c9_6.down
  · exact c9_7.down
  · exact c9_8.down
  · exact c9_9.down
  · exact c9_10.down
  · exact c9_11.down
  · exact c9_12.down
  · exact c9_13.down
  · exact c9_14.down
  · exact c9_15.down
  · exact c9_16.down
  · exact c9_17.down
  · exact c9_18.down
  · exact c9_19.down
  · exact c9_20.down
  · exact c9_21.down
  · exact c9_22.down
  · exact c9_23.down
  · exact c9_24.down
  · exact c9_25.down
  · exact c9_26.down
  · exact c9_27.down
  · exact c9_28.down
  · exact c9_29.down
  · exact c9_30.down
  · exact c9_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f10 : PLift (fitted p10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_0 : PLift (covers (masks p10) 11 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_1 : PLift (covers (masks p10) 11 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_2 : PLift (covers (masks p10) 11 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_3 : PLift (covers (masks p10) 11 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_4 : PLift (covers (masks p10) 11 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_5 : PLift (covers (masks p10) 11 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_6 : PLift (covers (masks p10) 11 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_7 : PLift (covers (masks p10) 11 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_8 : PLift (covers (masks p10) 11 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_9 : PLift (covers (masks p10) 11 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_10 : PLift (covers (masks p10) 11 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_11 : PLift (covers (masks p10) 11 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_12 : PLift (covers (masks p10) 11 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_13 : PLift (covers (masks p10) 11 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_14 : PLift (covers (masks p10) 11 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_15 : PLift (covers (masks p10) 11 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_16 : PLift (covers (masks p10) 11 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_17 : PLift (covers (masks p10) 11 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_18 : PLift (covers (masks p10) 11 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_19 : PLift (covers (masks p10) 11 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_20 : PLift (covers (masks p10) 11 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_21 : PLift (covers (masks p10) 11 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_22 : PLift (covers (masks p10) 11 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_23 : PLift (covers (masks p10) 11 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_24 : PLift (covers (masks p10) 11 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_25 : PLift (covers (masks p10) 11 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_26 : PLift (covers (masks p10) 11 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_27 : PLift (covers (masks p10) 11 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_28 : PLift (covers (masks p10) 11 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_29 : PLift (covers (masks p10) 11 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_30 : PLift (covers (masks p10) 11 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c10_31 : PLift (covers (masks p10) 11 31) := ⟨by decide +kernel⟩

private theorem c10 (i : Fin 32) : covers (masks p10) p10.residual i.val := by
  fin_cases i
  · exact c10_0.down
  · exact c10_1.down
  · exact c10_2.down
  · exact c10_3.down
  · exact c10_4.down
  · exact c10_5.down
  · exact c10_6.down
  · exact c10_7.down
  · exact c10_8.down
  · exact c10_9.down
  · exact c10_10.down
  · exact c10_11.down
  · exact c10_12.down
  · exact c10_13.down
  · exact c10_14.down
  · exact c10_15.down
  · exact c10_16.down
  · exact c10_17.down
  · exact c10_18.down
  · exact c10_19.down
  · exact c10_20.down
  · exact c10_21.down
  · exact c10_22.down
  · exact c10_23.down
  · exact c10_24.down
  · exact c10_25.down
  · exact c10_26.down
  · exact c10_27.down
  · exact c10_28.down
  · exact c10_29.down
  · exact c10_30.down
  · exact c10_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f11 : PLift (fitted p11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_0 : PLift (covers (masks p11) 10 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_1 : PLift (covers (masks p11) 10 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_2 : PLift (covers (masks p11) 10 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_3 : PLift (covers (masks p11) 10 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_4 : PLift (covers (masks p11) 10 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_5 : PLift (covers (masks p11) 10 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_6 : PLift (covers (masks p11) 10 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_7 : PLift (covers (masks p11) 10 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_8 : PLift (covers (masks p11) 10 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_9 : PLift (covers (masks p11) 10 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_10 : PLift (covers (masks p11) 10 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_11 : PLift (covers (masks p11) 10 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_12 : PLift (covers (masks p11) 10 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_13 : PLift (covers (masks p11) 10 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_14 : PLift (covers (masks p11) 10 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_15 : PLift (covers (masks p11) 10 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_16 : PLift (covers (masks p11) 10 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_17 : PLift (covers (masks p11) 10 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_18 : PLift (covers (masks p11) 10 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_19 : PLift (covers (masks p11) 10 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_20 : PLift (covers (masks p11) 10 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_21 : PLift (covers (masks p11) 10 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_22 : PLift (covers (masks p11) 10 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_23 : PLift (covers (masks p11) 10 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_24 : PLift (covers (masks p11) 10 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_25 : PLift (covers (masks p11) 10 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_26 : PLift (covers (masks p11) 10 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_27 : PLift (covers (masks p11) 10 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_28 : PLift (covers (masks p11) 10 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_29 : PLift (covers (masks p11) 10 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_30 : PLift (covers (masks p11) 10 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c11_31 : PLift (covers (masks p11) 10 31) := ⟨by decide +kernel⟩

private theorem c11 (i : Fin 32) : covers (masks p11) p11.residual i.val := by
  fin_cases i
  · exact c11_0.down
  · exact c11_1.down
  · exact c11_2.down
  · exact c11_3.down
  · exact c11_4.down
  · exact c11_5.down
  · exact c11_6.down
  · exact c11_7.down
  · exact c11_8.down
  · exact c11_9.down
  · exact c11_10.down
  · exact c11_11.down
  · exact c11_12.down
  · exact c11_13.down
  · exact c11_14.down
  · exact c11_15.down
  · exact c11_16.down
  · exact c11_17.down
  · exact c11_18.down
  · exact c11_19.down
  · exact c11_20.down
  · exact c11_21.down
  · exact c11_22.down
  · exact c11_23.down
  · exact c11_24.down
  · exact c11_25.down
  · exact c11_26.down
  · exact c11_27.down
  · exact c11_28.down
  · exact c11_29.down
  · exact c11_30.down
  · exact c11_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f12 : PLift (fitted p12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_0 : PLift (covers (masks p12) 9 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_1 : PLift (covers (masks p12) 9 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_2 : PLift (covers (masks p12) 9 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_3 : PLift (covers (masks p12) 9 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_4 : PLift (covers (masks p12) 9 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_5 : PLift (covers (masks p12) 9 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_6 : PLift (covers (masks p12) 9 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_7 : PLift (covers (masks p12) 9 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_8 : PLift (covers (masks p12) 9 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_9 : PLift (covers (masks p12) 9 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_10 : PLift (covers (masks p12) 9 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_11 : PLift (covers (masks p12) 9 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_12 : PLift (covers (masks p12) 9 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_13 : PLift (covers (masks p12) 9 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_14 : PLift (covers (masks p12) 9 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_15 : PLift (covers (masks p12) 9 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_16 : PLift (covers (masks p12) 9 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_17 : PLift (covers (masks p12) 9 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_18 : PLift (covers (masks p12) 9 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_19 : PLift (covers (masks p12) 9 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_20 : PLift (covers (masks p12) 9 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_21 : PLift (covers (masks p12) 9 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_22 : PLift (covers (masks p12) 9 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_23 : PLift (covers (masks p12) 9 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_24 : PLift (covers (masks p12) 9 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_25 : PLift (covers (masks p12) 9 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_26 : PLift (covers (masks p12) 9 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_27 : PLift (covers (masks p12) 9 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_28 : PLift (covers (masks p12) 9 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_29 : PLift (covers (masks p12) 9 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_30 : PLift (covers (masks p12) 9 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c12_31 : PLift (covers (masks p12) 9 31) := ⟨by decide +kernel⟩

private theorem c12 (i : Fin 32) : covers (masks p12) p12.residual i.val := by
  fin_cases i
  · exact c12_0.down
  · exact c12_1.down
  · exact c12_2.down
  · exact c12_3.down
  · exact c12_4.down
  · exact c12_5.down
  · exact c12_6.down
  · exact c12_7.down
  · exact c12_8.down
  · exact c12_9.down
  · exact c12_10.down
  · exact c12_11.down
  · exact c12_12.down
  · exact c12_13.down
  · exact c12_14.down
  · exact c12_15.down
  · exact c12_16.down
  · exact c12_17.down
  · exact c12_18.down
  · exact c12_19.down
  · exact c12_20.down
  · exact c12_21.down
  · exact c12_22.down
  · exact c12_23.down
  · exact c12_24.down
  · exact c12_25.down
  · exact c12_26.down
  · exact c12_27.down
  · exact c12_28.down
  · exact c12_29.down
  · exact c12_30.down
  · exact c12_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f13 : PLift (fitted p13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_0 : PLift (covers (masks p13) 8 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_1 : PLift (covers (masks p13) 8 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_2 : PLift (covers (masks p13) 8 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_3 : PLift (covers (masks p13) 8 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_4 : PLift (covers (masks p13) 8 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_5 : PLift (covers (masks p13) 8 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_6 : PLift (covers (masks p13) 8 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_7 : PLift (covers (masks p13) 8 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_8 : PLift (covers (masks p13) 8 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_9 : PLift (covers (masks p13) 8 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_10 : PLift (covers (masks p13) 8 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_11 : PLift (covers (masks p13) 8 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_12 : PLift (covers (masks p13) 8 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_13 : PLift (covers (masks p13) 8 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_14 : PLift (covers (masks p13) 8 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_15 : PLift (covers (masks p13) 8 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_16 : PLift (covers (masks p13) 8 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_17 : PLift (covers (masks p13) 8 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_18 : PLift (covers (masks p13) 8 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_19 : PLift (covers (masks p13) 8 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_20 : PLift (covers (masks p13) 8 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_21 : PLift (covers (masks p13) 8 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_22 : PLift (covers (masks p13) 8 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_23 : PLift (covers (masks p13) 8 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_24 : PLift (covers (masks p13) 8 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_25 : PLift (covers (masks p13) 8 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_26 : PLift (covers (masks p13) 8 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_27 : PLift (covers (masks p13) 8 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_28 : PLift (covers (masks p13) 8 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_29 : PLift (covers (masks p13) 8 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_30 : PLift (covers (masks p13) 8 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c13_31 : PLift (covers (masks p13) 8 31) := ⟨by decide +kernel⟩

private theorem c13 (i : Fin 32) : covers (masks p13) p13.residual i.val := by
  fin_cases i
  · exact c13_0.down
  · exact c13_1.down
  · exact c13_2.down
  · exact c13_3.down
  · exact c13_4.down
  · exact c13_5.down
  · exact c13_6.down
  · exact c13_7.down
  · exact c13_8.down
  · exact c13_9.down
  · exact c13_10.down
  · exact c13_11.down
  · exact c13_12.down
  · exact c13_13.down
  · exact c13_14.down
  · exact c13_15.down
  · exact c13_16.down
  · exact c13_17.down
  · exact c13_18.down
  · exact c13_19.down
  · exact c13_20.down
  · exact c13_21.down
  · exact c13_22.down
  · exact c13_23.down
  · exact c13_24.down
  · exact c13_25.down
  · exact c13_26.down
  · exact c13_27.down
  · exact c13_28.down
  · exact c13_29.down
  · exact c13_30.down
  · exact c13_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f14 : PLift (fitted p14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_0 : PLift (covers (masks p14) 13 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_1 : PLift (covers (masks p14) 13 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_2 : PLift (covers (masks p14) 13 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_3 : PLift (covers (masks p14) 13 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_4 : PLift (covers (masks p14) 13 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_5 : PLift (covers (masks p14) 13 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_6 : PLift (covers (masks p14) 13 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_7 : PLift (covers (masks p14) 13 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_8 : PLift (covers (masks p14) 13 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_9 : PLift (covers (masks p14) 13 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_10 : PLift (covers (masks p14) 13 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_11 : PLift (covers (masks p14) 13 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_12 : PLift (covers (masks p14) 13 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_13 : PLift (covers (masks p14) 13 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_14 : PLift (covers (masks p14) 13 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_15 : PLift (covers (masks p14) 13 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_16 : PLift (covers (masks p14) 13 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_17 : PLift (covers (masks p14) 13 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_18 : PLift (covers (masks p14) 13 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_19 : PLift (covers (masks p14) 13 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_20 : PLift (covers (masks p14) 13 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_21 : PLift (covers (masks p14) 13 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_22 : PLift (covers (masks p14) 13 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_23 : PLift (covers (masks p14) 13 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_24 : PLift (covers (masks p14) 13 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_25 : PLift (covers (masks p14) 13 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_26 : PLift (covers (masks p14) 13 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_27 : PLift (covers (masks p14) 13 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_28 : PLift (covers (masks p14) 13 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_29 : PLift (covers (masks p14) 13 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_30 : PLift (covers (masks p14) 13 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c14_31 : PLift (covers (masks p14) 13 31) := ⟨by decide +kernel⟩

private theorem c14 (i : Fin 32) : covers (masks p14) p14.residual i.val := by
  fin_cases i
  · exact c14_0.down
  · exact c14_1.down
  · exact c14_2.down
  · exact c14_3.down
  · exact c14_4.down
  · exact c14_5.down
  · exact c14_6.down
  · exact c14_7.down
  · exact c14_8.down
  · exact c14_9.down
  · exact c14_10.down
  · exact c14_11.down
  · exact c14_12.down
  · exact c14_13.down
  · exact c14_14.down
  · exact c14_15.down
  · exact c14_16.down
  · exact c14_17.down
  · exact c14_18.down
  · exact c14_19.down
  · exact c14_20.down
  · exact c14_21.down
  · exact c14_22.down
  · exact c14_23.down
  · exact c14_24.down
  · exact c14_25.down
  · exact c14_26.down
  · exact c14_27.down
  · exact c14_28.down
  · exact c14_29.down
  · exact c14_30.down
  · exact c14_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f15 : PLift (fitted p15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_0 : PLift (covers (masks p15) 12 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_1 : PLift (covers (masks p15) 12 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_2 : PLift (covers (masks p15) 12 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_3 : PLift (covers (masks p15) 12 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_4 : PLift (covers (masks p15) 12 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_5 : PLift (covers (masks p15) 12 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_6 : PLift (covers (masks p15) 12 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_7 : PLift (covers (masks p15) 12 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_8 : PLift (covers (masks p15) 12 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_9 : PLift (covers (masks p15) 12 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_10 : PLift (covers (masks p15) 12 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_11 : PLift (covers (masks p15) 12 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_12 : PLift (covers (masks p15) 12 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_13 : PLift (covers (masks p15) 12 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_14 : PLift (covers (masks p15) 12 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_15 : PLift (covers (masks p15) 12 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_16 : PLift (covers (masks p15) 12 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_17 : PLift (covers (masks p15) 12 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_18 : PLift (covers (masks p15) 12 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_19 : PLift (covers (masks p15) 12 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_20 : PLift (covers (masks p15) 12 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_21 : PLift (covers (masks p15) 12 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_22 : PLift (covers (masks p15) 12 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_23 : PLift (covers (masks p15) 12 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_24 : PLift (covers (masks p15) 12 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_25 : PLift (covers (masks p15) 12 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_26 : PLift (covers (masks p15) 12 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_27 : PLift (covers (masks p15) 12 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_28 : PLift (covers (masks p15) 12 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_29 : PLift (covers (masks p15) 12 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_30 : PLift (covers (masks p15) 12 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c15_31 : PLift (covers (masks p15) 12 31) := ⟨by decide +kernel⟩

private theorem c15 (i : Fin 32) : covers (masks p15) p15.residual i.val := by
  fin_cases i
  · exact c15_0.down
  · exact c15_1.down
  · exact c15_2.down
  · exact c15_3.down
  · exact c15_4.down
  · exact c15_5.down
  · exact c15_6.down
  · exact c15_7.down
  · exact c15_8.down
  · exact c15_9.down
  · exact c15_10.down
  · exact c15_11.down
  · exact c15_12.down
  · exact c15_13.down
  · exact c15_14.down
  · exact c15_15.down
  · exact c15_16.down
  · exact c15_17.down
  · exact c15_18.down
  · exact c15_19.down
  · exact c15_20.down
  · exact c15_21.down
  · exact c15_22.down
  · exact c15_23.down
  · exact c15_24.down
  · exact c15_25.down
  · exact c15_26.down
  · exact c15_27.down
  · exact c15_28.down
  · exact c15_29.down
  · exact c15_30.down
  · exact c15_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f16 : PLift (fitted p16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_0 : PLift (covers (masks p16) 11 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_1 : PLift (covers (masks p16) 11 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_2 : PLift (covers (masks p16) 11 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_3 : PLift (covers (masks p16) 11 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_4 : PLift (covers (masks p16) 11 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_5 : PLift (covers (masks p16) 11 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_6 : PLift (covers (masks p16) 11 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_7 : PLift (covers (masks p16) 11 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_8 : PLift (covers (masks p16) 11 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_9 : PLift (covers (masks p16) 11 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_10 : PLift (covers (masks p16) 11 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_11 : PLift (covers (masks p16) 11 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_12 : PLift (covers (masks p16) 11 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_13 : PLift (covers (masks p16) 11 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_14 : PLift (covers (masks p16) 11 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_15 : PLift (covers (masks p16) 11 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_16 : PLift (covers (masks p16) 11 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_17 : PLift (covers (masks p16) 11 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_18 : PLift (covers (masks p16) 11 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_19 : PLift (covers (masks p16) 11 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_20 : PLift (covers (masks p16) 11 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_21 : PLift (covers (masks p16) 11 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_22 : PLift (covers (masks p16) 11 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_23 : PLift (covers (masks p16) 11 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_24 : PLift (covers (masks p16) 11 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_25 : PLift (covers (masks p16) 11 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_26 : PLift (covers (masks p16) 11 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_27 : PLift (covers (masks p16) 11 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_28 : PLift (covers (masks p16) 11 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_29 : PLift (covers (masks p16) 11 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_30 : PLift (covers (masks p16) 11 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c16_31 : PLift (covers (masks p16) 11 31) := ⟨by decide +kernel⟩

private theorem c16 (i : Fin 32) : covers (masks p16) p16.residual i.val := by
  fin_cases i
  · exact c16_0.down
  · exact c16_1.down
  · exact c16_2.down
  · exact c16_3.down
  · exact c16_4.down
  · exact c16_5.down
  · exact c16_6.down
  · exact c16_7.down
  · exact c16_8.down
  · exact c16_9.down
  · exact c16_10.down
  · exact c16_11.down
  · exact c16_12.down
  · exact c16_13.down
  · exact c16_14.down
  · exact c16_15.down
  · exact c16_16.down
  · exact c16_17.down
  · exact c16_18.down
  · exact c16_19.down
  · exact c16_20.down
  · exact c16_21.down
  · exact c16_22.down
  · exact c16_23.down
  · exact c16_24.down
  · exact c16_25.down
  · exact c16_26.down
  · exact c16_27.down
  · exact c16_28.down
  · exact c16_29.down
  · exact c16_30.down
  · exact c16_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f17 : PLift (fitted p17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_0 : PLift (covers (masks p17) 10 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_1 : PLift (covers (masks p17) 10 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_2 : PLift (covers (masks p17) 10 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_3 : PLift (covers (masks p17) 10 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_4 : PLift (covers (masks p17) 10 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_5 : PLift (covers (masks p17) 10 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_6 : PLift (covers (masks p17) 10 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_7 : PLift (covers (masks p17) 10 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_8 : PLift (covers (masks p17) 10 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_9 : PLift (covers (masks p17) 10 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_10 : PLift (covers (masks p17) 10 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_11 : PLift (covers (masks p17) 10 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_12 : PLift (covers (masks p17) 10 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_13 : PLift (covers (masks p17) 10 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_14 : PLift (covers (masks p17) 10 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_15 : PLift (covers (masks p17) 10 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_16 : PLift (covers (masks p17) 10 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_17 : PLift (covers (masks p17) 10 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_18 : PLift (covers (masks p17) 10 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_19 : PLift (covers (masks p17) 10 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_20 : PLift (covers (masks p17) 10 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_21 : PLift (covers (masks p17) 10 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_22 : PLift (covers (masks p17) 10 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_23 : PLift (covers (masks p17) 10 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_24 : PLift (covers (masks p17) 10 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_25 : PLift (covers (masks p17) 10 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_26 : PLift (covers (masks p17) 10 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_27 : PLift (covers (masks p17) 10 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_28 : PLift (covers (masks p17) 10 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_29 : PLift (covers (masks p17) 10 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_30 : PLift (covers (masks p17) 10 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c17_31 : PLift (covers (masks p17) 10 31) := ⟨by decide +kernel⟩

private theorem c17 (i : Fin 32) : covers (masks p17) p17.residual i.val := by
  fin_cases i
  · exact c17_0.down
  · exact c17_1.down
  · exact c17_2.down
  · exact c17_3.down
  · exact c17_4.down
  · exact c17_5.down
  · exact c17_6.down
  · exact c17_7.down
  · exact c17_8.down
  · exact c17_9.down
  · exact c17_10.down
  · exact c17_11.down
  · exact c17_12.down
  · exact c17_13.down
  · exact c17_14.down
  · exact c17_15.down
  · exact c17_16.down
  · exact c17_17.down
  · exact c17_18.down
  · exact c17_19.down
  · exact c17_20.down
  · exact c17_21.down
  · exact c17_22.down
  · exact c17_23.down
  · exact c17_24.down
  · exact c17_25.down
  · exact c17_26.down
  · exact c17_27.down
  · exact c17_28.down
  · exact c17_29.down
  · exact c17_30.down
  · exact c17_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f18 : PLift (fitted p18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_0 : PLift (covers (masks p18) 9 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_1 : PLift (covers (masks p18) 9 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_2 : PLift (covers (masks p18) 9 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_3 : PLift (covers (masks p18) 9 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_4 : PLift (covers (masks p18) 9 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_5 : PLift (covers (masks p18) 9 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_6 : PLift (covers (masks p18) 9 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_7 : PLift (covers (masks p18) 9 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_8 : PLift (covers (masks p18) 9 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_9 : PLift (covers (masks p18) 9 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_10 : PLift (covers (masks p18) 9 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_11 : PLift (covers (masks p18) 9 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_12 : PLift (covers (masks p18) 9 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_13 : PLift (covers (masks p18) 9 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_14 : PLift (covers (masks p18) 9 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_15 : PLift (covers (masks p18) 9 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_16 : PLift (covers (masks p18) 9 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_17 : PLift (covers (masks p18) 9 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_18 : PLift (covers (masks p18) 9 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_19 : PLift (covers (masks p18) 9 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_20 : PLift (covers (masks p18) 9 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_21 : PLift (covers (masks p18) 9 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_22 : PLift (covers (masks p18) 9 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_23 : PLift (covers (masks p18) 9 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_24 : PLift (covers (masks p18) 9 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_25 : PLift (covers (masks p18) 9 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_26 : PLift (covers (masks p18) 9 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_27 : PLift (covers (masks p18) 9 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_28 : PLift (covers (masks p18) 9 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_29 : PLift (covers (masks p18) 9 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_30 : PLift (covers (masks p18) 9 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c18_31 : PLift (covers (masks p18) 9 31) := ⟨by decide +kernel⟩

private theorem c18 (i : Fin 32) : covers (masks p18) p18.residual i.val := by
  fin_cases i
  · exact c18_0.down
  · exact c18_1.down
  · exact c18_2.down
  · exact c18_3.down
  · exact c18_4.down
  · exact c18_5.down
  · exact c18_6.down
  · exact c18_7.down
  · exact c18_8.down
  · exact c18_9.down
  · exact c18_10.down
  · exact c18_11.down
  · exact c18_12.down
  · exact c18_13.down
  · exact c18_14.down
  · exact c18_15.down
  · exact c18_16.down
  · exact c18_17.down
  · exact c18_18.down
  · exact c18_19.down
  · exact c18_20.down
  · exact c18_21.down
  · exact c18_22.down
  · exact c18_23.down
  · exact c18_24.down
  · exact c18_25.down
  · exact c18_26.down
  · exact c18_27.down
  · exact c18_28.down
  · exact c18_29.down
  · exact c18_30.down
  · exact c18_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f19 : PLift (fitted p19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_0 : PLift (covers (masks p19) 8 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_1 : PLift (covers (masks p19) 8 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_2 : PLift (covers (masks p19) 8 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_3 : PLift (covers (masks p19) 8 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_4 : PLift (covers (masks p19) 8 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_5 : PLift (covers (masks p19) 8 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_6 : PLift (covers (masks p19) 8 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_7 : PLift (covers (masks p19) 8 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_8 : PLift (covers (masks p19) 8 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_9 : PLift (covers (masks p19) 8 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_10 : PLift (covers (masks p19) 8 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_11 : PLift (covers (masks p19) 8 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_12 : PLift (covers (masks p19) 8 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_13 : PLift (covers (masks p19) 8 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_14 : PLift (covers (masks p19) 8 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_15 : PLift (covers (masks p19) 8 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_16 : PLift (covers (masks p19) 8 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_17 : PLift (covers (masks p19) 8 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_18 : PLift (covers (masks p19) 8 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_19 : PLift (covers (masks p19) 8 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_20 : PLift (covers (masks p19) 8 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_21 : PLift (covers (masks p19) 8 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_22 : PLift (covers (masks p19) 8 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_23 : PLift (covers (masks p19) 8 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_24 : PLift (covers (masks p19) 8 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_25 : PLift (covers (masks p19) 8 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_26 : PLift (covers (masks p19) 8 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_27 : PLift (covers (masks p19) 8 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_28 : PLift (covers (masks p19) 8 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_29 : PLift (covers (masks p19) 8 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_30 : PLift (covers (masks p19) 8 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c19_31 : PLift (covers (masks p19) 8 31) := ⟨by decide +kernel⟩

private theorem c19 (i : Fin 32) : covers (masks p19) p19.residual i.val := by
  fin_cases i
  · exact c19_0.down
  · exact c19_1.down
  · exact c19_2.down
  · exact c19_3.down
  · exact c19_4.down
  · exact c19_5.down
  · exact c19_6.down
  · exact c19_7.down
  · exact c19_8.down
  · exact c19_9.down
  · exact c19_10.down
  · exact c19_11.down
  · exact c19_12.down
  · exact c19_13.down
  · exact c19_14.down
  · exact c19_15.down
  · exact c19_16.down
  · exact c19_17.down
  · exact c19_18.down
  · exact c19_19.down
  · exact c19_20.down
  · exact c19_21.down
  · exact c19_22.down
  · exact c19_23.down
  · exact c19_24.down
  · exact c19_25.down
  · exact c19_26.down
  · exact c19_27.down
  · exact c19_28.down
  · exact c19_29.down
  · exact c19_30.down
  · exact c19_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f20 : PLift (fitted p20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_0 : PLift (covers (masks p20) 7 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_1 : PLift (covers (masks p20) 7 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_2 : PLift (covers (masks p20) 7 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_3 : PLift (covers (masks p20) 7 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_4 : PLift (covers (masks p20) 7 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_5 : PLift (covers (masks p20) 7 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_6 : PLift (covers (masks p20) 7 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_7 : PLift (covers (masks p20) 7 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_8 : PLift (covers (masks p20) 7 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_9 : PLift (covers (masks p20) 7 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_10 : PLift (covers (masks p20) 7 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_11 : PLift (covers (masks p20) 7 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_12 : PLift (covers (masks p20) 7 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_13 : PLift (covers (masks p20) 7 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_14 : PLift (covers (masks p20) 7 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_15 : PLift (covers (masks p20) 7 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_16 : PLift (covers (masks p20) 7 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_17 : PLift (covers (masks p20) 7 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_18 : PLift (covers (masks p20) 7 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_19 : PLift (covers (masks p20) 7 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_20 : PLift (covers (masks p20) 7 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_21 : PLift (covers (masks p20) 7 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_22 : PLift (covers (masks p20) 7 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_23 : PLift (covers (masks p20) 7 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_24 : PLift (covers (masks p20) 7 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_25 : PLift (covers (masks p20) 7 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_26 : PLift (covers (masks p20) 7 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_27 : PLift (covers (masks p20) 7 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_28 : PLift (covers (masks p20) 7 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_29 : PLift (covers (masks p20) 7 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_30 : PLift (covers (masks p20) 7 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c20_31 : PLift (covers (masks p20) 7 31) := ⟨by decide +kernel⟩

private theorem c20 (i : Fin 32) : covers (masks p20) p20.residual i.val := by
  fin_cases i
  · exact c20_0.down
  · exact c20_1.down
  · exact c20_2.down
  · exact c20_3.down
  · exact c20_4.down
  · exact c20_5.down
  · exact c20_6.down
  · exact c20_7.down
  · exact c20_8.down
  · exact c20_9.down
  · exact c20_10.down
  · exact c20_11.down
  · exact c20_12.down
  · exact c20_13.down
  · exact c20_14.down
  · exact c20_15.down
  · exact c20_16.down
  · exact c20_17.down
  · exact c20_18.down
  · exact c20_19.down
  · exact c20_20.down
  · exact c20_21.down
  · exact c20_22.down
  · exact c20_23.down
  · exact c20_24.down
  · exact c20_25.down
  · exact c20_26.down
  · exact c20_27.down
  · exact c20_28.down
  · exact c20_29.down
  · exact c20_30.down
  · exact c20_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f21 : PLift (fitted p21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_0 : PLift (covers (masks p21) 11 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_1 : PLift (covers (masks p21) 11 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_2 : PLift (covers (masks p21) 11 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_3 : PLift (covers (masks p21) 11 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_4 : PLift (covers (masks p21) 11 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_5 : PLift (covers (masks p21) 11 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_6 : PLift (covers (masks p21) 11 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_7 : PLift (covers (masks p21) 11 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_8 : PLift (covers (masks p21) 11 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_9 : PLift (covers (masks p21) 11 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_10 : PLift (covers (masks p21) 11 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_11 : PLift (covers (masks p21) 11 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_12 : PLift (covers (masks p21) 11 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_13 : PLift (covers (masks p21) 11 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_14 : PLift (covers (masks p21) 11 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_15 : PLift (covers (masks p21) 11 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_16 : PLift (covers (masks p21) 11 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_17 : PLift (covers (masks p21) 11 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_18 : PLift (covers (masks p21) 11 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_19 : PLift (covers (masks p21) 11 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_20 : PLift (covers (masks p21) 11 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_21 : PLift (covers (masks p21) 11 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_22 : PLift (covers (masks p21) 11 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_23 : PLift (covers (masks p21) 11 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_24 : PLift (covers (masks p21) 11 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_25 : PLift (covers (masks p21) 11 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_26 : PLift (covers (masks p21) 11 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_27 : PLift (covers (masks p21) 11 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_28 : PLift (covers (masks p21) 11 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_29 : PLift (covers (masks p21) 11 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_30 : PLift (covers (masks p21) 11 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c21_31 : PLift (covers (masks p21) 11 31) := ⟨by decide +kernel⟩

private theorem c21 (i : Fin 32) : covers (masks p21) p21.residual i.val := by
  fin_cases i
  · exact c21_0.down
  · exact c21_1.down
  · exact c21_2.down
  · exact c21_3.down
  · exact c21_4.down
  · exact c21_5.down
  · exact c21_6.down
  · exact c21_7.down
  · exact c21_8.down
  · exact c21_9.down
  · exact c21_10.down
  · exact c21_11.down
  · exact c21_12.down
  · exact c21_13.down
  · exact c21_14.down
  · exact c21_15.down
  · exact c21_16.down
  · exact c21_17.down
  · exact c21_18.down
  · exact c21_19.down
  · exact c21_20.down
  · exact c21_21.down
  · exact c21_22.down
  · exact c21_23.down
  · exact c21_24.down
  · exact c21_25.down
  · exact c21_26.down
  · exact c21_27.down
  · exact c21_28.down
  · exact c21_29.down
  · exact c21_30.down
  · exact c21_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f22 : PLift (fitted p22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_0 : PLift (covers (masks p22) 10 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_1 : PLift (covers (masks p22) 10 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_2 : PLift (covers (masks p22) 10 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_3 : PLift (covers (masks p22) 10 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_4 : PLift (covers (masks p22) 10 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_5 : PLift (covers (masks p22) 10 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_6 : PLift (covers (masks p22) 10 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_7 : PLift (covers (masks p22) 10 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_8 : PLift (covers (masks p22) 10 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_9 : PLift (covers (masks p22) 10 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_10 : PLift (covers (masks p22) 10 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_11 : PLift (covers (masks p22) 10 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_12 : PLift (covers (masks p22) 10 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_13 : PLift (covers (masks p22) 10 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_14 : PLift (covers (masks p22) 10 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_15 : PLift (covers (masks p22) 10 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_16 : PLift (covers (masks p22) 10 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_17 : PLift (covers (masks p22) 10 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_18 : PLift (covers (masks p22) 10 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_19 : PLift (covers (masks p22) 10 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_20 : PLift (covers (masks p22) 10 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_21 : PLift (covers (masks p22) 10 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_22 : PLift (covers (masks p22) 10 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_23 : PLift (covers (masks p22) 10 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_24 : PLift (covers (masks p22) 10 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_25 : PLift (covers (masks p22) 10 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_26 : PLift (covers (masks p22) 10 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_27 : PLift (covers (masks p22) 10 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_28 : PLift (covers (masks p22) 10 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_29 : PLift (covers (masks p22) 10 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_30 : PLift (covers (masks p22) 10 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c22_31 : PLift (covers (masks p22) 10 31) := ⟨by decide +kernel⟩

private theorem c22 (i : Fin 32) : covers (masks p22) p22.residual i.val := by
  fin_cases i
  · exact c22_0.down
  · exact c22_1.down
  · exact c22_2.down
  · exact c22_3.down
  · exact c22_4.down
  · exact c22_5.down
  · exact c22_6.down
  · exact c22_7.down
  · exact c22_8.down
  · exact c22_9.down
  · exact c22_10.down
  · exact c22_11.down
  · exact c22_12.down
  · exact c22_13.down
  · exact c22_14.down
  · exact c22_15.down
  · exact c22_16.down
  · exact c22_17.down
  · exact c22_18.down
  · exact c22_19.down
  · exact c22_20.down
  · exact c22_21.down
  · exact c22_22.down
  · exact c22_23.down
  · exact c22_24.down
  · exact c22_25.down
  · exact c22_26.down
  · exact c22_27.down
  · exact c22_28.down
  · exact c22_29.down
  · exact c22_30.down
  · exact c22_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f23 : PLift (fitted p23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_0 : PLift (covers (masks p23) 9 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_1 : PLift (covers (masks p23) 9 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_2 : PLift (covers (masks p23) 9 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_3 : PLift (covers (masks p23) 9 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_4 : PLift (covers (masks p23) 9 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_5 : PLift (covers (masks p23) 9 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_6 : PLift (covers (masks p23) 9 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_7 : PLift (covers (masks p23) 9 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_8 : PLift (covers (masks p23) 9 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_9 : PLift (covers (masks p23) 9 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_10 : PLift (covers (masks p23) 9 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_11 : PLift (covers (masks p23) 9 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_12 : PLift (covers (masks p23) 9 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_13 : PLift (covers (masks p23) 9 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_14 : PLift (covers (masks p23) 9 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_15 : PLift (covers (masks p23) 9 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_16 : PLift (covers (masks p23) 9 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_17 : PLift (covers (masks p23) 9 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_18 : PLift (covers (masks p23) 9 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_19 : PLift (covers (masks p23) 9 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_20 : PLift (covers (masks p23) 9 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_21 : PLift (covers (masks p23) 9 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_22 : PLift (covers (masks p23) 9 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_23 : PLift (covers (masks p23) 9 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_24 : PLift (covers (masks p23) 9 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_25 : PLift (covers (masks p23) 9 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_26 : PLift (covers (masks p23) 9 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_27 : PLift (covers (masks p23) 9 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_28 : PLift (covers (masks p23) 9 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_29 : PLift (covers (masks p23) 9 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_30 : PLift (covers (masks p23) 9 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c23_31 : PLift (covers (masks p23) 9 31) := ⟨by decide +kernel⟩

private theorem c23 (i : Fin 32) : covers (masks p23) p23.residual i.val := by
  fin_cases i
  · exact c23_0.down
  · exact c23_1.down
  · exact c23_2.down
  · exact c23_3.down
  · exact c23_4.down
  · exact c23_5.down
  · exact c23_6.down
  · exact c23_7.down
  · exact c23_8.down
  · exact c23_9.down
  · exact c23_10.down
  · exact c23_11.down
  · exact c23_12.down
  · exact c23_13.down
  · exact c23_14.down
  · exact c23_15.down
  · exact c23_16.down
  · exact c23_17.down
  · exact c23_18.down
  · exact c23_19.down
  · exact c23_20.down
  · exact c23_21.down
  · exact c23_22.down
  · exact c23_23.down
  · exact c23_24.down
  · exact c23_25.down
  · exact c23_26.down
  · exact c23_27.down
  · exact c23_28.down
  · exact c23_29.down
  · exact c23_30.down
  · exact c23_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f24 : PLift (fitted p24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_0 : PLift (covers (masks p24) 8 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_1 : PLift (covers (masks p24) 8 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_2 : PLift (covers (masks p24) 8 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_3 : PLift (covers (masks p24) 8 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_4 : PLift (covers (masks p24) 8 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_5 : PLift (covers (masks p24) 8 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_6 : PLift (covers (masks p24) 8 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_7 : PLift (covers (masks p24) 8 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_8 : PLift (covers (masks p24) 8 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_9 : PLift (covers (masks p24) 8 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_10 : PLift (covers (masks p24) 8 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_11 : PLift (covers (masks p24) 8 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_12 : PLift (covers (masks p24) 8 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_13 : PLift (covers (masks p24) 8 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_14 : PLift (covers (masks p24) 8 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_15 : PLift (covers (masks p24) 8 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_16 : PLift (covers (masks p24) 8 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_17 : PLift (covers (masks p24) 8 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_18 : PLift (covers (masks p24) 8 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_19 : PLift (covers (masks p24) 8 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_20 : PLift (covers (masks p24) 8 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_21 : PLift (covers (masks p24) 8 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_22 : PLift (covers (masks p24) 8 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_23 : PLift (covers (masks p24) 8 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_24 : PLift (covers (masks p24) 8 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_25 : PLift (covers (masks p24) 8 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_26 : PLift (covers (masks p24) 8 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_27 : PLift (covers (masks p24) 8 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_28 : PLift (covers (masks p24) 8 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_29 : PLift (covers (masks p24) 8 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_30 : PLift (covers (masks p24) 8 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c24_31 : PLift (covers (masks p24) 8 31) := ⟨by decide +kernel⟩

private theorem c24 (i : Fin 32) : covers (masks p24) p24.residual i.val := by
  fin_cases i
  · exact c24_0.down
  · exact c24_1.down
  · exact c24_2.down
  · exact c24_3.down
  · exact c24_4.down
  · exact c24_5.down
  · exact c24_6.down
  · exact c24_7.down
  · exact c24_8.down
  · exact c24_9.down
  · exact c24_10.down
  · exact c24_11.down
  · exact c24_12.down
  · exact c24_13.down
  · exact c24_14.down
  · exact c24_15.down
  · exact c24_16.down
  · exact c24_17.down
  · exact c24_18.down
  · exact c24_19.down
  · exact c24_20.down
  · exact c24_21.down
  · exact c24_22.down
  · exact c24_23.down
  · exact c24_24.down
  · exact c24_25.down
  · exact c24_26.down
  · exact c24_27.down
  · exact c24_28.down
  · exact c24_29.down
  · exact c24_30.down
  · exact c24_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f25 : PLift (fitted p25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_0 : PLift (covers (masks p25) 11 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_1 : PLift (covers (masks p25) 11 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_2 : PLift (covers (masks p25) 11 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_3 : PLift (covers (masks p25) 11 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_4 : PLift (covers (masks p25) 11 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_5 : PLift (covers (masks p25) 11 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_6 : PLift (covers (masks p25) 11 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_7 : PLift (covers (masks p25) 11 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_8 : PLift (covers (masks p25) 11 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_9 : PLift (covers (masks p25) 11 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_10 : PLift (covers (masks p25) 11 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_11 : PLift (covers (masks p25) 11 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_12 : PLift (covers (masks p25) 11 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_13 : PLift (covers (masks p25) 11 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_14 : PLift (covers (masks p25) 11 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_15 : PLift (covers (masks p25) 11 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_16 : PLift (covers (masks p25) 11 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_17 : PLift (covers (masks p25) 11 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_18 : PLift (covers (masks p25) 11 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_19 : PLift (covers (masks p25) 11 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_20 : PLift (covers (masks p25) 11 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_21 : PLift (covers (masks p25) 11 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_22 : PLift (covers (masks p25) 11 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_23 : PLift (covers (masks p25) 11 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_24 : PLift (covers (masks p25) 11 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_25 : PLift (covers (masks p25) 11 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_26 : PLift (covers (masks p25) 11 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_27 : PLift (covers (masks p25) 11 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_28 : PLift (covers (masks p25) 11 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_29 : PLift (covers (masks p25) 11 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_30 : PLift (covers (masks p25) 11 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c25_31 : PLift (covers (masks p25) 11 31) := ⟨by decide +kernel⟩

private theorem c25 (i : Fin 32) : covers (masks p25) p25.residual i.val := by
  fin_cases i
  · exact c25_0.down
  · exact c25_1.down
  · exact c25_2.down
  · exact c25_3.down
  · exact c25_4.down
  · exact c25_5.down
  · exact c25_6.down
  · exact c25_7.down
  · exact c25_8.down
  · exact c25_9.down
  · exact c25_10.down
  · exact c25_11.down
  · exact c25_12.down
  · exact c25_13.down
  · exact c25_14.down
  · exact c25_15.down
  · exact c25_16.down
  · exact c25_17.down
  · exact c25_18.down
  · exact c25_19.down
  · exact c25_20.down
  · exact c25_21.down
  · exact c25_22.down
  · exact c25_23.down
  · exact c25_24.down
  · exact c25_25.down
  · exact c25_26.down
  · exact c25_27.down
  · exact c25_28.down
  · exact c25_29.down
  · exact c25_30.down
  · exact c25_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f26 : PLift (fitted p26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_0 : PLift (covers (masks p26) 10 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_1 : PLift (covers (masks p26) 10 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_2 : PLift (covers (masks p26) 10 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_3 : PLift (covers (masks p26) 10 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_4 : PLift (covers (masks p26) 10 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_5 : PLift (covers (masks p26) 10 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_6 : PLift (covers (masks p26) 10 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_7 : PLift (covers (masks p26) 10 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_8 : PLift (covers (masks p26) 10 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_9 : PLift (covers (masks p26) 10 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_10 : PLift (covers (masks p26) 10 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_11 : PLift (covers (masks p26) 10 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_12 : PLift (covers (masks p26) 10 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_13 : PLift (covers (masks p26) 10 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_14 : PLift (covers (masks p26) 10 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_15 : PLift (covers (masks p26) 10 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_16 : PLift (covers (masks p26) 10 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_17 : PLift (covers (masks p26) 10 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_18 : PLift (covers (masks p26) 10 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_19 : PLift (covers (masks p26) 10 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_20 : PLift (covers (masks p26) 10 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_21 : PLift (covers (masks p26) 10 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_22 : PLift (covers (masks p26) 10 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_23 : PLift (covers (masks p26) 10 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_24 : PLift (covers (masks p26) 10 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_25 : PLift (covers (masks p26) 10 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_26 : PLift (covers (masks p26) 10 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_27 : PLift (covers (masks p26) 10 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_28 : PLift (covers (masks p26) 10 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_29 : PLift (covers (masks p26) 10 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_30 : PLift (covers (masks p26) 10 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c26_31 : PLift (covers (masks p26) 10 31) := ⟨by decide +kernel⟩

private theorem c26 (i : Fin 32) : covers (masks p26) p26.residual i.val := by
  fin_cases i
  · exact c26_0.down
  · exact c26_1.down
  · exact c26_2.down
  · exact c26_3.down
  · exact c26_4.down
  · exact c26_5.down
  · exact c26_6.down
  · exact c26_7.down
  · exact c26_8.down
  · exact c26_9.down
  · exact c26_10.down
  · exact c26_11.down
  · exact c26_12.down
  · exact c26_13.down
  · exact c26_14.down
  · exact c26_15.down
  · exact c26_16.down
  · exact c26_17.down
  · exact c26_18.down
  · exact c26_19.down
  · exact c26_20.down
  · exact c26_21.down
  · exact c26_22.down
  · exact c26_23.down
  · exact c26_24.down
  · exact c26_25.down
  · exact c26_26.down
  · exact c26_27.down
  · exact c26_28.down
  · exact c26_29.down
  · exact c26_30.down
  · exact c26_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f27 : PLift (fitted p27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_0 : PLift (covers (masks p27) 9 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_1 : PLift (covers (masks p27) 9 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_2 : PLift (covers (masks p27) 9 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_3 : PLift (covers (masks p27) 9 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_4 : PLift (covers (masks p27) 9 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_5 : PLift (covers (masks p27) 9 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_6 : PLift (covers (masks p27) 9 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_7 : PLift (covers (masks p27) 9 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_8 : PLift (covers (masks p27) 9 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_9 : PLift (covers (masks p27) 9 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_10 : PLift (covers (masks p27) 9 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_11 : PLift (covers (masks p27) 9 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_12 : PLift (covers (masks p27) 9 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_13 : PLift (covers (masks p27) 9 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_14 : PLift (covers (masks p27) 9 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_15 : PLift (covers (masks p27) 9 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_16 : PLift (covers (masks p27) 9 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_17 : PLift (covers (masks p27) 9 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_18 : PLift (covers (masks p27) 9 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_19 : PLift (covers (masks p27) 9 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_20 : PLift (covers (masks p27) 9 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_21 : PLift (covers (masks p27) 9 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_22 : PLift (covers (masks p27) 9 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_23 : PLift (covers (masks p27) 9 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_24 : PLift (covers (masks p27) 9 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_25 : PLift (covers (masks p27) 9 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_26 : PLift (covers (masks p27) 9 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_27 : PLift (covers (masks p27) 9 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_28 : PLift (covers (masks p27) 9 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_29 : PLift (covers (masks p27) 9 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_30 : PLift (covers (masks p27) 9 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c27_31 : PLift (covers (masks p27) 9 31) := ⟨by decide +kernel⟩

private theorem c27 (i : Fin 32) : covers (masks p27) p27.residual i.val := by
  fin_cases i
  · exact c27_0.down
  · exact c27_1.down
  · exact c27_2.down
  · exact c27_3.down
  · exact c27_4.down
  · exact c27_5.down
  · exact c27_6.down
  · exact c27_7.down
  · exact c27_8.down
  · exact c27_9.down
  · exact c27_10.down
  · exact c27_11.down
  · exact c27_12.down
  · exact c27_13.down
  · exact c27_14.down
  · exact c27_15.down
  · exact c27_16.down
  · exact c27_17.down
  · exact c27_18.down
  · exact c27_19.down
  · exact c27_20.down
  · exact c27_21.down
  · exact c27_22.down
  · exact c27_23.down
  · exact c27_24.down
  · exact c27_25.down
  · exact c27_26.down
  · exact c27_27.down
  · exact c27_28.down
  · exact c27_29.down
  · exact c27_30.down
  · exact c27_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f28 : PLift (fitted p28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_0 : PLift (covers (masks p28) 8 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_1 : PLift (covers (masks p28) 8 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_2 : PLift (covers (masks p28) 8 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_3 : PLift (covers (masks p28) 8 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_4 : PLift (covers (masks p28) 8 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_5 : PLift (covers (masks p28) 8 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_6 : PLift (covers (masks p28) 8 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_7 : PLift (covers (masks p28) 8 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_8 : PLift (covers (masks p28) 8 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_9 : PLift (covers (masks p28) 8 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_10 : PLift (covers (masks p28) 8 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_11 : PLift (covers (masks p28) 8 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_12 : PLift (covers (masks p28) 8 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_13 : PLift (covers (masks p28) 8 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_14 : PLift (covers (masks p28) 8 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_15 : PLift (covers (masks p28) 8 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_16 : PLift (covers (masks p28) 8 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_17 : PLift (covers (masks p28) 8 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_18 : PLift (covers (masks p28) 8 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_19 : PLift (covers (masks p28) 8 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_20 : PLift (covers (masks p28) 8 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_21 : PLift (covers (masks p28) 8 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_22 : PLift (covers (masks p28) 8 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_23 : PLift (covers (masks p28) 8 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_24 : PLift (covers (masks p28) 8 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_25 : PLift (covers (masks p28) 8 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_26 : PLift (covers (masks p28) 8 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_27 : PLift (covers (masks p28) 8 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_28 : PLift (covers (masks p28) 8 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_29 : PLift (covers (masks p28) 8 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_30 : PLift (covers (masks p28) 8 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c28_31 : PLift (covers (masks p28) 8 31) := ⟨by decide +kernel⟩

private theorem c28 (i : Fin 32) : covers (masks p28) p28.residual i.val := by
  fin_cases i
  · exact c28_0.down
  · exact c28_1.down
  · exact c28_2.down
  · exact c28_3.down
  · exact c28_4.down
  · exact c28_5.down
  · exact c28_6.down
  · exact c28_7.down
  · exact c28_8.down
  · exact c28_9.down
  · exact c28_10.down
  · exact c28_11.down
  · exact c28_12.down
  · exact c28_13.down
  · exact c28_14.down
  · exact c28_15.down
  · exact c28_16.down
  · exact c28_17.down
  · exact c28_18.down
  · exact c28_19.down
  · exact c28_20.down
  · exact c28_21.down
  · exact c28_22.down
  · exact c28_23.down
  · exact c28_24.down
  · exact c28_25.down
  · exact c28_26.down
  · exact c28_27.down
  · exact c28_28.down
  · exact c28_29.down
  · exact c28_30.down
  · exact c28_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f29 : PLift (fitted p29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_0 : PLift (covers (masks p29) 7 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_1 : PLift (covers (masks p29) 7 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_2 : PLift (covers (masks p29) 7 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_3 : PLift (covers (masks p29) 7 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_4 : PLift (covers (masks p29) 7 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_5 : PLift (covers (masks p29) 7 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_6 : PLift (covers (masks p29) 7 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_7 : PLift (covers (masks p29) 7 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_8 : PLift (covers (masks p29) 7 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_9 : PLift (covers (masks p29) 7 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_10 : PLift (covers (masks p29) 7 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_11 : PLift (covers (masks p29) 7 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_12 : PLift (covers (masks p29) 7 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_13 : PLift (covers (masks p29) 7 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_14 : PLift (covers (masks p29) 7 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_15 : PLift (covers (masks p29) 7 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_16 : PLift (covers (masks p29) 7 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_17 : PLift (covers (masks p29) 7 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_18 : PLift (covers (masks p29) 7 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_19 : PLift (covers (masks p29) 7 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_20 : PLift (covers (masks p29) 7 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_21 : PLift (covers (masks p29) 7 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_22 : PLift (covers (masks p29) 7 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_23 : PLift (covers (masks p29) 7 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_24 : PLift (covers (masks p29) 7 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_25 : PLift (covers (masks p29) 7 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_26 : PLift (covers (masks p29) 7 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_27 : PLift (covers (masks p29) 7 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_28 : PLift (covers (masks p29) 7 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_29 : PLift (covers (masks p29) 7 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_30 : PLift (covers (masks p29) 7 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c29_31 : PLift (covers (masks p29) 7 31) := ⟨by decide +kernel⟩

private theorem c29 (i : Fin 32) : covers (masks p29) p29.residual i.val := by
  fin_cases i
  · exact c29_0.down
  · exact c29_1.down
  · exact c29_2.down
  · exact c29_3.down
  · exact c29_4.down
  · exact c29_5.down
  · exact c29_6.down
  · exact c29_7.down
  · exact c29_8.down
  · exact c29_9.down
  · exact c29_10.down
  · exact c29_11.down
  · exact c29_12.down
  · exact c29_13.down
  · exact c29_14.down
  · exact c29_15.down
  · exact c29_16.down
  · exact c29_17.down
  · exact c29_18.down
  · exact c29_19.down
  · exact c29_20.down
  · exact c29_21.down
  · exact c29_22.down
  · exact c29_23.down
  · exact c29_24.down
  · exact c29_25.down
  · exact c29_26.down
  · exact c29_27.down
  · exact c29_28.down
  · exact c29_29.down
  · exact c29_30.down
  · exact c29_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f30 : PLift (fitted p30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_0 : PLift (covers (masks p30) 11 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_1 : PLift (covers (masks p30) 11 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_2 : PLift (covers (masks p30) 11 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_3 : PLift (covers (masks p30) 11 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_4 : PLift (covers (masks p30) 11 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_5 : PLift (covers (masks p30) 11 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_6 : PLift (covers (masks p30) 11 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_7 : PLift (covers (masks p30) 11 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_8 : PLift (covers (masks p30) 11 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_9 : PLift (covers (masks p30) 11 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_10 : PLift (covers (masks p30) 11 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_11 : PLift (covers (masks p30) 11 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_12 : PLift (covers (masks p30) 11 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_13 : PLift (covers (masks p30) 11 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_14 : PLift (covers (masks p30) 11 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_15 : PLift (covers (masks p30) 11 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_16 : PLift (covers (masks p30) 11 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_17 : PLift (covers (masks p30) 11 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_18 : PLift (covers (masks p30) 11 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_19 : PLift (covers (masks p30) 11 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_20 : PLift (covers (masks p30) 11 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_21 : PLift (covers (masks p30) 11 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_22 : PLift (covers (masks p30) 11 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_23 : PLift (covers (masks p30) 11 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_24 : PLift (covers (masks p30) 11 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_25 : PLift (covers (masks p30) 11 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_26 : PLift (covers (masks p30) 11 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_27 : PLift (covers (masks p30) 11 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_28 : PLift (covers (masks p30) 11 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_29 : PLift (covers (masks p30) 11 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_30 : PLift (covers (masks p30) 11 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c30_31 : PLift (covers (masks p30) 11 31) := ⟨by decide +kernel⟩

private theorem c30 (i : Fin 32) : covers (masks p30) p30.residual i.val := by
  fin_cases i
  · exact c30_0.down
  · exact c30_1.down
  · exact c30_2.down
  · exact c30_3.down
  · exact c30_4.down
  · exact c30_5.down
  · exact c30_6.down
  · exact c30_7.down
  · exact c30_8.down
  · exact c30_9.down
  · exact c30_10.down
  · exact c30_11.down
  · exact c30_12.down
  · exact c30_13.down
  · exact c30_14.down
  · exact c30_15.down
  · exact c30_16.down
  · exact c30_17.down
  · exact c30_18.down
  · exact c30_19.down
  · exact c30_20.down
  · exact c30_21.down
  · exact c30_22.down
  · exact c30_23.down
  · exact c30_24.down
  · exact c30_25.down
  · exact c30_26.down
  · exact c30_27.down
  · exact c30_28.down
  · exact c30_29.down
  · exact c30_30.down
  · exact c30_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f31 : PLift (fitted p31) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_0 : PLift (covers (masks p31) 10 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_1 : PLift (covers (masks p31) 10 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_2 : PLift (covers (masks p31) 10 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_3 : PLift (covers (masks p31) 10 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_4 : PLift (covers (masks p31) 10 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_5 : PLift (covers (masks p31) 10 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_6 : PLift (covers (masks p31) 10 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_7 : PLift (covers (masks p31) 10 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_8 : PLift (covers (masks p31) 10 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_9 : PLift (covers (masks p31) 10 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_10 : PLift (covers (masks p31) 10 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_11 : PLift (covers (masks p31) 10 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_12 : PLift (covers (masks p31) 10 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_13 : PLift (covers (masks p31) 10 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_14 : PLift (covers (masks p31) 10 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_15 : PLift (covers (masks p31) 10 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_16 : PLift (covers (masks p31) 10 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_17 : PLift (covers (masks p31) 10 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_18 : PLift (covers (masks p31) 10 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_19 : PLift (covers (masks p31) 10 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_20 : PLift (covers (masks p31) 10 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_21 : PLift (covers (masks p31) 10 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_22 : PLift (covers (masks p31) 10 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_23 : PLift (covers (masks p31) 10 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_24 : PLift (covers (masks p31) 10 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_25 : PLift (covers (masks p31) 10 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_26 : PLift (covers (masks p31) 10 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_27 : PLift (covers (masks p31) 10 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_28 : PLift (covers (masks p31) 10 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_29 : PLift (covers (masks p31) 10 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_30 : PLift (covers (masks p31) 10 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c31_31 : PLift (covers (masks p31) 10 31) := ⟨by decide +kernel⟩

private theorem c31 (i : Fin 32) : covers (masks p31) p31.residual i.val := by
  fin_cases i
  · exact c31_0.down
  · exact c31_1.down
  · exact c31_2.down
  · exact c31_3.down
  · exact c31_4.down
  · exact c31_5.down
  · exact c31_6.down
  · exact c31_7.down
  · exact c31_8.down
  · exact c31_9.down
  · exact c31_10.down
  · exact c31_11.down
  · exact c31_12.down
  · exact c31_13.down
  · exact c31_14.down
  · exact c31_15.down
  · exact c31_16.down
  · exact c31_17.down
  · exact c31_18.down
  · exact c31_19.down
  · exact c31_20.down
  · exact c31_21.down
  · exact c31_22.down
  · exact c31_23.down
  · exact c31_24.down
  · exact c31_25.down
  · exact c31_26.down
  · exact c31_27.down
  · exact c31_28.down
  · exact c31_29.down
  · exact c31_30.down
  · exact c31_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f32 : PLift (fitted p32) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_0 : PLift (covers (masks p32) 9 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_1 : PLift (covers (masks p32) 9 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_2 : PLift (covers (masks p32) 9 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_3 : PLift (covers (masks p32) 9 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_4 : PLift (covers (masks p32) 9 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_5 : PLift (covers (masks p32) 9 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_6 : PLift (covers (masks p32) 9 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_7 : PLift (covers (masks p32) 9 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_8 : PLift (covers (masks p32) 9 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_9 : PLift (covers (masks p32) 9 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_10 : PLift (covers (masks p32) 9 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_11 : PLift (covers (masks p32) 9 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_12 : PLift (covers (masks p32) 9 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_13 : PLift (covers (masks p32) 9 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_14 : PLift (covers (masks p32) 9 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_15 : PLift (covers (masks p32) 9 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_16 : PLift (covers (masks p32) 9 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_17 : PLift (covers (masks p32) 9 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_18 : PLift (covers (masks p32) 9 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_19 : PLift (covers (masks p32) 9 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_20 : PLift (covers (masks p32) 9 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_21 : PLift (covers (masks p32) 9 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_22 : PLift (covers (masks p32) 9 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_23 : PLift (covers (masks p32) 9 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_24 : PLift (covers (masks p32) 9 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_25 : PLift (covers (masks p32) 9 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_26 : PLift (covers (masks p32) 9 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_27 : PLift (covers (masks p32) 9 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_28 : PLift (covers (masks p32) 9 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_29 : PLift (covers (masks p32) 9 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_30 : PLift (covers (masks p32) 9 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c32_31 : PLift (covers (masks p32) 9 31) := ⟨by decide +kernel⟩

private theorem c32 (i : Fin 32) : covers (masks p32) p32.residual i.val := by
  fin_cases i
  · exact c32_0.down
  · exact c32_1.down
  · exact c32_2.down
  · exact c32_3.down
  · exact c32_4.down
  · exact c32_5.down
  · exact c32_6.down
  · exact c32_7.down
  · exact c32_8.down
  · exact c32_9.down
  · exact c32_10.down
  · exact c32_11.down
  · exact c32_12.down
  · exact c32_13.down
  · exact c32_14.down
  · exact c32_15.down
  · exact c32_16.down
  · exact c32_17.down
  · exact c32_18.down
  · exact c32_19.down
  · exact c32_20.down
  · exact c32_21.down
  · exact c32_22.down
  · exact c32_23.down
  · exact c32_24.down
  · exact c32_25.down
  · exact c32_26.down
  · exact c32_27.down
  · exact c32_28.down
  · exact c32_29.down
  · exact c32_30.down
  · exact c32_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f33 : PLift (fitted p33) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_0 : PLift (covers (masks p33) 8 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_1 : PLift (covers (masks p33) 8 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_2 : PLift (covers (masks p33) 8 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_3 : PLift (covers (masks p33) 8 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_4 : PLift (covers (masks p33) 8 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_5 : PLift (covers (masks p33) 8 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_6 : PLift (covers (masks p33) 8 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_7 : PLift (covers (masks p33) 8 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_8 : PLift (covers (masks p33) 8 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_9 : PLift (covers (masks p33) 8 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_10 : PLift (covers (masks p33) 8 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_11 : PLift (covers (masks p33) 8 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_12 : PLift (covers (masks p33) 8 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_13 : PLift (covers (masks p33) 8 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_14 : PLift (covers (masks p33) 8 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_15 : PLift (covers (masks p33) 8 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_16 : PLift (covers (masks p33) 8 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_17 : PLift (covers (masks p33) 8 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_18 : PLift (covers (masks p33) 8 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_19 : PLift (covers (masks p33) 8 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_20 : PLift (covers (masks p33) 8 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_21 : PLift (covers (masks p33) 8 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_22 : PLift (covers (masks p33) 8 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_23 : PLift (covers (masks p33) 8 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_24 : PLift (covers (masks p33) 8 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_25 : PLift (covers (masks p33) 8 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_26 : PLift (covers (masks p33) 8 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_27 : PLift (covers (masks p33) 8 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_28 : PLift (covers (masks p33) 8 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_29 : PLift (covers (masks p33) 8 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_30 : PLift (covers (masks p33) 8 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c33_31 : PLift (covers (masks p33) 8 31) := ⟨by decide +kernel⟩

private theorem c33 (i : Fin 32) : covers (masks p33) p33.residual i.val := by
  fin_cases i
  · exact c33_0.down
  · exact c33_1.down
  · exact c33_2.down
  · exact c33_3.down
  · exact c33_4.down
  · exact c33_5.down
  · exact c33_6.down
  · exact c33_7.down
  · exact c33_8.down
  · exact c33_9.down
  · exact c33_10.down
  · exact c33_11.down
  · exact c33_12.down
  · exact c33_13.down
  · exact c33_14.down
  · exact c33_15.down
  · exact c33_16.down
  · exact c33_17.down
  · exact c33_18.down
  · exact c33_19.down
  · exact c33_20.down
  · exact c33_21.down
  · exact c33_22.down
  · exact c33_23.down
  · exact c33_24.down
  · exact c33_25.down
  · exact c33_26.down
  · exact c33_27.down
  · exact c33_28.down
  · exact c33_29.down
  · exact c33_30.down
  · exact c33_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f34 : PLift (fitted p34) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_0 : PLift (covers (masks p34) 7 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_1 : PLift (covers (masks p34) 7 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_2 : PLift (covers (masks p34) 7 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_3 : PLift (covers (masks p34) 7 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_4 : PLift (covers (masks p34) 7 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_5 : PLift (covers (masks p34) 7 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_6 : PLift (covers (masks p34) 7 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_7 : PLift (covers (masks p34) 7 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_8 : PLift (covers (masks p34) 7 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_9 : PLift (covers (masks p34) 7 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_10 : PLift (covers (masks p34) 7 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_11 : PLift (covers (masks p34) 7 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_12 : PLift (covers (masks p34) 7 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_13 : PLift (covers (masks p34) 7 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_14 : PLift (covers (masks p34) 7 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_15 : PLift (covers (masks p34) 7 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_16 : PLift (covers (masks p34) 7 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_17 : PLift (covers (masks p34) 7 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_18 : PLift (covers (masks p34) 7 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_19 : PLift (covers (masks p34) 7 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_20 : PLift (covers (masks p34) 7 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_21 : PLift (covers (masks p34) 7 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_22 : PLift (covers (masks p34) 7 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_23 : PLift (covers (masks p34) 7 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_24 : PLift (covers (masks p34) 7 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_25 : PLift (covers (masks p34) 7 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_26 : PLift (covers (masks p34) 7 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_27 : PLift (covers (masks p34) 7 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_28 : PLift (covers (masks p34) 7 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_29 : PLift (covers (masks p34) 7 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_30 : PLift (covers (masks p34) 7 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c34_31 : PLift (covers (masks p34) 7 31) := ⟨by decide +kernel⟩

private theorem c34 (i : Fin 32) : covers (masks p34) p34.residual i.val := by
  fin_cases i
  · exact c34_0.down
  · exact c34_1.down
  · exact c34_2.down
  · exact c34_3.down
  · exact c34_4.down
  · exact c34_5.down
  · exact c34_6.down
  · exact c34_7.down
  · exact c34_8.down
  · exact c34_9.down
  · exact c34_10.down
  · exact c34_11.down
  · exact c34_12.down
  · exact c34_13.down
  · exact c34_14.down
  · exact c34_15.down
  · exact c34_16.down
  · exact c34_17.down
  · exact c34_18.down
  · exact c34_19.down
  · exact c34_20.down
  · exact c34_21.down
  · exact c34_22.down
  · exact c34_23.down
  · exact c34_24.down
  · exact c34_25.down
  · exact c34_26.down
  · exact c34_27.down
  · exact c34_28.down
  · exact c34_29.down
  · exact c34_30.down
  · exact c34_31.down

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def f35 : PLift (fitted p35) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_0 : PLift (covers (masks p35) 6 0) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_1 : PLift (covers (masks p35) 6 1) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_2 : PLift (covers (masks p35) 6 2) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_3 : PLift (covers (masks p35) 6 3) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_4 : PLift (covers (masks p35) 6 4) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_5 : PLift (covers (masks p35) 6 5) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_6 : PLift (covers (masks p35) 6 6) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_7 : PLift (covers (masks p35) 6 7) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_8 : PLift (covers (masks p35) 6 8) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_9 : PLift (covers (masks p35) 6 9) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_10 : PLift (covers (masks p35) 6 10) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_11 : PLift (covers (masks p35) 6 11) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_12 : PLift (covers (masks p35) 6 12) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_13 : PLift (covers (masks p35) 6 13) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_14 : PLift (covers (masks p35) 6 14) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_15 : PLift (covers (masks p35) 6 15) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_16 : PLift (covers (masks p35) 6 16) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_17 : PLift (covers (masks p35) 6 17) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_18 : PLift (covers (masks p35) 6 18) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_19 : PLift (covers (masks p35) 6 19) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_20 : PLift (covers (masks p35) 6 20) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_21 : PLift (covers (masks p35) 6 21) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_22 : PLift (covers (masks p35) 6 22) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_23 : PLift (covers (masks p35) 6 23) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_24 : PLift (covers (masks p35) 6 24) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_25 : PLift (covers (masks p35) 6 25) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_26 : PLift (covers (masks p35) 6 26) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_27 : PLift (covers (masks p35) 6 27) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_28 : PLift (covers (masks p35) 6 28) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_29 : PLift (covers (masks p35) 6 29) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_30 : PLift (covers (masks p35) 6 30) := ⟨by decide +kernel⟩

set_option maxRecDepth 60000 in
set_option maxHeartbeats 0 in
private def c35_31 : PLift (covers (masks p35) 6 31) := ⟨by decide +kernel⟩

private theorem c35 (i : Fin 32) : covers (masks p35) p35.residual i.val := by
  fin_cases i
  · exact c35_0.down
  · exact c35_1.down
  · exact c35_2.down
  · exact c35_3.down
  · exact c35_4.down
  · exact c35_5.down
  · exact c35_6.down
  · exact c35_7.down
  · exact c35_8.down
  · exact c35_9.down
  · exact c35_10.down
  · exact c35_11.down
  · exact c35_12.down
  · exact c35_13.down
  · exact c35_14.down
  · exact c35_15.down
  · exact c35_16.down
  · exact c35_17.down
  · exact c35_18.down
  · exact c35_19.down
  · exact c35_20.down
  · exact c35_21.down
  · exact c35_22.down
  · exact c35_23.down
  · exact c35_24.down
  · exact c35_25.down
  · exact c35_26.down
  · exact c35_27.down
  · exact c35_28.down
  · exact c35_29.down
  · exact c35_30.down
  · exact c35_31.down

private theorem bank_fitted (i : Fin 36) : fitted (bank i) := by
  fin_cases i
  · exact f0.down
  · exact f1.down
  · exact f2.down
  · exact f3.down
  · exact f4.down
  · exact f5.down
  · exact f6.down
  · exact f7.down
  · exact f8.down
  · exact f9.down
  · exact f10.down
  · exact f11.down
  · exact f12.down
  · exact f13.down
  · exact f14.down
  · exact f15.down
  · exact f16.down
  · exact f17.down
  · exact f18.down
  · exact f19.down
  · exact f20.down
  · exact f21.down
  · exact f22.down
  · exact f23.down
  · exact f24.down
  · exact f25.down
  · exact f26.down
  · exact f27.down
  · exact f28.down
  · exact f29.down
  · exact f30.down
  · exact f31.down
  · exact f32.down
  · exact f33.down
  · exact f34.down
  · exact f35.down

private theorem bank_covers (i : Fin 36) :
    ∀ j : Fin 32, covers (masks (bank i)) (bank i).residual j.val := by
  fin_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4
  · exact c5
  · exact c6
  · exact c7
  · exact c8
  · exact c9
  · exact c10
  · exact c11
  · exact c12
  · exact c13
  · exact c14
  · exact c15
  · exact c16
  · exact c17
  · exact c18
  · exact c19
  · exact c20
  · exact c21
  · exact c22
  · exact c23
  · exact c24
  · exact c25
  · exact c26
  · exact c27
  · exact c28
  · exact c29
  · exact c30
  · exact c31
  · exact c32
  · exact c33
  · exact c34
  · exact c35

private theorem fixed_endpoints : ∀ t : Fin 15,
    ((edgeEnds t.val).1 = 0 ∨ (edgeEnds t.val).1 = 1) ∧
      (edgeEnds t.val).1 < (edgeEnds t.val).2 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem packet_exists :
    ∀ (d : Fin 4) (a : Fin 3) (b : Fin 8),
      1 ≤ d.val → a.val < d.val → b.val ≤ 8-d.val → d.val ≤ 1+a.val+b.val →
      ∃ i : Fin 36, (bank i).degree = d.val ∧ (bank i).near = a.val ∧ (bank i).far = b.val := by decide

theorem nine_vertex_cover (G : SimpleGraph V) (connected : G.Connected)
    [DecidableRel G.Adj] (size : G.edgeFinset.card = 16) :
    ∃ m ∈ [2251801971660822], ∃ e : V ↪ V, ∀ i j, G.Adj i j →
      m.testBit ((min (e i) (e j)).val*9+(max (e i) (e j)).val) = false := by
  obtain ⟨π,d,a,b,pos,hd,ha,hb,hp,root,near,far⟩ := normalize G connected size
  obtain ⟨i, hd', ha', hb'⟩ := packet_exists ⟨d, by omega⟩ ⟨a, by omega⟩ ⟨b, by omega⟩ pos ha hb hp
  let H := G.comap π
  let iso := SimpleGraph.Iso.comap π G
  have hcard : H.edgeFinset.card = 16 := iso.card_edgeFinset_eq.trans size
  have hconn : H.Connected := iso.connected_iff.mpr connected
  have valid := bank_fitted i
  have hfixed (t : Fin 15) : adjAt H t.val ↔ Bit (bank i).fixed t.val := by
    change G.Adj (π (edgeEnds t.val).1) (π (edgeEnds t.val).2) ↔ (bank i).fixed.testBit t.val = true
    rw [valid.1.1 t, hd', ha', hb']
    unfold pattern
    obtain ⟨h0 | h1, hlt⟩ := fixed_endpoints t
    · have hlep : 0 < (edgeEnds t.val).2.val := by rw [h0] at hlt; exact hlt
      simpa only [h0, if_pos, decide_eq_true_eq] using root (edgeEnds t.val).2 hlep
    · rw [h1, if_neg (by decide : (1 : V) ≠ 0)]
      by_cases hle : (edgeEnds t.val).2.val ≤ d
      · have hlep : 2 ≤ (edgeEnds t.val).2.val := by
          rw [h1] at hlt
          change 1 < (edgeEnds t.val).2.val at hlt
          omega
        simpa only [if_pos hle, decide_eq_true_eq] using near (edgeEnds t.val).2 hlep hle
      · simpa only [if_neg hle, decide_eq_true_eq] using far (edgeEnds t.val).2 (by omega)
  obtain ⟨m, hm, emb, avoid⟩ := decode H hconn hcard (bank i) hfixed valid (bank_covers i)
  refine ⟨m, hm, π.symm.toEmbedding.trans emb, ?_⟩
  intro u v huv
  apply avoid (π.symm u) (π.symm v)
  simpa only [H, SimpleGraph.comap_adj, π.apply_symm_apply] using huv

end OMA.NineVertexCover

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1_H1_R1.H2 := by
  classical
  intro G connected size
  rw [OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1.edgeNumber] at size
  exact OMA.NineVertexCover.nine_vertex_cover G connected size