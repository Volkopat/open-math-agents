import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1_H1_R1
import Mathlib

namespace OMA.EightVertexCover

private abbrev V := Fin 8

private def ends : Fin 28 → V × V :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]

private def edgeEnds (i : ℕ) : V × V := ends (Fin.ofNat 28 i)

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

private def forbidden (host : ℕ) (p q : V) : Bool :=
  host.testBit ((min p q).val * 8 + (max p q).val)

private def permOf (code : ℕ) (i : V) : V :=
  Fin.ofNat 8 ((code >>> (3*i.val)) % 8)

private structure Witness where
  absent : ℕ
  host : ℕ
  code : ℕ

private structure Packet where
  d : ℕ
  link : Bool
  k : ℕ
  fixed : ℕ
  residual : ℕ
  rows : List Witness

private def forbiddenEdge (row : Witness) (index : ℕ) : Bool :=
  let pair := edgeEnds index
  forbidden row.host (permOf row.code pair.1) (permOf row.code pair.2)

private def valid (packet : Packet) (row : Witness) : Prop :=
  row.host ∈ [36169948434793600, 70781333153792] ∧
  Function.Injective (permOf row.code) ∧
  (∀ i : Fin 13, packet.fixed.testBit i.val = true → forbiddenEdge row i.val = false) ∧
  (∀ i : Fin 15, forbiddenEdge row (i.val+13) = row.absent.testBit i.val)

private instance (packet : Packet) (row : Witness) : Decidable (valid packet row) := by
  unfold valid
  infer_instance

private def allowedLanes (row : Witness) : ℕ :=
  ((List.range 15).filter row.absent.testBit).foldr
    (fun i rest => (ones (2^15) ^^^ plane 15 i) &&& rest) (ones (2^15))

private def coveredLanes (packet : Packet) : ℕ :=
  packet.rows.foldr (fun row rest => allowedLanes row ||| rest) 0

private def covers (packet : Packet) : Prop :=
  coveredLanes packet &&& exactWeight 15 packet.residual = exactWeight 15 packet.residual

private instance (packet : Packet) : Decidable (covers packet) := by
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

private theorem cover_at {packet : Packet} {lane : ℕ} (hc : covers packet)
    (h : Bit (exactWeight 15 packet.residual) lane) :
    ∃ row ∈ packet.rows, Bit (allowedLanes row) lane := by
  unfold covers at hc
  have hb : Bit (coveredLanes packet &&& exactWeight 15 packet.residual) lane := by rw [hc]; exact h
  have hf : Bit (coveredLanes packet) lane := by
    exact (by simpa only [Bit, Nat.testBit_and, Bool.and_eq_true] using hb :
      Bit (coveredLanes packet) lane ∧ Bit (exactWeight 15 packet.residual) lane).1
  change Bit (packet.rows.foldr (fun row rest => allowedLanes row ||| rest) 0) lane at hf
  generalize packet.rows = rows at hf ⊢
  induction rows with
  | nil => simp [Bit] at hf
  | cons row rows ih =>
    simp only [List.foldr_cons, Bit, Nat.testBit_or, Bool.or_eq_true] at hf
    rcases hf with h | h
    · exact ⟨row, List.mem_cons_self, h⟩
    · obtain ⟨w, hm, hw⟩ := ih h
      exact ⟨w, List.mem_cons_of_mem _ hm, hw⟩

private theorem allowed_at {row : Witness} {t j : ℕ} (ht : t < 2^15)
    (hj : j < 15) (ha : Bit row.absent j) (h : Bit (allowedLanes row) t) :
    ¬ Bit (plane 15 j) t := by
  have hm : j ∈ (List.range 15).filter row.absent.testBit := by simp [hj, ha]
  let mask (i : ℕ) := ones (2^15) ^^^ plane 15 i
  change Bit (((List.range 15).filter row.absent.testBit).foldr
    (fun i rest => mask i &&& rest) (ones (2^15))) t at h
  generalize (List.range 15).filter row.absent.testBit = ls at hm h
  have hb : Bit (mask j) t := by
    induction ls with
    | nil => simp at hm
    | cons i ls ih =>
      simp only [List.foldr_cons, Bit, Nat.testBit_and, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hm with he | he
      · subst i; exact h.1
      · exact ih he h.2
  have hu := ones_bit.mpr ht
  change (ones (2^15)).testBit t = true at hu
  change (ones (2^15) ^^^ plane 15 j).testBit t = true at hb
  rw [Nat.testBit_xor, hu] at hb
  intro hh
  change (plane 15 j).testBit t = true at hh
  rw [hh] at hb
  contradiction

private theorem inLeft {L R : List V} (h : (L ++ R).Nodup) (i : ℕ)
    (hi : i < (L ++ R).length) : (L ++ R)[i] ∈ L ↔ i < L.length := by
  by_cases hL : i < L.length
  · rw [List.getElem_append_left hL]
    exact ⟨fun _ => hL, fun _ => List.getElem_mem (h := hL)⟩
  · have hR : L.length ≤ i := by omega
    rw [List.getElem_append_right hR]
    have hmem : R[i-L.length]'(by simp only [List.length_append] at hi; omega) ∈ R := List.getElem_mem _
    exact ⟨fun hm => (List.disjoint_left.mp h.disjoint hm hmem).elim,
      fun hh => (hL hh).elim⟩

private theorem pivot_normalization (G : SimpleGraph V) [DecidableRel G.Adj]
    (connected : G.Connected) (hsize : G.edgeFinset.card = 11) :
    ∃ (π : Equiv.Perm V) (d k : ℕ), (d = 1 ∨ d = 2) ∧ k ≤ 7-d ∧
      (∀ j : V, 0 < j.val → (G.Adj (π 0) (π j) ↔ j.val ≤ d)) ∧
      (∀ j : V, d < j.val → (G.Adj (π 1) (π j) ↔ j.val ≤ d+k)) := by
  have havg : ∑ v, G.degree v = 22 := by rw [G.sum_degrees_eq_twice_card_edges, hsize]
  have hsmall : ∃ v, G.degree v ≤ 2 := by
    by_contra! hh
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset V))
      (f := fun _ => (3 : ℕ)) (g := fun v => G.degree v) (fun v _ => by have := hh v; omega)
    rw [havg] at h
    norm_num [V] at h
  obtain ⟨v, hv⟩ := hsmall
  let N := G.neighborFinset v
  let d := N.card
  have hpos : 0 < d := connected.preconnected.degree_pos_of_nontrivial v
  have hd : d = 1 ∨ d = 2 := by change d ≤ 2 at hv; omega
  have hNv : v ∉ N := by simp [N]
  have hnL : 0 < N.toList.length := by rw [Finset.length_toList]; exact hpos
  let u : V := N.toList[0]
  let P : List V := v :: N.toList
  let R := Finset.univ \ insert v N
  let A := R.filter (G.Adj u)
  let B := R.filter (fun w => ¬G.Adj u w)
  let k := A.card
  let Q : List V := A.toList ++ B.toList
  let L : List V := P ++ Q
  have hR : R.card = 7-d := by
    dsimp [R]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_insert_of_notMem hNv]
    simp only [Finset.card_univ, Fintype.card_fin, V]
    change 8 - (d+1) = 7-d
    omega
  have hk : k ≤ 7-d := hR ▸ Finset.card_filter_le _ _
  have hAB : A.card + B.card = R.card := Finset.card_filter_add_card_filter_not (s := R) (G.Adj u)
  have hP : P.length = d+1 := by simp [P, d]
  have hQ : Q.length = 7-d := by simpa [Q, hR] using hAB
  have hL : L.length = 8 := by simp only [L, List.length_append, hP, hQ]; omega
  have hPmem (w : V) : w ∈ P ↔ w = v ∨ w ∈ N := by simp [P]
  have hRmem (w : V) : w ∈ R ↔ w ≠ v ∧ w ∉ N := by simp [R, not_or]
  have hQnodup : Q.Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, List.disjoint_left.mpr ?_⟩
    intro w hA hB
    simp only [Finset.mem_toList, A, B, Finset.mem_filter] at hA hB
    exact hB.2 hA.2
  have hLnodup : L.Nodup := by
    apply List.nodup_append'.mpr
    refine ⟨by simp [P, hNv, Finset.nodup_toList], hQnodup, List.disjoint_left.mpr ?_⟩
    intro w hw hw'
    have hr : w ∈ R := by
      simp only [Q, List.mem_append, Finset.mem_toList, A, B, Finset.mem_filter] at hw'
      exact hw'.elim And.left And.left
    exact (hPmem w).mp hw |>.elim ((hRmem w).mp hr).1 ((hRmem w).mp hr).2
  let f (i : V) : V := L[i.val]'(by rw [hL]; exact i.isLt)
  let π : Equiv.Perm V := Equiv.ofBijective f
    (Finite.injective_iff_bijective.mp (fun _ _ h => Fin.ext (hLnodup.getElem_inj_iff.mp h)))
  have hπ (i : V) : π i = f i := rfl
  have h0 : π 0 = v := by
    rw [hπ]
    dsimp [f, L]
    rw [List.getElem_append_left (by rw [hP]; omega)]
    rfl
  have h1 : π 1 = u := by
    rw [hπ]
    dsimp [f, L]
    rw [List.getElem_append_left (by rw [hP]; omega)]
    rfl
  refine ⟨π, d, k, hd, hk, ?_, ?_⟩
  · intro j hj
    have hne : π j ≠ v := fun h => by
      have eq := π.injective (h.trans h0.symm)
      have : j.val = 0 := congrArg Fin.val eq
      omega
    have hm : (π j ∈ P) ↔ j.val < d+1 := by
      rw [hπ]
      simpa only [hP] using inLeft hLnodup j.val (by rw [hL]; exact j.isLt)
    have hmem : π j ∈ N ↔ j.val < d+1 := by simpa [hPmem, hne] using hm
    rw [h0, ← G.mem_neighborFinset]
    change π j ∈ N ↔ j.val ≤ d
    exact hmem.trans (by omega)
  · intro j hj
    have hj' : P.length ≤ j.val := by rw [hP]; omega
    have hq : j.val-P.length < Q.length := by rw [hQ, hP]; have := j.isLt; omega
    have hf : π j = Q[j.val-P.length] := by
      rw [hπ]
      dsimp [f, L]
      exact List.getElem_append_right hj'
    have hp : π j ∈ Q := hf ▸ List.getElem_mem hq
    have hr : π j ∈ R := by
      simp only [Q, List.mem_append, Finset.mem_toList, A, B, Finset.mem_filter] at hp
      exact hp.elim And.left And.left
    have hm : (π j ∈ A) ↔ j.val-P.length < k := by
      rw [hf]
      simpa only [Finset.mem_toList, Finset.length_toList] using
        inLeft hQnodup (j.val-P.length) hq
    rw [h1]
    have hmem : π j ∈ A ↔ G.Adj u (π j) := by simp [A, hr]
    exact hmem.symm.trans (hm.trans (by rw [hP]; omega))

private def edgeAt (t : Fin 28) : Sym2 V := s((ends t).1, (ends t).2)

private theorem edges_inj : Function.Injective edgeAt := by decide

private theorem edges_onto : ∀ i j : V, i ≠ j →
    ∃ t : Fin 28, ends t = (i,j) ∨ ends t = (j,i) := by decide

private theorem fixed_pairs : ∀ t : Fin 13,
    ((edgeEnds t.val).1 = 0 ∨ (edgeEnds t.val).1 = 1) ∧
      (edgeEnds t.val).1 < (edgeEnds t.val).2 := by decide

private theorem forbidden_symm (m : ℕ) (p q : V) :
    forbidden m p q = forbidden m q p := by simp [forbidden, min_comm, max_comm]

private abbrev adjAt (G : SimpleGraph V) (i : ℕ) : Prop :=
  G.Adj (edgeEnds i).1 (edgeEnds i).2

private theorem edge_sum (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ j ∈ Finset.range 28, if adjAt G j then 1 else 0) = G.edgeFinset.card := by
  let selected := Finset.univ.filter fun t : Fin 28 => G.Adj (ends t).1 (ends t).2
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
        obtain ⟨t, ht | ht⟩ := edges_onto i j ha'.ne
        · exact ⟨t, by simpa [selected, ht] using ha', by simp [edgeAt, ht]⟩
        · exact ⟨t, by simpa [selected, ht] using ha'.symm, by simp [edgeAt, ht, Sym2.eq_swap]⟩
  have hcount : (∑ t : Fin 28, if G.Adj (ends t).1 (ends t).2 then 1 else 0) =
      G.edgeFinset.card := by
    rw [Finset.sum_boole]
    change selected.card = _
    rw [← Finset.card_image_of_injective _ edges_inj, himage]
  rw [← hcount, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have h : Fin.ofNat 28 i.val = i := by apply Fin.ext; simp
  simp only [adjAt, edgeEnds, h]

private theorem sum_range_shift (a b : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range (a+b), f i) =
      (∑ i ∈ Finset.range a, f i) + ∑ i ∈ Finset.range b, f (i+a) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show a+(b+1) = a+b+1 by omega, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    rw [Nat.add_comm a b, Nat.add_assoc]

private def pattern (d k : ℕ) (link : Bool) (p : V × V) : Bool :=
  if p.1 = 0 then decide (p.2.val ≤ d)
  else if d = 2 ∧ p.2 = 2 then link
  else decide (d < p.2.val ∧ p.2.val ≤ d+k)

private def shape (p : Packet) : Prop :=
  (∀ t : Fin 13, p.fixed.testBit t.val = pattern p.d p.k p.link (edgeEnds t.val)) ∧
    (∑ i ∈ Finset.range 13, if Bit p.fixed i then 1 else 0) + p.residual = 11

private instance (p : Packet) : Decidable (shape p) := by unfold shape; infer_instance

private theorem packet_cover (G : SimpleGraph V) [DecidableRel G.Adj] (size : G.edgeFinset.card = 11)
    (p : Packet) (count : (∑ i ∈ Finset.range 13, if Bit p.fixed i then 1 else 0) + p.residual = 11)
    (fixed : ∀ t : Fin 13, adjAt G t.val ↔ Bit p.fixed t.val)
    (pairs : ∀ w ∈ p.rows, valid p w) (cover : covers p) :
    ∃ m ∈ [36169948434793600, 70781333153792], ∃ e : V ↪ V,
      ∀ i j, G.Adj i j → forbidden m (e i) (e j) = false := by
  obtain ⟨t, ht, ht'⟩ := realizes (fun j => adjAt G (j+13)) 15
  have hfix : (∑ j ∈ Finset.range 13, if adjAt G j then 1 else 0) =
      ∑ j ∈ Finset.range 13, if Bit p.fixed j then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [fixed ⟨j, Finset.mem_range.mp hj⟩]
  have hfree : (∑ j ∈ Finset.range 15, if adjAt G (j+13) then 1 else 0) = laneCount 15 t := by
    unfold laneCount
    apply Finset.sum_congr rfl
    intro j hj
    simp only [ht' j (Finset.mem_range.mp hj)]
  have he := edge_sum G
  change (∑ j ∈ Finset.range (13+15), if adjAt G j then 1 else 0) = _ at he
  rw [sum_range_shift, hfix, hfree, size] at he
  have hl : laneCount 15 t = p.residual := by omega
  obtain ⟨w, hw, hwL⟩ := cover_at cover ((exactWeight_at ht).mpr hl)
  obtain ⟨hm, hinj, hknown, hunk⟩ := pairs w hw
  refine ⟨w.host, hm, ⟨permOf w.code, hinj⟩, ?_⟩
  have hrow (j : Fin 28) (h : G.Adj (ends j).1 (ends j).2) : forbiddenEdge w j.val = false := by
    have hh : Fin.ofNat 28 j.val = j := by apply Fin.ext; simp
    have he' : adjAt G j.val := by simpa only [adjAt, edgeEnds, hh] using h
    by_cases hj : j.val < 13
    · exact hknown ⟨j.val, hj⟩ ((fixed ⟨j.val, hj⟩).mp he')
    · let i : Fin 15 := ⟨j.val-13, by have := j.isLt; omega⟩
      have hi : i.val+13 = j.val := by dsimp [i]; omega
      rw [← hi, hunk i]
      apply Bool.eq_false_iff.mpr
      intro hb
      apply allowed_at ht i.isLt hb hwL
      exact (ht' _ i.isLt).mpr (hi ▸ he')
  intro i j ha
  obtain ⟨a, h | h⟩ := edges_onto i j ha.ne
  · have hr := hrow a (by simpa only [h] using ha)
    have hh : Fin.ofNat 28 a.val = a := by apply Fin.ext; simp
    simpa only [forbiddenEdge, edgeEnds, hh, h, Function.Embedding.coeFn_mk] using hr
  · have hr := hrow a (by simpa only [h] using ha.symm)
    have hh : Fin.ofNat 28 a.val = a := by apply Fin.ext; simp
    simpa only [forbiddenEdge, edgeEnds, hh, h, Function.Embedding.coeFn_mk,
      forbidden_symm w.host (permOf w.code j) (permOf w.code i)] using hr

private def packet0 : Packet :=
  ⟨1, false, 0, 1, 10, [
    ⟨3, 70781333153792, 14968107⟩,
    ⟨12, 70781333153792, 16322859⟩,
    ⟨48, 36169948434793600, 15835701⟩,
    ⟨192, 70781333153792, 16324651⟩,
    ⟨768, 36169948434793600, 15798517⟩,
    ⟨3072, 70781333153792, 13353515⟩,
    ⟨12288, 70781333153792, 13267499⟩,
    ⟨16385, 36169948434793600, 4603445⟩,
    ⟨16386, 36169948434793600, 4617781⟩,
    ⟨20, 70781333153792, 14487851⟩,
    ⟨24, 70781333153792, 13340971⟩,
    ⟨36, 36169948434793600, 9413173⟩,
    ⟨40, 36169948434793600, 10330677⟩,
    ⟨320, 70781333153792, 14489643⟩,
    ⟨384, 70781333153792, 13342763⟩,
    ⟨576, 70781333153792, 15098923⟩,
    ⟨640, 36169948434793600, 10293493⟩,
    ⟨5120, 70781333153792, 15933995⟩,
    ⟨6144, 36169948434793600, 15239413⟩,
    ⟨9216, 36169948434793600, 6064373⟩,
    ⟨10240, 70781333153792, 10428971⟩]⟩

private def packet1 : Packet :=
  ⟨1, false, 1, 129, 9, [
    ⟨33, 70781333153792, 14952861⟩,
    ⟨66, 36169948434793600, 9269813⟩,
    ⟨132, 36169948434793600, 9155125⟩,
    ⟨264, 36169948434793600, 6173237⟩,
    ⟨528, 36169948434793600, 15799861⟩,
    ⟨3072, 70781333153792, 13353515⟩,
    ⟨12288, 70781333153792, 13267499⟩,
    ⟨16385, 36169948434793600, 4603445⟩,
    ⟨34, 70781333153792, 14960029⟩,
    ⟨96, 70781333153792, 15149099⟩,
    ⟨16388, 36169948434793600, 4703797⟩,
    ⟨16512, 70781333153792, 13866027⟩,
    ⟨65, 70781333153792, 15010205⟩,
    ⟨258, 36169948434793600, 5370421⟩,
    ⟨520, 36169948434793600, 10294837⟩,
    ⟨1040, 36169948434793600, 15341109⟩,
    ⟨2064, 70781333153792, 10264989⟩,
    ⟨1536, 70781333153792, 16335403⟩,
    ⟨2560, 70781333153792, 14500395⟩,
    ⟨129, 70781333153792, 15239581⟩,
    ⟨4097, 36169948434793600, 8961589⟩,
    ⟨8193, 36169948434793600, 5291573⟩]⟩

private def packet2 : Packet :=
  ⟨1, false, 2, 385, 8, [
    ⟨36, 36169948434793600, 9413173⟩,
    ⟨66, 36169948434793600, 9269813⟩,
    ⟨144, 36169948434793600, 15348277⟩,
    ⟨264, 36169948434793600, 6173237⟩,
    ⟨513, 36169948434793600, 9405557⟩,
    ⟨3072, 70781333153792, 13159979⟩,
    ⟨12288, 70781333153792, 13245995⟩,
    ⟨16385, 36169948434793600, 14824565⟩,
    ⟨514, 70781333153792, 15024541⟩,
    ⟨576, 70781333153792, 15084573⟩,
    ⟨16392, 70781333153792, 5476765⟩,
    ⟨16640, 70781333153792, 9149469⟩,
    ⟨1025, 36169948434793600, 10323061⟩,
    ⟨2049, 36169948434793600, 15828085⟩]⟩

private def packet3 : Packet :=
  ⟨1, false, 3, 897, 7, [
    ⟨36, 36169948434793600, 9413173⟩,
    ⟨66, 36169948434793600, 9412725⟩,
    ⟨513, 36169948434793600, 9405557⟩,
    ⟨4104, 70781333153792, 3240349⟩,
    ⟨8208, 70781333153792, 8745373⟩,
    ⟨16512, 70781333153792, 5307421⟩,
    ⟨3328, 70781333153792, 11512844⟩,
    ⟨258, 36169948434793600, 15835253⟩,
    ⟨1025, 36169948434793600, 10323061⟩,
    ⟨4160, 70781333153792, 2784285⟩,
    ⟨328, 36169948434793600, 13273183⟩,
    ⟨1544, 70781333153792, 16097676⟩,
    ⟨4608, 70781333153792, 2780701⟩]⟩

private def packet4 : Packet :=
  ⟨1, false, 4, 1921, 6, [
    ⟨56, 36169948434793600, 13902623⟩,
    ⟨386, 36169948434793600, 13903967⟩,
    ⟨3073, 36169948434793600, 13911135⟩,
    ⟨12289, 36169948434793600, 14025823⟩,
    ⟨3076, 36169948434793600, 13975647⟩,
    ⟨88, 36169948434793600, 13959967⟩,
    ⟨12320, 36169948434793600, 14033439⟩,
    ⟨896, 36169948434793600, 13965343⟩,
    ⟨102, 36169948434793600, 4413647⟩,
    ⟨23040, 70781333153792, 11640370⟩,
    ⟨26112, 70781333153792, 9805362⟩,
    ⟨523, 36169948434793600, 5273485⟩,
    ⟨165, 36169948434793600, 5258701⟩,
    ⟨20800, 70781333153792, 11661874⟩,
    ⟨531, 36169948434793600, 8943501⟩,
    ⟨24588, 70781333153792, 9826418⟩,
    ⟨10336, 36169948434793600, 9131535⟩,
    ⟨5250, 36169948434793600, 5928461⟩,
    ⟨293, 36169948434793600, 8928717⟩,
    ⟨2626, 36169948434793600, 9167053⟩,
    ⟨16529, 70781333153792, 11765362⟩,
    ⟨4120, 70781333153792, 7827596⟩,
    ⟨1121, 36169948434793600, 4357325⟩,
    ⟨8262, 36169948434793600, 9111501⟩,
    ⟨22020, 70781333153792, 13741637⟩,
    ⟨2580, 36169948434793600, 13287631⟩,
    ⟨75, 36169948434793600, 5259149⟩,
    ⟨388, 36169948434793600, 13961311⟩]⟩

private def packet5 : Packet :=
  ⟨1, false, 5, 3969, 5, [
    ⟨45, 36169948434793600, 5345165⟩,
    ⟨450, 36169948434793600, 15838277⟩,
    ⟨3585, 36169948434793600, 15852613⟩,
    ⟨4618, 36169948434793600, 5918927⟩,
    ⟨9284, 36169948434793600, 15407301⟩,
    ⟨4768, 36169948434793600, 5920271⟩,
    ⟨4115, 36169948434793600, 15255429⟩,
    ⟨17480, 36169948434793600, 16335557⟩,
    ⟨17540, 36169948434793600, 16336453⟩,
    ⟨10290, 70781333153792, 10433157⟩,
    ⟨8600, 70781333153792, 11498564⟩,
    ⟨27140, 70781333153792, 10071621⟩,
    ⟨4385, 36169948434793600, 15256773⟩,
    ⟨2388, 70781333153792, 12444740⟩,
    ⟨537, 36169948434793600, 15800197⟩,
    ⟨170, 36169948434793600, 5789903⟩,
    ⟨30784, 70781333153792, 9036741⟩,
    ⟨9008, 70781333153792, 12399492⟩,
    ⟨23808, 70781333153792, 7545797⟩,
    ⟨705, 36169948434793600, 5475533⟩,
    ⟨310, 70781333153792, 6231876⟩,
    ⟨2315, 70781333153792, 8102724⟩,
    ⟨2225, 70781333153792, 8104516⟩,
    ⟨150, 36169948434793600, 15348613⟩,
    ⟨102, 36169948434793600, 4413647⟩]⟩

private def packet6 : Packet :=
  ⟨1, false, 6, 8065, 4, [
    ⟨107, 70781333153792, 16295685⟩,
    ⟨2836, 70781333153792, 12430404⟩,
    ⟨13504, 70781333153792, 13505989⟩,
    ⟨16525, 70781333153792, 13694149⟩,
    ⟨17458, 70781333153792, 7068740⟩,
    ⟨29440, 70781333153792, 6972357⟩,
    ⟨14342, 70781333153792, 5946948⟩,
    ⟨1984, 70781333153792, 13155268⟩,
    ⟨3097, 70781333153792, 4701508⟩,
    ⟨18656, 70781333153792, 7019460⟩,
    ⟨1573, 70781333153792, 16339652⟩,
    ⟨12568, 70781333153792, 11369540⟩,
    ⟨18954, 70781333153792, 5201476⟩,
    ⟨342, 70781333153792, 6088516⟩,
    ⟨10529, 70781333153792, 10430021⟩,
    ⟨598, 70781333153792, 14525189⟩,
    ⟨2588, 70781333153792, 5816132⟩]⟩

private def packet7 : Packet :=
  ⟨2, false, 0, 3, 9, [
    ⟨33, 70781333153792, 14952875⟩,
    ⟨66, 36169948434793600, 9269813⟩,
    ⟨132, 36169948434793600, 9155125⟩,
    ⟨264, 36169948434793600, 6173237⟩,
    ⟨528, 36169948434793600, 15799861⟩,
    ⟨3072, 70781333153792, 13353515⟩,
    ⟨12288, 70781333153792, 13267499⟩,
    ⟨16385, 36169948434793600, 4603445⟩,
    ⟨34, 70781333153792, 14960043⟩,
    ⟨96, 70781333153792, 15149099⟩,
    ⟨16388, 36169948434793600, 4703797⟩,
    ⟨16512, 70781333153792, 13866027⟩,
    ⟨65, 70781333153792, 15010219⟩,
    ⟨258, 36169948434793600, 5370421⟩,
    ⟨520, 36169948434793600, 10294837⟩,
    ⟨1040, 36169948434793600, 15341109⟩,
    ⟨2064, 70781333153792, 10265003⟩,
    ⟨1536, 70781333153792, 16335403⟩,
    ⟨2560, 70781333153792, 14500395⟩,
    ⟨129, 70781333153792, 15239595⟩,
    ⟨4097, 36169948434793600, 8961589⟩,
    ⟨8193, 36169948434793600, 5291573⟩]⟩

private def packet8 : Packet :=
  ⟨2, false, 1, 259, 8, [
    ⟨36, 36169948434793600, 9413173⟩,
    ⟨66, 36169948434793600, 9269813⟩,
    ⟨144, 36169948434793600, 15348277⟩,
    ⟨264, 36169948434793600, 6173237⟩,
    ⟨513, 36169948434793600, 9405557⟩,
    ⟨3072, 70781333153792, 13159979⟩,
    ⟨12288, 70781333153792, 13245995⟩,
    ⟨16385, 36169948434793600, 14824565⟩,
    ⟨514, 70781333153792, 15024555⟩,
    ⟨576, 70781333153792, 15084573⟩,
    ⟨16392, 70781333153792, 5476779⟩,
    ⟨16640, 70781333153792, 9149469⟩,
    ⟨1025, 36169948434793600, 10323061⟩,
    ⟨2049, 36169948434793600, 15828085⟩]⟩

private def packet9 : Packet :=
  ⟨2, false, 2, 771, 7, [
    ⟨36, 36169948434793600, 9413173⟩,
    ⟨66, 36169948434793600, 9412725⟩,
    ⟨513, 36169948434793600, 9405557⟩,
    ⟨4104, 70781333153792, 3240363⟩,
    ⟨8208, 70781333153792, 8745387⟩,
    ⟨16512, 70781333153792, 5307421⟩,
    ⟨3328, 70781333153792, 11512844⟩,
    ⟨258, 36169948434793600, 15835253⟩,
    ⟨1025, 36169948434793600, 10323061⟩,
    ⟨4160, 70781333153792, 2784285⟩,
    ⟨328, 36169948434793600, 13273183⟩,
    ⟨2568, 36169948434793600, 13287519⟩,
    ⟨4608, 70781333153792, 2780701⟩]⟩

private def packet10 : Packet :=
  ⟨2, false, 3, 1795, 6, [
    ⟨56, 36169948434793600, 13902623⟩,
    ⟨386, 36169948434793600, 13903967⟩,
    ⟨3073, 36169948434793600, 13911135⟩,
    ⟨12289, 36169948434793600, 14025823⟩,
    ⟨3076, 36169948434793600, 13975647⟩,
    ⟨21056, 36169948434793600, 2049677⟩,
    ⟨88, 36169948434793600, 13959967⟩,
    ⟨896, 36169948434793600, 13965371⟩,
    ⟨102, 36169948434793600, 4413647⟩,
    ⟨12290, 36169948434793600, 14032991⟩,
    ⟨523, 36169948434793600, 5273485⟩,
    ⟨16608, 36169948434793600, 1981581⟩,
    ⟨533, 36169948434793600, 9144205⟩,
    ⟨24864, 36169948434793600, 13733517⟩,
    ⟨24588, 70781333153792, 9826418⟩,
    ⟨17426, 70781333153792, 11776114⟩,
    ⟨6688, 36169948434793600, 8644237⟩,
    ⟨388, 36169948434793600, 13961311⟩,
    ⟨8770, 36169948434793600, 9139725⟩,
    ⟨1572, 36169948434793600, 5498381⟩,
    ⟨22784, 36169948434793600, 14435981⟩,
    ⟨135, 36169948434793600, 4341645⟩,
    ⟨1376, 36169948434793600, 8518797⟩,
    ⟨2593, 36169948434793600, 9039373⟩,
    ⟨263, 36169948434793600, 671629⟩,
    ⟨26752, 36169948434793600, 14561421⟩,
    ⟨536, 36169948434793600, 13963551⟩,
    ⟨83, 36169948434793600, 8929165⟩]⟩

private def packet11 : Packet :=
  ⟨2, false, 4, 3843, 5, [
    ⟨45, 36169948434793600, 5345165⟩,
    ⟨450, 36169948434793600, 15838277⟩,
    ⟨15360, 36169948434793600, 14037135⟩,
    ⟨16410, 70781333153792, 9146739⟩,
    ⟨17952, 36169948434793600, 1992333⟩,
    ⟨4673, 36169948434793600, 5455373⟩,
    ⟨277, 70781333153792, 10257779⟩,
    ⟨26752, 36169948434793600, 14561421⟩,
    ⟨5252, 36169948434793600, 6014477⟩,
    ⟨8992, 36169948434793600, 12736143⟩,
    ⟨2070, 70781333153792, 10264947⟩,
    ⟨360, 36169948434793600, 15350853⟩,
    ⟨8776, 36169948434793600, 15418949⟩,
    ⟨1155, 36169948434793600, 5270223⟩,
    ⟨22784, 36169948434793600, 14435981⟩,
    ⟨25856, 36169948434793600, 14550669⟩,
    ⟨4115, 36169948434793600, 15255429⟩,
    ⟨3712, 36169948434793600, 10346637⟩,
    ⟨16608, 36169948434793600, 1981581⟩,
    ⟨523, 36169948434793600, 5273485⟩]⟩

private def packet12 : Packet :=
  ⟨2, false, 5, 7939, 4, [
    ⟨928, 36169948434793600, 9206925⟩,
    ⟨13376, 36169948434793600, 10421901⟩,
    ⟨18752, 36169948434793600, 13647501⟩,
    ⟨22656, 36169948434793600, 16385677⟩,
    ⟨1063, 70781333153792, 16303301⟩,
    ⟨8732, 70781333153792, 4615877⟩,
    ⟨203, 70781333153792, 15407301⟩,
    ⟨8467, 70781333153792, 10425541⟩,
    ⟨18976, 36169948434793600, 14837389⟩,
    ⟨5148, 70781333153792, 3239621⟩,
    ⟨8416, 36169948434793600, 1293453⟩,
    ⟨1547, 70781333153792, 15418053⟩,
    ⟨4167, 70781333153792, 16389317⟩,
    ⟨25728, 36169948434793600, 16270989⟩]⟩

private def packet13 : Packet :=
  ⟨2, true, 0, 131, 8, [
    ⟨36, 36169948434793600, 9413173⟩,
    ⟨66, 36169948434793600, 9269813⟩,
    ⟨144, 36169948434793600, 15348277⟩,
    ⟨264, 36169948434793600, 6173237⟩,
    ⟨513, 36169948434793600, 9248309⟩,
    ⟨3072, 70781333153792, 13353515⟩,
    ⟨12288, 70781333153792, 13267499⟩,
    ⟨16385, 36169948434793600, 4603445⟩,
    ⟨520, 36169948434793600, 10294837⟩,
    ⟨16640, 70781333153792, 10196011⟩,
    ⟨48, 36169948434793600, 15835701⟩,
    ⟨130, 36169948434793600, 9040437⟩,
    ⟨192, 70781333153792, 16324651⟩,
    ⟨80, 36169948434793600, 15807029⟩,
    ⟨1028, 36169948434793600, 9147957⟩,
    ⟨2052, 36169948434793600, 5477941⟩]⟩

private def packet14 : Packet :=
  ⟨2, true, 1, 387, 7, [
    ⟨36, 36169948434793600, 9413173⟩,
    ⟨66, 36169948434793600, 9269813⟩,
    ⟨144, 36169948434793600, 15348277⟩,
    ⟨264, 36169948434793600, 6173237⟩,
    ⟨513, 36169948434793600, 9405557⟩,
    ⟨3072, 70781333153792, 13159979⟩,
    ⟨12288, 70781333153792, 13245995⟩,
    ⟨16385, 36169948434793600, 14824565⟩,
    ⟨544, 70781333153792, 15027229⟩,
    ⟨132, 36169948434793600, 9155125⟩,
    ⟨80, 36169948434793600, 15807029⟩,
    ⟨16390, 36169948434793600, 4673823⟩]⟩

private def packet15 : Packet :=
  ⟨2, true, 2, 899, 6, [
    ⟨36, 36169948434793600, 9413173⟩,
    ⟨66, 36169948434793600, 9412725⟩,
    ⟨513, 36169948434793600, 9405557⟩,
    ⟨4224, 70781333153792, 3243037⟩,
    ⟨8448, 70781333153792, 8748061⟩,
    ⟨17408, 70781333153792, 5303837⟩,
    ⟨40, 36169948434793600, 10330677⟩,
    ⟨2060, 36169948434793600, 5935391⟩]⟩

private def packet16 : Packet :=
  ⟨2, true, 3, 1923, 5, [
    ⟨56, 36169948434793600, 13902623⟩,
    ⟨386, 36169948434793600, 13903967⟩,
    ⟨3073, 36169948434793600, 13911135⟩,
    ⟨12289, 36169948434793600, 14025823⟩,
    ⟨3076, 36169948434793600, 13975647⟩,
    ⟨4674, 36169948434793600, 5469709⟩,
    ⟨24768, 70781333153792, 9826866⟩,
    ⟨525, 36169948434793600, 5474189⟩,
    ⟨340, 36169948434793600, 13273295⟩,
    ⟨23040, 70781333153792, 11640370⟩,
    ⟨17696, 70781333153792, 11776562⟩,
    ⟨102, 36169948434793600, 4413647⟩,
    ⟨13312, 70781333153792, 7695884⟩,
    ⟨16529, 70781333153792, 11765362⟩,
    ⟨24834, 36169948434793600, 14558789⟩,
    ⟨388, 36169948434793600, 13961311⟩]⟩

private def packet17 : Packet :=
  ⟨2, true, 4, 3971, 4, [
    ⟨45, 36169948434793600, 5345165⟩,
    ⟨450, 36169948434793600, 15838277⟩,
    ⟨3585, 36169948434793600, 15852613⟩,
    ⟨4618, 36169948434793600, 5918927⟩,
    ⟨17540, 36169948434793600, 16336453⟩,
    ⟨30784, 70781333153792, 9036741⟩,
    ⟨8498, 70781333153792, 12530756⟩,
    ⟨8776, 36169948434793600, 15418949⟩,
    ⟨4115, 36169948434793600, 15255429⟩,
    ⟨4504, 70781333153792, 7828548⟩,
    ⟨228, 36169948434793600, 5487629⟩,
    ⟨17760, 70781333153792, 5184452⟩,
    ⟨26784, 70781333153792, 11212740⟩,
    ⟨8476, 70781333153792, 8748229⟩]⟩

private def packet18 : Packet :=
  ⟨2, true, 5, 8067, 3, [
    ⟨107, 70781333153792, 15149253⟩,
    ⟨2836, 70781333153792, 12430404⟩,
    ⟨13504, 70781333153792, 13505989⟩,
    ⟨16525, 70781333153792, 13694149⟩,
    ⟨17458, 70781333153792, 7068740⟩,
    ⟨23296, 70781333153792, 11115972⟩,
    ⟨12309, 70781333153792, 5927621⟩,
    ⟨3968, 70781333153792, 4675524⟩,
    ⟨4174, 70781333153792, 15342789⟩]⟩

private def bank : Fin 19 → Packet := ![packet0, packet1, packet2, packet3, packet4, packet5, packet6, packet7, packet8, packet9, packet10, packet11, packet12, packet13, packet14, packet15, packet16, packet17, packet18]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check0 :
    PLift (shape packet0 ∧ (∀ w ∈ packet0.rows, valid packet0 w) ∧ covers packet0) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check1 :
    PLift (shape packet1 ∧ (∀ w ∈ packet1.rows, valid packet1 w) ∧ covers packet1) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check2 :
    PLift (shape packet2 ∧ (∀ w ∈ packet2.rows, valid packet2 w) ∧ covers packet2) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check3 :
    PLift (shape packet3 ∧ (∀ w ∈ packet3.rows, valid packet3 w) ∧ covers packet3) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check4 :
    PLift (shape packet4 ∧ (∀ w ∈ packet4.rows, valid packet4 w) ∧ covers packet4) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check5 :
    PLift (shape packet5 ∧ (∀ w ∈ packet5.rows, valid packet5 w) ∧ covers packet5) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check6 :
    PLift (shape packet6 ∧ (∀ w ∈ packet6.rows, valid packet6 w) ∧ covers packet6) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check7 :
    PLift (shape packet7 ∧ (∀ w ∈ packet7.rows, valid packet7 w) ∧ covers packet7) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check8 :
    PLift (shape packet8 ∧ (∀ w ∈ packet8.rows, valid packet8 w) ∧ covers packet8) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check9 :
    PLift (shape packet9 ∧ (∀ w ∈ packet9.rows, valid packet9 w) ∧ covers packet9) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check10 :
    PLift (shape packet10 ∧ (∀ w ∈ packet10.rows, valid packet10 w) ∧ covers packet10) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check11 :
    PLift (shape packet11 ∧ (∀ w ∈ packet11.rows, valid packet11 w) ∧ covers packet11) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check12 :
    PLift (shape packet12 ∧ (∀ w ∈ packet12.rows, valid packet12 w) ∧ covers packet12) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check13 :
    PLift (shape packet13 ∧ (∀ w ∈ packet13.rows, valid packet13 w) ∧ covers packet13) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check14 :
    PLift (shape packet14 ∧ (∀ w ∈ packet14.rows, valid packet14 w) ∧ covers packet14) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check15 :
    PLift (shape packet15 ∧ (∀ w ∈ packet15.rows, valid packet15 w) ∧ covers packet15) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check16 :
    PLift (shape packet16 ∧ (∀ w ∈ packet16.rows, valid packet16 w) ∧ covers packet16) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check17 :
    PLift (shape packet17 ∧ (∀ w ∈ packet17.rows, valid packet17 w) ∧ covers packet17) :=
  ⟨by decide +kernel⟩

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private def check18 :
    PLift (shape packet18 ∧ (∀ w ∈ packet18.rows, valid packet18 w) ∧ covers packet18) :=
  ⟨by decide +kernel⟩

private theorem bank_checked (i : Fin 19) :
    shape (bank i) ∧ (∀ w ∈ (bank i).rows, valid (bank i) w) ∧ covers (bank i) := by
  fin_cases i
  · exact check0.down
  · exact check1.down
  · exact check2.down
  · exact check3.down
  · exact check4.down
  · exact check5.down
  · exact check6.down
  · exact check7.down
  · exact check8.down
  · exact check9.down
  · exact check10.down
  · exact check11.down
  · exact check12.down
  · exact check13.down
  · exact check14.down
  · exact check15.down
  · exact check16.down
  · exact check17.down
  · exact check18.down

set_option maxRecDepth 12000 in
private theorem packet_exists :
    ∀ (d : Fin 3) (a : Bool) (k : Fin 7),
      (d.val = 1 ∨ d.val = 2) → (a = true → d.val = 2) → k.val ≤ 7-d.val →
      ∃ i : Fin 19, (bank i).d = d.val ∧ (bank i).link = a ∧ (bank i).k = k.val := by decide

theorem eight_vertex_cover (G : SimpleGraph V) (connected : G.Connected)
    [DecidableRel G.Adj] (size : G.edgeFinset.card = 11) :
    ∃ m ∈ [36169948434793600, 70781333153792], ∃ e : V ↪ V, ∀ i j, G.Adj i j →
      m.testBit ((min (e i) (e j)).val*8+(max (e i) (e j)).val) = false := by
  obtain ⟨π,d,k,hd,hk,root,pivot⟩ := pivot_normalization G connected size
  let a := if d = 2 then decide (G.Adj (π 1) (π 2)) else false
  have hda : a = true → d = 2 := by
    dsimp [a]
    split <;> simp_all
  obtain ⟨i, hd', ha', hk'⟩ := packet_exists ⟨d, by omega⟩ a ⟨k, by omega⟩ hd hda hk
  let H := G.comap π
  have hcard : H.edgeFinset.card = 11 := ((SimpleGraph.Iso.comap π G).card_edgeFinset_eq).trans size
  obtain ⟨⟨bits,count⟩, witnesses, cover⟩ := bank_checked i
  have hfixed (t : Fin 13) : adjAt H t.val ↔ Bit (bank i).fixed t.val := by
    change G.Adj (π (edgeEnds t.val).1) (π (edgeEnds t.val).2) ↔ (bank i).fixed.testBit t.val = true
    rw [bits t, hd', hk', ha']
    unfold pattern
    obtain ⟨h0 | h1, hlt⟩ := fixed_pairs t
    · have hpos : 0 < (edgeEnds t.val).2.val := by
        rw [h0] at hlt
        exact hlt
      have h := root (edgeEnds t.val).2 hpos
      simpa only [h0, if_pos, decide_eq_true_eq] using h
    · rw [h1, if_neg (by decide : (1 : V) ≠ 0)]
      by_cases hh : d = 2 ∧ (edgeEnds t.val).2 = 2
      · rw [if_pos hh, hh.2]
        simp [a, hh.1]
      · have hlo : 1 < (edgeEnds t.val).2.val := by
          rw [h1] at hlt
          exact hlt
        have hgt : d < (edgeEnds t.val).2.val := by
          by_contra! hc
          apply hh
          refine ⟨by omega, Fin.ext ?_⟩
          change (edgeEnds t.val).2.val = 2
          omega
        simpa only [if_neg hh, decide_eq_true_eq, hgt, true_and] using pivot (edgeEnds t.val).2 hgt
  obtain ⟨m, hm, emb, avoid⟩ := packet_cover H hcard (bank i) count hfixed witnesses cover
  refine ⟨m, hm, π.symm.toEmbedding.trans emb, ?_⟩
  intro u v huv
  apply avoid (π.symm u) (π.symm v)
  simpa only [H, SimpleGraph.comap_adj, π.apply_symm_apply] using huv

end OMA.EightVertexCover

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1_H1_R1.H1 := by
  classical
  intro G connected size
  rw [OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H1_R1.edgeNumber] at size
  exact OMA.EightVertexCover.eight_vertex_cover G connected size