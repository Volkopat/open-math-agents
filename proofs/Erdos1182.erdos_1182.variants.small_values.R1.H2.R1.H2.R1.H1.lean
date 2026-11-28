import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1

/-! # Common edge bound for the two 15-vertex hosts (Erdos 1182, order 8)

We prove `OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1.H1`:
for the two explicit 15-vertex graphs `C 0, C 1` and any pair of embeddings
`f : Fin 2 → Fin 8 ↪ Fin 15`, the intersection `D := ⨅ a, (C a)ᶜ.comap (f a)`
satisfies `D.edgeSet.ncard ≤ 20` (in fact without needing `D.Connected`).

Let `B0 := (C 0)ᶜ` and `B1 := (C 1)ᶜ`. Using fast pattern-matched adjacency
tables and incremental kernel-checked enumeration:
1. Every 8-vertex induced subgraph of `B0` with at least 21 edges has at most 22
   edges and contains one of the 5 explicit 6-cliques of `B0`.
2. Every 5-clique of `B1` has vertex set equal to one of 11 explicit 5-element
   lists, and any two distinct 5-cliques of `B1` intersect in at most 2 vertices.
3. If `D` had at least 21 edges, then `G0 := B0.comap (f 0)` would have at most
   22 edges, so `D` omits at most one edge of `G0`. Deleting at most one edge
   from a 6-clique `K` of `G0` leaves two distinct 5-cliques `K.erase u` and
   `K.erase v` in `D` intersecting in 4 vertices, contradicting (2) via `f 1`.
-/

namespace Erdos1182H1

open SimpleGraph Finset

private def mask0 : ℕ := 822777387642256703234551838076830900798754331299012273175546532
private def mask1 : ℕ := 822764833055638660808762661315316885505752648441781026290401700

/-- Fast pattern-matched adjacency predicate for `B0 = (C 0)ᶜ`. -/
private def adj0 (i j : ℕ) : Bool :=
  match i with
  | 0 => match j with | 1 | 3 | 4 | 6 | 8 | 10 | 12 | 13 => true | _ => false
  | 1 => match j with | 0 | 2 | 3 | 5 | 7 | 10 | 12 | 13 => true | _ => false
  | 2 => match j with | 1 | 5 | 7 | 9 | 10 | 11 | 13 | 14 => true | _ => false
  | 3 => match j with | 0 | 1 | 4 | 6 | 8 | 10 | 12 | 13 => true | _ => false
  | 4 => match j with | 0 | 3 | 6 | 8 | 9 | 11 | 12 | 14 => true | _ => false
  | 5 => match j with | 1 | 2 | 7 | 9 | 10 | 11 | 13 | 14 => true | _ => false
  | 6 => match j with | 0 | 3 | 4 | 8 | 9 | 11 | 12 | 14 => true | _ => false
  | 7 => match j with | 1 | 2 | 5 | 9 | 10 | 11 | 13 | 14 => true | _ => false
  | 8 => match j with | 0 | 3 | 4 | 6 | 9 | 11 | 12 | 14 => true | _ => false
  | 9 => match j with | 2 | 4 | 5 | 6 | 7 | 8 | 11 | 14 => true | _ => false
  | 10 => match j with | 0 | 1 | 2 | 3 | 5 | 7 | 12 | 13 => true | _ => false
  | 11 => match j with | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 14 => true | _ => false
  | 12 => match j with | 0 | 1 | 3 | 4 | 6 | 8 | 10 | 13 => true | _ => false
  | 13 => match j with | 0 | 1 | 2 | 3 | 5 | 7 | 10 | 12 => true | _ => false
  | 14 => match j with | 2 | 4 | 5 | 6 | 7 | 8 | 9 | 11 => true | _ => false
  | _ => false

/-- Fast pattern-matched adjacency predicate for `B1 = (C 1)ᶜ`. -/
private def adj1 (i j : ℕ) : Bool :=
  match i with
  | 0 => match j with | 1 | 3 | 4 | 6 | 9 | 10 | 11 | 12 | 13 | 14 => true | _ => false
  | 1 => match j with | 0 | 2 | 5 | 7 | 9 | 10 | 11 | 12 | 13 | 14 => true | _ => false
  | 2 => match j with | 1 | 3 | 5 | 7 | 8 | 10 | 11 | 13 | 14 => true | _ => false
  | 3 => match j with | 0 | 2 | 4 | 6 | 8 | 10 | 11 | 13 | 14 => true | _ => false
  | 4 => match j with | 0 | 3 | 5 | 6 | 8 | 9 | 11 | 12 | 14 => true | _ => false
  | 5 => match j with | 1 | 2 | 4 | 7 | 8 | 9 | 11 | 12 | 14 => true | _ => false
  | 6 => match j with | 0 | 3 | 4 | 7 | 8 | 9 | 10 | 12 | 13 => true | _ => false
  | 7 => match j with | 1 | 2 | 5 | 6 | 8 | 9 | 10 | 12 | 13 => true | _ => false
  | 8 => match j with | 2 | 3 | 4 | 5 | 6 | 7 | 10 | 12 | 14 => true | _ => false
  | 9 => match j with | 0 | 1 | 4 | 5 | 6 | 7 | 11 | 12 | 13 => true | _ => false
  | 10 => match j with | 0 | 1 | 2 | 3 | 6 | 7 | 8 | 12 | 13 | 14 => true | _ => false
  | 11 => match j with | 0 | 1 | 2 | 3 | 4 | 5 | 9 | 13 | 14 => true | _ => false
  | 12 => match j with | 0 | 1 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 14 => true | _ => false
  | 13 => match j with | 0 | 1 | 2 | 3 | 6 | 7 | 9 | 10 | 11 => true | _ => false
  | 14 => match j with | 0 | 1 | 2 | 3 | 4 | 5 | 8 | 10 | 11 | 12 => true | _ => false
  | _ => false

private def k6List0 : List (List ℕ) :=
  [[0, 1, 3, 10, 12, 13], [0, 3, 4, 6, 8, 12], [1, 2, 5, 7, 10, 13],
   [2, 5, 7, 9, 11, 14], [4, 6, 8, 9, 11, 14]]

private def k5List1 : List (List ℕ) :=
  [[0, 1, 9, 11, 13], [0, 1, 10, 12, 14], [0, 3, 4, 11, 14], [0, 3, 6, 10, 13],
   [0, 4, 6, 9, 12], [1, 2, 5, 11, 14], [1, 2, 7, 10, 13], [1, 5, 7, 9, 12],
   [2, 3, 8, 10, 14], [4, 5, 8, 12, 14], [6, 7, 8, 10, 12]]

private def countAdj (adj : ℕ → ℕ → Bool) (v : ℕ) : List ℕ → ℕ
  | [] => 0
  | w :: ws => (if adj v w then 1 else 0) + countAdj adj v ws

private def edgeCount (adj : ℕ → ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | v :: vs => countAdj adj v vs + edgeCount adj vs

private def checkB0 : ℕ → ℕ → List ℕ → ℕ → Bool
  | _, 0, sel, edges =>
    decide (edges < 21) ||
      (decide (edges ≤ 22) && k6List0.any (fun K => K.all (fun v => sel.contains v)))
  | 0, _ + 1, _, _ => true
  | n + 1, k + 1, sel, edges =>
    checkB0 n (k + 1) sel edges && checkB0 n k (n :: sel) (edges + countAdj adj0 n sel)

private def checkB1 : ℕ → ℕ → List ℕ → Bool
  | _, 0, sel => k5List1.contains sel
  | 0, _ + 1, _ => true
  | n + 1, k + 1, sel =>
    checkB1 n (k + 1) sel &&
      (if sel.all (fun v => adj1 n v) then checkB1 n k (n :: sel) else true)

/- ### Fast kernel-checked finite facts -/

private lemma check_adj0 :
    ∀ i j : Fin 15,
      (i ≠ j ∧ !(mask0.testBit ((min i j).val * 15 + (max i j).val))) ↔
        adj0 i.val j.val = true := by
  decide

private lemma check_adj1 :
    ∀ i j : Fin 15,
      (i ≠ j ∧ !(mask1.testBit ((min i j).val * 15 + (max i j).val))) ↔
        adj1 i.val j.val = true := by
  decide

private lemma adj0_of_ge_left {i j : ℕ} (hi : 15 ≤ i) : adj0 i j = false := by
  unfold adj0
  split <;> first | omega | rfl

private lemma adj0_of_ge_right {i j : ℕ} (hj : 15 ≤ j) : adj0 i j = false := by
  unfold adj0
  split <;> first | rfl | (split <;> first | omega | rfl)

private lemma adj0_symm : ∀ i j : ℕ, adj0 i j = adj0 j i := by
  intro i j
  by_cases hi : i < 15
  · by_cases hj : j < 15
    · have h : ∀ a b : Fin 15, adj0 a.val b.val = adj0 b.val a.val := by decide
      exact h ⟨i, hi⟩ ⟨j, hj⟩
    · rw [adj0_of_ge_right (by omega), adj0_of_ge_left (by omega)]
  · rw [adj0_of_ge_left (by omega), adj0_of_ge_right (by omega)]

private lemma adj0_irrefl : ∀ i : ℕ, adj0 i i = false := by
  intro i
  by_cases hi : i < 15
  · have h : ∀ a : Fin 15, adj0 a.val a.val = false := by decide
    exact h ⟨i, hi⟩
  · exact adj0_of_ge_left (by omega)

private lemma check_k6List0 :
    k6List0.all (fun K =>
      K.length == 6 && K.Nodup && K.all (fun v => decide (v < 15)) &&
        K.all (fun u => K.all (fun w => u == w || adj0 u w))) = true := by
  decide

private lemma check_k5Pairs1 :
    k5List1.all (fun t₁ =>
      k5List1.all (fun t₂ =>
        (t₁ == t₂) || decide (t₁.countP (fun x => t₂.contains x) ≤ 2))) = true := by
  decide

private lemma check_k5Nodup :
    k5List1.all (fun t => decide t.Nodup) = true := by
  decide

set_option maxHeartbeats 2000000 in
private lemma check_B0_dense8 : checkB0 15 8 [] 0 = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
private lemma check_B1_k5 : checkB1 15 5 [] = true := by
  decide +kernel

/- ### Soundness lemmas for list enumeration -/

private lemma countAdj_eq_card_filter (adj : ℕ → ℕ → Bool) (v : ℕ) (L : List ℕ)
    (hnd : L.Nodup) :
    countAdj adj v L = (L.toFinset.filter (fun w => adj v w = true)).card := by
  induction L with
  | nil => simp [countAdj]
  | cons w ws ih =>
    obtain ⟨hw, hws⟩ := List.nodup_cons.mp hnd
    rw [countAdj, ih hws, List.toFinset_cons, Finset.filter_insert]
    have hwnot : w ∉ ws.toFinset := by simpa using hw
    by_cases hadj : adj v w = true
    · rw [if_pos hadj, if_pos hadj, Finset.card_insert_of_notMem]
      · omega
      · intro hmem
        exact hwnot (Finset.mem_filter.mp hmem).1
    · rw [if_neg hadj, if_neg hadj, zero_add]

private lemma two_mul_edgeCount_eq_degSum (L : List ℕ) (hnd : L.Nodup) :
    2 * edgeCount adj0 L = ∑ v ∈ L.toFinset, (L.toFinset.filter (fun w => adj0 v w = true)).card := by
  induction L with
  | nil => simp [edgeCount]
  | cons v vs ih =>
    obtain ⟨hv, hvs⟩ := List.nodup_cons.mp hnd
    have hvnot : v ∉ vs.toFinset := by simpa using hv
    rw [edgeCount, Nat.mul_add, ih hvs, List.toFinset_cons, Finset.sum_insert hvnot]
    have hv_term :
        ((insert v vs.toFinset).filter (fun w => adj0 v w = true)).card = countAdj adj0 v vs := by
      rw [Finset.filter_insert, if_neg (by simp [adj0_irrefl]),
        countAdj_eq_card_filter adj0 v vs hvs]
    have hrest :
        ∑ x ∈ vs.toFinset, ((insert v vs.toFinset).filter (fun w => adj0 x w = true)).card =
          countAdj adj0 v vs +
            ∑ x ∈ vs.toFinset, (vs.toFinset.filter (fun w => adj0 x w = true)).card := by
      have hterm : ∀ x ∈ vs.toFinset,
          ((insert v vs.toFinset).filter (fun w => adj0 x w = true)).card =
            (if adj0 x v = true then 1 else 0) +
              (vs.toFinset.filter (fun w => adj0 x w = true)).card := by
        intro x _
        rw [Finset.filter_insert]
        by_cases hxv : adj0 x v = true
        · rw [if_pos hxv, if_pos hxv, Finset.card_insert_of_notMem]
          · omega
          · intro hmem
            exact hvnot (Finset.mem_filter.mp hmem).1
        · rw [if_neg hxv, if_neg hxv, zero_add]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      congr 1
      rw [countAdj_eq_card_filter adj0 v vs hvs, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro x _
      rw [adj0_symm x v]
    rw [hv_term, hrest]
    omega

private lemma checkB0_spec (n : ℕ) : ∀ (k : ℕ) (sel : List ℕ),
    checkB0 n k sel (edgeCount adj0 sel) = true →
    sel.Nodup →
    (∀ w ∈ sel, n ≤ w) →
    ∀ S : Finset (Fin 15), (∀ v ∈ S, v.val < n) → S.card = k →
      ∃ L : List ℕ, L.Nodup ∧ (∀ x, x ∈ L ↔ x ∈ sel ∨ ∃ v ∈ S, v.val = x) ∧
        (edgeCount adj0 L < 21 ∨
          (edgeCount adj0 L ≤ 22 ∧ ∃ K ∈ k6List0, ∀ v ∈ K, v ∈ L)) := by
  induction n with
  | zero =>
    intro k sel h hnd _ S hS hcard
    cases k with
    | zero =>
      have hSe : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hSe
      simp only [checkB0, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
        List.all_eq_true, List.elem_iff] at h
      refine ⟨sel, hnd, by simp, ?_⟩
      rcases h with hlt | ⟨hle, K, hK, hsub⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨hle, K, hK, hsub⟩
    | succ k =>
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      have := hS v hv
      omega
  | succ n ih =>
    intro k sel h hnd hge S hS hcard
    cases k with
    | zero =>
      have hSe : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hSe
      simp only [checkB0, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
        List.all_eq_true, List.elem_iff] at h
      refine ⟨sel, hnd, by simp, ?_⟩
      rcases h with hlt | ⟨hle, K, hK, hsub⟩
      · exact Or.inl hlt
      · exact Or.inr ⟨hle, K, hK, hsub⟩
    | succ k =>
      dsimp [checkB0] at h
      rw [Bool.and_eq_true] at h
      by_cases hn15 : n < 15
      · let v₀ : Fin 15 := ⟨n, hn15⟩
        by_cases hv₀ : v₀ ∈ S
        · let S' := S.erase v₀
          have hS' : ∀ v ∈ S', v.val < n := by
            intro v hv
            obtain ⟨hne, hvS⟩ := Finset.mem_erase.mp hv
            have hvlt := hS v hvS
            have hne' : v.val ≠ n := fun heq => hne (Fin.ext heq)
            omega
          have hS'card : S'.card = k := by
            rw [Finset.card_erase_of_mem hv₀, hcard]
            omega
          have hn_not_sel : n ∉ sel := fun hmem => by have := hge n hmem; omega
          have hnd' : (n :: sel).Nodup := List.nodup_cons.mpr ⟨hn_not_sel, hnd⟩
          have hge' : ∀ w ∈ n :: sel, n ≤ w := by
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hws
            · exact le_rfl
            · have := hge w hws; omega
          have hedge : edgeCount adj0 sel + countAdj adj0 n sel = edgeCount adj0 (n :: sel) := by
            rw [edgeCount, add_comm]
          have h2 := h.2
          rw [hedge] at h2
          obtain ⟨L, hLnd, hLmem, hLprop⟩ := ih k (n :: sel) h2 hnd' hge' S' hS' hS'card
          refine ⟨L, hLnd, fun x => ?_, hLprop⟩
          rw [hLmem]
          constructor
          · rintro (hcons | ⟨v, hv, rfl⟩)
            · rcases List.mem_cons.mp hcons with rfl | hxsel
              · exact Or.inr ⟨v₀, hv₀, rfl⟩
              · exact Or.inl hxsel
            · exact Or.inr ⟨v, Finset.mem_of_mem_erase hv, rfl⟩
          · rintro (hxsel | ⟨v, hv, rfl⟩)
            · exact Or.inl (List.mem_cons_of_mem n hxsel)
            · by_cases hveq : v = v₀
              · subst hveq
                exact Or.inl List.mem_cons_self
              · exact Or.inr ⟨v, Finset.mem_erase.mpr ⟨hveq, hv⟩, rfl⟩
        · have hS' : ∀ v ∈ S, v.val < n := by
            intro v hv
            have hvlt := hS v hv
            have hne' : v.val ≠ n := fun heq => hv₀ (by convert hv using 1; exact Fin.ext heq.symm)
            omega
          have hge' : ∀ w ∈ sel, n ≤ w := fun w hw => by have := hge w hw; omega
          exact ih (k + 1) sel h.1 hnd hge' S hS' hcard
      · have hS' : ∀ v ∈ S, v.val < n := fun v _ => lt_of_lt_of_le v.isLt (by omega)
        have hge' : ∀ w ∈ sel, n ≤ w := fun w hw => by have := hge w hw; omega
        exact ih (k + 1) sel h.1 hnd hge' S hS' hcard

private lemma checkB1_spec (n : ℕ) : ∀ (k : ℕ) (sel : List ℕ),
    checkB1 n k sel = true →
    ∀ S : Finset (Fin 15), (∀ v ∈ S, v.val < n) → S.card = k →
      (∀ u ∈ S, ∀ v ∈ S, u ≠ v → adj1 u.val v.val = true) →
      (∀ u ∈ S, ∀ w ∈ sel, adj1 u.val w = true) →
      ∃ L ∈ k5List1, ∀ x, x ∈ L ↔ x ∈ sel ∨ ∃ v ∈ S, v.val = x := by
  induction n with
  | zero =>
    intro k sel h S hS hcard _ _
    cases k with
    | zero =>
      have hSe : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hSe
      exact ⟨sel, List.elem_iff.mp h, by simp⟩
    | succ k =>
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      have := hS v hv
      omega
  | succ n ih =>
    intro k sel h S hS hcard hclq hcross
    cases k with
    | zero =>
      have hSe : S = ∅ := Finset.card_eq_zero.mp hcard
      subst hSe
      exact ⟨sel, List.elem_iff.mp h, by simp⟩
    | succ k =>
      dsimp [checkB1] at h
      rw [Bool.and_eq_true] at h
      by_cases hn15 : n < 15
      · let v₀ : Fin 15 := ⟨n, hn15⟩
        by_cases hv₀ : v₀ ∈ S
        · let S' := S.erase v₀
          have hS' : ∀ v ∈ S', v.val < n := by
            intro v hv
            obtain ⟨hne, hvS⟩ := Finset.mem_erase.mp hv
            have hvlt := hS v hvS
            have hne' : v.val ≠ n := fun heq => hne (Fin.ext heq)
            omega
          have hS'card : S'.card = k := by
            rw [Finset.card_erase_of_mem hv₀, hcard]
            omega
          have hall_n : sel.all (fun v => adj1 n v) = true :=
            List.all_eq_true.mpr fun w hw => hcross v₀ hv₀ w hw
          have h2 : checkB1 n k (n :: sel) = true := by
            simpa [hall_n] using h.2
          have hclq' : ∀ u ∈ S', ∀ v ∈ S', u ≠ v → adj1 u.val v.val = true := fun u hu v hv =>
            hclq u (Finset.mem_of_mem_erase hu) v (Finset.mem_of_mem_erase hv)
          have hcross' : ∀ u ∈ S', ∀ w ∈ n :: sel, adj1 u.val w = true := by
            intro u hu w hw
            rcases List.mem_cons.mp hw with rfl | hws
            · exact hclq u (Finset.mem_of_mem_erase hu) v₀ hv₀ (Finset.mem_erase.mp hu).1
            · exact hcross u (Finset.mem_of_mem_erase hu) w hws
          obtain ⟨L, hLmem, hLiff⟩ := ih k (n :: sel) h2 S' hS' hS'card hclq' hcross'
          refine ⟨L, hLmem, fun x => ?_⟩
          rw [hLiff]
          constructor
          · rintro (hcons | ⟨v, hv, rfl⟩)
            · rcases List.mem_cons.mp hcons with rfl | hxsel
              · exact Or.inr ⟨v₀, hv₀, rfl⟩
              · exact Or.inl hxsel
            · exact Or.inr ⟨v, Finset.mem_of_mem_erase hv, rfl⟩
          · rintro (hxsel | ⟨v, hv, rfl⟩)
            · exact Or.inl (List.mem_cons_of_mem n hxsel)
            · by_cases hveq : v = v₀
              · subst hveq
                exact Or.inl List.mem_cons_self
              · exact Or.inr ⟨v, Finset.mem_erase.mpr ⟨hveq, hv⟩, rfl⟩
        · have hS' : ∀ v ∈ S, v.val < n := by
            intro v hv
            have hvlt := hS v hv
            have hne' : v.val ≠ n := fun heq => hv₀ (by convert hv using 1; exact Fin.ext heq.symm)
            omega
          exact ih (k + 1) sel h.1 S hS' hcard hclq hcross
      · have hS' : ∀ v ∈ S, v.val < n := fun v _ => lt_of_lt_of_le v.isLt (by omega)
        exact ih (k + 1) sel h.1 S hS' hcard hclq hcross

/- ### Main theorem -/

theorem main_H1 : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1.H1 := by
  classical
  dsimp only [OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1.H1]
  intro f _
  let masks := (![mask0, mask1] : Fin 2 → ℕ)
  let C (a : Fin 2) : SimpleGraph (Fin 15) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val * 15 + (max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm, by simpa [min_comm j i, max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  let B0 : SimpleGraph (Fin 15) := (C 0)ᶜ
  let B1 : SimpleGraph (Fin 15) := (C 1)ᶜ
  let G0 : SimpleGraph (Fin 8) := B0.comap (f 0)
  let G1 : SimpleGraph (Fin 8) := B1.comap (f 1)
  let D : SimpleGraph (Fin 8) := ⨅ a, (C a)ᶜ.comap (f a)
  change D.edgeSet.ncard ≤ 20
  have hB0_adj : ∀ i j : Fin 15, B0.Adj i j ↔ adj0 i.val j.val = true := by
    intro i j
    rw [← check_adj0 i j]
    simp only [B0, C, masks, SimpleGraph.compl_adj, Matrix.cons_val_zero, Bool.not_eq_true']
    constructor
    · intro ⟨hne, hnot⟩
      refine ⟨hne, ?_⟩
      cases h : mask0.testBit ((min i j).val * 15 + (max i j).val)
      · rfl
      · exact absurd ⟨hne, h⟩ hnot
    · intro ⟨hne, hfalse⟩
      refine ⟨hne, fun h => ?_⟩
      rw [h.2] at hfalse
      exact Bool.noConfusion hfalse
  have hB1_adj : ∀ i j : Fin 15, B1.Adj i j ↔ adj1 i.val j.val = true := by
    intro i j
    rw [← check_adj1 i j]
    simp only [B1, C, masks, SimpleGraph.compl_adj, Matrix.cons_val_one, Matrix.cons_val_zero,
      Bool.not_eq_true']
    constructor
    · intro ⟨hne, hnot⟩
      refine ⟨hne, ?_⟩
      cases h : mask1.testBit ((min i j).val * 15 + (max i j).val)
      · rfl
      · exact absurd ⟨hne, h⟩ hnot
    · intro ⟨hne, hfalse⟩
      refine ⟨hne, fun h => ?_⟩
      rw [h.2] at hfalse
      exact Bool.noConfusion hfalse
  by_contra hgt
  have hD_ge : 21 ≤ D.edgeFinset.card := by
    have heq : D.edgeSet.ncard = D.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card D.edgeSet]
      congr 1
      ext e
      simp [SimpleGraph.edgeFinset]
    omega
  have hD_le_G0 : D ≤ G0 := iInf_le (fun a => (C a)ᶜ.comap (f a)) 0
  have hD_le_G1 : D ≤ G1 := iInf_le (fun a => (C a)ᶜ.comap (f a)) 1
  have hDe_sub_G0 : D.edgeFinset ⊆ G0.edgeFinset := SimpleGraph.edgeFinset_mono hD_le_G0
  have hG0_ge : 21 ≤ G0.edgeFinset.card := le_trans hD_ge (Finset.card_le_card hDe_sub_G0)
  -- Apply checkB0_spec to S0 := univ.map (f 0)
  let S0 : Finset (Fin 15) := Finset.univ.map (f 0)
  have hS0_card : S0.card = 8 := by simp [S0]
  obtain ⟨L0, hL0_nd, hL0_mem, hL0_prop⟩ :=
    checkB0_spec 15 8 [] check_B0_dense8 List.nodup_nil (by simp) S0 (fun v _ => v.isLt) hS0_card
  have hL0_toFinset : L0.toFinset = S0.image Fin.val := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_image, hL0_mem, List.not_mem_nil, false_or]
  have hedge_G0 : edgeCount adj0 L0 = G0.edgeFinset.card := by
    have h2 : 2 * edgeCount adj0 L0 = 2 * G0.edgeFinset.card := by
      rw [two_mul_edgeCount_eq_degSum L0 hL0_nd, hL0_toFinset, ← G0.sum_degrees_eq_twice_card_edges]
      have hsum_img :
          ∑ x ∈ S0.image Fin.val, ((S0.image Fin.val).filter (fun w => adj0 x w = true)).card =
            ∑ v ∈ S0, (S0.filter (B0.Adj v)).card := by
        rw [Finset.sum_image (fun a _ b _ h => Fin.ext h)]
        apply Finset.sum_congr rfl
        intro v _
        refine Finset.card_bij (fun w hw => ⟨w, ?_⟩) ?_ ?_ ?_
        · obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hw).1
          exact u.isLt
        · intro w hw
          obtain ⟨hwimg, hadj⟩ := Finset.mem_filter.mp hw
          obtain ⟨u, huS0, rfl⟩ := Finset.mem_image.mp hwimg
          exact Finset.mem_filter.mpr ⟨huS0, (hB0_adj v u).mpr hadj⟩
        · intro w₁ _ w₂ _ h
          exact congrArg Fin.val h
        · intro u hu
          obtain ⟨huS0, hadj⟩ := Finset.mem_filter.mp hu
          exact ⟨u.val, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ huS0, (hB0_adj v u).mp hadj⟩, rfl⟩
      rw [hsum_img]
      dsimp [S0]
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro u _
      rw [← G0.card_neighborFinset_eq_degree]
      symm
      refine Finset.card_bij (fun w _ => f 0 w) ?_ ?_ ?_
      · intro w hw
        have hadj : G0.Adj u w := (G0.mem_neighborFinset u w).mp hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩, hadj⟩
      · intro w₁ _ w₂ _ h
        exact (f 0).injective h
      · intro y hy
        obtain ⟨hyS0, hadj⟩ := Finset.mem_filter.mp hy
        obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp hyS0
        exact ⟨w, (G0.mem_neighborFinset u w).mpr hadj, rfl⟩
    omega
  rcases hL0_prop with hlt21 | ⟨hle22, KL, hKL_mem, hKL_sub⟩
  · omega
  have hG0_le : G0.edgeFinset.card ≤ 22 := by omega
  -- Extract 6-clique K in G0 from KL ∈ k6List0
  have hKL_ok := List.all_eq_true.mp check_k6List0 KL hKL_mem
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hKL_ok
  obtain ⟨⟨⟨hKL_len, hKL_nd⟩, hKL_lt⟩, hKL_clq⟩ := hKL_ok
  let K0 : Finset (Fin 15) := Finset.univ.filter (fun v => v.val ∈ KL)
  have hK0_card : K0.card = 6 := by
    have hbij : K0.card = KL.toFinset.card := by
      refine Finset.card_bij (fun v _ => v.val) ?_ ?_ ?_
      · intro v hv
        exact List.mem_toFinset.mpr (Finset.mem_filter.mp hv).2
      · intro v₁ _ v₂ _ h
        exact Fin.ext h
      · intro x hx
        have hxKL : x ∈ KL := List.mem_toFinset.mp hx
        exact ⟨⟨x, hKL_lt x hxKL⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxKL⟩, rfl⟩
    rw [hbij, List.toFinset_card_of_nodup hKL_nd, hKL_len]
  have hK0_sub_S0 : K0 ⊆ S0 := by
    intro v hv
    have hvKL : v.val ∈ KL := (Finset.mem_filter.mp hv).2
    have hvL0 : v.val ∈ L0 := hKL_sub v.val hvKL
    have hmem := (hL0_mem v.val).mp hvL0
    simp only [List.not_mem_nil, false_or] at hmem
    obtain ⟨w, hwS0, hwv⟩ := hmem
    exact (Fin.ext hwv) ▸ hwS0
  have hK0_clq : ∀ x ∈ K0, ∀ y ∈ K0, x ≠ y → B0.Adj x y := by
    intro x hx y hy hxy
    have hxKL : x.val ∈ KL := (Finset.mem_filter.mp hx).2
    have hyKL : y.val ∈ KL := (Finset.mem_filter.mp hy).2
    have hne : x.val ≠ y.val := fun h => hxy (Fin.ext h)
    exact (hB0_adj x y).mpr ((hKL_clq x.val hxKL y.val hyKL).resolve_left hne)
  let K : Finset (Fin 8) := Finset.univ.filter (fun u => f 0 u ∈ K0)
  have hK_map : K.map (f 0) = K0 := by
    ext v
    simp only [K, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hv
      obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp (hK0_sub_S0 hv)
      exact ⟨u, hv, rfl⟩
  have hK_card : K.card = 6 := by
    have := Finset.card_map (s := K) (f 0)
    rw [hK_map, hK0_card] at this
    exact this.symm
  have hK_clq : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → G0.Adj x y := fun x hx y hy hxy =>
    hK0_clq (f 0 x) (Finset.mem_filter.mp hx).2 (f 0 y) (Finset.mem_filter.mp hy).2
      ((f 0).injective.ne hxy)
  -- Find distinct u, v ∈ K such that K.erase u and K.erase v are both cliques in D
  have hdiff_le : (G0.edgeFinset \ D.edgeFinset).card ≤ 1 := by
    have := Finset.card_sdiff_add_card_eq_card hDe_sub_G0
    omega
  have hexists_uv : ∃ u ∈ K, ∃ v ∈ K, u ≠ v ∧
      (∀ x ∈ K.erase u, ∀ y ∈ K.erase u, x ≠ y → D.Adj x y) ∧
      (∀ x ∈ K.erase v, ∀ y ∈ K.erase v, x ≠ y → D.Adj x y) := by
    have hK_two : ∃ u ∈ K, ∃ v ∈ K, u ≠ v := by
      obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < K.card)
      obtain ⟨v, hv⟩ := Finset.card_pos.mp
        (by rw [Finset.card_erase_of_mem hu]; omega : 0 < (K.erase u).card)
      exact ⟨u, hu, v, (Finset.mem_erase.mp hv).2, (Finset.mem_erase.mp hv).1.symm⟩
    by_cases h0 : (G0.edgeFinset \ D.edgeFinset).card = 0
    · have hempty : G0.edgeFinset \ D.edgeFinset = ∅ := Finset.card_eq_zero.mp h0
      have hall : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → D.Adj x y := by
        intro x hx y hy hxy
        have hG0e : s(x, y) ∈ G0.edgeFinset := SimpleGraph.mem_edgeFinset.mpr (hK_clq x hx y hy hxy)
        by_contra hnotD
        have hmem : s(x, y) ∈ G0.edgeFinset \ D.edgeFinset :=
          Finset.mem_sdiff.mpr ⟨hG0e, fun hD => hnotD (SimpleGraph.mem_edgeFinset.mp hD)⟩
        rw [hempty] at hmem
        exact Finset.notMem_empty _ hmem
      obtain ⟨u, hu, v, hv, huv⟩ := hK_two
      exact ⟨u, hu, v, hv, huv,
        fun x hx y hy hxy => hall x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy,
        fun x hx y hy hxy => hall x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy⟩
    · have h1 : (G0.edgeFinset \ D.edgeFinset).card = 1 := by omega
      obtain ⟨e₀, he₀⟩ := Finset.card_eq_one.mp h1
      induction e₀ using Sym2.ind with
      | _ p q =>
        have hpq_mem : s(p, q) ∈ G0.edgeFinset := by
          have : s(p, q) ∈ G0.edgeFinset \ D.edgeFinset := by
            rw [he₀]; exact Finset.mem_singleton_self _
          exact (Finset.mem_sdiff.mp this).1
        have hpq_ne : p ≠ q := G0.ne_of_adj (SimpleGraph.mem_edgeFinset.mp hpq_mem)
        have hD_of_ne : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → s(x, y) ≠ s(p, q) → D.Adj x y := by
          intro x hx y hy hxy hne
          have hG0e : s(x, y) ∈ G0.edgeFinset := SimpleGraph.mem_edgeFinset.mpr (hK_clq x hx y hy hxy)
          by_contra hnotD
          have hmem : s(x, y) ∈ G0.edgeFinset \ D.edgeFinset :=
            Finset.mem_sdiff.mpr ⟨hG0e, fun hD => hnotD (SimpleGraph.mem_edgeFinset.mp hD)⟩
          rw [he₀, Finset.mem_singleton] at hmem
          exact hne hmem
        by_cases hboth : p ∈ K ∧ q ∈ K
        · refine ⟨p, hboth.1, q, hboth.2, hpq_ne, ?_, ?_⟩
          · intro x hx y hy hxy
            refine hD_of_ne x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy ?_
            intro heq
            have hp_in : p ∈ s(x, y) := heq ▸ Sym2.mem_mk_left p q
            rcases Sym2.mem_iff.mp hp_in with rfl | rfl
            · exact (Finset.mem_erase.mp hx).1 rfl
            · exact (Finset.mem_erase.mp hy).1 rfl
          · intro x hx y hy hxy
            refine hD_of_ne x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy ?_
            intro heq
            have hq_in : q ∈ s(x, y) := heq ▸ Sym2.mem_mk_right p q
            rcases Sym2.mem_iff.mp hq_in with rfl | rfl
            · exact (Finset.mem_erase.mp hx).1 rfl
            · exact (Finset.mem_erase.mp hy).1 rfl
        · obtain ⟨u, hu, v, hv, huv⟩ := hK_two
          have hall : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → D.Adj x y := by
            intro x hx y hy hxy
            refine hD_of_ne x hx y hy hxy ?_
            intro heq
            have hp_in : p ∈ s(x, y) := heq ▸ Sym2.mem_mk_left p q
            have hq_in : q ∈ s(x, y) := heq ▸ Sym2.mem_mk_right p q
            have hpK : p ∈ K := by rcases Sym2.mem_iff.mp hp_in with rfl | rfl <;> assumption
            have hqK : q ∈ K := by rcases Sym2.mem_iff.mp hq_in with rfl | rfl <;> assumption
            exact hboth ⟨hpK, hqK⟩
          exact ⟨u, hu, v, hv, huv,
            fun x hx y hy hxy => hall x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy,
            fun x hx y hy hxy => hall x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy⟩
  obtain ⟨u, huK, v, hvK, huv, hclq_u, hclq_v⟩ := hexists_uv
  -- Map the two 5-cliques into B1 via f 1
  let T1 : Finset (Fin 15) := (K.erase u).map (f 1)
  let T2 : Finset (Fin 15) := (K.erase v).map (f 1)
  have hT1_card : T1.card = 5 := by
    rw [Finset.card_map, Finset.card_erase_of_mem huK, hK_card]
  have hT2_card : T2.card = 5 := by
    rw [Finset.card_map, Finset.card_erase_of_mem hvK, hK_card]
  have hT1_clq : ∀ x ∈ T1, ∀ y ∈ T1, x ≠ y → adj1 x.val y.val = true := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact (hB1_adj _ _).mp (hD_le_G1 (hclq_u a ha b hb fun h => hxy (congrArg (f 1) h)))
  have hT2_clq : ∀ x ∈ T2, ∀ y ∈ T2, x ≠ y → adj1 x.val y.val = true := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
    exact (hB1_adj _ _).mp (hD_le_G1 (hclq_v a ha b hb fun h => hxy (congrArg (f 1) h)))
  obtain ⟨L1, hL1_mem, hL1_iff⟩ :=
    checkB1_spec 15 5 [] check_B1_k5 T1 (fun w _ => w.isLt) hT1_card hT1_clq (by simp)
  obtain ⟨L2, hL2_mem, hL2_iff⟩ :=
    checkB1_spec 15 5 [] check_B1_k5 T2 (fun w _ => w.isLt) hT2_card hT2_clq (by simp)
  have hL1_ne_L2 : L1 ≠ L2 := by
    intro heq
    have hv_in : (f 1 v).val ∈ L1 :=
      (hL1_iff _).mpr (Or.inr ⟨f 1 v, Finset.mem_map.mpr ⟨v, Finset.mem_erase.mpr ⟨huv.symm, hvK⟩, rfl⟩, rfl⟩)
    rw [heq] at hv_in
    rcases (hL2_iff _).mp hv_in with hnil | ⟨w, hwT2, hwval⟩
    · simp at hnil
    · have hw_eq : w = f 1 v := Fin.ext hwval
      subst hw_eq
      obtain ⟨z, hz, hzv⟩ := Finset.mem_map.mp hwT2
      have hzv' : z = v := (f 1).injective hzv
      exact (Finset.mem_erase.mp hz).1 hzv'
  have hpair := List.all_eq_true.mp (List.all_eq_true.mp check_k5Pairs1 L1 hL1_mem) L2 hL2_mem
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hpair
  have hcount_le : L1.countP (fun x => L2.contains x) ≤ 2 := hpair.resolve_left hL1_ne_L2
  have hL1_nd : L1.Nodup := of_decide_eq_true (List.all_eq_true.mp check_k5Nodup L1 hL1_mem)
  -- Meanwhile ((K.erase u).erase v).map (f 1) has size 4 and embeds into L1 ∩ L2
  let I4 : Finset (Fin 15) := ((K.erase u).erase v).map (f 1)
  have hI4_card : I4.card = 4 := by
    have hv_in_Ku : v ∈ K.erase u := Finset.mem_erase.mpr ⟨huv.symm, hvK⟩
    rw [Finset.card_map, Finset.card_erase_of_mem hv_in_Ku, Finset.card_erase_of_mem huK, hK_card]
  have hI4_le : I4.card ≤ L1.countP (fun x => L2.contains x) := by
    have hcount_eq : L1.countP (fun x => L2.contains x) =
        (L1.filter (fun x => L2.contains x)).toFinset.card := by
      rw [List.countP_eq_length_filter, List.toFinset_card_of_nodup (hL1_nd.filter _)]
    rw [hcount_eq]
    refine Finset.card_le_card_of_injOn Fin.val ?_ (fun a _ b _ h => Fin.ext h)
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hw
    have hz_u : z ∈ K.erase u := Finset.mem_of_mem_erase hz
    have hz_v : z ∈ K.erase v :=
      Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1, Finset.mem_of_mem_erase hz_u⟩
    have h1 : (f 1 z).val ∈ L1 :=
      (hL1_iff _).mpr (Or.inr ⟨f 1 z, Finset.mem_map.mpr ⟨z, hz_u, rfl⟩, rfl⟩)
    have h2 : (f 1 z).val ∈ L2 :=
      (hL2_iff _).mpr (Or.inr ⟨f 1 z, Finset.mem_map.mpr ⟨z, hz_v, rfl⟩, rfl⟩)
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨h1, List.elem_iff.mpr h2⟩)
  omega

end Erdos1182H1

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_small_values_R1_H2_R1_H2_R1.H1 := by
  exact Erdos1182H1.main_H1
