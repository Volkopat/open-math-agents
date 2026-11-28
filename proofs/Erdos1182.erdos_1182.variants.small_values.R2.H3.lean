import OMAReductions.R_Erdos1182_erdos_1182_variants_small_values_R2

/-!
R2.H3 combines the order-eight and order-nine common edge bounds.
Both certificates and their mathematical arguments are by @dasante78, merged in
lefttosolve2/open-math-agents PRs #12188 and #12433. They are reproduced here
because the checker accepts one proof file with only the assigned project import.
-/

namespace SmallValuesR2

open SimpleGraph Finset

def Bound1 : Prop :=
  let masks := (![822777387642256703234551838076830900798754331299012273175546532,822764833055638660808762661315316885505752648441781026290401700] : Fin 2 → ℕ)
  let C (a : Fin 2) : SimpleGraph (Fin 15) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*15+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  ∀ f : Fin 2 → Fin 8 ↪ Fin 15,
    let D := ⨅ a, (C a)ᶜ.comap (f a)
    D.Connected → D.edgeSet.ncard ≤ 20

def Bound2 : Prop :=
  let masks := (![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,3794304128205901233965105136443933563551981921148588106415553686027566907782081184,165643176072884037276740330230205787895060569518802011647374886495636132] : Fin 3 → ℕ)
  let C (a : Fin 3) : SimpleGraph (Fin 17) :=
    { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val*17+(max i j).val) = true
      symm := ⟨fun i j v => ⟨v.1.symm,by simpa [min_comm j i,max_comm j i] using v.2⟩⟩
      loopless := ⟨by simp⟩ }
  ∀ f : Fin 3 → Fin 9 ↪ Fin 17,
    let D := ⨅ a, (C a)ᶜ.comap (f a)
    D.Connected → D.edgeSet.ncard ≤ 27

end SmallValuesR2

/-! # Common edge bound for the two 15-vertex hosts (Erdos 1182, order 8)

We prove `SmallValuesR2.Bound1`:
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

theorem main_H1 : SmallValuesR2.Bound1 := by
  classical
  dsimp only [SmallValuesR2.Bound1]
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


/-!
Proof of `SmallValuesR2.Bound2`
(common edge bound `≤ 27` for the three 17-vertex hosts on `Fin 9`).

Let `C 0, C 1, C 2` be the three 17-vertex hosts and `D = ⨅ a, (C a)ᶜ.comap (f a)`.
Suppose `28 ≤ D.edgeSet.ncard`. Using fast pure-`Nat.ble`/`Nat.beq` kernel certificates
counting non-edges (`e(C_a[S]) ≤ 8` corresponding to `e(C_aᶜ[S]) ≥ 28`), we verify:
1. `(C 1)ᶜ` is `K₆`-free, so `D` is `K₆`-free.
2. Every 9-vertex induced subgraph `G₀` of `(C 0)ᶜ` with `e(G₀) ≥ 28` has `e(G₀) ≤ 30` and
   contains a `K₆`, and every `K₆`-free subgraph `H ≤ G₀` with `e(H) ≥ 28` has minimum degree
   at least `5` and fails `2 ≤ c₅(H) ∧ 4 * c₅(H) + e₇ᵈⁱʳ(H) = 16`.
3. Every 9-vertex induced subgraph `G₂` of `(C 2)ᶜ` with `e(G₂) ≥ 28` and minimum degree at
   least `5` has `e(G₂) ≤ 30` and contains a `K₆`, and every `K₆`-free subgraph `H ≤ G₂` with
   `e(H) ≥ 28` and minimum degree at least `5` satisfies `2 ≤ c₅(H) ∧ 4 * c₅(H) + e₇ᵈⁱʳ(H) = 16`.

Transferring these graph-isomorphism invariants along `H₀ ≃g D ≃g H₂` yields a contradiction.
-/

open SimpleGraph Finset

namespace Erdos1182H2

private def masks : Fin 3 → ℕ :=
  ![3794289654249960540213394811365649999491732653694874493236865398263569676450744992,
    3794304128205901233965105136443933563551981921148588106415553686027566907782081184,
    165643176072884037276740330230205787895060569518802011647374886495636132]

private def hostC (a : Fin 3) : SimpleGraph (Fin 17) :=
  { Adj := fun i j => i ≠ j ∧ (masks a).testBit ((min i j).val * 17 + (max i j).val) = true
    symm := ⟨fun i j v => ⟨v.1.symm, by simpa [min_comm j i, max_comm j i] using v.2⟩⟩
    loopless := ⟨by simp⟩ }

private instance (a : Fin 3) : DecidableRel (hostC a).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

private def c0Adj (i j : ℕ) : Bool :=
  if i.ble 8 then
    if i.ble 4 then
      if i.ble 2 then
        if i.ble 1 then
          if i.ble 0 then (j.beq 5 || j.beq 7 || j.beq 9 || j.beq 11 || j.beq 14 || j.beq 16)
          else (j.beq 6 || j.beq 8 || j.beq 9 || j.beq 11 || j.beq 14 || j.beq 16)
        else (j.beq 3 || j.beq 6 || j.beq 8 || j.beq 12 || j.beq 14 || j.beq 16)
      else
        if i.ble 3 then (j.beq 2 || j.beq 5 || j.beq 7 || j.beq 9 || j.beq 11 || j.beq 15)
        else (j.beq 5 || j.beq 7 || j.beq 10 || j.beq 13 || j.beq 14 || j.beq 16)
    else
      if i.ble 6 then
        if i.ble 5 then (j.beq 0 || j.beq 3 || j.beq 4 || j.beq 6 || j.beq 8 || j.beq 12)
        else (j.beq 1 || j.beq 2 || j.beq 5 || j.beq 7 || j.beq 10 || j.beq 13)
      else
        if i.ble 7 then (j.beq 0 || j.beq 3 || j.beq 4 || j.beq 6 || j.beq 8 || j.beq 12)
        else (j.beq 1 || j.beq 2 || j.beq 5 || j.beq 7 || j.beq 10 || j.beq 13)
  else
    if i.ble 12 then
      if i.ble 10 then
        if i.ble 9 then (j.beq 0 || j.beq 1 || j.beq 3 || j.beq 10 || j.beq 12 || j.beq 13)
        else (j.beq 4 || j.beq 6 || j.beq 8 || j.beq 9 || j.beq 11 || j.beq 15)
      else
        if i.ble 11 then (j.beq 0 || j.beq 1 || j.beq 3 || j.beq 10 || j.beq 12 || j.beq 13)
        else (j.beq 2 || j.beq 5 || j.beq 7 || j.beq 9 || j.beq 11 || j.beq 15)
    else
      if i.ble 14 then
        if i.ble 13 then (j.beq 4 || j.beq 6 || j.beq 8 || j.beq 9 || j.beq 11 || j.beq 15)
        else (j.beq 0 || j.beq 1 || j.beq 2 || j.beq 4 || j.beq 15)
      else
        if i.ble 15 then (j.beq 3 || j.beq 10 || j.beq 12 || j.beq 13 || j.beq 14 || j.beq 16)
        else (j.beq 0 || j.beq 1 || j.beq 2 || j.beq 4 || j.beq 15)

private def c1Adj (i j : ℕ) : Bool :=
  if i.ble 8 then
    if i.ble 4 then
      if i.ble 2 then
        if i.ble 1 then
          if i.ble 0 then (j.beq 5 || j.beq 7 || j.beq 9 || j.beq 11 || j.beq 13)
          else (j.beq 6 || j.beq 8 || j.beq 9 || j.beq 12 || j.beq 13)
        else (j.beq 3 || j.beq 6 || j.beq 11 || j.beq 13 || j.beq 15)
      else
        if i.ble 3 then (j.beq 2 || j.beq 7 || j.beq 9 || j.beq 12 || j.beq 14)
        else (j.beq 5 || j.beq 7 || j.beq 10 || j.beq 12 || j.beq 13)
    else
      if i.ble 6 then
        if i.ble 5 then (j.beq 0 || j.beq 4 || j.beq 6 || j.beq 8 || j.beq 14)
        else (j.beq 1 || j.beq 2 || j.beq 5 || j.beq 10 || j.beq 16)
      else
        if i.ble 7 then (j.beq 0 || j.beq 3 || j.beq 4 || j.beq 8 || j.beq 16)
        else (j.beq 1 || j.beq 5 || j.beq 7 || j.beq 10 || j.beq 15)
  else
    if i.ble 12 then
      if i.ble 10 then
        if i.ble 9 then (j.beq 0 || j.beq 1 || j.beq 3 || j.beq 10 || j.beq 15)
        else (j.beq 4 || j.beq 6 || j.beq 8 || j.beq 9 || j.beq 11)
      else
        if i.ble 11 then (j.beq 0 || j.beq 2 || j.beq 10 || j.beq 12 || j.beq 14)
        else (j.beq 1 || j.beq 3 || j.beq 4 || j.beq 11 || j.beq 15)
    else
      if i.ble 14 then
        if i.ble 13 then (j.beq 0 || j.beq 1 || j.beq 2 || j.beq 4 || j.beq 14)
        else (j.beq 3 || j.beq 5 || j.beq 11 || j.beq 13 || j.beq 16)
      else
        if i.ble 15 then (j.beq 2 || j.beq 8 || j.beq 9 || j.beq 12 || j.beq 16)
        else (j.beq 6 || j.beq 7 || j.beq 14 || j.beq 15)

private def c2Adj (i j : ℕ) : Bool :=
  if i.ble 8 then
    if i.ble 4 then
      if i.ble 2 then
        if i.ble 1 then
          if i.ble 0 then (j.beq 2 || j.beq 5 || j.beq 7 || j.beq 9 || j.beq 11 || j.beq 14 || j.beq 15)
          else (j.beq 4 || j.beq 6 || j.beq 8 || j.beq 11 || j.beq 14 || j.beq 15 || j.beq 16)
        else (j.beq 0 || j.beq 3 || j.beq 4 || j.beq 6 || j.beq 8 || j.beq 12 || j.beq 16)
      else
        if i.ble 3 then (j.beq 2 || j.beq 5 || j.beq 7 || j.beq 9 || j.beq 11 || j.beq 14 || j.beq 15)
        else (j.beq 1 || j.beq 2 || j.beq 5 || j.beq 7 || j.beq 10 || j.beq 13)
    else
      if i.ble 6 then
        if i.ble 5 then (j.beq 0 || j.beq 3 || j.beq 4 || j.beq 6 || j.beq 8 || j.beq 12 || j.beq 16)
        else (j.beq 1 || j.beq 2 || j.beq 5 || j.beq 7 || j.beq 10 || j.beq 13)
      else
        if i.ble 7 then (j.beq 0 || j.beq 3 || j.beq 4 || j.beq 6 || j.beq 8 || j.beq 12 || j.beq 16)
        else (j.beq 1 || j.beq 2 || j.beq 5 || j.beq 7 || j.beq 10 || j.beq 13)
  else
    if i.ble 12 then
      if i.ble 10 then
        if i.ble 9 then (j.beq 0 || j.beq 3 || j.beq 10 || j.beq 12 || j.beq 13 || j.beq 16)
        else (j.beq 4 || j.beq 6 || j.beq 8 || j.beq 9 || j.beq 11 || j.beq 14 || j.beq 15)
      else
        if i.ble 11 then (j.beq 0 || j.beq 1 || j.beq 3 || j.beq 10 || j.beq 12 || j.beq 13)
        else (j.beq 2 || j.beq 5 || j.beq 7 || j.beq 9 || j.beq 11 || j.beq 14 || j.beq 15)
    else
      if i.ble 14 then
        if i.ble 13 then (j.beq 4 || j.beq 6 || j.beq 8 || j.beq 9 || j.beq 11 || j.beq 14 || j.beq 15)
        else (j.beq 0 || j.beq 1 || j.beq 3 || j.beq 10 || j.beq 12 || j.beq 13)
      else
        if i.ble 15 then (j.beq 0 || j.beq 1 || j.beq 3 || j.beq 10 || j.beq 12 || j.beq 13)
        else (j.beq 1 || j.beq 2 || j.beq 5 || j.beq 7 || j.beq 9)

private lemma c0Adj_iff : ∀ i j : Fin 17, (hostC 0).Adj i j ↔ c0Adj i.val j.val = true := by
  decide +kernel

private lemma c1Adj_iff : ∀ i j : Fin 17, (hostC 1).Adj i j ↔ c1Adj i.val j.val = true := by
  decide +kernel

private lemma c2Adj_iff : ∀ i j : Fin 17, (hostC 2).Adj i j ↔ c2Adj i.val j.val = true := by
  decide +kernel

private def listAll (p : ℕ → Bool) : List ℕ → Bool
  | [] => true
  | x :: xs => p x && listAll p xs

private def countList (p : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + countList p xs

private def forallLt : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | k + 1, p => p k && forallLt k p

private def countLt : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | k + 1, p => (if p k then 1 else 0) + countLt k p

private def sumLt : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | k + 1, f => f k + sumLt k f

/- Check for independent set of size `need` in `cAdj` (which is a clique in `cAdjᶜ`) -/
private def hasIndepAux (cAdj : ℕ → ℕ → Bool) : ℕ → ℕ → ℕ → List ℕ → Bool
  | _, _, 0, _ => true
  | 0, _, _ + 1, _ => false
  | fuel + 1, start, need + 1, chosen =>
    if fuel.ble need && !(fuel.beq need) then false
    else
      (if listAll (fun u => !(cAdj start u)) chosen then
        hasIndepAux cAdj fuel (start + 1) need (start :: chosen)
      else false)
      || hasIndepAux cAdj fuel (start + 1) (need + 1) chosen

private lemma cert_b1_no_k6 : hasIndepAux c1Adj 17 0 6 [] = false := by
  decide +kernel

private def addNonEdge (cg : ℕ → ℕ → Bool) (u v i j : ℕ) : Bool :=
  cg i j || (i.beq u && j.beq v) || (i.beq v && j.beq u)

private def evalSub (cg : ℕ → ℕ → Bool) (wantB2 : Bool) : Bool :=
  if hasIndepAux cg 9 0 6 [] then true
  else
    let d0 := countLt 9 (cg 0)
    let d1 := countLt 9 (cg 1)
    let d2 := countLt 9 (cg 2)
    let d3 := countLt 9 (cg 3)
    let d4 := countLt 9 (cg 4)
    let d5 := countLt 9 (cg 5)
    let d6 := countLt 9 (cg 6)
    let d7 := countLt 9 (cg 7)
    let d8 := countLt 9 (cg 8)
    let md5 := d0.ble 3 && d1.ble 3 && d2.ble 3 && d3.ble 3 && d4.ble 3 &&
               d5.ble 3 && d6.ble 3 && d7.ble 3 && d8.ble 3
    if !wantB2 then
      if !md5 then false
      else
        let c5 := (if d0.beq 3 then 1 else 0) + (if d1.beq 3 then 1 else 0) +
                  (if d2.beq 3 then 1 else 0) + (if d3.beq 3 then 1 else 0) +
                  (if d4.beq 3 then 1 else 0) + (if d5.beq 3 then 1 else 0) +
                  (if d6.beq 3 then 1 else 0) + (if d7.beq 3 then 1 else 0) +
                  (if d8.beq 3 then 1 else 0)
        if c5.ble 1 then true
        else
          let dAt (i : ℕ) : ℕ :=
            if i.ble 4 then
              if i.ble 2 then (if i.ble 1 then (if i.ble 0 then d0 else d1) else d2)
              else (if i.ble 3 then d3 else d4)
            else
              if i.ble 6 then (if i.ble 5 then d5 else d6)
              else (if i.ble 7 then d7 else d8)
          let e7 := sumLt 9 (fun i =>
            if (dAt i).beq 1 then
              countLt 9 (fun j => !(i.beq j) && (dAt j).beq 1 && !(cg i j))
            else 0)
          !((4 * c5 + e7).beq 16)
    else
      if !md5 then true
      else
        let c5 := (if d0.beq 3 then 1 else 0) + (if d1.beq 3 then 1 else 0) +
                  (if d2.beq 3 then 1 else 0) + (if d3.beq 3 then 1 else 0) +
                  (if d4.beq 3 then 1 else 0) + (if d5.beq 3 then 1 else 0) +
                  (if d6.beq 3 then 1 else 0) + (if d7.beq 3 then 1 else 0) +
                  (if d8.beq 3 then 1 else 0)
        if c5.ble 1 then false
        else
          let dAt (i : ℕ) : ℕ :=
            if i.ble 4 then
              if i.ble 2 then (if i.ble 1 then (if i.ble 0 then d0 else d1) else d2)
              else (if i.ble 3 then d3 else d4)
            else
              if i.ble 6 then (if i.ble 5 then d5 else d6)
              else (if i.ble 7 then d7 else d8)
          let e7 := sumLt 9 (fun i =>
            if (dAt i).beq 1 then
              countLt 9 (fun j => !(i.beq j) && (dAt j).beq 1 && !(cg i j))
            else 0)
          (4 * c5 + e7).beq 16

private def checkLeaf (cAdj : ℕ → ℕ → Bool) (wantB2 : Bool) (nonedges : ℕ) (vs : List ℕ) : Bool :=
  match vs with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8] =>
    let vAt (i : ℕ) : ℕ :=
      if i.ble 4 then
        if i.ble 2 then (if i.ble 1 then (if i.ble 0 then v0 else v1) else v2)
        else (if i.ble 3 then v3 else v4)
      else
        if i.ble 6 then (if i.ble 5 then v5 else v6)
        else (if i.ble 7 then v7 else v8)
    let cg (i j : ℕ) : Bool := cAdj (vAt i) (vAt j)
    let skip := wantB2 && !(forallLt 9 (fun i => (countLt 9 (cg i)).ble 3))
    if skip then true
    else
      (6).ble nonedges &&
      hasIndepAux cg 9 0 6 [] &&
      (if nonedges.ble 7 then
        forallLt 9 (fun u => forallLt 9 (fun v =>
          if u.ble v && !(u.beq v) && !(cg u v) then
            evalSub (addNonEdge cg u v) wantB2
          else true))
      else true) &&
      (if nonedges.ble 6 then
        forallLt 9 (fun u1 => forallLt 9 (fun v1 =>
          if u1.ble v1 && !(u1.beq v1) && !(cg u1 v1) then
            let cg1 := addNonEdge cg u1 v1
            forallLt 9 (fun u2 => forallLt 9 (fun v2 =>
              if u2.ble v2 && !(u2.beq v2) &&
                 ((u1.ble u2 && !(u1.beq u2)) || (u1.beq u2 && v1.ble v2 && !(v1.beq v2))) &&
                 !(cg u2 v2) then
                evalSub (addNonEdge cg1 u2 v2) wantB2
              else true))
          else true))
      else true)
  | _ => false

private def dfs9 (cAdj : ℕ → ℕ → Bool) (wantB2 : Bool) : ℕ → ℕ → ℕ → ℕ → List ℕ → Bool
  | _, _, 0, nonedges, vs =>
    if nonedges.ble 8 then checkLeaf cAdj wantB2 nonedges vs else true
  | 0, _, _ + 1, _, _ => true
  | fuel + 1, start, need + 1, nonedges, vs =>
    if !(nonedges.ble 8) then true
    else if fuel.ble need && !(fuel.beq need) then true
    else
      let add := countList (fun u => cAdj start u) vs
      dfs9 cAdj wantB2 fuel (start + 1) need (nonedges + add) (start :: vs) &&
      dfs9 cAdj wantB2 fuel (start + 1) (need + 1) nonedges vs

private lemma cert_b0_dense : dfs9 c0Adj false 17 0 9 0 [] = true := by
  decide +kernel

private lemma cert_b2_dense : dfs9 c2Adj true 17 0 9 0 [] = true := by
  decide +kernel

/- Section 2: Soundness of recursive Bool/Nat combinators -/

private lemma ble_iff_le (a b : ℕ) : a.ble b = true ↔ a ≤ b :=
  Iff.of_eq Nat.ble_eq

private lemma beq_iff_eq (a b : ℕ) : a.beq b = true ↔ a = b :=
  Iff.of_eq Nat.beq_eq

private lemma beq_eq_false_iff (a b : ℕ) : a.beq b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, beq_iff_eq]

private lemma listAll_eq_true {p : ℕ → Bool} {l : List ℕ} :
    listAll p l = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp [listAll]
  | cons a t ih =>
    simp only [listAll, Bool.and_eq_true, ih, List.mem_cons, forall_eq_or_imp]

private lemma forallLt_eq_true {n : ℕ} {p : ℕ → Bool} (h : forallLt n p = true) :
    ∀ i < n, p i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ k ih =>
    simp only [forallLt, Bool.and_eq_true] at h
    intro i hi
    by_cases he : i = k
    · exact he ▸ h.1
    · exact ih h.2 i (by omega)

private lemma countLt_eq_sum {n : ℕ} (p : ℕ → Bool) :
    countLt n p = ∑ i : Fin n, if p i.val = true then 1 else 0 := by
  induction n with
  | zero => simp [countLt]
  | succ k ih =>
    simp only [countLt, ih]
    rw [Fin.sum_univ_castSucc, add_comm]
    rfl

private lemma countLt_eq_card {n : ℕ} (p : ℕ → Bool) :
    countLt n p = (Finset.univ.filter (fun i : Fin n => p i.val = true)).card := by
  rw [countLt_eq_sum, Finset.card_filter]

private lemma sumLt_eq_sum {n : ℕ} (f : ℕ → ℕ) :
    sumLt n f = ∑ i : Fin n, f i.val := by
  induction n with
  | zero => simp [sumLt]
  | succ k ih =>
    simp only [sumLt, ih]
    rw [Fin.sum_univ_castSucc, add_comm]
    rfl

private lemma countList_eq_sum {p : ℕ → Bool} (l : List ℕ) :
    countList p l = ∑ i : Fin l.length, if p l[i.val] = true then 1 else 0 := by
  induction l with
  | nil => simp [countList]
  | cons a t ih =>
    simp only [countList, ih, List.length_cons]
    rw [Fin.sum_univ_succ]
    rfl

private lemma list_pairwise_lt_length_le :
    ∀ (l : List ℕ) (lo hi : ℕ), l.Pairwise (· < ·) → (∀ x ∈ l, lo ≤ x ∧ x < hi) →
      l.length ≤ hi - lo
  | [], _, _, _, _ => Nat.zero_le _
  | a :: t, lo, hi, hp, hmem => by
    rw [List.pairwise_cons] at hp
    have ha := hmem a (List.mem_cons_self ..)
    have hrec := list_pairwise_lt_length_le t (a + 1) hi hp.2 (fun x hx => by
      have hx' := hmem x (List.mem_cons_of_mem _ hx)
      have hax := hp.1 x hx
      omega)
    simp only [List.length_cons]
    omega

/- Section 3: Soundness of `hasIndepAux` (both directions) -/

private lemma hasIndepAux_false_contra {cAdj : ℕ → ℕ → Bool} :
    ∀ (fuel start need : ℕ) (chosen : List ℕ),
      hasIndepAux cAdj fuel start need chosen = false →
      ∀ (rest : List ℕ), rest.length = need → rest.Pairwise (· < ·) →
        (∀ x ∈ rest, start ≤ x ∧ x < start + fuel) →
        (∀ x ∈ rest, ∀ y ∈ chosen, cAdj x y = false) →
        (∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → cAdj x y = false) →
        False
  | _, _, 0, _, hfalse, _, _, _, _, _, _ => by
    simp [hasIndepAux] at hfalse
  | 0, start, need + 1, _, _, rest, hlen, _, hrange, _, _ => by
    cases rest with
    | nil => simp at hlen
    | cons a _ =>
      have := hrange a (List.mem_cons_self ..)
      omega
  | fuel + 1, start, need + 1, chosen, hfalse, rest, hlen, hpw, hrange, hch, hind => by
    have hlen_le := list_pairwise_lt_length_le rest start (start + (fuel + 1)) hpw hrange
    have hnot_lt : ¬ (fuel < need) := by omega
    have hcond : (fuel.ble need && !(fuel.beq need)) = false := by
      rw [Bool.and_eq_false_iff, Bool.not_eq_false']
      by_cases hle : fuel ≤ need
      · right; exact (beq_iff_eq _ _).mpr (by omega)
      · left; cases hb : fuel.ble need
        · rfl
        · exact absurd ((ble_iff_le _ _).mp hb) hle
    simp only [hasIndepAux, hcond, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_false_iff] at hfalse
    obtain ⟨hbr1, hbr2⟩ := hfalse
    cases rest with
    | nil => simp at hlen
    | cons a t =>
      rw [List.pairwise_cons] at hpw
      have ha_range := hrange a (List.mem_cons_self ..)
      by_cases has : a = start
      · subst has
        have hall : listAll (fun u => !(cAdj a u)) chosen = true := by
          rw [listAll_eq_true]
          intro y hy
          simp [hch a (List.mem_cons_self ..) y hy]
        simp only [hall, ↓reduceIte] at hbr1
        exact hasIndepAux_false_contra fuel (a + 1) need (a :: chosen) hbr1 t
          (by simpa using hlen) hpw.2
          (fun x hx => by
            have hx' := hrange x (List.mem_cons_of_mem _ hx)
            have hax := hpw.1 x hx
            omega)
          (fun x hx y hy => by
            rcases List.mem_cons.mp hy with rfl | hy'
            · exact hind x (List.mem_cons_of_mem _ hx) y (List.mem_cons_self ..) (by have := hpw.1 x hx; omega)
            · exact hch x (List.mem_cons_of_mem _ hx) y hy')
          (fun x hx y hy hne => hind x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hne)
      · exact hasIndepAux_false_contra fuel (start + 1) (need + 1) chosen hbr2 (a :: t)
          hlen (List.pairwise_cons.mpr hpw)
          (fun x hx => by
            have hx' := hrange x hx
            rcases List.mem_cons.mp hx with rfl | hxt
            · omega
            · have := hpw.1 x hxt; omega)
          hch hind

private lemma hasIndepAux_true_exists {cAdj : ℕ → ℕ → Bool} :
    ∀ (fuel start need : ℕ) (chosen : List ℕ),
      (∀ i < start + fuel, ∀ j < start + fuel, cAdj i j = cAdj j i) →
      hasIndepAux cAdj fuel start need chosen = true →
      (∀ x ∈ chosen, x < start) →
      (∀ x ∈ chosen, ∀ y ∈ chosen, x ≠ y → cAdj x y = false) →
      chosen.Nodup →
      ∃ full : List ℕ, full.length = chosen.length + need ∧ full.Nodup ∧
        (∀ x ∈ full, x < start + fuel) ∧
        (∀ x ∈ full, ∀ y ∈ full, x ≠ y → cAdj x y = false)
  | _, start, 0, chosen, _, _, hlt, hind, hnd =>
    ⟨chosen, by simp, hnd, fun x hx => by have := hlt x hx; omega, hind⟩
  | 0, _, _ + 1, _, _, htrue, _, _, _ => by
    simp [hasIndepAux] at htrue
  | fuel + 1, start, need + 1, chosen, hsym, htrue, hlt, hind, hnd => by
    have hsym' : ∀ i < (start + 1) + fuel, ∀ j < (start + 1) + fuel, cAdj i j = cAdj j i :=
      fun i hi j hj => hsym i (by omega) j (by omega)
    simp only [hasIndepAux] at htrue
    split at htrue
    · simp at htrue
    · rw [Bool.or_eq_true] at htrue
      rcases htrue with hbr1 | hbr2
      · split at hbr1
        · rename_i hall
          rw [listAll_eq_true] at hall
          have hnotmem : start ∉ chosen := fun hm => by have := hlt start hm; omega
          have hnd' : (start :: chosen).Nodup := List.nodup_cons.mpr ⟨hnotmem, hnd⟩
          have hlt' : ∀ x ∈ start :: chosen, x < start + 1 := by
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx'
            · omega
            · have := hlt x hx'; omega
          have hind' : ∀ x ∈ start :: chosen, ∀ y ∈ start :: chosen, x ≠ y → cAdj x y = false := by
            intro x hx y hy hne
            rcases List.mem_cons.mp hx with rfl | hx' <;>
              rcases List.mem_cons.mp hy with rfl | hy'
            · exact absurd rfl hne
            · have := hall y hy'; simpa using this
            · have := hall x hx'
              rw [hsym x (by have := hlt x hx'; omega) y (by omega)]
              simpa using this
            · exact hind x hx' y hy' hne
          obtain ⟨full, hflen, hfnd, hflt, hfind⟩ :=
            hasIndepAux_true_exists fuel (start + 1) need (start :: chosen) hsym' hbr1 hlt' hind' hnd'
          exact ⟨full, by simp only [List.length_cons] at hflen; omega, hfnd,
            fun x hx => by have := hflt x hx; omega, hfind⟩
        · simp at hbr1
      · obtain ⟨full, hflen, hfnd, hflt, hfind⟩ :=
          hasIndepAux_true_exists fuel (start + 1) (need + 1) chosen hsym' hbr2
            (fun x hx => by have := hlt x hx; omega) hind hnd
        exact ⟨full, hflen, hfnd, fun x hx => by have := hflt x hx; omega, hfind⟩

private lemma b1_cliqueFree_six : (hostC 1)ᶜ.CliqueFree 6 := by
  intro S hS
  obtain ⟨hScl, hScard⟩ := hS
  let rest : List ℕ := (S.sort (· ≤ ·)).map Fin.val
  have hlen : rest.length = 6 := by simp [rest, hScard]
  have hpw : rest.Pairwise (· < ·) := by
    have hp := Finset.pairwise_sort S (· ≤ ·)
    have hnd := Finset.sort_nodup S (· ≤ ·)
    have hlt := (hp.and hnd).imp (fun h => lt_of_le_of_ne h.1 h.2)
    exact List.pairwise_map.mpr (hlt.imp (fun h => h))
  have hrange : ∀ x ∈ rest, 0 ≤ x ∧ x < 17 := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨Nat.zero_le _, v.isLt⟩
  have hind : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → c1Adj x y = false := by
    intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
    have huS : u ∈ S := (Finset.mem_sort (· ≤ ·)).mp hu
    have hvS : v ∈ S := (Finset.mem_sort (· ≤ ·)).mp hv
    have huv : u ≠ v := fun h => hne (congrArg Fin.val h)
    have hadj : (hostC 1)ᶜ.Adj u v := hScl huS hvS huv
    have hnot : ¬ (hostC 1).Adj u v := hadj.2
    rw [c1Adj_iff] at hnot
    cases hc : c1Adj u.val v.val
    · rfl
    · exact absurd hc hnot
  exact hasIndepAux_false_contra 17 0 6 [] cert_b1_no_k6 rest hlen hpw hrange
    (by simp) hind

private lemma cliqueFree_of_hasIndepAux_true {G : SimpleGraph (Fin 9)} {cg : ℕ → ℕ → Bool}
    (hsym : ∀ i < 9, ∀ j < 9, cg i j = cg j i)
    (hcg : ∀ i j : Fin 9, G.Adj i j ↔ i ≠ j ∧ cg i.val j.val = false)
    (htrue : hasIndepAux cg 9 0 6 [] = true) : ¬ G.CliqueFree 6 := by
  intro hcf
  obtain ⟨full, hflen, hfnd, hflt, hfind⟩ :=
    hasIndepAux_true_exists 9 0 6 [] (by simpa using hsym) htrue (by simp) (by simp) List.nodup_nil
  simp only [List.length_nil, zero_add] at hflen hflt
  let S : Finset (Fin 9) := Finset.univ.filter (fun v : Fin 9 => v.val ∈ full)
  have hScard : S.card = 6 := by
    have hbij : full.toFinset.card = S.card := by
      refine Finset.card_bij (fun x hx => ⟨x, hflt x (List.mem_toFinset.mp hx)⟩) ?_ ?_ ?_
      · intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, List.mem_toFinset.mp hx⟩
      · intro x₁ _ x₂ _ h
        exact congrArg Fin.val h
      · intro v hv
        exact ⟨v.val, List.mem_toFinset.mpr (Finset.mem_filter.mp hv).2, rfl⟩
    rw [← hbij, List.toFinset_card_of_nodup hfnd, hflen]
  have hScl : G.IsClique (S : Set (Fin 9)) := by
    intro u hu v hv huv
    have hu' : u.val ∈ full := (Finset.mem_filter.mp hu).2
    have hv' : v.val ∈ full := (Finset.mem_filter.mp hv).2
    exact (hcg u v).mpr ⟨huv, hfind u.val hu' v.val hv' (fun h => huv (Fin.ext h))⟩
  exact hcf S ⟨hScl, hScard⟩

/- Section 4: Soundness of `dfs9` and non-edge counting -/

private def pairCount (cAdj : ℕ → ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: xs => countList (fun u => cAdj x u) xs + pairCount cAdj xs

private lemma pairCount_append_ge (cAdj : ℕ → ℕ → Bool) (l₁ l₂ : List ℕ) :
    pairCount cAdj l₂ ≤ pairCount cAdj (l₁ ++ l₂) := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
    simp only [List.cons_append, pairCount]
    omega

private lemma dfs9_sound {cAdj : ℕ → ℕ → Bool} {wantB2 : Bool} :
    ∀ (fuel start need nonedges : ℕ) (vs : List ℕ),
      dfs9 cAdj wantB2 fuel start need nonedges vs = true →
      nonedges = pairCount cAdj vs →
      ∀ (rest : List ℕ), rest.length = need → rest.Pairwise (· < ·) →
        (∀ x ∈ rest, start ≤ x ∧ x < start + fuel) →
        pairCount cAdj (rest.reverse ++ vs) ≤ 8 →
        checkLeaf cAdj wantB2 (pairCount cAdj (rest.reverse ++ vs)) (rest.reverse ++ vs) = true
  | _, _, 0, nonedges, vs, hok, hne, rest, hlen, _, _, hle => by
    cases rest with
    | cons _ _ => simp at hlen
    | nil =>
      simp only [List.reverse_nil, List.nil_append] at hle ⊢
      rw [hne] at hok
      have h8 : (pairCount cAdj vs).ble 8 = true := (ble_iff_le _ _).mpr hle
      simpa [dfs9, h8] using hok
  | 0, start, need + 1, _, _, _, _, rest, hlen, _, hrange, _ => by
    cases rest with
    | nil => simp at hlen
    | cons a _ =>
      have := hrange a (List.mem_cons_self ..)
      omega
  | fuel + 1, start, need + 1, nonedges, vs, hok, hne, rest, hlen, hpw, hrange, hle => by
    have hnon_le : nonedges ≤ 8 := by
      rw [hne]
      exact (pairCount_append_ge cAdj rest.reverse vs).trans hle
    have hlen_le := list_pairwise_lt_length_le rest start (start + (fuel + 1)) hpw hrange
    have h8 : nonedges.ble 8 = true := (ble_iff_le _ _).mpr hnon_le
    have hcond : (fuel.ble need && !(fuel.beq need)) = false := by
      rw [Bool.and_eq_false_iff, Bool.not_eq_false']
      by_cases hle : fuel ≤ need
      · right; exact (beq_iff_eq _ _).mpr (by omega)
      · left; cases hb : fuel.ble need
        · rfl
        · exact absurd ((ble_iff_le _ _).mp hb) hle
    simp only [dfs9, h8, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcond, Bool.and_eq_true] at hok
    obtain ⟨hbr1, hbr2⟩ := hok
    cases rest with
    | nil => simp at hlen
    | cons a t =>
      rw [List.pairwise_cons] at hpw
      have ha_range := hrange a (List.mem_cons_self ..)
      by_cases has : a = start
      · subst has
        have hrev : (a :: t).reverse ++ vs = t.reverse ++ (a :: vs) := by
          simp [List.reverse_cons, List.append_assoc]
        rw [hrev] at hle ⊢
        have hne' : nonedges + countList (fun u => cAdj a u) vs = pairCount cAdj (a :: vs) := by
          simp only [pairCount, hne]
          omega
        exact dfs9_sound fuel (a + 1) need _ (a :: vs) hbr1 hne' t
          (by simpa using hlen) hpw.2
          (fun x hx => by
            have hx' := hrange x (List.mem_cons_of_mem _ hx)
            have hax := hpw.1 x hx
            omega)
          hle
      · exact dfs9_sound fuel (start + 1) (need + 1) nonedges vs hbr2 hne (a :: t)
          hlen (List.pairwise_cons.mpr hpw)
          (fun x hx => by
            have hx' := hrange x hx
            rcases List.mem_cons.mp hx with rfl | hxt
            · omega
            · have := hpw.1 x hxt; omega)
          hle

private lemma two_mul_pairCount {cAdj : ℕ → ℕ → Bool} {B : ℕ}
    (hsym : ∀ i < B, ∀ j < B, cAdj i j = cAdj j i) (hirr : ∀ i < B, cAdj i i = false) :
    ∀ (l : List ℕ), (∀ x ∈ l, x < B) →
      2 * pairCount cAdj l =
        ∑ i : Fin l.length, ∑ j : Fin l.length, if cAdj l[i.val] l[j.val] = true then 1 else 0
  | [], _ => by simp [pairCount]
  | a :: t, hlt => by
    have ha : a < B := hlt a (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, x < B := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    simp only [pairCount, List.length_cons]
    rw [Fin.sum_univ_succ]
    have h0 : (∑ j : Fin (t.length + 1),
        if cAdj (a :: t)[(0 : Fin (t.length + 1)).val] (a :: t)[j.val] = true then 1 else 0) =
        countList (fun u => cAdj a u) t := by
      rw [Fin.sum_univ_succ, countList_eq_sum]
      simp only [Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ,
        hirr a ha, Bool.false_eq_true, ↓reduceIte, zero_add]
      rfl
    have hrest : (∑ i : Fin t.length, ∑ j : Fin (t.length + 1),
        if cAdj (a :: t)[i.succ.val] (a :: t)[j.val] = true then 1 else 0) =
        countList (fun u => cAdj a u) t +
        ∑ i : Fin t.length, ∑ j : Fin t.length, if cAdj t[i.val] t[j.val] = true then 1 else 0 := by
      have hsplit : ∀ i : Fin t.length,
          (∑ j : Fin (t.length + 1),
            if cAdj (a :: t)[i.succ.val] (a :: t)[j.val] = true then 1 else 0) =
          (if cAdj a t[i.val] = true then 1 else 0) +
          (∑ j : Fin t.length, if cAdj t[i.val] t[j.val] = true then 1 else 0) := by
        intro i
        rw [Fin.sum_univ_succ]
        have hi : t[i.val] < B := ht t[i.val] (List.getElem_mem _)
        simp [hsym t[i.val] hi a ha]
      simp_rw [hsplit, Finset.sum_add_distrib, ← countList_eq_sum]
    have ih := two_mul_pairCount hsym hirr t ht
    rw [h0, hrest]
    omega

/- Section 5: Graph invariants on `Fin 9` and isomorphism transfer -/

private def minDeg5 (H : SimpleGraph (Fin 9)) [DecidableRel H.Adj] : Prop :=
  ∀ v : Fin 9, 5 ≤ H.degree v

private def c5 (H : SimpleGraph (Fin 9)) [DecidableRel H.Adj] : ℕ :=
  (Finset.univ.filter (fun v : Fin 9 => H.degree v = 5)).card

private def e7dir (H : SimpleGraph (Fin 9)) [DecidableRel H.Adj] : ℕ :=
  ∑ u : Fin 9, ∑ v : Fin 9, if H.degree u = 7 ∧ H.degree v = 7 ∧ H.Adj u v then 1 else 0

private def isB2Sig (H : SimpleGraph (Fin 9)) [DecidableRel H.Adj] : Prop :=
  2 ≤ c5 H ∧ 4 * c5 H + e7dir H = 16

private lemma minDeg5_iso {H D : SimpleGraph (Fin 9)} [DecidableRel H.Adj] [DecidableRel D.Adj]
    (e : H ≃g D) : minDeg5 H ↔ minDeg5 D := by
  constructor
  · intro h v
    have := h (e.symm v)
    simpa [e.degree_eq] using this
  · intro h v
    have := h (e v)
    simpa [e.degree_eq] using this

private lemma c5_iso {H D : SimpleGraph (Fin 9)} [DecidableRel H.Adj] [DecidableRel D.Adj]
    (e : H ≃g D) : c5 H = c5 D := by
  dsimp only [c5]
  refine Finset.card_bij (fun v _ => e v) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    simpa [e.degree_eq] using hv
  · intro u _ v _ h
    exact e.injective h
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨e.symm w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [e.degree_eq] using hw⟩,
      e.apply_symm_apply w⟩

private lemma e7dir_iso {H D : SimpleGraph (Fin 9)} [DecidableRel H.Adj] [DecidableRel D.Adj]
    (e : H ≃g D) : e7dir H = e7dir D := by
  dsimp only [e7dir]
  rw [← e.toEquiv.sum_comp (fun u => ∑ v : Fin 9,
    if D.degree u = 7 ∧ D.degree v = 7 ∧ D.Adj u v then 1 else 0)]
  refine Finset.sum_congr rfl fun u _ => ?_
  dsimp only [RelIso.coe_fn_toEquiv]
  rw [← e.toEquiv.sum_comp (fun v =>
    if D.degree (e u) = 7 ∧ D.degree v = 7 ∧ D.Adj (e u) v then 1 else 0)]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [e.degree_eq, e.map_rel_iff]

private lemma isB2Sig_iso {H D : SimpleGraph (Fin 9)} [DecidableRel H.Adj] [DecidableRel D.Adj]
    (e : H ≃g D) : isB2Sig H ↔ isB2Sig D := by
  dsimp only [isB2Sig]
  rw [c5_iso e, e7dir_iso e]

private lemma cliqueFree_iso {H D : SimpleGraph (Fin 9)} (e : H ≃g D) :
    H.CliqueFree 6 ↔ D.CliqueFree 6 := by
  have dir : ∀ {A B : SimpleGraph (Fin 9)}, (A ≃g B) → B.CliqueFree 6 → A.CliqueFree 6 := by
    intro A B iso hB S ⟨hScl, hSc⟩
    refine hB (S.map iso.toEquiv.toEmbedding) ⟨?_, by simp [hSc]⟩
    intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact iso.map_rel_iff.mpr (hScl hu hv (fun h => hne (congrArg iso.toEquiv.toEmbedding h)))
  exact ⟨dir e.symm, dir e⟩

/- Section 6: Connecting `evalSub` and `checkLeaf` to `H ≤ G` on `Fin 9` -/

private lemma deg_add_cdeg {H : SimpleGraph (Fin 9)} [DecidableRel H.Adj] {ch : ℕ → ℕ → Bool}
    (hch : ∀ i j : Fin 9, H.Adj i j ↔ i ≠ j ∧ ch i.val j.val = false)
    (hirr : ∀ i : Fin 9, ch i.val i.val = false) (i : Fin 9) :
    H.degree i + countLt 9 (ch i.val) = 8 := by
  rw [countLt_eq_card]
  have hdeg : H.degree i = (Finset.univ.filter (fun j : Fin 9 => H.Adj i j)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext j
    simp [SimpleGraph.mem_neighborFinset]
  rw [hdeg]
  have hdisj : Disjoint (Finset.univ.filter (fun j : Fin 9 => H.Adj i j))
      (Finset.univ.filter (fun j : Fin 9 => ch i.val j.val = true)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    have h1 := ((hch i j).mp (Finset.mem_filter.mp hj1).2).2
    have h2 := (Finset.mem_filter.mp hj2).2
    rw [h1] at h2
    simp at h2
  have hunion : Finset.univ.filter (fun j : Fin 9 => H.Adj i j) ∪
      Finset.univ.filter (fun j : Fin 9 => ch i.val j.val = true) = Finset.univ.erase i := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro (hadj | htrue)
      · exact (hadj.ne).symm
      · rintro rfl; rw [hirr] at htrue; simp at htrue
    · intro hne
      cases hc : ch i.val j.val
      · exact Or.inl ((hch i j).mpr ⟨hne.symm, hc⟩)
      · exact Or.inr rfl
  rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

private lemma evalSub_sound {H : SimpleGraph (Fin 9)} [DecidableRel H.Adj] {ch : ℕ → ℕ → Bool}
    {wantB2 : Bool}
    (hsym : ∀ i < 9, ∀ j < 9, ch i j = ch j i)
    (hirr : ∀ i : Fin 9, ch i.val i.val = false)
    (hch : ∀ i j : Fin 9, H.Adj i j ↔ i ≠ j ∧ ch i.val j.val = false)
    (hcf : H.CliqueFree 6)
    (heval : evalSub ch wantB2 = true) :
    (wantB2 = false → minDeg5 H ∧ ¬ isB2Sig H) ∧
    (wantB2 = true → minDeg5 H → isB2Sig H) := by
  have hnoK6 : hasIndepAux ch 9 0 6 [] = false := by
    cases hk : hasIndepAux ch 9 0 6 []
    · rfl
    · exact absurd hcf (cliqueFree_of_hasIndepAux_true hsym hch hk)
  have hdeg : ∀ i : Fin 9, countLt 9 (ch i.val) = 8 - H.degree i := by
    intro i
    have := deg_add_cdeg hch hirr i
    omega
  have hd_le3 : ∀ i : Fin 9, (countLt 9 (ch i.val)).ble 3 = true ↔ 5 ≤ H.degree i := by
    intro i
    rw [ble_iff_le, hdeg i]
    have hle8 : H.degree i ≤ 8 := by have := deg_add_cdeg hch hirr i; omega
    omega
  have hd_eq3 : ∀ i : Fin 9, (countLt 9 (ch i.val)).beq 3 = true ↔ H.degree i = 5 := by
    intro i
    rw [beq_iff_eq, hdeg i]
    have hle8 : H.degree i ≤ 8 := by have := deg_add_cdeg hch hirr i; omega
    omega
  have hd_eq1 : ∀ i : Fin 9, (countLt 9 (ch i.val)).beq 1 = true ↔ H.degree i = 7 := by
    intro i
    rw [beq_iff_eq, hdeg i]
    have hle8 : H.degree i ≤ 8 := by have := deg_add_cdeg hch hirr i; omega
    omega
  let dAt (i : ℕ) : ℕ :=
    if i.ble 4 then
      if i.ble 2 then (if i.ble 1 then (if i.ble 0 then countLt 9 (ch 0) else countLt 9 (ch 1)) else countLt 9 (ch 2))
      else (if i.ble 3 then countLt 9 (ch 3) else countLt 9 (ch 4))
    else
      if i.ble 6 then (if i.ble 5 then countLt 9 (ch 5) else countLt 9 (ch 6))
      else (if i.ble 7 then countLt 9 (ch 7) else countLt 9 (ch 8))
  have hdAt_eq : ∀ i : Fin 9, dAt i.val = countLt 9 (ch i.val) := by
    intro i; fin_cases i <;> rfl
  have hmd5_iff :
      ((countLt 9 (ch 0)).ble 3 && (countLt 9 (ch 1)).ble 3 && (countLt 9 (ch 2)).ble 3 &&
       (countLt 9 (ch 3)).ble 3 && (countLt 9 (ch 4)).ble 3 && (countLt 9 (ch 5)).ble 3 &&
       (countLt 9 (ch 6)).ble 3 && (countLt 9 (ch 7)).ble 3 && (countLt 9 (ch 8)).ble 3) = true ↔
      minDeg5 H := by
    simp only [Bool.and_eq_true]
    constructor
    · intro h i
      fin_cases i
      · exact (hd_le3 0).mp h.1.1.1.1.1.1.1.1
      · exact (hd_le3 1).mp h.1.1.1.1.1.1.1.2
      · exact (hd_le3 2).mp h.1.1.1.1.1.1.2
      · exact (hd_le3 3).mp h.1.1.1.1.1.2
      · exact (hd_le3 4).mp h.1.1.1.1.2
      · exact (hd_le3 5).mp h.1.1.1.2
      · exact (hd_le3 6).mp h.1.1.2
      · exact (hd_le3 7).mp h.1.2
      · exact (hd_le3 8).mp h.2
    · intro h
      exact ⟨⟨⟨⟨⟨⟨⟨⟨(hd_le3 0).mpr (h 0), (hd_le3 1).mpr (h 1)⟩, (hd_le3 2).mpr (h 2)⟩,
        (hd_le3 3).mpr (h 3)⟩, (hd_le3 4).mpr (h 4)⟩, (hd_le3 5).mpr (h 5)⟩,
        (hd_le3 6).mpr (h 6)⟩, (hd_le3 7).mpr (h 7)⟩, (hd_le3 8).mpr (h 8)⟩
  have hc5_eq :
      ((if (countLt 9 (ch 0)).beq 3 then 1 else 0) + (if (countLt 9 (ch 1)).beq 3 then 1 else 0) +
       (if (countLt 9 (ch 2)).beq 3 then 1 else 0) + (if (countLt 9 (ch 3)).beq 3 then 1 else 0) +
       (if (countLt 9 (ch 4)).beq 3 then 1 else 0) + (if (countLt 9 (ch 5)).beq 3 then 1 else 0) +
       (if (countLt 9 (ch 6)).beq 3 then 1 else 0) + (if (countLt 9 (ch 7)).beq 3 then 1 else 0) +
       (if (countLt 9 (ch 8)).beq 3 then 1 else 0)) = c5 H := by
    have hsum9 : ∀ f : Fin 9 → ℕ,
        ∑ i : Fin 9, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
      intro f
      simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero, zero_add]
      rfl
    dsimp only [c5]
    rw [Finset.card_filter, hsum9]
    have hterm : ∀ (k : ℕ) (hk : k < 9),
        (if (countLt 9 (ch k)).beq 3 = true then 1 else 0) =
        (if H.degree ⟨k, hk⟩ = 5 then 1 else 0) := by
      intro k hk
      by_cases h : H.degree ⟨k, hk⟩ = 5
      · simp [h, (hd_eq3 ⟨k, hk⟩).mpr h]
      · have hf : (countLt 9 (ch k)).beq 3 = false := by
          cases hb : (countLt 9 (ch k)).beq 3
          · rfl
          · exact absurd ((hd_eq3 ⟨k, hk⟩).mp hb) h
        simp [h, hf]
    rw [hterm 0 (by decide), hterm 1 (by decide), hterm 2 (by decide), hterm 3 (by decide),
      hterm 4 (by decide), hterm 5 (by decide), hterm 6 (by decide), hterm 7 (by decide),
      hterm 8 (by decide)]
    rfl
  have he7_eq :
      sumLt 9 (fun i =>
        if (dAt i).beq 1 then
          countLt 9 (fun j => !(i.beq j) && (dAt j).beq 1 && !(ch i j))
        else 0) = e7dir H := by
    rw [sumLt_eq_sum]
    dsimp only [e7dir]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdAt_eq i]
    by_cases hi7 : H.degree i = 7
    · have hb : (countLt 9 (ch i.val)).beq 1 = true := (hd_eq1 i).mpr hi7
      rw [hb]
      simp only [↓reduceIte, countLt_eq_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hdAt_eq j]
      by_cases hij : H.degree j = 7 ∧ H.Adj i j
      · have h1 : i.val.beq j.val = false := by
          cases h : i.val.beq j.val
          · rfl
          · exfalso; exact hij.2.ne (Fin.ext ((beq_iff_eq _ _).mp h))
        have h2 : (countLt 9 (ch j.val)).beq 1 = true := (hd_eq1 j).mpr hij.1
        have h3 : ch i.val j.val = false := ((hch i j).mp hij.2).2
        simp [hi7, hij.1, hij.2, h1, h2, h3]
      · have hnot : ¬ (H.degree i = 7 ∧ H.degree j = 7 ∧ H.Adj i j) := fun h => hij ⟨h.2.1, h.2.2⟩
        have hb0 : (!(i.val.beq j.val) && (countLt 9 (ch j.val)).beq 1 && !(ch i.val j.val)) = false := by
          by_contra h
          simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_true'] at h
          have hne : i ≠ j := fun he => by
            have : i.val.beq j.val = true := (beq_iff_eq _ _).mpr (congrArg Fin.val he)
            rw [this] at h; simp at h
          exact hij ⟨(hd_eq1 j).mp h.1.2, (hch i j).mpr ⟨hne, h.2⟩⟩
        simp [hnot, hb0]
    · have hb : (countLt 9 (ch i.val)).beq 1 = false := by
        cases h : (countLt 9 (ch i.val)).beq 1
        · rfl
        · exact absurd ((hd_eq1 i).mp h) hi7
      simp [hb, hi7]
  dsimp only [dAt] at he7_eq
  dsimp only [evalSub] at heval
  rw [hnoK6] at heval
  simp only [Bool.false_eq_true, ↓reduceIte] at heval
  constructor
  · intro hw
    subst hw
    simp only [Bool.not_false, ↓reduceIte] at heval
    by_cases hmd : minDeg5 H
    · have hmdB := hmd5_iff.mpr hmd
      simp only [hmdB, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval
      refine ⟨hmd, ?_⟩
      intro ⟨hc5_2, h4c5⟩
      have hc5not1 : (c5 H).ble 1 = false := by
        cases h : (c5 H).ble 1
        · rfl
        · have := (ble_iff_le _ _).mp h; omega
      rw [hc5_eq] at heval
      simp only [hc5not1, Bool.false_eq_true, ↓reduceIte] at heval
      rw [he7_eq] at heval
      have h16 : (4 * c5 H + e7dir H).beq 16 = true := (beq_iff_eq _ _).mpr h4c5
      rw [h16] at heval
      simp at heval
    · have hmdB : ((countLt 9 (ch 0)).ble 3 && (countLt 9 (ch 1)).ble 3 && (countLt 9 (ch 2)).ble 3 &&
         (countLt 9 (ch 3)).ble 3 && (countLt 9 (ch 4)).ble 3 && (countLt 9 (ch 5)).ble 3 &&
         (countLt 9 (ch 6)).ble 3 && (countLt 9 (ch 7)).ble 3 && (countLt 9 (ch 8)).ble 3) = false := by
        cases h : ((countLt 9 (ch 0)).ble 3 && (countLt 9 (ch 1)).ble 3 && (countLt 9 (ch 2)).ble 3 &&
          (countLt 9 (ch 3)).ble 3 && (countLt 9 (ch 4)).ble 3 && (countLt 9 (ch 5)).ble 3 &&
          (countLt 9 (ch 6)).ble 3 && (countLt 9 (ch 7)).ble 3 && (countLt 9 (ch 8)).ble 3)
        · rfl
        · exact absurd (hmd5_iff.mp h) hmd
      simp only [hmdB, Bool.not_false, ↓reduceIte] at heval
      simp at heval
  · intro hw hmd
    subst hw
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval
    have hmdB := hmd5_iff.mpr hmd
    simp only [hmdB, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at heval
    rw [hc5_eq] at heval
    by_cases hc5_1 : c5 H ≤ 1
    · have hb : (c5 H).ble 1 = true := (ble_iff_le _ _).mpr hc5_1
      simp [hb] at heval
    · have hb : (c5 H).ble 1 = false := by
        cases h : (c5 H).ble 1
        · rfl
        · exact absurd ((ble_iff_le _ _).mp h) hc5_1
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at heval
      rw [he7_eq] at heval
      exact ⟨by omega, (beq_iff_eq _ _).mp heval⟩

private lemma edge_to_ordered_pair {G : SimpleGraph (Fin 9)} [DecidableRel G.Adj] {e : Sym2 (Fin 9)}
    (he : e ∈ G.edgeFinset) :
    ∃ u v : Fin 9, u.val < v.val ∧ G.Adj u v ∧ e = s(u, v) := by
  induction e using Sym2.ind with
  | _ a b =>
    have hadj : G.Adj a b := by simpa using SimpleGraph.mem_edgeFinset.mp he
    have hne : a ≠ b := hadj.ne
    by_cases hlt : a.val < b.val
    · exact ⟨a, b, hlt, hadj, rfl⟩
    · exact ⟨b, a, by omega, hadj.symm, Sym2.eq_swap⟩

private lemma addNonEdge_symm {cg : ℕ → ℕ → Bool} (hsym : ∀ i < 9, ∀ j < 9, cg i j = cg j i)
    (u v : ℕ) :
    ∀ i < 9, ∀ j < 9, addNonEdge cg u v i j = addNonEdge cg u v j i := by
  intro i hi j hj
  dsimp only [addNonEdge]
  rw [hsym i hi j hj]
  cases cg j i <;> cases i.beq u <;> cases j.beq v <;> cases i.beq v <;> cases j.beq u <;> rfl

private lemma addNonEdge_eq_false_iff {cg : ℕ → ℕ → Bool} {u v i j : ℕ} :
    addNonEdge cg u v i j = false ↔
      cg i j = false ∧ ¬ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) := by
  dsimp only [addNonEdge]
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff]
  tauto

private lemma addNonEdge_irrefl {cg : ℕ → ℕ → Bool} (hirr : ∀ i : Fin 9, cg i.val i.val = false)
    {u v : ℕ} (huv : u ≠ v) :
    ∀ i : Fin 9, addNonEdge cg u v i.val i.val = false := by
  intro i
  dsimp only [addNonEdge]
  rw [hirr i]
  by_cases hu : i.val = u
  · have hv : i.val.beq v = false := by
      cases h : i.val.beq v
      · rfl
      · exact absurd (hu.symm.trans ((beq_iff_eq _ _).mp h)) huv
    simp [hv]
  · have hu' : i.val.beq u = false := by
      cases h : i.val.beq u
      · rfl
      · exact absurd ((beq_iff_eq _ _).mp h) hu
    simp [hu']

private lemma host_spec {a : Fin 3} {cAdj : ℕ → ℕ → Bool} {wantB2 : Bool}
    (hcAdj_iff : ∀ i j : Fin 17, (hostC a).Adj i j ↔ cAdj i.val j.val = true)
    (hcert : dfs9 cAdj wantB2 17 0 9 0 [] = true)
    (f : Fin 9 ↪ Fin 17)
    (D : SimpleGraph (Fin 9)) [DecidableRel D.Adj]
    (hDle : D ≤ (hostC a)ᶜ.comap f)
    (hDe : 28 ≤ D.edgeFinset.card)
    (hDcf : D.CliqueFree 6) :
    (wantB2 = false → minDeg5 D ∧ ¬ isB2Sig D) ∧
    (wantB2 = true → minDeg5 D → isB2Sig D) := by
  classical
  have hsym17 : ∀ i < 17, ∀ j < 17, cAdj i j = cAdj j i := by
    intro i hi j hj
    have h1 := hcAdj_iff ⟨i, hi⟩ ⟨j, hj⟩
    have h2 := hcAdj_iff ⟨j, hj⟩ ⟨i, hi⟩
    cases hc1 : cAdj i j <;> cases hc2 : cAdj j i <;> simp_all [SimpleGraph.adj_comm]
  have hirr17 : ∀ i < 17, cAdj i i = false := by
    intro i hi
    have h1 := hcAdj_iff ⟨i, hi⟩ ⟨i, hi⟩
    cases hc : cAdj i i
    · rfl
    · exact absurd (h1.mpr hc) ((hostC a).loopless.irrefl ⟨i, hi⟩)
  let S : Finset (Fin 17) := Finset.univ.map f
  have hSc : S.card = 9 := by simp [S]
  let l_inc : List (Fin 17) := S.sort (· ≤ ·)
  have hl_len : l_inc.length = 9 := by simp [l_inc, hSc]
  let l_dec : List (Fin 17) := l_inc.reverse
  have hld_len : l_dec.length = 9 := by simp [l_dec, hl_len]
  have hld_nd : l_dec.Nodup := List.nodup_reverse.mpr (Finset.sort_nodup S (· ≤ ·))
  let g : Fin 9 ↪ Fin 17 :=
    ⟨fun i => l_dec[i.val]'(by omega), fun i j h => by
      have hinj := List.nodup_iff_injective_getElem.mp hld_nd
      have heq := hinj (a₁ := ⟨i.val, by omega⟩) (a₂ := ⟨j.val, by omega⟩) h
      exact Fin.ext (by simpa using congrArg Fin.val heq)⟩
  have hS_eq : ∀ i : Fin 9, ∃ j : Fin 9, g j = f i := by
    intro i
    have hmem : f i ∈ l_dec := by
      rw [List.mem_reverse, Finset.mem_sort]
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
    obtain ⟨idx, hidx, heq⟩ := List.mem_iff_getElem.mp hmem
    exact ⟨⟨idx, by omega⟩, heq⟩
  choose σ_fn hσ_fn using hS_eq
  have hσ_inj : Function.Injective σ_fn := fun i j h => by
    apply f.injective
    rw [← hσ_fn i, ← hσ_fn j, h]
  let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective σ_fn ((Finite.injective_iff_bijective).mp hσ_inj)
  have hf_eq : ∀ i, f i = g (σ i) := fun i => (hσ_fn i).symm
  let G : SimpleGraph (Fin 9) := (hostC a)ᶜ.comap g
  let H : SimpleGraph (Fin 9) := D.comap σ.symm
  let iso : H ≃g D := SimpleGraph.Iso.comap σ.symm D
  have hHle : H ≤ G := by
    intro u v huv
    have h1 : D.Adj (σ.symm u) (σ.symm v) := huv
    have h2 : (hostC a)ᶜ.Adj (f (σ.symm u)) (f (σ.symm v)) := hDle h1
    simpa [G, hf_eq] using h2
  have hHe : 28 ≤ H.edgeFinset.card := by
    rw [iso.card_edgeFinset_eq]; exact hDe
  have hHcf : H.CliqueFree 6 := (cliqueFree_iso iso).mpr hDcf
  let rest : List ℕ := l_inc.map Fin.val
  have hrest_len : rest.length = 9 := by simp [rest, hl_len]
  have hrest_pw : rest.Pairwise (· < ·) := by
    have hp := Finset.pairwise_sort S (· ≤ ·)
    have hnd := Finset.sort_nodup S (· ≤ ·)
    exact List.pairwise_map.mpr ((hp.and hnd).imp (fun h => Fin.lt_def.mp (lt_of_le_of_ne h.1 h.2)))
  have hrest_range : ∀ x ∈ rest, 0 ≤ x ∧ x < 17 := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨Nat.zero_le _, v.isLt⟩
  let vs : List ℕ := rest.reverse
  have hvs_eq : vs = l_dec.map Fin.val := by simp [vs, rest, l_dec, List.map_reverse]
  have hvs_len : vs.length = 9 := by simp [vs, hrest_len]
  have hvs_get : ∀ i : Fin 9, vs[i.val]'(by omega) = (g i).val := by
    intro i
    simp only [hvs_eq, List.getElem_map]
    rfl
  match hvs_match : vs with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8] =>
    let vAt (i : ℕ) : ℕ :=
      if i.ble 4 then
        if i.ble 2 then (if i.ble 1 then (if i.ble 0 then v0 else v1) else v2)
        else (if i.ble 3 then v3 else v4)
      else
        if i.ble 6 then (if i.ble 5 then v5 else v6)
        else (if i.ble 7 then v7 else v8)
    have hvAt_eq : ∀ i : Fin 9, vAt i.val = (g i).val := by
      intro i
      have hgi : vs.getD i.val 0 = (g i).val := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact hvs_get i
      rw [hvs_match] at hgi
      fin_cases i <;> simpa [vAt] using hgi
    let cg (i j : ℕ) : Bool := cAdj (vAt i) (vAt j)
    have hcg_sym : ∀ i < 9, ∀ j < 9, cg i j = cg j i := by
      intro i hi j hj
      dsimp only [cg]
      rw [hvAt_eq ⟨i, hi⟩, hvAt_eq ⟨j, hj⟩]
      exact hsym17 _ (g ⟨i, hi⟩).isLt _ (g ⟨j, hj⟩).isLt
    have hcg_irr : ∀ i : Fin 9, cg i.val i.val = false := by
      intro i
      dsimp only [cg]
      rw [hvAt_eq i]
      exact hirr17 _ (g i).isLt
    have hcg_adj : ∀ i j : Fin 9, G.Adj i j ↔ i ≠ j ∧ cg i.val j.val = false := by
      intro i j
      simp only [G, SimpleGraph.comap_adj, SimpleGraph.compl_adj, cg, hvAt_eq]
      constructor
      · rintro ⟨hne, hnot⟩
        refine ⟨fun h => hne (congrArg g h), ?_⟩
        rw [hcAdj_iff] at hnot
        cases hc : cAdj (g i).val (g j).val
        · rfl
        · exact absurd hc hnot
      · rintro ⟨hne, hf⟩
        refine ⟨fun h => hne (g.injective h), ?_⟩
        rw [hcAdj_iff, hf]
        simp
    have hvs_lt : ∀ x ∈ vs, x < 17 := by
      intro x hx
      rw [hvs_eq] at hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
      exact v.isLt
    have hpair_eq : G.edgeFinset.card + pairCount cAdj vs = 36 := by
      have h2p := two_mul_pairCount hsym17 hirr17 vs hvs_lt
      have hsum_deg : ∑ i : Fin 9, G.degree i + ∑ i : Fin 9, countLt 9 (cg i.val) = 72 := by
        rw [← Finset.sum_add_distrib]
        have h8 : ∀ i : Fin 9, G.degree i + countLt 9 (cg i.val) = 8 :=
          deg_add_cdeg hcg_adj hcg_irr
        simp [h8]
      have hsum_cg : ∑ i : Fin 9, countLt 9 (cg i.val) = 2 * pairCount cAdj vs := by
        rw [h2p]
        symm
        rw [← (finCongr hvs_len.symm).sum_comp]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← (finCongr hvs_len.symm).sum_comp, countLt_eq_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [finCongr_apply, Fin.val_cast, cg, hvAt_eq, hvs_get]
      have hhand := G.sum_degrees_eq_twice_card_edges
      omega
    have hGe : 28 ≤ G.edgeFinset.card :=
      hHe.trans (Finset.card_le_card (SimpleGraph.edgeFinset_mono hHle))
    have hnon_le8 : pairCount cAdj vs ≤ 8 := by omega
    have hleaf : checkLeaf cAdj wantB2 (pairCount cAdj vs) vs = true := by
      have h := dfs9_sound 17 0 9 0 [] hcert rfl rest hrest_len hrest_pw hrest_range (by simpa [vs] using hnon_le8)
      simpa [vs] using h
    rw [hvs_match] at hleaf
    dsimp only [checkLeaf] at hleaf
    have hG_deg_ge : ∀ (hmdD : minDeg5 D), ∀ i : Fin 9, (countLt 9 (cg i.val)).ble 3 = true := by
      intro hmdD i
      have hmdH : minDeg5 H := (minDeg5_iso iso).mpr hmdD
      have hle : H.degree i ≤ G.degree i := by
        refine Finset.card_le_card fun j hj => ?_
        rw [SimpleGraph.mem_neighborFinset] at hj ⊢
        exact hHle hj
      have := deg_add_cdeg hcg_adj hcg_irr i
      have := hmdH i
      exact (ble_iff_le _ _).mpr (by omega)
    have finish (hnot_skip : (wantB2 && !(forallLt 9 (fun i => (countLt 9 (cg i)).ble 3))) = false) :
        (wantB2 = false → minDeg5 H ∧ ¬ isB2Sig H) ∧
        (wantB2 = true → minDeg5 H → isB2Sig H) := by
      dsimp only [cg, vAt] at hnot_skip
      rw [hnot_skip] at hleaf
      simp only [Bool.false_eq_true, ↓reduceIte] at hleaf
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hleaf
      obtain ⟨⟨⟨h6le, hGK6⟩, hdel1⟩, hdel2⟩ := hleaf
      rw [← hvs_match] at h6le hdel1 hdel2
      have hnon_ge6 : 6 ≤ pairCount cAdj vs := (ble_iff_le _ _).mp h6le
      have hGe_le30 : G.edgeFinset.card ≤ 30 := by omega
      have hH_ne_G : H.edgeFinset ≠ G.edgeFinset := by
        intro heq
        have hHG : H = G := SimpleGraph.edgeFinset_inj.mp heq
        exact cliqueFree_of_hasIndepAux_true hcg_sym hcg_adj hGK6 (hHG ▸ hHcf)
      have hsub : H.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hHle
      have hdiff_add := Finset.card_sdiff_add_card_eq_card hsub
      have hdiff_pos : 0 < (G.edgeFinset \ H.edgeFinset).card := by
        by_contra h0
        have he0 : G.edgeFinset \ H.edgeFinset = ∅ := Finset.card_eq_zero.mp (by omega)
        exact hH_ne_G (Finset.Subset.antisymm hsub (Finset.sdiff_eq_empty_iff_subset.mp he0))
      have hdiff_le2 : (G.edgeFinset \ H.edgeFinset).card ≤ 2 := by omega
      by_cases hd1 : (G.edgeFinset \ H.edgeFinset).card = 1
      · obtain ⟨e, he_eq⟩ := Finset.card_eq_one.mp hd1
        have heG : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp (he_eq ▸ Finset.mem_singleton_self e)).1
        obtain ⟨u, v, huv_lt, huv_adj, rfl⟩ := edge_to_ordered_pair heG
        have hnon7 : (pairCount cAdj vs).ble 7 = true := (ble_iff_le _ _).mpr (by omega)
        simp only [hnon7, ↓reduceIte] at hdel1
        have hcg_uv : cg u.val v.val = false := ((hcg_adj u v).mp huv_adj).2
        have hok1 := forallLt_eq_true (forallLt_eq_true hdel1 u.val u.isLt) v.val v.isLt
        have hcond1 : (u.val.ble v.val && !(u.val.beq v.val) && !(cg u.val v.val)) = true := by
          simp only [Bool.and_eq_true, Bool.not_eq_true', ble_iff_le, beq_eq_false_iff, hcg_uv, and_true]
          exact ⟨by omega, by omega⟩
        dsimp only [cg, vAt] at hcond1
        simp only [hcond1, ↓reduceIte] at hok1
        have hch : ∀ i j : Fin 9, H.Adj i j ↔ i ≠ j ∧ addNonEdge cg u.val v.val i.val j.val = false := by
          intro i j
          rw [addNonEdge_eq_false_iff]
          have hmem_sdiff : s(i, j) ∈ G.edgeFinset \ H.edgeFinset ↔ s(i, j) = s(u, v) := by
            rw [he_eq, Finset.mem_singleton]
          constructor
          · intro hij
            have hGij : G.Adj i j := hHle hij
            have hne : s(i, j) ≠ s(u, v) := fun hs =>
              (Finset.mem_sdiff.mp (hmem_sdiff.mpr hs)).2 (SimpleGraph.mem_edgeFinset.mpr hij)
            refine ⟨hij.ne, ((hcg_adj i j).mp hGij).2, ?_⟩
            rintro (⟨hi, hj⟩ | ⟨hi, hj⟩)
            · exact hne (by rw [Fin.ext hi, Fin.ext hj])
            · exact hne (by rw [Fin.ext hi, Fin.ext hj]; exact Sym2.eq_swap)
          · rintro ⟨hne, hcgf, hpair⟩
            have hGij : G.Adj i j := (hcg_adj i j).mpr ⟨hne, hcgf⟩
            by_contra hnotH
            have hseq : s(i, j) = s(u, v) := hmem_sdiff.mp
              (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hGij,
                fun hm => hnotH (SimpleGraph.mem_edgeFinset.mp hm)⟩)
            rw [Sym2.eq_iff] at hseq
            rcases hseq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hpair (Or.inl ⟨rfl, rfl⟩)
            · exact hpair (Or.inr ⟨rfl, rfl⟩)
        exact evalSub_sound (addNonEdge_symm hcg_sym u.val v.val)
          (addNonEdge_irrefl hcg_irr (by omega)) hch hHcf hok1
      · have hd2 : (G.edgeFinset \ H.edgeFinset).card = 2 := by omega
        obtain ⟨e₁, e₂, he12, he_eq⟩ := Finset.card_eq_two.mp hd2
        have he₁G : e₁ ∈ G.edgeFinset := (Finset.mem_sdiff.mp (by rw [he_eq]; simp)).1
        have he₂G : e₂ ∈ G.edgeFinset := (Finset.mem_sdiff.mp (by rw [he_eq]; simp)).1
        obtain ⟨a₁, b₁, hab1, hadj1, rfl⟩ := edge_to_ordered_pair he₁G
        obtain ⟨a₂, b₂, hab2, hadj2, rfl⟩ := edge_to_ordered_pair he₂G
        have hpair_ne : (a₁.val, b₁.val) ≠ (a₂.val, b₂.val) := by
          intro h
          have ha : a₁ = a₂ := Fin.ext (congrArg Prod.fst h)
          have hb : b₁ = b₂ := Fin.ext (congrArg Prod.snd h)
          exact he12 (by rw [ha, hb])
        obtain ⟨u₁, v₁, u₂, v₂, huv1, huv2, hlex, hG1, hG2, hset_eq⟩ :
            ∃ u₁ v₁ u₂ v₂ : Fin 9, u₁.val < v₁.val ∧ u₂.val < v₂.val ∧
              (u₁.val < u₂.val ∨ (u₁.val = u₂.val ∧ v₁.val < v₂.val)) ∧
              G.Adj u₁ v₁ ∧ G.Adj u₂ v₂ ∧
              G.edgeFinset \ H.edgeFinset = {s(u₁, v₁), s(u₂, v₂)} := by
          by_cases hord : a₁.val < a₂.val ∨ (a₁.val = a₂.val ∧ b₁.val < b₂.val)
          · exact ⟨a₁, b₁, a₂, b₂, hab1, hab2, hord, hadj1, hadj2, he_eq⟩
          · refine ⟨a₂, b₂, a₁, b₁, hab2, hab1, ?_, hadj2, hadj1, by rw [he_eq, Finset.pair_comm]⟩
            by_cases hae : a₁.val = a₂.val
            · right; refine ⟨hae.symm, ?_⟩
              have hbe : b₁.val ≠ b₂.val := fun hb => hpair_ne (Prod.ext hae hb)
              omega
            · left; omega
        have hnon6 : (pairCount cAdj vs).ble 6 = true := (ble_iff_le _ _).mpr (by omega)
        simp only [hnon6, ↓reduceIte] at hdel2
        have hcg1 : cg u₁.val v₁.val = false := ((hcg_adj u₁ v₁).mp hG1).2
        have hcg2 : cg u₂.val v₂.val = false := ((hcg_adj u₂ v₂).mp hG2).2
        have hok1 := forallLt_eq_true (forallLt_eq_true hdel2 u₁.val u₁.isLt) v₁.val v₁.isLt
        have hcond1 : (u₁.val.ble v₁.val && !(u₁.val.beq v₁.val) && !(cg u₁.val v₁.val)) = true := by
          simp only [Bool.and_eq_true, Bool.not_eq_true', ble_iff_le, beq_eq_false_iff, hcg1, and_true]
          exact ⟨by omega, by omega⟩
        dsimp only [cg, vAt] at hcond1
        simp only [hcond1, ↓reduceIte] at hok1
        have hok2 := forallLt_eq_true (forallLt_eq_true hok1 u₂.val u₂.isLt) v₂.val v₂.isLt
        have hcond2 : (u₂.val.ble v₂.val && !(u₂.val.beq v₂.val) &&
            ((u₁.val.ble u₂.val && !(u₁.val.beq u₂.val)) ||
             (u₁.val.beq u₂.val && v₁.val.ble v₂.val && !(v₁.val.beq v₂.val))) &&
            !(cg u₂.val v₂.val)) = true := by
          simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
            ble_iff_le, beq_iff_eq, beq_eq_false_iff, hcg2, and_true]
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          rcases hlex with hlt | ⟨heq, hlt⟩
          · left; exact ⟨by omega, by omega⟩
          · right; exact ⟨⟨heq, by omega⟩, by omega⟩
        dsimp only [cg, vAt] at hcond2
        simp only [hcond2, ↓reduceIte] at hok2
        let ch := addNonEdge (addNonEdge cg u₁.val v₁.val) u₂.val v₂.val
        have hch : ∀ i j : Fin 9, H.Adj i j ↔ i ≠ j ∧ ch i.val j.val = false := by
          intro i j
          dsimp only [ch]
          rw [addNonEdge_eq_false_iff, addNonEdge_eq_false_iff]
          have hmem_sdiff : s(i, j) ∈ G.edgeFinset \ H.edgeFinset ↔
              s(i, j) = s(u₁, v₁) ∨ s(i, j) = s(u₂, v₂) := by
            rw [hset_eq, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · intro hij
            have hGij : G.Adj i j := hHle hij
            have hne1 : s(i, j) ≠ s(u₁, v₁) := fun hs =>
              (Finset.mem_sdiff.mp (hmem_sdiff.mpr (Or.inl hs))).2 (SimpleGraph.mem_edgeFinset.mpr hij)
            have hne2 : s(i, j) ≠ s(u₂, v₂) := fun hs =>
              (Finset.mem_sdiff.mp (hmem_sdiff.mpr (Or.inr hs))).2 (SimpleGraph.mem_edgeFinset.mpr hij)
            refine ⟨hij.ne, ⟨((hcg_adj i j).mp hGij).2, ?_⟩, ?_⟩
            · rintro (⟨hi, hj⟩ | ⟨hi, hj⟩)
              · exact hne1 (by rw [Fin.ext hi, Fin.ext hj])
              · exact hne1 (by rw [Fin.ext hi, Fin.ext hj]; exact Sym2.eq_swap)
            · rintro (⟨hi, hj⟩ | ⟨hi, hj⟩)
              · exact hne2 (by rw [Fin.ext hi, Fin.ext hj])
              · exact hne2 (by rw [Fin.ext hi, Fin.ext hj]; exact Sym2.eq_swap)
          · rintro ⟨hne, ⟨hcgf, hpair1⟩, hpair2⟩
            have hGij : G.Adj i j := (hcg_adj i j).mpr ⟨hne, hcgf⟩
            by_contra hnotH
            have hin : s(i, j) ∈ G.edgeFinset \ H.edgeFinset :=
              Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hGij,
                fun hm => hnotH (SimpleGraph.mem_edgeFinset.mp hm)⟩
            rcases hmem_sdiff.mp hin with hs1 | hs2
            · rw [Sym2.eq_iff] at hs1
              rcases hs1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hpair1 (Or.inl ⟨rfl, rfl⟩)
              · exact hpair1 (Or.inr ⟨rfl, rfl⟩)
            · rw [Sym2.eq_iff] at hs2
              rcases hs2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact hpair2 (Or.inl ⟨rfl, rfl⟩)
              · exact hpair2 (Or.inr ⟨rfl, rfl⟩)
        exact evalSub_sound (addNonEdge_symm (addNonEdge_symm hcg_sym u₁.val v₁.val) u₂.val v₂.val)
          (addNonEdge_irrefl (addNonEdge_irrefl hcg_irr (by omega)) (by omega)) hch hHcf hok2
    constructor
    · intro hw
      have hres := (finish (by simp [hw])).1 hw
      exact ⟨(minDeg5_iso iso).mp hres.1, fun h => hres.2 ((isB2Sig_iso iso).mpr h)⟩
    · intro hw hmdD
      have hall_le3 : forallLt 9 (fun i => (countLt 9 (cg i)).ble 3) = true := by
        have hforall : ∀ i < 9, (countLt 9 (cg i)).ble 3 = true := fun i hi =>
          hG_deg_ge hmdD ⟨i, hi⟩
        have aux : ∀ n ≤ 9, forallLt n (fun i => (countLt 9 (cg i)).ble 3) = true := by
          intro n hn
          induction n with
          | zero => rfl
          | succ k ih =>
            simp only [forallLt, Bool.and_eq_true]
            exact ⟨hforall k (by omega), ih (by omega)⟩
        exact aux 9 le_rfl
      have hres := (finish (by simp [hw, hall_le3])).2 hw ((minDeg5_iso iso).mpr hmdD)
      exact (isB2Sig_iso iso).mp hres
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | [_, _, _, _, _] | [_, _, _, _, _, _]
  | [_, _, _, _, _, _, _] | [_, _, _, _, _, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
    rw [hvs_match] at hvs_len
    simp at hvs_len

end Erdos1182H2

theorem Erdos1182H2.main_H2 : SmallValuesR2.Bound2 := by
  classical
  dsimp only [SmallValuesR2.Bound2]
  intro f _
  by_contra hlt
  change ¬ (⨅ a, (Erdos1182H2.hostC a)ᶜ.comap (f a)).edgeSet.ncard ≤ 27 at hlt
  set D := ⨅ a, (Erdos1182H2.hostC a)ᶜ.comap (f a)
  have hDe : 28 ≤ D.edgeFinset.card := by
    have hnc : D.edgeSet.ncard = D.edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card]
      congr 1
      ext x
      simp [SimpleGraph.edgeFinset]
    omega
  have hD0 : D ≤ (Erdos1182H2.hostC 0)ᶜ.comap (f 0) := iInf_le _ 0
  have hD1 : D ≤ (Erdos1182H2.hostC 1)ᶜ.comap (f 1) := iInf_le _ 1
  have hD2 : D ≤ (Erdos1182H2.hostC 2)ᶜ.comap (f 2) := iInf_le _ 2
  have hDcf : D.CliqueFree 6 := by
    intro S ⟨hScl, hSc⟩
    refine Erdos1182H2.b1_cliqueFree_six (S.map (f 1)) ⟨?_, by simp [hSc]⟩
    intro x hx y hy hne
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    exact hD1 (hScl hu hv (fun h => hne (congrArg (f 1) h)))
  have h0 := (Erdos1182H2.host_spec Erdos1182H2.c0Adj_iff
    Erdos1182H2.cert_b0_dense (f 0) D hD0 hDe hDcf).1 rfl
  have h2 := (Erdos1182H2.host_spec Erdos1182H2.c2Adj_iff
    Erdos1182H2.cert_b2_dense (f 2) D hD2 hDe hDcf).2 rfl h0.1
  exact h0.2 h2

theorem OMA.solution : OMA.R_Erdos1182_erdos_1182_variants_small_values_R2.H3 := by
  exact ⟨Erdos1182H1.main_H1, Erdos1182H2.main_H2⟩
