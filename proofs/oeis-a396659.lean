import OMAStatements.S_oeis_a396659
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

namespace OMA.P_oeis_a396659

open OMA.S_oeis_a396659

/-- An Eulerian circuit on the complete directed graph with self-loops on `Fin n` starting at `0`. -/
private def IsEulerCircuit (n : ℕ) (hn : 0 < n) (c : Fin (n ^ 2) → Fin n × Fin n) : Prop :=
  (c ⟨0, by nlinarith⟩).1 = ⟨0, hn⟩ ∧
  (∀ i : Fin (n ^ 2), (hi : i.val + 1 < n ^ 2) → (c i).2 = (c ⟨i.val + 1, hi⟩).1) ∧
  Function.Injective c

/-- An Eulerian trail of length `n^2 - 1` starting at `0` that omits only the self-loop `(u, u)`. -/
private def IsCircuitWithoutLoop (n : ℕ) (hn : 0 < n) (u : Fin n)
    (p : Fin (n ^ 2 - 1) → Fin n × Fin n) : Prop :=
  (∀ h0 : 0 < n ^ 2 - 1, (p ⟨0, h0⟩).1 = ⟨0, hn⟩) ∧
  (∀ i : Fin (n ^ 2 - 1), (hi : i.val + 1 < n ^ 2 - 1) → (p i).2 = (p ⟨i.val + 1, hi⟩).1) ∧
  Function.Injective p ∧
  (∀ i : Fin (n ^ 2 - 1), p i ≠ (u, u))

/-- Degree balance along any directed walk `p : Fin m → Fin n × Fin n` (`m ≥ 1`). -/
private lemma walk_degree_balance {n m : ℕ} (hm : 1 ≤ m) (p : Fin m → Fin n × Fin n)
    (hchain : ∀ i : Fin m, (hi : i.val + 1 < m) → (p i).2 = (p ⟨i.val + 1, hi⟩).1)
    (x : Fin n) :
    ((Finset.univ.filter fun i : Fin m => (p i).1 = x).card : ℤ) -
    ((Finset.univ.filter fun i : Fin m => (p i).2 = x).card : ℤ) =
    (if (p ⟨0, by omega⟩).1 = x then (1 : ℤ) else 0) -
    (if (p ⟨m - 1, by omega⟩).2 = x then (1 : ℤ) else 0) := by
  have hcard1 : ((Finset.univ.filter fun i : Fin m => (p i).1 = x).card : ℤ) =
      ∑ i : Fin m, if (p i).1 = x then (1 : ℤ) else 0 := by
    simp [Finset.sum_boole]
  have hcard2 : ((Finset.univ.filter fun i : Fin m => (p i).2 = x).card : ℤ) =
      ∑ i : Fin m, if (p i).2 = x then (1 : ℤ) else 0 := by
    simp [Finset.sum_boole]
  rw [hcard1, hcard2, ← Finset.sum_sub_distrib]
  -- Convert Fin m sum to Finset.range m sum and telescope
  have hrange : ∀ (f : Fin m → ℤ), ∑ i : Fin m, f i =
      ∑ k ∈ Finset.range m, if hk : k < m then f ⟨k, hk⟩ else 0 := by
    intro f
    calc ∑ i : Fin m, f i = ∑ i : Fin m, (if hk : i.val < m then f ⟨i.val, hk⟩ else 0) :=
          Finset.sum_congr rfl fun i _ => by simp [i.isLt]
      _ = ∑ k ∈ Finset.range m, if hk : k < m then f ⟨k, hk⟩ else 0 :=
          Fin.sum_univ_eq_sum_range (fun k => if hk : k < m then f ⟨k, hk⟩ else 0) m
  let g : ℕ → ℤ := fun k =>
    if hk : k < m then (if (p ⟨k, hk⟩).1 = x then 1 else 0)
    else if (p ⟨m - 1, by omega⟩).2 = x then 1 else 0
  have hterm : ∀ k ∈ Finset.range m,
      (if hk : k < m then
        ((if (p ⟨k, hk⟩).1 = x then (1 : ℤ) else 0) - (if (p ⟨k, hk⟩).2 = x then (1 : ℤ) else 0))
       else 0) = g k - g (k + 1) := by
    intro k hk
    have hkm : k < m := Finset.mem_range.mp hk
    rw [dif_pos hkm]
    dsimp only [g]
    rw [dif_pos hkm]
    by_cases hk1 : k + 1 < m
    · rw [dif_pos hk1, hchain ⟨k, hkm⟩ hk1]
    · rw [dif_neg hk1]
      have hkeq : k = m - 1 := by omega
      subst hkeq
      rfl
  rw [hrange, Finset.sum_congr rfl hterm, Finset.sum_range_sub']
  dsimp only [g]
  rw [dif_pos (by omega : 0 < m), dif_neg (by omega : ¬ m < m)]

private lemma euler_bijective {n : ℕ} {hn : 0 < n} {c : Fin (n ^ 2) → Fin n × Fin n}
    (hc : IsEulerCircuit n hn c) : Function.Bijective c := by
  refine (Fintype.bijective_iff_injective_and_card c).mpr ⟨hc.2.2, ?_⟩
  simp [sq]

private lemma euler_end {n : ℕ} {hn : 0 < n} {c : Fin (n ^ 2) → Fin n × Fin n}
    (hc : IsEulerCircuit n hn c) :
    (c ⟨n ^ 2 - 1, Nat.sub_lt (by nlinarith) Nat.one_pos⟩).2 = ⟨0, hn⟩ := by
  have hbij := euler_bijective hc
  have hbal := walk_degree_balance (by nlinarith : 1 ≤ n ^ 2) c hc.2.1 ⟨0, hn⟩
  have h1 : (Finset.univ.filter fun i : Fin (n ^ 2) => (c i).1 = ⟨0, hn⟩).card =
      (Finset.univ.filter fun e : Fin n × Fin n => e.1 = ⟨0, hn⟩).card := by
    refine Finset.card_bij (fun i _ => c i) ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi
    · intro i _ j _ h; exact hc.2.2 h
    · intro e he
      obtain ⟨i, rfl⟩ := hbij.2 e
      exact ⟨i, by simpa using he, rfl⟩
  have h2 : (Finset.univ.filter fun i : Fin (n ^ 2) => (c i).2 = ⟨0, hn⟩).card =
      (Finset.univ.filter fun e : Fin n × Fin n => e.2 = ⟨0, hn⟩).card := by
    refine Finset.card_bij (fun i _ => c i) ?_ ?_ ?_
    · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi
    · intro i _ j _ h; exact hc.2.2 h
    · intro e he
      obtain ⟨i, rfl⟩ := hbij.2 e
      exact ⟨i, by simpa using he, rfl⟩
  have h1c : (Finset.univ.filter fun e : Fin n × Fin n => e.1 = ⟨0, hn⟩).card = n := by
    have : (Finset.univ.filter fun e : Fin n × Fin n => e.1 = ⟨0, hn⟩) =
        Finset.univ.image (fun y : Fin n => ((⟨0, hn⟩ : Fin n), y)) := by
      ext ⟨a, b⟩; simp [eq_comm]
    rw [this, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Finset.card_fin]
  have h2c : (Finset.univ.filter fun e : Fin n × Fin n => e.2 = ⟨0, hn⟩).card = n := by
    have : (Finset.univ.filter fun e : Fin n × Fin n => e.2 = ⟨0, hn⟩) =
        Finset.univ.image (fun x : Fin n => (x, (⟨0, hn⟩ : Fin n))) := by
      ext ⟨a, b⟩; simp [eq_comm]
    rw [this, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Finset.card_fin]
  rw [h1, h2, h1c, h2c, sub_self, hc.1, if_pos rfl] at hbal
  by_contra hne
  rw [if_neg hne] at hbal
  norm_num at hbal

/-- Splice detours `(b', last), (last, b')` into a list of edges on `Fin n` at the first arrival
at each vertex `b ∉ seen`. -/
private def spliceEdges {n : ℕ} : Finset (Fin n) → List (Fin n × Fin n) →
    List (Fin (n + 1) × Fin (n + 1))
  | _, [] => []
  | seen, (a, b) :: rest =>
    if b ∈ seen then
      (a.castSucc, b.castSucc) :: spliceEdges seen rest
    else
      (a.castSucc, b.castSucc) :: (b.castSucc, Fin.last n) :: (Fin.last n, b.castSucc) ::
        spliceEdges (insert b seen) rest

private lemma spliceEdges_mem {n : ℕ} (seen : Finset (Fin n)) (xs : List (Fin n × Fin n))
    (e : Fin (n + 1) × Fin (n + 1)) :
    e ∈ spliceEdges seen xs ↔
      (∃ a b : Fin n, (a, b) ∈ xs ∧ e = (a.castSucc, b.castSucc)) ∨
      (∃ b : Fin n, b ∉ seen ∧ (∃ a : Fin n, (a, b) ∈ xs) ∧
        (e = (b.castSucc, Fin.last n) ∨ e = (Fin.last n, b.castSucc))) := by
  induction xs generalizing seen with
  | nil => simp [spliceEdges]
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    dsimp only [spliceEdges]
    split_ifs with hb
    · rw [List.mem_cons, ih seen]
      constructor
      · rintro (rfl | ⟨a', b', hmem, rfl⟩ | ⟨b', hb', ⟨a', hmem⟩, hcase⟩)
        · exact Or.inl ⟨a, b, List.mem_cons_self .., rfl⟩
        · exact Or.inl ⟨a', b', List.mem_cons_of_mem _ hmem, rfl⟩
        · exact Or.inr ⟨b', hb', ⟨a', List.mem_cons_of_mem _ hmem⟩, hcase⟩
      · rintro (⟨a', b', hmem, rfl⟩ | ⟨b', hb', ⟨a', hmem⟩, hcase⟩)
        · rcases List.mem_cons.mp hmem with h | h
          · cases h; exact Or.inl rfl
          · exact Or.inr (Or.inl ⟨a', b', h, rfl⟩)
        · rcases List.mem_cons.mp hmem with h | h
          · cases h; exact absurd hb hb'
          · exact Or.inr (Or.inr ⟨b', hb', ⟨a', h⟩, hcase⟩)
    · rw [List.mem_cons, List.mem_cons, List.mem_cons, ih (insert b seen)]
      constructor
      · rintro (rfl | rfl | rfl | ⟨a', b', hmem, rfl⟩ | ⟨b', hb', ⟨a', hmem⟩, hcase⟩)
        · exact Or.inl ⟨a, b, List.mem_cons_self .., rfl⟩
        · exact Or.inr ⟨b, hb, ⟨a, List.mem_cons_self ..⟩, Or.inl rfl⟩
        · exact Or.inr ⟨b, hb, ⟨a, List.mem_cons_self ..⟩, Or.inr rfl⟩
        · exact Or.inl ⟨a', b', List.mem_cons_of_mem _ hmem, rfl⟩
        · simp only [Finset.mem_insert, not_or] at hb'
          exact Or.inr ⟨b', hb'.2, ⟨a', List.mem_cons_of_mem _ hmem⟩, hcase⟩
      · rintro (⟨a', b', hmem, rfl⟩ | ⟨b', hb', ⟨a', hmem⟩, hcase⟩)
        · rcases List.mem_cons.mp hmem with h | h
          · cases h; exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a', b', h, rfl⟩)))
        · by_cases hbb : b' = b
          · subst hbb
            rcases hcase with rfl | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl rfl))
          · rcases List.mem_cons.mp hmem with h | h
            · cases h; exact absurd rfl hbb
            · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨b', by simp [hbb, hb'], ⟨a', h⟩, hcase⟩)))

private lemma spliceEdges_nodup {n : ℕ} (seen : Finset (Fin n)) (xs : List (Fin n × Fin n))
    (hnd : xs.Nodup) : (spliceEdges seen xs).Nodup := by
  induction xs generalizing seen with
  | nil => simp [spliceEdges]
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    rw [List.nodup_cons] at hnd
    dsimp only [spliceEdges]
    split_ifs with hb
    · rw [List.nodup_cons]
      refine ⟨?_, ih seen hnd.2⟩
      rw [spliceEdges_mem]
      rintro (⟨a', b', hmem, heq⟩ | ⟨b', _, _, heq | heq⟩)
      · rcases Prod.mk.inj heq with ⟨ha, hb'⟩
        have := Fin.castSucc_injective n ha
        have := Fin.castSucc_injective n hb'
        subst_vars; exact hnd.1 hmem
      · exact Fin.castSucc_ne_last b (Prod.mk.inj heq).2
      · exact Fin.castSucc_ne_last a (Prod.mk.inj heq).1
    · have ih' := ih (insert b seen) hnd.2
      have hne3 : (Fin.last n, b.castSucc) ∉ spliceEdges (insert b seen) tl := by
        rw [spliceEdges_mem]
        rintro (⟨a', b', _, heq⟩ | ⟨b', hb', _, heq | heq⟩)
        · exact Fin.castSucc_ne_last a' (Prod.mk.inj heq).1.symm
        · exact Fin.castSucc_ne_last b' (Prod.mk.inj heq).1.symm
        · have : b = b' := Fin.castSucc_injective n (Prod.mk.inj heq).2
          subst this; exact hb' (Finset.mem_insert_self b seen)
      have hne2 : (b.castSucc, Fin.last n) ∉ (Fin.last n, b.castSucc) :: spliceEdges (insert b seen) tl := by
        rw [List.mem_cons]
        rintro (heq | hmem)
        · exact Fin.castSucc_ne_last b (Prod.mk.inj heq).1
        · rw [spliceEdges_mem] at hmem
          rcases hmem with ⟨a', b', _, heq⟩ | ⟨b', hb', _, heq | heq⟩
          · exact Fin.castSucc_ne_last b' (Prod.mk.inj heq).2.symm
          · have : b = b' := Fin.castSucc_injective n (Prod.mk.inj heq).1
            subst this; exact hb' (Finset.mem_insert_self b seen)
          · exact Fin.castSucc_ne_last b (Prod.mk.inj heq).1
      have hne1 : (a.castSucc, b.castSucc) ∉
          (b.castSucc, Fin.last n) :: (Fin.last n, b.castSucc) :: spliceEdges (insert b seen) tl := by
        rw [List.mem_cons, List.mem_cons]
        rintro (heq | heq | hmem)
        · exact Fin.castSucc_ne_last b (Prod.mk.inj heq).2
        · exact Fin.castSucc_ne_last a (Prod.mk.inj heq).1
        · rw [spliceEdges_mem] at hmem
          rcases hmem with ⟨a', b', hmem', heq⟩ | ⟨b', _, _, heq | heq⟩
          · rcases Prod.mk.inj heq with ⟨ha, hb'⟩
            have := Fin.castSucc_injective n ha
            have := Fin.castSucc_injective n hb'
            subst_vars; exact hnd.1 hmem'
          · exact Fin.castSucc_ne_last b (Prod.mk.inj heq).2
          · exact Fin.castSucc_ne_last a (Prod.mk.inj heq).1
      exact List.nodup_cons.mpr ⟨hne1, List.nodup_cons.mpr ⟨hne2, List.nodup_cons.mpr ⟨hne3, ih'⟩⟩⟩

private lemma spliceEdges_chain {n : ℕ} (seen : Finset (Fin n)) (xs : List (Fin n × Fin n))
    (hch : xs.IsChain (fun e1 e2 => e1.2 = e2.1)) :
    (spliceEdges seen xs).IsChain (fun e1 e2 => e1.2 = e2.1) ∧
    (∀ (hxs : xs ≠ []), ∃ (hs : spliceEdges seen xs ≠ []),
      ((spliceEdges seen xs).head hs).1 = ((xs.head hxs).1).castSucc) := by
  induction xs generalizing seen with
  | nil => simp [spliceEdges]
  | cons hd tl ih =>
    rcases hd with ⟨a, b⟩
    dsimp only [spliceEdges]
    cases tl with
    | nil =>
      split_ifs with hb
      · refine ⟨List.isChain_singleton _, fun _ => ⟨List.cons_ne_nil _ _, rfl⟩⟩
      · refine ⟨?_, fun _ => ⟨List.cons_ne_nil _ _, rfl⟩⟩
        simp [spliceEdges, List.isChain_cons_cons]
    | cons hd2 tl2 =>
      rw [List.isChain_cons_cons] at hch
      have hch_tl : (hd2 :: tl2).IsChain (fun e1 e2 => e1.2 = e2.1) := hch.2
      have hlink : b = hd2.1 := hch.1
      split_ifs with hb
      · obtain ⟨hc, hh⟩ := ih seen hch_tl
        obtain ⟨hs, hhead⟩ := hh (List.cons_ne_nil _ _)
        cases hsp : spliceEdges seen (hd2 :: tl2) with
        | nil => exact absurd hsp hs
        | cons u us =>
          rw [hsp] at hc
          have hhead' : u.1 = hd2.1.castSucc := by
            revert hs hhead
            rw [hsp]
            intro _ h
            exact h
          refine ⟨List.isChain_cons_cons.mpr ⟨by rw [hhead', hlink], hc⟩,
            fun _ => ⟨List.cons_ne_nil _ _, rfl⟩⟩
      · obtain ⟨hc, hh⟩ := ih (insert b seen) hch_tl
        obtain ⟨hs, hhead⟩ := hh (List.cons_ne_nil _ _)
        cases hsp : spliceEdges (insert b seen) (hd2 :: tl2) with
        | nil => exact absurd hsp hs
        | cons u us =>
          rw [hsp] at hc
          have hhead' : u.1 = hd2.1.castSucc := by
            revert hs hhead
            rw [hsp]
            intro _ h
            exact h
          refine ⟨?_, fun _ => ⟨List.cons_ne_nil _ _, rfl⟩⟩
          exact List.isChain_cons_cons.mpr ⟨rfl,
            List.isChain_cons_cons.mpr ⟨rfl,
              List.isChain_cons_cons.mpr ⟨by rw [hhead', hlink], hc⟩⟩⟩

private lemma exists_euler_list (n : ℕ) (hn : 0 < n) :
    ∃ l : List (Fin n × Fin n),
      l.Nodup ∧
      (∀ e : Fin n × Fin n, e ∈ l) ∧
      l.IsChain (fun e1 e2 => e1.2 = e2.1) ∧
      ∃ hl : l ≠ [], (l.head hl).1 = ⟨0, hn⟩ := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨[(0, 0)], by simp, ?_, by simp, List.cons_ne_nil _ _, rfl⟩
    intro ⟨a, b⟩
    fin_cases a; fin_cases b; simp
  | succ k hk ih =>
    obtain ⟨l, hnd, hmem, hch, hl, hhead⟩ := ih
    let z : Fin k := ⟨0, hk⟩
    let sp := spliceEdges {z} l
    let l' : List (Fin (k + 1) × Fin (k + 1)) :=
      (z.castSucc, Fin.last k) :: (Fin.last k, Fin.last k) :: (Fin.last k, z.castSucc) :: sp
    have hsp_nd : sp.Nodup := spliceEdges_nodup {z} l hnd
    have hsp_ch := spliceEdges_chain {z} l hch
    have hnot1 : (Fin.last k, z.castSucc) ∉ sp := by
      rw [spliceEdges_mem]
      rintro (⟨a, b, _, heq⟩ | ⟨b, hb, _, heq | heq⟩)
      · exact Fin.castSucc_ne_last a (Prod.mk.inj heq).1.symm
      · exact Fin.castSucc_ne_last b (Prod.mk.inj heq).1.symm
      · have : z = b := Fin.castSucc_injective k (Prod.mk.inj heq).2
        subst this; exact hb (Finset.mem_singleton_self z)
    have hnot2 : (Fin.last k, Fin.last k) ∉ (Fin.last k, z.castSucc) :: sp := by
      rw [List.mem_cons]
      rintro (heq | hm)
      · exact Fin.castSucc_ne_last z (Prod.mk.inj heq).2.symm
      · rw [spliceEdges_mem] at hm
        rcases hm with ⟨a, b, _, heq⟩ | ⟨b, _, _, heq | heq⟩
        · exact Fin.castSucc_ne_last a (Prod.mk.inj heq).1.symm
        · exact Fin.castSucc_ne_last b (Prod.mk.inj heq).1.symm
        · exact Fin.castSucc_ne_last b (Prod.mk.inj heq).2.symm
    have hnot3 : (z.castSucc, Fin.last k) ∉ (Fin.last k, Fin.last k) :: (Fin.last k, z.castSucc) :: sp := by
      rw [List.mem_cons, List.mem_cons]
      rintro (heq | heq | hm)
      · exact Fin.castSucc_ne_last z (Prod.mk.inj heq).1
      · exact Fin.castSucc_ne_last z (Prod.mk.inj heq).1
      · rw [spliceEdges_mem] at hm
        rcases hm with ⟨a, b, _, heq⟩ | ⟨b, hb, _, heq | heq⟩
        · exact Fin.castSucc_ne_last b (Prod.mk.inj heq).2.symm
        · have : z = b := Fin.castSucc_injective k (Prod.mk.inj heq).1
          subst this; exact hb (Finset.mem_singleton_self z)
        · exact Fin.castSucc_ne_last z (Prod.mk.inj heq).1
    have hl'_nd : l'.Nodup :=
      List.nodup_cons.mpr ⟨hnot3, List.nodup_cons.mpr ⟨hnot2, List.nodup_cons.mpr ⟨hnot1, hsp_nd⟩⟩⟩
    have hl'_mem : ∀ e : Fin (k + 1) × Fin (k + 1), e ∈ l' := by
      intro ⟨a, b⟩
      refine Fin.lastCases ?_ (fun a' => ?_) a
      · refine Fin.lastCases ?_ (fun b' => ?_) b
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · by_cases hb' : b' = z
          · subst hb'
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))
            rw [spliceEdges_mem]
            exact Or.inr ⟨b', by simp [hb'], ⟨z, hmem (z, b')⟩, Or.inr rfl⟩
      · refine Fin.lastCases ?_ (fun b' => ?_) b
        · by_cases ha' : a' = z
          · subst ha'; exact List.mem_cons_self ..
          · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))
            rw [spliceEdges_mem]
            exact Or.inr ⟨a', by simp [ha'], ⟨z, hmem (z, a')⟩, Or.inl rfl⟩
        · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_))
          rw [spliceEdges_mem]
          exact Or.inl ⟨a', b', hmem (a', b'), rfl⟩
    have hl'_ch : l'.IsChain (fun e1 e2 => e1.2 = e2.1) := by
      obtain ⟨hsp_ne, hsp_hd⟩ := hsp_ch.2 hl
      rw [hhead] at hsp_hd
      cases hsp_eq : sp with
      | nil => exact absurd hsp_eq hsp_ne
      | cons u us =>
        have hch_u : (u :: us).IsChain (fun e1 e2 => e1.2 = e2.1) := hsp_eq ▸ hsp_ch.1
        have hhd_u : u.1 = z.castSucc := by
          dsimp only [sp] at hsp_eq
          revert hsp_ne hsp_hd
          rw [hsp_eq]
          intro _ h
          exact h
        dsimp only [l']
        rw [hsp_eq]
        exact List.isChain_cons_cons.mpr ⟨rfl,
          List.isChain_cons_cons.mpr ⟨rfl,
            List.isChain_cons_cons.mpr ⟨hhd_u.symm, hch_u⟩⟩⟩
    exact ⟨l', hl'_nd, hl'_mem, hl'_ch, List.cons_ne_nil _ _, rfl⟩

private lemma exists_euler_circuit (n : ℕ) (hn : 0 < n) :
    ∃ c : Fin (n ^ 2) → Fin n × Fin n, IsEulerCircuit n hn c := by
  obtain ⟨l, hnd, hmem, hch, hl, hhead⟩ := exists_euler_list n hn
  have hlen : l.length = n ^ 2 := by
    have h1 : l.toFinset = Finset.univ := by
      ext e; simp [hmem e]
    have h2 : l.toFinset.card = l.length := List.toFinset_card_of_nodup hnd
    rw [← h2, h1, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  have hn2_pos : 0 < n ^ 2 := by nlinarith
  let c : Fin (n ^ 2) → Fin n × Fin n := fun i => l.get (i.cast hlen.symm)
  refine ⟨c, ?_, ?_, ?_⟩
  · change (l[0]'(by omega)).1 = ⟨0, hn⟩
    rw [← List.head_eq_getElem hl]
    exact hhead
  · intro i hi
    have hrel := List.isChain_iff_getElem.mp hch i.val (by omega)
    exact hrel
  · intro i j hij
    have hget := (List.nodup_iff_injective_get.mp hnd) hij
    exact Fin.ext (by simpa using congrArg Fin.val hget)

/-- Any injective function `Fin (n^2 - 1) → Fin n × Fin n` misses a unique directed edge. -/
private lemma exists_unique_missing_edge {n : ℕ} (hn : 2 ≤ n)
    {p : Fin (n ^ 2 - 1) → Fin n × Fin n} (hinj : Function.Injective p) :
    ∃! f : Fin n × Fin n, ∀ i : Fin (n ^ 2 - 1), p i ≠ f := by
  let S : Finset (Fin n × Fin n) := Finset.univ.image p
  have hScard : S.card = n ^ 2 - 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hcompl_card : (Finset.univ \ S).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, ← sq, hScard]
    have : 4 ≤ n ^ 2 := by nlinarith
    omega
  obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcompl_card
  refine ⟨f, ?_, ?_⟩
  · intro i hi
    have hmem : f ∈ Finset.univ \ S := by rw [hf]; exact Finset.mem_singleton_self f
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
  · intro g hg
    have hmem : g ∈ Finset.univ \ S := by
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ g, ?_⟩
      rw [Finset.mem_image]
      rintro ⟨i, _, hi⟩
      exact hg i hi
    rw [hf, Finset.mem_singleton] at hmem
    exact hmem

/-- For `n ≥ 2`, any walk `p : Fin (n^2 - 1) → Fin n × Fin n` with distinct edges visits all `n` vertices. -/
private lemma visits_all_of_inj_pred {n : ℕ} (hn : 2 ≤ n)
    {p : Fin (n ^ 2 - 1) → Fin n × Fin n} (hinj : Function.Injective p) :
    ∀ v : Fin n, ∃ i : Fin (n ^ 2 - 1), (p i).2 = v := by
  obtain ⟨f, _, huniq⟩ := exists_unique_missing_edge hn hinj
  intro v
  have hex : ∃ u : Fin n, (u, v) ≠ f := by
    by_cases h0 : (⟨0, by omega⟩, v) = f
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h1
      have : (⟨0, by omega⟩ : Fin n) = ⟨1, by omega⟩ := (Prod.mk.inj (h0.trans h1.symm)).1
      simp at this
    · exact ⟨⟨0, by omega⟩, h0⟩
  obtain ⟨u, hne⟩ := hex
  by_contra hno
  push Not at hno
  have hall : ∀ i : Fin (n ^ 2 - 1), p i ≠ (u, v) := by
    intro i hi
    exact hno i (congrArg Prod.snd hi)
  exact hne (huniq (u, v) hall)

/-- Degree balance classifies the missing edge `f` of a length `n^2 - 1` simple trail from `0`:
either `f = (v_end, 0)` or `f = (u, u)` for some `u ≠ 0` (and `v_end = 0`). -/
private lemma classify_missing_edge {n : ℕ} (hn : 2 ≤ n)
    {p : Fin (n ^ 2 - 1) → Fin n × Fin n}
    (hstart : (p ⟨0, Nat.sub_pos_of_lt (by nlinarith)⟩).1 = ⟨0, by omega⟩)
    (hchain : ∀ i : Fin (n ^ 2 - 1), (hi : i.val + 1 < n ^ 2 - 1) → (p i).2 = (p ⟨i.val + 1, hi⟩).1)
    (hinj : Function.Injective p)
    {f : Fin n × Fin n} (hmiss : ∀ i : Fin (n ^ 2 - 1), p i ≠ f) :
    (f.2 = ⟨0, by omega⟩ ∧ f.1 = (p ⟨n ^ 2 - 2, by have : 4 ≤ n ^ 2 := (by nlinarith); omega⟩).2) ∨
    (f.2 ≠ ⟨0, by omega⟩ ∧ f.1 = f.2 ∧ (p ⟨n ^ 2 - 2, by have : 4 ≤ n ^ 2 := (by nlinarith); omega⟩).2 = ⟨0, by omega⟩) := by
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hm1 : 1 ≤ n ^ 2 - 1 := by omega
  let S : Finset (Fin n × Fin n) := Finset.univ.image p
  have hS : S = Finset.univ.erase f := by
    have hsub : S ⊆ Finset.univ.erase f := by
      intro e he
      rw [Finset.mem_erase]
      rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
      exact ⟨hmiss i, Finset.mem_univ _⟩
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ f), Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, ← sq, Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hdiff : ∀ x : Fin n,
      (if (⟨0, by omega⟩ : Fin n) = x then (1 : ℤ) else 0) -
      (if (p ⟨n ^ 2 - 2, by omega⟩).2 = x then (1 : ℤ) else 0) =
      (if f.2 = x then (1 : ℤ) else 0) - (if f.1 = x then (1 : ℤ) else 0) := by
    intro x
    have hbal := walk_degree_balance hm1 p hchain x
    have hlast_idx : (⟨n ^ 2 - 1 - 1, by omega⟩ : Fin (n ^ 2 - 1)) = ⟨n ^ 2 - 2, by omega⟩ :=
      Fin.ext (by dsimp only; omega)
    rw [hstart, hlast_idx] at hbal
    have h1 : (Finset.univ.filter fun i : Fin (n ^ 2 - 1) => (p i).1 = x).card =
        (S.filter fun e : Fin n × Fin n => e.1 = x).card := by
      refine Finset.card_bij (fun i _ => p i) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨Finset.mem_image_of_mem p (Finset.mem_univ i), hi⟩
      · intro i _ j _ h; exact hinj h
      · intro e he
        simp only [Finset.mem_filter] at he
        rcases Finset.mem_image.mp he.1 with ⟨i, _, rfl⟩
        exact ⟨i, by simp [he.2], rfl⟩
    have h2 : (Finset.univ.filter fun i : Fin (n ^ 2 - 1) => (p i).2 = x).card =
        (S.filter fun e : Fin n × Fin n => e.2 = x).card := by
      refine Finset.card_bij (fun i _ => p i) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨Finset.mem_image_of_mem p (Finset.mem_univ i), hi⟩
      · intro i _ j _ h; exact hinj h
      · intro e he
        simp only [Finset.mem_filter] at he
        rcases Finset.mem_image.mp he.1 with ⟨i, _, rfl⟩
        exact ⟨i, by simp [he.2], rfl⟩
    have hall1 : (Finset.univ.filter fun e : Fin n × Fin n => e.1 = x).card = n := by
      have : (Finset.univ.filter fun e : Fin n × Fin n => e.1 = x) =
          Finset.univ.image (fun y : Fin n => (x, y)) := by ext ⟨a, b⟩; simp [eq_comm]
      rw [this, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Finset.card_fin]
    have hall2 : (Finset.univ.filter fun e : Fin n × Fin n => e.2 = x).card = n := by
      have : (Finset.univ.filter fun e : Fin n × Fin n => e.2 = x) =
          Finset.univ.image (fun y : Fin n => (y, x)) := by ext ⟨a, b⟩; simp [eq_comm]
      rw [this, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Finset.card_fin]
    have hs1 : ((S.filter fun e : Fin n × Fin n => e.1 = x).card : ℤ) =
        (n : ℤ) - if f.1 = x then 1 else 0 := by
      rw [hS, Finset.filter_erase]
      by_cases hf1 : f.1 = x
      · rw [if_pos hf1, Finset.card_erase_of_mem (by simp [hf1]), hall1]
        have : 1 ≤ n := by omega
        omega
      · rw [if_neg hf1, Finset.erase_eq_of_notMem (by simp [hf1]), hall1]
        ring
    have hs2 : ((S.filter fun e : Fin n × Fin n => e.2 = x).card : ℤ) =
        (n : ℤ) - if f.2 = x then 1 else 0 := by
      rw [hS, Finset.filter_erase]
      by_cases hf2 : f.2 = x
      · rw [if_pos hf2, Finset.card_erase_of_mem (by simp [hf2]), hall2]
        have : 1 ≤ n := by omega
        omega
      · rw [if_neg hf2, Finset.erase_eq_of_notMem (by simp [hf2]), hall2]
        ring
    rw [h1, h2, hs1, hs2] at hbal
    linarith
  by_cases hf2 : f.2 = ⟨0, by omega⟩
  · left
    refine ⟨hf2, ?_⟩
    have h0 := hdiff f.1
    split_ifs at h0 with h1 h2 h3 h4 <;> first | exact h2.symm | omega
  · right
    have h1 := hdiff f.2
    have hf12 : f.1 = f.2 := by
      split_ifs at h1 with ha hb hc hd <;> first | exact hd | omega
    have h0 := hdiff ⟨0, by omega⟩
    have hend : (p ⟨n ^ 2 - 2, by omega⟩).2 = ⟨0, by omega⟩ := by
      split_ifs at h0 with ha hb hc hd <;> first | exact hb | omega
    exact ⟨hf2, hf12, hend⟩

/-- Helper: count of `T n (n^2 + 1)` equals `n * |EC|`. -/
private lemma card_T_succ_sq {n : ℕ} (hn : 2 ≤ n) (hn0 : 0 < n) :
    letI := Classical.decPred (IsEulerCircuit n hn0)
    T n (n ^ 2 + 1) = n * (Finset.univ.filter fun c => IsEulerCircuit n hn0 c).card := by
  classical
  have hk : 1 ≤ n ^ 2 + 1 := by omega
  unfold T
  rw [dif_pos ⟨hn0, hk⟩]
  have hcard :
      (Finset.univ.filter fun w : Fin (n ^ 2 + 1) → Fin n × Fin n =>
        IsEdgeCollisionWalk n (n ^ 2 + 1) hn0 hk w).card =
      ((Finset.univ.filter fun c : Fin (n ^ 2) → Fin n × Fin n => IsEulerCircuit n hn0 c) ×ˢ
        (Finset.univ : Finset (Fin n))).card := by
    refine Finset.card_bij
      (fun w _ => (fun i : Fin (n ^ 2) => w ⟨i.val, by omega⟩, (w ⟨n ^ 2, by omega⟩).2))
      ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hstart, hchain, hinj, _, _⟩ := hw.2
      rw [Finset.mem_product, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, ?_, ?_⟩, Finset.mem_univ _⟩
      · exact hstart
      · intro i hi
        exact hchain ⟨i.val, by have := i.isLt; omega⟩ (by dsimp only; omega)
      · intro i j hij
        by_contra hne
        exact hinj ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩
          (fun h => hne (Fin.ext (by simpa using congrArg Fin.val h))) hij
    · intro w1 hw1 w2 hw2 heq
      rw [Finset.mem_filter] at hw1 hw2
      rcases Prod.mk.inj heq with ⟨hpre, hy⟩
      funext i
      by_cases hi : i.val < n ^ 2
      · exact congrFun hpre ⟨i.val, hi⟩
      · have hieq : i = ⟨n ^ 2, by omega⟩ := Fin.ext (by have := i.isLt; dsimp only; omega)
        rw [hieq]
        have hc1 : IsEulerCircuit n hn0 (fun k : Fin (n ^ 2) => w1 ⟨k.val, by omega⟩) := by
          refine ⟨hw1.2.1, fun k hk' => hw1.2.2.1 ⟨k.val, by have := k.isLt; omega⟩ (by dsimp only; omega), fun k1 k2 h => ?_⟩
          by_contra hne
          exact hw1.2.2.2.1 ⟨k1.val, by have := k1.isLt; omega⟩ ⟨k2.val, by have := k2.isLt; omega⟩
            (fun h' => hne (Fin.ext (by simpa using congrArg Fin.val h'))) h
        have hc2 : IsEulerCircuit n hn0 (fun k : Fin (n ^ 2) => w2 ⟨k.val, by omega⟩) := by
          refine ⟨hw2.2.1, fun k hk' => hw2.2.2.1 ⟨k.val, by have := k.isLt; omega⟩ (by dsimp only; omega), fun k1 k2 h => ?_⟩
          by_contra hne
          exact hw2.2.2.2.1 ⟨k1.val, by have := k1.isLt; omega⟩ ⟨k2.val, by have := k2.isLt; omega⟩
            (fun h' => hne (Fin.ext (by simpa using congrArg Fin.val h'))) h
        have hn2_ge : 4 ≤ n ^ 2 := by nlinarith
        have hf1 : (w1 ⟨n ^ 2, by omega⟩).1 = ⟨0, hn0⟩ := by
          have := hw1.2.2.1 ⟨n ^ 2 - 1, by omega⟩ (by dsimp only; omega)
          have hidx : (⟨n ^ 2 - 1 + 1, by omega⟩ : Fin (n ^ 2 + 1)) = ⟨n ^ 2, by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [hidx] at this
          exact this.symm.trans (euler_end hc1)
        have hf2 : (w2 ⟨n ^ 2, by omega⟩).1 = ⟨0, hn0⟩ := by
          have := hw2.2.2.1 ⟨n ^ 2 - 1, by omega⟩ (by dsimp only; omega)
          have hidx : (⟨n ^ 2 - 1 + 1, by omega⟩ : Fin (n ^ 2 + 1)) = ⟨n ^ 2, by omega⟩ :=
            Fin.ext (by dsimp only; omega)
          rw [hidx] at this
          exact this.symm.trans (euler_end hc2)
        exact Prod.ext (hf1.trans hf2.symm) hy
    · intro ⟨c, y⟩ hcy
      rw [Finset.mem_product, Finset.mem_filter] at hcy
      have hc : IsEulerCircuit n hn0 c := hcy.1.2
      let w : Fin (n ^ 2 + 1) → Fin n × Fin n := fun i =>
        if hi : i.val < n ^ 2 then c ⟨i.val, hi⟩ else (⟨0, hn0⟩, y)
      refine ⟨w, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ w, ?_, ?_, ?_, ?_, ?_⟩
        · dsimp only [w]; rw [dif_pos (by nlinarith)]; exact hc.1
        · intro i hi
          dsimp only [w]
          by_cases h1 : i.val + 1 < n ^ 2
          · rw [dif_pos (by omega), dif_pos h1]; exact hc.2.1 ⟨i.val, by omega⟩ h1
          · have hieq : i.val = n ^ 2 - 1 := by omega
            rw [dif_pos (by omega), dif_neg h1]
            have hfin : (⟨i.val, by omega⟩ : Fin (n ^ 2)) = ⟨n ^ 2 - 1, Nat.sub_lt (by nlinarith) Nat.one_pos⟩ := Fin.ext hieq
            rw [hfin]
            exact euler_end hc
        · intro i j hij
          dsimp only [w]
          rw [dif_pos (by have := i.isLt; omega), dif_pos (by have := j.isLt; omega)]
          intro h
          exact hij (Fin.ext (by simpa using congrArg Fin.val (hc.2.2 h)))
        · obtain ⟨j, hj⟩ := (euler_bijective hc).2 (⟨0, hn0⟩, y)
          refine ⟨⟨j.val, by have := j.isLt; omega⟩, ?_⟩
          dsimp only [w]
          rw [dif_neg (by omega), dif_pos j.isLt]
          exact hj.symm
        · intro v
          obtain ⟨j, hj⟩ := (euler_bijective hc).2 (⟨0, hn0⟩, v)
          right
          refine ⟨⟨j.val, by have := j.isLt; omega⟩, ?_⟩
          dsimp only [w]
          rw [dif_pos j.isLt]
          exact congrArg Prod.snd hj
      · refine Prod.ext ?_ ?_
        · funext i; dsimp only [w]; rw [dif_pos i.isLt]
        · dsimp only [w]; rw [dif_neg (by omega)]
  rw [show (letI := Classical.decPred (IsEdgeCollisionWalk n (n ^ 2 + 1) hn0 hk);
      (Finset.univ.filter fun w : Fin (n ^ 2 + 1) → Fin n × Fin n =>
        IsEdgeCollisionWalk n (n ^ 2 + 1) hn0 hk w).card) =
      (Finset.univ.filter fun w : Fin (n ^ 2 + 1) → Fin n × Fin n =>
        IsEdgeCollisionWalk n (n ^ 2 + 1) hn0 hk w).card by congr 1]
  rw [hcard, Finset.card_product, Finset.card_fin, mul_comm]

/-- For each `u ≠ 0`, `(n - 1) * |EC_without u| = |EC|` by inserting/deleting `(u, u)` after
an arrival at `u`. -/
private lemma card_without_loop_mul {n : ℕ} (hn : 2 ≤ n) (hn0 : 0 < n) (u : Fin n) (hu : u ≠ ⟨0, hn0⟩) :
    letI := Classical.decPred (IsEulerCircuit n hn0)
    letI := Classical.decPred (IsCircuitWithoutLoop n hn0 u)
    (n - 1) * (Finset.univ.filter fun p => IsCircuitWithoutLoop n hn0 u p).card =
      (Finset.univ.filter fun c => IsEulerCircuit n hn0 c).card := by
  classical
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  let EC := Finset.univ.filter fun c : Fin (n ^ 2) → Fin n × Fin n => IsEulerCircuit n hn0 c
  let WL := Finset.univ.filter fun p : Fin (n ^ 2 - 1) → Fin n × Fin n => IsCircuitWithoutLoop n hn0 u p
  -- Count pairs (p, k) with p ∈ WL and (p k).2 = u.
  let Pairs := WL.sigma fun p => Finset.univ.filter fun k : Fin (n ^ 2 - 1) => (p k).2 = u
  have hPairs_left : Pairs.card = (n - 1) * WL.card := by
    rw [Finset.card_sigma]
    have hconst : ∀ p ∈ WL, (Finset.univ.filter fun k : Fin (n ^ 2 - 1) => (p k).2 = u).card = n - 1 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨_, _, hinj, hmiss⟩ := hp.2
      have hS : Finset.univ.image p = Finset.univ.erase (u, u) := by
        have hsub : Finset.univ.image p ⊆ Finset.univ.erase (u, u) := by
          intro e he
          rw [Finset.mem_erase]
          rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
          exact ⟨hmiss i, Finset.mem_univ _⟩
        refine Finset.eq_of_subset_of_card_le hsub ?_
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin, ← sq, Finset.card_image_of_injective _ hinj, Finset.card_fin]
      have h1 : (Finset.univ.filter fun k : Fin (n ^ 2 - 1) => (p k).2 = u).card =
          ((Finset.univ.erase (u, u)).filter fun e : Fin n × Fin n => e.2 = u).card := by
        rw [← hS]
        refine Finset.card_bij (fun k _ => p k) ?_ ?_ ?_
        · intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          exact ⟨Finset.mem_image_of_mem p (Finset.mem_univ k), hk⟩
        · intro k1 _ k2 _ h; exact hinj h
        · intro e he
          simp only [Finset.mem_filter] at he
          rcases Finset.mem_image.mp he.1 with ⟨k, _, rfl⟩
          exact ⟨k, by simp [he.2], rfl⟩
      rw [h1, Finset.filter_erase, Finset.card_erase_of_mem (by simp)]
      have hall : (Finset.univ.filter fun e : Fin n × Fin n => e.2 = u).card = n := by
        have : (Finset.univ.filter fun e : Fin n × Fin n => e.2 = u) =
            Finset.univ.image (fun x : Fin n => (x, u)) := by ext ⟨a, b⟩; simp [eq_comm]
        rw [this, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Finset.card_fin]
      rw [hall]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, mul_comm]
  -- Bijection Pairs ≃ EC: insert (u, u) right after index k!
  let ins (p : Fin (n ^ 2 - 1) → Fin n × Fin n) (k : Fin (n ^ 2 - 1)) :
      Fin (n ^ 2) → Fin n × Fin n := fun i =>
    if h1 : i.val ≤ k.val then p ⟨i.val, by omega⟩
    else if h2 : i.val = k.val + 1 then (u, u)
    else p ⟨i.val - 1, by omega⟩
  have hPairs_eq_EC : Pairs.card = EC.card := by
    refine Finset.card_bij (fun pk _ => ins pk.1 pk.2) ?_ ?_ ?_
    · intro ⟨p, k⟩ hpk
      simp only [Pairs, WL, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hpk
      rcases hpk with ⟨⟨hstart, hchain, hinj, hmiss⟩, hku⟩
      simp only [EC, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · dsimp only [ins]
        rw [dif_pos (Nat.zero_le k.val)]
        exact hstart (by omega)
      · intro i hi
        dsimp only [ins]
        by_cases h1 : i.val < k.val
        · rw [dif_pos (by omega), dif_pos (by omega)]
          exact hchain ⟨i.val, by omega⟩ (by dsimp only; omega)
        · by_cases h2 : i.val = k.val
          · rw [dif_pos (by omega), dif_neg (by omega), dif_pos (by omega)]
            have : (⟨i.val, by omega⟩ : Fin (n ^ 2 - 1)) = k := Fin.ext h2
            rw [this, hku]
          · by_cases h3 : i.val = k.val + 1
            · rw [dif_neg (by omega), dif_pos h3, dif_neg (by omega), dif_neg (by omega)]
              have hklt : k.val + 1 < n ^ 2 - 1 := by omega
              have hch := hchain k hklt
              have hidx : (⟨i.val + 1 - 1, by omega⟩ : Fin (n ^ 2 - 1)) = ⟨k.val + 1, hklt⟩ :=
                Fin.ext (by dsimp only; omega)
              rw [hidx, ← hch, hku]
            · rw [dif_neg (by omega), dif_neg h3, dif_neg (by omega), dif_neg (by omega)]
              have hidx : (⟨i.val + 1 - 1, by omega⟩ : Fin (n ^ 2 - 1)) = ⟨(i.val - 1) + 1, by omega⟩ :=
                Fin.ext (by dsimp only; omega)
              rw [hidx]
              exact hchain ⟨i.val - 1, by omega⟩ (by dsimp only; omega)
      · intro i j hij
        dsimp only [ins] at hij
        split_ifs at hij with hi1 hj1 hj2 hi2 hj3 hj4 hi3 hj5
        · exact Fin.ext (by simpa using congrArg Fin.val (hinj hij))
        · exact absurd hij (hmiss _)
        · have := congrArg Fin.val (hinj hij); dsimp only at this; omega
        · exact absurd hij.symm (hmiss _)
        · exact Fin.ext (by omega)
        · exact absurd hij.symm (hmiss _)
        · have := congrArg Fin.val (hinj hij); dsimp only at this; omega
        · exact absurd hij (hmiss _)
        · have := congrArg Fin.val (hinj hij); dsimp only at this; exact Fin.ext (by omega)
    · intro ⟨p1, k1⟩ h1 ⟨p2, k2⟩ h2 heq
      simp only [Pairs, WL, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      have hk_eq : k1 = k2 := by
        have hpos1 : ins p1 k1 ⟨k1.val + 1, by omega⟩ = (u, u) := by
          dsimp only [ins]; rw [dif_neg (by omega), dif_pos rfl]
        have hpos2 : ins p2 k2 ⟨k1.val + 1, by omega⟩ = (u, u) := by rw [← heq]; exact hpos1
        dsimp only [ins] at hpos2
        split_ifs at hpos2 with ha hb
        · exact absurd hpos2 (h2.1.2.2.2 _)
        · exact Fin.ext (by omega)
        · exact absurd hpos2 (h2.1.2.2.2 _)
      subst hk_eq
      have hp_eq : p1 = p2 := by
        funext i
        by_cases hi : i.val ≤ k1.val
        · have h := congrFun heq ⟨i.val, by omega⟩
          dsimp only [ins] at h
          rw [dif_pos hi, dif_pos hi] at h
          exact h
        · have h := congrFun heq ⟨i.val + 1, by omega⟩
          dsimp only [ins] at h
          rw [dif_neg (by omega), dif_neg (by omega),
            dif_neg (by omega), dif_neg (by omega)] at h
          have hfin : (⟨i.val + 1 - 1, by omega⟩ : Fin (n ^ 2 - 1)) = i := Fin.ext (by dsimp only; omega)
          rw [hfin] at h
          exact h
      subst hp_eq
      rfl
    · intro c hc
      simp only [EC, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      obtain ⟨m, hm⟩ := (euler_bijective hc).2 (u, u)
      have hm_pos : 0 < m.val := by
        by_contra h0
        have hm0 : m = ⟨0, by nlinarith⟩ := Fin.ext (by dsimp only; omega)
        rw [hm0] at hm
        have := congrArg Prod.fst hm
        rw [hc.1] at this
        exact hu this.symm
      let k : Fin (n ^ 2 - 1) := ⟨m.val - 1, by omega⟩
      let p : Fin (n ^ 2 - 1) → Fin n × Fin n := fun i =>
        if hi : i.val < m.val then c ⟨i.val, by omega⟩ else c ⟨i.val + 1, by omega⟩
      have hp_mem : p ∈ WL := by
        simp only [WL, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro _; dsimp only [p]; rw [dif_pos hm_pos]; exact hc.1
        · intro i hi
          dsimp only [p]
          by_cases h1 : i.val + 1 < m.val
          · rw [dif_pos (by omega), dif_pos h1]; exact hc.2.1 ⟨i.val, by omega⟩ (by dsimp only; omega)
          · by_cases h2 : i.val < m.val
            · rw [dif_pos h2, dif_neg h1]
              have hmeq : m = ⟨i.val + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
              have hm_val : m.val = i.val + 1 := congrArg Fin.val hmeq
              have hc1 := hc.2.1 ⟨i.val, by omega⟩ (by dsimp only; omega)
              have hc2 := hc.2.1 m (by omega)
              dsimp only at hc1
              have hfin1 : (⟨i.val + 1, by omega⟩ : Fin (n ^ 2)) = m := hmeq.symm
              have hfin2 : (⟨m.val + 1, by omega⟩ : Fin (n ^ 2)) = ⟨i.val + 1 + 1, by omega⟩ :=
                Fin.ext (by dsimp only; omega)
              rw [hfin1, hm] at hc1
              rw [hm, hfin2] at hc2
              exact hc1.trans hc2
            · rw [dif_neg h2, dif_neg h1]
              exact hc.2.1 ⟨i.val + 1, by omega⟩ (by dsimp only; omega)
        · intro i j hij
          dsimp only [p] at hij
          split_ifs at hij with hi hj hj'
          · exact Fin.ext (by simpa using congrArg Fin.val (hc.2.2 hij))
          · have := congrArg Fin.val (hc.2.2 hij); dsimp only at this; omega
          · have := congrArg Fin.val (hc.2.2 hij); dsimp only at this; omega
          · have := congrArg Fin.val (hc.2.2 hij); dsimp only at this; exact Fin.ext (by omega)
        · intro i hi
          dsimp only [p] at hi
          split_ifs at hi with hlt
          · have := congrArg Fin.val (hc.2.2 (hi.trans hm.symm)); dsimp only at this; omega
          · have := congrArg Fin.val (hc.2.2 (hi.trans hm.symm)); dsimp only at this; omega
      have hku : (p k).2 = u := by
        dsimp only [p, k]
        rw [dif_pos (by omega)]
        have hc1 := hc.2.1 ⟨m.val - 1, by omega⟩ (by dsimp only; omega)
        have hfin : (⟨m.val - 1 + 1, by omega⟩ : Fin (n ^ 2)) = m := Fin.ext (by dsimp only; omega)
        rw [hfin, hm] at hc1
        exact hc1
      refine ⟨⟨p, k⟩, ?_, ?_⟩
      · simp only [Pairs, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hp_mem, hku⟩
      · funext i
        dsimp only [ins, p, k]
        by_cases h1 : i.val < m.val
        · rw [dif_pos (by omega), dif_pos h1]
        · by_cases h2 : i.val = m.val
          · rw [dif_neg (by omega), dif_pos (by omega)]
            have : i = m := Fin.ext h2
            rw [this, hm]
          · rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]
            have hfin : (⟨i.val - 1 + 1, by omega⟩ : Fin (n ^ 2)) = i := Fin.ext (by dsimp only; omega)
            rw [hfin]
  exact hPairs_left.symm.trans hPairs_eq_EC

/-- Helper: count of `T n (n^2)` equals `(2 * n - 1) * |EC|`. -/
private lemma card_T_sq {n : ℕ} (hn : 2 ≤ n) (hn0 : 0 < n) :
    letI := Classical.decPred (IsEulerCircuit n hn0)
    T n (n ^ 2) = (2 * n - 1) * (Finset.univ.filter fun c => IsEulerCircuit n hn0 c).card := by
  classical
  have hk : 1 ≤ n ^ 2 := by nlinarith
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  unfold T
  rw [dif_pos ⟨hn0, hk⟩]
  let W := Finset.univ.filter fun w : Fin (n ^ 2) → Fin n × Fin n =>
    IsEdgeCollisionWalk n (n ^ 2) hn0 hk w
  let EC := Finset.univ.filter fun c : Fin (n ^ 2) → Fin n × Fin n => IsEulerCircuit n hn0 c
  -- Split W into WA (prefix ends at some v_end and misses (v_end, 0)) vs WB (prefix misses (u, u) with u ≠ 0)
  let isCaseA (w : Fin (n ^ 2) → Fin n × Fin n) : Prop :=
    ∃ v_end : Fin n, ∀ i : Fin (n ^ 2 - 1), w ⟨i.val, by omega⟩ ≠ (v_end, ⟨0, hn0⟩)
  let WA := W.filter isCaseA
  let WB := W.filter (fun w => ¬ isCaseA w)
  have hW_split : W.card = WA.card + WB.card :=
    (Finset.card_filter_add_card_filter_not isCaseA).symm
  -- Count WA: bijection with EC × {y : Fin n // y ≠ 0}
  have hWA : WA.card = (n - 1) * EC.card := by
    let Y := (Finset.univ : Finset (Fin n)).erase ⟨0, hn0⟩
    have hYcard : Y.card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    have hbij : WA.card = (EC ×ˢ Y).card := by
      refine Finset.card_bij
        (fun w _ => (fun i : Fin (n ^ 2) =>
          if hi : i.val < n ^ 2 - 1 then w ⟨i.val, by omega⟩
          else ((w ⟨n ^ 2 - 2, by omega⟩).2, ⟨0, hn0⟩),
          (w ⟨n ^ 2 - 1, by omega⟩).2)) ?_ ?_ ?_
      · intro w hw
        rw [Finset.mem_filter, Finset.mem_filter] at hw
        obtain ⟨⟨_, hstart, hchain, hinj, hcoll, _⟩, ⟨v_end, hmiss⟩⟩ := hw
        let p : Fin (n ^ 2 - 1) → Fin n × Fin n := fun i => w ⟨i.val, by omega⟩
        have hpinj : Function.Injective p := by
          intro i j h; by_contra hne; exact hinj i j hne h
        have hpch : ∀ i : Fin (n ^ 2 - 1), (hi : i.val + 1 < n ^ 2 - 1) → (p i).2 = (p ⟨i.val + 1, hi⟩).1 :=
          fun i hi => hchain ⟨i.val, by omega⟩ (by dsimp only; omega)
        have hcls := classify_missing_edge hn hstart hpch hpinj hmiss
        have hv_eq : v_end = (w ⟨n ^ 2 - 2, by omega⟩).2 := by
          rcases hcls with ⟨_, h1⟩ | ⟨h2, _, _⟩
          · exact h1
          · exact absurd rfl h2
        rw [Finset.mem_product, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, ?_, ?_, ?_⟩, ?_⟩
        · dsimp only; rw [dif_pos (by omega)]; exact hstart
        · intro i hi
          dsimp only
          by_cases h1 : i.val + 1 < n ^ 2 - 1
          · rw [dif_pos (by omega), dif_pos h1]; exact hchain ⟨i.val, by omega⟩ (by dsimp only; omega)
          · have hieq : i.val = n ^ 2 - 2 := by omega
            rw [dif_pos (by omega), dif_neg h1]
            have hfin : (⟨i.val, by omega⟩ : Fin (n ^ 2)) = ⟨n ^ 2 - 2, by omega⟩ := Fin.ext hieq
            rw [hfin]
        · intro i j hij
          dsimp only at hij
          by_cases hi : i.val < n ^ 2 - 1 <;> by_cases hj : j.val < n ^ 2 - 1
          · rw [dif_pos hi, dif_pos hj] at hij
            by_contra hne
            exact hinj ⟨i.val, hi⟩ ⟨j.val, hj⟩ (fun h => hne (Fin.ext (by simpa using congrArg Fin.val h))) hij
          · rw [dif_pos hi, dif_neg hj] at hij
            exact absurd (hv_eq ▸ hij) (hmiss ⟨i.val, hi⟩)
          · rw [dif_neg hi, dif_pos hj] at hij
            exact absurd (hv_eq ▸ hij.symm) (hmiss ⟨j.val, hj⟩)
          · exact Fin.ext (by omega)
        · rw [Finset.mem_erase]
          refine ⟨?_, Finset.mem_univ _⟩
          intro hy0
          obtain ⟨j, hj⟩ := hcoll
          have hlast_fst : (w ⟨n ^ 2 - 1, by omega⟩).1 = (w ⟨n ^ 2 - 2, by omega⟩).2 := by
            have := hchain ⟨n ^ 2 - 2, by omega⟩ (by dsimp only; omega)
            have hfin : (⟨n ^ 2 - 2 + 1, by omega⟩ : Fin (n ^ 2)) = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hfin] at this
            exact this.symm
          have hwlast : w ⟨n ^ 2 - 1, by omega⟩ = (v_end, ⟨0, hn0⟩) :=
            Prod.ext (hlast_fst.trans hv_eq.symm) hy0
          exact hmiss j (hj.symm.trans hwlast)
      · intro w1 hw1 w2 hw2 heq
        rw [Finset.mem_filter, Finset.mem_filter] at hw1 hw2
        rcases Prod.mk.inj heq with ⟨hc, hy⟩
        funext i
        by_cases hi : i.val < n ^ 2 - 1
        · have h := congrFun hc ⟨i.val, by omega⟩
          rw [dif_pos hi, dif_pos hi] at h
          exact h
        · have hieq : i = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hieq]
          have h1 : (w1 ⟨n ^ 2 - 1, by omega⟩).1 = (w1 ⟨n ^ 2 - 2, by omega⟩).2 := by
            have := hw1.1.2.2.1 ⟨n ^ 2 - 2, by omega⟩ (by dsimp only; omega)
            have hfin : (⟨n ^ 2 - 2 + 1, by omega⟩ : Fin (n ^ 2)) = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hfin] at this; exact this.symm
          have h2 : (w2 ⟨n ^ 2 - 1, by omega⟩).1 = (w2 ⟨n ^ 2 - 2, by omega⟩).2 := by
            have := hw2.1.2.2.1 ⟨n ^ 2 - 2, by omega⟩ (by dsimp only; omega)
            have hfin : (⟨n ^ 2 - 2 + 1, by omega⟩ : Fin (n ^ 2)) = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hfin] at this; exact this.symm
          have hprev : w1 ⟨n ^ 2 - 2, by omega⟩ = w2 ⟨n ^ 2 - 2, by omega⟩ := by
            have h := congrFun hc ⟨n ^ 2 - 2, by omega⟩
            rw [dif_pos (by dsimp only; omega), dif_pos (by dsimp only; omega)] at h
            exact h
          exact Prod.ext (h1.trans ((congrArg Prod.snd hprev).trans h2.symm)) hy
      · intro ⟨c, y⟩ hcy
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_erase] at hcy
        obtain ⟨⟨_, hc⟩, hy0, _⟩ := hcy
        let v_end := (c ⟨n ^ 2 - 2, by omega⟩).2
        let w : Fin (n ^ 2) → Fin n × Fin n := fun i =>
          if hi : i.val < n ^ 2 - 1 then c i else (v_end, y)
        have hclast : c ⟨n ^ 2 - 1, by omega⟩ = (v_end, ⟨0, hn0⟩) := by
          have h1 : (c ⟨n ^ 2 - 1, by omega⟩).1 = v_end := by
            have := hc.2.1 ⟨n ^ 2 - 2, by omega⟩ (by dsimp only; omega)
            have hfin : (⟨n ^ 2 - 2 + 1, by omega⟩ : Fin (n ^ 2)) = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hfin] at this; exact this.symm
          exact Prod.ext h1 (euler_end hc)
        refine ⟨w, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_filter]
          refine ⟨⟨Finset.mem_univ w, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · dsimp only [w]; rw [dif_pos (by omega)]; exact hc.1
          · intro i hi
            dsimp only [w]
            by_cases h1 : i.val + 1 < n ^ 2 - 1
            · rw [dif_pos (by omega), dif_pos h1]; exact hc.2.1 i hi
            · have hieq : i.val = n ^ 2 - 2 := by omega
              rw [dif_pos (by omega), dif_neg h1]
              have hfin : i = ⟨n ^ 2 - 2, by omega⟩ := Fin.ext hieq
              rw [hfin]
          · intro i j hij
            dsimp only [w]
            rw [dif_pos i.isLt, dif_pos j.isLt]
            intro h; exact hij (Fin.ext (by simpa using congrArg Fin.val (hc.2.2 h)))
          · obtain ⟨j, hj⟩ := (euler_bijective hc).2 (v_end, y)
            dsimp only at hj
            have hj_lt : j.val < n ^ 2 - 1 := by
              by_contra hge
              have hjeq : j = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hjeq, hclast] at hj
              exact hy0 (Prod.mk.inj hj).2.symm
            refine ⟨⟨j.val, hj_lt⟩, ?_⟩
            dsimp only [w]
            rw [dif_neg (by omega), dif_pos hj_lt]
            exact hj.symm
          · intro v
            right
            have hpinj : Function.Injective (fun i : Fin (n ^ 2 - 1) => c ⟨i.val, by omega⟩) :=
              fun i j h => Fin.ext (by simpa using congrArg Fin.val (hc.2.2 h))
            obtain ⟨i, hi⟩ := visits_all_of_inj_pred hn hpinj v
            refine ⟨⟨i.val, by omega⟩, ?_⟩
            dsimp only [w]; rw [dif_pos i.isLt]; exact hi
          · refine ⟨v_end, fun i hi => ?_⟩
            dsimp only [w] at hi
            rw [dif_pos i.isLt] at hi
            have := congrArg Fin.val (hc.2.2 (hi.trans hclast.symm))
            dsimp only at this
            omega
        · refine Prod.ext ?_ ?_
          · funext i
            dsimp only [w]
            by_cases hi : i.val < n ^ 2 - 1
            · rw [dif_pos hi, dif_pos hi]
            · have hieq : i = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
              rw [hieq]
              rw [dif_neg (by dsimp only; omega), dif_pos (by omega)]
              exact hclast.symm
          · dsimp only [w]; rw [dif_neg (by omega)]
    rw [hbij, Finset.card_product, hYcard, mul_comm]
  -- Count WB: bijection with (Σ u ∈ Y, WL u) × Fin n
  have hWB : WB.card = n * EC.card := by
    let Y := (Finset.univ : Finset (Fin n)).erase ⟨0, hn0⟩
    have hYcard : Y.card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    let Bpre := Y.sigma fun u =>
      Finset.univ.filter fun p : Fin (n ^ 2 - 1) → Fin n × Fin n => IsCircuitWithoutLoop n hn0 u p
    have hBpre_mul : (n - 1) * Bpre.card = (n - 1) * EC.card := by
      rw [Finset.card_sigma, Finset.mul_sum]
      have hterm : ∀ u ∈ Y,
          (n - 1) * (Finset.univ.filter fun p => IsCircuitWithoutLoop n hn0 u p).card = EC.card := by
        intro u hu
        rw [Finset.mem_erase] at hu
        exact card_without_loop_mul hn hn0 u hu.1
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, hYcard, smul_eq_mul]
    have hBpre : Bpre.card = EC.card := mul_left_cancel₀ (by omega : n - 1 ≠ 0) hBpre_mul
    have hbij : WB.card = (Bpre ×ˢ (Finset.univ : Finset (Fin n))).card := by
      refine Finset.card_bij
        (fun w hw =>
          let p : Fin (n ^ 2 - 1) → Fin n × Fin n := fun i => w ⟨i.val, by omega⟩
          let u : Fin n :=
            if h : ∃ u : Fin n, ∀ i : Fin (n ^ 2 - 1), p i ≠ (u, u) then Classical.choose h
            else ⟨0, hn0⟩
          (⟨u, p⟩, (w ⟨n ^ 2 - 1, by omega⟩).2)) ?_ ?_ ?_
      · intro w hw
        rw [Finset.mem_filter, Finset.mem_filter] at hw
        obtain ⟨⟨_, hstart, hchain, hinj, _, _⟩, hnotA⟩ := hw
        let p : Fin (n ^ 2 - 1) → Fin n × Fin n := fun i => w ⟨i.val, by omega⟩
        have hpinj : Function.Injective p := fun i j h => by by_contra hne; exact hinj i j hne h
        have hpch : ∀ i : Fin (n ^ 2 - 1), (hi : i.val + 1 < n ^ 2 - 1) → (p i).2 = (p ⟨i.val + 1, hi⟩).1 :=
          fun i hi => hchain ⟨i.val, by omega⟩ (by dsimp only; omega)
        obtain ⟨f, hfmiss, huniq⟩ := exists_unique_missing_edge hn hpinj
        have hcls := classify_missing_edge hn hstart hpch hpinj hfmiss
        rcases hcls with ⟨hf2, _⟩ | ⟨hf2, hf12, _⟩
        · exfalso
          exact hnotA ⟨f.1, fun i hi => hfmiss i (hi.trans (Prod.ext rfl hf2.symm))⟩
        · have hex : ∃ u : Fin n, ∀ i : Fin (n ^ 2 - 1), p i ≠ (u, u) :=
            ⟨f.2, fun i hi => hfmiss i (hi.trans (Prod.ext hf12.symm rfl))⟩
          have hu_spec : ∀ i : Fin (n ^ 2 - 1), p i ≠ (Classical.choose hex, Classical.choose hex) :=
            Classical.choose_spec hex
          have hu_eq : Classical.choose hex = f.2 := by
            have := huniq (Classical.choose hex, Classical.choose hex) hu_spec
            exact (Prod.mk.inj this).2
          rw [Finset.mem_product]
          refine ⟨?_, Finset.mem_univ _⟩
          simp only [Bpre, Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [dif_pos hex]
          refine ⟨Finset.mem_erase.mpr ⟨hu_eq ▸ hf2, Finset.mem_univ _⟩, ?_, hpch, hpinj, hu_spec⟩
          intro _; exact hstart
      · intro w1 hw1 w2 hw2 heq
        rw [Finset.mem_filter, Finset.mem_filter] at hw1 hw2
        rcases Prod.mk.inj heq with ⟨hsig, hy⟩
        have hpre : (fun i : Fin (n ^ 2 - 1) => w1 ⟨i.val, by omega⟩) =
            (fun i : Fin (n ^ 2 - 1) => w2 ⟨i.val, by omega⟩) := by
          have := congrArg Sigma.snd hsig
          exact this
        funext i
        by_cases hi : i.val < n ^ 2 - 1
        · exact congrFun hpre ⟨i.val, hi⟩
        · have hieq : i = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hieq]
          have h1 : (w1 ⟨n ^ 2 - 1, by omega⟩).1 = (w1 ⟨n ^ 2 - 2, by omega⟩).2 := by
            have := hw1.1.2.2.1 ⟨n ^ 2 - 2, by omega⟩ (by dsimp only; omega)
            have hfin : (⟨n ^ 2 - 2 + 1, by omega⟩ : Fin (n ^ 2)) = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hfin] at this; exact this.symm
          have h2 : (w2 ⟨n ^ 2 - 1, by omega⟩).1 = (w2 ⟨n ^ 2 - 2, by omega⟩).2 := by
            have := hw2.1.2.2.1 ⟨n ^ 2 - 2, by omega⟩ (by dsimp only; omega)
            have hfin : (⟨n ^ 2 - 2 + 1, by omega⟩ : Fin (n ^ 2)) = ⟨n ^ 2 - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
            rw [hfin] at this; exact this.symm
          have hprev : w1 ⟨n ^ 2 - 2, by omega⟩ = w2 ⟨n ^ 2 - 2, by omega⟩ :=
            congrFun hpre ⟨n ^ 2 - 2, by omega⟩
          exact Prod.ext (h1.trans ((congrArg Prod.snd hprev).trans h2.symm)) hy
      · intro ⟨⟨u, p⟩, y⟩ hupy
        simp only [Finset.mem_product, Bpre, Y, Finset.mem_sigma, Finset.mem_erase,
          Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hupy
        obtain ⟨hu0, hstart, hchain, hinj, hmiss⟩ := hupy
        have hcls := classify_missing_edge hn (hstart (by omega)) hchain hinj hmiss
        have hend : (p ⟨n ^ 2 - 2, by omega⟩).2 = ⟨0, hn0⟩ := by
          rcases hcls with ⟨h1, _⟩ | ⟨_, _, h2⟩
          · exact absurd h1 hu0
          · exact h2
        let w : Fin (n ^ 2) → Fin n × Fin n := fun i =>
          if hi : i.val < n ^ 2 - 1 then p ⟨i.val, hi⟩ else (⟨0, hn0⟩, y)
        have hmem_w : w ∈ WB := by
          rw [Finset.mem_filter, Finset.mem_filter]
          refine ⟨⟨Finset.mem_univ w, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
          · dsimp only [w]; rw [dif_pos (by omega)]; exact hstart (by omega)
          · intro i hi
            dsimp only [w]
            by_cases h1 : i.val + 1 < n ^ 2 - 1
            · rw [dif_pos (by omega), dif_pos h1]; exact hchain ⟨i.val, by omega⟩ h1
            · have hieq : i.val = n ^ 2 - 2 := by omega
              rw [dif_pos (by omega), dif_neg h1]
              have hfin : (⟨i.val, by omega⟩ : Fin (n ^ 2 - 1)) = ⟨n ^ 2 - 2, by omega⟩ := Fin.ext hieq
              rw [hfin]; exact hend
          · intro i j hij
            dsimp only [w]; rw [dif_pos i.isLt, dif_pos j.isLt]
            intro h; exact hij (hinj h)
          · obtain ⟨_, _, huniq⟩ := exists_unique_missing_edge hn hinj
            have hne_uu : (⟨0, hn0⟩, y) ≠ (u, u) := fun h => hu0 (Prod.mk.inj h).1.symm
            by_contra hno
            push Not at hno
            have hall : ∀ j : Fin (n ^ 2 - 1), p j ≠ (⟨0, hn0⟩, y) := by
              intro j hj
              have h1 := hno j
              dsimp only [w] at h1
              rw [dif_neg (by omega), dif_pos j.isLt] at h1
              exact h1 hj.symm
            exact hne_uu ((huniq (⟨0, hn0⟩, y) hall).trans (huniq (u, u) hmiss).symm)
          · intro v
            right
            obtain ⟨i, hi⟩ := visits_all_of_inj_pred hn hinj v
            refine ⟨⟨i.val, by omega⟩, ?_⟩
            dsimp only [w]; rw [dif_pos i.isLt]; exact hi
          · rintro ⟨v_end, hmissA⟩
            obtain ⟨_, _, huniq⟩ := exists_unique_missing_edge hn hinj
            have hmissA' : ∀ i : Fin (n ^ 2 - 1), p i ≠ (v_end, ⟨0, hn0⟩) := by
              intro i hi
              have := hmissA i
              dsimp only [w] at this
              rw [dif_pos i.isLt] at this
              exact this hi
            have heq := (huniq (v_end, ⟨0, hn0⟩) hmissA').trans (huniq (u, u) hmiss).symm
            exact hu0 (Prod.mk.inj heq).2.symm
        refine ⟨w, hmem_w, ?_⟩
        have hpre : (fun i : Fin (n ^ 2 - 1) => w ⟨i.val, by omega⟩) = p := by
          funext i; dsimp only [w]; rw [dif_pos i.isLt]
        have hpre_i : ∀ i : Fin (n ^ 2 - 1), w ⟨i.val, by omega⟩ = p i := fun i => congrFun hpre i
        have hex : ∃ u' : Fin n, ∀ i : Fin (n ^ 2 - 1), w ⟨i.val, by omega⟩ ≠ (u', u') :=
          ⟨u, fun i => by rw [hpre_i i]; exact hmiss i⟩
        have hu_eq : Classical.choose hex = u := by
          have hspec : ∀ i : Fin (n ^ 2 - 1), p i ≠ (Classical.choose hex, Classical.choose hex) :=
            fun i => by rw [← hpre_i i]; exact Classical.choose_spec hex i
          obtain ⟨_, _, huniq⟩ := exists_unique_missing_edge hn hinj
          have heq := (huniq _ hspec).trans (huniq (u, u) hmiss).symm
          exact (Prod.mk.inj heq).1
        refine Prod.ext ?_ ?_
        · dsimp only
          rw [dif_pos hex]
          exact Sigma.ext hu_eq (heq_of_eq hpre)
        · dsimp only [w]; rw [dif_neg (by omega)]
    rw [hbij, Finset.card_product, Finset.card_fin, hBpre, mul_comm]
  rw [show (letI := Classical.decPred (IsEdgeCollisionWalk n (n ^ 2) hn0 hk);
      (Finset.univ.filter fun w : Fin (n ^ 2) → Fin n × Fin n =>
        IsEdgeCollisionWalk n (n ^ 2) hn0 hk w).card) = W.card by congr 1]
  rw [hW_split, hWA, hWB]
  have : 2 * n - 1 = (n - 1) + n := by omega
  rw [this, add_mul]

private theorem prove_main : type_of% @OMA.S_oeis_a396659.main := by
  intro n hn
  classical
  have hn0' : 0 < n := by omega
  have h1 := card_T_sq hn hn0'
  have h2 := card_T_succ_sq hn hn0'
  obtain ⟨c, hc⟩ := exists_euler_circuit n hn0'
  have hEC_pos : 0 < (Finset.univ.filter fun c => IsEulerCircuit n hn0' c).card :=
    Finset.card_pos.mpr ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩
  set E := (Finset.univ.filter fun c => IsEulerCircuit n hn0' c).card
  have hE0 : (E : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hT2_ne : (T n (n ^ 2 + 1) : ℚ) ≠ 0 := by
    rw [h2, Nat.cast_mul]
    exact mul_ne_zero hn0 hE0
  rw [div_eq_div_iff hT2_ne hn0, h1, h2]
  have hsub : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
    push_cast
    ring
  push_cast
  rw [hsub]
  ring

end OMA.P_oeis_a396659

theorem OMA.solution : type_of% @OMA.S_oeis_a396659.main :=
  OMA.P_oeis_a396659.prove_main
