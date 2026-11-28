import OMAStatements.S_arxiv_2105_06777
import Mathlib

namespace OMA.P_arxiv_2105_06777

open OMA.S_arxiv_2105_06777

/-- The path graph `P_4` on 4 vertices `0 - 1 - 2 - 3`. -/
def P4 : SimpleGraph (Fin 4) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

lemma P4_adj_01 : P4.Adj 0 1 := Or.inl rfl
lemma P4_adj_12 : P4.Adj 1 2 := Or.inl rfl
lemma P4_adj_23 : P4.Adj 2 3 := Or.inl rfl

lemma P4_reachable_zero : ∀ v : Fin 4, P4.Reachable v 0 := by
  intro v
  match v with
  | ⟨0, _⟩ => exact SimpleGraph.Reachable.refl 0
  | ⟨1, _⟩ => exact P4_adj_01.symm.reachable
  | ⟨2, _⟩ => exact P4_adj_12.symm.reachable.trans P4_adj_01.symm.reachable
  | ⟨3, _⟩ =>
    exact P4_adj_23.symm.reachable.trans
      (P4_adj_12.symm.reachable.trans P4_adj_01.symm.reachable)

lemma P4_connected : P4.Connected :=
  ⟨fun u v => (P4_reachable_zero u).trans (P4_reachable_zero v).symm⟩

/-- In a walk of `P4`, every adjacent step changes the vertex value by `±1`, so a cycle would
need to leave and return to its maximum vertex along two distinct smaller neighbors, impossible
since each vertex has at most one smaller neighbor. -/
lemma P4_no_two_lt_adj (m a b : Fin 4) (ha : P4.Adj m a) (hb : P4.Adj m b)
    (ham : a.val < m.val) (hbm : b.val < m.val) : a = b := by
  rcases ha with h1 | h1 <;> rcases hb with h2 | h2 <;> apply Fin.ext <;> omega

lemma walk_support_getElem {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) :
    ∀ (i : ℕ) (hi : i < p.support.length), p.support[i] = p.getVert i := by
  induction p with
  | nil =>
    intro i hi
    have h0 : i = 0 := by simp at hi; omega
    subst h0; rfl
  | cons hadj p ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ j =>
      simp only [SimpleGraph.Walk.support_cons, List.getElem_cons_succ,
        SimpleGraph.Walk.getVert_cons_succ]
      exact ih j (by simpa using hi)

lemma P4_isAcyclic : P4.IsAcyclic := by
  intro v c hc
  have hlen : 3 ≤ c.length := hc.three_le_length
  have hnodup : c.support.tail.Nodup := hc.support_nodup
  have hne : (Finset.univ : Finset (Fin c.length)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨k, _, hkmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin c.length => (c.getVert i.val).val) hne
  let m := c.getVert k.val
  let prevIdx : ℕ := if k.val = 0 then c.length - 1 else k.val - 1
  let nextIdx : ℕ := if k.val + 1 = c.length then 0 else k.val + 1
  have hprev_lt : prevIdx < c.length := by dsimp [prevIdx]; split_ifs <;> omega
  have hnext_lt : nextIdx < c.length := by dsimp [nextIdx]; split_ifs <;> omega
  have hadj_next : P4.Adj m (c.getVert nextIdx) := by
    have h1 := c.adj_getVert_succ (i := k.val) k.isLt
    by_cases hlast : k.val + 1 = c.length
    · have hget : c.getVert (k.val + 1) = c.getVert 0 := by
        rw [hlast, SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
      simpa [m, nextIdx, hlast, hget] using h1
    · simpa [m, nextIdx, hlast] using h1
  have hadj_prev : P4.Adj m (c.getVert prevIdx) := by
    by_cases h0 : k.val = 0
    · have h1 := c.adj_getVert_succ (i := c.length - 1) (by omega)
      have hlen1 : c.length - 1 + 1 = c.length := by omega
      rw [hlen1, SimpleGraph.Walk.getVert_length] at h1
      have hm0 : m = v := by simp [m, h0, SimpleGraph.Walk.getVert_zero]
      rw [hm0]
      exact (by simpa [prevIdx, h0] using h1 : P4.Adj (c.getVert prevIdx) v).symm
    · have h1 := c.adj_getVert_succ (i := k.val - 1) (by omega)
      have hsub1 : k.val - 1 + 1 = k.val := by omega
      rw [hsub1] at h1
      exact (by simpa [m, prevIdx, h0] using h1 : P4.Adj (c.getVert prevIdx) m).symm
  have hle_prev : (c.getVert prevIdx).val ≤ m.val :=
    hkmax ⟨prevIdx, hprev_lt⟩ (Finset.mem_univ _)
  have hle_next : (c.getVert nextIdx).val ≤ m.val :=
    hkmax ⟨nextIdx, hnext_lt⟩ (Finset.mem_univ _)
  have hlt_prev : (c.getVert prevIdx).val < m.val :=
    lt_of_le_of_ne hle_prev (fun heq => P4.loopless.irrefl m (by
      have : c.getVert prevIdx = m := Fin.ext heq
      rwa [this] at hadj_prev))
  have hlt_next : (c.getVert nextIdx).val < m.val :=
    lt_of_le_of_ne hle_next (fun heq => P4.loopless.irrefl m (by
      have : c.getVert nextIdx = m := Fin.ext heq
      rwa [this] at hadj_next))
  have heq_pn : c.getVert prevIdx = c.getVert nextIdx :=
    P4_no_two_lt_adj m _ _ hadj_prev hadj_next hlt_prev hlt_next
  have hp_ne_n : prevIdx ≠ nextIdx := by dsimp [prevIdx, nextIdx]; split_ifs <;> omega
  have hget_tail : ∀ (i : ℕ) (hi : i < c.length),
      c.support.tail[(if i = 0 then c.length - 1 else i - 1)]'(by
        rw [List.length_tail, SimpleGraph.Walk.length_support]; split_ifs <;> omega) =
      c.getVert i := by
    intro i hi
    rw [List.getElem_tail, walk_support_getElem c]
    split_ifs with h0
    · subst h0
      have h1 : c.length - 1 + 1 = c.length := by omega
      rw [h1, SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero]
    · have h1 : i - 1 + 1 = i := by omega
      rw [h1]
  set ip := if prevIdx = 0 then c.length - 1 else prevIdx - 1
  set inx := if nextIdx = 0 then c.length - 1 else nextIdx - 1
  have hip : ip < c.support.tail.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]; dsimp [ip]; split_ifs <;> omega
  have hinx : inx < c.support.tail.length := by
    rw [List.length_tail, SimpleGraph.Walk.length_support]; dsimp [inx]; split_ifs <;> omega
  have hsame : c.support.tail[ip]'hip = c.support.tail[inx]'hinx := by
    rw [hget_tail prevIdx hprev_lt, hget_tail nextIdx hnext_lt, heq_pn]
  have hidx_eq : ip = inx :=
    (List.Nodup.getElem_inj_iff hnodup (i := ip) (j := inx) (hi := hip) (hj := hinx)).mp hsame
  dsimp [ip, inx] at hidx_eq
  split_ifs at hidx_eq <;> omega

lemma P4_isTree : P4.IsTree := ⟨P4_connected, P4_isAcyclic⟩

section BlowupP4

variable (sizes : Fin 4 → ℕ) (isClique : Fin 4 → Bool)

abbrev BV (sizes : Fin 4 → ℕ) := (i : Fin 4) × Fin (sizes i)

/-- Every vertex in `B = blowup P4 sizes isClique` only connects to its own block or adjacent
blocks in `P4`. -/
lemma B_adj_step {u v : BV sizes} (h : (blowup P4 sizes isClique).Adj u v) :
    u.1.val = v.1.val ∨ u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val := by
  rcases h.2 with hadj | ⟨heq, _⟩
  · rcases hadj with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)
  · exact Or.inl (congrArg Fin.val heq)

/-- Along any walk in `B`, the block index changes by at most 1 per step. -/
lemma B_walk_diff_le {u v : BV sizes} (p : (blowup P4 sizes isClique).Walk u v) :
    (u.1.val : ℤ) - (v.1.val : ℤ) ≤ (p.length : ℤ) ∧
    (v.1.val : ℤ) - (u.1.val : ℤ) ≤ (p.length : ℤ) := by
  induction p with
  | nil => simp
  | cons hadj p ih =>
    rename_i a b c
    have hstep := B_adj_step sizes isClique hadj
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    rcases hstep with h | h | h <;> omega

/-- Distance in `B` is at least `|u.1 - v.1|`. -/
lemma B_dist_ge_block_diff (u v : BV sizes) (hreach : (blowup P4 sizes isClique).Reachable u v) :
    (u.1.val : ℤ) - (v.1.val : ℤ) ≤ ((blowup P4 sizes isClique).dist u v : ℤ) ∧
    (v.1.val : ℤ) - (u.1.val : ℤ) ≤ ((blowup P4 sizes isClique).dist u v : ℤ) := by
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  rw [← hp]
  exact B_walk_diff_le sizes isClique p

lemma B_adj_of_P4 {u v : BV sizes} (h : P4.Adj u.1 v.1) :
    (blowup P4 sizes isClique).Adj u v := by
  refine ⟨fun heq => P4.loopless.irrefl u.1 (heq ▸ h), Or.inl h⟩

lemma B_connected (hpos : ∀ i, 0 < sizes i) : (blowup P4 sizes isClique).Connected := by
  let x0 : BV sizes := ⟨0, ⟨0, hpos 0⟩⟩
  let x1 : BV sizes := ⟨1, ⟨0, hpos 1⟩⟩
  let x2 : BV sizes := ⟨2, ⟨0, hpos 2⟩⟩
  have hreach0 : ∀ u : BV sizes, (blowup P4 sizes isClique).Reachable u x0 := by
    intro ⟨i, j⟩
    match i with
    | ⟨0, _⟩ =>
      have h1 : (blowup P4 sizes isClique).Adj ⟨0, j⟩ x1 := B_adj_of_P4 sizes isClique P4_adj_01
      have h2 : (blowup P4 sizes isClique).Adj x1 x0 := B_adj_of_P4 sizes isClique P4_adj_01.symm
      exact h1.reachable.trans h2.reachable
    | ⟨1, _⟩ =>
      exact (B_adj_of_P4 sizes isClique P4_adj_01.symm).reachable
    | ⟨2, _⟩ =>
      have h1 : (blowup P4 sizes isClique).Adj ⟨2, j⟩ x1 := B_adj_of_P4 sizes isClique P4_adj_12.symm
      have h2 : (blowup P4 sizes isClique).Adj x1 x0 := B_adj_of_P4 sizes isClique P4_adj_01.symm
      exact h1.reachable.trans h2.reachable
    | ⟨3, _⟩ =>
      have h1 : (blowup P4 sizes isClique).Adj ⟨3, j⟩ x2 := B_adj_of_P4 sizes isClique P4_adj_23.symm
      have h2 : (blowup P4 sizes isClique).Adj x2 x1 := B_adj_of_P4 sizes isClique P4_adj_12.symm
      have h3 : (blowup P4 sizes isClique).Adj x1 x0 := B_adj_of_P4 sizes isClique P4_adj_01.symm
      exact h1.reachable.trans (h2.reachable.trans h3.reachable)
  have : Nonempty (BV sizes) := ⟨x0⟩
  exact ⟨fun u v => (hreach0 u).trans (hreach0 v).symm⟩

/-- Upper bound: `dist u v ≤ 3` for all `u, v`, and `≤ 2` unless `{u.1, v.1} = {0, 3}`. -/
lemma B_dist_le_three (hpos : ∀ i, 0 < sizes i) (u v : BV sizes) :
    (blowup P4 sizes isClique).dist u v ≤ 3 := by
  let x1 : BV sizes := ⟨1, ⟨0, hpos 1⟩⟩
  let x2 : BV sizes := ⟨2, ⟨0, hpos 2⟩⟩
  have hwalk1 : ∀ a b : BV sizes,
      (blowup P4 sizes isClique).Adj a b → (blowup P4 sizes isClique).dist a b ≤ 1 := fun a b h1 =>
    SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil)
  have hwalk2 : ∀ a b c : BV sizes,
      (blowup P4 sizes isClique).Adj a b → (blowup P4 sizes isClique).Adj b c →
      (blowup P4 sizes isClique).dist a c ≤ 2 := fun a b c h1 h2 =>
    SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil))
  have hwalk3 : ∀ a b c d : BV sizes,
      (blowup P4 sizes isClique).Adj a b → (blowup P4 sizes isClique).Adj b c →
      (blowup P4 sizes isClique).Adj c d →
      (blowup P4 sizes isClique).dist a d ≤ 3 := fun a b c d h1 h2 h3 =>
    SimpleGraph.dist_le
      (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3 SimpleGraph.Walk.nil)))
  rcases u with ⟨iu, ju⟩
  rcases v with ⟨iv, jv⟩
  match iu, iv with
  | ⟨0, _⟩, ⟨0, _⟩ =>
    exact le_trans (hwalk2 _ x1 _ (B_adj_of_P4 _ _ P4_adj_01) (B_adj_of_P4 _ _ P4_adj_01.symm)) (by omega)
  | ⟨0, _⟩, ⟨1, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_01)) (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ =>
    exact le_trans (hwalk2 _ x1 _ (B_adj_of_P4 _ _ P4_adj_01) (B_adj_of_P4 _ _ P4_adj_12)) (by omega)
  | ⟨0, _⟩, ⟨3, _⟩ =>
    exact hwalk3 _ x1 x2 _ (B_adj_of_P4 _ _ P4_adj_01) (B_adj_of_P4 _ _ P4_adj_12) (B_adj_of_P4 _ _ P4_adj_23)
  | ⟨1, _⟩, ⟨0, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_01.symm)) (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ =>
    exact le_trans (hwalk2 _ x2 _ (B_adj_of_P4 _ _ P4_adj_12) (B_adj_of_P4 _ _ P4_adj_12.symm)) (by omega)
  | ⟨1, _⟩, ⟨2, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_12)) (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ =>
    exact le_trans (hwalk2 _ x2 _ (B_adj_of_P4 _ _ P4_adj_12) (B_adj_of_P4 _ _ P4_adj_23)) (by omega)
  | ⟨2, _⟩, ⟨0, _⟩ =>
    exact le_trans (hwalk2 _ x1 _ (B_adj_of_P4 _ _ P4_adj_12.symm) (B_adj_of_P4 _ _ P4_adj_01.symm)) (by omega)
  | ⟨2, _⟩, ⟨1, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_12.symm)) (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ =>
    exact le_trans (hwalk2 _ x1 _ (B_adj_of_P4 _ _ P4_adj_12.symm) (B_adj_of_P4 _ _ P4_adj_12)) (by omega)
  | ⟨2, _⟩, ⟨3, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_23)) (by omega)
  | ⟨3, _⟩, ⟨0, _⟩ =>
    exact hwalk3 _ x2 x1 _ (B_adj_of_P4 _ _ P4_adj_23.symm) (B_adj_of_P4 _ _ P4_adj_12.symm)
      (B_adj_of_P4 _ _ P4_adj_01.symm)
  | ⟨3, _⟩, ⟨1, _⟩ =>
    exact le_trans (hwalk2 _ x2 _ (B_adj_of_P4 _ _ P4_adj_23.symm) (B_adj_of_P4 _ _ P4_adj_12.symm)) (by omega)
  | ⟨3, _⟩, ⟨2, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_23.symm)) (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ =>
    exact le_trans (hwalk2 _ x2 _ (B_adj_of_P4 _ _ P4_adj_23.symm) (B_adj_of_P4 _ _ P4_adj_23)) (by omega)

lemma B_dist_eq_two_of_02 (hpos : ∀ i, 0 < sizes i) {u v : BV sizes} (hu : u.1 = 0) (hv : v.1 = 2) :
    (blowup P4 sizes isClique).dist u v = 2 := by
  let x1 : BV sizes := ⟨1, ⟨0, hpos 1⟩⟩
  have hle : (blowup P4 sizes isClique).dist u v ≤ 2 := by
    have h1 : (blowup P4 sizes isClique).Adj u x1 :=
      B_adj_of_P4 sizes isClique (by rw [hu]; exact P4_adj_01)
    have h2 : (blowup P4 sizes isClique).Adj x1 v :=
      B_adj_of_P4 sizes isClique (by rw [hv]; exact P4_adj_12)
    exact SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil))
  have hge := (B_dist_ge_block_diff sizes isClique u v (B_connected sizes isClique hpos u v)).2
  rw [hu, hv] at hge
  omega

/-- Upper bound: `dist u v ≤ 2` unless `{u.1, v.1} = {0, 3}`. -/
lemma B_dist_le_two_of_ne03 (hpos : ∀ i, 0 < sizes i) (u v : BV sizes)
    (hnot : ¬ ((u.1.val = 0 ∧ v.1.val = 3) ∨ (u.1.val = 3 ∧ v.1.val = 0))) :
    (blowup P4 sizes isClique).dist u v ≤ 2 := by
  let x1 : BV sizes := ⟨1, ⟨0, hpos 1⟩⟩
  let x2 : BV sizes := ⟨2, ⟨0, hpos 2⟩⟩
  have hwalk1 : ∀ a b : BV sizes,
      (blowup P4 sizes isClique).Adj a b → (blowup P4 sizes isClique).dist a b ≤ 1 := fun a b h1 =>
    SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 SimpleGraph.Walk.nil)
  have hwalk2 : ∀ a b c : BV sizes,
      (blowup P4 sizes isClique).Adj a b → (blowup P4 sizes isClique).Adj b c →
      (blowup P4 sizes isClique).dist a c ≤ 2 := fun a b c h1 h2 =>
    SimpleGraph.dist_le (SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil))
  rcases u with ⟨iu, ju⟩
  rcases v with ⟨iv, jv⟩
  match iu, iv with
  | ⟨0, _⟩, ⟨0, _⟩ => exact hwalk2 _ x1 _ (B_adj_of_P4 _ _ P4_adj_01) (B_adj_of_P4 _ _ P4_adj_01.symm)
  | ⟨0, _⟩, ⟨1, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_01)) (by omega)
  | ⟨0, _⟩, ⟨2, _⟩ => exact hwalk2 _ x1 _ (B_adj_of_P4 _ _ P4_adj_01) (B_adj_of_P4 _ _ P4_adj_12)
  | ⟨0, _⟩, ⟨3, _⟩ => exact absurd (Or.inl ⟨rfl, rfl⟩) hnot
  | ⟨1, _⟩, ⟨0, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_01.symm)) (by omega)
  | ⟨1, _⟩, ⟨1, _⟩ => exact hwalk2 _ x2 _ (B_adj_of_P4 _ _ P4_adj_12) (B_adj_of_P4 _ _ P4_adj_12.symm)
  | ⟨1, _⟩, ⟨2, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_12)) (by omega)
  | ⟨1, _⟩, ⟨3, _⟩ => exact hwalk2 _ x2 _ (B_adj_of_P4 _ _ P4_adj_12) (B_adj_of_P4 _ _ P4_adj_23)
  | ⟨2, _⟩, ⟨0, _⟩ => exact hwalk2 _ x1 _ (B_adj_of_P4 _ _ P4_adj_12.symm) (B_adj_of_P4 _ _ P4_adj_01.symm)
  | ⟨2, _⟩, ⟨1, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_12.symm)) (by omega)
  | ⟨2, _⟩, ⟨2, _⟩ => exact hwalk2 _ x1 _ (B_adj_of_P4 _ _ P4_adj_12.symm) (B_adj_of_P4 _ _ P4_adj_12)
  | ⟨2, _⟩, ⟨3, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_23)) (by omega)
  | ⟨3, _⟩, ⟨0, _⟩ => exact absurd (Or.inr ⟨rfl, rfl⟩) hnot
  | ⟨3, _⟩, ⟨1, _⟩ => exact hwalk2 _ x2 _ (B_adj_of_P4 _ _ P4_adj_23.symm) (B_adj_of_P4 _ _ P4_adj_12.symm)
  | ⟨3, _⟩, ⟨2, _⟩ => exact le_trans (hwalk1 _ _ (B_adj_of_P4 _ _ P4_adj_23.symm)) (by omega)
  | ⟨3, _⟩, ⟨3, _⟩ => exact hwalk2 _ x2 _ (B_adj_of_P4 _ _ P4_adj_23.symm) (B_adj_of_P4 _ _ P4_adj_23)

/-- Key structural lemma: a vertex `x3` in leaf block `3` can ONLY be an internal vertex of a
shortest path from `u` to `v` if `u` and `v` are both in block `2` and `isClique 2 = false`
(with `dist u v = 2`). -/
lemma x3_only_on_22 (hpos : ∀ i, 0 < sizes i) {u v x3 : BV sizes} (hx3 : x3.1 = 3)
    {w : Fin ((blowup P4 sizes isClique).dist u v + 1) → BV sizes}
    (hw : w ∈ shortestPaths (blowup P4 sizes isClique) u v)
    (hpass : passesThrough x3 w) :
    u.1 = 2 ∧ v.1 = 2 ∧ isClique 2 = false ∧ (blowup P4 sizes isClique).dist u v = 2 := by
  let B := blowup P4 sizes isClique
  let L := B.dist u v
  have hmem : w 0 = u ∧ w ⟨L, Nat.lt_succ_self L⟩ = v ∧
      ∀ k : Fin L, B.Adj (w k.castSucc) (w k.succ) := by
    simpa [shortestPaths, B, L] using hw
  rcases hmem with ⟨hw0, hwL, hwadj⟩
  obtain ⟨k, hkpos, hklt, hwk⟩ := hpass
  change k.val < L at hklt
  have hLle3 : L ≤ 3 := B_dist_le_three sizes isClique hpos u v
  have hLge2 : 2 ≤ L := by omega
  -- Case 1: L = 3 -> blocks must go 0 -> 1 -> 2 -> 3 or 3 -> 2 -> 1 -> 0, never hitting 3 internally!
  by_cases hL3 : L = 3
  · exfalso
    have h0L : 0 < L := by omega
    have h1L : 1 < L := by omega
    have h2L : 2 < L := by omega
    have hstep0 := B_adj_step sizes isClique (hwadj ⟨0, h0L⟩)
    have hstep1 := B_adj_step sizes isClique (hwadj ⟨1, h1L⟩)
    have hstep2 := B_adj_step sizes isClique (hwadj ⟨2, h2L⟩)
    have huv03 : (u.1.val = 0 ∧ v.1.val = 3) ∨ (u.1.val = 3 ∧ v.1.val = 0) := by
      by_contra hnot
      have hle2 : L ≤ 2 := B_dist_le_two_of_ne03 sizes isClique hpos u v hnot
      omega
    have h0_eq : (⟨0, h0L⟩ : Fin L).castSucc = 0 := rfl
    have h2_eq : (⟨2, h2L⟩ : Fin L).succ = ⟨L, Nat.lt_succ_self L⟩ := Fin.ext (by simp [hL3])
    have h1_eq : (⟨0, h0L⟩ : Fin L).succ = (⟨1, h1L⟩ : Fin L).castSucc := rfl
    have h2'_eq : (⟨1, h1L⟩ : Fin L).succ = (⟨2, h2L⟩ : Fin L).castSucc := rfl
    rw [h0_eq, hw0] at hstep0
    rw [← h1_eq] at hstep1
    rw [← h2'_eq, h2_eq, hwL] at hstep2
    have hkv : (w k).1.val = 3 := by rw [hwk, hx3]; rfl
    have hk12 : k = (⟨0, h0L⟩ : Fin L).succ ∨ k = (⟨1, h1L⟩ : Fin L).succ := by
      have : k.val = 1 ∨ k.val = 2 := by omega
      rcases this with h | h
      · exact Or.inl (Fin.ext (by simp [h]))
      · exact Or.inr (Fin.ext (by simp [h]))
    rcases hk12 with hk1 | hk2
    · rw [hk1] at hkv
      rcases huv03 with ⟨hu0, hv3⟩ | ⟨hu3, hv0⟩ <;>
        rcases hstep0 with hs0 | hs0 | hs0 <;>
        rcases hstep1 with hs1 | hs1 | hs1 <;>
        rcases hstep2 with hs2 | hs2 | hs2 <;> omega
    · rw [hk2] at hkv
      rcases huv03 with ⟨hu0, hv3⟩ | ⟨hu3, hv0⟩ <;>
        rcases hstep0 with hs0 | hs0 | hs0 <;>
        rcases hstep1 with hs1 | hs1 | hs1 <;>
        rcases hstep2 with hs2 | hs2 | hs2 <;> omega
  -- Case 2: L = 2 -> k = 1, so u ~ x3 ~ v and ¬ B.Adj u v!
  · have hL2 : L = 2 := by omega
    have hk1 : k.val = 1 := by omega
    have hu_x3 : B.Adj u x3 := by
      have h := hwadj ⟨0, by omega⟩
      have h0 : (⟨0, by omega⟩ : Fin L).castSucc = 0 := rfl
      have h1 : (⟨0, by omega⟩ : Fin L).succ = k := Fin.ext (by simp [hk1])
      rw [h0, h1, hw0, hwk] at h
      exact h
    have hx3_v : B.Adj x3 v := by
      have h := hwadj ⟨1, by omega⟩
      have h1 : (⟨1, by omega⟩ : Fin L).castSucc = k := Fin.ext (by simp [hk1])
      have h2 : (⟨1, by omega⟩ : Fin L).succ = ⟨L, Nat.lt_succ_self L⟩ := Fin.ext (by simp [hL2])
      rw [h1, h2, hwk, hwL] at h
      exact h
    have hnot_adj : ¬ B.Adj u v := fun hadj => by
      have hle1 : L ≤ 1 := SimpleGraph.dist_le hadj.toWalk
      omega
    have hne_uv : u ≠ v := fun heq => by
      have h0 : L = 0 := by dsimp [L]; rw [heq]; exact SimpleGraph.dist_self
      omega
    have hsu := B_adj_step sizes isClique hu_x3
    have hsv := B_adj_step sizes isClique hx3_v
    have hu23 : u.1 = 2 ∨ u.1 = 3 := by
      have : u.1.val = 2 ∨ u.1.val = 3 := by
        have hx3v : x3.1.val = 3 := by rw [hx3]; rfl
        omega
      rcases this with h | h <;> [exact Or.inl (Fin.ext h); exact Or.inr (Fin.ext h)]
    have hv23 : v.1 = 2 ∨ v.1 = 3 := by
      have : v.1.val = 2 ∨ v.1.val = 3 := by
        have hx3v : x3.1.val = 3 := by rw [hx3]; rfl
        omega
      rcases this with h | h <;> [exact Or.inl (Fin.ext h); exact Or.inr (Fin.ext h)]
    rcases hu23 with hu2 | hu3 <;> rcases hv23 with hv2 | hv3
    · refine ⟨hu2, hv2, ?_, hL2⟩
      by_contra hcl
      have hcl' : isClique 2 = true := Bool.eq_true_of_not_eq_false hcl
      exact hnot_adj ⟨hne_uv, Or.inr ⟨hu2.trans hv2.symm, hu2 ▸ hcl'⟩⟩
    · exfalso
      exact hnot_adj (B_adj_of_P4 sizes isClique (by rw [hu2, hv3]; exact P4_adj_23))
    · exfalso
      exact hnot_adj (B_adj_of_P4 sizes isClique (by rw [hu3, hv2]; exact P4_adj_23.symm))
    · exfalso
      -- Both u, v are in block 3 and adjacent to x3 (also in block 3), so isClique 3 = true -> u ~ v!
      have hcl3 : isClique 3 = true := by
        rcases hu_x3.2 with hP4 | ⟨_, hcl⟩
        · rw [hu3, hx3] at hP4; exact absurd hP4 (P4.loopless.irrefl 3)
        · rwa [hu3] at hcl
      exact hnot_adj ⟨hne_uv, Or.inr ⟨hu3.trans hv3.symm, hu3 ▸ hcl3⟩⟩

/-- For any `u, v` with `B.dist u v = 2`, a shortest path from `u` to `v` passing through a given
vertex `x` is unique (`![u, x, v]`), so `sigmaThrough B u v x ≤ 1`, and equals `1` whenever
`B.Adj u x ∧ B.Adj x v`. -/
lemma sigmaThrough_eq_one_of_dist_two {u v x : BV sizes}
    (hdist : (blowup P4 sizes isClique).dist u v = 2)
    (hux : (blowup P4 sizes isClique).Adj u x)
    (hxv : (blowup P4 sizes isClique).Adj x v) :
    sigmaThrough (blowup P4 sizes isClique) u v x = 1 := by
  let B := blowup P4 sizes isClique
  classical
  unfold sigmaThrough
  let w0 : Fin (B.dist u v + 1) → BV sizes := fun i =>
    if i.val = 0 then u else if i.val = 1 then x else v
  have hw0_mem : w0 ∈ (shortestPaths B u v).filter (passesThrough x) := by
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [shortestPaths, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by simp [w0], by simp [w0, B, hdist], fun k => ?_⟩
      have hklt : k.val < 2 := by have := k.isLt; dsimp [B] at this; omega
      have hk : k.val = 0 ∨ k.val = 1 := by omega
      rcases hk with h0 | h1
      · dsimp only [w0]
        rw [if_pos (by simp [h0]), if_neg (by simp [h0]), if_pos (by simp [h0])]
        exact hux
      · dsimp only [w0]
        rw [if_neg (by simp [h1]), if_pos (by simp [h1]),
          if_neg (by simp [h1]), if_neg (by simp [h1])]
        exact hxv
    · exact ⟨⟨1, by dsimp [B]; omega⟩, by norm_num, by dsimp [B]; omega, by
        dsimp only [w0]; rw [if_neg (by decide), if_pos rfl]⟩
  have huniq : ∀ w ∈ (shortestPaths B u v).filter (passesThrough x), w = w0 := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hsp, ⟨k, hkpos, hklt, hwk⟩⟩ := hw
    have hmem : w 0 = u ∧ w ⟨B.dist u v, Nat.lt_succ_self _⟩ = v ∧
        ∀ j : Fin (B.dist u v), B.Adj (w j.castSucc) (w j.succ) := by
      simpa [shortestPaths] using hsp
    have hk1 : k.val = 1 := by dsimp [B] at hklt; omega
    funext i
    have hilt : i.val < 3 := by have := i.isLt; dsimp [B] at this; omega
    have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hi with h0 | h1 | h2
    · have : i = 0 := Fin.ext h0
      rw [this, hmem.1]; dsimp only [w0]; rw [if_pos (Fin.val_zero _)]
    · have : i = k := Fin.ext (by omega)
      rw [this, hwk]; dsimp only [w0]; rw [if_neg (by omega), if_pos hk1]
    · have : i = ⟨B.dist u v, Nat.lt_succ_self _⟩ := Fin.ext (by dsimp [B]; omega)
      rw [this, hmem.2.1]; dsimp only [w0]
      rw [if_neg (by dsimp [B]; omega), if_neg (by dsimp [B]; omega)]
  rw [Finset.card_eq_one]
  exact ⟨w0, Finset.eq_singleton_iff_unique_mem.mpr ⟨hw0_mem, huniq⟩⟩

lemma B_not_betweennessUniform (hpos : ∀ i, 0 < sizes i) :
    ¬ IsBetweennessUniform (blowup P4 sizes isClique) := by
  intro hunif
  set B := blowup P4 sizes isClique
  let x1 : BV sizes := ⟨1, ⟨0, hpos 1⟩⟩
  let x3 : BV sizes := ⟨3, ⟨0, hpos 3⟩⟩
  let u0 : BV sizes := ⟨0, ⟨0, hpos 0⟩⟩
  let v2 : BV sizes := ⟨2, ⟨0, hpos 2⟩⟩
  have heq := hunif x3 x1
  -- Show `betweenness B x3 < betweenness B x1` pointwise over `(u, v)`
  let term (x u v : BV sizes) : ℚ :=
    if u ≠ x ∧ v ≠ x ∧ u ≠ v ∧ 0 < sigma B u v then
      (sigmaThrough B u v x : ℚ) / (sigma B u v : ℚ)
    else 0
  have hterm_le : ∀ u v : BV sizes, term x3 u v ≤ term x1 u v := by
    intro u v
    dsimp only [term]
    split_ifs with h3 h1
    · -- Both conditions hold
      by_cases hst0 : sigmaThrough B u v x3 = 0
      · rw [hst0, Nat.cast_zero, zero_div]
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · have hpos3 : 0 < sigmaThrough B u v x3 := Nat.pos_of_ne_zero hst0
        classical
        obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos3
        rw [Finset.mem_filter] at hw
        obtain ⟨hu2, hv2, hcl2, hdist2⟩ :=
          x3_only_on_22 sizes isClique hpos (x3 := x3) rfl hw.1 hw.2
        have h1eq : sigmaThrough B u v x1 = 1 :=
          sigmaThrough_eq_one_of_dist_two sizes isClique hdist2
            (B_adj_of_P4 sizes isClique (by rw [hu2]; exact P4_adj_12.symm))
            (B_adj_of_P4 sizes isClique (by rw [hv2]; exact P4_adj_12))
        have h3eq : sigmaThrough B u v x3 = 1 :=
          sigmaThrough_eq_one_of_dist_two sizes isClique hdist2
            (B_adj_of_P4 sizes isClique (by rw [hu2]; exact P4_adj_23))
            (B_adj_of_P4 sizes isClique (by rw [hv2]; exact P4_adj_23.symm))
        rw [h1eq, h3eq]
    · -- Condition for x3 holds, condition for x1 fails -> u = x1 or v = x1 -> sigmaThrough x3 = 0!
      have hst0 : sigmaThrough B u v x3 = 0 := by
        by_contra hne0
        classical
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne0)
        rw [Finset.mem_filter] at hw
        obtain ⟨hu2, hv2, _, _⟩ :=
          x3_only_on_22 sizes isClique hpos (x3 := x3) rfl hw.1 hw.2
        apply h1
        refine ⟨?_, ?_, h3.2.2.1, h3.2.2.2⟩
        · intro he; have := congrArg Sigma.fst he; rw [hu2] at this; exact absurd this (by dsimp [x1]; decide)
        · intro he; have := congrArg Sigma.fst he; rw [hv2] at this; exact absurd this (by dsimp [x1]; decide)
      rw [hst0, Nat.cast_zero, zero_div]
    · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · exact le_refl 0
  -- Strict inequality at `(u0, v2)`!
  have hdist02 : B.dist u0 v2 = 2 := B_dist_eq_two_of_02 sizes isClique hpos rfl rfl
  have hst1_02 : sigmaThrough B u0 v2 x1 = 1 :=
    sigmaThrough_eq_one_of_dist_two sizes isClique hdist02
      (B_adj_of_P4 sizes isClique P4_adj_01)
      (B_adj_of_P4 sizes isClique P4_adj_12)
  have hsig_pos : 0 < sigma B u0 v2 := by
    have hle : sigmaThrough B u0 v2 x1 ≤ sigma B u0 v2 := by
      classical
      exact Finset.card_filter_le _ _
    omega
  have hst3_02 : sigmaThrough B u0 v2 x3 = 0 := by
    by_contra hne0
    classical
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne0)
    rw [Finset.mem_filter] at hw
    obtain ⟨hu2, _, _, _⟩ := x3_only_on_22 sizes isClique hpos (x3 := x3) rfl hw.1 hw.2
    exact absurd hu2 (by dsimp [u0]; decide)
  have hlt_02 : term x3 u0 v2 < term x1 u0 v2 := by
    have hu0_ne_x1 : u0 ≠ x1 := fun h => absurd (congrArg Sigma.fst h) (by dsimp [u0, x1]; decide)
    have hv2_ne_x1 : v2 ≠ x1 := fun h => absurd (congrArg Sigma.fst h) (by dsimp [v2, x1]; decide)
    have hu0_ne_v2 : u0 ≠ v2 := fun h => absurd (congrArg Sigma.fst h) (by dsimp [u0, v2]; decide)
    have ht3 : term x3 u0 v2 = 0 := by
      dsimp only [term]
      split_ifs <;> simp [hst3_02]
    have ht1 : term x1 u0 v2 = (1 : ℚ) / (sigma B u0 v2 : ℚ) := by
      dsimp only [term]
      rw [if_pos ⟨hu0_ne_x1, hv2_ne_x1, hu0_ne_v2, hsig_pos⟩, hst1_02, Nat.cast_one]
    rw [ht3, ht1]
    exact div_pos one_pos (Nat.cast_pos.mpr hsig_pos)
  have hlt : betweenness B x3 < betweenness B x1 := by
    change (∑ u : BV sizes, ∑ v : BV sizes, term x3 u v) <
      (∑ u : BV sizes, ∑ v : BV sizes, term x1 u v)
    refine Finset.sum_lt_sum (fun u _ => Finset.sum_le_sum fun v _ => hterm_le u v) ?_
    refine ⟨u0, Finset.mem_univ u0, ?_⟩
    exact Finset.sum_lt_sum (fun v _ => hterm_le u0 v) ⟨v2, Finset.mem_univ v2, hlt_02⟩
  exact ne_of_lt hlt heq

end BlowupP4

end OMA.P_arxiv_2105_06777

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2105_06777.main) := by
  intro h
  obtain ⟨sizes, isClique, hpos, hunif⟩ := h 4 OMA.P_arxiv_2105_06777.P4 OMA.P_arxiv_2105_06777.P4_isTree
  exact OMA.P_arxiv_2105_06777.B_not_betweennessUniform sizes isClique hpos hunif
